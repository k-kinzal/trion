package dev.trion.intellij

import com.intellij.codeInsight.navigation.actions.GotoDeclarationHandler
import com.intellij.lang.documentation.AbstractDocumentationProvider
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.LocalFileSystem
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.psi.PsiElement
import com.intellij.psi.PsiFile
import com.intellij.psi.PsiManager
import java.io.File

/** What the text at an offset points to. */
sealed class TrionTarget {
    data class Include(val path: String) : TrionTarget()
    data class Namespace(val name: String) : TrionTarget()
    data class Source(val name: String, val quote: String?) : TrionTarget()
    data class Statement(val id: String) : TrionTarget()
    data class Term(val words: List<String>, val at: Int) : TrionTarget()
}

object TrionResolver {
    private val id = Regex("[A-Z][A-Z0-9-]*(?:/[a-z][a-z0-9-]*)?")
    private val article = setOf("a", "an", "the", "each", "every", "all", "any", "no")

    private fun lineAt(text: String, offset: Int): Pair<Int, String> {
        val start = text.lastIndexOf('\n', (offset - 1).coerceAtLeast(0)).let { if (offset == 0) 0 else it + 1 }
        val end = text.indexOf('\n', offset).let { if (it < 0) text.length else it }
        return start to text.substring(start, end)
    }

    /** Reads the reference under an offset from the line it stands on. */
    fun targetAt(text: String, offset: Int): TrionTarget? {
        val (start, line) = lineAt(text, offset.coerceIn(0, text.length))
        val column = offset - start
        val code = TrionLines.stripComment(line)
        val trimmed = code.trim()
        val directive = TrionLines.directive(line)
        // A verification marker in a comment of another language reads the same way.
        Regex("trion:\\s*verifies\\s+(.*)").find(line)?.let { marker ->
            Regex("[a-z][a-z0-9.-]*(?:@[0-9a-f]+)?#(${id.pattern})").findAll(marker.value).forEach { found ->
                val range = found.range.first + marker.range.first..found.range.last + marker.range.first
                if (column in range) return TrionTarget.Statement(found.groupValues[1])
            }
        }
        if (column > code.length) return null
        when (directive) {
            "include" -> return Regex("\"(.*)\"").find(trimmed)?.let { TrionTarget.Include(it.groupValues[1]) }
            "use" -> return TrionTarget.Namespace(trimmed.removePrefix("use").trim())
            "cite" -> {
                val name = trimmed.removePrefix("cite").trim()
                val hash = code.indexOf('#')
                val onSource = hash < 0 || column <= hash
                return TrionTarget.Source(name.substringBefore('#'), name.substringAfter('#', "").ifEmpty { null }.takeIf { !onSource })
            }
            "ref", "left", "right", "statements", "verifies", "detailed", "overrides" -> return idAt(code, column)?.let { TrionTarget.Statement(it) }
            null -> {}
            else -> if (directive !in setOf("step", "when", "activate", "form", "required")) return null
        }
        Regex("\\[(${id.pattern})]").findAll(code).forEach { found ->
            if (column in found.range.first..found.range.last + 1) return TrionTarget.Statement(found.groupValues[1])
        }
        // Sentence text: the words of the line with the index of the word under the caret.
        val words = Regex("[A-Za-z][A-Za-z0-9_'-]*(?:::[A-Za-z][A-Za-z0-9_'-]*)?").findAll(code).toList()
        val at = words.indexOfFirst { column in it.range.first..it.range.last + 1 }
        return if (at < 0) null else TrionTarget.Term(words.map { it.value }, at)
    }

    private fun idAt(code: String, column: Int): String? =
        id.findAll(code).firstOrNull { column in it.range.first..it.range.last + 1 && (it.range.first == 0 || !code[it.range.first - 1].isLetter()) }?.value

    private fun normal(word: String): String {
        val lower = word.lowercase()
        return when {
            lower.endsWith("ies") && lower.length > 4 -> lower.dropLast(3) + "y"
            lower.endsWith("ses") || lower.endsWith("xes") || lower.endsWith("ches") || lower.endsWith("shes") -> lower.dropLast(2)
            lower.endsWith("s") && !lower.endsWith("ss") && lower.length > 3 -> lower.dropLast(1)
            else -> lower
        }
    }

    private fun key(words: List<String>): String = words.joinToString(" ") { normal(it) }

    /** The glossary entry for the longest run of words around the caret that names a term. */
    fun term(target: TrionTarget.Term, glossary: List<TrionTerm>): TrionTerm? {
        val byLocal = HashMap<String, MutableList<TrionTerm>>()
        for (entry in glossary) {
            byLocal.getOrPut(key(entry.term.substringAfterLast("::").split(' '))) { ArrayList() }.add(entry)
        }
        val words = target.words
        val best = { found: List<TrionTerm> -> found.minByOrNull { listOf("explicit", "declared", "primitive", "imported", "derived").indexOf(it.status).let { rank -> if (rank < 0) 9 else rank } } }
        for (length in minOf(6, words.size) downTo 1) {
            for (first in (target.at - length + 1).coerceAtLeast(0)..target.at) {
                if (first + length > words.size) continue
                val run = words.subList(first, first + length).map { it.substringAfterLast("::") }
                if (length > 1 && run.first().lowercase() in article) continue
                byLocal[key(run)]?.let { return best(it) }
            }
        }
        return null
    }

    fun root(file: PsiFile): File? = file.virtualFile?.onDisk()?.let { packageRoot(it) }

    private fun trionFiles(root: File): Sequence<File> =
        root.walkTopDown().onEnter { it.name != "target" && it.name != "build" && it.name != "node_modules" && !it.name.startsWith(".") }.filter { it.isFile && it.name.endsWith(".trion") }

    /** The outline of every trion file under a package root, read from disk. */
    fun scan(root: File): List<TrionIndexedFile> = trionFiles(root).map { TrionIndexedFile(it, TrionOutline.entries(it.readText())) }.toList()

    /** The file and offset an outline entry of the package occupies. */
    private fun find(files: List<TrionIndexedFile>, wanted: (OutlineEntry) -> Boolean): Pair<File, Int>? =
        files.firstNotNullOfOrNull { indexed -> indexed.entries.firstOrNull(wanted)?.let { indexed.file to it.start } }

    /** `file:line` relative to the package root, as the glossary prints positions. */
    private fun position(root: File, position: String): Pair<File, Int>? {
        val path = position.substringBeforeLast(':')
        val line = position.substringAfterLast(':').toIntOrNull() ?: return null
        val file = File(root, path).takeIf { it.isFile } ?: return null
        val offset = TrionOutline.lineOffset(file.readText(), line - 1)
        return if (offset < 0) null else file to offset
    }

    /** Where a target is declared: a file and an offset in it. */
    fun locate(target: TrionTarget, from: File, root: File?, files: (File) -> List<TrionIndexedFile> = ::scan, glossary: () -> List<TrionTerm>): Pair<File, Int>? = when (target) {
        is TrionTarget.Include -> File(from.parentFile, target.path).takeIf { it.isFile }?.let { it to 0 }
        is TrionTarget.Namespace -> root?.let { r ->
            val manifest = File(r, "trion.toml").readText()
            val pkg = Regex("name\\s*=\\s*\"([^\"]+)\"").find(manifest.substringAfter("[package]", manifest))?.groupValues?.get(1)
            val names = setOf(target.name, "$pkg.${target.name}")
            find(files(r)) { it.kind == "namespace" && it.name in names }
        }
        is TrionTarget.Source -> root?.let { r ->
            if (target.quote == null) {
                find(files(r)) { it.kind == "source" && it.name == target.name }
            } else {
                files(r).firstNotNullOfOrNull { indexed ->
                    val source = indexed.entries.firstOrNull { it.kind == "source" && it.name == target.name }
                    source?.let { s -> indexed.entries.firstOrNull { it.kind == "quote" && it.name == target.quote && it.start in s.start..s.end } }?.let { indexed.file to it.start }
                }
            }
        }
        is TrionTarget.Statement -> root?.let { r ->
            val known = files(r)
            find(known) { it.kind == "statement" && it.name == target.id } ?: find(known) { it.kind == "statement" && it.name == target.id.substringBefore('/') }
        }
        is TrionTarget.Term -> root?.let { r -> term(target, glossary())?.origin?.let { position(r, it) } }
    }
}

class TrionGotoDeclarationHandler : GotoDeclarationHandler {
    override fun getGotoDeclarationTargets(sourceElement: PsiElement?, offset: Int, editor: Editor?): Array<PsiElement>? {
        val file = sourceElement?.containingFile ?: return null
        val marker = file.language != TrionLanguage
        if (marker && !file.text.contains("trion: verifies")) return null
        val target = TrionResolver.targetAt(file.text, offset) ?: return null
        if (marker && target !is TrionTarget.Statement) return null
        val from = file.virtualFile?.onDisk() ?: return null
        val root = packageRoot(from)
        // This handler runs on the UI thread, also while the pointer moves with the key held:
        // it reads only what is already known, and the rest is read in the background.
        val cli = TrionCli.getInstance(file.project)
        val found = TrionResolver.locate(target, from, root, { cli.knownIndex(it) }) { root?.let { cli.knownGlossary(it) } ?: emptyList() } ?: return null
        return element(file.project, found.first, found.second)?.let { arrayOf(it) }
    }

    companion object {
        fun element(project: Project, file: File, offset: Int): PsiElement? {
            val virtual: VirtualFile = LocalFileSystem.getInstance().refreshAndFindFileByIoFile(file) ?: return null
            val psi = PsiManager.getInstance(project).findFile(virtual) ?: return null
            // A position names a line; the declaration starts at its first word.
            val text = psi.text
            var at = offset.coerceIn(0, (text.length - 1).coerceAtLeast(0))
            while (at < text.length - 1 && text[at].isWhitespace() && text[at] != '\n') at++
            return psi.findElementAt(at) ?: psi
        }
    }
}

/** Says what a term is and what a statement identifier stands for. */
class TrionDocumentationProvider : AbstractDocumentationProvider() {
    override fun getCustomDocumentationElement(editor: Editor, file: PsiFile, contextElement: PsiElement?, targetOffset: Int): PsiElement? =
        contextElement?.takeIf { file.language == TrionLanguage && TrionResolver.targetAt(file.text, targetOffset) != null }

    override fun generateDoc(element: PsiElement?, originalElement: PsiElement?): String? {
        val leaf = originalElement ?: element ?: return null
        val file = leaf.containingFile ?: return null
        return documentation(file, leaf.textRange.startOffset)
    }

    override fun generateHoverDoc(element: PsiElement, originalElement: PsiElement?): String? = generateDoc(element, originalElement)

    companion object {
        private fun escape(text: String) = TrionExternalAnnotator.escape(text)

        fun documentation(file: PsiFile, offset: Int): String? {
            val root = TrionResolver.root(file) ?: return null
            val cli = TrionCli.getInstance(file.project)
            return when (val target = TrionResolver.targetAt(file.text, offset)) {
                is TrionTarget.Statement -> cli.explain(root, target.id)?.let { "<pre>${escape(it)}</pre>" }
                is TrionTarget.Term -> TrionResolver.term(target, cli.glossary(root))?.let { termDocumentation(it) }
                else -> null
            }
        }

        fun termDocumentation(term: TrionTerm): String {
            val out = StringBuilder("<b>${escape(term.term)}</b> &mdash; ")
            out.append(
                when (term.status) {
                    "explicit" -> "defined term"
                    "declared" -> "declared term"
                    "primitive" -> "declared predicate"
                    "imported" -> "term of another namespace"
                    else -> "derived term: no definition or declaration states what it is"
                },
            )
            if (term.kinds.isNotEmpty()) out.append(" (${escape(term.kinds.joinToString(", "))})")
            term.definition?.let { out.append("<p>${escape(it)}</p>") }
            if (term.definition == null && term.rules.isNotEmpty()) {
                out.append("<p>Read from its use: ${escape(term.rules.joinToString("; "))}.</p>")
            }
            if (term.referenced.isNotEmpty()) out.append("<p>Refers to: ${escape(term.referenced.joinToString(", "))}</p>")
            term.definedAt?.let { out.append("<p>Defined at ${escape(it)}</p>") }
            term.declaredAt?.let { out.append("<p>Declared at ${escape(it)}</p>") }
            out.append("<p>${term.occurrences} use${if (term.occurrences == 1) "" else "s"}")
            term.firstUse?.let { out.append(", first at ${escape(it)}") }
            out.append("</p>")
            return out.toString()
        }
    }
}
