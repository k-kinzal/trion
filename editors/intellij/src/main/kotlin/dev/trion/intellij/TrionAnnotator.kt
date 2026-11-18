package dev.trion.intellij

import com.intellij.lang.annotation.AnnotationHolder
import com.intellij.lang.annotation.ExternalAnnotator
import com.intellij.lang.annotation.HighlightSeverity
import com.intellij.openapi.project.Project
import com.intellij.openapi.util.TextRange
import com.intellij.psi.PsiFile
import java.io.File

class TrionCheckRequest(val project: Project, val root: File, val relative: String, val text: String)

class TrionMark(val range: TextRange?, val severity: HighlightSeverity, val message: String, val tooltip: String)

/**
 * Shows what `trion check` says about the package of the file. The command reads the files
 * on disk, so the marks describe the saved text.
 */
class TrionExternalAnnotator : ExternalAnnotator<TrionCheckRequest, TrionReport>() {
    override fun collectInformation(file: PsiFile): TrionCheckRequest? {
        val disk = file.virtualFile?.onDisk() ?: return null
        val root = packageRoot(disk) ?: return null
        return TrionCheckRequest(file.project, root, disk.relativeTo(root).invariantSeparatorsPath, file.text)
    }

    override fun doAnnotate(request: TrionCheckRequest): TrionReport? {
        val cli = TrionCli.getInstance(request.project)
        val report = cli.check(request.root)
        // This runs in the background, so navigation finds the outlines and the glossary ready.
        cli.index(request.root)
        cli.glossary(request.root)
        return report
    }

    override fun apply(file: PsiFile, report: TrionReport?, holder: AnnotationHolder) {
        val request = collectInformation(file) ?: return
        for (mark in marks(report ?: return, request.relative, file.text)) {
            val builder = holder.newAnnotation(mark.severity, mark.message).tooltip(mark.tooltip)
            (if (mark.range != null) builder.range(mark.range) else builder.fileLevel()).create()
        }
    }

    companion object {
        /** The marks of one file: a banner that says whether the package holds, then one mark per place a diagnostic names. */
        fun marks(report: TrionReport, relative: String, text: String): List<TrionMark> {
            val out = ArrayList<TrionMark>()
            val failed = report.failure != null || report.errors > 0 || (report.verdict != null && report.verdict != "consistent")
            out.add(TrionMark(null, if (failed) HighlightSeverity.WARNING else HighlightSeverity.INFORMATION, report.summary(), report.summary()))
            for (diagnostic in report.diagnostics) {
                val severity = if (diagnostic.severity == "error") HighlightSeverity.ERROR else HighlightSeverity.WARNING
                for (ref in diagnostic.refs.filter { it.file == relative }) {
                    val range = lineRange(text, ref.line) ?: continue
                    val others = diagnostic.refs.filter { it !== ref }.joinToString("") { "<br>&nbsp;&nbsp;with ${escape(it.id)} (${escape(it.file)}:${it.line}): ${escape(it.text)}" }
                    val message = "${diagnostic.code}: ${diagnostic.message}"
                    out.add(TrionMark(range, severity, message, "<html><b>${escape(diagnostic.code)}</b>: ${escape(diagnostic.message)}$others</html>"))
                }
            }
            // Nothing that passes may be unread: a part without a formal reading and a statement
            // that constrains nothing are errors, marked on the part that the message names.
            for (diagnostic in report.opaque + report.ungrounded) {
                val ref = diagnostic.refs.firstOrNull { it.file == relative } ?: continue
                val range = namedPart(text, ref.line, diagnostic.message) ?: lineRange(text, ref.line) ?: continue
                out.add(TrionMark(range, HighlightSeverity.ERROR, "${diagnostic.code}: ${diagnostic.message}", "<html><b>${escape(diagnostic.code)}</b>: ${escape(diagnostic.message)}</html>"))
            }
            return out
        }

        /**
         * The part that a message names: the message begins with the part in backticks, and the
         * part is sought as whole words from the first line of the statement to the end of its sentence.
         */
        fun namedPart(text: String, line: Int, message: String): TextRange? {
            if (line < 1 || !message.startsWith("`")) return null
            val part = message.substring(1).substringBefore('`').ifEmpty { return null }
            val isWord = { c: Char -> c.isLetterOrDigit() || c == '-' || c == '_' }
            var start = TrionOutline.lineOffset(text, line - 1)
            repeat(12) {
                if (start < 0 || start >= text.length) return null
                val end = text.indexOf('\n', start).let { if (it < 0) text.length else it }
                var from = start
                while (true) {
                    val found = text.indexOf(part, from)
                    if (found < 0 || found + part.length > end) break
                    val before = found > start && isWord(text[found - 1])
                    val after = found + part.length < end && isWord(text[found + part.length])
                    if (!before && !after) return TextRange(found, found + part.length)
                    from = found + part.length
                }
                if (text.substring(start, end).trimEnd().endsWith(".")) return null
                start = end + 1
            }
            return null
        }

        /** The text of a 1-based line without its indentation. */
        fun lineRange(text: String, line: Int): TextRange? {
            if (line < 1) return null
            val start = TrionOutline.lineOffset(text, line - 1)
            if (start < 0 || start > text.length) return null
            val end = text.indexOf('\n', start).let { if (it < 0) text.length else it }
            val content = text.substring(start, end)
            val indent = content.length - content.trimStart().length
            return if (content.isBlank()) null else TextRange(start + indent, start + content.trimEnd().length)
        }

        fun escape(text: String): String = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    }
}
