package dev.trion.intellij

import com.intellij.ide.structureView.StructureViewBuilder
import com.intellij.ide.structureView.StructureViewModel
import com.intellij.ide.structureView.StructureViewModelBase
import com.intellij.ide.structureView.StructureViewTreeElement
import com.intellij.ide.structureView.TreeBasedStructureViewBuilder
import com.intellij.ide.util.treeView.smartTree.TreeElement
import com.intellij.icons.AllIcons
import com.intellij.lang.ASTNode
import com.intellij.lang.PsiStructureViewFactory
import com.intellij.lang.folding.FoldingBuilderEx
import com.intellij.lang.folding.FoldingDescriptor
import com.intellij.navigation.ItemPresentation
import com.intellij.openapi.editor.Document
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.fileEditor.OpenFileDescriptor
import com.intellij.openapi.project.DumbAware
import com.intellij.openapi.util.TextRange
import com.intellij.psi.PsiElement
import com.intellij.psi.PsiFile
import javax.swing.Icon

/** Folds each block over the lines indented under its header, and each flat header to the next one. */
class TrionFoldingBuilder : FoldingBuilderEx(), DumbAware {
    override fun buildFoldRegions(root: PsiElement, document: Document, quick: Boolean): Array<FoldingDescriptor> =
        regions(document.text).map { (range, placeholder) -> FoldingDescriptor(root.node, range, null, placeholder) }.toTypedArray()

    override fun getPlaceholderText(node: ASTNode): String = "..."

    override fun isCollapsedByDefault(node: ASTNode): Boolean = false

    companion object {
        /** The fold ranges of a text with their placeholders: from the end of a header line to the end of its block. */
        fun regions(text: String): List<Pair<TextRange, String>> = TrionOutline.entries(text)
            .mapNotNull { entry ->
                val headerEnd = text.indexOf('\n', entry.start).let { if (it < 0) text.length else it }
                if (entry.end > headerEnd + 1) TextRange(headerEnd, entry.end) to " ..." else null
            }
    }
}

class TrionStructureViewFactory : PsiStructureViewFactory {
    override fun getStructureViewBuilder(psiFile: PsiFile): StructureViewBuilder = object : TreeBasedStructureViewBuilder() {
        override fun createStructureViewModel(editor: Editor?): StructureViewModel =
            StructureViewModelBase(psiFile, editor, TrionStructureElement(psiFile, null))
    }
}

/** A node of the structure view: the file, a namespace, a section, a declaration block or an identified statement. */
class TrionStructureElement(private val file: PsiFile, private val entry: OutlineEntry?) : StructureViewTreeElement, ItemPresentation {
    override fun getValue(): Any = entry ?: file

    override fun getPresentation(): ItemPresentation = this

    override fun getPresentableText(): String = when {
        entry == null -> file.name
        entry.kind == "statement" -> "[${entry.name}]"
        entry.kind == "section" -> entry.name
        else -> "${entry.kind} ${entry.name}"
    }

    override fun getIcon(unused: Boolean): Icon? = when (entry?.kind) {
        null -> TrionFileType.icon
        "namespace" -> AllIcons.Nodes.Package
        "section" -> AllIcons.Nodes.Folder
        "statement" -> AllIcons.Nodes.Property
        else -> AllIcons.Nodes.Tag
    }

    override fun getChildren(): Array<TreeElement> = children(file, entry).map { TrionStructureElement(file, it) }.toTypedArray()

    override fun navigate(requestFocus: Boolean) {
        val virtual = file.virtualFile ?: return
        OpenFileDescriptor(file.project, virtual, entry?.start ?: 0).navigate(requestFocus)
    }

    override fun canNavigate(): Boolean = file.virtualFile != null

    override fun canNavigateToSource(): Boolean = canNavigate()

    companion object {
        private val shown = setOf("namespace", "section", "source", "check", "example", "trace", "role", "compatibility", "diagram kind", "primitive", "measure", "predicate", "environment", "system", "statement")

        /** The entries directly inside [parent]: those it encloses that no nearer shown entry encloses. */
        fun children(file: PsiFile, parent: OutlineEntry?): List<OutlineEntry> {
            val entries = TrionOutline.entries(file.text).filter { it.kind in shown }
            val inside = { outer: OutlineEntry?, inner: OutlineEntry -> outer == null || (inner !== outer && inner.start > outer.start && inner.start < outer.end) }
            return entries.filter { candidate ->
                parent != candidate && inside(parent, candidate) && entries.none { between -> between != candidate && between != parent && inside(parent, between) && inside(between, candidate) }
            }
        }
    }
}
