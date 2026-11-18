package dev.trion.intellij

import com.intellij.icons.AllIcons
import com.intellij.lang.Commenter
import com.intellij.lang.Language
import com.intellij.openapi.fileTypes.LanguageFileType
import com.intellij.openapi.util.IconLoader
import javax.swing.Icon

object TrionLanguage : Language("Trion") {
    private fun readResolve(): Any = TrionLanguage
}

object TrionFileType : LanguageFileType(TrionLanguage) {
    private val fileIcon: Icon by lazy {
        IconLoader.findIcon("/icons/trion.svg", TrionFileType::class.java.classLoader) ?: AllIcons.FileTypes.Text
    }

    override fun getName(): String = "Trion"

    override fun getDescription(): String = "Trion specification"

    override fun getDefaultExtension(): String = "trion"

    override fun getIcon(): Icon = fileIcon
}

/** A trion comment runs from `//` to the end of the line; the language has no block comments. */
class TrionCommenter : Commenter {
    override fun getLineCommentPrefix(): String = "// "

    override fun getBlockCommentPrefix(): String? = null

    override fun getBlockCommentSuffix(): String? = null

    override fun getCommentedBlockCommentPrefix(): String? = null

    override fun getCommentedBlockCommentSuffix(): String? = null
}

/** Typing a quote closes it; typing over the closing quote steps past it. */
class TrionQuoteHandler : com.intellij.codeInsight.editorActions.SimpleTokenSetQuoteHandler(TrionTokens.STRING, TrionTokens.LITERAL)
