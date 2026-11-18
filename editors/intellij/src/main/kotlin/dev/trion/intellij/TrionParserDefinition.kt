package dev.trion.intellij

import com.intellij.extapi.psi.PsiFileBase
import com.intellij.lang.ASTNode
import com.intellij.lang.BracePair
import com.intellij.lang.PairedBraceMatcher
import com.intellij.lang.ParserDefinition
import com.intellij.lang.PsiParser
import com.intellij.lexer.Lexer
import com.intellij.openapi.fileTypes.FileType
import com.intellij.openapi.project.Project
import com.intellij.psi.FileViewProvider
import com.intellij.psi.PsiElement
import com.intellij.psi.PsiFile
import com.intellij.psi.tree.IElementType
import com.intellij.psi.tree.IFileElementType
import com.intellij.psi.tree.TokenSet

private val FILE = IFileElementType(TrionLanguage)

class TrionFile(viewProvider: FileViewProvider) : PsiFileBase(viewProvider, TrionLanguage) {
    override fun getFileType(): FileType = TrionFileType
}

/**
 * Gives `.trion` files a flat PSI tree of tokens. The `trion` command owns the sentence
 * grammar; the plugin reads the line structure itself (see [TrionOutline]).
 */
class TrionParserDefinition : ParserDefinition {
    override fun createLexer(project: Project?): Lexer = TrionLexer()

    override fun createParser(project: Project?): PsiParser = PsiParser { root, builder ->
        val marker = builder.mark()
        while (!builder.eof()) {
            builder.advanceLexer()
        }
        marker.done(root)
        builder.treeBuilt
    }

    override fun getFileNodeType(): IFileElementType = FILE

    override fun getCommentTokens(): TokenSet = TokenSet.create(TrionTokens.COMMENT)

    override fun getStringLiteralElements(): TokenSet = TokenSet.create(TrionTokens.STRING, TrionTokens.RAW_STRING)

    override fun createElement(node: ASTNode): PsiElement =
        throw UnsupportedOperationException("The trion PSI tree has no composite elements: ${node.elementType}")

    override fun createFile(viewProvider: FileViewProvider): PsiFile = TrionFile(viewProvider)
}

/** The language has no bracket tokens to pair: `[ID]` is one token. Quotes pair through the quote handler. */
class TrionBraceMatcher : PairedBraceMatcher {
    override fun getPairs(): Array<BracePair> = emptyArray()

    override fun isPairedBracesAllowedBeforeType(lbraceType: IElementType, contextType: IElementType?): Boolean = true

    override fun getCodeConstructStart(file: PsiFile?, openingBraceOffset: Int): Int = openingBraceOffset
}
