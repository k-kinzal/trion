package dev.trion.intellij

import com.intellij.lexer.Lexer
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors as Default
import com.intellij.openapi.editor.HighlighterColors
import com.intellij.openapi.editor.colors.TextAttributesKey
import com.intellij.openapi.editor.colors.TextAttributesKey.createTextAttributesKey
import com.intellij.openapi.fileTypes.SyntaxHighlighter
import com.intellij.openapi.fileTypes.SyntaxHighlighterBase
import com.intellij.openapi.fileTypes.SyntaxHighlighterFactory
import com.intellij.openapi.options.colors.AttributesDescriptor
import com.intellij.openapi.options.colors.ColorDescriptor
import com.intellij.openapi.options.colors.ColorSettingsPage
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.psi.tree.IElementType
import javax.swing.Icon

object TrionColors {
    val COMMENT = createTextAttributesKey("TRION_COMMENT", Default.LINE_COMMENT)
    val STRING = createTextAttributesKey("TRION_STRING", Default.STRING)
    val RAW_STRING = createTextAttributesKey("TRION_RAW_STRING", Default.STRING)
    val LITERAL = createTextAttributesKey("TRION_LITERAL", Default.CONSTANT)
    val SPEC_ID = createTextAttributesKey("TRION_SPEC_ID", Default.METADATA)
    val DIRECTIVE = createTextAttributesKey("TRION_DIRECTIVE", Default.KEYWORD)
    val NAME = createTextAttributesKey("TRION_NAME", Default.CLASS_NAME)
    val REFERENCE = createTextAttributesKey("TRION_REFERENCE", Default.CLASS_REFERENCE)
    val CONDITION = createTextAttributesKey("TRION_CONDITION", Default.KEYWORD)
    val MODAL = createTextAttributesKey("TRION_MODAL", Default.KEYWORD)
    val DEFINER = createTextAttributesKey("TRION_DEFINER", Default.KEYWORD)
    val VARIABLE = createTextAttributesKey("TRION_VARIABLE", Default.LOCAL_VARIABLE)
    val NUMBER = createTextAttributesKey("TRION_NUMBER", Default.NUMBER)
    val UNIT = createTextAttributesKey("TRION_UNIT", Default.NUMBER)
    val QUALIFIED = createTextAttributesKey("TRION_QUALIFIED", Default.STATIC_FIELD)
    val PUNCTUATION = createTextAttributesKey("TRION_PUNCTUATION", Default.OPERATION_SIGN)
    val BAD = createTextAttributesKey("TRION_BAD_CHARACTER", HighlighterColors.BAD_CHARACTER)

    val byToken: Map<IElementType, TextAttributesKey> = mapOf(
        TrionTokens.COMMENT to COMMENT,
        TrionTokens.STRING to STRING,
        TrionTokens.RAW_STRING to RAW_STRING,
        TrionTokens.LITERAL to LITERAL,
        TrionTokens.SPEC_ID to SPEC_ID,
        TrionTokens.DIRECTIVE to DIRECTIVE,
        TrionTokens.NAME to NAME,
        TrionTokens.REFERENCE to REFERENCE,
        TrionTokens.CONDITION to CONDITION,
        TrionTokens.MODAL to MODAL,
        TrionTokens.DEFINER to DEFINER,
        TrionTokens.VARIABLE to VARIABLE,
        TrionTokens.NUMBER to NUMBER,
        TrionTokens.UNIT to UNIT,
        TrionTokens.QUALIFIED to QUALIFIED,
        TrionTokens.PUNCTUATION to PUNCTUATION,
        TrionTokens.BAD to BAD,
    )
}

class TrionSyntaxHighlighter : SyntaxHighlighterBase() {
    override fun getHighlightingLexer(): Lexer = TrionLexer()

    override fun getTokenHighlights(tokenType: IElementType?): Array<TextAttributesKey> =
        pack(TrionColors.byToken[tokenType])
}

class TrionSyntaxHighlighterFactory : SyntaxHighlighterFactory() {
    override fun getSyntaxHighlighter(project: Project?, virtualFile: VirtualFile?): SyntaxHighlighter = TrionSyntaxHighlighter()
}

class TrionColorSettingsPage : ColorSettingsPage {
    override fun getDisplayName(): String = "Trion"

    override fun getIcon(): Icon = TrionFileType.icon

    override fun getHighlighter(): SyntaxHighlighter = TrionSyntaxHighlighter()

    override fun getAdditionalHighlightingTagToDescriptorMap(): Map<String, TextAttributesKey>? = null

    override fun getColorDescriptors(): Array<ColorDescriptor> = ColorDescriptor.EMPTY_ARRAY

    override fun getAttributeDescriptors(): Array<AttributesDescriptor> = arrayOf(
        AttributesDescriptor("Comment", TrionColors.COMMENT),
        AttributesDescriptor("String", TrionColors.STRING),
        AttributesDescriptor("Raw string", TrionColors.RAW_STRING),
        AttributesDescriptor("Literal in backticks", TrionColors.LITERAL),
        AttributesDescriptor("Statement identifier", TrionColors.SPEC_ID),
        AttributesDescriptor("Declaration keyword", TrionColors.DIRECTIVE),
        AttributesDescriptor("Declared name", TrionColors.NAME),
        AttributesDescriptor("Reference to a source or a statement", TrionColors.REFERENCE),
        AttributesDescriptor("Condition keyword", TrionColors.CONDITION),
        AttributesDescriptor("Modal verb", TrionColors.MODAL),
        AttributesDescriptor("Definition verb", TrionColors.DEFINER),
        AttributesDescriptor("Variable", TrionColors.VARIABLE),
        AttributesDescriptor("Number", TrionColors.NUMBER),
        AttributesDescriptor("Unit", TrionColors.UNIT),
        AttributesDescriptor("Qualified term", TrionColors.QUALIFIED),
        AttributesDescriptor("Punctuation", TrionColors.PUNCTUATION),
    )

    override fun getDemoText(): String = """
        // The rooms of a chat service.
        package chat
        include "rooms/members.trion"

        namespace chat.room:
            use grpc
            cite R#ROOMS

            source R:
                title "The first request"
                locator "requirements/first.txt"
                quote ROOMS ${"\"\"\""}
        A room is private or public.
        ${"\"\"\""}

            section "Room types":
                A room means a place where members exchange messages.
                Each room has exactly one owner.

                [ROOM-KINDS]
                The room type is `private` or `public`.

                For each room R:
                    [ROOM-JOIN]
                    When a member M joins R, the service shall notify
                    the owner of R within 500 ms unless R is archived.

                [ROOM-CLOSE]
                If the owner leaves, then the service shall not delete grpc::message history.
    """.trimIndent()
}
