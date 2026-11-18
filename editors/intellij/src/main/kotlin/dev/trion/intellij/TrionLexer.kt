package dev.trion.intellij

import com.intellij.lexer.LexerBase
import com.intellij.psi.TokenType
import com.intellij.psi.tree.IElementType

class TrionTokenType(name: String) : IElementType(name, TrionLanguage)

object TrionTokens {
    @JvmField val COMMENT = TrionTokenType("COMMENT")
    @JvmField val STRING = TrionTokenType("STRING")
    @JvmField val RAW_STRING = TrionTokenType("RAW_STRING")
    @JvmField val LITERAL = TrionTokenType("LITERAL")
    @JvmField val SPEC_ID = TrionTokenType("SPEC_ID")
    @JvmField val DIRECTIVE = TrionTokenType("DIRECTIVE")
    @JvmField val NAME = TrionTokenType("NAME")
    @JvmField val REFERENCE = TrionTokenType("REFERENCE")
    @JvmField val CONDITION = TrionTokenType("CONDITION")
    @JvmField val MODAL = TrionTokenType("MODAL")
    @JvmField val DEFINER = TrionTokenType("DEFINER")
    @JvmField val VARIABLE = TrionTokenType("VARIABLE")
    @JvmField val NUMBER = TrionTokenType("NUMBER")
    @JvmField val UNIT = TrionTokenType("UNIT")
    @JvmField val QUALIFIED = TrionTokenType("QUALIFIED")
    @JvmField val WORD = TrionTokenType("WORD")
    @JvmField val PUNCTUATION = TrionTokenType("PUNCTUATION")
    @JvmField val BAD = TrionTokenType("BAD")
}

/** What the first word of a line declares, and the shape the rest of the line must have. */
internal object TrionLines {
    private const val ID = "[A-Z][A-Z0-9-]*(?:/[a-z][a-z0-9-]*)?"
    private const val DOTTED = "[a-z][a-z0-9-]*(?:\\.[a-z][a-z0-9-]*)*"
    private val shapes: Map<String, Regex> = mapOf(
        "package" to Regex("$DOTTED\\s+edition\\s+\".*"),
        "include" to Regex("\".*"),
        "namespace" to Regex("$DOTTED\\s*:?"),
        "use" to Regex(DOTTED),
        "section" to Regex("\".*\"\\s*:?"),
        "note" to Regex("\".*"),
        "ref" to Regex("\\[.*"),
        "source" to Regex("$ID\\s*:?"),
        "check" to Regex("$ID\\s*:"),
        "example" to Regex("$ID\\s*:"),
        "trace" to Regex("$ID\\s*:"),
        "role" to Regex("\\S+\\s*:"),
        "cite" to Regex("$ID(?:#$ID)?"),
        "unsourced" to Regex("\".*"),
        "ratified" to Regex("by\\s.*"),
        "term" to Regex("[^:]+:\\s*\\S+"),
        "alias" to Regex(".+ = .+"),
        "bind" to Regex(".+"),
        "extend" to Regex(".+ with .+"),
        "classify" to Regex(".+"),
        "predicate" to Regex("[a-z][a-z0-9-]*\\(.*\\)"),
        "primitive" to Regex("[A-Za-z].*[^.:]|[A-Za-z]"),
        // The population whose shares statements may bound: a name of at most four words.
        "measure" to Regex("[A-Za-z][A-Za-z0-9-]*(?:\\s+[A-Za-z][A-Za-z0-9-]*){0,3}"),
        "detailed" to Regex("by\\s+\\[.*"),
        // How a statement ranks against the statements that conflict with it.
        "overrides" to Regex("\\[.*"),
        "default" to Regex(""),
        "weight" to Regex("[0-9]+"),
        // Who controls an actor. A name is a few words; a wrapped sentence line is longer or ends a sentence.
        "environment" to Regex("[A-Za-z][A-Za-z0-9-]*(?:\\s+[A-Za-z][A-Za-z0-9-]*){0,2}"),
        "system" to Regex("[A-Za-z][A-Za-z0-9-]*(?:\\s+[A-Za-z][A-Za-z0-9-]*){0,2}"),
        "compatibility" to Regex("$ID\\s*:"),
        "element" to Regex("\".*"),
        "types" to Regex("\".*"),
        "expansion" to Regex("\".*"),
        "preserves" to Regex("\".*"),
        "concept" to Regex(":"),
        "diagram" to Regex("(?:kind\\s+)?\\S+\\s*:"),
        "step" to Regex("[a-z][a-z0-9-]*\\s*:.*"),
        "start" to Regex("[a-z][a-z0-9-]*"),
        "finish" to Regex("[a-z][a-z0-9-]*(?:\\s*,\\s*[a-z][a-z0-9-]*)*"),
        "choose" to Regex("after\\s+[a-z][a-z0-9-]*\\s*:"),
        "when" to Regex(".*->\\s*[a-z][a-z0-9-]*"),
        "otherwise" to Regex("->\\s*[a-z][a-z0-9-]*"),
        "title" to Regex("\".*"),
        "locator" to Regex("\".*"),
        "kind" to Regex("[a-z-]+"),
        "path" to Regex("\".*"),
        "sha256" to Regex("\".*"),
        "revision" to Regex("\".*"),
        "select" to Regex("\".*"),
        "retrieved" to Regex("\\S.*"),
        "transcript" to Regex("first|any"),
        "minimum" to Regex("[0-9.]+%?"),
        "quote" to Regex("$ID\\s+\".*"),
        "form" to Regex("[a-z-]+|$ID\\s*:.*|[A-Z][A-Za-z-]*"),
        "input" to Regex("\".*"),
        "base" to Regex("\".*"),
        "candidate" to Regex("\".*"),
        "using" to Regex("definitions"),
        "expect" to Regex("\\S.*"),
        "left" to Regex("\\[.*"),
        "right" to Regex("\\[.*"),
        "relation" to Regex("[a-z-]+"),
        "statements" to Regex("\\[.*"),
        "verifies" to Regex("\\S.*"),
        "artifact" to Regex("\".*"),
        "activate" to Regex(":.*"),
        "required" to Regex("$ID\\s*:.*"),
    )

    /** The declaring word of a line, when the rest of the line has its shape. */
    fun directive(line: CharSequence): String? {
        val text = stripComment(line).trim()
        val word = text.takeWhile { it.isLetterOrDigit() }
        val shape = shapes[word] ?: return null
        val rest = text.substring(word.length)
        if (rest.isNotEmpty() && !rest[0].isWhitespace() && rest[0] != ':') {
            return null
        }
        return if (shape.matches(rest.trim())) word else null
    }

    /** The line without a trailing `//` comment that stands outside strings and literals. */
    fun stripComment(line: CharSequence): String {
        var inString = false
        var inLiteral = false
        var i = 0
        while (i < line.length) {
            val c = line[i]
            when {
                inString -> if (c == '\\') i++ else if (c == '"') inString = false
                inLiteral -> if (c == '`') inLiteral = false
                c == '"' -> inString = true
                c == '`' -> inLiteral = true
                c == '/' && i + 1 < line.length && line[i + 1] == '/' -> return line.substring(0, i)
            }
            i++
        }
        return line.toString()
    }

    /** Whether the line opens a block: its code ends with a colon. */
    fun opensBlock(line: CharSequence): Boolean = stripComment(line).trimEnd().endsWith(":")
}

private val CONDITIONS = setOf(
    "when", "while", "where", "if", "then", "unless", "otherwise", "after", "once", "upon", "before", "during", "until",
    "for", "each", "only", "exactly",
)
private val OPENERS = setOf("When", "While", "Where", "If", "After", "Once", "Upon", "Before", "During", "Until", "On")
private val MODALS = setOf("shall", "must", "should", "may")
private val UNITS = setOf(
    "ms", "s", "seconds", "second", "minutes", "minute", "hours", "hour", "days", "day", "bytes", "kb", "mb", "gb", "percent", "times",
)

/**
 * The lexer of record for highlighting. It reads a line the way the parser does: a line whose
 * first word declares something is a declaration, and every other line is sentence text.
 * State 1 means the position is inside a raw string.
 */
class TrionLexer : LexerBase() {
    private var buffer: CharSequence = ""
    private var end = 0
    private var tokenStart = 0
    private var tokenEnd = 0
    private var type: IElementType? = null
    private var inRaw = false
    private var rawAfter = false

    override fun start(buffer: CharSequence, startOffset: Int, endOffset: Int, initialState: Int) {
        this.buffer = buffer
        end = endOffset
        tokenStart = startOffset
        tokenEnd = startOffset
        inRaw = initialState == 1
        advance()
    }

    override fun getState(): Int = if (rawAfter) 1 else 0

    override fun getTokenType(): IElementType? = type

    override fun getTokenStart(): Int = tokenStart

    override fun getTokenEnd(): Int = tokenEnd

    override fun getBufferSequence(): CharSequence = buffer

    override fun getBufferEnd(): Int = end

    override fun advance() {
        tokenStart = tokenEnd
        if (tokenStart >= end) {
            type = null
            rawAfter = inRaw
            return
        }
        type = next()
        rawAfter = inRaw
    }

    private fun at(text: String, offset: Int = tokenStart): Boolean =
        offset + text.length <= end && buffer.subSequence(offset, offset + text.length).toString() == text

    private fun lineStart(offset: Int): Int {
        var i = offset
        while (i > 0 && buffer[i - 1] != '\n') i--
        return i
    }

    private fun lineEnd(offset: Int): Int {
        var i = offset
        while (i < end && buffer[i] != '\n') i++
        return i
    }

    private fun next(): IElementType {
        val c = buffer[tokenStart]
        if (inRaw) {
            var i = tokenStart
            while (i < end && !at("\"\"\"", i)) i++
            if (i < end) {
                i += 3
                inRaw = false
            }
            tokenEnd = i
            return TrionTokens.RAW_STRING
        }
        if (c.isWhitespace()) {
            var i = tokenStart
            while (i < end && buffer[i].isWhitespace()) i++
            tokenEnd = i
            return TokenType.WHITE_SPACE
        }
        if (at("//")) {
            tokenEnd = lineEnd(tokenStart)
            return TrionTokens.COMMENT
        }
        if (at("\"\"\"")) {
            var i = tokenStart + 3
            while (i < end && !at("\"\"\"", i)) i++
            if (i < end) i += 3 else inRaw = true
            tokenEnd = i
            return TrionTokens.RAW_STRING
        }
        if (c == '"') {
            var i = tokenStart + 1
            while (i < end && buffer[i] != '"' && buffer[i] != '\n') {
                if (buffer[i] == '\\' && i + 1 < end && buffer[i + 1] != '\n') i++
                i++
            }
            if (i < end && buffer[i] == '"') i++
            tokenEnd = i
            return TrionTokens.STRING
        }
        if (c == '`') {
            var i = tokenStart + 1
            while (i < end && buffer[i] != '`' && buffer[i] != '\n') i++
            if (i < end && buffer[i] == '`') i++
            tokenEnd = i
            return TrionTokens.LITERAL
        }
        if (c == '[') {
            var i = tokenStart + 1
            while (i < end && (buffer[i].isLetterOrDigit() || buffer[i] == '-' || buffer[i] == '/')) i++
            if (i < end && buffer[i] == ']' && i > tokenStart + 1) {
                tokenEnd = i + 1
                return TrionTokens.SPEC_ID
            }
            tokenEnd = tokenStart + 1
            return TrionTokens.PUNCTUATION
        }
        if (at("->")) {
            tokenEnd = tokenStart + 2
            return TrionTokens.PUNCTUATION
        }
        if (c.isDigit() || (c == '-' && tokenStart + 1 < end && buffer[tokenStart + 1].isDigit() && !wordBefore())) {
            var i = tokenStart + 1
            while (i < end && (buffer[i].isDigit() || ((buffer[i] == '.' || buffer[i] == ',') && i + 1 < end && buffer[i + 1].isDigit()))) i++
            if (i < end && buffer[i] == '%') i++
            if (!wordBefore() && (i >= end || !isWordChar(buffer[i]))) {
                tokenEnd = i
                return TrionTokens.NUMBER
            }
            // `500ms`: the number, then the unit as its own token.
            val unitEnd = wordEnd(i)
            if (!wordBefore() && buffer.subSequence(i, unitEnd).toString().lowercase() in UNITS) {
                tokenEnd = i
                return TrionTokens.NUMBER
            }
        }
        if (isWordChar(c)) {
            return word()
        }
        tokenEnd = tokenStart + 1
        return if (c in ".,;:()#=/*+<>!?%]{}'|&^$@~-\\") TrionTokens.PUNCTUATION else TrionTokens.BAD
    }

    private fun isWordChar(c: Char): Boolean = c.isLetterOrDigit() || c == '_'

    private fun wordBefore(): Boolean = tokenStart > 0 && (isWordChar(buffer[tokenStart - 1]) || buffer[tokenStart - 1] == '-')

    private fun wordEnd(from: Int): Int {
        var i = from
        while (i < end) {
            val c = buffer[i]
            val joins = (c == '-' || c == '.' || c == '\'') && i + 1 < end && isWordChar(buffer[i + 1])
            val qualifies = c == ':' && i + 2 < end && buffer[i + 1] == ':' && isWordChar(buffer[i + 2])
            when {
                isWordChar(c) || joins -> i++
                qualifies -> i += 2
                else -> break
            }
        }
        return i
    }

    private fun word(): IElementType {
        tokenEnd = wordEnd(tokenStart)
        val text = buffer.subSequence(tokenStart, tokenEnd).toString()
        val start = lineStart(tokenStart)
        val line = buffer.subSequence(start, lineEnd(tokenStart))
        val before = buffer.subSequence(start, tokenStart).toString()
        val first = before.isBlank()
        val directive = TrionLines.directive(line)
        if (directive != null) {
            val head = before.trim().split(Regex("\\s+")).filter { it.isNotEmpty() }
            return when {
                first -> TrionTokens.DIRECTIVE
                directive == "package" && text == "edition" -> TrionTokens.DIRECTIVE
                directive == "ratified" && (text == "by" || text == "on") -> TrionTokens.DIRECTIVE
                directive == "choose" && text == "after" -> TrionTokens.DIRECTIVE
                directive == "extend" && text == "with" -> TrionTokens.DIRECTIVE
                directive == "detailed" && text == "by" -> TrionTokens.DIRECTIVE
                directive == "diagram" && text == "kind" && head.size == 1 -> TrionTokens.DIRECTIVE
                directive == "diagram" && head.size == 2 && head[1] == "kind" -> TrionTokens.NAME
                directive == "using" -> TrionTokens.DIRECTIVE
                directive == "primitive" || directive == "measure" || directive == "environment" || directive == "system" -> TrionTokens.NAME
                directive in setOf("cite", "verifies", "left", "right", "statements", "ref", "detailed", "overrides") -> TrionTokens.REFERENCE
                head.size == 1 && directive in setOf("namespace", "use", "source", "check", "example", "trace", "role", "quote", "package", "predicate", "step", "start", "finish", "required", "compatibility", "diagram") -> TrionTokens.NAME
                directive == "form" && head.size == 1 && text[0].isUpperCase() -> TrionTokens.NAME
                directive in setOf("activate", "form", "required", "step", "when") -> sentenceWord(text, before)
                else -> TrionTokens.WORD
            }
        }
        return sentenceWord(text, before)
    }

    private fun sentenceWord(text: String, before: String): IElementType {
        val lower = text.lowercase()
        val previous = before.trimEnd().substringAfterLast(' ').lowercase()
        return when {
            text.contains("::") -> TrionTokens.QUALIFIED
            lower in MODALS -> TrionTokens.MODAL
            (lower == "not" || lower == "never") && previous in MODALS -> TrionTokens.MODAL
            text == "means" -> TrionTokens.DEFINER
            text in OPENERS || text == "For" -> TrionTokens.CONDITION
            lower in CONDITIONS && text == lower && conditionWord(lower, previous) -> TrionTokens.CONDITION
            lower in UNITS && text == lower && before.trimEnd().lastOrNull()?.isDigit() == true -> TrionTokens.UNIT
            isVariable(text) && !(text == "A" && articleFollows()) -> TrionTokens.VARIABLE
            else -> TrionTokens.WORD
        }
    }

    /** `each` and `for` are condition words only in `For each`; `only` and `exactly` only before `when`. */
    private fun conditionWord(lower: String, previous: String): Boolean = when (lower) {
        "each" -> previous == "for"
        "for" -> false
        "only", "exactly" -> buffer.subSequence(tokenEnd, minOf(end, tokenEnd + 7)).toString().let { it.startsWith(" when") || it.startsWith(" where") || it.startsWith(" if") }
        "before", "after", "once", "upon", "during", "until" -> false
        else -> true
    }

    private fun isVariable(text: String): Boolean =
        text.isNotEmpty() && text[0] in 'A'..'Z' && text.drop(1).all { it.isDigit() }

    private fun articleFollows(): Boolean =
        tokenEnd + 1 < end && buffer[tokenEnd] == ' ' && buffer[tokenEnd + 1].isLowerCase()
}
