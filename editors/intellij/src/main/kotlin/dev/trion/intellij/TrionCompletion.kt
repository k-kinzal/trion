package dev.trion.intellij

import com.intellij.codeInsight.completion.CompletionContributor
import com.intellij.codeInsight.completion.CompletionParameters
import com.intellij.codeInsight.completion.CompletionResultSet
import com.intellij.codeInsight.lookup.LookupElementBuilder

/**
 * Completes the words that the language fixes: the word that opens a line, the kind of an
 * example or a source, and the expectation of an example. It reads the text only, so it runs
 * no command; terms come from the language server where LSP4IJ is installed.
 */
class TrionCompletionContributor : CompletionContributor() {
    override fun fillCompletionVariants(parameters: CompletionParameters, result: CompletionResultSet) {
        if (parameters.originalFile.language != TrionLanguage) return
        val text = parameters.editor.document.charsSequence
        val offset = parameters.offset.coerceIn(0, text.length)
        val start = text.lastIndexOf('\n', (offset - 1).coerceAtLeast(0)).let { if (offset == 0) 0 else it + 1 }
        val before = text.subSequence(start.coerceAtMost(offset), offset).toString()
        val (prefix, words) = TrionCompletion.candidates(before)
        val set = result.withPrefixMatcher(prefix)
        for (word in words) {
            set.addElement(LookupElementBuilder.create(word).withTypeText(TrionCompletion.describe(word), true))
        }
    }
}

object TrionCompletion {
    /** Words that open a line of the file, a block or a namespace. */
    val openers = listOf(
        "package", "include", "namespace", "use", "section", "ref", "source", "check", "example", "trace", "role",
        "term", "predicate", "primitive", "measure", "environment", "system", "alias", "bind", "extend", "classify",
        "diagram", "diagram kind", "compatibility", "concept",
    )

    /** Lines that stand under a statement and say how it relates to sources and to other statements. */
    val annotations = listOf("cite", "unsourced", "ratified by", "detailed by", "overrides", "default", "weight")

    /** Fields of a source, a check, an example, a trace, a flow, a diagram kind and a compatibility block. */
    val fields = listOf(
        "title", "locator", "kind", "path", "sha256", "revision", "select", "retrieved", "transcript", "minimum", "quote",
        "relation", "left", "right", "using definitions", "statements", "form", "input", "base", "candidate", "expect",
        "artifact", "verifies", "step", "start", "finish", "choose after", "when", "otherwise",
        "element", "types", "expansion", "preserves", "activate:", "required",
    )

    /** Words that open a sentence or a shared context. */
    val frames = listOf("Where", "While", "When", "If", "For each", "Each", "The", "No", "There is")

    /** What may follow `kind`: the kinds of an example and of a source. */
    val kinds = listOf("syntax", "comparison", "consistency", "code-trace", "reading", "requirement", "citation")

    /** What may follow `expect`, beside the quoted lines of a reading example. */
    val expectations = listOf("accepted", "rejected", "consistent", "inconsistent", "conflict", "redundant", "extension", "base-inconsistent")

    private val described = mapOf(
        "primitive" to "a term whose meaning is the statements about it",
        "measure" to "a population whose shares statements bound",
        "environment" to "an actor that the environment controls",
        "system" to "an actor that the system controls",
        "detailed by" to "the statements that detail this one",
        "overrides" to "the statements that this one wins against",
        "default" to "this statement yields to a more specific one",
        "weight" to "the weight of a recommendation",
        "reading" to "an example that states the expected reading",
    )

    fun describe(word: String): String = described[word] ?: ""

    /** The typed prefix and the words that may stand there, for the text of the line before the caret. */
    fun candidates(before: String): Pair<String, List<String>> {
        val line = before.trimStart()
        val after = { word: String -> line.startsWith("$word ") }
        return when {
            after("kind") -> line.removePrefix("kind").trimStart() to kinds
            after("expect") -> line.removePrefix("expect").trimStart() to expectations
            after("transcript") -> line.removePrefix("transcript").trimStart() to listOf("first", "any")
            after("relation") -> line.removePrefix("relation").trimStart() to listOf("equivalent")
            // Only the first words of a line are fixed; inside a sentence the words are the author's.
            line.count { it == ' ' } <= 1 -> line to openers + annotations + fields + frames
            else -> line to emptyList()
        }
    }
}
