package dev.trion.intellij

/** One line that structures a file: a block header, a flat header or an identified statement. */
data class OutlineEntry(
    val kind: String,
    val name: String,
    val line: Int,
    val indent: Int,
    val start: Int,
    /** The offset just past the last line that belongs to the entry. */
    val end: Int,
    val depth: Int,
)

/**
 * The line structure of a file, read the way the parser reads it: a block holds the lines
 * indented more than its header, and a flat namespace or section runs to the next one.
 */
object TrionOutline {
    private class Line(val number: Int, val start: Int, val end: Int, val text: String, val indent: Int, val blank: Boolean)

    private fun lines(text: String): List<Line> {
        val out = ArrayList<Line>()
        var start = 0
        var number = 0
        var raw = false
        while (start <= text.length) {
            val end = text.indexOf('\n', start).let { if (it < 0) text.length else it }
            val line = text.substring(start, end)
            val insideRaw = raw
            if (Regex("\"\"\"").findAll(line).count() % 2 == 1) raw = !raw
            // The lines inside a raw string continue the line that opened it.
            if (insideRaw) {
                out.add(Line(number, start, end, "", Int.MAX_VALUE, false))
            } else {
                val code = TrionLines.stripComment(line)
                out.add(Line(number, start, end, code.trim(), line.length - line.trimStart().length, code.isBlank()))
            }
            if (end == text.length) break
            start = end + 1
            number++
        }
        return out
    }

    private val identified = Regex("^\\[([A-Z][A-Z0-9-]*(?:/[a-z][a-z0-9-]*)?)]")
    private val named = Regex("^(namespace|source|check|example|trace|role|compatibility|diagram kind)\\s+([^\\s:]+)\\s*(:?)$")
    private val primitive = Regex("^primitive\\s+(.+)$")
    private val control = Regex("^(environment|system)\\s+(.+)$")
    private val predicate = Regex("^predicate\\s+([a-z][a-z0-9-]*)\\(")
    private val section = Regex("^section\\s+\"(.*)\"\\s*(:?)$")
    private val quote = Regex("^quote\\s+([A-Z][A-Z0-9-]*)\\s")
    private val term = Regex("^term\\s+([^:]+):")
    private val means = Regex("^(?:\\[[^]]*]\\s*)?(?:An?|The)?\\s*(.+?)\\s+means\\s", RegexOption.IGNORE_CASE)

    fun entries(text: String): List<OutlineEntry> {
        val all = lines(text)
        val lines = all.filter { !it.blank }
        val out = ArrayList<OutlineEntry>()
        // The headers that enclose the current line, as (indent, flat kind or null).
        val open = ArrayList<Pair<Int, String?>>()
        for ((index, line) in lines.withIndex()) {
            while (open.isNotEmpty()) {
                val (indent, flat) = open.last()
                if (line.indent == Int.MAX_VALUE) break
                val closes = if (flat == null) line.indent <= indent else line.indent < indent || (line.indent == indent && line.text.startsWith("$flat "))
                if (closes) open.removeAt(open.size - 1) else break
            }
            val depth = open.size
            val header = named.find(line.text)
            val titled = section.find(line.text)
            val isBlock = TrionLines.opensBlock(line.text)
            val flat = when {
                header != null && header.groupValues[1] == "namespace" && header.groupValues[3].isEmpty() -> "namespace"
                titled != null && titled.groupValues[2].isEmpty() -> "section"
                else -> null
            }
            val end = when {
                flat != null -> blockEnd(lines, index) { next -> next.indent < line.indent || (next.indent == line.indent && next.text.startsWith("$flat ")) }
                isBlock -> blockEnd(lines, index) { next -> next.indent <= line.indent }
                else -> line.end
            }
            fun add(kind: String, name: String) = out.add(OutlineEntry(kind, name, line.number, line.indent, line.start + line.indent, end, depth))
            when {
                header != null -> add(header.groupValues[1], header.groupValues[2])
                titled != null -> add("section", titled.groupValues[1])
                identified.containsMatchIn(line.text) -> add("statement", identified.find(line.text)!!.groupValues[1])
                quote.containsMatchIn(line.text) -> add("quote", quote.find(line.text)!!.groupValues[1])
                term.containsMatchIn(line.text) -> add("term", term.find(line.text)!!.groupValues[1].trim())
                TrionLines.directive(line.text) == "primitive" -> add("primitive", primitive.find(line.text)!!.groupValues[1].trim())
                TrionLines.directive(line.text) == "measure" -> add("measure", line.text.trim().removePrefix("measure").trim())
                TrionLines.directive(line.text) in setOf("environment", "system") -> control.find(line.text)!!.let { add(it.groupValues[1], it.groupValues[2].trim()) }
                TrionLines.directive(line.text) == "predicate" -> add("predicate", predicate.find(line.text)!!.groupValues[1])
                isBlock -> add("block", line.text.trimEnd(':').trim())
            }
            means.find(line.text)?.let { found ->
                if (TrionLines.directive(line.text) == null) add("definition", found.groupValues[1].trim())
            }
            if (flat != null) open.add(line.indent to flat) else if (isBlock) open.add(line.indent to null)
        }
        return out
    }

    private fun blockEnd(lines: List<Line>, index: Int, closes: (Line) -> Boolean): Int {
        var last = lines[index]
        for (next in lines.subList(index + 1, lines.size)) {
            if (closes(next)) break
            last = next
        }
        return last.end
    }

    /** The offset of the line with this number, or -1. */
    fun lineOffset(text: String, line: Int): Int {
        var offset = 0
        repeat(line) {
            offset = text.indexOf('\n', offset) + 1
            if (offset == 0) return -1
        }
        return offset
    }
}
