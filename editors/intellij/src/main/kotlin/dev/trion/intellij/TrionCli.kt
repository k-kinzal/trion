package dev.trion.intellij

import com.google.gson.JsonArray
import com.google.gson.JsonElement
import com.google.gson.JsonObject
import com.google.gson.JsonParser
import com.intellij.execution.configurations.PathEnvironmentVariableUtil
import com.intellij.notification.NotificationAction
import com.intellij.notification.NotificationGroupManager
import com.intellij.notification.NotificationType
import com.intellij.openapi.components.Service
import com.intellij.openapi.options.ShowSettingsUtil
import com.intellij.openapi.project.Project
import com.intellij.openapi.util.SystemInfo
import com.intellij.openapi.util.io.FileUtil
import com.intellij.openapi.vfs.VirtualFile
import java.io.File
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean

private const val INSTALL_COMMAND = "cargo install --path crates/trion-cli"

/**
 * A bare command name is searched on PATH and then in ~/.cargo/bin, where `cargo install`
 * puts it. Anything with a path separator is taken as a path, with a leading `~` expanded.
 */
internal fun resolveServerBinary(configured: String): File? {
    val expanded = FileUtil.expandUserHome(configured.trim())
    if (expanded.isEmpty()) {
        return null
    }
    if (expanded.contains('/') || expanded.contains(File.separatorChar)) {
        return File(expanded).takeIf { it.isAbsolute && it.isFile && it.canExecute() }
    }
    PathEnvironmentVariableUtil.findInPath(expanded)?.let { return it }
    val fileName = if (SystemInfo.isWindows && !expanded.contains('.')) "$expanded.exe" else expanded
    val cargoBinary = File(System.getProperty("user.home"), ".cargo/bin/$fileName")
    return cargoBinary.takeIf { it.isFile && it.canExecute() }
}

/**
 * The binary the plugin runs: the configured one, or a build of the project itself
 * (`target/debug/trion`, `target/release/trion`) when the configured one is not there.
 */
internal fun resolveBinary(configured: String, projectDir: String?): File? {
    resolveServerBinary(configured)?.let { return it }
    val name = if (SystemInfo.isWindows) "trion.exe" else "trion"
    // The newest build of the project is the one that knows its current syntax.
    val built = listOf("target/release", "target/debug")
        .mapNotNull { build -> projectDir?.let { File(it, "$build/$name") } }
        .filter { it.isFile && it.canExecute() }
        .maxByOrNull { it.lastModified() }
    return built ?: resolveServerBinary(DEFAULT_SERVER_PATH)
}

/** The directory of the nearest `trion.toml` above a file. */
internal fun packageRoot(file: File): File? {
    var dir: File? = if (file.isDirectory) file else file.parentFile
    while (dir != null) {
        if (File(dir, "trion.toml").isFile) {
            return dir
        }
        dir = dir.parentFile
    }
    return null
}

data class TrionRef(val id: String, val file: String, val line: Int, val text: String)

data class TrionDiagnostic(val severity: String, val code: String, val message: String, val refs: List<TrionRef>)

data class TrionReport(
    val diagnostics: List<TrionDiagnostic>,
    val verdict: String?,
    val status: String?,
    val failure: String? = null,
    /** The bounds the verdict was established within, as the command words them. */
    val bounds: String? = null,
    /** Parts of a sentence without a formal reading, and statements that constrain nothing: errors. */
    val opaque: List<TrionDiagnostic> = emptyList(),
    val ungrounded: List<TrionDiagnostic> = emptyList(),
    /** Pairs of statements whose responses conflict while both conditions hold: decisions left to the author. */
    val overlaps: Int = 0,
    /** Statements that constrain the environment: what the specification assumes. */
    val assumptions: Int = 0,
) {
    val errors: Int get() = diagnostics.count { it.severity == "error" } + opaque.size + ungrounded.size
    val warnings: Int get() = diagnostics.count { it.severity != "error" }

    /** One line that says whether the package holds, within which bounds, and how much of it is not read. */
    fun summary(): String {
        if (failure != null) return "trion: $failure"
        val within = bounds?.let { " within $it" } ?: ""
        val unread = if (opaque.isEmpty() && ungrounded.isEmpty()) "" else "; not read: ${opaque.size} part${if (opaque.size == 1) "" else "s"} without a formal reading, ${ungrounded.size} ungrounded statement${if (ungrounded.size == 1) "" else "s"}"
        val decisions = listOfNotNull(
            overlaps.takeIf { it > 0 }?.let { "$it condition overlap${if (it == 1) "" else "s"}" },
            assumptions.takeIf { it > 0 }?.let { "$it assumption${if (it == 1) "" else "s"} about the environment" },
        ).joinToString(", ").let { if (it.isEmpty()) "" else "; $it" }
        return "trion: ${verdict ?: "not analysed"}$within; $errors error${if (errors == 1) "" else "s"}, $warnings warning${if (warnings == 1) "" else "s"} in the package$decisions$unread"
    }
}

/** The outline of one file of a package. */
class TrionIndexedFile(val file: File, val entries: List<OutlineEntry>)

/**
 * Running the command, or reading every file of a package, takes time that the UI thread
 * does not have: a handler that waited there once froze the IDE. A test fails on such a call;
 * outside tests the call is refused.
 */
internal fun onUiThread(what: String): Boolean {
    val application = com.intellij.openapi.application.ApplicationManager.getApplication() ?: return false
    if (!application.isDispatchThread) return false
    check(!application.isUnitTestMode) { "$what on the UI thread" }
    com.intellij.openapi.diagnostic.Logger.getInstance(TrionCli::class.java).warn("$what was asked for on the UI thread and was not done")
    return true
}

data class TrionTerm(
    val term: String,
    val status: String,
    val kinds: List<String>,
    val occurrences: Int,
    val firstUse: String?,
    val declaredAt: String?,
    val definedAt: String?,
    val definition: String?,
    val rules: List<String>,
    val referenced: List<String>,
) {
    /** Where the term comes from: its definition, its declaration, or its first use. */
    val origin: String? get() = definedAt ?: declaredAt ?: firstUse
}

class TrionOutput(val exit: Int, val stdout: String, val stderr: String)

@Service(Service.Level.PROJECT)
class TrionCli(private val project: Project) {
    private val glossaries = ConcurrentHashMap<String, Pair<Long, List<TrionTerm>>>()
    private val reports = ConcurrentHashMap<String, TrionReport>()

    fun binary(): File? = resolveBinary(TrionSettings.getInstance().serverPath, project.basePath)

    /** Runs the binary in a package root. Returns null, after one notice, when there is no binary. */
    fun run(root: File, vararg arguments: String): TrionOutput? {
        if (onUiThread("trion ${arguments.firstOrNull { !it.startsWith("--") } ?: ""}")) return null
        val binary = binary()
        if (binary == null) {
            notifyMissingBinary(project, TrionSettings.getInstance().serverPath)
            return null
        }
        return execute(binary, root, arguments.toList())
    }

    fun check(root: File): TrionReport? {
        val output = run(root, "--json", "check", root.path) ?: return null
        val report = parseReport(output)
        reports[root.path] = report
        return report
    }

    fun lastReport(root: File): TrionReport? = reports[root.path]

    /** The glossary of a package, read again when one of its files changed. */
    fun glossary(root: File): List<TrionTerm> {
        if (onUiThread("reading the glossary")) return glossaries[root.path]?.second ?: emptyList()
        val stamp = root.walkTopDown().onEnter { it.name != "target" && !it.name.startsWith(".") && it.name != "node_modules" && it.name != "build" }
            .filter { it.name.endsWith(".trion") || it.name == "trion.toml" }.maxOfOrNull { it.lastModified() } ?: 0
        glossaries[root.path]?.let { (at, terms) -> if (at == stamp) return terms }
        val output = run(root, "--json", "glossary", root.path) ?: return emptyList()
        val terms = parseGlossary(output.stdout)
        glossaries[root.path] = stamp to terms
        return terms
    }

    private val loading = ConcurrentHashMap.newKeySet<String>()
    private val indexes = ConcurrentHashMap<String, List<TrionIndexedFile>>()
    private val indexing = ConcurrentHashMap.newKeySet<String>()

    /** The outline of every trion file of a package, read from disk. */
    fun index(root: File): List<TrionIndexedFile> {
        if (onUiThread("reading the files of a package")) return indexes[root.path] ?: emptyList()
        val files = TrionResolver.scan(root)
        indexes[root.path] = files
        return files
    }

    /**
     * The outlines as far as they are known now, for the UI thread: a first call returns
     * nothing and reads the package in the background.
     */
    fun knownIndex(root: File): List<TrionIndexedFile> {
        val known = indexes[root.path]
        if (indexing.add(root.path)) {
            com.intellij.openapi.application.ApplicationManager.getApplication().executeOnPooledThread {
                try {
                    index(root)
                } finally {
                    indexing.remove(root.path)
                }
            }
        }
        return known ?: emptyList()
    }

    /**
     * The glossary as far as it is known now. This never runs the command on the
     * calling thread, so the UI thread may ask: a first call returns nothing and
     * starts the command in the background.
     */
    fun knownGlossary(root: File): List<TrionTerm> {
        val known = glossaries[root.path]?.second
        if (loading.add(root.path)) {
            com.intellij.openapi.application.ApplicationManager.getApplication().executeOnPooledThread {
                try {
                    glossary(root)
                } finally {
                    loading.remove(root.path)
                }
            }
        }
        return known ?: emptyList()
    }

    fun explain(root: File, id: String): String? = run(root, "explain", id, root.path)?.takeIf { it.exit == 0 }?.stdout

    /** The document view of one file, as the HTML that `trion render` prints. */
    fun render(root: File, relative: String): TrionOutput? = run(root, "render", root.path, "--file", relative)

    companion object {
        fun getInstance(project: Project): TrionCli = project.getService(TrionCli::class.java)

        private val missingBinaryNotified = AtomicBoolean(false)

        fun resetMissingBinaryNotice() = missingBinaryNotified.set(false)

        /** One missing binary raises one balloon, however many features ask for it. */
        internal fun notifyMissingBinary(project: Project, configured: String) {
            if (!missingBinaryNotified.compareAndSet(false, true)) {
                return
            }
            NotificationGroupManager.getInstance()
                .getNotificationGroup("Trion")
                .createNotification(
                    "Trion binary not found",
                    "Cannot find <code>$configured</code>, and the project has no <code>target/debug/trion</code>. " +
                        "Build it with <code>cargo build</code>, install it with <code>$INSTALL_COMMAND</code>, or set its path. " +
                        "Highlighting, folding and the structure view work without it; diagnostics, term documentation and the preview do not.",
                    NotificationType.ERROR,
                )
                .addAction(
                    NotificationAction.createSimpleExpiring("Open settings") {
                        ShowSettingsUtil.getInstance().showSettingsDialog(project, "Trion")
                    },
                )
                .notify(project)
        }

        /** The running command of each kind (`check`, `render`, …) in each directory. */
        private val running = ConcurrentHashMap<String, Process>()

        /**
         * Runs the command and stops it after `seconds`. A newer run of the same
         * kind in the same directory stops the older one: only its result matters.
         */
        internal fun execute(binary: File, directory: File, arguments: List<String>, seconds: Long = 20): TrionOutput {
            val process = ProcessBuilder(listOf(binary.path) + arguments).directory(directory).redirectErrorStream(false).start()
            val kind = directory.path + "|" + (arguments.firstOrNull { !it.startsWith("-") } ?: "") + "|" + (arguments.lastOrNull() ?: "")
            running.put(kind, process)?.destroyForcibly()
            process.outputStream.close()
            val stdout = StringBuilder()
            val stderr = StringBuilder()
            // Both streams are read on their own threads, so the time limit below holds
            // even when the command prints nothing.
            val out = Thread { runCatching { stdout.append(process.inputStream.bufferedReader().readText()) } }.apply { isDaemon = true; start() }
            val err = Thread { runCatching { stderr.append(process.errorStream.bufferedReader().readText()) } }.apply { isDaemon = true; start() }
            val finished = process.waitFor(seconds, TimeUnit.SECONDS)
            running.remove(kind, process)
            if (!finished) {
                process.destroyForcibly()
                return TrionOutput(-1, "", "trion did not finish within $seconds seconds")
            }
            out.join(2000)
            err.join(1000)
            return TrionOutput(process.exitValue(), stdout.toString(), stderr.toString())
        }

        private fun JsonObject.text(name: String): String? = get(name)?.takeIf { !it.isJsonNull }?.asString

        private fun JsonElement?.items(): List<JsonElement> = (this as? JsonArray)?.toList() ?: emptyList()

        private fun unread(list: JsonElement?): List<TrionDiagnostic> = list.items().map { it.asJsonObject }.map { d ->
            val refs = d.get("refs").items().map { it.asJsonObject }.map { r ->
                TrionRef(r.text("id") ?: "", r.text("file") ?: "", r.get("line")?.asInt ?: 0, r.text("text") ?: "")
            }
            TrionDiagnostic("error", d.text("code") ?: "", d.text("message") ?: "", refs)
        }

        fun parseReport(output: TrionOutput): TrionReport {
            val root = try {
                JsonParser.parseString(output.stdout).asJsonObject
            } catch (problem: Exception) {
                val reason = output.stderr.lines().firstOrNull { it.isNotBlank() } ?: "the check printed no report (exit ${output.exit})"
                return TrionReport(emptyList(), null, null, reason)
            }
            val diagnostics = root.get("diagnostics").items().map { it.asJsonObject }.map { d ->
                val refs = d.get("refs").items().map { it.asJsonObject }.map { r ->
                    TrionRef(r.text("id") ?: "", r.text("file") ?: "", r.get("line")?.asInt ?: 0, r.text("text") ?: "")
                }
                TrionDiagnostic(d.text("severity") ?: "error", d.text("code") ?: "", d.text("message") ?: "", refs)
            }
            val consistency = root.get("consistency")?.takeIf { it.isJsonObject }?.asJsonObject
            val limits = consistency?.get("bounds")?.takeIf { it.isJsonObject }?.asJsonObject
            val bounds = listOfNotNull(
                limits?.get("trace_length")?.takeIf { !it.isJsonNull }?.asInt?.let { "traces of $it moment${if (it == 1) "" else "s"}" },
                limits?.get("scope")?.takeIf { !it.isJsonNull }?.asInt?.let { "$it individual${if (it == 1) "" else "s"} of each type" },
                limits?.get("decisions")?.takeIf { !it.isJsonNull }?.asLong?.let { "$it decisions for each query" },
            ).joinToString(" and ").ifEmpty { null }
            return TrionReport(diagnostics, consistency?.text("verdict"), consistency?.text("status"), null, bounds, unread(root.get("opaque")), unread(root.get("ungrounded")), root.get("overlaps").items().size, root.get("environment")?.takeIf { it.isJsonObject }?.asJsonObject?.get("assumptions").items().size)
        }

        fun parseGlossary(json: String): List<TrionTerm> = try {
            JsonParser.parseString(json).items().map { it.asJsonObject }.map { e ->
                val derivation = e.get("derivation")?.takeIf { it.isJsonObject }?.asJsonObject
                TrionTerm(
                    term = e.text("term") ?: "",
                    status = e.text("status") ?: "",
                    kinds = e.get("kinds").items().map { it.asString },
                    occurrences = e.get("occurrences")?.asInt ?: 0,
                    firstUse = e.text("first_use"),
                    declaredAt = e.text("declared_at") ?: e.get("declared_at")?.takeIf { it.isJsonObject }?.asJsonObject?.text("id"),
                    definedAt = e.text("defined_at") ?: e.get("defined_at")?.takeIf { it.isJsonObject }?.asJsonObject?.text("id"),
                    definition = e.text("definition"),
                    rules = derivation?.get("rules").items().map { it.asString },
                    referenced = derivation?.get("referenced").items().map { it.toString().trim('"') },
                )
            }
        } catch (problem: Exception) {
            emptyList()
        }
    }
}

/** The file on disk behind a virtual file, when it has one. */
internal fun VirtualFile.onDisk(): File? = if (isInLocalFileSystem) File(path) else null
