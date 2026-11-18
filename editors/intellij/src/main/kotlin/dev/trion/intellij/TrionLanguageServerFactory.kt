package dev.trion.intellij

import com.intellij.openapi.project.Project
import com.intellij.openapi.project.ProjectManager
import com.intellij.openapi.util.SystemInfo
import com.intellij.psi.PsiFile
import com.redhat.devtools.lsp4ij.LanguageServerFactory
import com.redhat.devtools.lsp4ij.LanguageServerManager
import com.redhat.devtools.lsp4ij.client.features.LSPClientFeatures
import com.redhat.devtools.lsp4ij.client.features.LSPDiagnosticFeature
import com.redhat.devtools.lsp4ij.client.features.LSPHoverFeature
import com.redhat.devtools.lsp4ij.client.features.LSPSemanticTokensFeature
import com.redhat.devtools.lsp4ij.server.CannotStartProcessException
import com.redhat.devtools.lsp4ij.server.ProcessStreamConnectionProvider
import com.redhat.devtools.lsp4ij.server.StreamConnectionProvider
import java.io.File

internal const val SERVER_ID = "dev.trion.intellij.server"

/**
 * Loaded only where the LSP4IJ plugin is installed. The plugin colours, checks and documents
 * a file itself, so the server adds what remains: completion and the other requests.
 */
class TrionLanguageServerFactory : LanguageServerFactory {
    init {
        TrionSettings.onChange(SERVER_ID) {
            for (project in ProjectManager.getInstance().openProjects) {
                val manager = LanguageServerManager.getInstance(project)
                manager.stop(SERVER_ID)
                manager.start(SERVER_ID)
            }
        }
    }

    override fun createConnectionProvider(project: Project): StreamConnectionProvider = TrionConnectionProvider(project)

    override fun createClientFeatures(): LSPClientFeatures = LSPClientFeatures()
        .setDiagnosticFeature(object : LSPDiagnosticFeature() {
            override fun isEnabled(file: PsiFile): Boolean = false
        })
        .setSemanticTokensFeature(object : LSPSemanticTokensFeature() {
            override fun isEnabled(file: PsiFile): Boolean = false
        })
        .setHoverFeature(object : LSPHoverFeature() {
            override fun isEnabled(file: PsiFile): Boolean = false
        })
}

private class TrionConnectionProvider(private val project: Project) : ProcessStreamConnectionProvider() {
    /** Resolves on every start, so that installing the binary and restarting the server is enough. */
    override fun start() {
        val configured = TrionSettings.getInstance().serverPath
        // The language server is the `trion-lsp` command, which is installed beside `trion`.
        val server = resolveBinary(configured, project.basePath)?.let { trion -> File(trion.parentFile, if (SystemInfo.isWindows) "trion-lsp.exe" else "trion-lsp") }?.takeIf { it.isFile && it.canExecute() }
        if (server == null) {
            TrionCli.notifyMissingBinary(project, configured)
            throw CannotStartProcessException("Cannot find the trion-lsp binary beside: $configured")
        }
        commands = listOf(server.path)
        workingDirectory = project.basePath
        super.start()
    }
}
