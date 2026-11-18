package dev.trion.intellij

import com.intellij.openapi.util.Disposer
import com.intellij.testFramework.fixtures.BasePlatformTestCase
import com.redhat.devtools.lsp4ij.LanguageServersRegistry
import com.redhat.devtools.lsp4ij.server.CannotStartProcessException
import com.redhat.devtools.lsp4ij.server.ProcessStreamConnectionProvider
import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit

class TrionPluginTest : BasePlatformTestCase() {
    private val rawQuotes = "\"\"\""

    private val sample = """
        // A comment.
        package chat edition "2026-11-09"

        namespace chat.api:
            use grpc
            predicate reachable(node, node)
            source R:
                title "The \"first\" request"
                quote INTENT $rawQuotes
        not // a comment inside a raw string
        $rawQuotes

            section "Requests":
                unsourced "The session leaves this open."
                [EARS-1]
                When a request arrives, the API shall respond within 500 ms.
                    cite R#INTENT

            trace EARS-TEST:
                verifies chat#EARS-1

        namespace chat.room

        section "Room types"

        [ROOM-KINDS] The room type is private or public.
    """.trimIndent()

    /** Points the settings at [path] for the rest of the test. */
    private fun useServerPath(path: String) {
        val settings = TrionSettings.getInstance()
        val previous = settings.serverPath
        settings.serverPath = path
        Disposer.register(testRootDisposable) { settings.serverPath = previous }
    }

    // trion: verifies trion#EDITOR-INTELLIJ
    fun testATrionFileHasTheFileTypeAndLanguage() {
        val file = myFixture.configureByText("sample.trion", sample)
        assertEquals(TrionFileType, file.fileType)
        assertEquals(TrionLanguage, file.language)
        assertInstanceOf(file, TrionFile::class.java)
        assertEquals(sample, file.text)
    }

    // trion: verifies trion#EDITOR-INTELLIJ
    fun testCommentingUsesTheSlashPrefix() {
        myFixture.configureByText("sample.trion", "package chat edition \"1\"")
        myFixture.performEditorAction("CommentByLineComment")
        myFixture.checkResult("// package chat edition \"1\"")
    }

    // trion: verifies trion#EDITOR-INTELLIJ
    fun testTheLanguageServerIsMappedToTrionFiles() {
        val registry = LanguageServersRegistry.getInstance()
        val definition = registry.getServerDefinition(SERVER_ID)
        assertNotNull("LSP4IJ has no server $SERVER_ID", definition)
        assertTrue(TrionLanguage in registry.supportedLanguages)
        val trion = myFixture.configureByText("sample.trion", sample)
        assertTrue(registry.isFileSupported(trion))
        assertEquals("trion", definition!!.getLanguageId(trion))
        val text = myFixture.configureByText("notes.txt", "Not a trion file.")
        assertFalse(registry.isFileSupported(text))
    }

    // trion: verifies trion#EDITOR-INTELLIJ, trion#EDITOR-SERVER-PATH
    fun testTheServerStartsTheConfiguredBinaryWithLsp() {
        val dir = Files.createTempDirectory("trion-server").toFile()
        Disposer.register(testRootDisposable) { dir.deleteRecursively() }
        val arguments = File(dir, "arguments")
        val binary = File(dir, "trion")
        binary.writeText("#!/bin/sh\n")
        assertTrue(binary.setExecutable(true))
        // The language server is the `trion-lsp` command beside `trion`; it takes no argument.
        val server = File(dir, "trion-lsp")
        server.writeText("#!/bin/sh\necho \"started $#\" > '${arguments.path}'\nexec cat\n")
        assertTrue(server.setExecutable(true))
        useServerPath(binary.path)
        // The light test project has a base path that is not on disk; a real project's is.
        File(project.basePath!!).mkdirs()

        val provider = TrionLanguageServerFactory().createConnectionProvider(project) as ProcessStreamConnectionProvider
        provider.start()
        try {
            assertEquals(listOf(server.path), provider.commands)
            assertEquals(project.basePath, provider.workingDirectory)
            val deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(10)
            while (!(arguments.isFile && arguments.readText().isNotBlank()) && System.nanoTime() < deadline) {
                Thread.sleep(20)
            }
            assertEquals("started 0", arguments.readText().trim())
        } finally {
            provider.stop()
        }
    }

    // trion: verifies trion#EDITOR-SERVER-PATH
    fun testAMissingConfiguredBinaryDoesNotStart() {
        useServerPath("/does/not/exist/trion")
        val provider = TrionLanguageServerFactory().createConnectionProvider(project)
        try {
            provider.start()
            fail("a missing binary started")
        } catch (expected: CannotStartProcessException) {
            assertTrue(expected.message!!.contains("/does/not/exist/trion"))
        }
    }

    // trion: verifies trion#EDITOR-SERVER-PATH
    fun testAMissingBinaryResolvesToNull() {
        assertNull(resolveServerBinary("trion-binary-that-does-not-exist"))
        assertNull(resolveServerBinary("/does/not/exist/trion"))
        assertNull(resolveServerBinary("   "))
    }

    // trion: verifies trion#EDITOR-SERVER-PATH
    fun testAnAbsolutePathToAnExecutableResolves() {
        val shell = File("/bin/sh")
        assertEquals(shell, resolveServerBinary(shell.path))
    }

    // trion: verifies trion#EDITOR-SERVER-PATH
    fun testSettingsDefaultToTheCommandName() {
        assertEquals(DEFAULT_SERVER_PATH, TrionSettings().serverPath)
    }

    // trion: verifies trion#EDITOR-SERVER-PATH
    fun testABlankSettingFallsBackToTheCommandName() {
        val settings = TrionSettings()
        settings.serverPath = "  "
        assertEquals(DEFAULT_SERVER_PATH, settings.serverPath)
    }
}
