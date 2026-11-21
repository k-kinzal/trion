package dev.trion.intellij

import com.intellij.lang.annotation.HighlightSeverity
import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.application.ReadAction
import com.intellij.openapi.fileTypes.SyntaxHighlighterFactory
import com.intellij.openapi.util.Disposer
import com.intellij.openapi.util.io.FileUtil
import com.intellij.openapi.vfs.LocalFileSystem
import com.intellij.psi.PsiFile
import com.intellij.psi.PsiManager
import com.intellij.testFramework.fixtures.BasePlatformTestCase
import java.io.File

class TrionLanguageTest : BasePlatformTestCase() {
    private val q = "\"\"\""

    private val sample = """
        // trion language specification.
        // Its syntax has not been checked.
        package trion

        include "rooms/members.trion"

        namespace trion.room:
            use trion.vocabulary
            cite R#ROOMS

            source R:
                title "The first request"
                quote ROOMS $q
        A room is not public. // 0.1
        $q

            section "Room types":
                A package means a specification assembled from an entry file and the
                source files reachable through include declarations. Each room has an owner.

                [ROOM-KINDS]
                The room type is `private` or `public`.

                For each room R:
                    [ROOM-JOIN]
                    When a member M joins R, the service shall not wait
                    more than 500 ms unless R is archived.

        namespace trion.flat

        section "Flat one"

        [FLAT-A] The API shall stop.

        section "Flat two"

        [FLAT-B] The API shall log grpc::status.
    """.trimIndent()

    /** Runs what the plugin runs in the background: the command and the reading of a package never run on the UI thread. */
    private fun <T> background(body: () -> T): T =
        ApplicationManager.getApplication().executeOnPooledThread(java.util.concurrent.Callable { body() }).get()

    private fun <T> reading(body: () -> T): T = background { ReadAction.compute<T, RuntimeException> { body() } }

    private fun tokens(text: String): List<Pair<String, String>> {
        val lexer = TrionLexer()
        lexer.start(text)
        val out = ArrayList<Pair<String, String>>()
        var covered = 0
        while (lexer.tokenType != null) {
            assertEquals("tokens are contiguous", covered, lexer.tokenStart)
            covered = lexer.tokenEnd
            out.add(text.substring(lexer.tokenStart, lexer.tokenEnd) to lexer.tokenType.toString())
            lexer.advance()
        }
        assertEquals(text.length, covered)
        return out
    }

    private fun typeOf(tokens: List<Pair<String, String>>, text: String): String =
        tokens.firstOrNull { it.first == text }?.second ?: fail("no token `$text` in ${tokens.map { it.first }.filter { it.isNotBlank() }}").let { "" }

    // trion: verifies trion#EDITOR-IDEA-HIGHLIGHT
    fun testDeclarationsSentencesAndReferencesGetTheirOwnTokens() {
        val all = tokens(sample)
        for (keyword in listOf("package", "include", "namespace", "use", "cite", "source", "title", "quote", "section")) {
            assertEquals(keyword, "DIRECTIVE", typeOf(all, keyword))
        }
        assertEquals("NAME", typeOf(all, "trion.room"))
        assertEquals("NAME", typeOf(all, "trion.flat"))
        assertEquals("REFERENCE", typeOf(all, "ROOMS"))
        assertEquals("SPEC_ID", typeOf(all, "[ROOM-KINDS]"))
        assertEquals("LITERAL", typeOf(all, "`private`"))
        assertEquals("DEFINER", typeOf(all, "means"))
        assertEquals("CONDITION", typeOf(all, "When"))
        assertEquals("CONDITION", typeOf(all, "unless"))
        assertEquals("CONDITION", typeOf(all, "For"))
        assertEquals("MODAL", typeOf(all, "shall"))
        assertEquals("MODAL", all[all.indexOfFirst { it.first == "shall" } + 2].second)
        assertEquals("VARIABLE", typeOf(all, "M"))
        assertEquals("NUMBER", typeOf(all, "500"))
        assertEquals("UNIT", typeOf(all, "ms"))
        assertEquals("QUALIFIED", typeOf(all, "grpc::status"))
        // An article is not a variable, and a wrapped sentence line is not a declaration.
        assertEquals("WORD", typeOf(all, "A"))
        val wrapped = all.indexOfFirst { it.first == "reachable" }
        assertEquals("source" to "WORD", all[wrapped - 4])
        assertFalse(all.any { it.second == "BAD" })
    }

    // trion: verifies trion#EDITOR-IDEA-HIGHLIGHT
    fun testCommentsAndStringsAreSingleTokens() {
        val all = tokens(sample)
        // The reported cases: no number and no keyword inside a comment or a string.
        assertEquals("COMMENT", typeOf(all, "// trion language specification."))
        assertEquals("COMMENT", typeOf(all, "// Its syntax has not been checked."))
        assertEquals("STRING", typeOf(all, "\"rooms/members.trion\""))
        assertEquals("RAW_STRING", typeOf(all, "$q\nA room is not public. // 0.1\n$q"))
        assertFalse(all.any { it.first == "0.1" || it.first == "not" && it.second != "MODAL" })
        // A lexer restarted inside a raw string continues it.
        val lexer = TrionLexer()
        val inside = sample.indexOf("A room is not public")
        lexer.start(sample, inside, sample.length, 1)
        assertEquals(TrionTokens.RAW_STRING, lexer.tokenType)
        assertEquals(sample.indexOf(q, inside) + 3, lexer.tokenEnd)
    }

    // trion: verifies trion#EDITOR-IDEA-HIGHLIGHT
    fun testATrionFileIsColouredByThePluginsOwnHighlighter() {
        val file = myFixture.configureByText("sample.trion", sample)
        val highlighter = SyntaxHighlighterFactory.getSyntaxHighlighter(TrionFileType, project, file.virtualFile)!!
        assertInstanceOf(highlighter, TrionSyntaxHighlighter::class.java)
        assertInstanceOf(highlighter.highlightingLexer, TrionLexer::class.java)
        assertEquals(listOf(TrionColors.DIRECTIVE), highlighter.getTokenHighlights(TrionTokens.DIRECTIVE).toList())
        assertEquals(listOf(TrionColors.COMMENT), highlighter.getTokenHighlights(TrionTokens.COMMENT).toList())
        assertEquals(listOf(TrionColors.MODAL), highlighter.getTokenHighlights(TrionTokens.MODAL).toList())
        // The PSI tree is made of the same tokens.
        val keyword = file.findElementAt(sample.indexOf("package"))!!
        assertEquals(TrionTokens.DIRECTIVE, keyword.node.elementType)
        // The colour settings page shows every token kind and no bad character.
        val page = TrionColorSettingsPage()
        val demo = tokens(page.demoText)
        assertFalse(demo.any { it.second == "BAD" })
        for (kind in listOf("COMMENT", "STRING", "RAW_STRING", "LITERAL", "SPEC_ID", "DIRECTIVE", "NAME", "REFERENCE", "CONDITION", "MODAL", "DEFINER", "VARIABLE", "NUMBER", "UNIT", "QUALIFIED")) {
            assertTrue(kind, demo.any { it.second == kind })
        }
        assertEquals(16, page.attributeDescriptors.size)
    }

    // trion: verifies trion#EDITOR-IDEA-FOLDING
    fun testBlocksFoldByIndentationAndFlatHeadersToTheNextOne() {
        val folded = TrionFoldingBuilder.regions(sample).map { (range, _) -> sample.substring(range.startOffset, range.endOffset) }
        val of = { header: String -> folded.first { region -> sample.substring(0, sample.indexOf(region)).trimEnd().endsWith(header) } }
        // The source block holds its raw string to the closing quotes.
        assertTrue(of("source R:").trimEnd().endsWith(q))
        assertTrue(of("For each room R:").trimEnd().endsWith("unless R is archived."))
        assertTrue(of("namespace trion.room:").trimEnd().endsWith("unless R is archived."))
        // A flat namespace runs to the end; a flat section stops before the next section.
        assertTrue(of("namespace trion.flat").trimEnd().endsWith("grpc::status."))
        assertTrue(of("section \"Flat one\"").trimEnd().endsWith("[FLAT-A] The API shall stop."))
        // The editor builds the same regions.
        val file = myFixture.configureByText("sample.trion", sample)
        val descriptors = TrionFoldingBuilder().buildFoldRegions(file, myFixture.editor.document, false)
        assertEquals(folded.size, descriptors.size)
    }

    // trion: verifies trion#EDITOR-IDEA-STRUCTURE
    fun testTheStructureViewNestsNamespacesSectionsAndStatements() {
        val file = myFixture.configureByText("sample.trion", sample)
        val top = TrionStructureElement.children(file, null)
        assertEquals(listOf("namespace trion.room", "namespace trion.flat"), top.map { "${it.kind} ${it.name}" })
        val room = TrionStructureElement.children(file, top[0])
        assertEquals(listOf("source R", "section Room types"), room.map { "${it.kind} ${it.name}" })
        val types = TrionStructureElement.children(file, room[1])
        assertEquals(listOf("ROOM-KINDS", "ROOM-JOIN"), types.map { it.name })
        val flat = TrionStructureElement.children(file, top[1])
        assertEquals(listOf("Flat one", "Flat two"), flat.map { it.name })
        assertEquals(listOf("FLAT-B"), TrionStructureElement.children(file, flat[1]).map { it.name })
        val root = TrionStructureElement(file, null)
        assertEquals(2, root.children.size)
        assertEquals("[ROOM-KINDS]", TrionStructureElement(file, types[0]).presentableText)
    }

    // A package on disk with a stub `trion` binary that prints canned reports.

    private lateinit var root: File

    private fun stubPackage(render: String = "echo '<html><body><p data-file=\"spec/rooms.trion\" data-line=\"4\">Rooms</p></body></html>'") {
        root = FileUtil.createTempDirectory("trion-package", null)
        Disposer.register(testRootDisposable) { root.deleteRecursively() }
        File(root, "trion.toml").writeText("[package]\nname = \"chat\"\nentry = \"spec/chat.trion\"\n")
        File(root, "spec").mkdirs()
        File(root, "spec/chat.trion").writeText(
            "package chat\n\ninclude \"rooms.trion\"\n\nnamespace chat:\n    use chat.room\n    cite R#ROOMS\n\n    section \"Scope\":\n        ref [ROOM-KINDS]\n        [CHAT-1] The chat service shall keep each room.\n",
        )
        File(root, "spec/rooms.trion").writeText(
            "namespace chat.room:\n    source R:\n        title \"t\"\n        locator \"l\"\n        quote ROOMS \"Rooms.\"\n\n    A room means a place for messages.\n\n    [ROOM-KINDS]\n    The room type is private or public.\n    [ROOM-OPEN] The room type is open.\n",
        )
        File(root, "tests").mkdirs()
        File(root, "tests/rooms.rs").writeText("// trion: verifies chat#ROOM-KINDS, chat#CHAT-1\n#[test]\nfn kinds() {}\n")
        val glossary = """[{"term":"room::room","status":"explicit","kinds":["entity"],"occurrences":3,"first_use":"spec/rooms.trion:7","declared_at":null,"defined_at":"spec/rooms.trion:7","definition":"A room means a place for messages.","derivation":null},
            {"term":"chat service","status":"derived","kinds":["entity"],"occurrences":1,"first_use":"spec/chat.trion:11","declared_at":null,"defined_at":null,"definition":null,"derivation":{"interpretation":["entity"],"rules":["the subject of an action is an entity"],"premises":["spec/chat.trion:11"],"referenced":[]}}]"""
        File(root, "glossary.json").writeText(glossary)
        val check = """{"diagnostics":[{"severity":"error","code":"contradiction","message":"these specifications cannot all hold","refs":[{"id":"ROOM-KINDS","file":"spec/rooms.trion","line":10,"text":"The room type is private or public."},{"id":"ROOM-OPEN","file":"spec/rooms.trion","line":11,"text":"The room type is open."}]},
            {"severity":"warning","code":"spec-without-test","message":"this rule has no linked test","refs":[{"id":"CHAT-1","file":"spec/chat.trion","line":11,"text":"x"}]}],
            "consistency":{"status":"unsatisfiable","verdict":"inconsistent"}}"""
        File(root, "check.json").writeText(check)
        val binary = File(root, "trion-stub")
        binary.writeText(
            "#!/bin/sh\necho \"$*\" >> '${root.path}/calls'\ncase \"$*\" in\n" +
                "  *glossary*) cat '${root.path}/glossary.json' ;;\n" +
                "  *check*) cat '${root.path}/check.json'; exit 1 ;;\n" +
                "  explain*) echo \"[$2] The room type is private or public.\"; echo \"sources: R#ROOMS\" ;;\n" +
                "  render*) $render ;;\n" +
                "esac\n",
        )
        assertTrue(binary.setExecutable(true))
        val settings = TrionSettings.getInstance()
        val previous = settings.serverPath
        settings.serverPath = binary.path
        Disposer.register(testRootDisposable) { settings.serverPath = previous }
        // The annotator reads the outlines of the package in the background when a file opens.
        background { TrionCli.getInstance(project).index(root) }
    }

    private fun open(relative: String): PsiFile {
        val virtual = LocalFileSystem.getInstance().refreshAndFindFileByIoFile(File(root, relative))!!
        myFixture.openFileInEditor(virtual)
        return PsiManager.getInstance(project).findFile(virtual)!!
    }

    /** The file name and the line text that Go to Declaration reaches from the first [marker] in a file. */
    private fun declaration(relative: String, marker: String, inside: Int = 1): String? {
        val file = open(relative)
        val offset = file.text.indexOf(marker) + inside
        val targets = TrionGotoDeclarationHandler().getGotoDeclarationTargets(file.findElementAt(offset), offset, myFixture.editor) ?: return null
        val target = targets.single()
        val text = target.containingFile.text
        val start = target.textRange.startOffset
        val line = text.substring(text.lastIndexOf('\n', start) + 1, text.indexOf('\n', start).let { if (it < 0) text.length else it })
        return "${target.containingFile.name}: ${line.trim()}"
    }

    // trion: verifies trion#EDITOR-IDEA-NAVIGATE-INCLUDE
    fun testAnIncludeOpensTheIncludedFile() {
        stubPackage()
        assertEquals("rooms.trion: namespace chat.room:", declaration("spec/chat.trion", "\"rooms.trion\"", 3))
        assertEquals("rooms.trion: namespace chat.room:", declaration("spec/chat.trion", "include", 2))
    }

    // trion: verifies trion#EDITOR-IDEA-NAVIGATE
    fun testNamespacesSourcesQuotesAndStatementsAreReachable() {
        stubPackage()
        assertEquals("rooms.trion: namespace chat.room:", declaration("spec/chat.trion", "chat.room", 6))
        assertEquals("rooms.trion: source R:", declaration("spec/chat.trion", "cite R", 5))
        assertEquals("rooms.trion: quote ROOMS \"Rooms.\"", declaration("spec/chat.trion", "#ROOMS", 2))
        assertEquals("rooms.trion: [ROOM-KINDS]", declaration("spec/chat.trion", "[ROOM-KINDS]", 3))
        // A verification marker in a test of another language leads to the statement.
        assertEquals("rooms.trion: [ROOM-KINDS]", declaration("tests/rooms.rs", "ROOM-KINDS", 2))
        assertEquals("chat.trion: [CHAT-1] The chat service shall keep each room.", declaration("tests/rooms.rs", "CHAT-1", 2))
    }

    // trion: verifies trion#EDITOR-IDEA-TERM-DOC
    fun testATermLeadsToItsDefinitionAndSaysWhatItIs() {
        stubPackage()
        // Navigation never waits for the command: it uses the glossary once the glossary is read.
        background { TrionCli.getInstance(project).glossary(root) }
        // `each room` in another file resolves to the definition of `room`.
        assertEquals("rooms.trion: A room means a place for messages.", declaration("spec/chat.trion", "each room", 6))
        val chat = open("spec/chat.trion")
        val defined = reading { TrionDocumentationProvider.documentation(chat, chat.text.indexOf("each room") + 6) }!!
        assertTrue(defined, defined.contains("defined term") && defined.contains("A room means a place for messages.") && defined.contains("spec/rooms.trion:7"))
        // A term with no definition says so, and says how it is read.
        val derived = reading { TrionDocumentationProvider.documentation(chat, chat.text.indexOf("chat service") + 7) }!!
        assertTrue(derived, derived.contains("<b>chat service</b>") && derived.contains("no definition or declaration") && derived.contains("the subject of an action is an entity"))
        // The longest run of words wins over a single word.
        val target = TrionResolver.targetAt(chat.text, chat.text.indexOf("chat service") + 1) as TrionTarget.Term
        assertEquals("chat service", TrionResolver.term(target, background { TrionCli.getInstance(project).glossary(root) })!!.term)
        val provider = TrionDocumentationProvider()
        assertNotNull(provider.getCustomDocumentationElement(myFixture.editor, chat, chat.findElementAt(chat.text.indexOf("chat service")), chat.text.indexOf("chat service")))
    }

    // trion: verifies trion#EDITOR-IDEA-STATEMENT-DOC
    fun testAStatementIdentifierShowsItsExplanation() {
        stubPackage()
        val rooms = open("spec/rooms.trion")
        val leaf = rooms.findElementAt(rooms.text.indexOf("[ROOM-KINDS]") + 2)
        val doc = reading { TrionDocumentationProvider().generateDoc(null, leaf) }!!
        assertTrue(doc, doc.contains("[ROOM-KINDS] The room type is private or public.") && doc.contains("sources: R#ROOMS"))
        assertTrue(File(root, "calls").readText().contains("explain ROOM-KINDS ${root.path}"))
    }

    // trion: verifies trion#EDITOR-IDEA-DIAGNOSTICS
    fun testCheckResultsMarkTheirLinesAndSayWhetherThePackageHolds() {
        stubPackage()
        val rooms = open("spec/rooms.trion")
        val annotator = TrionExternalAnnotator()
        val request = annotator.collectInformation(rooms)!!
        assertEquals("spec/rooms.trion", request.relative)
        val report = background { annotator.doAnnotate(request) }!!
        assertTrue(File(root, "calls").readText().contains("--json check ${root.path}"))
        assertEquals("inconsistent", report.verdict)
        val marks = TrionExternalAnnotator.marks(report, request.relative, rooms.text)
        // The banner, then one mark on each statement of the contradiction; the warning is in another file.
        assertEquals(3, marks.size)
        assertNull(marks[0].range)
        assertEquals(HighlightSeverity.WARNING, marks[0].severity)
        assertEquals("trion: inconsistent; 1 error, 1 warning in the package", marks[0].message)
        assertEquals(listOf("The room type is private or public.", "[ROOM-OPEN] The room type is open."), marks.drop(1).map { rooms.text.substring(it.range!!.startOffset, it.range!!.endOffset) })
        assertTrue(marks.drop(1).all { it.severity == HighlightSeverity.ERROR && it.message == "contradiction: these specifications cannot all hold" })
        assertTrue(marks[1].tooltip.contains("with ROOM-OPEN (spec/rooms.trion:11)"))
        val chat = TrionExternalAnnotator.marks(report, "spec/chat.trion", File(root, "spec/chat.trion").readText())
        assertEquals(listOf(HighlightSeverity.WARNING, HighlightSeverity.WARNING), chat.map { it.severity })
        // A package that holds says so.
        val fine = TrionCli.parseReport(TrionOutput(0, "{\"diagnostics\":[],\"consistency\":{\"status\":\"satisfiable\",\"verdict\":\"consistent\"}}", ""))
        val banner = TrionExternalAnnotator.marks(fine, "spec/rooms.trion", rooms.text).single()
        assertEquals(HighlightSeverity.INFORMATION, banner.severity)
        assertEquals("trion: consistent; 0 errors, 0 warnings in the package", banner.message)
        // A run that prints no report is reported, not swallowed.
        val broken = TrionCli.parseReport(TrionOutput(2, "", "error: cannot read trion.toml\n"))
        assertEquals("trion: error: cannot read trion.toml", broken.summary())
    }

    // trion: verifies trion#EDITOR-IDEA-TIME-LIMIT
    fun testACommandThatDoesNotFinishIsStopped() {
        val directory = FileUtil.createTempDirectory("trion-slow", null)
        Disposer.register(testRootDisposable) { directory.deleteRecursively() }
        val slow = File(directory, "trion-slow")
        slow.writeText("#!/bin/sh\nsleep 30\necho late\n")
        assertTrue(slow.setExecutable(true))
        val started = System.currentTimeMillis()
        val output = TrionCli.execute(slow, directory, listOf("check", directory.path), seconds = 1)
        assertTrue("the command ran on", System.currentTimeMillis() - started < 10_000)
        assertEquals(-1, output.exit)
        assertEquals("", output.stdout)
        assertTrue(output.stderr, output.stderr.contains("did not finish within 1 seconds"))
    }

    // trion: verifies trion#EDITOR-IDEA-BINARY
    fun testTheBinaryIsTheConfiguredOneOrTheBuildOfTheProject() {
        stubPackage()
        val project = FileUtil.createTempDirectory("trion-project", null)
        Disposer.register(testRootDisposable) { project.deleteRecursively() }
        assertNull(resolveBinary("/does/not/exist/trion", project.path)?.takeIf { it.path.startsWith(project.path) })
        val built = File(project, "target/debug/trion")
        built.parentFile.mkdirs()
        built.writeText("#!/bin/sh\n")
        assertTrue(built.setExecutable(true))
        assertEquals(built, resolveBinary("/does/not/exist/trion", project.path))
        assertEquals(File(root, "trion-stub"), resolveBinary(File(root, "trion-stub").path, project.path))
        assertEquals(root, packageRoot(File(root, "spec/rooms.trion")))
        assertNull(packageRoot(File("/")))
    }

    // trion: verifies trion#EDITOR-IDEA-PREVIEW
    fun testThePreviewShowsWhatRenderPrints() {
        stubPackage()
        val rooms = open("spec/rooms.trion")
        val html = background { TrionPreviewHtml.render(project, rooms.virtualFile) }
        assertTrue(html, html.contains("data-line=\"4\"") && html.contains("Rooms"))
        assertTrue(File(root, "calls").readText().contains("render ${root.path} --file spec/rooms.trion"))
        val script = TrionPreviewHtml.scrollScript("spec/rooms.trion", 9)
        assertTrue(script.contains("data-line") && script.contains("spec/rooms.trion") && script.contains("l<=9"))
        val provider = TrionSplitEditorProvider()
        assertTrue(provider.accept(project, rooms.virtualFile))
        assertFalse(provider.accept(project, open("tests/rooms.rs").virtualFile))
    }

    // trion: verifies trion#EDITOR-IDEA-PREVIEW
    fun testThePreviewExplainsWhyItIsEmpty() {
        stubPackage("echo \"error: unrecognized subcommand 'render'\" >&2; exit 2")
        val rooms = open("spec/rooms.trion")
        val old = background { TrionPreviewHtml.render(project, rooms.virtualFile) }
        assertTrue(old, old.contains("This trion binary has no render command"))
        val outside = FileUtil.createTempFile("alone", ".trion")
        Disposer.register(testRootDisposable) { outside.delete() }
        outside.writeText("namespace x\n")
        val alone = LocalFileSystem.getInstance().refreshAndFindFileByIoFile(outside)!!
        assertTrue(background { TrionPreviewHtml.render(project, alone) }.contains("No trion.toml was found"))
    }

    private val repository = File(System.getProperty("user.dir")).resolve("../..").canonicalFile

    // trion: verifies trion#EDITOR-IDEA-HIGHLIGHT, trion#EDITOR-IDEA-FOLDING
    fun testTheSpecificationOfTheRepositoryLexesAndFolds() {
        val files = File(repository, "spec").walkTopDown().filter { it.name.endsWith(".trion") }.toList()
        assertTrue(files.size > 10)
        for (file in files) {
            val text = file.readText()
            val all = tokens(text)
            assertFalse(file.path, all.any { it.second == "BAD" })
            // Every directive keyword starts a line, and no comment or string is split.
            assertTrue(file.path, all.filter { it.second == "COMMENT" }.all { it.first.startsWith("//") })
            for ((range, _) in TrionFoldingBuilder.regions(text)) {
                assertTrue(file.path, range.startOffset < range.endOffset && range.endOffset <= text.length)
            }
        }
        val entry = tokens(File(repository, "spec/trion.trion").readText())
        assertEquals("DIRECTIVE", typeOf(entry, "package"))
        assertEquals("DIRECTIVE", typeOf(entry, "include"))
        assertEquals("DIRECTIVE", typeOf(entry, "namespace"))
        assertEquals("DIRECTIVE", typeOf(entry, "cite"))
        assertTrue(entry.any { it.first == "section" && it.second == "DIRECTIVE" })
    }

    // trion: verifies trion#EDITOR-IDEA-TERM-DOC, trion#EDITOR-IDEA-DIAGNOSTICS
    fun testTheBuiltBinaryExplainsTheTrionLanguageAndChecksTheRepository() {
        val binary = File(repository, "target/debug/trion")
        if (!binary.canExecute()) {
            return
        }
        val settings = TrionSettings.getInstance()
        val previous = settings.serverPath
        settings.serverPath = binary.path
        Disposer.register(testRootDisposable) { settings.serverPath = previous }
        val cli = TrionCli.getInstance(project)
        val text = File(repository, "spec/trion.trion").readText()
        val offset = text.indexOf("The trion language is a formal") + 6
        val target = TrionResolver.targetAt(text, offset) as TrionTarget.Term
        val glossary = background { cli.glossary(repository) }
        val term = TrionResolver.term(target, glossary)
        assertNotNull("the glossary has no entry for `trion language`", term)
        assertEquals("trion language", term!!.term.substringAfterLast("::"))
        assertNotNull(background { TrionResolver.locate(target, File(repository, "spec/trion.trion"), repository) { glossary } })
        assertTrue(TrionDocumentationProvider.termDocumentation(term).contains("trion language"))
        // The report of the real command is read on a small package: the time of the whole repository is not what this test is about.
        val small = FileUtil.createTempDirectory("trion-small", null)
        Disposer.register(testRootDisposable) { small.deleteRecursively() }
        File(small, "trion.toml").writeText("[package]\nname = \"p\"\nentry = \"a.trion\"\n")
        File(small, "a.trion").writeText("package p\nnamespace p\n[A] The API shall stop.\n[LONE] The gadget shall frobnicate the widget.\n")
        val report = background { cli.check(small) }!!
        assertNull(report.failure)
        assertEquals("consistent", report.verdict)
        assertTrue(report.summary(), report.ungrounded.isEmpty())
        assertNotNull(report.verdict)
        // The real report states its bounds, and how much of the package says nothing.
        assertTrue(report.summary(), report.summary().contains("within traces of"))
    }

    // trion: verifies trion#EDITOR-IDEA-PRIORITY
    fun testPriorityLinesAndControlDeclarationsAreRead() {
        val text = """
            namespace p:
                environment user
                system API
                [OPEN] The door shall be open.
                [ALARM] While the alarm is active, the door shall be closed.
                    overrides [OPEN], [SHUT]
                [S] The API should log the call.
                    weight 3
                [D] The API shall accept the request.
                    default
                The system shall keep the default route of the environment
                and the weight of each parcel.
        """.trimIndent()
        val all = tokens(text)
        val on = { line: String -> tokens(line).filter { it.first.isNotBlank() }.map { it.second } }
        assertEquals(listOf("DIRECTIVE", "NAME"), on("environment user"))
        assertEquals(listOf("DIRECTIVE", "NAME"), on("system API"))
        val priority = tokens("    overrides [OPEN], [SHUT]").filter { it.first.isNotBlank() }
        assertEquals("overrides" to "DIRECTIVE", priority.first())
        assertTrue(priority.toString(), priority.any { it.first.contains("OPEN") && it.second != "WORD" })
        assertEquals("DIRECTIVE", on("    default").first())
        assertEquals("DIRECTIVE", on("    weight 3").first())
        // The same words inside a sentence are sentence words.
        for (word in listOf("system", "default", "environment", "weight")) {
            assertEquals(word, "WORD", all.last { it.first == word }.second)
        }
        assertFalse(all.any { it.second == "BAD" })
        // The structure view lists who controls an actor.
        val kinds = TrionOutline.entries(text).map { "${it.kind} ${it.name}" }
        assertTrue(kinds.toString(), "environment user" in kinds && "system API" in kinds)
        // An identifier of a priority line leads to its statement.
        assertEquals(TrionTarget.Statement("OPEN"), TrionResolver.targetAt(text, text.indexOf("[OPEN], [SHUT]") + 2))
        assertEquals(TrionTarget.Statement("SHUT"), TrionResolver.targetAt(text, text.indexOf("[SHUT]") + 3))
    }

    // trion: verifies trion#EDITOR-IDEA-DECISIONS
    fun testTheBannerCountsOverlapsAndAssumptions() {
        val json = """{"diagnostics":[],"consistency":{"verdict":"consistent","status":"satisfiable","bounds":{"decisions":null,"trace_length":3,"scope":3}},
            "overlaps":[{"first":{"id":"J1"},"second":{"id":"J2"},"conditions":[],"message":"m"}],
            "environment":{"assumptions":[{"statement":{"id":"E1"},"actor":"user","message":"m"},{"statement":{"id":"E3"},"actor":"user","message":"m"}],"unrealizable":[]}}"""
        val report = TrionCli.parseReport(TrionOutput(0, json, ""))
        assertEquals(1, report.overlaps)
        assertEquals(2, report.assumptions)
        val summary = report.summary()
        assertTrue(summary, summary.contains("1 condition overlap, 2 assumptions about the environment"))
        // A report without them says nothing about them.
        val plain = TrionCli.parseReport(TrionOutput(0, """{"diagnostics":[],"consistency":{"verdict":"consistent","status":"satisfiable"}}""", "")).summary()
        assertFalse(plain, plain.contains("overlap") || plain.contains("assumption"))
    }

    // trion: verifies trion#EDITOR-IDEA-DECLARATIONS
    fun testNewDeclarationsAndTheRefinementLineAreReadAsDeclarations() {
        val text = """
            namespace p:
                primitive message
                predicate reachable(node, node)
                diagram kind transition:
                    element "${'$'}from -> ${'$'}to;"
                    expansion "While the door is ${'$'}from, the light shall be ${'$'}to."
                compatibility BASE-SENTENCES:
                    source ORACLE
                    revision "abc"
                    form Event-driven
                [TOP] The API shall keep each message.
                    detailed by [SAVE], [LOAD]
                [SAVE] The API shall save each message.
                Each guest is a user. No guest is a member.
                The primitive value of the message is detailed by the sender.
        """.trimIndent()
        val all = tokens(text)
        val on = { line: String -> tokens(line.trim()).filter { it.first.isNotBlank() }.map { it.second } }
        assertEquals(listOf("DIRECTIVE", "NAME"), on("primitive message"))
        assertEquals(listOf("DIRECTIVE", "DIRECTIVE", "NAME", "PUNCTUATION"), on("diagram kind transition:"))
        assertEquals(listOf("DIRECTIVE", "NAME", "PUNCTUATION"), on("compatibility BASE-SENTENCES:"))
        assertEquals("DIRECTIVE", on("element \"x\"").first())
        val refinement = tokens("detailed by [SAVE], [LOAD]").filter { it.first.isNotBlank() }
        assertEquals(listOf("detailed" to "DIRECTIVE", "by" to "DIRECTIVE"), refinement.take(2))
        assertTrue(refinement.toString(), refinement.any { it.first.contains("SAVE") && it.second != "WORD" })
        // The same words inside a sentence are sentence words.
        assertEquals("WORD", all.last { it.first == "primitive" }.second)
        assertEquals("WORD", all.last { it.first == "detailed" }.second)
        assertFalse(all.any { it.second == "BAD" })
        // The structure view lists the new declarations.
        val kinds = TrionOutline.entries(text).map { "${it.kind} ${it.name}" }
        for (wanted in listOf("primitive message", "predicate reachable", "diagram kind transition", "compatibility BASE-SENTENCES", "statement TOP")) {
            assertTrue("$wanted in $kinds", wanted in kinds)
        }
        // An identifier of a refinement line leads to its statement.
        val column = text.indexOf("[SAVE], [LOAD]") + 2
        assertEquals(TrionTarget.Statement("SAVE"), TrionResolver.targetAt(text, column))
        assertEquals(TrionTarget.Statement("LOAD"), TrionResolver.targetAt(text, text.indexOf("[LOAD]") + 3))
    }

    // trion: verifies trion#EDITOR-IDEA-NAVIGATE
    fun testARefinementLineLeadsToTheDetailingStatement() {
        stubPackage()
        File(root, "spec/chat.trion").appendText("            detailed by [ROOM-KINDS], [ROOM-OPEN]\n")
        LocalFileSystem.getInstance().refreshAndFindFileByIoFile(File(root, "spec/chat.trion"))!!.refresh(false, false)
        assertEquals("rooms.trion: [ROOM-OPEN] The room type is open.", declaration("spec/chat.trion", "[ROOM-OPEN]", 3))
        assertEquals("rooms.trion: [ROOM-KINDS]", declaration("spec/chat.trion", "detailed by [ROOM-KINDS]", 15))
    }

    // trion: verifies trion#EDITOR-IDEA-DIAGNOSTICS, trion#EDITOR-IDEA-UNREAD-ERROR
    fun testAnUnreadPartAndAnUngroundedStatementAreErrorsOnTheirPlace() {
        val json = """{"diagnostics":[],"consistency":{"status":"satisfiable","verdict":"consistent","bounds":{"decisions":null,"trace_length":3}},
            "opaque":[{"severity":"error","code":"UNSUPPORTED_SEMANTICS","message":"`another` is a word that tells two things apart","refs":[{"id":"A","file":"a.trion","line":2,"text":"x"}]}],
            "ungrounded":[{"severity":"error","code":"ungrounded","message":"this statement constrains nothing","refs":[{"id":"B","file":"a.trion","line":4,"text":"y"}]},
                          {"severity":"error","code":"ungrounded","message":"this statement constrains nothing","refs":[{"id":"C","file":"b.trion","line":1,"text":"z"}]}]}"""
        val report = TrionCli.parseReport(TrionOutput(1, json, ""))
        assertEquals(3, report.errors)
        assertEquals("trion: consistent within traces of 3 moments; 3 errors, 0 warnings in the package; not read: 1 part without a formal reading, 2 ungrounded statements", report.summary())
        // The sentence of [A] wraps: the unread word stands on its second line.
        val text = "namespace p\n[A] The API shall log\n    another call.\n[B] The gadget shall frobnicate.\n"
        val marks = TrionExternalAnnotator.marks(report, "a.trion", text)
        // The banner warns, and each of the two places of this file is an error without any setting.
        assertEquals(listOf(HighlightSeverity.WARNING, HighlightSeverity.ERROR, HighlightSeverity.ERROR), marks.map { it.severity })
        assertEquals("another", marks[1].range!!.substring(text))
        assertEquals("[B] The gadget shall frobnicate.", marks[2].range!!.substring(text))
        assertTrue(marks[1].message, marks[1].message.startsWith("UNSUPPORTED_SEMANTICS: `another`"))
        // A word inside another word is not the named part.
        assertNull(TrionExternalAnnotator.namedPart("[A] The API shall log anotherness.\n", 1, "`another` is not read"))
        val bounded = TrionCli.parseReport(TrionOutput(0, """{"diagnostics":[],"consistency":{"verdict":"unknown","bounds":{"decisions":200,"trace_length":3,"scope":2}}}""", ""))
        assertTrue(bounded.summary(), bounded.summary().contains("unknown within traces of 3 moments and 2 individuals of each type and 200 decisions for each query"))
    }

    // trion: verifies trion#EDITOR-IDEA-MEASURE
    fun testAMeasureDeclarationAndTheFieldsOfAnExampleAreRead() {
        val text = "namespace p\n    measure requests\n    example R:\n        kind reading\n        base \"The API shall stop.\"\n        candidate \"The API shall not stop.\"\n    check C:\n        using definitions\n"
        val found = tokens(text)
        assertTrue(found.toString(), found.contains("measure" to "DIRECTIVE") && found.contains("requests" to "NAME"))
        for (word in listOf("base", "candidate", "using", "kind")) {
            assertTrue("$word: $found", found.contains(word to "DIRECTIVE"))
        }
        assertTrue(TrionOutline.entries(text).any { it.kind == "measure" && it.name == "requests" })
        // A sentence that begins with the word is no declaration.
        assertNull(TrionLines.directive("measure the load of each request before the deadline."))
    }

    // trion: verifies trion#EDITOR-IDEA-COMPLETION
    fun testTheWordsThatTheLanguageFixesAreCompletedWithoutTheCommand() {
        val (prefix, words) = TrionCompletion.candidates("    me")
        assertEquals("me", prefix)
        for (word in listOf("measure", "primitive", "environment", "system", "detailed by", "overrides", "default", "weight", "compatibility", "diagram kind", "using definitions")) {
            assertTrue(word, words.contains(word))
        }
        assertEquals("re" to TrionCompletion.kinds, TrionCompletion.candidates("        kind re"))
        assertTrue(TrionCompletion.kinds.contains("reading"))
        assertTrue(TrionCompletion.candidates("        expect ").second.contains("inconsistent"))
        // Inside a sentence the words are the author's.
        assertTrue(TrionCompletion.candidates("The API shall re").second.isEmpty())
        // The contributor is registered for the language.
        val contributors = com.intellij.codeInsight.completion.CompletionContributor.forLanguage(TrionLanguage)
        assertTrue(contributors.toString(), contributors.any { it is TrionCompletionContributor })
    }

    // trion: verifies trion#EDITOR-IDEA-RESPONSIVE
    fun testNothingRunsTheCommandOrReadsThePackageOnTheUiThread() {
        stubPackage()
        File(root, "calls").delete()
        assertTrue(ApplicationManager.getApplication().isDispatchThread)
        val cli = TrionCli.getInstance(project)
        // A call on the UI thread is an error that this test would see.
        for (call in listOf<() -> Any?>({ cli.run(root, "--json", "check", root.path) }, { cli.check(root) }, { cli.explain(root, "ROOM-KINDS") }, { cli.render(root, "spec/rooms.trion") })) {
            try {
                call()
                fail("the command ran on the UI thread")
            } catch (expected: IllegalStateException) {
                assertTrue(expected.message, expected.message!!.contains("on the UI thread"))
            }
        }
        assertFalse("no process was started", File(root, "calls").exists())
        // What the UI thread may ask for answers at once from what is known.
        cli.knownGlossary(root)
        cli.knownIndex(root)
        // Every handler that the platform calls on the UI thread stays clear of the command.
        val chat = open("spec/chat.trion")
        val offset = chat.text.indexOf("[ROOM-KINDS]") + 3
        TrionGotoDeclarationHandler().getGotoDeclarationTargets(chat.findElementAt(offset), offset, myFixture.editor)
        TrionGotoDeclarationHandler().getGotoDeclarationTargets(chat.findElementAt(chat.text.indexOf("each room") + 6), chat.text.indexOf("each room") + 6, myFixture.editor)
        TrionDocumentationProvider().getCustomDocumentationElement(myFixture.editor, chat, chat.findElementAt(offset), offset)
        TrionExternalAnnotator().collectInformation(chat)
        TrionFoldingBuilder.regions(chat.text)
        TrionStructureElement.children(chat, null)
        TrionSplitEditorProvider().accept(project, chat.virtualFile)
    }

    // trion: verifies trion#EDITOR-IDEA-PREVIEW
    fun testEachPreviewShowsItsOwnFileAndIsDrawnAgainWhenItsFileChanges() {
        stubPackage("echo \"<html><body data-args='${'$'}*'>${'$'}(cat stamp 2>/dev/null)</body></html>\"")
        val rooms = LocalFileSystem.getInstance().refreshAndFindFileByIoFile(File(root, "spec/rooms.trion"))!!
        val chat = LocalFileSystem.getInstance().refreshAndFindFileByIoFile(File(root, "spec/chat.trion"))!!
        val shownRooms = ArrayList<String>()
        val shownChat = ArrayList<String>()
        val first = TrionPreviewModel(project, rooms) { shownRooms.add(it) }
        val second = TrionPreviewModel(project, chat) { shownChat.add(it) }
        first.placeholder()
        assertTrue(shownRooms.single().contains("Rendering rooms.trion"))
        background { first.render(); second.render() }
        assertTrue(shownRooms.last(), shownRooms.last().contains("--file spec/rooms.trion"))
        assertTrue(shownChat.last(), shownChat.last().contains("--file spec/chat.trion"))
        assertEquals("spec/chat.trion", second.relative())
        // Selecting a file again renders it again; the same document is not loaded twice.
        val before = shownChat.size
        background { second.render() }
        assertEquals(before, shownChat.size)
        // A change of the package gives a new document for the same file.
        File(root, "stamp").writeText("changed")
        background { second.render() }
        assertEquals(before + 1, shownChat.size)
        assertTrue(shownChat.last().contains("changed") && shownChat.last().contains("--file spec/chat.trion"))
        // The placeholder is shown only before the first document.
        second.placeholder()
        assertEquals(before + 1, shownChat.size)
    }
}
