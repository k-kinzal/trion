package dev.trion.intellij

import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.editor.event.CaretEvent
import com.intellij.openapi.editor.event.CaretListener
import com.intellij.openapi.editor.event.DocumentEvent
import com.intellij.openapi.editor.event.DocumentListener
import com.intellij.openapi.fileEditor.FileDocumentManager
import com.intellij.openapi.fileEditor.FileEditor
import com.intellij.openapi.fileEditor.FileEditorPolicy
import com.intellij.openapi.fileEditor.FileEditorProvider
import com.intellij.openapi.fileEditor.FileEditorState
import com.intellij.openapi.fileEditor.TextEditor
import com.intellij.openapi.fileEditor.TextEditorWithPreview
import com.intellij.openapi.fileEditor.impl.text.TextEditorProvider
import com.intellij.openapi.project.DumbAware
import com.intellij.openapi.project.Project
import com.intellij.openapi.util.Disposer
import com.intellij.openapi.util.UserDataHolderBase
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.openapi.vfs.VirtualFileManager
import com.intellij.openapi.vfs.newvfs.BulkFileListener
import com.intellij.openapi.vfs.newvfs.events.VFileEvent
import com.intellij.ui.components.JBLabel
import com.intellij.ui.jcef.JBCefApp
import com.intellij.ui.jcef.JBCefBrowser
import com.intellij.util.Alarm
import java.awt.BorderLayout
import java.beans.PropertyChangeListener
import javax.swing.JComponent
import javax.swing.JPanel
import javax.swing.SwingConstants

/** The HTML that the preview shows for a file. */
object TrionPreviewHtml {
    fun message(title: String, detail: String): String =
        "<!doctype html><html><head><meta charset=\"utf-8\"><style>body{font-family:sans-serif;margin:2em;color:#888}pre{white-space:pre-wrap}</style></head>" +
            "<body><h3>${TrionExternalAnnotator.escape(title)}</h3><pre>${TrionExternalAnnotator.escape(detail)}</pre></body></html>"

    fun render(project: Project, file: VirtualFile): String {
        val disk = file.onDisk() ?: return message("No preview", "The file is not on disk.")
        val root = packageRoot(disk) ?: return message("No preview", "No trion.toml was found above ${disk.name}: a preview shows a file of a package.")
        val output = TrionCli.getInstance(project).render(root, disk.relativeTo(root).invariantSeparatorsPath)
            ?: return message("The trion binary was not found", "Build it with `cargo build`, or set its path under Settings | Languages & Frameworks | Trion.")
        if (output.exit != 0 || output.stdout.isBlank()) {
            val old = output.stderr.contains("unrecognized subcommand")
            return message(
                if (old) "This trion binary has no render command" else "The preview could not be rendered",
                if (old) "Update the binary: the preview needs `trion render`.\n\n${output.stderr}" else output.stderr.ifBlank { "trion render exited with ${output.exit}" },
            )
        }
        return output.stdout
    }

    /** Scrolls the page to the statement at or before a 1-based line of a file. */
    fun scrollScript(relative: String, line: Int): String =
        "(function(){var best=null;document.querySelectorAll('[data-line]').forEach(function(e){" +
            "var f=e.getAttribute('data-file');if(f&&f!=='${relative.replace("'", "\\'")}')return;" +
            "var l=parseInt(e.getAttribute('data-line'));if(l<=$line&&(!best||l>=parseInt(best.getAttribute('data-line'))))best=e;});" +
            "if(best)best.scrollIntoView({block:'center'});})();"
}

/**
 * What one preview shows: the rendered document of its own file. It renders in the
 * background, shows a document once, and renders again when the file is selected or a
 * file of the package changes.
 */
class TrionPreviewModel(private val project: Project, val file: VirtualFile, private val show: (String) -> Unit) {
    @Volatile
    private var shown: String? = null

    /** The line of the caret, which the page is kept at after it loads. */
    @Volatile
    var line: Int = 1

    /** The path of the file relative to its package, as the rendered document names it. */
    fun relative(): String? = file.onDisk()?.let { disk -> packageRoot(disk)?.let { disk.relativeTo(it).invariantSeparatorsPath } }

    fun placeholder() {
        if (shown == null) {
            show(TrionPreviewHtml.message("Rendering ${file.name}", "The document appears when trion render finishes."))
        }
    }

    /** Renders the file now, on the calling thread, and shows the document when it changed. */
    fun render() {
        val html = TrionPreviewHtml.render(project, file)
        // The same document is not loaded twice: loading resets the scroll position.
        if (html != shown) {
            shown = html
            show(html)
        }
    }
}

class TrionPreviewEditor(private val project: Project, private val file: VirtualFile) : UserDataHolderBase(), FileEditor {
    private val panel = JPanel(BorderLayout())
    private val browser: JBCefBrowser? = if (JBCefApp.isSupported()) JBCefBrowser() else null
    private val alarm = Alarm(Alarm.ThreadToUse.POOLED_THREAD, this)
    private val model = TrionPreviewModel(project, file) { html ->
        ApplicationManager.getApplication().invokeLater { if (!Disposer.isDisposed(this)) browser?.loadHTML(html) }
    }

    init {
        if (browser != null) {
            Disposer.register(this, browser)
            panel.add(browser.component, BorderLayout.CENTER)
            // A page that has just loaded starts at its top: it is moved to the caret again.
            browser.jbCefClient.addLoadHandler(
                object : org.cef.handler.CefLoadHandlerAdapter() {
                    override fun onLoadEnd(cef: org.cef.browser.CefBrowser?, frame: org.cef.browser.CefFrame?, status: Int) {
                        if (frame?.isMain == true) scroll()
                    }
                },
                browser.cefBrowser,
            )
        } else {
            panel.add(JBLabel("The preview needs the embedded browser (JCEF), which this IDE runtime does not provide.", SwingConstants.CENTER), BorderLayout.CENTER)
        }
        val bus = project.messageBus.connect(this)
        bus.subscribe(
            VirtualFileManager.VFS_CHANGES,
            object : BulkFileListener {
                override fun after(events: List<VFileEvent>) {
                    if (events.any { it.path.endsWith(".trion") || it.path.endsWith("trion.toml") }) refresh(300)
                }
            },
        )
        // A preview that was hidden while the package changed is drawn again when its file is selected.
        bus.subscribe(
            com.intellij.openapi.fileEditor.FileEditorManagerListener.FILE_EDITOR_MANAGER,
            object : com.intellij.openapi.fileEditor.FileEditorManagerListener {
                override fun selectionChanged(event: com.intellij.openapi.fileEditor.FileEditorManagerEvent) {
                    if (event.newFile == file) refresh(0)
                }
            },
        )
        FileDocumentManager.getInstance().getDocument(file)?.addDocumentListener(
            object : DocumentListener {
                override fun documentChanged(event: DocumentEvent) = saveThenRefresh()
            },
            this,
        )
        refresh(0)
    }

    /** `trion render` reads the disk, so a pause in typing saves the document first. */
    private fun saveThenRefresh() {
        alarm.cancelAllRequests()
        alarm.addRequest({
            ApplicationManager.getApplication().invokeLater {
                val documents = FileDocumentManager.getInstance()
                documents.getDocument(file)?.let { if (documents.isDocumentUnsaved(it)) documents.saveDocument(it) }
                refresh(0)
            }
        }, 800)
    }

    fun refresh(delay: Int) {
        if (browser == null) return
        model.placeholder()
        alarm.cancelAllRequests()
        alarm.addRequest({ model.render() }, delay)
    }

    private fun scroll() {
        val relative = model.relative() ?: return
        browser?.cefBrowser?.executeJavaScript(TrionPreviewHtml.scrollScript(relative, model.line), "", 0)
    }

    /** Keeps the page at the statement the caret is on. */
    fun follow(editor: TextEditor) {
        model.line = editor.editor.caretModel.logicalPosition.line + 1
        editor.editor.caretModel.addCaretListener(
            object : CaretListener {
                override fun caretPositionChanged(event: CaretEvent) {
                    model.line = event.newPosition.line + 1
                    // The path is found off the UI thread; the script itself is cheap.
                    alarm.addRequest({ scroll() }, 0)
                }
            },
            this,
        )
    }

    override fun getComponent(): JComponent = panel

    override fun getPreferredFocusedComponent(): JComponent? = browser?.component

    override fun getName(): String = "Preview"

    override fun setState(state: FileEditorState) {}

    override fun isModified(): Boolean = false

    override fun isValid(): Boolean = file.isValid

    override fun addPropertyChangeListener(listener: PropertyChangeListener) {}

    override fun removePropertyChangeListener(listener: PropertyChangeListener) {}

    override fun getFile(): VirtualFile = file

    override fun dispose() {}
}

/** Opens a trion file as text beside its document view, the way a Markdown file opens. */
class TrionSplitEditorProvider : FileEditorProvider, DumbAware {
    override fun accept(project: Project, file: VirtualFile): Boolean = file.fileType == TrionFileType && file.isInLocalFileSystem

    override fun createEditor(project: Project, file: VirtualFile): FileEditor {
        val text = TextEditorProvider.getInstance().createEditor(project, file) as TextEditor
        // A missing embedded browser must never keep the file from opening as text.
        val preview = try {
            TrionPreviewEditor(project, file)
        } catch (error: LinkageError) {
            return text
        }
        preview.follow(text)
        return TextEditorWithPreview(text, preview, "Trion", TextEditorWithPreview.Layout.SHOW_EDITOR_AND_PREVIEW)
    }

    override fun getEditorTypeId(): String = "trion-split-editor"

    override fun getPolicy(): FileEditorPolicy = FileEditorPolicy.HIDE_DEFAULT_EDITOR
}
