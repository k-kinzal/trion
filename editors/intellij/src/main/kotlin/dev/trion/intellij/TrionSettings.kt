package dev.trion.intellij

import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.components.PersistentStateComponent
import com.intellij.openapi.components.State
import com.intellij.openapi.components.Storage
import com.intellij.openapi.fileChooser.FileChooserDescriptor
import com.intellij.openapi.options.BoundConfigurable
import com.intellij.openapi.ui.DialogPanel
import com.intellij.openapi.ui.TextFieldWithBrowseButton
import com.intellij.ui.dsl.builder.AlignX
import com.intellij.ui.dsl.builder.bindText
import com.intellij.ui.dsl.builder.panel
import java.util.concurrent.ConcurrentHashMap

internal const val DEFAULT_SERVER_PATH = "trion"

@State(name = "TrionSettings", storages = [Storage("trion.xml")])
class TrionSettings : PersistentStateComponent<TrionSettings.State> {
    class State {
        var serverPath: String = DEFAULT_SERVER_PATH
    }

    private var state = State()

    var serverPath: String
        get() = state.serverPath
        set(value) {
            state.serverPath = value.trim().ifEmpty { DEFAULT_SERVER_PATH }
        }

    override fun getState(): State = state

    override fun loadState(loaded: State) {
        state = loaded
    }

    companion object {
        fun getInstance(): TrionSettings = ApplicationManager.getApplication().getService(TrionSettings::class.java)

        private val listeners = ConcurrentHashMap<String, () -> Unit>()

        /** Registers what runs after the settings are applied. */
        fun onChange(key: String, listener: () -> Unit) {
            listeners[key] = listener
        }

        internal fun changed() = listeners.values.forEach { it() }
    }
}

class TrionConfigurable : BoundConfigurable("Trion") {
    private val settings = TrionSettings.getInstance()

    override fun createPanel(): DialogPanel = panel {
        row("Trion binary:") {
            val field = TextFieldWithBrowseButton()
            field.addBrowseFolderListener(null, FileChooserDescriptor(true, false, false, false, false, false))
            cell(field)
                .align(AlignX.FILL)
                .bindText(settings::serverPath)
                .comment("A command name or a path. Without it the plugin uses the newest of <code>target/release/trion</code> and <code>target/debug/trion</code> of the project. It runs <code>check</code>, <code>glossary</code>, <code>explain</code> and <code>render</code>.")
        }
    }

    override fun apply() {
        super.apply()
        TrionCli.resetMissingBinaryNotice()
        TrionSettings.changed()
    }
}
