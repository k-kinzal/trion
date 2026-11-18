# Trion for IntelliJ

An IntelliJ Platform plugin for the trion specification language. It works on the Community editions and on the other JetBrains IDEs (build 243 and later), and needs no other plugin.

| Feature | Source |
|---|---|
| Syntax highlighting, with its own page under **Settings \| Editor \| Color Scheme \| Trion** | the plugin's lexer |
| Folding by indentation, flat `namespace` and `section` headers fold to the next one | the plugin |
| Structure view: namespaces, sections, declaration blocks, identified statements | the plugin |
| Line comments, quote pairing | the plugin |
| Errors and warnings on their lines, and a banner that says whether the package holds | `trion --json check` |
| Go to Declaration on `include`, `use`, `cite SOURCE#QUOTE`, `ref [ID]`, `[ID]`, verification markers, and terms | the plugin and `trion --json glossary` |
| Quick documentation: what a term is, and what `trion explain` says about a statement identifier | `trion --json glossary`, `trion explain` |
| Split editor with a document preview that follows the caret | `trion render` |
| Completion | `trion lsp`, only where the [LSP4IJ](https://plugins.jetbrains.com/plugin/23257-lsp4ij) plugin is installed |

The commands read the files on disk. Diagnostics describe the saved text, and the preview saves the document after a pause in typing.

## The trion binary

The plugin uses the path under **Settings | Languages & Frameworks | Trion** (default `trion`, searched on `PATH` and then in `~/.cargo/bin`; a leading `~` is expanded). When that is not there, it uses the newer of `target/release/trion` and `target/debug/trion` of the open project. The banner of a file states the consistency result with its bounds and the number of opaque readings and ungrounded statements; **Mark ungrounded statements and opaque readings** on the same settings page marks them on their lines, and is off by default. The plugin never runs the command on the UI thread: navigation uses the outlines and the glossary that were read in the background, so a first jump right after a file opens may find nothing yet. One notification links to the settings page when no binary is found. Highlighting, folding and the structure view work without it.

```
cargo install --path crates/trion-cli
```

## Building

Gradle needs a JDK 17 or newer to run, and provisions the JDK 21 toolchain itself when it is not installed.

```
./gradlew buildPlugin     # writes build/distributions/trion-intellij-<version>.zip
./gradlew test            # headless platform tests
./gradlew verifyPlugin    # checks binary compatibility against the IDE versions in build.gradle.kts
./gradlew runIde          # starts a sandbox IDE with the plugin
```

Install the zip with **Settings | Plugins | Install Plugin from Disk**, and remove an earlier version first.
