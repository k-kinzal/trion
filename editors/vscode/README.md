# Trion for VS Code

Language support for the trion specification language: `.trion` files get syntax highlighting, and diagnostics, hover, go-to-definition, completion and semantic tokens from `trion lsp`.

A sentence that passes `trion check` is formally interpreted and verified. The server therefore publishes as errors, where they stand, each part of a sentence without a formal reading (`UNSUPPORTED_SEMANTICS`, marked on the word that the message names) and each statement that constrains nothing (`ungrounded`). A condition overlap and an assumption about the environment are information.

The command **Trion: Open Preview to the Side** shows the document that `trion render` prints for the file.

The grammar highlights `//` comments, `"..."` and `"""..."""` strings, block headers ending in `:`, the flat `namespace` and `section` headers, `cite`, `unsourced` and `ratified` annotations, the lines `detailed by`, `overrides`, `default` and `weight` under a statement, the declarations `term`, `predicate`, `primitive`, `measure`, `environment` and `system`, the fields of sources, checks, examples (also of the kind `reading`), traces, flows, diagram kinds and compatibility blocks, `[ID]` identifiers and `package#ID` references, and the EARS and modal keywords of each sentence. **Toggle Line Comment** inserts `//`, a line ending in `:` indents the next line, and blocks fold by indentation.

## Requirements

The `trion` binary with the `lsp` command. From the trion repository:

```
cargo install --path crates/trion-cli
```

The extension looks for `trion` on `PATH`, then in `~/.cargo/bin`. Highlighting works without the binary.

## Settings

| Setting | Default | Meaning |
| --- | --- | --- |
| `trion.server.path` | `trion` | The binary, as a command name or an absolute path. A leading `~` is expanded. |
| `trion.trace.server` | `off` | Logs LSP traffic to the "Trion Language Server" output channel. |

Changing `trion.server.path` restarts the server. In an untrusted workspace, a value set by the workspace is ignored.

The command **Trion: Restart Language Server** restarts it by hand.

## Building

The grammar lives in `editors/grammar/` and is copied in by the build, so edit it there. Its tests are in `editors/grammar/test/` (`npm install && npm test`).

```
npm install
npm run compile     # copies the grammar, type-checks, bundles to out/extension.js
npm test            # tests binary lookup and that activation starts `trion lsp` for trion files
npm run package     # writes trion.vsix
code --install-extension trion.vsix
```
