import * as vscode from 'vscode';
import {
  LanguageClient,
  type LanguageClientOptions,
  type ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';
import { renderDocument } from './preview';
import { dirname, join } from 'node:path';
import { resolveServerPath } from './serverPath';

const INSTALL_COMMAND = 'cargo install --path crates/trion-cli && cargo install --path crates/trion-lsp';

let client: LanguageClient | undefined;
let outputChannel: vscode.OutputChannel | undefined;
/** Serializes starts and stops, so that a restart cannot race an earlier one. */
let lifecycle: Promise<void> = Promise.resolve();

function enqueue(step: () => Promise<void>): Promise<void> {
  lifecycle = lifecycle.then(step, step);
  return lifecycle;
}

function configuredServerPath(): string {
  return vscode.workspace.getConfiguration('trion').get<string>('server.path', 'trion');
}

async function reportMissingBinary(configured: string): Promise<void> {
  const openSettings = 'Open Settings';
  const copyInstall = 'Copy Install Command';
  const retry = 'Retry';
  const choice = await vscode.window.showErrorMessage(
    `Trion: cannot find the language server binary "${configured}". ` +
      `Install it from the trion repository with \`${INSTALL_COMMAND}\`, ` +
      'or set "trion.server.path" to the binary. Highlighting still works without it.',
    openSettings,
    copyInstall,
    retry,
  );
  if (choice === openSettings) {
    await vscode.commands.executeCommand('workbench.action.openSettings', 'trion.server.path');
  } else if (choice === copyInstall) {
    await vscode.env.clipboard.writeText(INSTALL_COMMAND);
  } else if (choice === retry) {
    await restart();
  }
}

async function reportStartFailure(binary: string, error: unknown): Promise<void> {
  const showOutput = 'Show Output';
  const retry = 'Retry';
  const detail = error instanceof Error ? error.message : String(error);
  const choice = await vscode.window.showErrorMessage(
    `Trion: "${binary}" failed to start: ${detail}. ` +
      'Check that the path names the trion-lsp binary.',
    showOutput,
    retry,
  );
  if (choice === showOutput) {
    outputChannel?.show();
  } else if (choice === retry) {
    await restart();
  }
}

/** The configured binary, or the one that an open workspace built. */
function findBinary(configured: string): string | undefined {
  const found = resolveServerPath(configured);
  if (found !== undefined) {
    return found;
  }
  for (const folder of vscode.workspace.workspaceFolders ?? []) {
    for (const profile of ['debug', 'release']) {
      const built = resolveServerPath(`${folder.uri.fsPath}/target/${profile}/trion`);
      if (built !== undefined) {
        return built;
      }
    }
  }
  return undefined;
}

/** The open previews, by the file they show. */
const previews = new Map<string, vscode.WebviewPanel>();

async function refreshPreview(file: string): Promise<void> {
  const panel = previews.get(file);
  if (panel !== undefined) {
    panel.webview.html = await renderDocument(findBinary(configuredServerPath()), file);
  }
}

async function openPreview(): Promise<void> {
  const document = vscode.window.activeTextEditor?.document;
  if (document === undefined || document.languageId !== 'trion') {
    return;
  }
  const file = document.uri.fsPath;
  let panel = previews.get(file);
  if (panel === undefined) {
    const name = file.split(/[/\\]/).pop() ?? file;
    // The rendered document carries no script, so the view runs none.
    panel = vscode.window.createWebviewPanel('trion.preview', `Preview ${name}`, vscode.ViewColumn.Beside, { enableScripts: false });
    previews.set(file, panel);
    panel.onDidDispose(() => previews.delete(file));
  } else {
    panel.reveal(vscode.ViewColumn.Beside);
  }
  await refreshPreview(file);
}

async function start(): Promise<void> {
  const configured = configuredServerPath();
  const binary = findBinary(configured);
  if (binary === undefined) {
    void reportMissingBinary(configured);
    return;
  }

  // The language server is the `trion-lsp` command, which is installed beside `trion`.
  const server = resolveServerPath(join(dirname(binary), 'trion-lsp'));
  if (server === undefined) {
    void reportMissingBinary(join(dirname(binary), 'trion-lsp'));
    return;
  }

  const serverOptions: ServerOptions = {
    command: server,
    args: [],
    transport: TransportKind.stdio,
  };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'trion' }],
    outputChannel,
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher('**/{*.trion,trion.toml}'),
    },
  };

  const next = new LanguageClient('trion', 'Trion Language Server', serverOptions, clientOptions);
  client = next;
  try {
    await next.start();
  } catch (error) {
    if (client === next) {
      client = undefined;
    }
    await next.dispose().catch(() => undefined);
    void reportStartFailure(binary, error);
  }
}

async function stop(): Promise<void> {
  const running = client;
  client = undefined;
  if (running !== undefined) {
    await running.dispose().catch(() => undefined);
  }
}

function restart(): Promise<void> {
  return enqueue(async () => {
    await stop();
    await start();
  });
}

export function activate(context: vscode.ExtensionContext): Promise<void> {
  outputChannel = vscode.window.createOutputChannel('Trion Language Server');
  context.subscriptions.push(
    outputChannel,
    vscode.commands.registerCommand('trion.restartServer', restart),
    vscode.commands.registerCommand('trion.openPreview', openPreview),
    vscode.workspace.onDidSaveTextDocument((document) => {
      // A change in one file can change the status of another, so every preview is drawn again.
      if (document.uri.fsPath.endsWith('.trion')) {
        for (const file of previews.keys()) {
          void refreshPreview(file);
        }
      }
    }),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration('trion.server.path')) {
        void restart();
      }
    }),
    vscode.workspace.onDidGrantWorkspaceTrust(() => void restart()),
  );
  return enqueue(start);
}

export function deactivate(): Promise<void> {
  return enqueue(stop);
}
