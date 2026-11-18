// Activates the bundled extension against stand-ins for the `vscode` and
// `vscode-languageclient` modules, and checks the language contribution.
const assert = require('node:assert/strict');
const { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } = require('node:fs');
const Module = require('node:module');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
const { test, after, beforeEach } = require('node:test');
const esbuild = require('esbuild');

const root = join(__dirname, '..');
const scratch = mkdtempSync(join(tmpdir(), 'trion-extension-'));
after(() => rmSync(scratch, { recursive: true, force: true }));

const bundle = join(scratch, 'extension.cjs');
esbuild.buildSync({
  entryPoints: [join(root, 'src', 'extension.ts')],
  outfile: bundle,
  bundle: true,
  platform: 'node',
  format: 'cjs',
  external: ['vscode', 'vscode-languageclient', 'vscode-languageclient/*'],
  logLevel: 'silent',
});

/** What the extension did through the stand-in APIs. */
let calls;
let serverPath;

beforeEach(() => {
  calls = { clients: [], errors: [], commands: [], handlers: {}, panels: [], saved: [] };
  vscode.window.activeTextEditor = undefined;
  vscode.workspace.workspaceFolders = undefined;
  serverPath = 'trion';
});

const disposable = { dispose() {} };
const vscode = {
  workspace: {
    getConfiguration: () => ({ get: (key, fallback) => (key === 'server.path' ? serverPath : fallback) }),
    createFileSystemWatcher: (pattern) => ({ pattern, dispose() {} }),
    onDidChangeConfiguration: () => disposable,
    onDidGrantWorkspaceTrust: () => disposable,
    onDidSaveTextDocument: (listener) => {
      calls.saved.push(listener);
      return disposable;
    },
  },
  ViewColumn: { Beside: -2 },
  window: {
    createOutputChannel: () => ({ show() {}, dispose() {} }),
    createWebviewPanel: (type, title, column, options) => {
      const panel = { type, title, column, options, webview: { html: '' }, onDidDispose: () => disposable, reveal() {} };
      calls.panels.push(panel);
      return panel;
    },
    showErrorMessage: async (message) => {
      calls.errors.push(message);
      return undefined;
    },
  },
  commands: {
    registerCommand: (name, handler) => {
      calls.commands.push(name);
      calls.handlers[name] = handler;
      return disposable;
    },
    executeCommand: async () => undefined,
  },
  env: { clipboard: { writeText: async () => undefined } },
};

class LanguageClient {
  constructor(id, name, serverOptions, clientOptions) {
    Object.assign(this, { id, name, serverOptions, clientOptions, started: false });
    calls.clients.push(this);
  }
  async start() {
    this.started = true;
  }
  async dispose() {}
}
const languageClient = { LanguageClient, TransportKind: { stdio: 0, ipc: 1, pipe: 2, socket: 3 } };

const load = Module._load;
Module._load = function (request, ...rest) {
  if (request === 'vscode') return vscode;
  if (request === 'vscode-languageclient/node') return languageClient;
  return load.call(this, request, ...rest);
};
after(() => {
  Module._load = load;
});
const extension = require(bundle);

async function activate() {
  const context = { subscriptions: [] };
  await extension.activate(context);
  return context;
}

function fakeBinary() {
  const file = join(scratch, 'bin', 'trion');
  mkdirSync(join(scratch, 'bin'), { recursive: true });
  // The language server is the `trion-lsp` command beside `trion`.
  for (const binary of [file, join(scratch, 'bin', 'trion-lsp')]) {
    writeFileSync(binary, '#!/bin/sh\n');
    chmodSync(binary, 0o755);
  }
  return file;
}

// trion: verifies trion#EDITOR-VSCODE, trion#EDITOR-SERVER-PATH
test('activation starts the configured binary as the language server for trion documents', async () => {
  serverPath = fakeBinary();
  const context = await activate();
  assert.equal(calls.clients.length, 1);
  const [client] = calls.clients;
  assert.ok(client.started);
  assert.equal(client.serverOptions.command, join(scratch, 'bin', 'trion-lsp'));
  assert.deepEqual(client.serverOptions.args, []);
  assert.equal(client.serverOptions.transport, languageClient.TransportKind.stdio);
  assert.deepEqual(client.clientOptions.documentSelector, [{ scheme: 'file', language: 'trion' }]);
  assert.equal(client.clientOptions.synchronize.fileEvents.pattern, '**/{*.trion,trion.toml}');
  assert.ok(calls.commands.includes('trion.restartServer'));
  assert.deepEqual(calls.errors, []);
  await extension.deactivate();
  assert.ok(context.subscriptions.length > 0);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a binary that cannot be found starts no client and names the install command', async () => {
  serverPath = join(scratch, 'missing', 'trion');
  await activate();
  assert.equal(calls.clients.length, 0);
  assert.equal(calls.errors.length, 1);
  assert.match(calls.errors[0], /cannot find the language server binary/);
  assert.match(calls.errors[0], /cargo install --path crates\/trion-cli/);
  await extension.deactivate();
});

// trion: verifies trion#EDITOR-VSCODE, trion#EDITOR-INDENT-FOLDING
test('the manifest contributes the trion language with slash line comments', () => {
  const manifest = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  // VS Code derives the onLanguage:trion activation event from the language contribution.
  assert.ok(manifest.activationEvents === undefined || manifest.activationEvents.includes('onLanguage:trion'));
  assert.equal(manifest.main, './out/extension.js');
  const [language] = manifest.contributes.languages;
  assert.equal(language.id, 'trion');
  assert.deepEqual(language.extensions, ['.trion']);

  const configuration = JSON.parse(readFileSync(join(root, language.configuration), 'utf8'));
  assert.deepEqual(configuration.comments, { lineComment: '//' });
  // A block closes where its indentation ends: the editor indents after a header and folds by indentation.
  assert.equal(configuration.indentationRules, undefined);
  assert.deepEqual(configuration.folding, { offSide: true });
  const [enter] = configuration.onEnterRules;
  assert.deepEqual(enter.action, { indent: 'indent' });
  const header = new RegExp(enter.beforeText);
  assert.match('    section "Title":', header);
  assert.match('When the parser receives an input, the parser shall perform all of the following actions:', header);
  assert.doesNotMatch('    // a comment:', header);
  assert.doesNotMatch('section "Room types"', header);
  assert.doesNotMatch('    [A] The API shall stop.', header);
});

/** A package with one file and a stand-in `trion` that prints what it was asked to render. */
function fakePackage() {
  const dir = join(scratch, 'package');
  mkdirSync(join(dir, 'spec'), { recursive: true });
  mkdirSync(join(dir, 'target', 'debug'), { recursive: true });
  writeFileSync(join(dir, 'trion.toml'), '[package]\nname = "p"\n');
  writeFileSync(join(dir, 'spec', 'a.trion'), 'namespace p\n[A] The API shall stop.\n');
  const binary = join(dir, 'target', 'debug', 'trion');
  writeFileSync(binary, '#!/bin/sh\necho "<!doctype html><html><body data-args=\\"$*\\">document</body></html>"\nexit 1\n');
  chmodSync(binary, 0o755);
  return { dir, file: join(dir, 'spec', 'a.trion'), binary };
}

// trion: verifies trion#EDITOR-VSCODE-PREVIEW, trion#EDITOR-BUILT-BINARY
test('the preview shows the rendered document of the open file beside it', async () => {
  const { dir, file } = fakePackage();
  // The configured command does not exist; the binary that the workspace built is used.
  serverPath = join(scratch, 'missing', 'trion');
  vscode.workspace.workspaceFolders = [{ uri: { fsPath: dir } }];
  vscode.window.activeTextEditor = { document: { languageId: 'trion', uri: { fsPath: file } } };
  await activate();
  assert.ok(calls.commands.includes('trion.openPreview'));
  await calls.handlers['trion.openPreview']();
  assert.equal(calls.panels.length, 1);
  const [panel] = calls.panels;
  assert.equal(panel.column, vscode.ViewColumn.Beside);
  // The rendered document needs no script.
  assert.deepEqual(panel.options, { enableScripts: false });
  assert.match(panel.webview.html, new RegExp(`data-args="render ${dir} --file spec/a.trion"`));
  // Saving a trion file draws the preview again.
  panel.webview.html = '';
  calls.saved[0]({ uri: { fsPath: file } });
  await new Promise((resolve) => setTimeout(resolve, 300));
  assert.match(panel.webview.html, /document/);
  // A second request shows the same panel.
  await calls.handlers['trion.openPreview']();
  assert.equal(calls.panels.length, 1);
  await extension.deactivate();
});

// trion: verifies trion#EDITOR-VSCODE-PREVIEW
test('the preview says what is missing instead of a document', async () => {
  const outside = join(scratch, 'loose.trion');
  writeFileSync(outside, 'namespace p\n');
  serverPath = fakeBinary();
  vscode.window.activeTextEditor = { document: { languageId: 'trion', uri: { fsPath: outside } } };
  await activate();
  await calls.handlers['trion.openPreview']();
  assert.match(calls.panels[0].webview.html, /no trion\.toml was found/);
  const manifest = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  assert.ok(manifest.contributes.commands.some((c) => c.command === 'trion.openPreview'));
  assert.equal(manifest.contributes.menus['editor/title'][0].when, 'editorLangId == trion');
  await extension.deactivate();
});
