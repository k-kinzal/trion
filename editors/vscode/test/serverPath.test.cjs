// Run through `npm test`, which first bundles src/serverPath.ts to out/serverPath.cjs.
const assert = require('node:assert/strict');
const { chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } = require('node:fs');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
const { test, after } = require('node:test');
const { resolveServerPath } = require('../out/serverPath.cjs');

const root = mkdtempSync(join(tmpdir(), 'trion-server-path-'));
after(() => rmSync(root, { recursive: true, force: true }));

function executable(path, mode = 0o755) {
  mkdirSync(join(path, '..'), { recursive: true });
  writeFileSync(path, '#!/bin/sh\n');
  chmodSync(path, mode);
  return path;
}

const env = (overrides) => ({
  path: undefined,
  pathExt: undefined,
  home: join(root, 'nohome'),
  platform: 'darwin',
  ...overrides,
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a bare name is found on PATH', () => {
  const file = executable(join(root, 'a', 'trion'));
  assert.equal(resolveServerPath('trion', env({ path: join(root, 'a') })), file);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a bare name falls back to ~/.cargo/bin', () => {
  const home = join(root, 'home');
  const file = executable(join(home, '.cargo', 'bin', 'trion'));
  assert.equal(resolveServerPath('trion', env({ path: join(root, 'empty'), home })), file);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a missing binary resolves to undefined', () => {
  assert.equal(resolveServerPath('trion', env({ path: join(root, 'empty') })), undefined);
  assert.equal(resolveServerPath('/does/not/exist/trion', env()), undefined);
  assert.equal(resolveServerPath('   ', env()), undefined);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a file without the execute bit does not count', () => {
  executable(join(root, 'noexec', 'trion'), 0o644);
  assert.equal(resolveServerPath('trion', env({ path: join(root, 'noexec') })), undefined);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('an absolute path and a leading tilde are honored', () => {
  const home = join(root, 'tilde');
  const file = executable(join(home, 'bin', 'trion'));
  assert.equal(resolveServerPath(file, env()), file);
  assert.equal(resolveServerPath('~/bin/trion', env({ home })), file);
});

// trion: verifies trion#EDITOR-SERVER-PATH
test('a relative path is rejected rather than resolved against an unknown directory', () => {
  assert.equal(resolveServerPath('./trion', env({ path: root })), undefined);
});
