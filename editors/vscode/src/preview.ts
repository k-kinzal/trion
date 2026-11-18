// Finds what the preview shows. This module does not import `vscode`, so it can be tested in plain Node.
import { execFile } from 'node:child_process';
import { existsSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';

/** The directory of the nearest `trion.toml` above a file. */
export function packageRoot(file: string): string | undefined {
  let directory = dirname(file);
  for (;;) {
    if (existsSync(join(directory, 'trion.toml'))) {
      return directory;
    }
    const parent = dirname(directory);
    if (parent === directory) {
      return undefined;
    }
    directory = parent;
  }
}

/** The arguments of `trion render` for one file of a package. */
export function renderArguments(root: string, file: string): string[] {
  return ['render', root, '--file', relative(root, file)];
}

function escape(text: string): string {
  return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

/** A page that says why there is no document to show. */
export function messagePage(message: string): string {
  return `<!doctype html><html><body><p>${escape(message)}</p></body></html>`;
}

/** The rendered document of a file, or a page that explains what is missing. */
export function renderDocument(binary: string | undefined, file: string): Promise<string> {
  if (binary === undefined) {
    return Promise.resolve(messagePage('The trion command was not found. Set "trion.server.path" to the trion binary.'));
  }
  const root = packageRoot(file);
  if (root === undefined) {
    return Promise.resolve(messagePage('This file belongs to no package: no trion.toml was found above it.'));
  }
  return new Promise((resolve) => {
    execFile(binary, renderArguments(root, file), { maxBuffer: 64 * 1024 * 1024 }, (error, stdout, stderr) => {
      // The command exits with 1 when the package has errors, and still prints the document.
      if (stdout.trim().startsWith('<')) {
        resolve(stdout);
      } else {
        resolve(messagePage(`trion render failed: ${stderr.trim() || (error?.message ?? 'no output')}`));
      }
    });
  });
}
