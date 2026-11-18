// Finds the server binary. This module does not import `vscode`, so it can be tested in plain Node.
import { accessSync, constants, statSync } from 'node:fs';
import { homedir } from 'node:os';
import { delimiter, isAbsolute, join } from 'node:path';

export interface ResolveEnvironment {
  readonly path: string | undefined;
  readonly pathExt: string | undefined;
  readonly home: string;
  readonly platform: NodeJS.Platform;
}

export function currentEnvironment(): ResolveEnvironment {
  return {
    path: process.env.PATH,
    pathExt: process.env.PATHEXT,
    home: homedir(),
    platform: process.platform,
  };
}

function isExecutable(file: string, platform: NodeJS.Platform): boolean {
  try {
    if (!statSync(file).isFile()) {
      return false;
    }
    accessSync(file, platform === 'win32' ? constants.F_OK : constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

function withExtensions(file: string, env: ResolveEnvironment): string[] {
  if (env.platform !== 'win32') {
    return [file];
  }
  const extensions = (env.pathExt ?? '.EXE;.CMD;.BAT').split(';').filter(Boolean);
  return [file, ...extensions.map((extension) => file + extension)];
}

/**
 * Returns the absolute path of the binary, or undefined when it does not exist.
 *
 * A bare command name is searched on PATH and then in ~/.cargo/bin, because
 * `cargo install` puts it there and GUI-launched editors often lack that PATH entry.
 * Anything containing a path separator is taken as a path, with a leading `~` expanded.
 */
export function resolveServerPath(
  configured: string,
  env: ResolveEnvironment = currentEnvironment(),
): string | undefined {
  const trimmed = configured.trim();
  if (trimmed === '') {
    return undefined;
  }
  const expanded = /^~(?=[/\\]|$)/.test(trimmed) ? env.home + trimmed.slice(1) : trimmed;
  const isPath = expanded.includes('/') || (env.platform === 'win32' && expanded.includes('\\'));
  if (isPath) {
    if (!isAbsolute(expanded)) {
      return undefined;
    }
    return withExtensions(expanded, env).find((file) => isExecutable(file, env.platform));
  }
  const directories = [
    ...(env.path ?? '').split(delimiter).filter(Boolean),
    join(env.home, '.cargo', 'bin'),
  ];
  for (const directory of directories) {
    const match = withExtensions(join(directory, expanded), env).find((file) =>
      isExecutable(file, env.platform),
    );
    if (match !== undefined) {
      return match;
    }
  }
  return undefined;
}
