// Copies the shared TextMate grammar into the extension. editors/grammar/ is the only source.
import { copyFileSync, mkdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const source = join(root, '..', 'grammar', 'trion.tmLanguage.json');
const target = join(root, 'syntaxes', 'trion.tmLanguage.json');

mkdirSync(dirname(target), { recursive: true });
copyFileSync(source, target);
console.log(`copied ${source} -> ${target}`);
