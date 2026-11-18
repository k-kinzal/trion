// Tokenizes a fixture and the real trion specifications with the same engine VS Code uses.
import assert from 'node:assert/strict';
import { readFileSync, globSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import oniguruma from 'vscode-oniguruma';
import textmate from 'vscode-textmate';

const here = dirname(fileURLToPath(import.meta.url));
const editors = join(here, '..', '..');
const repoRoot = join(editors, '..');
const grammarPath = join(here, '..', 'trion.tmLanguage.json');
const rawGrammar = readFileSync(grammarPath, 'utf8');

const wasm = readFileSync(createRequire(import.meta.url).resolve('vscode-oniguruma/release/onig.wasm'));
await oniguruma.loadWASM(wasm.buffer.slice(wasm.byteOffset, wasm.byteOffset + wasm.byteLength));
const registry = new textmate.Registry({
  onigLib: Promise.resolve({
    createOnigScanner: (patterns) => new oniguruma.OnigScanner(patterns),
    createOnigString: (text) => new oniguruma.OnigString(text),
  }),
  loadGrammar: async (scope) =>
    scope === 'source.trion' ? textmate.parseRawGrammar(rawGrammar, grammarPath) : null,
});
const grammar = await registry.loadGrammar('source.trion');

function tokenize(source) {
  let state = textmate.INITIAL;
  return source.split('\n').map((line) => {
    const result = grammar.tokenizeLine(line, state);
    state = result.ruleStack;
    return {
      line,
      tokens: result.tokens.map((t) => ({
        start: t.startIndex,
        text: line.slice(t.startIndex, t.endIndex),
        scopes: t.scopes,
      })),
    };
  });
}

const hasScope = (token, scope) => token.scopes.some((s) => s === scope || s.startsWith(`${scope}.`));
const significant = (tokens) => tokens.filter((t) => t.text.trim() !== '');

const fixture = tokenize(readFileSync(join(here, 'fixtures', 'sample.trion'), 'utf8'));

/** The tokens of the first fixture line that starts with `prefix`, searching from the line that starts with `after`. */
function tokensOf(prefix, after) {
  let from = 0;
  if (after !== undefined) {
    from = fixture.findIndex((l) => l.line.trimStart().startsWith(after));
    assert.ok(from >= 0, `the fixture has no line starting with ${after}`);
  }
  const found = fixture.slice(from).find((l) => l.line.trimStart().startsWith(prefix));
  assert.ok(found, `the fixture has no line starting with ${prefix}`);
  return found.tokens;
}

/** Asserts that `text` is exactly one token on the line and carries `scope`. */
function expectToken([prefix, text, scope, after]) {
  const tokens = tokensOf(prefix, after);
  const token = tokens.find((t) => t.text === text);
  assert.ok(token, `no token ${JSON.stringify(text)} on line ${prefix}: ${JSON.stringify(tokens.map((t) => t.text))}`);
  assert.ok(hasScope(token, scope), `${JSON.stringify(text)} on line ${prefix} has ${token.scopes.join(' ')}, expected ${scope}`);
}

const expectAll = (cases) => cases.forEach(expectToken);

function expectNoScope(tokens, text, prefix) {
  for (const t of tokens.filter((t) => t.text.includes(text))) {
    assert.ok(!t.scopes.some((s) => s.startsWith(prefix)), `${JSON.stringify(t.text)} has ${t.scopes.join(' ')}`);
  }
}

// trion: verifies trion#EDITOR-GRAMMAR
test('every grammar pattern compiles in Oniguruma', () => {
  const patterns = [];
  (function walk(node) {
    if (Array.isArray(node)) node.forEach(walk);
    else if (node && typeof node === 'object') {
      for (const key of ['match', 'begin', 'end', 'while']) {
        // An end pattern refers to the indentation that its begin pattern captured.
        if (typeof node[key] === 'string') patterns.push(key === 'end' ? node[key].replace('\\1', '(?:  )') : node[key]);
      }
      Object.values(node).forEach(walk);
    }
  })(JSON.parse(rawGrammar));
  assert.ok(patterns.length > 60);
  for (const pattern of patterns) {
    assert.doesNotThrow(() => new oniguruma.OnigScanner([pattern]), pattern);
  }
  assert.throws(() => new oniguruma.OnigScanner(['(unclosed']), 'the compile check can fail');
});

// trion: verifies trion#EDITOR-GRAMMAR
test('the VS Code extension ships this grammar file unchanged', () => {
  const { scopeName } = JSON.parse(rawGrammar);
  assert.equal(scopeName, 'source.trion');

  const copy = readFileSync(join(editors, 'vscode', 'scripts', 'copy-grammar.mjs'), 'utf8');
  assert.match(copy, /join\(root, '\.\.', 'grammar', 'trion\.tmLanguage\.json'\)/);
  assert.match(copy, /join\(root, 'syntaxes', 'trion\.tmLanguage\.json'\)/);
  const [entry] = JSON.parse(readFileSync(join(editors, 'vscode', 'package.json'), 'utf8')).contributes.grammars;
  assert.deepEqual(entry, { language: 'trion', scopeName, path: './syntaxes/trion.tmLanguage.json' });
  // The copy in the extension is the file that these tests read.
  assert.equal(readFileSync(join(editors, 'vscode', 'syntaxes', 'trion.tmLanguage.json'), 'utf8'), rawGrammar);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('line comments start with two slashes outside a string', () => {
  expectAll([
    ['// A fixture', '//', 'punctuation.definition.comment'],
    ['// A fixture', ' A fixture that exercises every construct of the grammar.', 'comment.line.double-slash'],
    ['[EARS-3]', '//', 'punctuation.definition.comment'],
    ['[EARS-3]', ' a trailing comment', 'comment.line.double-slash'],
    ['[EARS-3]', '.', 'punctuation.terminator'],
  ]);
  const [hash] = tokenize('# not a comment any more.');
  assert.ok(!hash.tokens.some((t) => hasScope(t, 'comment')));
  const [url] = tokenize('note "https://example.com/a"');
  assert.ok(!url.tokens.some((t) => hasScope(t, 'comment')), 'a // inside a string');
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a quoted string keeps its escapes and ends at the line break', () => {
  expectAll([
    ['title', '"', 'punctuation.definition.string.begin'],
    ['title', 'The first ', 'string.quoted.double'],
    ['title', '\\"', 'constant.character.escape'],
  ]);
  const lines = tokenize('note "unterminated\n[NEXT-1] The API shall stop.');
  assert.ok(lines[1].tokens.some((t) => t.text === 'NEXT-1' && hasScope(t, 'entity.name.function.spec-id')));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a raw string spans lines verbatim until three quotes', () => {
  expectAll([
    ['quote OLD-FORM', '"""', 'punctuation.definition.string.begin'],
    ['# not a comment', '# not a comment, "quoted" and // not a comment either', 'string.quoted.triple'],
    ['end', 'end', 'string.quoted.triple', 'quote OLD-FORM'],
    ['title "After the quote"', 'title', 'meta.block.source'],
    ['[NOT-AN-ID]', '    [NOT-AN-ID] When this ends, it is data.', 'string.quoted.triple'],
    ['expect rejected', 'expect', 'keyword.other.field.expect'],
  ]);
  for (const t of tokensOf('# not a comment')) {
    assert.ok(!t.scopes.some((s) => s.startsWith('comment') || s.startsWith('keyword')), t.scopes.join(' '));
  }
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('file directives scope the package, its edition and includes', () => {
  expectAll([
    ['package', 'package', 'keyword.other.directive.package'],
    ['package', 'chat', 'entity.name.namespace.package'],
    ['package', 'edition', 'keyword.other.directive.edition'],
    ['package', '2026-11-09', 'string.quoted.double'],
    ['include', 'include', 'keyword.other.directive.include'],
    ['include', 'parts/more.trion', 'string.quoted.double'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER, trion#EDITOR-GRAMMAR-INDENTATION
test('block headers are scoped and a block closes where its indentation ends', () => {
  expectAll([
    ['namespace', 'namespace', 'storage.type.namespace'],
    ['namespace', 'chat.api', 'entity.name.namespace'],
    ['namespace', ':', 'punctuation.section.block.begin'],
    ['section', 'section', 'storage.type.section'],
    ['section', 'Requests and responses', 'entity.name.section'],
    ['section', ':', 'punctuation.section.block.begin'],
    ['source R:', 'source', 'storage.type.source'],
    ['source R:', 'R', 'entity.name.source'],
    ['role', 'role', 'storage.type.role'],
    ['role', 'service', 'entity.name.type.role'],
    ['check', 'check', 'storage.type.check'],
    ['check', 'PIPELINE-EQUIVALENCE', 'entity.name.check'],
    ['example SYNTAX-CASE', 'example', 'storage.type.example'],
    ['example SYNTAX-CASE', 'SYNTAX-CASE', 'entity.name.example'],
    ['trace', 'trace', 'storage.type.trace'],
    ['trace', 'EARS-TEST', 'entity.name.trace'],
    ['[MODEL] concept', 'concept', 'storage.type.concept'],
    ['namespace chat.room', 'namespace', 'storage.type.namespace'],
    ['namespace chat.room', 'chat.room', 'entity.name.namespace'],
    ['section "Room types"', 'section', 'storage.type.section'],
    ['section "Room types"', 'Room types', 'entity.name.section'],
  ]);
  // The flat forms carry no colon.
  for (const header of ['namespace chat.room', 'section "Room types"']) {
    assert.ok(!tokensOf(header).some((t) => hasScope(t, 'punctuation.section.block.begin')), header);
  }
  // The line after a block is outside it, and blank lines do not close it.
  const blocks = [
    ['source R:', 'meta.block.source', 'kind requirement', 'role service'],
    ['role service', 'meta.block.role', 'required HEALTH', 'section "Requests'],
    ['check PIPELINE', 'meta.block.check', 'using definitions', 'example SYNTAX-CASE'],
    ['example COMPARISON-CASE', 'meta.block.example', 'expect trace-to', 'note "Statements'],
    ['trace EARS-TEST', 'meta.block.trace', 'verifies chat#EARS-1', 'namespace chat.room'],
  ];
  for (const [header, scope, inside, after] of blocks) {
    assert.ok(tokensOf(inside, header).every((t) => hasScope(t, scope)), `${inside} is inside ${header}`);
    assert.ok(tokensOf(after, header).every((t) => !hasScope(t, scope)), `${after} is outside ${header}`);
  }
  // `end` is an ordinary word.
  const [end] = tokenize('end');
  assert.ok(!end.tokens.some((t) => t.scopes.some((s) => s.startsWith('keyword.'))));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('namespace directives scope use, term, alias, bind, extend and classify', () => {
  expectAll([
    ['use', 'use', 'keyword.other.directive.use'],
    ['use', 'grpc', 'entity.name.namespace'],
    ['term', 'term', 'keyword.other.directive.term'],
    ['term', 'API', 'entity.name.type.term'],
    ['term', 'entity', 'storage.type.kind'],
    ['alias', 'alias', 'keyword.other.directive.alias'],
    ['alias', 'endpoint', 'entity.name.type.term'],
    ['alias', '=', 'keyword.operator.assignment'],
    ['bind', 'bind', 'keyword.other.directive.bind'],
    ['bind', 'as', 'keyword.other.directive.as'],
    ['bind', 'grpc.service', 'entity.name.namespace.role'],
    ['bind', '.', 'punctuation.terminator'],
    ['extend', 'extend', 'keyword.other.directive.extend'],
    ['extend', 'with', 'keyword.other.directive.with'],
    ['extend', 'Auditable', 'entity.other.inherited-class'],
    ['extend', 'Pageable', 'entity.other.inherited-class'],
    ['predicate', 'predicate', 'keyword.other.directive.predicate'],
    ['predicate', 'reachable', 'entity.name.function.predicate'],
    ['predicate', 'node, node', 'variable.parameter'],
    ['classify', 'classify', 'keyword.other.directive.classify'],
    ['classify', 'Security', 'entity.name.type.classification'],
    ['note', 'note', 'keyword.other.directive.note'],
    ['note', 'Statements read as one specification.', 'string.quoted.double'],
    ['ref', 'ref', 'keyword.other.directive.ref'],
    ['ref', 'EARS-1', 'variable.other.spec-id'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-DECLARATIONS
test('a primitive, a diagram kind, a compatibility claim and a refinement line are scoped', () => {
  expectAll([
    ['primitive', 'primitive', 'keyword.other.directive.primitive'],
    ['primitive', 'message', 'entity.name.type.term'],
    ['diagram kind', 'diagram', 'storage.type.diagram'],
    ['diagram kind', 'kind', 'storage.type.diagram.kind'],
    ['diagram kind', 'transition', 'entity.name.type.diagram'],
    ['element', 'element', 'keyword.other.field.element', 'diagram kind'],
    ['element', '$from -> $event -> $to;', 'string.quoted.double', 'diagram kind'],
    ['types', 'types', 'keyword.other.field.types', 'diagram kind'],
    ['expansion', 'expansion', 'keyword.other.field.expansion', 'diagram kind'],
    ['preserves', 'preserves', 'keyword.other.field.preserves', 'diagram kind'],
    ['compatibility', 'compatibility', 'storage.type.compatibility'],
    ['compatibility', 'BASE-SENTENCES', 'entity.name.compatibility'],
    ['source R', 'source', 'keyword.other.field.source', 'compatibility'],
    ['source R', 'R', 'variable.other.source', 'compatibility'],
    ['revision', 'revision', 'keyword.other.field.revision', 'compatibility'],
    ['form Event-driven', 'form', 'keyword.other.field.form', 'compatibility'],
    ['form Event-driven', 'Event-driven', 'constant.language.form', 'compatibility'],
    ['detailed by', 'detailed', 'storage.type.annotation.detailed'],
    ['detailed by', 'by', 'keyword.other.annotation.by'],
    ['detailed by', 'EARS-2', 'variable.other.spec-id'],
    ['detailed by', 'EARS-3', 'variable.other.spec-id'],
  ]);
  // The blocks end where their indentation ends.
  assert.ok(tokensOf('source R:').every((t) => !hasScope(t, 'meta.block.compatibility')));
});

// trion: verifies trion#EDITOR-GRAMMAR-MEASURE
test('a measure declaration and a reading example are scoped', () => {
  expectAll([
    ['measure', 'measure', 'keyword.other.directive.measure'],
    ['measure', 'requests', 'entity.name.type.measure'],
    ['kind reading', 'reading', 'constant.language.kind', 'example READING-CASE'],
    ['expect "assume', 'expect', 'keyword.other.field.expect', 'example READING-CASE'],
    ['expect "assume', 'assume: ⊤', 'string.quoted.double', 'example READING-CASE'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PRIORITY
test('priority lines and control declarations are scoped', () => {
  expectAll([
    ['overrides', 'overrides', 'storage.type.annotation.overrides'],
    ['overrides', 'EARS-4', 'variable.other.spec-id'],
    ['overrides', 'EARS-5', 'variable.other.spec-id'],
    ['default', 'default', 'storage.type.annotation.default'],
    ['weight', 'weight', 'storage.type.annotation.weight'],
    ['weight', '3', 'constant.numeric.weight'],
    ['environment', 'environment', 'keyword.other.directive.control'],
    ['environment', 'user', 'entity.name.type.actor'],
    ['system', 'system', 'keyword.other.directive.control'],
    ['system', 'API', 'entity.name.type.actor'],
  ]);
  // A sentence that begins with one of these words is still a sentence.
  const sentence = tokenize('    The system shall stop.\n    The default route shall stay.\n');
  assert.ok(sentence.flatMap((l) => l.tokens).every((t) => !t.scopes.some((s) => s.includes('directive.control') || s.includes('annotation.default'))));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('citations, unsourced reasons and ratifications are annotations', () => {
  expectAll([
    ['cite R#INTENT', 'cite', 'storage.type.annotation.cite'],
    ['cite R#INTENT', 'R', 'variable.other.source'],
    ['cite R#INTENT', '#', 'punctuation.separator.quote'],
    ['cite R#INTENT', 'INTENT', 'variable.other.quote'],
    ['cite LANGUAGE-DRAFT', 'LANGUAGE-DRAFT', 'variable.other.source'],
    ['cite R#INTENT', 'cite', 'meta.annotation.citation', '[EARS-1]'],
    ['unsourced', 'unsourced', 'storage.type.annotation.unsourced'],
    ['unsourced', 'The session leaves the API unspecified.', 'string.quoted.double'],
    ['ratified', 'ratified', 'storage.type.annotation.ratified'],
    ['ratified', 'by', 'keyword.other.annotation.by'],
    ['ratified', 'alice', 'variable.other.ratifier'],
    ['ratified', 'on', 'keyword.other.annotation.on'],
    ['ratified', '2026-11-09', 'constant.numeric.date'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('source fields and quotes are scoped inside a source block', () => {
  expectAll([
    ['title', 'title', 'keyword.other.field.title'],
    ['kind requirement', 'kind', 'keyword.other.field.kind'],
    ['kind requirement', 'requirement', 'constant.language.kind'],
    ['transcript', 'transcript', 'keyword.other.field.transcript'],
    ['transcript', 'first', 'constant.language.transcript'],
    ['minimum', 'minimum', 'keyword.other.field.minimum'],
    ['minimum', '80%', 'constant.numeric'],
    ['quote INTENT', 'quote', 'keyword.other.field.quote'],
    ['quote INTENT', 'INTENT', 'entity.name.quote'],
    ['quote INTENT', '仕様記述言語を作成します。', 'string.quoted.double'],
    ['quote OLD-FORM', 'OLD-FORM', 'entity.name.quote'],
    ['title', 'title', 'meta.block.source'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('role members scope placeholders and regular expressions', () => {
  expectAll([
    ['activate', 'activate', 'keyword.other.directive.activate'],
    ['activate', '$', 'punctuation.definition.variable'],
    ['activate', 'subject', 'variable.other.placeholder'],
    ['activate', 'shall', 'keyword.other.modal'],
    ['form METHOD-NAME', 'form', 'keyword.other.directive.form'],
    ['form METHOD-NAME', 'METHOD-NAME', 'entity.name.function.form'],
    ['form METHOD-NAME', 'where', 'keyword.control.constraint'],
    ['form METHOD-NAME', 'matches', 'keyword.operator.match'],
    ['form METHOD-NAME', 'when', 'keyword.control.constraint'],
    ['form METHOD-NAME', 'does not match', 'keyword.operator.match'],
    ['form METHOD-NAME', '[A-Z]', 'constant.other.character-class.regexp'],
    ['form METHOD-NAME', '\\/', 'constant.character.escape.regexp'],
    ['form METHOD-NAME', '^', 'keyword.control.anchor.regexp'],
    ['required', 'required', 'keyword.other.directive.required'],
    ['required', 'HEALTH', 'entity.name.function.form'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('stable identifiers are declared at the start of a line and referenced elsewhere', () => {
  expectAll([
    ['[EARS-1]', '[', 'punctuation.definition.spec-id.begin'],
    ['[EARS-1]', 'EARS-1', 'entity.name.function.spec-id'],
    ['[EARS-1]', ']', 'punctuation.definition.spec-id.end'],
    ['[DELIVERY/identity]', 'DELIVERY/identity', 'entity.name.function.spec-id'],
    ['left', 'DELIVERY', 'variable.other.spec-id'],
    ['candidate', 'PIPELINE/model', 'variable.other.spec-id'],
    ['verifies', 'chat', 'entity.name.namespace'],
    ['verifies', '#', 'punctuation.separator.reference'],
    ['verifies', 'EARS-1', 'variable.other.spec-id'],
    ['[bad id!]', 'bad id!', 'invalid.illegal.spec-id'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('EARS keywords, modal words and definitions are keywords', () => {
  expectAll([
    ['Where tracing', 'Where', 'keyword.control.conditional'],
    ['Where tracing', 'while', 'keyword.control.conditional'],
    ['Where tracing', 'when', 'keyword.control.conditional'],
    ['the API shall respond', 'shall', 'keyword.other.modal'],
    ['the API shall respond', 'unless', 'keyword.control.exception'],
    ['the API shall respond', '500', 'constant.numeric'],
    ['the API shall respond', 'ms', 'keyword.other.unit'],
    ['the API shall respond', '.', 'punctuation.terminator'],
    ['[EARS-2]', 'If', 'keyword.control.conditional'],
    ['[EARS-2]', 'then', 'keyword.control.conditional'],
    ['[EARS-2]', 'must', 'keyword.other.modal'],
    ['[EARS-2]', 'not', 'keyword.other.modal.negation'],
    ['[EARS-2]', 'GET /foo', 'string.quoted.other.backtick'],
    ['[EARS-2]', 'unless', 'string.quoted.other.backtick'],
    ['[EARS-2]', 'or', 'keyword.operator.logical'],
    ['[EARS-3]', 'should', 'keyword.other.modal'],
    ['[EARS-3]', 'never', 'keyword.other.modal.negation'],
    ['[EARS-4]', 'may', 'keyword.other.modal'],
    ['[TERM-1]', 'means', 'keyword.operator.definition'],
    ['Before the', 'Before', 'keyword.control.temporal'],
    ['Before the', 'After', 'keyword.control.temporal'],
    ['Before the', 'Once', 'keyword.control.temporal'],
    ['Before the', 'Upon', 'keyword.control.temporal'],
    ['Before the', 'Until', 'keyword.control.temporal'],
    ['Before the', 'During', 'keyword.control.temporal'],
    ['For each', 'For each', 'keyword.control.loop'],
    ['For each', ':', 'punctuation.section.block.begin'],
    ['When the formalizer', 'When', 'keyword.control.conditional'],
    ['When the formalizer', ':', 'punctuation.section.block.begin'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('quantities, comparisons and logical words are scoped', () => {
  expectAll([
    ['[CMP-1]', 'is', 'keyword.operator.copula'],
    ['[CMP-1]', 'at most', 'keyword.other.quantifier'],
    ['[CMP-1]', '30', 'constant.numeric'],
    ['[CMP-1]', 'seconds', 'keyword.other.unit'],
    ['[CMP-1]', 'at least', 'keyword.other.quantifier'],
    ['[CMP-1]', 'one', 'constant.numeric.word'],
    ['[CMP-1]', 'exactly', 'keyword.other.quantifier'],
    ['[CMP-1]', '1,000', 'constant.numeric'],
    ['[CMP-2]', 'Each', 'keyword.other.quantifier'],
    ['[CMP-2]', 'every', 'keyword.other.quantifier'],
    ['[CMP-2]', 'no', 'keyword.other.quantifier'],
    ['[CMP-3]', 'greater than', 'keyword.operator.comparison'],
    ['[CMP-3]', '1.5', 'constant.numeric'],
    ['[CMP-3]', 'GB', 'keyword.other.unit'],
    ['[CMP-3]', 'less than', 'keyword.operator.comparison'],
    ['[CMP-3]', '%', 'keyword.other.unit'],
    ['[CMP-3]', 'equal to', 'keyword.operator.comparison'],
    ['[CMP-3]', 'between', 'keyword.operator.comparison'],
    ['[CMP-3]', 'up to', 'keyword.operator.comparison'],
    ['[ENUM]', 'one of', 'keyword.other.enumeration'],
    ['[ENUM]', ',', 'punctuation.separator.comma'],
    ['[QUAL]', 'trion.vocabulary', 'entity.name.namespace'],
    ['[QUAL]', 'either', 'keyword.operator.logical'],
    ['[QUAL]', 'both', 'keyword.operator.logical'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('action lists scope their phrase and item terminators', () => {
  expectAll([
    ['the checker shall perform', 'perform all of the following actions', 'keyword.other.composition'],
    ['the checker shall perform', ':', 'punctuation.section.block.begin'],
    ['[DELIVERY/identity]', ';', 'punctuation.terminator.item'],
    ['[DELIVERY/channels]', 'perform one or more of the following actions', 'keyword.other.composition'],
    ['emit D', ';', 'punctuation.terminator.item'],
  ]);
  const [ordered] = tokenize('the compiler shall perform the following actions in order:');
  assert.ok(ordered.tokens.some((t) => t.text === 'perform the following actions in order' && hasScope(t, 'keyword.other.composition')));
  const [one] = tokenize('the parser shall perform exactly one of the following actions:');
  assert.ok(one.tokens.some((t) => t.text === 'perform exactly one of the following actions' && hasScope(t, 'keyword.other.composition')));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a flow scopes steps, edges and choices up to its last indented line', () => {
  expectAll([
    ['the compiler shall follow', 'follow this flow', 'keyword.other.flow'],
    ['[PIPELINE/model] step', 'PIPELINE/model', 'entity.name.function.spec-id'],
    ['[PIPELINE/model] step', 'step', 'keyword.control.flow.step'],
    ['[PIPELINE/model] step', 'model', 'entity.name.function.step'],
    ['[PIPELINE/model] step', 'S', 'variable.other'],
    ['[PIPELINE/model] step', ';', 'punctuation.terminator.item'],
    ['step verify', 'verify', 'entity.name.function.step'],
    ['start', 'start', 'keyword.control.flow.start'],
    ['start', 'model', 'variable.other.step'],
    ['model -> verify', 'model', 'variable.other.step'],
    ['model -> verify', '->', 'keyword.operator.arrow'],
    ['choose after', 'choose after', 'keyword.control.flow.choose'],
    ['choose after', 'verify', 'variable.other.step'],
    ['when S is consistent', 'when', 'keyword.control.conditional'],
    ['when S is consistent', '->', 'keyword.operator.arrow'],
    ['when S is consistent', 'report', 'variable.other.step'],
    ['otherwise', 'otherwise', 'keyword.control.conditional.otherwise'],
    ['otherwise', 'model', 'variable.other.step'],
    ['otherwise', 'otherwise', 'meta.block.choice'],
    ['finish', 'finish', 'keyword.control.flow.finish'],
    ['finish', 'report', 'variable.other.step'],
    ['finish', 'finish', 'meta.block.flow'],
  ]);
  const after = tokensOf('[MODEL] concept');
  assert.ok(after.every((t) => !hasScope(t, 'meta.block.flow')), 'the flow ends where its indentation ends');
  assert.ok(tokensOf('finish').every((t) => !hasScope(t, 'meta.block.choice')), 'the choice ends where its indentation ends');
  // A header on one line opens the flow as well.
  const oneLine = tokenize('[F] When a call arrives, the API shall follow this flow:\n    step a: stop;\n    start a\n[G] The API shall stop.');
  assert.ok(oneLine[0].tokens.some((t) => t.text === 'F' && hasScope(t, 'entity.name.function.spec-id')));
  assert.ok(oneLine[1].tokens.some((t) => t.text === 'step' && hasScope(t, 'keyword.control.flow.step')));
  assert.ok(oneLine[3].tokens.every((t) => !hasScope(t, 'meta.block.flow')));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a concept edge scopes its arrows', () => {
  expectAll([
    ['[MODEL] concept', 'MODEL', 'entity.name.function.spec-id'],
    ['[MODEL/statements]', 'MODEL/statements', 'entity.name.function.spec-id'],
    ['[MODEL/statements]', 'each', 'keyword.other.quantifier'],
    ['[MODEL/statements]', '->', 'keyword.operator.arrow'],
    ['[MODEL/statements]', 'zero or more', 'keyword.other.quantifier'],
    ['[MODEL/statements]', ';', 'punctuation.terminator.item'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('check, example and trace fields are scoped inside their blocks', () => {
  expectAll([
    ['relation', 'relation', 'keyword.other.field.relation'],
    ['relation', 'equivalent', 'constant.language.relation'],
    ['left', 'left', 'keyword.other.field.left'],
    ['right', 'right', 'keyword.other.field.right'],
    ['right', 'MODEL', 'variable.other.spec-id'],
    ['using', 'using', 'keyword.other.field.using'],
    ['using', 'definitions', 'constant.language.using'],
    ['kind syntax', 'kind', 'keyword.other.field.kind'],
    ['kind syntax', 'syntax', 'constant.language.kind'],
    ['form statement', 'form', 'keyword.other.field.form'],
    ['form statement', 'statement', 'constant.language.form'],
    ['input', 'input', 'keyword.other.field.input'],
    ['input', '"""', 'string.quoted.triple'],
    ['expect rejected', 'rejected', 'constant.language.expectation'],
    ['expect rejected', 'MISSING_PREDICATE', 'string.quoted.double'],
    ['base', 'base', 'keyword.other.field.base'],
    ['base', 'DELIVERY', 'variable.other.spec-id'],
    ['candidate', 'candidate', 'keyword.other.field.candidate'],
    ['expect trace-to', 'trace-to', 'constant.language.expectation'],
    ['expect trace-to', 'EARS-1', 'variable.other.spec-id'],
    ['artifact', 'artifact', 'keyword.other.field.artifact'],
    ['artifact', 'cargo:syntax::accepts_every_ears_pattern', 'string.quoted.double'],
    ['verifies', 'verifies', 'keyword.other.field.verifies'],
  ]);
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('variables are capital letters with digits, not the article A', () => {
  expectAll([
    ['When the checker produces', 'D', 'variable.other'],
    ['[QUAL]', 'A', 'variable.other'],
    ['[QUAL]', 'B', 'variable.other'],
  ]);
  expectNoScope(tokensOf('[EARS-4]'), 'A', 'variable');
  expectNoScope(tokensOf('[TERM-1]'), 'A', 'variable');
  const [line] = tokenize('A report R1 for D is ready.');
  assert.ok(line.tokens.some((t) => t.text === 'R1' && hasScope(t, 'variable.other')));
  expectNoScope(line.tokens, 'A', 'variable');
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('hyphenated words do not contain keywords', () => {
  const tokens = tokensOf('The is-active');
  for (const word of ['is-active', 'may-fail', 'no-op']) {
    expectNoScope(tokens, word, 'keyword.');
  }
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a field keyword outside its block is an ordinary word', () => {
  const lines = tokenize('kind requirement\nstep model: do it;\nstart and completion events.\nrelation equivalent');
  for (const { line, tokens } of lines) {
    assert.ok(!tokens.some((t) => t.scopes.some((s) => s.startsWith('keyword.other.field') || s.startsWith('keyword.control.flow'))), line);
  }
  const [form] = tokenize('form statement');
  assert.ok(!form.tokens.some((t) => hasScope(t, 'keyword.other.directive.form')));
});

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('a sentence that begins with a directive word is not a directive', () => {
  for (const sentence of ['package delivery shall be fast.', 'use of the API shall be logged.', 'cite the source.']) {
    const [line] = tokenize(sentence);
    assert.ok(!line.tokens.some((t) => t.scopes.some((s) => s.startsWith('keyword.other.directive') || s.startsWith('storage.type'))), sentence);
    assert.ok(line.tokens.some((t) => t.text === 'shall' && hasScope(t, 'keyword.other.modal')) || !sentence.includes('shall'), sentence);
  }
});

const samples = [
  ...globSync('spec/**/*.trion', { cwd: repoRoot }),
  ...globSync('stdlib/**/*.trion', { cwd: repoRoot }),
];

// trion: verifies trion#EDITOR-GRAMMAR-PARSER
test('every spec and stdlib file tokenizes the way the parser reads it', () => {
  assert.ok(samples.length >= 5, samples.join());
  for (const sample of samples) {
    const lines = tokenize(readFileSync(join(repoRoot, sample), 'utf8'));
    for (const { line, tokens } of lines) {
      const context = `${sample}: ${line}`;
      for (const t of tokens) {
        assert.ok(!t.scopes.some((s) => s.startsWith('invalid.')), `unexpected invalid scope on ${JSON.stringify(t.text)} in ${context}`);
      }
      const words = significant(tokens);
      // Raw string contents are data, not syntax.
      if (words.length > 0 && words.every((t) => hasScope(t, 'string.quoted.triple') && !hasScope(t, 'punctuation.definition.string'))) continue;
      const first = words[0];
      if (/^\s*\/\//.test(line)) {
        assert.ok(words.every((t) => hasScope(t, 'comment')), context);
      } else if (/^\s*(cite|unsourced|ratified)\s/.test(line)) {
        assert.ok(hasScope(first, 'storage.type.annotation'), context);
      } else if (/^\s*\[[A-Z][A-Z0-9-]*(\/[a-z][a-z0-9-]*)?\]/.test(line)) {
        assert.ok(words.some((t) => hasScope(t, 'entity.name.function.spec-id')), context);
      } else if (/^\s*(namespace|section|source|role|check|example|trace)\s.*:\s*$/.test(line)) {
        assert.ok(hasScope(first, `storage.type.${line.trim().split(/\s/)[0]}`), context);
      } else if (/^\s*(package|include|use|note|ref)\s/.test(line)) {
        assert.ok(hasScope(first, 'keyword.other.directive'), context);
      }
      if (/:\s*$/.test(line) && !/^\s*\/\//.test(line)) {
        assert.ok(hasScope(words.at(-1), 'punctuation.section.block.begin'), `a block header ends with a colon: ${context}`);
      }
      // No block reaches a line that is not indented.
      if (/^\S/.test(line) && !/^\/\//.test(line) && !tokens.some((t) => hasScope(t, 'string.quoted.triple'))) {
        assert.ok(tokens.every((t) => !t.scopes.some((s) => s.startsWith('meta.block.') && !/meta\.block\.(namespace|section)/.test(s))), `a block closes where its indentation ends: ${context}`);
      }
      for (const match of line.matchAll(/(?<!\S)`([^`]+)`(?=[\s,.;:]|$)/g)) {
        const opening = tokens.findLast((t) => t.start <= match.index);
        // A backtick inside a comment or a string is not a literal.
        if (hasScope(opening, 'comment') || hasScope(opening, 'string.quoted')) continue;
        const body = match.index + 1;
        const inside = tokens.filter((t) => t.start >= body && t.start < body + match[1].length);
        assert.ok(inside.length > 0, context);
        for (const t of inside) {
          assert.ok(hasScope(t, 'string.quoted.other.backtick'), `literal ${match[1]} in ${context}`);
          assert.ok(!t.scopes.some((s) => s.startsWith('keyword.')), `literal ${match[1]} in ${context}`);
        }
      }
    }
  }
});
