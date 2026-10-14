// SPDX-License-Identifier: MPL-2.0
// Documentation checks only: never evidence that K-CUT is proved.  The proof
// gate is scripts/check.sh under .github/workflows/proofs.yml.
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { basename, dirname, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const skipDirs = new Set(['.git', 'node_modules', '.cache', '_build']);

/**
 * Lists the files under `dir` whose names pass `keep`, recursively, skipping
 * dependency, cache and Git directories.  An absent `dir` yields nothing.
 * @param {string} dir - Directory to scan.
 * @param {(name: string) => boolean} keep - File-name filter.
 * @returns {string[]} Absolute paths.
 */
function filesUnder(dir, keep) {
  if (!existsSync(dir)) return [];
  const out = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (skipDirs.has(entry.name)) continue;
    const path = resolve(dir, entry.name);
    if (entry.isDirectory()) out.push(...filesUnder(path, keep));
    else if (entry.isFile() && keep(entry.name)) out.push(path);
  }
  return out;
}

const escape = text => text.replace(/[.*+?^${}()|[\]\\]/g, String.raw`\$&`);
const mentions = (text, id) => new RegExp(String.raw`\b${escape(id)}\b`).test(text);

/**
 * Index of the line that defines `name`: its type signature, its first
 * clause when it has no signature, or its record, data or module declaration.
 * @param {string[]} lines - Source lines.
 * @param {string} name - Agda identifier.
 * @returns {number} Line index, or -1.
 */
function definitionLine(lines, name) {
  const re = new RegExp(String.raw`^\s*(?:(?:record|data|module)\s+)?${escape(name)}(?:\s*[:=]|\s|$)`);
  return lines.findIndex(line => re.test(line));
}

/**
 * The comment block directly above line `i`: contiguous `--` lines, no blank
 * line between them and the definition.
 * @param {string[]} lines - Source lines.
 * @param {number} i - Index of the definition line.
 * @returns {string} The block's text.
 */
function commentAbove(lines, i) {
  const block = [];
  for (let j = i - 1; j >= 0 && /^\s*--/.test(lines[j]); j--) block.unshift(lines[j]);
  return block.join('\n');
}

/**
 * A file's header: everything before its first line of code, where an OPTIONS
 * pragma, a shebang, a blank line and a comment all still count as header.
 * @param {string[]} lines - Source lines.
 * @returns {string} The header's text.
 */
function header(lines) {
  const out = [];
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed !== '' && !trimmed.startsWith('#!') && !trimmed.startsWith('{-#') && !/^(--|#|\/\/)/.test(trimmed)) break;
    out.push(line);
  }
  return out.join('\n');
}

/**
 * Reads the source files the ledger may cite and indexes their modules.
 * @param {string} root - Repository root.
 * @returns {{ sources: Map<string, string[]>, agda: string[], modules: Map<string, string[]> }}
 * Lines per relative path; the Agda paths; module name -> files (each
 * file's basename, plus every named nested module).
 */
function sourceIndex(root) {
  const sources = new Map();
  for (const dir of ['src', 'tests', 'applications', 'scripts']) {
    for (const file of filesUnder(resolve(root, dir), name => /\.(agda|sh|mjs)$/.test(name))) {
      sources.set(relative(root, file), readFileSync(file, 'utf8').split('\n'));
    }
  }
  const agda = [...sources.keys()].filter(path => path.endsWith('.agda'));
  const modules = new Map();
  const addModule = (name, file) => modules.set(name, [...(modules.get(name) ?? []), file]);
  for (const file of agda) {
    addModule(basename(file, '.agda'), file);
    for (const line of sources.get(file)) {
      const nested = /^\s*module\s+([^\s_(][^\s(]*)/.exec(line);
      if (nested) addModule(nested[1].split('.').pop(), file);
    }
  }
  return { sources, agda, modules };
}

/**
 * The ledger's table rows: ID, status cell, and the files of the modules the
 * row's section header names (as `Module.agda`).  A duplicate ID is reported.
 * @param {string} ledger - PROOF-STATUS.adoc text.
 * @param {Map<string, string[]>} modules - Module name -> files.
 * @param {string[]} errors - Findings are appended here.
 * @returns {{ id: string, status: string, sectionModules: string[] }[]} Rows in order.
 */
function ledgerRows(ledger, modules, errors) {
  const rows = [];
  const seen = new Set();
  let sectionModules = [];
  for (const line of ledger.split('\n')) {
    if (line.startsWith('==')) {
      sectionModules = [...line.matchAll(/([\w/]+)\.agda/g)].flatMap(m => modules.get(basename(m[1])) ?? []);
      continue;
    }
    if (!line.startsWith('|')) continue;
    const cells = line.slice(1).trimEnd().replace(/\|$/, '').split(' | ').map(cell => cell.trim());
    const id = cells[0];
    if (!/^[A-Z]-\d+$/.test(id)) continue;
    if (seen.has(id)) errors.push(`Duplicate ledger ID ${id} in PROOF-STATUS.adoc`);
    seen.add(id);
    rows.push({ id, status: cells.at(-1), sectionModules });
  }
  return rows;
}

/**
 * Checks one file citation of a ledger row: the file must exist and its
 * header must name the row.
 * @param {string} root - Repository root.
 * @param {{ sources: Map<string, string[]>, agda: string[] }} index - From sourceIndex.
 * @param {string} id - Row ID.
 * @param {string} name - A path, with or without `.agda`, or a `Module.agda`.
 * @returns {string | null} A finding, or null when the citation is bound.
 */
function checkFileCitation(root, index, id, name) {
  const file = name.includes('/')
    ? [name, `${name}.agda`].find(candidate => existsSync(resolve(root, candidate)))
    : index.agda.find(path => basename(path) === name);
  if (!file) return `Ledger ${id} cites ${name}, which does not exist`;
  const lines = index.sources.get(file) ?? readFileSync(resolve(root, file), 'utf8').split('\n');
  return mentions(header(lines), id) ? null : `Ledger ${id}: the header of ${file} does not name the row`;
}

/**
 * Checks one definition citation of a ledger row: the name must be defined in
 * one of the candidate files, and the comment block directly above the
 * definition must name the row.
 * @param {Map<string, string[]>} sources - Lines per file.
 * @param {string} id - Row ID.
 * @param {string} name - The cited name as written.
 * @param {string} target - The identifier to find (the name without its module).
 * @param {string[]} candidates - Files to search, in order.
 * @returns {string | null} A finding, or null when the citation is bound.
 */
function checkDefinitionCitation(sources, id, name, target, candidates) {
  for (const file of candidates) {
    const lines = sources.get(file);
    const i = definitionLine(lines, target);
    if (i < 0) continue;
    return mentions(commentAbove(lines, i), id) ? null : `Ledger ${id}: the comment above ${target} in ${file} does not name the row`;
  }
  return `Ledger ${id} cites ${name}, which is not defined under src/, tests/ or applications/`;
}

/**
 * Reports every ledger reference, in Agda and shell comments and in every
 * document, to a row the ledger does not have.  JavaScript is tooling and may
 * quote IDs as test data, so it is not scanned.
 * @param {string} root - Repository root.
 * @param {Map<string, string[]>} sources - Lines per file.
 * @param {string} ledger - PROOF-STATUS.adoc text.
 * @param {Set<string>} ids - The ledger's row IDs.
 * @param {string[]} errors - Findings are appended here.
 * @returns {void}
 */
function checkStaleReferences(root, sources, ledger, ids, errors) {
  const letters = new Set([...ids].map(id => id[0]));
  const texts = [['PROOF-STATUS.adoc', ledger]];
  for (const [path, lines] of sources) if (!path.endsWith('.mjs')) texts.push([path, lines.join('\n')]);
  for (const file of filesUnder(root, name => name.endsWith('.adoc'))) {
    if (basename(file) !== 'PROOF-STATUS.adoc') texts.push([relative(root, file), readFileSync(file, 'utf8')]);
  }
  for (const [file, text] of texts) {
    for (const [id, letter] of text.matchAll(/\b([A-Z])-\d+\b/g)) {
      if (letters.has(letter) && !ids.has(id)) errors.push(`Stale ledger reference ${id} in ${file}: PROOF-STATUS.adoc has no such row`);
    }
  }
}

/**
 * The ledger binds every claim to the code.  For each PROVEN or TESTED row of
 * PROOF-STATUS.adoc, every backticked name in the status cell must resolve:
 * a bare name or `Module.name` to a definition under src/, tests/ or
 * applications/, a `Module.agda` or a path to an existing file.  The comment
 * block directly above a cited definition, or the header of a cited file,
 * must name the row, so a claim cannot outlive its proof or point at the
 * wrong one.  Row IDs are unique, and nothing in the repository names a row
 * that does not exist.  Bare names are looked up first in the modules the row
 * itself qualifies, then in the modules its section header names, then
 * anywhere.
 * @param {string} root - Repository root.
 * @param {string[]} errors - Findings are appended here.
 * @returns {void}
 */
function checkLedgerBinding(root, errors) {
  const ledgerPath = resolve(root, 'PROOF-STATUS.adoc');
  if (!existsSync(ledgerPath)) return;
  const ledger = readFileSync(ledgerPath, 'utf8');
  const index = sourceIndex(root);
  const rows = ledgerRows(ledger, index.modules, errors);
  for (const row of rows) {
    if (/^OPEN\b/.test(row.status) || !/\b(PROVEN|TESTED)\b/.test(row.status)) continue;
    const rowModules = [];
    for (const [, name] of row.status.matchAll(/`([^`\s]+)`/g)) {
      const finding = checkCitation(root, index, row, rowModules, name);
      if (finding) errors.push(finding);
    }
  }
  checkStaleReferences(root, index.sources, ledger, new Set(rows.map(row => row.id)), errors);
}

/**
 * Checks one citation of a ledger row, a file or a definition, and records
 * the files of a qualified module in `rowModules` so the row's later bare
 * names are looked up there first.
 * @param {string} root - Repository root.
 * @param {{ sources: Map<string, string[]>, agda: string[], modules: Map<string, string[]> }} index - From sourceIndex.
 * @param {{ id: string, sectionModules: string[] }} row - The citing row.
 * @param {string[]} rowModules - Files of the modules the row has qualified so far.
 * @param {string} name - The cited name as written.
 * @returns {string | null} A finding, or null when the citation is bound.
 */
function checkCitation(root, index, row, rowModules, name) {
  if (name.includes('/') || name.endsWith('.agda')) return checkFileCitation(root, index, row.id, name);
  const dot = name.lastIndexOf('.');
  const qualified = dot > 0 && index.modules.has(name.slice(0, dot));
  const candidates = qualified ? index.modules.get(name.slice(0, dot)) : [...rowModules, ...row.sectionModules, ...index.agda];
  if (qualified) rowModules.push(...candidates);
  return checkDefinitionCitation(index.sources, row.id, name, qualified ? name.slice(dot + 1) : name, candidates);
}

/**
 * Checks every AsciiDoc file under `root` for broken local links and retired
 * references, and flags retired state files, appending findings to `errors`.
 * @param {string} root - Repository root.
 * @param {string[]} errors - Findings are appended here.
 * @returns {void}
 * @throws {Error} If a directory cannot be scanned or an AsciiDoc file read.
 */
function checkDocuments(root, errors) {
  for (const path of filesUnder(root, name => name.endsWith('.a2ml'))) errors.push(`Retired state format: ${path}`);
  for (const path of filesUnder(root, name => name.endsWith('.adoc'))) {
    const text = readFileSync(path, 'utf8');
    for (const [, target] of text.matchAll(/link:([^\s[]+)\[/g)) {
      if (/^[a-z][a-z\d+.-]*:/i.test(target) || target.startsWith('#')) continue;
      const local = target.split('#')[0];
      if (!existsSync(resolve(dirname(path), local))) errors.push(`Broken local link in ${path}: ${target}`);
    }
    if (text.includes('dev-notes/2026-06-16-choreographic-types-what-it-is.adoc')) {
      errors.push(`Retired nonexistent design-note reference: ${path}`);
    }
    if (text.includes('bestpractices.dev/projects/XXXX')) errors.push(`Placeholder certification badge: ${path}`);
  }
}

/**
 * Every Agda module or script a reader could copy from README or the ledger
 * must exist: a cited path is a claim that the file is there to check.
 * @param {string} root - Repository root.
 * @param {string[]} errors - Findings are appended here.
 * @returns {void}
 */
function checkCitedPaths(root, errors) {
  for (const surface of ['README.adoc', 'PROOF-STATUS.adoc']) {
    const surfacePath = resolve(root, surface);
    if (!existsSync(surfacePath)) continue;
    const text = readFileSync(surfacePath, 'utf8');
    for (const [, source] of text.matchAll(/\b((?:src|tests|applications|scripts)\/[\w./-]+\.(?:agda|sh|mjs))\b/g)) {
      if (existsSync(resolve(root, source))) continue;
      errors.push(source.endsWith('.agda')
        ? `Nonexistent Agda build target cited in ${surface}: ${source}`
        : `Nonexistent script cited in ${surface}: ${source}`);
    }
  }
}

/**
 * Checks the documentation of the repository rooted at `root` for the
 * structural lies this notebook has told before: broken local links, retired
 * formats, placeholder badges, a README that stops disclosing that it is a
 * pre-registration or stops pointing at the proof ledger, any Agda or script
 * path cited in README or PROOF-STATUS that does not exist, and a ledger row
 * that is not bound to the definition it claims.
 * Returns the list of findings; an empty list is a pass.
 * Filesystem errors during directory scans or file reads propagate to the
 * caller rather than becoming findings, including a missing README.adoc.
 * @param {string} root - Repository root.
 * @returns {string[]} Findings.
 */
export function checkRepository(root) {
  const errors = [];
  checkDocuments(root, errors);
  const readme = readFileSync(resolve(root, 'README.adoc'), 'utf8');
  if (!/pre-registration/i.test(readme)) errors.push('README must disclose pre-registration status');
  // Proof status lives in one place, the ledger, so README must point at it
  // rather than carry a status sentence of its own that can drift from it.
  if (!readme.includes('PROOF-STATUS.adoc')) errors.push('README must point at PROOF-STATUS.adoc for what is and is not proved');
  // The ledger README points at must itself exist.
  if (!existsSync(resolve(root, 'PROOF-STATUS.adoc'))) errors.push('PROOF-STATUS.adoc, the proof ledger, is missing');
  checkCitedPaths(root, errors);
  checkLedgerBinding(root, errors);
  const citationPath = resolve(root, 'CITATION.cff');
  if (existsSync(citationPath) && !/pre-registration/i.test(readFileSync(citationPath, 'utf8'))) {
    errors.push('CITATION.cff must disclose pre-registration status');
  }
  return errors;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const errors = checkRepository(resolve(dirname(fileURLToPath(import.meta.url)), '..'));
  errors.forEach(error => console.error(error));
  if (errors.length) process.exitCode = 1;
  else console.log('Documentation integrity passed (not an Agda proof check).');
}
