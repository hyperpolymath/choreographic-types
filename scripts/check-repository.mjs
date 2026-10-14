// SPDX-License-Identifier: MPL-2.0
// Documentation checks only: never evidence that K-CUT is proved.  The proof
// gate is scripts/check.sh under .github/workflows/proofs.yml.
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { basename, dirname, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const skipDirs = ['.git', 'node_modules', '.cache', '_build'];

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
    if (skipDirs.includes(entry.name)) continue;
    const path = resolve(dir, entry.name);
    if (entry.isDirectory()) out.push(...filesUnder(path, keep));
    else if (entry.isFile() && keep(entry.name)) out.push(path);
  }
  return out;
}

const escape = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const mentions = (text, id) => new RegExp(`\\b${escape(id)}\\b`).test(text);

/**
 * Index of the line that defines `name`: its type signature, its first
 * clause when it has no signature, or its record, data or module declaration.
 * @param {string[]} lines - Source lines.
 * @param {string} name - Agda identifier.
 * @returns {number} Line index, or -1.
 */
function definitionLine(lines, name) {
  const re = new RegExp(`^\\s*(?:(?:record|data|module)\\s+)?${escape(name)}(?:\\s*[:=]|\\s|$)`);
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
    if (!/^\s*$|^#!|^\{-#.*#-\}\s*$|^\s*(--|#|\/\/)/.test(line)) break;
    out.push(line);
  }
  return out.join('\n');
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
  /** @type {Map<string, string[]>} relative path -> lines */
  const sources = new Map();
  for (const dir of ['src', 'tests', 'applications', 'scripts']) {
    for (const file of filesUnder(resolve(root, dir), name => /\.(agda|sh|mjs)$/.test(name))) {
      sources.set(relative(root, file), readFileSync(file, 'utf8').split('\n'));
    }
  }
  const agda = [...sources.keys()].filter(path => path.endsWith('.agda'));
  // Module name -> files: each file's basename, plus every named nested module.
  /** @type {Map<string, string[]>} */
  const modules = new Map();
  const addModule = (name, file) => modules.set(name, [...(modules.get(name) ?? []), file]);
  for (const file of agda) {
    addModule(basename(file, '.agda'), file);
    for (const line of sources.get(file)) {
      const nested = line.match(/^\s*module\s+([^\s_(][^\s(]*)/);
      if (nested) addModule(nested[1].split('.').pop(), file);
    }
  }
  const rows = [];
  const ids = new Set();
  let sectionModules = [];
  for (const line of ledger.split('\n')) {
    const section = line.match(/^==+\s+(.*)/);
    if (section) {
      sectionModules = [...section[1].matchAll(/([\w/]+)\.agda/g)].flatMap(m => modules.get(basename(m[1])) ?? []);
      continue;
    }
    const row = line.match(/^\|\s*([A-Z]-\d+)\s*\|(.*)$/);
    if (!row) continue;
    const cells = row[2].replace(/\s*\|\s*$/, '').split(/\s\|\s/);
    if (ids.has(row[1])) errors.push(`Duplicate ledger ID ${row[1]} in PROOF-STATUS.adoc`);
    ids.add(row[1]);
    rows.push({ id: row[1], status: cells[cells.length - 1].trim(), sectionModules });
  }
  for (const { id, status, sectionModules } of rows) {
    if (/^OPEN\b/.test(status) || !/\b(PROVEN|TESTED)\b/.test(status)) continue;
    const rowModules = [];
    for (const [, name] of status.matchAll(/`([^`\s]+)`/g)) {
      if (name.includes('/') || name.endsWith('.agda')) {
        const file = name.includes('/')
          ? [name, `${name}.agda`].find(candidate => existsSync(resolve(root, candidate)))
          : agda.find(path => basename(path) === name);
        if (!file) { errors.push(`Ledger ${id} cites ${name}, which does not exist`); continue; }
        const lines = sources.get(file) ?? readFileSync(resolve(root, file), 'utf8').split('\n');
        if (!mentions(header(lines), id)) errors.push(`Ledger ${id}: the header of ${file} does not name the row`);
        continue;
      }
      const dot = name.lastIndexOf('.');
      const qualified = dot > 0 && modules.has(name.slice(0, dot));
      const target = qualified ? name.slice(dot + 1) : name;
      const candidates = qualified ? modules.get(name.slice(0, dot)) : [...rowModules, ...sectionModules, ...agda];
      if (qualified) rowModules.push(...candidates);
      let found = null;
      for (const file of candidates) {
        const i = definitionLine(sources.get(file), target);
        if (i >= 0) { found = { file, i }; break; }
      }
      if (!found) { errors.push(`Ledger ${id} cites ${name}, which is not defined under src/, tests/ or applications/`); continue; }
      if (!mentions(commentAbove(sources.get(found.file), found.i), id)) {
        errors.push(`Ledger ${id}: the comment above ${target} in ${found.file} does not name the row`);
      }
    }
  }
  // No Agda or shell comment and no document may name a row the ledger does
  // not have.  JavaScript is tooling and may quote IDs as test data.
  const letters = new Set([...ids].map(id => id[0]));
  const texts = [['PROOF-STATUS.adoc', ledger], ...[...sources].filter(([path]) => !path.endsWith('.mjs'))];
  for (const file of filesUnder(root, name => name.endsWith('.adoc'))) {
    if (basename(file) !== 'PROOF-STATUS.adoc') texts.push([relative(root, file), readFileSync(file, 'utf8')]);
  }
  for (const [file, text] of texts) {
    const body = Array.isArray(text) ? text.join('\n') : text;
    for (const [id, letter] of body.matchAll(/\b([A-Z])-\d+\b/g)) {
      if (letters.has(letter) && !ids.has(id)) errors.push(`Stale ledger reference ${id} in ${file}: PROOF-STATUS.adoc has no such row`);
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
  /**
   * Recursively checks AsciiDoc links and stale references, and flags retired
   * state files, appending findings to `errors`. Skips dependency, cache and
   * Git directories.
   * @param {string} dir - Directory to scan.
   * @returns {void}
   * @throws {Error} If a directory cannot be scanned or an AsciiDoc file read.
   */
  function walk(dir) {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      if (skipDirs.includes(entry.name)) continue;
      const path = resolve(dir, entry.name);
      if (entry.isDirectory()) walk(path);
      else if (entry.isFile()) {
        if (entry.name.endsWith('.a2ml')) errors.push(`Retired state format: ${path}`);
        if (!entry.name.endsWith('.adoc')) continue;
        const text = readFileSync(path, 'utf8');
        for (const [, target] of text.matchAll(/link:([^\s\[]+)\[/g)) {
          if (/^[a-z][a-z\d+.-]*:/i.test(target) || target.startsWith('#')) continue;
          const local = target.split('#')[0];
          if (!existsSync(resolve(dirname(path), local))) errors.push(`Broken local link in ${path}: ${target}`);
        }
        if (/dev-notes\/2026-06-16-choreographic-types-what-it-is\.adoc/.test(text)) {
          errors.push(`Retired nonexistent design-note reference: ${path}`);
        }
        if (/bestpractices\.dev\/projects\/XXXX/.test(text)) errors.push(`Placeholder certification badge: ${path}`);
      }
    }
  }
  walk(root);
  const readme = readFileSync(resolve(root, 'README.adoc'), 'utf8');
  if (!/pre-registration/i.test(readme)) errors.push('README must disclose pre-registration status');
  // Proof status lives in one place, the ledger, so README must point at it
  // rather than carry a status sentence of its own that can drift from it.
  if (!readme.includes('PROOF-STATUS.adoc')) errors.push('README must point at PROOF-STATUS.adoc for what is and is not proved');
  // The ledger README points at must itself exist.
  if (!existsSync(resolve(root, 'PROOF-STATUS.adoc'))) errors.push('PROOF-STATUS.adoc, the proof ledger, is missing');
  // Every Agda module or script a reader could copy from README or the ledger
  // must exist: a cited path is a claim that the file is there to check.
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
