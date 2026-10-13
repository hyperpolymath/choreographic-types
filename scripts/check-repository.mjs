// SPDX-License-Identifier: MPL-2.0
// Documentation checks only: never evidence that K-CUT is proved.  The proof
// gate is scripts/check.sh under .github/workflows/proofs.yml.
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

/**
 * Checks the documentation of the repository rooted at `root` for the
 * structural lies this notebook has told before: broken local links, retired
 * formats, placeholder badges, a README that stops disclosing that it is a
 * pre-registration or stops pointing at the proof ledger, and any Agda or
 * script path cited in README or PROOF-STATUS that does not exist.
 * Returns the list of findings; an empty list is a pass.
 * Filesystem errors during directory scans or file reads propagate to the
 * caller rather than becoming findings, including a missing README.adoc.
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
      if (['.git', 'node_modules', '.cache', '_build'].includes(entry.name)) continue;
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
