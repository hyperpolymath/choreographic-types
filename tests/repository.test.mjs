// SPDX-License-Identifier: MPL-2.0
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { checkRepository } from '../scripts/check-repository.mjs';
import { payloadFrom, samePolicy } from '../scripts/actions-policy.mjs';

const status = 'A pre-registration. What is and is not proved: PROOF-STATUS.adoc.\n';
const ledger = '| K-1 | claim | OPEN |\n';
/**
 * Creates a temporary repository with a README and proof ledger, applying
 * file overrides and registering cleanup after the test.
 * @param {import('node:test').TestContext} t - Test context used for cleanup.
 * @param {Record<string, string | null>} files - File contents; null omits a file.
 * @returns {string} Path to the temporary repository.
 */
function fixture(t, files = {}) {
  const root = mkdtempSync(join(tmpdir(), 'choreo-check-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const [name, text] of Object.entries({ 'README.adoc': status, 'PROOF-STATUS.adoc': ledger, ...files })) {
    if (text === null) continue;
    mkdirSync(dirname(join(root, name)), { recursive: true });
    writeFileSync(join(root, name), text);
  }
  return root;
}
test('honest pre-registration passes', t => assert.deepEqual(checkRepository(fixture(t)), []));
test('existing local and external links pass', t => {
  const root = fixture(t, { 'README.adoc': status + 'link:note.adoc#heading[note] link:https://example.org/[web]', 'note.adoc': 'note' });
  assert.deepEqual(checkRepository(root), []);
});
test('existing cited Agda and script paths pass', t => {
  const root = fixture(t, {
    'README.adoc': status + 'Check with `bash scripts/check.sh`; the keystone is `src/K.agda`.\n',
    'PROOF-STATUS.adoc': '| K-1 | claim | PROVEN (`src/K.agda`) |\n',
    'scripts/check.sh': '',
    'src/K.agda': '-- Ledger K-1.\nmodule K where\n',
  });
  assert.deepEqual(checkRepository(root), []);
});

// The ledger binds claims to code: a cited name must be defined, and the
// comment above it (or the header of a cited file) must name the row.
const bound = {
  'PROOF-STATUS.adoc': '== Keystone (K.agda)\n| K-1 | claim | PROVEN (`K.thm`, `lemma`)\n| K-2 | claim | TESTED (`tests/reject/Bad`)\n| K-3 | claim | OPEN\n',
  'src/K.agda': 'module K where\n-- The theorem, and a lemma inside a nested module.\n-- Ledger K-1.\nthm : Set\nthm = Set\nmodule Inner where\n  -- Ledger K-1.\n  lemma = thm\n',
  'tests/reject/Bad.agda': '{-# OPTIONS --safe #-}\n-- Ledger K-2.\nmodule Bad where\n',
};
test('ledger rows bound to commented definitions pass', t => assert.deepEqual(checkRepository(fixture(t, bound)), []));
for (const [name, files, expected] of [
  ['ledger cites an undefined name', { 'PROOF-STATUS.adoc': bound['PROOF-STATUS.adoc'].replace('`K.thm`', '`K.missing`') }, /K-1 cites K\.missing, which is not defined/],
  ['ledger cites a missing file', { 'PROOF-STATUS.adoc': bound['PROOF-STATUS.adoc'].replace('tests/reject/Bad', 'tests/reject/Gone') }, /K-2 cites tests\/reject\/Gone, which does not exist/],
  ['cited definition does not name its row', { 'src/K.agda': bound['src/K.agda'].replace('-- Ledger K-1.\nthm', 'thm') }, /K-1: the comment above thm in src\/K\.agda does not name the row/],
  ['a blank line breaks the comment block', { 'src/K.agda': bound['src/K.agda'].replace('-- Ledger K-1.\nthm', '-- Ledger K-1.\n\nthm') }, /comment above thm .* does not name the row/],
  ['cited file header does not name its row', { 'tests/reject/Bad.agda': 'module Bad where\n-- Ledger K-2.\n' }, /K-2: the header of tests\/reject\/Bad\.agda does not name the row/],
  ['duplicate ledger ID', { 'PROOF-STATUS.adoc': bound['PROOF-STATUS.adoc'].replace('| K-2 |', '| K-1 |') }, /Duplicate ledger ID K-1/],
  ['stale ledger reference in a comment', { 'src/K.agda': bound['src/K.agda'].replace('-- Ledger K-1.\nthm', '-- Ledger K-1, K-9.\nthm') }, /Stale ledger reference K-9 in src\/K\.agda/],
  ['stale ledger reference in a document', { 'note.adoc': 'See K-7.' }, /Stale ledger reference K-7 in note\.adoc/],
]) test(`regression: ${name}`, t => assert.match(checkRepository(fixture(t, { ...bound, ...files })).join('\n'), expected));
for (const [name, files, expected] of [
  ['broken link', { 'note.adoc': 'link:absent.agda[]' }, /Broken local link/],
  ['retired state', { 'STATE.a2ml': 'stale' }, /Retired state format/],
  ['missing build', { 'README.adoc': status + 'agda --no-libraries -i src src/ChoreographicTypes/All.agda' }, /Nonexistent Agda build target cited in README/],
  ['missing module in the ledger', { 'PROOF-STATUS.adoc': 'PROVEN (`src/Choreographic/Missing.agda`)' }, /Nonexistent Agda build target cited in PROOF-STATUS/],
  ['missing script', { 'README.adoc': status + 'run `bash scripts/absent.sh`' }, /Nonexistent script cited in README/],
  ['missing note', { 'note.adoc': '`dev-notes/2026-06-16-choreographic-types-what-it-is.adoc`' }, /nonexistent design-note/],
  ['false badge', { 'note.adoc': 'https://www.bestpractices.dev/projects/XXXX' }, /Placeholder/],
  ['lost ledger pointer', { 'README.adoc': 'A pre-registration with a status line of its own: everything is proven.' }, /must point at PROOF-STATUS\.adoc/],
  ['missing ledger', { 'PROOF-STATUS.adoc': null }, /PROOF-STATUS\.adoc, the proof ledger, is missing/],
  ['lost project disclosure', { 'README.adoc': 'Status: PROOF-STATUS.adoc' }, /pre-registration status/],
]) test(`regression: ${name}`, t => assert.match(checkRepository(fixture(t, files)).join('\n'), expected));

test('regression: citation without pre-registration disclosure', t => {
  const files = { 'CITATION.cff': 'title: "Choreographic Types"\nabstract: "A graded theory notebook."\n' };
  assert.match(checkRepository(fixture(t, files)).join('\n'), /CITATION\.cff must disclose/);
});
test('honest citation metadata passes', t => {
  const files = { 'CITATION.cff': 'abstract: "A pre-registration; the checked fragment is ledgered in PROOF-STATUS.adoc."\n' };
  assert.deepEqual(checkRepository(fixture(t, files)), []);
});

const canon = { github_owned_allowed: true, verified_allowed: true, patterns_allowed: ['owner/a@*', 'owner/b@*'] };
test('payload strips non-API metadata', () => assert.deepEqual(payloadFrom({ ...canon, version: 1 }), canon));
test('empty, malformed and duplicate patterns fail closed', () => {
  for (const patterns_allowed of [[], null, [''], [3], ['a', 'a']]) assert.throws(() => payloadFrom({ ...canon, patterns_allowed }));
  assert.throws(() => payloadFrom({ ...canon, verified_allowed: 'true' }));
});
test('comparison ignores ordering but detects same-count drift and flags', () => {
  assert.ok(samePolicy({ ...canon, patterns_allowed: [...canon.patterns_allowed].reverse() }, canon));
  assert.ok(!samePolicy({ ...canon, patterns_allowed: ['owner/a@*', 'other/c@*'] }, canon));
  assert.ok(!samePolicy({ ...canon, verified_allowed: false }, canon));
  assert.ok(!samePolicy({ ...canon, patterns_allowed: [] }, canon));
});
