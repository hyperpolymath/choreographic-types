// SPDX-License-Identifier: MPL-2.0
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { checkRepository } from '../scripts/check-repository.mjs';
import { payloadFrom, samePolicy } from '../scripts/actions-policy.mjs';

const status = 'A pre-registration. Nothing in this repo is proven yet.\n';
function fixture(t, files = {}) {
  const root = mkdtempSync(join(tmpdir(), 'choreo-check-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const [name, text] of Object.entries({ 'README.adoc': status, ...files })) writeFileSync(join(root, name), text);
  return root;
}
test('honest pre-registration passes', t => assert.deepEqual(checkRepository(fixture(t)), []));
test('existing local and external links pass', t => {
  const root = fixture(t, { 'README.adoc': status + 'link:note.adoc#heading[note] link:https://example.org/[web]', 'note.adoc': 'note' });
  assert.deepEqual(checkRepository(root), []);
});
for (const [name, files, expected] of [
  ['broken link', { 'note.adoc': 'link:absent.agda[]' }, /Broken local link/],
  ['retired state', { 'STATE.a2ml': 'stale' }, /Retired state format/],
  ['missing build', { 'README.adoc': status + 'agda --no-libraries -i src src/ChoreographicTypes/All.agda' }, /Nonexistent Agda build/],
  ['missing note', { 'note.adoc': '`dev-notes/2026-06-16-choreographic-types-what-it-is.adoc`' }, /nonexistent design-note/],
  ['false badge', { 'note.adoc': 'https://www.bestpractices.dev/projects/XXXX' }, /Placeholder/],
  ['lost proof disclosure', { 'README.adoc': 'pre-registration' }, /proof status/],
  ['lost project disclosure', { 'README.adoc': 'Nothing in this repo is proven yet.' }, /pre-registration status/],
]) test(`regression: ${name}`, t => assert.match(checkRepository(fixture(t, files)).join('\n'), expected));

test('regression: completed-formalisation claim in README', t => {
  const files = { 'README.adoc': status + 'An Agda formalisation of a graded theory.\n' };
  assert.match(checkRepository(fixture(t, files)).join('\n'), /completed Agda formalisation/);
});
test('regression: completed-formalisation claim in CITATION.cff', t => {
  const files = { 'CITATION.cff': 'abstract: "Agda formalisation of a graded multiparty-session type theory."\n' };
  assert.match(checkRepository(fixture(t, files)).join('\n'), /completed Agda formalisation/);
});
test('regression: citation without pre-registration disclosure', t => {
  const files = { 'CITATION.cff': 'title: "Choreographic Types"\nabstract: "A graded theory notebook."\n' };
  assert.match(checkRepository(fixture(t, files)).join('\n'), /CITATION\.cff must disclose/);
});
test('honest citation metadata passes', t => {
  const files = { 'CITATION.cff': 'abstract: "A pre-registration; Agda is the intended prover, no checked formalisation yet."\n' };
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
