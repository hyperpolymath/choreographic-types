// SPDX-License-Identifier: MPL-2.0
// Read-only audit / payload preparation. Intentionally has no PUT mode.
import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export function payloadFrom(canon) {
  const { github_owned_allowed, verified_allowed, patterns_allowed } = canon;
  if (typeof github_owned_allowed !== 'boolean' || typeof verified_allowed !== 'boolean' ||
      !Array.isArray(patterns_allowed) || !patterns_allowed.length ||
      patterns_allowed.some(p => typeof p !== 'string' || !p.trim()) ||
      new Set(patterns_allowed).size !== patterns_allowed.length) {
    throw new Error('Invalid or empty canonical allow-list; refusing to prepare a payload');
  }
  return { github_owned_allowed, verified_allowed, patterns_allowed };
}

export function samePolicy(actual, expected) {
  return actual.github_owned_allowed === expected.github_owned_allowed &&
    actual.verified_allowed === expected.verified_allowed &&
    Array.isArray(actual.patterns_allowed) &&
    JSON.stringify([...actual.patterns_allowed].sort()) === JSON.stringify([...expected.patterns_allowed].sort());
}

function api(endpoint) {
  return JSON.parse(execFileSync('gh', ['api', endpoint], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'] }));
}

function main() {
  const [mode, ref] = process.argv.slice(2);
  if (!['payload', 'audit'].includes(mode) || !/^[a-f0-9]{40}$/.test(ref ?? '') || process.argv.length !== 4) {
    throw new Error('Usage: node scripts/actions-policy.mjs <payload|audit> <standards full commit SHA>');
  }
  const file = api(`repos/hyperpolymath/standards/contents/config/settings/actions-allowlist.json?ref=${ref}`);
  const expected = payloadFrom(JSON.parse(Buffer.from(file.content, 'base64').toString('utf8')));
  console.error(`Canon ${ref}: ${expected.patterns_allowed.length} patterns`);
  if (mode === 'payload') {
    console.log(JSON.stringify(expected, null, 2));
    return;
  }
  let failed = false;
  for (const repo of ['choreographic-types', 'echo-types']) {
    try {
      const base = `repos/hyperpolymath/${repo}/actions/permissions`;
      const permissions = api(base);
      const actual = api(`${base}/selected-actions`);
      const matches = permissions.enabled === true && permissions.allowed_actions === 'selected' && samePolicy(actual, expected);
      console.log(`${repo}: ${matches ? 'MATCH' : 'DRIFT'}; live patterns=${actual.patterns_allowed?.length}; expected=${expected.patterns_allowed.length}`);
      failed ||= !matches;
    } catch (error) {
      console.error(`${repo}: UNKNOWN (API access failed); not a policy pass`);
      failed = true;
    }
  }
  if (failed) process.exitCode = 1;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { main(); } catch (error) { console.error(error.message); process.exitCode = 1; }
}
