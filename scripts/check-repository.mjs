// SPDX-License-Identifier: MPL-2.0
// Documentation checks only: never evidence that K-CUT is proved.
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export function checkRepository(root) {
  const errors = [];
  function walk(dir) {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      if (['.git', 'node_modules', '.cache'].includes(entry.name)) continue;
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
  if (!readme.includes('Nothing in this repo is proven yet.')) errors.push('README must disclose proof status');
  for (const [, source] of readme.matchAll(/\bagda\b[^\n]*?([\w./-]+\.agda)/g)) {
    if (!existsSync(resolve(root, source))) errors.push(`Nonexistent Agda build target: ${source}`);
  }
  // The surfaces that mirror the repository description must not claim a
  // completed formalisation until a checked module exists (issue #15, D-4).
  // Relax this in the same change that lands the first checked module.
  for (const surface of ['README.adoc', 'CITATION.cff']) {
    const surfacePath = resolve(root, surface);
    if (!existsSync(surfacePath)) continue;
    if (/agda\s+formali[sz]ation/i.test(readFileSync(surfacePath, 'utf8'))) {
      errors.push(`Description claim of a completed Agda formalisation in ${surface}; not true until a checked module exists`);
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
