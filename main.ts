// Swiftmark runner: renders every case in cases.json with parse() and
// writes the HTML strings (same order) to html.json.
//
// Usage inside the harness container:
//   node /bot/main.ts            (reads /input/cases.json, writes /output/html.json)
//
// Usage locally:
//   MAKEFUN_INPUT_DIR=./in MAKEFUN_OUTPUT_DIR=./out node main.ts
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR || '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8')) as Array<{ id: string; markdown: string }>;
const html: string[] = [];
for (const c of cases) {
  html.push(parse(c.markdown));
}
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
