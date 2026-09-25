/**
 * Write the generated trace module consumed by TraceValidation.tla.
 *
 * Run through tsx: `tsx scripts/emit-traces.ts`.
 */

import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { buildTraces, renderTracesModule } from "../src/formal/trace.ts";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");
const output = resolve(root, "spec/generated/TracesData.tla");

const traces = buildTraces();
mkdirSync(dirname(output), { recursive: true });
writeFileSync(output, renderTracesModule(traces.map((entry) => entry.trace)), "utf8");

process.stdout.write(
  `wrote ${output} with ${traces.length} trace(s): ${traces.map((entry) => entry.name).join(", ")}\n`,
);
