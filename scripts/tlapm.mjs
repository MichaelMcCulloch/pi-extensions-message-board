#!/usr/bin/env node
/**
 * Inductive-proof driver (TLAPS / tlapm).
 *
 *   node scripts/tlapm.mjs        check spec/MessageBoardProof.tla
 *
 * Proves `Spec => []Inv` for EVERY value of `Agents`, `Boxes`, `Messages`,
 * `Posts`, `Topics`, `Cap`, and `MaxClock` -- the parameterized MessageBoard,
 * not only the TLC fixture. `spec/MessageBoardProof.tla` establishes
 * `Init => Inv` and that each of the nine actions preserves each invariant
 * component; `PTL` turns that into `[]Inv` (983 obligations).
 *
 * The driver locates tlapm from `TLAPM`, then `~/.local/tlapm/bin/tlapm`,
 * then `PATH`, and its stdlib from `TLAPM_LIBRARY`, then the sibling lib
 * directory, then a small set of conventional install locations. TLAPS needs a
 * Z3 on `PATH`; tlapm 1.6.x works with Z3 4.8+ (the pre-1.6 tlapm does not
 * work with modern Z3, and the TLAPS 1.5.0 Linux installer ships without its
 * backends).
 */

import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { delimiter, dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");
const specDir = resolve(root, "spec");
const PROOF = "MessageBoardProof.tla";

function findTlapm() {
  const candidates = [
    process.env.TLAPM,
    resolve(process.env.HOME ?? "", ".local/tlapm/bin/tlapm"),
    "/usr/local/bin/tlapm",
    "/usr/bin/tlapm",
  ].filter((candidate) => typeof candidate === "string" && candidate.length > 0);
  for (const candidate of candidates) {
    if (candidate === "tlapm" || existsSync(candidate)) return candidate;
  }
  return "tlapm";
}

function findStdlib(tlapm) {
  if (process.env.TLAPM_LIBRARY) return process.env.TLAPM_LIBRARY;
  const candidates = [
    resolve(dirname(tlapm), "..", "lib/tlapm/stdlib"),
    resolve(process.env.HOME ?? "", ".local/tlapm/lib/tlapm/stdlib"),
    "/usr/local/lib/tlapm/stdlib",
    "/usr/lib/tlapm/stdlib",
  ];
  for (const candidate of candidates) {
    if (existsSync(resolve(candidate, "TLAPS.tla"))) return candidate;
  }
  return undefined;
}

function main() {
  const tlapm = findTlapm();
  const stdlib = findStdlib(tlapm);
  const args = [];
  if (stdlib) args.push("-I", stdlib);
  args.push(PROOF);

  process.stdout.write(`\n$ (cd spec && ${tlapm} ${args.join(" ")})\n`);
  const result = spawnSync(tlapm, args, {
    cwd: specDir,
    stdio: "inherit",
    env: { ...process.env, PATH: `${dirname(tlapm)}${delimiter}${process.env.PATH ?? ""}` },
  });
  if (result.error) {
    process.stderr.write(
      `\nTLAPS not available (${result.error.message}).\n` +
        "Install tlapm 1.6+ (e.g. https://github.com/tlaplus/tlapm/releases) and a Z3 on PATH,\n" +
        "or set TLAPM and TLAPM_LIBRARY.\n",
    );
    process.exit(1);
  }
  if (result.status !== 0) {
    process.stderr.write(`\ninductive proof failed (tlapm exit ${result.status ?? "signal"})\n`);
    process.exit(1);
  }
  process.stdout.write("inductive proof passed: Spec => []Inv for all constants\n");
}

main();
