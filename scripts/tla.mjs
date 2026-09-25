#!/usr/bin/env node
/**
 * Formal verification driver.
 *
 *   node scripts/tla.mjs model    exhaustive TLC check of the state machine
 *   node scripts/tla.mjs traces   regenerate implementation traces and validate
 *   node scripts/tla.mjs all      both
 *
 * TLC ships as a JVM jar. The driver finds a jar from `TLA2TOOLS_JAR`, then
 * `spec/vendor/tla2tools.jar`, and otherwise downloads the pinned release.
 * Override the JVM with `JAVA`.
 */

import { execFileSync, spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { delimiter, dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");
const specDir = resolve(root, "spec");
const generatedDir = resolve(specDir, "generated");
const vendorJar = resolve(specDir, "vendor/tla2tools.jar");
const TLA_VERSION = "v1.8.0";
const TLA_URL = `https://github.com/tlaplus/tlaplus/releases/download/${TLA_VERSION}/tla2tools.jar`;

const command = process.argv[2] ?? "all";

function javaMajor(candidate) {
  const probe = spawnSync(candidate, ["-version"], { encoding: "utf8" });
  if (probe.status !== 0) return -1;
  const text = `${probe.stderr ?? ""}${probe.stdout ?? ""}`;
  const match = text.match(/version "(\d+)(?:\.(\d+))?/);
  if (!match) return -1;
  const major = Number(match[1]);
  return major === 1 ? Number(match[2] ?? "0") : major;
}

function findJava() {
  const candidates = [
    process.env.JAVA,
    "java-11",
    "/usr/lib/jvm/java-11-openjdk/bin/java",
    "/usr/lib/jvm/java-17-openjdk/bin/java",
    "/usr/lib/jvm/java-21-openjdk/bin/java",
    "/usr/lib/jvm/default/bin/java",
    "java",
  ].filter((candidate) => typeof candidate === "string" && candidate.length > 0);
  for (const candidate of candidates) {
    if (javaMajor(candidate) >= 11) return candidate;
  }
  throw new Error("no Java 11+ runtime found; set JAVA to a Java 11+ executable");
}

async function ensureJar() {
  if (process.env.TLA2TOOLS_JAR) return process.env.TLA2TOOLS_JAR;
  if (existsSync(vendorJar) && statSync(vendorJar).size > 1_000_000) return vendorJar;
  process.stdout.write(`downloading TLA+ tools ${TLA_VERSION} -> ${vendorJar}\n`);
  const response = await fetch(TLA_URL);
  if (!response.ok) throw new Error(`failed to download ${TLA_URL}: ${response.status}`);
  mkdirSync(dirname(vendorJar), { recursive: true });
  writeFileSync(vendorJar, Buffer.from(await response.arrayBuffer()));
  return vendorJar;
}

function runTlc(java, jar, module, config) {
  const args = [
    "-XX:+UseParallelGC",
    "-cp",
    `${jar}${delimiter}${generatedDir}`,
    "tlc2.TLC",
    "-cleanup",
    "-deadlock",
    "-config",
    config,
    module,
  ];
  process.stdout.write(`\n$ (cd spec && ${java} ${args.join(" ")})\n`);
  const result = spawnSync(java, args, { cwd: specDir, stdio: "inherit" });
  if (result.status !== 0) {
    throw new Error(`TLC failed for ${module} (exit ${result.status ?? "signal"})`);
  }
}

function runCommand(command, args) {
  const result = spawnSync(command, args, { cwd: root, stdio: "inherit" });
  if (result.status !== 0) throw new Error(`${command} ${args.join(" ")} failed`);
}

async function checkModel(java, jar) {
  const logPath = resolve(specDir, "tlc-model.log");
  const args = [
    "-XX:+UseParallelGC",
    "-cp",
    `${jar}${delimiter}${generatedDir}`,
    "tlc2.TLC",
    "-cleanup",
    "-deadlock",
    "-config",
    "MessageBoard.cfg",
    "MessageBoard.tla",
  ];
  const result = spawnSync(java, args, { cwd: specDir, encoding: "utf8" });
  const output = `${result.stdout ?? ""}${result.stderr ?? ""}`;
  process.stdout.write(output);
  writeFileSync(logPath, output, "utf8");
  if (result.status !== 0) throw new Error(`TLC failed for the model (exit ${result.status})`);

  const distinct = output.replaceAll(",", "").match(/(\d+)\s+distinct states found/);
  if (distinct) {
    const count = Number(distinct[1]);
    writeFileSync(
      resolve(specDir, ".tlc-state-count.json"),
      JSON.stringify({ distinctStates: count, version: TLA_VERSION }, null, 2),
    );
    process.stdout.write(`\nmodel checked: ${count} distinct reachable states\n`);
  }
  return output;
}

async function main() {
  const java = findJava();
  const jar = await ensureJar();

  if (command === "model" || command === "all") {
    await checkModel(java, jar);
  }
  if (command === "traces" || command === "all") {
    runCommand(resolve(root, "node_modules/.bin/tsx"), ["scripts/emit-traces.ts"]);
    runTlc(java, jar, "TraceValidation.tla", "TraceValidation.cfg");
    process.stdout.write("trace validation passed\n");
  }
  if (!["model", "traces", "all"].includes(command)) {
    throw new Error(`unknown command ${command}; expected model, traces, or all`);
  }
}

main().catch((error) => {
  process.stderr.write(`\nformal verification failed: ${error.message}\n`);
  process.exit(1);
});
