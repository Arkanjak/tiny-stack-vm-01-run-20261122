// Tiny stack VM: a complete from-scratch interpreter of make.fun's tiny stack
// ISA v1. One run answers a whole set: /input/<id>/{program.bin,input.bin}
// -> /output/<id>/{stdout.bin,exit.txt}. Env overrides are for local runs.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STEP_LIMIT = 1_000_000;
const OUT_MAX = 65_536;

// Every opcode as [byte, immediate bytes, values popped, values pushed].
const OPS = [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2], [5, 0, 2, 2],
  [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1],
  [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1],
  [26, 0, 2, 1], [27, 0, 1, 1], [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1],
  [33, 0, 2, 1], [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
];
const IMM = new Uint8Array(256).fill(255);
const NEED = new Uint8Array(256);
const GIVE = new Uint8Array(256);
for (const [o, im, po, pu] of OPS) {
  IMM[o] = im;
  NEED[o] = po;
  GIVE[o] = pu;
}

// Runs one program on its input bytes: the bytes it wrote and its exit code
// (a trap's code included; output written before a trap is kept).
function run(prog, input) {
  const n = prog.length;
  const st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const end = (code) => ({ out: out.subarray(0, ol), code });
  for (;;) {
    if (steps === STEP_LIMIT) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const im = IMM[op];
    if (im === 255) return end(5);
    if (pc + im >= n) return end(9);
    steps++;
    const nx = pc + 1 + im;
    const po = NEED[op];
    if (sp < po) return end(2);
    if (sp - po + GIVE[op] > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0:
        return end(0);
      case 1:
        st[sp++] = (prog[nx - 1] << 24) >> 24;
        break;
      case 2:
        st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 3:
        sp--;
        break;
      case 4:
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 5: {
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 6:
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 7: {
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = a;
        break;
      }
      case 23:
        st[sp - 1] = (-st[sp - 1]) | 0;
        break;
      case 27:
        st[sp - 1] = ~st[sp - 1];
        break;
      case 16:
      case 17:
      case 18:
      case 19:
      case 20:
      case 21:
      case 22:
      case 24:
      case 25:
      case 26:
      case 28:
      case 29:
      case 30:
      case 32:
      case 33:
      case 34: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 48:
        pc = nx + (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16);
        break;
      case 49: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        if (st[--sp] === 0) pc = nx + rel;
        break;
      }
      case 50: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        if (st[--sp] !== 0) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        cs[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = cs[--cp];
        break;
      case 64: {
        const a = st[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        st[sp - 1] = mem[a];
        break;
      }
      case 65: {
        const a = st[sp - 1];
        const v = st[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        mem[a] = v;
        break;
      }
      case 80: {
        const v = st[sp - 1];
        const u = v < 0 ? -v : v;
        let len = v < 0 ? 1 : 0;
        let t = u;
        do {
          len++;
          t = (t / 10) | 0;
        } while (t > 0);
        if (ol + len > OUT_MAX) return end(11);
        sp--;
        let p = ol + len;
        t = u;
        if (u === 0) {
          out[ol] = 48;
        } else {
          while (t > 0) {
            out[--p] = 48 + (t % 10);
            t = (t / 10) | 0;
          }
        }
        if (v < 0) out[ol] = 45;
        ol += len;
        break;
      }
      case 81:
        if (ol + 1 > OUT_MAX) return end(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 82:
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 83:
        return end(st[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const r = run(readFileSync(join(IN_DIR, id, 'program.bin')), readFileSync(join(IN_DIR, id, 'input.bin')));
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), String(r.code) + '\n');
}
