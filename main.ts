// Tiny stack VM for make.fun's tiny-stack-vm-01 (ISA v1), from scratch.
// Runs every program in /input/<id>/, writes /output/<id>/stdout.bin +
// exit.txt. 32-bit wrapping arithmetic, all ten traps, step/output limits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode validity + immediate length.
function imm(op) {
  if (op === 0x01) return 1;
  if (op === 0x02) return 4;
  if (op >= 0x30 && op <= 0x33) return 2;
  return 0;
}
function valid(op) {
  return op <= 0x07 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34)
    || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
}

// Stack shape per opcode, packed as pops * 4 + pushes (both fit in 2 bits).
function shape(op) {
  if (op === 0x07) return 15; // 3 pops, 3 pushes
  if (op === 0x05) return 10; // 2 pops, 2 pushes
  if (op === 0x06) return 11; // 2 pops, 3 pushes
  if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) return 9; // 2, 1
  if (op === 0x41) return 8; // 2, 0
  if (op === 0x04) return 6; // 1, 2
  if (op === 0x40) return 5; // 1, 1
  if (op === 0x03 || op === 0x17 || op === 0x1b || op === 0x31 || op === 0x32
    || op === 0x50 || op === 0x51 || op === 0x53) return 4; // 1, 0
  if (op === 0x01 || op === 0x02 || op === 0x52) return 1; // 0, 1
  return 0;
}

// Two-operand arithmetic. Returns null only for division by zero (trap 4).
function bin(op, a, b) {
  switch (op) {
    case 0x10: return (a + b) | 0;
    case 0x11: return (a - b) | 0;
    case 0x12: return Math.imul(a, b);
    case 0x13: return b === 0 ? null : (a / b) | 0;
    case 0x14: return b === 0 ? null : b === -1 ? 0 : (a % b) | 0;
    case 0x15: return b === 0 ? null : Math.floor((a >>> 0) / (b >>> 0)) | 0;
    case 0x16: return b === 0 ? null : ((a >>> 0) % (b >>> 0)) | 0;
    case 0x18: return a & b;
    case 0x19: return a | b;
    case 0x1a: return a ^ b;
    case 0x1c: return a << b;
    case 0x1d: return a >> b;
    case 0x1e: return (a >>> b) | 0;
    case 0x20: return a === b ? 1 : 0;
    case 0x21: return a < b ? 1 : 0;
    default: return (a >>> 0) < (b >>> 0) ? 1 : 0; // 0x22 LTU
  }
}

function run(p, inp) {
  const n = p.length;
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64);  // call stack
  const M = new Int32Array(256); // memory
  const O = new Uint8Array(65536); // output bytes
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, st = 0;
  for (;;) {
    if (st === 1000000) return { out: O.subarray(0, ol), code: 10 };
    if (pc < 0 || pc >= n) return { out: O.subarray(0, ol), code: 9 };
    const op = p[pc];
    if (!valid(op)) return { out: O.subarray(0, ol), code: 5 };
    const im = imm(op);
    if (pc + im >= n) return { out: O.subarray(0, ol), code: 9 };
    st++;
    const nx = pc + 1 + im;
    const sh = shape(op);
    const need = sh >> 2, give = sh & 3;
    if (sp < need) return { out: O.subarray(0, ol), code: 2 };
    if (sp - need + give > 256) return { out: O.subarray(0, ol), code: 3 };
    pc = nx;
    switch (op) {
      case 0x00: return { out: O.subarray(0, ol), code: 0 }; // HALT
      case 0x01: S[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: S[sp] = S[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 0x06: S[sp] = S[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
      case 0x17: S[sp - 1] = (-S[sp - 1]) | 0; break; // NEG
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        const r = bin(op, a, b);
        if (r === null) return { out: O.subarray(0, ol), code: 4 };
        sp -= 2; S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return { out: O.subarray(0, ol), code: 7 };
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return { out: O.subarray(0, ol), code: 8 };
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return { out: O.subarray(0, ol), code: 6 };
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE
        const addr = S[sp - 1], v = S[sp - 2];
        if (addr < 0 || addr >= 256) return { out: O.subarray(0, ol), code: 6 };
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: { // PRINT
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return { out: O.subarray(0, ol), code: 11 };
        sp--;
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (ol + 1 > 65536) return { out: O.subarray(0, ol), code: 11 };
        O[ol++] = S[--sp] & 255;
        break;
      case 0x52: S[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN
      case 0x53: return { out: O.subarray(0, ol), code: S[--sp] & 255 }; // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
