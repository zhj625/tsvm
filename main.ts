// A tiny stack virtual machine for make.fun's tiny stack ISA v1 (the kit's ISA.md; the reference
// semantics are generator/subject/vm.mjs and this file follows them rule for rule, in the same order).
// One run answers every instance: for each /input/<id>/ it runs program.bin on input.bin and writes
// /output/<id>/stdout.bin (the exact bytes written) and /output/<id>/exit.txt (the exit code).
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode facts as three digit strings indexed by opcode byte: immediate bytes, values popped,
// values pushed ('.' = no such opcode, trap 5). Stack needs are checked before an instruction runs.
const IM = '01400000........000000000000000.000.............22220...........00..............0000';
const PO = '00011223........222222212221222.222.............01100...........12..............1101';
const PU = '01102233........111111111111111.111.............00000...........10..............0010';

function run(prog, input) {
  const n = prog.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256); // stack, call stack, memory
  let sp = 0, csp = 0;
  const out = new Uint8Array(65536);
  let olen = 0, inPos = 0, pc = 0, steps = 0;
  const end = (code) => [out.subarray(0, olen), code];

  for (;;) {
    if (steps === 1_000_000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const imm = IM.charCodeAt(op) - 48;
    if (!(imm >= 0)) return end(5); // a '.' hole, or a byte past the table (NaN)
    if (pc + imm >= n) return end(9);
    steps++;
    const pops = PO.charCodeAt(op) - 48;
    if (sp < pops) return end(2);
    if (sp - pops + (PU.charCodeAt(op) - 48) > 256) return end(3);
    const next = pc + 1 + imm;
    pc = next;

    switch (op) {
      case 0x00: return end(0);
      case 0x01: D[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02:
        D[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a;
        break;
      }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG wraps: -INT_MIN is INT_MIN
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: { // JMP JZ JNZ: target is next + the signed 16-bit offset
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        if (op === 0x30 || (op === 0x31) === (D[--sp] === 0)) pc = next + rel;
        break;
      }
      case 0x33: // CALL: the immediate is an absolute address
        if (csp === 64) return end(7);
        C[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: case 0x41: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        if (op === 0x40) D[sp - 1] = M[addr];
        else { M[addr] = D[sp - 2]; sp -= 2; }
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no padding, no newline
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11); // writes none of its bytes
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        D[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53: return end(D[--sp] & 255); // EXIT: the code is the value's low byte
      default: { // the two-operand group: arithmetic, logic, comparison
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // the low 32 bits of the exact product
        else if (op >= 0x13 && op <= 0x16) { // DIV MOD DIVU MODU: all trap 4 on a zero divisor
          if (b === 0) return end(4);
          if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
          else if (op === 0x14) r = b === -1 ? 0 : (a % b) | 0; // the sign of a
          else if (op === 0x15) r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
          else r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);        // only the low 5 bits of the count
        else if (op === 0x1d) r = a >> (b & 31);        // arithmetic shift
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical shift
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;         // LTU
        sp -= 2;
        D[sp++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const prog = readFileSync(join(dir, 'program.bin'));
  const input = readFileSync(join(dir, 'input.bin'));
  const [stdout, exit] = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), exit + '\n');
}
