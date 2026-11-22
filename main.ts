// Tiny stack VM: faithful interpreter of make.fun's tiny stack ISA v1.
// One run answers a whole set: /input/<id>/{program,input}.bin ->
// /output/<id>/{stdout.bin,exit.txt}. Traps keep prior output; exit code is
// the trap's code. Step limit, pc, opcode, immediate, stack checks run in
// ISA order before each instruction's own traps and effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
function run(p: Uint8Array, q: Uint8Array) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), o = new Uint8Array(65536);
  let s = 0, c = 0, n = 0, ip = 0, pc = 0, t = 0;
  const d = (x: number) => ({ out: o.subarray(0, n), code: x });
  for (;;) {
    if (t === 1e6) return d(10);
    if (pc < 0 || pc >= p.length) return d(9);
    const k = p[pc];
    let f = 0, u = 0, v = 0;
    switch (k) {
      case 0x01: f = 1; v = 1; break;
      case 0x02: f = 4; v = 1; break;
      case 0x03: u = 1; break;
      case 0x04: u = 1; v = 2; break;
      case 0x05: u = 2; v = 2; break;
      case 0x06: u = 2; v = 3; break;
      case 0x07: u = 3; v = 3; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20:
      case 0x21: case 0x22: u = 2; v = 1; break;
      case 0x17: case 0x1b: u = 1; v = 1; break;
      case 0x30: f = 2; break;
      case 0x31: case 0x32: f = 2; u = 1; break;
      case 0x33: f = 2; break;
      case 0x40: u = 1; v = 1; break;
      case 0x41: u = 2; break;
      case 0x50: case 0x51: case 0x53: u = 1; break;
      case 0x52: v = 1; break;
      case 0x00: case 0x34: break;
      default: return d(5);
    }
    if (pc + f >= p.length) return d(9);
    t++;
    if (s < u) return d(2);
    if (s - u + v > 256) return d(3);
    const nx = pc + 1 + f;
    pc = nx;
    switch (k) {
      case 0x00: return d(0);
      case 0x01: D[s++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[s++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: s--; break;
      case 0x04: D[s] = D[s - 1]; s++; break;
      case 0x05: { const a = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = a; break; }
      case 0x06: D[s] = D[s - 2]; s++; break;
      case 0x07: { const a = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = a; break; }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20:
      case 0x21: case 0x22: {
        const b = D[s - 1], a = D[s - 2];
        let r: number;
        switch (k) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return d(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return d(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return d(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return d(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        s -= 2; D[s++] = r; break;
      }
      case 0x17: D[s - 1] = (-D[s - 1]) | 0; break;
      case 0x1b: D[s - 1] = ~D[s - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (k !== 0x30) { const x = D[--s]; take = k === 0x31 ? x === 0 : x !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (c === 64) return d(7);
        C[c++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:
        if (c === 0) return d(8);
        pc = C[--c]; break;
      case 0x40: {
        const a = D[s - 1];
        if (a < 0 || a >= 256) return d(6);
        D[s - 1] = M[a]; break;
      }
      case 0x41: {
        const a = D[s - 1], x = D[s - 2];
        if (a < 0 || a >= 256) return d(6);
        s -= 2; M[a] = x; break;
      }
      case 0x50: {
        const w = String(D[s - 1]);
        if (n + w.length > 65536) return d(11);
        s--;
        for (let i = 0; i < w.length; i++) o[n++] = w.charCodeAt(i);
        break;
      }
      case 0x51:
        if (n + 1 > 65536) return d(11);
        o[n++] = D[--s] & 255; break;
      case 0x52: D[s++] = ip < q.length ? q[ip++] : -1; break;
      default: return d(D[--s] & 255); // EXIT
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
