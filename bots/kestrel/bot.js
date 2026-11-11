// 红隼 Kestrel —— 纯视觉闭环参赛脚本。
// 对局中的全部输入只有 lab.observe / lab.act / lab.fire 返回的 JPEG；输出只有移动、旋转、瞄准和单发请求。
// 流程：JPEG 局部解码 -> 像素感知（两车位置与装甲相位、炮管、弹丸、HUD 条）
//       -> 状态估计（对手位移的经验分布、来弹轨迹、热量）-> 贴身 -> 机动 / 装甲相位防御 / 瞄准 / 开火。
// 策略说明、实测数据和已知局限见同目录 README.md。

// ───────────────────────── JPEG 局部解码 ─────────────────────────
// 供图是基线 JPEG、三个分量同采样（4:4:4）。熵码必须顺序读完，但反变换只对需要像素的
// 最小编码单元做：两车周围、HUD 条，以及亮度相对背景突增的单元（弹丸）。整帧只花几毫秒。
const B64 = new Uint8Array(128);
for (let i = 0; i < 64; i++) B64['ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'.charCodeAt(i)] = i;
const ZZ = Uint8Array.from([0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63]);
const AAN = [1, 1.387039845, 1.306562965, 1.175875602, 1, 0.785694958, 0.5411961, 0.275899379];
let jb = new Uint8Array(1 << 18), bp = 0, bb = 0, bc = 0;
// H、V：每个编码单元横纵各含几个 8×8 块；uw、uh：单元像素尺寸；mw、mh：单元网格。
const J = { w: 0, h: 0, H: 1, V: 1, nb: 1, uw: 8, uh: 8, mw: 0, mh: 0, nm: 0, scan: 0, head: null, ht: [], qt: [0, 1, 2, 3].map(() => new Float32Array(64)),
  c: [0, 1, 2].map(() => ({ q: null, dc: null, ac: null, pred: 0, tq: 0, co: [0, 1, 2, 3].map(() => new Float32Array(64)), flat: [true, true, true, true] })) };
let F = null;                         // RGB 帧缓冲（只有本帧解出的单元是新的）
let need = null, got = null, dn = null, nDn = 0, fno = 0, mst = null, bg = null, lastDc = null, still = null, flood = false;
const hot = new Int32Array(4096);

function b64bytes(s) {
  const n = s.length;
  if (jb.length < n) jb = new Uint8Array(n * 2);
  let o = 0;
  for (let i = 0; i < n; i += 4) {
    const v = B64[s.charCodeAt(i)] << 18 | B64[s.charCodeAt(i + 1)] << 12 | B64[s.charCodeAt(i + 2) & 127] << 6 | B64[s.charCodeAt(i + 3) & 127];
    jb[o++] = v >> 16; jb[o++] = v >> 8 & 255; jb[o++] = v & 255;
  }
}
function huff(p) {
  let n = 0;
  for (let i = 0; i < 16; i++) n += jb[p + i];
  const T = { look: new Uint16Array(512), maxc: new Int32Array(18), minc: new Int32Array(18), ptr: new Int32Array(18), vals: jb.slice(p + 16, p + 16 + n), size: 17 + n };
  let code = 0, k = 0;
  for (let len = 1; len <= 16; len++) {
    const cnt = jb[p + len - 1];
    T.minc[len] = code; T.ptr[len] = k;
    for (let i = 0; i < cnt; i++, k++, code++) if (len <= 9) { const base = code << (9 - len); for (let j = 0; j < 1 << (9 - len); j++) T.look[base + j] = len << 8 | T.vals[k]; }
    T.maxc[len] = cnt ? code - 1 : -1;
    code <<= 1;
  }
  return T;
}
function parseHead() {
  if (jb[0] !== 255 || jb[1] !== 216) throw Error('jpeg');
  // 头部与上一帧完全相同时沿用已建好的表。
  if (J.head) { let same = true; for (let i = 0; i < J.scan; i++) if (jb[i] !== J.head[i]) { same = false; break; } if (same) return; }
  let p = 2;
  for (;;) {
    if (jb[p] !== 255) throw Error('jpeg');
    const m = jb[p + 1], len = jb[p + 2] << 8 | jb[p + 3], end = p + 2 + len;
    if (m === 0xdb) {
      for (let q = p + 4; q < end;) { const id = jb[q] & 3, wide = jb[q] >> 4; q++; for (let i = 0; i < 64; i++) { const z = ZZ[i]; J.qt[id][z] = (wide ? jb[q] << 8 | jb[q + 1] : jb[q]) * AAN[z >> 3] * AAN[z & 7] / 8; q += wide ? 2 : 1; } }
    } else if (m === 0xc0) {
      J.h = jb[p + 5] << 8 | jb[p + 6]; J.w = jb[p + 7] << 8 | jb[p + 8];
      const hv = jb[p + 11];
      if (jb[p + 9] !== 3 || jb[p + 14] !== hv || jb[p + 17] !== hv || (hv >> 4) > 2 || (hv & 15) > 2) throw Error('jpeg');
      J.H = hv >> 4; J.V = hv & 15;
      for (let i = 0; i < 3; i++) J.c[i].tq = jb[p + 12 + i * 3];
    } else if (m === 0xc4) {
      for (let q = p + 4; q < end;) { const T = huff(q + 1); J.ht[(jb[q] >> 4) * 4 + (jb[q] & 3)] = T; q += T.size; }
    } else if (m === 0xdd) { if (jb[p + 4] || jb[p + 5]) throw Error('jpeg'); }
    else if (m === 0xda) {
      for (let i = 0; i < 3; i++) { const t = jb[p + 6 + i * 2]; J.c[i].dc = J.ht[t >> 4]; J.c[i].ac = J.ht[4 + (t & 15)]; J.c[i].q = J.qt[J.c[i].tq]; }
      J.scan = end; J.head = jb.slice(0, end);
      break;
    } else if (m >= 0xc1 && m <= 0xcf && m !== 0xc8) throw Error('jpeg');
    p = end;
  }
  J.nb = J.H * J.V; J.uw = 8 * J.H; J.uh = 8 * J.V;
  J.mw = Math.ceil(J.w / J.uw); J.mh = Math.ceil(J.h / J.uh);
  const nm = J.mw * J.mh;
  if (J.nm !== nm || !mst || bg.length !== nm * J.nb) {
    J.nm = nm;
    F = new Uint8ClampedArray(J.w * J.h * 3); need = new Uint8Array(nm); got = new Int32Array(nm); dn = new Int32Array(nm);
    mst = new Int32Array(nm * 6); bg = new Float32Array(nm * J.nb).fill(-999); lastDc = new Int16Array(nm * J.nb); still = new Uint8Array(nm * J.nb);
  }
}
function fill() {
  while (bc <= 24) {
    let c = jb[bp++];
    if (c === 255) { if (jb[bp] === 0) bp++; else { bp--; c = 0; } }
    bb = bb << 8 | c; bc += 8;
  }
}
function sym(T) {
  if (bc < 16) fill();
  const e = T.look[(bb >>> (bc - 9)) & 511];
  if (e) { bc -= e >> 8; return e & 255; }
  let code = (bb >>> (bc - 9)) & 511;
  for (let len = 10; len <= 16; len++) {
    code = code << 1 | ((bb >>> (bc - len)) & 1);
    if (code <= T.maxc[len]) { bc -= len; return T.vals[T.ptr[len] + code - T.minc[len]]; }
  }
  throw Error('jpeg');
}
// 解一个 8×8 块的熵码；out 为空时只跳过（仍要更新直流预测）。返回该块是否只有直流分量。
function block(c, out) {
  let s = sym(c.dc);
  if (s) { if (bc < 16) fill(); let v = (bb >>> (bc - s)) & ((1 << s) - 1); bc -= s; if (v < 1 << (s - 1)) v -= (1 << s) - 1; c.pred += v; }
  const q = c.q, ac = c.ac;
  let flat = true;
  if (out) { out.fill(0); out[0] = c.pred * q[0]; }
  for (let k = 1; k < 64;) {
    const rs = sym(ac); s = rs & 15;
    if (!s) { if (rs < 0xf0) break; k += 16; continue; }
    k += rs >> 4;
    if (bc < 16) fill();
    if (out) { let v = (bb >>> (bc - s)) & ((1 << s) - 1); if (v < 1 << (s - 1)) v -= (1 << s) - 1; const z = ZZ[k]; out[z] = v * q[z]; flat = false; }
    bc -= s; k++;
  }
  return flat;
}
// 浮点 AAN 反余弦变换（量化表已预乘比例因子），原地输出像素差值。
function idct(d) {
  for (let pass = 0; pass < 2; pass++) {
    const st = pass ? 1 : 8, lim = pass ? 64 : 8, inc = pass ? 8 : 1;
    for (let i = 0; i < lim; i += inc) {
      const a0 = d[i], a1 = d[i + st], a2 = d[i + 2 * st], a3 = d[i + 3 * st], a4 = d[i + 4 * st], a5 = d[i + 5 * st], a6 = d[i + 6 * st], a7 = d[i + 7 * st];
      const t10 = a0 + a4, t11 = a0 - a4, t13 = a2 + a6, t12 = (a2 - a6) * 1.414213562 - t13;
      const e0 = t10 + t13, e3 = t10 - t13, e1 = t11 + t12, e2 = t11 - t12;
      const z13 = a5 + a3, z10 = a5 - a3, z11 = a1 + a7, z12 = a1 - a7;
      const o7 = z11 + z13, z5 = (z10 + z12) * 1.847759065;
      const o6 = -2.61312593 * z10 + z5 - o7, o5 = (z11 - z13) * 1.414213562 - o6, o4 = 1.0823922 * z12 - z5 + o5;
      d[i] = e0 + o7; d[i + 7 * st] = e0 - o7; d[i + st] = e1 + o6; d[i + 6 * st] = e1 - o6;
      d[i + 2 * st] = e2 + o5; d[i + 5 * st] = e2 - o5; d[i + 4 * st] = e3 + o4; d[i + 3 * st] = e3 - o4;
    }
  }
}
// 完整解出一个编码单元并写入帧缓冲。
function unit(m) {
  const c = J.c, nb = J.nb, w = J.w;
  for (let k = 0; k < 3; k++) for (let j = 0; j < nb; j++) c[k].flat[j] = block(c[k], c[k].co[j]);
  const X0 = (m % J.mw) * J.uw, Y0 = ((m / J.mw) | 0) * J.uh;
  for (let j = 0; j < nb; j++) {
    const yy = c[0].co[j], cb = c[1].co[j], cr = c[2].co[j];
    if (c[0].flat[j]) yy.fill(yy[0]); else idct(yy);
    if (c[1].flat[j]) cb.fill(cb[0]); else idct(cb);
    if (c[2].flat[j]) cr.fill(cr[0]); else idct(cr);
    const x0 = X0 + (j % J.H) * 8, y0 = Y0 + ((j / J.H) | 0) * 8, xe = Math.min(8, w - x0), ye = Math.min(8, J.h - y0);
    for (let y = 0; y < ye; y++) {
      let o = ((y0 + y) * w + x0) * 3, i = y * 8;
      for (let x = 0; x < xe; x++, i++, o += 3) { const Y = yy[i] + 128, b = cb[i], r = cr[i]; F[o] = Y + 1.402 * r; F[o + 1] = Y - 0.344136 * b - 0.714136 * r; F[o + 2] = Y + 1.772 * b; }
    }
  }
  got[m] = fno; dn[nDn++] = m;
}
function rewind(m) {
  const i = m * 6;
  bp = mst[i]; bb = mst[i + 1]; bc = mst[i + 2]; J.c[0].pred = mst[i + 3]; J.c[1].pred = mst[i + 4]; J.c[2].pred = mst[i + 5];
}
// 解一帧：need[m]=1 的单元必解；其余只读亮度直流，与背景相比突增的（弹丸、特效）连同邻近单元补解。
// all=true 时整帧全解（首帧或跟丢时用）。
function decode(all) {
  const c = J.c, nm = J.nm, mw = J.mw, nb = J.nb, k0 = c[0].q[0], rebase = flood;
  bp = J.scan; bb = 0; bc = 0; c[0].pred = c[1].pred = c[2].pred = 0;
  fno++; nDn = 0;
  let nHot = 0, nUp = 0;
  for (let m = 0; m < nm; m++) {
    const i = m * 6;
    mst[i] = bp; mst[i + 1] = bb; mst[i + 2] = bc; mst[i + 3] = c[0].pred; mst[i + 4] = c[1].pred; mst[i + 5] = c[2].pred;
    if (all || need[m]) { unit(m); continue; }
    let up = false;
    for (let j = 0; j < nb; j++) {
      block(c[0], null);
      const u = m * nb + j, dcv = c[0].pred, v = dcv * k0;
      // 背景维护：连续多帧不变才认作新背景，弹丸不会在同一处停留。
      if (Math.abs(dcv - lastDc[u]) <= 1) { if (still[u] < 250) still[u]++; } else still[u] = 0;
      lastDc[u] = dcv;
      if (rebase || bg[u] < -500 || still[u] >= 5) bg[u] = v;
      else if (v - bg[u] > 4) up = true;
    }
    if (up) { rewind(m); unit(m); if (nHot < 4096) hot[nHot++] = m; nUp++; continue; }
    for (let j = 0; j < nb; j++) block(c[1], null);
    for (let j = 0; j < nb; j++) block(c[2], null);
  }
  // 大面积变亮（准备期结束）：下一帧整体重取背景。
  flood = nUp > nm * 0.2;
  // 弹丸可能压在单元边界上：把突变单元的邻近单元也补解。
  for (let h = 0; h < nHot; h++) {
    const m = hot[h], mx = m % mw, my = (m / mw) | 0;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      const x = mx + dx, y = my + dy;
      if (x < 0 || y < 0 || x >= mw || y >= J.mh) continue;
      const n = y * mw + x;
      if (got[n] !== fno) { rewind(n); unit(n); }
    }
  }
}
function mark(x0, y0, x1, y1) {
  const a = Math.max(0, Math.floor(x0 / J.uw)), b = Math.min(J.mw - 1, Math.floor(x1 / J.uw)), c = Math.max(0, Math.floor(y0 / J.uh)), d = Math.min(J.mh - 1, Math.floor(y1 / J.uh));
  for (let y = c; y <= d; y++) if (b >= a) need.fill(1, y * J.mw + a, y * J.mw + b + 1);
}

// ───────────────────────── 感知 ─────────────────────────
// 输出统一为「场地坐标」：x∈[0,960]，y∈[0,600]（已去掉顶部 HUD，并按图宽归一）。
const CAP = 4096;
const bX = new Int16Array(CAP), bY = new Int16Array(CAP), rX = new Int16Array(CAP), rY = new Int16Array(CAP);
const wX = new Int16Array(CAP), wY = new Int16Array(CAP);
let nB = 0, nR = 0, nW = 0;
const TAU = Math.PI * 2, HALF = Math.PI / 2;
const wrap = a => { a %= TAU; return a > Math.PI ? a - TAU : a < -Math.PI ? a + TAU : a; };
const clamp = (v, lo, hi) => v < lo ? lo : v > hi ? hi : v;

// 扫描本帧已解出的单元，按颜色把像素分到：蓝装甲 / 红装甲 / 高亮白（弹芯）。
function scan(y0) {
  nB = nR = nW = 0;
  const d = F, w = J.w, h = J.h, mw = J.mw;
  for (let k = 0; k < nDn; k++) {
    const m = dn[k], x0 = (m % mw) * J.uw, my = ((m / mw) | 0) * J.uh, xe = Math.min(w, x0 + J.uw), ye = Math.min(h, my + J.uh);
    for (let y = my < y0 ? y0 : my; y < ye; y++) {
      let i = (y * w + x0) * 3;
      for (let x = x0; x < xe; x++, i += 3) {
        const r = d[i];
        if (r > 200) {
          const g = d[i + 1], b = d[i + 2];
          if (g < 120) { if (b < 135 && nR < CAP) { rX[nR] = x; rY[nR++] = y; } }
          else if (r > 222 && g > 212 && b > 206 && nW < CAP) { wX[nW] = x; wY[nW++] = y; }
        } else if (r < 90 && d[i + 2] > 185 && d[i + 1] > 135 && nB < CAP) { bX[nB] = x; bY[nB++] = y; }
      }
    }
  }
}

// 由一种颜色的装甲像素求车体中心与装甲相位（mod 90°）。px/py 为上一帧像素位置先验（NaN 表示没有）。
const plateSX = new Float64Array(4), plateSY = new Float64Array(4), plateN = new Int32Array(4);
const grid = new Uint16Array(32 * 24);
function locate(X, Y, n, px, py, s, out) {
  out.ok = false;
  const few = 24 * s * s;                // 像素数门槛随画面面积缩放
  if (n < few * 0.8) return out;
  let cx = NaN, cy = NaN, m = 0, sx = 0, sy = 0;
  const near = 50 * s, near2 = near * near;
  if (px === px) {
    for (let i = 0; i < n; i++) { const dx = X[i] - px, dy = Y[i] - py; if (dx * dx + dy * dy < near2) { sx += X[i]; sy += Y[i]; m++; } }
    if (m >= few) { cx = sx / m; cy = sy / m; }
  }
  if (cx !== cx) {
    // 全局搜索：48px 粗网格投票，取 3×3 邻域像素最多处。
    const cell = 48 * s, gw = 32, gh = 24;
    grid.fill(0);
    for (let i = 0; i < n; i++) grid[Math.min(gh - 1, (Y[i] / cell) | 0) * gw + Math.min(gw - 1, (X[i] / cell) | 0)]++;
    let best = 0, bi = 0;
    for (let gy = 0; gy < gh; gy++) for (let gx = 0; gx < gw; gx++) {
      let c = 0;
      for (let v = gy > 0 ? gy - 1 : 0; v <= gy + 1 && v < gh; v++) for (let u = gx > 0 ? gx - 1 : 0; u <= gx + 1 && u < gw; u++) c += grid[v * gw + u];
      if (c > best) { best = c; bi = gy * gw + gx; }
    }
    if (best < few) return out;
    const gx = (bi % gw + 0.5) * cell, gy = (((bi / gw) | 0) + 0.5) * cell, lim = cell * 1.6;
    sx = sy = m = 0;
    for (let i = 0; i < n; i++) if (Math.abs(X[i] - gx) < lim && Math.abs(Y[i] - gy) < lim) { sx += X[i]; sy += Y[i]; m++; }
    cx = sx / m; cy = sy / m;
    sx = sy = m = 0;
    for (let i = 0; i < n; i++) { const dx = X[i] - cx, dy = Y[i] - cy; if (dx * dx + dy * dy < near2) { sx += X[i]; sy += Y[i]; m++; } }
    if (m < few) return out;
    cx = sx / m; cy = sy / m;
  }
  const lo2 = (17 * s) ** 2, hi2 = (35 * s) ** 2, PRs = 26 * s;
  let th = 0, plates = 0;
  for (let it = 0; it < 4; it++) {
    let s4 = 0, c4 = 0;
    for (let i = 0; i < n; i++) {
      const dx = X[i] - cx, dy = Y[i] - cy, r2 = dx * dx + dy * dy;
      if (r2 < lo2 || r2 > hi2) continue;
      // (dx+i·dy)^4 的辐角 = 4φ
      const a = dx * dx - dy * dy, b = 2 * dx * dy, q = r2 * r2;
      c4 += (a * a - b * b) / q; s4 += 2 * a * b / q;
    }
    th = Math.atan2(s4, c4) / 4;
    plateSX.fill(0); plateSY.fill(0); plateN.fill(0);
    for (let i = 0; i < n; i++) {
      const dx = X[i] - cx, dy = Y[i] - cy, r2 = dx * dx + dy * dy;
      if (r2 < lo2 || r2 > hi2) continue;
      let k = Math.round((Math.atan2(dy, dx) - th) / HALF); k = ((k % 4) + 4) % 4;
      plateSX[k] += X[i]; plateSY[k] += Y[i]; plateN[k]++;
    }
    let ax = 0, ay = 0; plates = 0;
    const minPix = 14 * s * s;
    for (let k = 0; k < 4; k++) {
      if (plateN[k] < minPix) continue;
      const a = th + k * HALF;
      ax += plateSX[k] / plateN[k] - PRs * Math.cos(a); ay += plateSY[k] / plateN[k] - PRs * Math.sin(a); plates++;
    }
    if (!plates) return out;
    cx = ax / plates; cy = ay / plates;
  }
  out.ok = true; out.px = cx; out.py = cy; out.a = th; out.plates = plates;
  return out;
}

// 炮管朝向：车体外环 r∈[30,37] 内高亮像素按角度分箱，取最集中的方向（抗角标、弹丸、近身干扰）。
const aN = new Uint16Array(72), aX = new Float32Array(72), aY = new Float32Array(72);
function barrel(d, w, h, cx, cy, s, dim) {
  const tr = dim ? 188 : 216, tg = dim ? 192 : 220, tb = dim ? 199 : 226;
  const R = 38 * s, lo2 = (30 * s) ** 2, hi2 = (37.2 * s) ** 2;
  const x0 = Math.max(0, Math.ceil(cx - R)), x1 = Math.min(w - 1, Math.floor(cx + R));
  const y0 = Math.max(0, Math.ceil(cy - R)), y1 = Math.min(h - 1, Math.floor(cy + R));
  aN.fill(0); aX.fill(0); aY.fill(0);
  for (let y = y0; y <= y1; y++) {
    const dy = y - cy;
    for (let x = x0; x <= x1; x++) {
      const dx = x - cx, r2 = dx * dx + dy * dy;
      if (r2 < lo2 || r2 > hi2) continue;
      const i = (y * w + x) * 3;
      if (d[i] > tr && d[i + 1] > tg && d[i + 2] > tb) {
        const k = Math.min(71, ((Math.atan2(dy, dx) + Math.PI) * (36 / Math.PI)) | 0);
        aN[k]++; aX[k] += dx; aY[k] += dy;
      }
    }
  }
  let best = 0, bk = 0;
  for (let k = 0; k < 72; k++) { const c = aN[(k + 71) % 72] + aN[k] + aN[(k + 1) % 72]; if (c > best) { best = c; bk = k; } }
  if (best < 5 * s * s) return NaN;
  let sx = 0, sy = 0;
  for (let j = -2; j <= 2; j++) { const k = (bk + j + 72) % 72; sx += aX[k]; sy += aY[k]; }
  return Math.atan2(sy, sx);
}

// HUD：血条比例（0..1）与热量条比例（0..1）。
function hudBar(d, w, s, x0, y, len, test) {
  const row = Math.round((y + 0.5) * s - 0.5), a = Math.round(x0 * s), n = Math.round(len * s);
  let last = -1;
  for (let k = 0; k < n; k++) { const i = (row * w + a + k) * 3; if (test(d[i], d[i + 1], d[i + 2])) last = k; }
  return (last + 1) / n;
}
const isRedBar = (r, g, b) => r > 180 && g < 130 && b < 150;
const isBlueBar = (r, g, b) => b > 180 && r < 120 && g > 110;
const isHeatBar = (r, g, b) => r > 150 && g > 70 && b < 150;

// 弹芯聚类：把高亮白像素并成小簇，返回场地内候选弹丸（像素坐标）。
const MAXC = 96;
const cSX = new Float64Array(MAXC), cSY = new Float64Array(MAXC), cN = new Int32Array(MAXC);
function clusterWhite(s) {
  let nc = 0;
  const lim2 = (5.5 * s) ** 2;
  for (let i = 0; i < nW; i++) {
    const x = wX[i], y = wY[i];
    let hit = -1;
    for (let c = nc - 1; c >= 0; c--) { const dx = cSX[c] / cN[c] - x, dy = cSY[c] / cN[c] - y; if (dx * dx + dy * dy < lim2) { hit = c; break; } }
    if (hit < 0) { if (nc >= MAXC) continue; hit = nc++; cSX[hit] = cSY[hit] = 0; cN[hit] = 0; }
    cSX[hit] += x; cSY[hit] += y; cN[hit]++;
  }
  return nc;
}

const lum = new Float64Array(12);
const obsBlue = { ok: false, px: NaN, py: NaN, a: 0, plates: 0 }, obsRed = { ok: false, px: NaN, py: NaN, a: 0, plates: 0 };
const SPOTS = [[120, 185], [400, 185], [840, 185], [120, 310], [400, 310], [840, 310], [120, 425], [400, 425], [840, 425], [120, 545], [400, 545], [840, 545]];
// 感知一帧。prior 为上一帧结果（null 则整帧搜索）；slack 为两车自上一帧以来可能移动的像素余量。
function perceive(o, prior, slack) {
  b64bytes(o.image.base64); parseHead();
  const s = J.w / 960, pb = prior && prior.bots.blue, pr = prior && prior.bots.red, all = !pb || !pr;
  if (!all) {
    need.fill(0);
    const R = (44 + slack) * s, row = y => Math.round((y + 0.5) * s - 0.5);
    mark(pb.px - R, pb.py - R, pb.px + R, pb.py + R); mark(pr.px - R, pr.py - R, pr.px + R, pr.py + R);
    for (const [x, y, len] of [[26, 43, 308], [626, 43, 308], [237, 62, 97], [837, 62, 97]]) mark(Math.round(x * s), row(y), Math.round(x * s) + Math.round(len * s), row(y));
    for (const [x, y] of SPOTS) { const X = row(x), Y = row(y); mark(X - 1, Y - 1, X + 1, Y + 1); }
  }
  decode(all);
  return analyze(prior);
}
// 备用路径：整帧 RGB 已由宿主解码（非 4:4:4 基线 JPEG 时使用）。
function perceiveRGB(img, prior) {
  const keep = F;
  J.w = img.width; J.h = img.height; J.H = J.V = J.nb = 1; J.uw = J.uh = 8; J.mw = (J.w + 7) >> 3; J.mh = (J.h + 7) >> 3;
  J.nm = J.mw * J.mh; J.head = null; mst = null;         // 回到局部解码时重新解析头并重建各缓冲
  if (!dn || dn.length < J.nm) { dn = new Int32Array(J.nm); got = new Int32Array(J.nm); }
  F = img.data; nDn = J.nm; fno++;
  for (let m = 0; m < nDn; m++) dn[m] = m;
  try { return analyze(prior); } finally { F = keep; }
}
function analyze(prior) {
  const d = F, w = J.w, h = J.h, s = w / 960, y0 = Math.round(80 * s);
  scan(y0);
  const fx = x => (x + 0.5) / s - 0.5, fy = y => (y + 0.5) / s - 80.5;
  const res = { s, bots: { blue: null, red: null }, shells: [], hp: { red: 0, blue: 0 }, heat: { red: 0, blue: 0 }, countdown: false };
  // 准备阶段全场罩一层暗色：在 12 个空地板点取亮度中位数判断。
  for (let k = 0; k < 12; k++) {
    const X = Math.round((SPOTS[k][0] + 0.5) * s - 0.5), Y = Math.round((SPOTS[k][1] + 0.5) * s - 0.5);
    let sum = 0;
    for (let v = -1; v <= 1; v++) for (let u = -1; u <= 1; u++) { const i = ((Y + v) * w + X + u) * 3; sum += d[i] + d[i + 1] + d[i + 2]; }
    lum[k] = sum / 9;
  }
  lum.sort();
  res.countdown = (lum[5] + lum[6]) / 2 < 177;
  const pb = prior && prior.bots.blue, pr = prior && prior.bots.red;
  locate(bX, bY, nB, pb ? pb.px : NaN, pb ? pb.py : NaN, s, obsBlue);
  locate(rX, rY, nR, pr ? pr.px : NaN, pr ? pr.py : NaN, s, obsRed);
  for (const [side, o] of [['blue', obsBlue], ['red', obsRed]]) {
    if (!o.ok) continue;
    res.bots[side] = { x: fx(o.px), y: fy(o.py), a: o.a, plates: o.plates, px: o.px, py: o.py, turret: barrel(d, w, h, o.px, o.py, s, res.countdown) };
  }
  res.hp.red = hudBar(d, w, s, 26, 43, 308, isRedBar); res.hp.blue = hudBar(d, w, s, 626, 43, 308, isBlueBar);
  res.heat.red = hudBar(d, w, s, 237, 62, 97, isHeatBar); res.heat.blue = hudBar(d, w, s, 837, 62, 97, isHeatBar);
  if (!res.countdown) {
    const nc = clusterWhite(s), keep2 = (60 * s) ** 2;
    for (let c = 0; c < nc; c++) {
      if (cN[c] < 3 * s * s || cN[c] > 34 * s * s) continue;
      const x = cSX[c] / cN[c], y = cSY[c] / cN[c];
      let skip = false;
      for (const o of [obsBlue, obsRed]) if (o.ok && (x - o.px) ** 2 + (y - o.py) ** 2 < keep2) skip = true;
      if (skip) continue;
      // 弹丸外圈与拖尾带发射方颜色：统计周围非白像素的红蓝差。
      let tone = 0, area = 0;
      const R = Math.max(1, Math.round(4 * s)), xi = Math.round(x), yi = Math.round(y);
      for (let v = -R; v <= R; v++) for (let u = -R; u <= R; u++) {
        const X = xi + u, Y = yi + v;
        if (X < 0 || Y < y0 || X >= w || Y >= h) continue;
        area++;
        const i = (Y * w + X) * 3;
        if (d[i] > 222 && d[i + 1] > 212) continue;
        tone += d[i] - d[i + 2];
      }
      // 阈值按窗口像素数折算，画面缩放后仍然成立。
      res.shells.push({ x: fx(x), y: fy(y), n: cN[c], owner: tone > -24.7 * area ? 'red' : 'blue' });
    }
  }
  return res;
}

// ───────────────────────── 弹道几何 ─────────────────────────
// 弹丸相对车体的运动步进：返回 1=打中装甲，-1=被车体挡下，0=落空。
// (bx,by) 弹丸相对车心位置；(wx,wy) 相对速度 px/s；ph 此刻装甲相位；om 车体角速度 rad/s。
// 车体几何：装甲心距 26、板 12×4、车体半径 23、弹丸半径 2。
function shellFate(bx, by, wx, wy, ph, om) {
  const sp = Math.hypot(wx, wy), ux = wx / sp, uy = wy / sp;
  const tca = -(bx * ux + by * uy), d2 = bx * bx + by * by - tca * tca;
  if (d2 > 940) return 0;
  const half = Math.sqrt(1089 - d2), s1 = tca + half;
  if (s1 < 0) return 0;
  // 从弹丸进入车体外接圆处开始，每 0.5px 步进一次；装甲相位随步进同步转动。
  let s = Math.max(0, tca - half);
  const a0 = ph + om * s / sp, da = om * 0.5 / sp, dc = Math.cos(da), dsn = Math.sin(da);
  let c = Math.cos(a0), sn = Math.sin(a0);
  for (; s <= s1; s += 0.5) {
    const x = bx + ux * s, y = by + uy * s, r2 = x * x + y * y;
    if (r2 <= 942) {
      let p = Math.abs(x * c + y * sn), q = Math.abs(-x * sn + y * c);
      if (q > p) { const k = p; p = q; q = k; }
      const ra = Math.abs(p - 26) - 2, ta = q - 6;
      if ((ra > 0 ? (ta > 0 ? ra * ra + ta * ta : ra * ra) : (ta > 0 ? ta * ta : 0)) <= 4) return 1;
      if (r2 <= 625) return -1;
    }
    const k = c * dc - sn * dsn; sn = sn * dc + c * dsn; c = k;
  }
  return 0;
}
//@@MAIN 以上是不依赖 lab 的纯函数（可单独拿出来用带真值的画面做离线测试），以下开始读写 lab。
// ───────────────────────── 状态估计 ─────────────────────────
const ME = lab.side, FOE = ME === 'red' ? 'blue' : 'red';
const now = () => performance.now();
const SLOT = 1000 / 30, FW = 960, FH = 600, AR = 34;
const BV = 1000, MUZ = 42;            // 弹速（px/s）与出膛点到车心距离
const ENC = 9;                        // 画面从采样到可被取到的最小延迟（ms，本机实测）
const LEAD = 8;                       // 指令在控制边界生效之后，到弹丸出膛还要多久（ms，本机实测）
const STEP = 1000 / 60;               // 控制周期
let vMax = 184, wMax = 8;             // 我方满速（px/s）与满转速（rad/s）：默认功率下的值，运行中按实际位移重新标定
const DEBUG = false;                  // 置 true 时每 2 秒往本席日志写一行运行统计
const POLL = true;                    // 在控制边界之间主动取新画面
const rnd = Math.random;
const wrap90 = a => { a %= HALF; return a > HALF / 2 ? a - HALF : a < -HALF / 2 ? a + HALF : a; };

const est = {
  frame: -1, slot: 0, off: Infinity, t: 0, prior: null,
  me: { x: ME === 'red' ? 210 : 750, y: 300, a: 0 },
  fh: [], k: null, omJit: 1, turnT: 0, arr: 0, arrPrev: 0, heatPrev: 0,
  countdown: true, hp: { me: 1, foe: 1 }, heat: 0, foeHeat: 0,
  shells: [],
};
const cmd = { vx: 0, vy: 0, om: 0 };
let turEst = NaN, turT = 0, aimDir = 0, lastFire = -1e9, lastD = 26, bndT = 0;
let fireGap = 56, reqN = 0, realN = 0, heat0 = 0, heatT = 0, heatM = 0, heatMT = 0;
let vSumD = 0, vSumT = 0, vLast = 0, mePrev = null, impureT = 0, lastMX = 0, lastMY = 0;
const shots = [];
const wander = { ang: rnd() * TAU, until: 0 };
const dbg = { frames: 0, fires: 0, loops: 0, lost: 0, spin: 0, risk: 0, decode: 0, pSum: 0, pN: 0, raids: 0, sh: [], poll: 0, fresh: 0 };

// 功率分配：平移与旋转共享上限。
function motion(mx, my, spin) {
  const q = Math.max(1, Math.hypot(mx, my, spin));
  return { vx: mx / q * vMax, vy: my / q * vMax, om: spin / q * wMax };
}

// 给新画面估计「内容时刻」：帧号等间隔，偏置取到达时刻的下包络。
function stamp(frameId, arrive) {
  est.slot += est.frame < 0 ? 0 : frameId - est.frame; est.frame = frameId;
  let e = arrive - est.slot * SLOT;
  if (est.off !== Infinity && e - est.off > 50) { const k = Math.round((e - est.off - 14) / SLOT); est.slot += k; e -= k * SLOT; }
  est.off = Math.min(est.off + 0.02, e);
  return est.slot * SLOT + est.off - ENC;
}

function foeAt(t) {
  const h = est.fh;
  for (let i = h.length - 1; i > 0; i--) if (h[i - 1].t <= t) {
    const a = h[i - 1], b = h[i], f = clamp((t - a.t) / (b.t - a.t || 1), 0, 1);
    return { x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f };
  }
  return h[0];
}

// 对手运动学：最近两段位移求速度；两段一致时合并降噪。
function foeKin() {
  const h = est.fh, n = h.length, L = h[n - 1];
  const k = { t: L.t, x: L.x, y: L.y, a: L.a, tur: L.tur, turOm: 0, vx: 0, vy: 0, om: 0, jerk: 999 };
  if (n < 2) return k;
  const P = h[n - 2], d1 = (L.t - P.t) / 1000;
  k.vx = (L.x - P.x) / d1; k.vy = (L.y - P.y) / d1; k.om = wrap90(L.a - P.a) / d1;
  if (L.tur === L.tur && P.tur === P.tur) k.turOm = wrap(L.tur - P.tur) / d1;
  if (n < 3) return k;
  const Q = h[n - 3], d2 = (P.t - Q.t) / 1000, ux = (P.x - Q.x) / d2, uy = (P.y - Q.y) / d2;
  k.jerk = Math.hypot(k.vx - ux, k.vy - uy);
  if (k.jerk < 45) { const d = d1 + d2; k.vx = (L.x - Q.x) / d; k.vy = (L.y - Q.y) / d; }
  const om2 = wrap90(P.a - Q.a) / d2;
  est.omJit += 0.05 * (Math.abs(k.om - om2) - est.omJit);
  if (Math.abs(k.om - om2) < 1.2) k.om = (k.om + om2) / 2;
  return k;
}

// 对手位移的经验分布：按预测时域分桶，保存「当时速度坐标系下，T 秒后的实际位移」样本。
// 不假设匀速或高斯：变向型对手的位移是多峰的，直接用样本找最可能的落点。
const TB = [0.06, 0.1, 0.14, 0.18, 0.22, 0.27, 0.32, 0.38, 0.45, 0.53, 0.62, 0.74], NS = 96;
const samp = TB.map(() => ({ par: new Float32Array(NS), per: new Float32Array(NS), ts: new Float32Array(NS), mv: new Uint8Array(NS), n: 0 }));
function learn() {
  const h = est.fh, n = h.length, L = h[n - 1];
  let i = n - 2;
  for (let b = 0; b < TB.length && i >= 0; b++) {
    const want = L.t - TB[b] * 1000;
    while (i > 0 && h[i].t > want) i--;
    let P = h[i];
    if (i + 1 < n - 1 && Math.abs(h[i + 1].t - want) < Math.abs(P.t - want)) P = h[i + 1];
    const T = (L.t - P.t) / 1000;
    if (P.vx === undefined || Math.abs(T - TB[b]) > 0.03) continue;
    const sc = TB[b] / T, dx = (L.x - P.x) * sc, dy = (L.y - P.y) * sc, sp = Math.hypot(P.vx, P.vy), S = samp[b], j = S.n++ % NS;
    if (sp > 25) { const ex = P.vx / sp, ey = P.vy / sp; S.par[j] = dx * ex + dy * ey; S.per[j] = -dx * ey + dy * ex; S.mv[j] = 1; }
    else { S.par[j] = dx; S.per[j] = dy; S.mv[j] = 0; }
    S.ts[j] = P.ts;
  }
}

function updateShells(list, t) {
  for (const s of est.shells) s.seen = false;
  for (const d of list) {
    if (d.owner !== FOE) continue;
    let m = null, bd = 1e9;
    for (const s of est.shells) {
      if (s.seen) continue;
      const el = (t - s.t) / 1000 * BV, ex = d.x - s.x - s.ux * el, ey = d.y - s.y - s.uy * el;
      const along = ex * s.ux + ey * s.uy, across = Math.abs(-ex * s.uy + ey * s.ux);
      if (across < 7 + (s.n < 2 ? 10 : 0) && Math.abs(along) < 28) { const e = across * 3 + Math.abs(along); if (e < bd) { bd = e; m = s; } }
    }
    if (m) {
      const bx = d.x - m.x0, by = d.y - m.y0, bl = Math.hypot(bx, by);
      if (bl > 18) { m.ux = bx / bl; m.uy = by / bl; }
      m.x = d.x; m.y = d.y; m.t = t; m.seen = true; m.n++;
    } else if (est.fh.length) {
      // 新弹丸：它必然来自对手炮口，方向取「出膛时刻的对手位置 → 弹丸」。
      const L = est.fh[est.fh.length - 1];
      const p = foeAt(t - (Math.hypot(d.x - L.x, d.y - L.y) - MUZ)) || L;
      const ux = d.x - p.x, uy = d.y - p.y, l = Math.hypot(ux, uy) || 1;
      est.shells.push({ x: d.x, y: d.y, x0: d.x, y0: d.y, t, ux: ux / l, uy: uy / l, n: 1, seen: true });
    }
  }
  est.shells = est.shells.filter(s => {
    if (s.seen) return true;
    const el = (t - s.t) / 1000 * BV, x = s.x + s.ux * el, y = s.y + s.uy * el;
    return t - s.t < 120 && x > 0 && x < FW && y > 0 && y < FH;
  });
}

function ingest(o, arrive) {
  if (o.frameId === est.frame) return false;
  const t0 = now();
  let p;
  try { p = perceive(o, est.prior, 8 + 0.5 * Math.min(120, arrive - est.arr)); } catch (e) { dbg.err = 'fallback ' + String(e).slice(0, 40); p = perceiveRGB(lab.pixels(o), est.prior); }
  est.arrPrev = est.arr; est.arr = arrive; est.heatPrev = est.heat;
  dbg.decode += now() - t0;
  // 内容时刻必须递增，否则帧间速度会算出无穷大。
  const t = Math.max(stamp(o.frameId, arrive), est.t + 8);
  let mine = p.bots[ME];
  const foe = p.bots[FOE];
  // 残缺测量（装甲被遮挡）且与上一帧跳变过大时丢弃，己方和对手同样处理。
  if (mine && mePrev && mine.plates < 3 && Math.hypot(mine.x - mePrev.x, mine.y - mePrev.y) > 4 + 0.6 * (t - mePrev.t)) { p.bots[ME] = est.prior && est.prior.bots[ME]; mine = null; dbg.lost++; }
  if (mine) { est.me.x = mine.x; est.me.y = mine.y; est.me.a = mine.a; if (mine.turret === mine.turret && !(Math.abs(wrap(mine.turret - turEst)) < 0.6)) { turEst = mine.turret; turT = arrive; } }
  if (foe) {
    const L = est.fh[est.fh.length - 1];
    if (L && foe.plates < 3 && Math.hypot(foe.x - L.x, foe.y - L.y) > 4 + 0.6 * (t - L.t)) { p.bots[FOE] = est.prior && est.prior.bots[FOE]; dbg.lost++; }
    else {
      const rec = { t, x: foe.x, y: foe.y, a: foe.a, tur: foe.turret, vx: undefined, vy: undefined, ts: 0 };
      est.fh.push(rec); if (est.fh.length > 40) est.fh.shift();
      est.k = foeKin(); if (est.k.jerk > 50 && est.k.jerk < 900) est.turnT = t; est.k.ts = rec.ts = Math.min(2000, t - est.turnT); rec.vx = est.k.vx; rec.vy = est.k.vy;
      if (!p.countdown) learn();
    }
  } else dbg.lost++;
  est.prior = p; est.t = t; est.countdown = p.countdown;
  est.hp.me = p.hp[ME]; est.hp.foe = p.hp[FOE]; est.heat = p.heat[ME] * 100; est.foeHeat = p.heat[FOE] * 100;
  if (!p.countdown) updateShells(p.shells, t); else est.shells.length = 0;
  if (!p.countdown) {
    // 实际出膛数（由热量条的增量推算）明显少于请求数：房间射速比预想的低，拉长请求间隔。
    const dh = est.heat - heat0 + 0.02 * (t - heatT);
    if (dh > 5) realN += Math.round(dh / 10);
    if (reqN >= 12) { if (realN < reqN * 0.6) fireGap = Math.min(1000, fireGap * 1.6); reqN = realN = 0; }
    // 自身满速标定（房间功率可调）。只在「指令是方向不变的纯平移、没贴墙、没顶着对手」时累计，
    // 用累计位移除以累计到达间隔：单帧的时间抖动和掉帧都不会带偏。两次独立估计一致、且与现值差一成半以上才改。
    if (mine && mePrev && arrive - mePrev.arr > 15 && arrive - mePrev.arr < 120 && mePrev.arr > impureT + 130 && curD > 60
      && mine.x > AR + 4 && mine.x < FW - AR - 4 && mine.y > AR + 4 && mine.y < FH - AR - 4) {
      vSumD += Math.hypot(mine.x - mePrev.x, mine.y - mePrev.y); vSumT += arrive - mePrev.arr;
      if (vSumT >= 1500) {
        const v = vSumD / vSumT * 1000;
        if (v > 20 && Math.abs(v - vLast) < 0.08 * v && Math.abs(v - vMax) > 0.15 * vMax) { vMax = v; wMax = 8 * v / 184; }
        vLast = v; vSumD = vSumT = 0;
      }
    }
  }
  heat0 = est.heat; heatT = t;
  mePrev = mine ? { x: mine.x, y: mine.y, t, arr: arrive } : null;
  dbg.frames++;
  return true;
}

// 当前热量的上界估计。两个上界取小：
//  ① 模型：每次请求都当作出膛（+10），按墙钟冷却；请求被宿主丢弃时它偏高，不会偏低。
//  ② HUD：读数 + 该画面到达前 250ms 以来的全部请求 − 到达后的冷却；画面延迟再大也不会漏算。
//     取最近两帧里较高的一个，单帧读数异常不会把估计拉低。
function hudBound(heat, arr, t) {
  let h = heat;
  for (let i = shots.length - 1; i >= 0 && shots[i] > arr - 250; i--) h += 10;
  return Math.max(0, h - 0.02 * Math.max(0, t - arr));
}
function heatNow(t) {
  const m = Math.max(0, heatM - 0.02 * (t - heatMT)), h = Math.max(hudBound(est.heat, est.arr, t), hudBound(est.heatPrev, est.arrPrev, t));
  heatM = Math.min(m, h); heatMT = t;
  return heatM;
}

// ───────────────────────── 瞄准 ─────────────────────────
// hx：弹道相对实际车心横向偏移 (i-16)*2 时是否命中；hist：对手未来横向位移的经验分布（2px 一格）。
const hx = new Float32Array(33), hist = new Float32Array(141), hsm = new Float32Array(141);

// 近距离命中表。弹丸从炮口出发，而炮口离车心有 42px：两车靠近后，出膛点可能已经越过对手朝向我方的
// 装甲板、落在车体里（出膛即被挡），也可能正好压在某块板上（出膛即命中）。远处那套「整条弹道平移」的
// 算法在这里不成立，所以按「弹道横向偏移 × 装甲相对弹道的相位 × 出膛点在垂足前多远」预先算好结局。
const TO = 32, TP = 45, S_LO = -14, S_HI = 34, NS0 = S_HI - S_LO + 1, NEAR_D = 150;
const NEAR = new Uint8Array((2 * TO + 1) * TP * NS0);
for (let o = -TO; o <= TO; o++) for (let p = 0; p < TP; p++) for (let s = S_LO; s <= S_HI; s++)
  NEAR[((o + TO) * TP + p) * NS0 + s - S_LO] = shellFate(-s, o, BV, 0, (p + 0.5) * HALF / TP, 0) === 1 ? 1 : 0;
const phIdx = a => { a %= HALF; if (a < 0) a += HALF; const i = (a * (TP / HALF)) | 0; return (i < TP ? i : TP - 1) * NS0; };
const pOff = new Float32Array(2 * TO + 1), thOff = new Float32Array(2 * TO + 1), sX = new Float32Array(NS + 8), sY = new Float32Array(NS + 8), sW = new Float32Array(NS + 8);
const PRI = [[0, 0, 0.4], [1, 0, 0.15], [-1, 0, 0.15], [0, 1, 0.15], [0, -1, 0.15]];
let lastOff = 99;
// 以炮塔角为搜索变量：对每个候选方向，按对手位置的经验分布逐个样本查表，取命中概率最高的方向。
function aimNear(k, mx, my, D, ux, uy, tLag, S, N, sc0, T0, mv, ex, ey) {
  // 弹丸飞到装甲圈的时间（贴身时为零）。
  const tof = Math.max(0, D - MUZ - 26) / BV, T = Math.max(0.02, tLag + tof), sc = sc0 * T / T0;
  let n = 0, ws = 0, mxT = 0, myT = 0;
  for (let j = 0; j < N; j++) {
    if (S.mv[j] !== mv) continue;
    const dt = (S.ts[j] - k.ts) / 90, w = 1 / (1 + dt * dt);
    sX[n] = k.x + (S.par[j] * ex - S.per[j] * ey) * sc; sY[n] = k.y + (S.par[j] * ey + S.per[j] * ex) * sc; sW[n++] = w; ws += w;
  }
  if (ws < 10) {
    // 样本不足时混入先验：匀速外推为中心，四周各放一个点。
    const sg = 3 + 22 * T, add = 10 - ws;
    for (const [a, b, w] of PRI) { sX[n] = k.x + k.vx * T + a * sg; sY[n] = k.y + k.vy * T + b * sg; sW[n++] = add * w; }
    ws = 10;
  }
  for (let i = 0; i < n; i++) {
    let x = clamp(sX[i], AR, FW - AR), y = clamp(sY[i], AR, FH - AR);
    // 两车不会重叠：落进我方车体范围的样本沿连线推出去。
    const ox = x - mx, oy = y - my, od = Math.hypot(ox, oy);
    if (od < 52 && od > 1e-6) { x = mx + ox / od * 52; y = my + oy / od * 52; }
    sX[i] = x; sY[i] = y; mxT += x * sW[i]; myT += y * sW[i];
  }
  mxT /= ws; myT /= ws;
  const base = Math.atan2(uy, ux), sig = 0.05 + est.omJit * T, blind = sig > 0.35, phC = k.a + k.om * T;
  for (let o = -TO; o <= TO; o++) {
    const th = base + Math.asin(clamp(o / D, -0.95, 0.95)), c = Math.cos(th), s = Math.sin(th);
    thOff[o + TO] = th;
    const Mx = mx + MUZ * c, My = my + MUZ * s, i0 = phIdx(phC - th), i1 = phIdx(phC + sig - th), i2 = phIdx(phC - sig - th);
    let p = 0;
    for (let i = 0; i < n; i++) {
      const rx = Mx - sX[i], ry = My - sY[i], off = Math.round(ry * c - rx * s);
      let s0 = Math.round(-(rx * c + ry * s));
      if (off < -TO || off > TO || s0 < S_LO) continue;
      if (s0 > S_HI) s0 = S_HI;
      const row = (off + TO) * TP * NS0 + s0 - S_LO;
      if (blind) { let h = 0; for (let q = 0; q < TP; q += 5) h += NEAR[row + q * NS0]; p += sW[i] * h / 9; }
      else p += sW[i] * (0.5 * NEAR[row + i0] + 0.25 * NEAR[row + i1] + 0.25 * NEAR[row + i2]);
    }
    pOff[o + TO] = p / ws;
  }
  let best = -1, bo = 0, bp = 0;
  for (let o = -TO; o <= TO; o++) {
    // 偏好宽一些的命中窗口：瞄点和时序都有一两个像素的误差。
    const v = (2 * pOff[o + TO] + (o > -TO ? pOff[o + TO - 1] : 0) + (o < TO ? pOff[o + TO + 1] : 0)) / 4;
    // 炮塔每转 0.1 弧度要 10ms，这段时间里对手又挪了位置：转得远的方向要打折，免得在两侧切线之间来回甩。
    let sc = v - (turEst === turEst ? 0.3 * Math.max(0, Math.abs(wrap(thOff[o + TO] - turEst)) - 0.05) : 0);
    if (Math.abs(o - lastOff) < 2.5) sc += 0.015;
    if (sc > best) { best = sc; bo = o; bp = v; }
  }
  lastOff = bo; best = bp;
  // 瞄点放在弹道离对手最近的那一点：我方位置估计有偏差时，弹道仍然经过这一点。
  const th = base + Math.asin(clamp(bo / D, -0.95, 0.95)), c = Math.cos(th), s = Math.sin(th);
  const L = Math.max(30, (mxT - mx) * c + (myT - my) * s);
  return { qx: mx + c * L, qy: my + s * L, p: Math.min(1, best), d: bo, tof, D };
}

function bestAim(k, mx, my, tFire) {
  const dx = k.x - mx, dy = k.y - my, D = Math.hypot(dx, dy) || 1, ux = dx / D, uy = dy / D, nx = -uy, ny = ux;
  const tof = Math.max(0, D - MUZ) / BV, T = Math.max(0.02, (tFire - k.t) / 1000 + tof);
  let b = 0;
  while (b < TB.length - 1 && Math.abs(TB[b + 1] - T) < Math.abs(TB[b] - T)) b++;
  const S = samp[b], N = Math.min(S.n, NS), sc = T / TB[b];
  const sp = Math.hypot(k.vx, k.vy), mv = sp > 25 ? 1 : 0, ex = mv ? k.vx / sp : 1, ey = mv ? k.vy / sp : 0;
  if (D < NEAR_D) return aimNear(k, mx, my, D, ux, uy, (tFire - k.t) / 1000, S, N, sc, T, mv, ex, ey);
  hist.fill(0);
  let ws = 0;
  for (let j = 0; j < N; j++) {
    if (S.mv[j] !== mv) continue;
    // 距上次变向的时长相近的样本权重更大（周期性变向的对手由此可被预判）。
    const dt = (S.ts[j] - k.ts) / 90, w = 1 / (1 + dt * dt);
    const px = (S.par[j] * ex - S.per[j] * ey) * sc, py = (S.par[j] * ey + S.per[j] * ex) * sc;
    const lat = (clamp(k.x + px, AR, FW - AR) - k.x) * nx + (clamp(k.y + py, AR, FH - AR) - k.y) * ny;
    const q = Math.round(lat / 2) + 70;
    if (q >= 0 && q < 141) hist[q] += w;
    ws += w;
  }
  if (ws < 10) {
    // 样本不足时混入先验：按当前速度匀速外推，散布随时域增大。
    const c = (clamp(k.x + k.vx * T, AR, FW - AR) - k.x) * nx + (clamp(k.y + k.vy * T, AR, FH - AR) - k.y) * ny, sg = 4 + 22 * T, add = 10 - ws;
    let z = 0;
    for (let q = 0; q < 141; q++) { const e = ((q - 70) * 2 - c) / sg; hsm[q] = Math.exp(-0.5 * e * e); z += hsm[q]; }
    for (let q = 0; q < 141; q++) hist[q] += add * hsm[q] / z;
    ws = 10;
  }
  // 量测与时序抖动：轻微平滑。
  for (let q = 0; q < 141; q++) hsm[q] = ((q > 1 ? hist[q - 2] : 0) + 2 * (q > 0 ? hist[q - 1] : 0) + 3 * hist[q] + 2 * (q < 140 ? hist[q + 1] : 0) + (q < 139 ? hist[q + 2] : 0)) / (9 * ws);
  const wx = ux * BV - 0.5 * k.vx, wy = uy * BV - 0.5 * k.vy;
  // 弹丸从炮口出发：近距离时起点就是出膛点（可能已贴着甚至压进对手车体）。
  const t0 = Math.min(0.05, tof), ph0 = k.a + k.om * (T - t0), blind = 0.05 + est.omJit * T > 0.35;
  for (let i = 0; i < 33; i++) {
    const off = (i - 16) * 2, bx = nx * off - wx * t0, by = ny * off - wy * t0;
    if (blind) { let c = 0; for (let q = 0; q < 4; q++) if (shellFate(bx, by, wx, wy, ph0 + q * 0.3927, k.om) === 1) c++; hx[i] = c / 4; }
    else hx[i] = shellFate(bx, by, wx, wy, ph0, k.om) === 1 ? 1 : 0;
  }
  // 弹道横向落点 d（相对对手当前位置）：命中率 = Σ 位移分布 × 该相对偏移是否命中。
  let best = -1, bd = 0;
  for (let d = -100; d <= 100; d += 2) {
    let p = 0;
    const base = d / 2 + 70 + 16;
    for (let i = 0; i < 33; i++) { if (!hx[i]) continue; const q = base - i; if (q >= 0 && q < 141) p += hx[i] * hsm[q]; }
    if (Math.abs(d - lastD) < 2.5) p += 0.015;
    if (p > best) { best = p; bd = d; }
  }
  lastD = bd;
  return { qx: k.x + bd * nx, qy: k.y + bd * ny, p: Math.min(1, best), d: bd, tof, D };
}

function aimPoint(mx, my, qx, qy) {
  const dx = qx - mx, dy = qy - my;
  let k = 1;
  if (qx < 2) k = Math.min(k, (2 - mx) / dx);
  if (qx > FW - 2) k = Math.min(k, (FW - 2 - mx) / dx);
  if (qy < 2) k = Math.min(k, (2 - my) / dy);
  if (qy > FH - 2) k = Math.min(k, (FH - 2 - my) / dy);
  return [clamp((mx + dx * k) / FW, 0, 1), clamp((my + dy * k) / FH, 0, 1)];
}

// ───────────────────────── 战果统计与交战距离 ─────────────────────────
// 交战距离只有一个：顶住对手。
// 炮口离车心 42px，两车顶住时对手的炮口已经伸到我方朝向它的装甲板内侧，照常瞄准的弹出膛就被车体挡下；
// 我方打车体边缘外侧的切线（见 aimNear），那里不论装甲转到哪个相位都有板。
// 早先的版本会先站远试射、按战况在远和贴身之间切换。拿四十多个风格各异的假想敌比下来，
// 开局直接顶上去、不离开，反而是最稳的：凡是不在贴身的时间，都是在让瞄得准的对手白打。
const HUG = 53;
// 按开火距离分四段统计（只用于调试输出）。
const BK = D => D < 66 ? 0 : D < 150 ? 1 : D < 230 ? 2 : 3;
const tally = { shots: [0, 0, 0, 0], hits: [0, 0, 0, 0], pSum: [0, 0, 0, 0], took: [0, 0, 0, 0] };
const flying = [], pRing = new Float32Array(32), pSort = new Float32Array(32);
let pRN = 0, overN = 0;
// 单发伤害占满血的比例：按默认房间（20 发致命）起步，第一次有人掉血时改成实测值。
let hpMe0 = 1, hpFoe0 = 1, dmgUnit = 0.05, dmgSeen = false, curD = 540, dPref = 300, nearT = 0;
// 把对手掉血记到「预计此刻到达」的那发弹丸所属的距离段；我方掉血记到当时的距离段。
function credit() {
  const t = est.t, drop = hpFoe0 - est.hp.foe;
  if (drop > 0.004) {
    if (!dmgSeen || drop < dmgUnit * 0.9) { dmgUnit = drop; dmgSeen = true; }
    for (let n = Math.max(1, Math.round(drop / dmgUnit)); n > 0 && flying.length; n--) {
      let bi = 0, bd = 1e9;
      for (let i = 0; i < flying.length; i++) { const e = Math.abs(flying[i].ta - t); if (e < bd) { bd = e; bi = i; } }
      if (bd > 220) break;
      tally.hits[flying[bi].b]++; flying.splice(bi, 1);
    }
  }
  hpFoe0 = est.hp.foe;
  for (let i = flying.length - 1; i >= 0; i--) if (flying[i].ta < t - 160) flying.splice(i, 1);
  const lost = hpMe0 - est.hp.me;
  if (lost > 0.004) {
    // 单发伤害也可以从自己掉的血里学到。
    if (!dmgSeen || lost < dmgUnit * 0.9) { dmgUnit = lost; dmgSeen = true; }
    tally.took[BK(curD)] += Math.max(1, Math.round(lost / dmgUnit));
  }
  hpMe0 = est.hp.me;
}
// ───────────────────────── 机动与防御 ─────────────────────────
const NDIR = 24, AIMJIT = [[0, 0.5], [0.04, 0.25], [-0.04, 0.25]];
const PERT = [[0, 0, 0.4], [3.5, 0, 0.2], [-3.5, 0, 0.2], [0, 0.1, 0.1], [0, -0.1, 0.1]];
function evalMove(ux, uy, spin, me, k, th) {
  const m = motion(ux, uy, spin);
  const x1 = clamp(me.x + m.vx * 0.25, AR, FW - AR), y1 = clamp(me.y + m.vy * 0.25, AR, FH - AR);
  let c = -(ux * wander.c + uy * wander.s) + 0.25 * Math.abs(spin);
  const g = 75;
  if (x1 < AR + g) c += 4 * ((AR + g - x1) / g) ** 2;
  if (x1 > FW - AR - g) c += 4 * ((x1 - (FW - AR - g)) / g) ** 2;
  if (y1 < AR + g) c += 4 * ((AR + g - y1) / g) ** 2;
  if (y1 > FH - AR - g) c += 4 * ((y1 - (FH - AR - g)) / g) ** 2;
  const D = Math.hypot(k.x + k.vx * 0.2 - x1, k.y + k.vy * 0.2 - y1); c += dPref < 80 ? 0.08 * Math.abs(Math.max(52, D) - dPref) : 0.7 * ((D - dPref) / 100) ** 2;
  let risk = 0;
  // 贴墙时被截断的速度分量按 0 处理。
  const evx = (x1 - me.x) * 4, evy = (y1 - me.y) * 4;
  for (const b of th) {
    const wx = b.ux * BV - evx, wy = b.uy * BV - evy, rx = b.x - me.x, ry = b.y - me.y;
    for (const [e, da, w] of PERT) if (shellFate(rx - b.uy * e, ry + b.ux * e, wx, wy, me.a + da, m.om) === 1) risk += w * b.w;
  }
  return { c: c + risk * 80, risk, x: ux, y: uy, spin };
}
function chooseMove(t, me, k) {
  if (t > wander.until) {
    // 贴身时对手只能打车体两侧各约 5px 宽的切线窗口，横向挪几个像素就脱开：改成又快又不规则的左右横移。
    const tight = dPref < 80 && curD < 75;
    const base = Math.atan2(k.y - me.y, k.x - me.x), a = base + (rnd() < 0.5 ? 1 : -1) * (HALF + (rnd() - 0.5) * (tight ? 0.5 : 1.5));
    wander.c = Math.cos(a); wander.s = Math.sin(a); wander.until = t + (tight ? 22 - 50 * Math.log(1 - rnd() * 0.95) : 110 + rnd() * 260);
  }
  // 把来弹推进到此刻，筛出有可能够到我的。
  const th = [];
  for (const s of est.shells) {
    const el = (t - s.t) / 1000 * BV, x = s.x + s.ux * el, y = s.y + s.uy * el;
    const rx = me.x - x, ry = me.y - y, along = rx * s.ux + ry * s.uy, across = Math.abs(rx * s.uy - ry * s.ux);
    if (along < -34 || across > 44 + vMax * along / BV) continue;
    th.push({ x, y, ux: s.ux, uy: s.uy, w: 1 });
  }
  // 近距离来不及看见弹丸再反应：把对手炮线当作一发随时会来的弹，提前摆好装甲相位。
  if (curD < 210 && k.tur === k.tur) {
    // 炮线按对手炮塔的转动趋势外推到此刻，并在左右各留一点角度余量。
    const lg = (t - k.t) / 1000, a0 = k.tur + clamp(k.turOm * lg, -0.25, 0.25), ox = k.x + k.vx * lg, oy = k.y + k.vy * lg;
    for (const [da, w] of AIMJIT) { const c = Math.cos(a0 + da), s = Math.sin(a0 + da); th.push({ x: ox + c * MUZ, y: oy + s * MUZ, ux: c, uy: s, w }); }
  }
  let best = null;
  for (let i = 0; i <= NDIR; i++) {
    const e = i < NDIR ? evalMove(Math.cos(i * TAU / NDIR), Math.sin(i * TAU / NDIR), 0, me, k, th) : evalMove(0, 0, 0, me, k, th);
    if (!best || e.c < best.c) best = e;
  }
  if (th.length && best.risk > 0.05) {
    // 单靠平移躲不开：加入旋转，让装甲相位把来弹让给车体。
    for (const spin of [1, -1, 0.5, -0.5]) {
      for (let i = 0; i < NDIR; i += 2) { const e = evalMove(Math.cos(i * TAU / NDIR), Math.sin(i * TAU / NDIR), spin, me, k, th); if (e.c < best.c) best = e; }
      const e = evalMove(0, 0, spin, me, k, th); if (e.c < best.c) best = e;
    }
    if (best.spin) dbg.spin++;
    dbg.risk += best.risk;
  }
  return best;
}

// 我方位置外推。两车不能重叠：顶住对手后，宿主把重叠量对半分给双方，朝对手方向多走的那段只算一半。
const adv = { x: 0, y: 0 };
function advance(x, y, vx, vy, dt, k) {
  x += vx * dt; y += vy * dt;
  if (k) { const dx = k.x - x, dy = k.y - y, d = Math.hypot(dx, dy); if (d < 52 && d > 1e-6) { const c = (52 - d) / 2 / d; x -= dx * c; y -= dy * c; } }
  adv.x = clamp(x, AR, FW - AR); adv.y = clamp(y, AR, FH - AR);
  return adv;
}
function decide(t) {
  const lag = Math.min(0.25, Math.max(0, (t - est.t) / 1000));
  const k = est.k;
  advance(est.me.x, est.me.y, cmd.vx, cmd.vy, lag, k);
  const me = { x: adv.x, y: adv.y, a: est.me.a + cmd.om * lag };
  const out = { act: { moveX: 0, moveY: 0, spin: 0, aimX: 0.5, aimY: 0.5, durationMs: 150 }, fire: false, dir: aimDir, m: cmd, shot: null };
  if (!k) return out;
  const heat = heatNow(t);
  curD = Math.hypot(k.x - me.x, k.y - me.y);
  dPref = est.countdown ? 300 : HUG;
  if (est.countdown || curD < 150) nearT = t;
  const mv = chooseMove(t, me, k);
  out.act.moveX = mv.x; out.act.moveY = mv.y; out.act.spin = mv.spin;
  out.m = motion(mv.x, mv.y, mv.spin);
  // 炮塔需要转过的角度越大，出膛越晚：按预计出膛时刻解算瞄点（先粗算一次估转角，再精算）。
  // 指令要等下一个控制边界才生效。act 返回的时刻紧跟在边界之后，由它推出离下一个边界还有多久。
  let toB = STEP - ((t - bndT + 2) % STEP);
  if (toB < 1.5) toB += STEP;
  const lead0 = bndT ? toB + LEAD : 17;
  let lead = lead0, sol = null, fx = 0, fy = 0, err = 0;
  for (let pass = 0; pass < 2; pass++) {
    advance(me.x, me.y, out.m.vx, out.m.vy, lead / 1000, k); fx = adv.x; fy = adv.y;
    sol = bestAim(k, fx, fy, t + lead);
    out.dir = Math.atan2(sol.qy - fy, sol.qx - fx);
    err = Math.abs(wrap(turEst - out.dir));
    if (err < 0.03 || err > 0.3 || curD >= 150) break;
    lead = lead0 + err * 100;
  }
  const [ax, ay] = aimPoint(fx, fy, sol.qx, sol.qy);
  out.act.aimX = ax; out.act.aimY = ay;
  // 转角不大时不等下一轮：下达瞄准后原地等炮塔到位就开火，缩短炮线暴露给对手的时间。
  // 只在近距离这样做；远距离要的是稳定跟踪下的时序一致。
  const ready = curD >= 150 ? err < 0.03 : err < 0.3;
  if (!est.countdown) {
    dbg.pSum += sol.p; dbg.pN++;
    const b = BK(sol.D);
    // 双方都还要挨很多发时，把贴近途中的热量省下来留到顶住再用；任一方只剩三发以内的血时先手更要紧，不省。
    const save = dmgUnit > 0 && est.hp.me > dmgUnit * 3.2 && est.hp.foe > dmgUnit * 3.2;
    let want;
    if (b < 2) {
      // 近距离：有余量时抓紧打；热量吃紧时一发要等半秒才凉回来，只在最近 32 次解算里把握排进前六的时刻打。
      pRing[pRN++ & 31] = sol.p;
      let thr = 0.3;
      if (heat >= 50 && pRN >= 16) { pSort.set(pRing); pSort.sort(); thr = Math.max(0.38, pSort[26]); }
      // 贴近途中 95px 以外不打：这一段的实测命中率只有顶住之后的一半不到，热量留到顶住再用。
      want = sol.p >= thr && !(save && sol.D > 95);
    }
    // 150px 以外不开火：打不中，白白烧掉连发的余量。只有追了三秒还进不了 150px 的对手，才用凉透的那点余量打冷枪。
    else want = t - nearT > 3000 && heat <= 8 && sol.p >= 0.2;
    // 收尾：双方都残血、对手只剩一发的血时，允许顶着过热多打一发抢先结束（过热自损一成血，最多两次）。
    // 自己血量还多的局不这么做：那种局不缺这半秒，白白自损。
    const last = dmgUnit > 0 && est.hp.foe > 0 && est.hp.foe <= dmgUnit * 1.2 && est.hp.me <= 0.4 && est.hp.me > 0.12 + dmgUnit * 1.5 && overN < 2 && heat > 87 && heat <= 97;
    out.fire = want && ready && t - lastFire >= fireGap && t - est.t < 140 && (heat <= 87 || last);
    out.over = last;
    out.shot = { b, p: sol.p, tof: sol.tof, d: sol.d };
  }
  return out;
}

// ───────────────────────── 主循环 ─────────────────────────
let obs = null, arrive = 0, fails = 0, calls = 0, logAt = now();
while (!obs) { try { obs = await lab.observe(); arrive = now(); } catch { if (++fails > 200) return; await lab.sleep(10); } }
fails = 0;
for (;;) {
  try { if (ingest(obs, arrive)) credit(); } catch (e) { dbg.err = String(e).slice(0, 80); }
  try {
    const t = now(), plan = decide(t), a = plan.act;
    // 最后一道防线：任何非数值都不发给宿主（被拒绝的调用连续出现会让脚本退出）。
    if (!(Math.abs(a.moveX) <= 1)) a.moveX = 0;
    if (!(Math.abs(a.moveY) <= 1)) a.moveY = 0;
    if (!(Math.abs(a.spin) <= 1)) a.spin = 0;
    if (!(a.aimX >= 0 && a.aimX <= 1)) a.aimX = 0.5;
    if (!(a.aimY >= 0 && a.aimY <= 1)) a.aimY = 0.5;
    obs = await lab.act(a); arrive = now(); calls++;
    const actAt = arrive;
    bndT = arrive;
    cmd.vx = plan.m.vx; cmd.vy = plan.m.vy; cmd.om = plan.m.om;
    if (a.spin || !(a.moveX || a.moveY) || a.moveX !== lastMX || a.moveY !== lastMY) impureT = arrive;
    lastMX = a.moveX; lastMY = a.moveY;
    // 炮塔模型：指令生效前按旧方向、之后按新方向，以 10 rad/s 逼近。
    if (turEst === turEst) {
      const step = (dir, ms) => { const e = wrap(dir - turEst); turEst = wrap(turEst + clamp(e, -0.01 * ms, 0.01 * ms)); };
      const eff = Math.max(turT, arrive - 6);
      step(aimDir, Math.max(0, eff - turT)); step(plan.dir, Math.max(0, arrive - eff));
    }
    turT = arrive; aimDir = plan.dir;
    if (plan.fire) {
      const rest = turEst === turEst ? Math.abs(wrap(turEst - plan.dir)) : 0;
      if (rest > 0.012) { const until = now() + rest * 100 + 1.5; while (now() < until); turEst = plan.dir; turT = now(); }
      const tf = now(), s = plan.shot;
      heatNow(tf); heatM += 10;
      shots.push(tf); if (shots.length > 40) shots.shift();
      lastFire = tf; dbg.fires++; reqN++; if (plan.over) overN++;
      tally.shots[s.b]++; tally.pSum[s.b] += s.p; flying.push({ ta: tf + 10 + s.tof * 1000, b: s.b });
      if (DEBUG) dbg.sh.push([Math.round(curD), s.d, +s.p.toFixed(2), Math.round(rest * 1000)]);
      obs = await lab.fire(); arrive = now(); calls++;
    }
    fails = 0; dbg.loops++;
    // 宿主对单局调用次数有上限：接近时放慢节奏。
    if (calls > 26000) await lab.sleep(30);
    else if (POLL && !est.countdown && obs.frameId === est.frame) {
      // 画面每两个控制周期采样一次，编码要几毫秒：在采样边界返回的 act 带回的还是旧画面。
      // 新画面编码完成时离下一个控制边界还有一小段时间，这时主动取一次，决策就能赶上下一个边界生效，
      // 不必再等一个周期。只在新画面按节奏应当出现的时刻去取，避免空等。
      const dead = actAt + 11;
      let tw = Math.max(est.t + SLOT + ENC - 0.5, now() + 0.3);
      for (let i = 0; i < 4 && tw <= dead && tw < est.t + SLOT + ENC + 25; i++) {
        while (now() < tw);
        const o = await lab.observe(); calls++; dbg.poll++;
        if (o.frameId !== est.frame) { obs = o; arrive = now(); dbg.fresh++; break; }
        tw = now() + 2;
      }
    }
    if (DEBUG && arrive - logAt > 2000) {
      logAt = arrive; calls++;
      await lab.log(JSON.stringify({ f: dbg.frames, lp: dbg.loops, fire: dbg.fires, poll: [dbg.fresh, dbg.poll], v: Math.round(vMax), gap: Math.round(fireGap), spin: dbg.spin, risk: +dbg.risk.toFixed(1), dec: +(dbg.decode / Math.max(1, dbg.frames)).toFixed(1), p: +(dbg.pSum / Math.max(1, dbg.pN)).toFixed(2), heat: Math.round(est.heat), fh: Math.round(est.foeHeat), hp: [est.hp.me.toFixed(2), est.hp.foe.toFixed(2)], D: Math.round(curD), sh: tally.shots, hi: tally.hits, tk: tally.took, err: dbg.err, S: dbg.sh }));
      dbg.sh = [];
      dbg.frames = dbg.fires = dbg.loops = dbg.lost = dbg.spin = dbg.risk = dbg.decode = dbg.pSum = dbg.pN = dbg.poll = dbg.fresh = 0;
    }
  } catch (e) {
    if (++fails > 40) return;
    await lab.sleep(4);
  }
}
