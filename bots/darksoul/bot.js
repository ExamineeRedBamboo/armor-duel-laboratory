// 暗魂 DarkSoul —— 纯视觉闭环参赛脚本。
// 输入只有 lab.observe / lab.act / lab.fire 返回的 JPEG；输出只有移动、旋转、瞄准和单发请求。
// 流程：局部 JPEG 解码 → 识别双方车体/装甲相位/炮管/弹丸/HUD → 帧时间与出膛延迟自校准 →
//       速度坐标系下的经验误差分布瞄准、诱导甩炮单发 → 来弹与炮线威胁下的平移/旋转防御。
// 策略说明与实测数据见同目录 README.md。

{
// ---------- 局部 JPEG 解码（基线 Huffman，三分量同采样）----------
// 熵码必须顺序读完；反变换与色彩转换只对被标记的单元做。不支持的结构返回 false，由调用方退回 lab.pixels。
const ZIGZAG = new Uint8Array([0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63]);
const IC = new Float32Array(64); // IC[x*8+u] = C(u)/2·cos((2x+1)uπ/16)
for (let x = 0; x < 8; x++) for (let u = 0; u < 8; u++) IC[x * 8 + u] = (u ? 0.5 : 0.5 / Math.SQRT2) * Math.cos((2 * x + 1) * u * Math.PI / 16);
const B64V = new Uint8Array(256);
{ const a = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'; for (let i = 0; i < 64; i++) B64V[a.charCodeAt(i)] = i; }

const JD = {
  buf: new Uint8Array(1 << 18), len: 0, w: 0, h: 0, H: 1, V: 1, nb: 1, uw: 8, uh: 8, mw: 0, mh: 0, nm: 0, ri: 0,
  q: [], comp: [], huff: [], scanStart: 0,
  rgb: null, mark: null, dcY: null, bgY: null, bgN: null, decodedAt: null, epoch: 0, state: null,
  coef: null, pix: null, tmp: new Float32Array(64),
};

function b64decode(s) {
  let n = s.length;
  while (n && s.charCodeAt(n - 1) === 61) n--;
  const out = (n * 3) >> 2;
  if (JD.buf.length < out + 8) JD.buf = new Uint8Array(out * 2);
  const b = JD.buf;
  let o = 0, i = 0;
  for (; i + 4 <= n; i += 4) {
    const v = B64V[s.charCodeAt(i)] << 18 | B64V[s.charCodeAt(i + 1)] << 12 | B64V[s.charCodeAt(i + 2)] << 6 | B64V[s.charCodeAt(i + 3)];
    b[o++] = v >> 16; b[o++] = (v >> 8) & 255; b[o++] = v & 255;
  }
  const r = n - i;
  if (r >= 2) {
    const v = B64V[s.charCodeAt(i)] << 18 | B64V[s.charCodeAt(i + 1)] << 12 | (r > 2 ? B64V[s.charCodeAt(i + 2)] << 6 : 0);
    b[o++] = v >> 16; if (r > 2) b[o++] = (v >> 8) & 255;
  }
  JD.len = o;
}

function buildHuff(counts, syms) {
  const fast = new Int32Array(512).fill(-1), maxcode = new Int32Array(18).fill(-1), valptr = new Int32Array(17), mincode = new Int32Array(17);
  let code = 0, k = 0;
  for (let l = 1; l <= 16; l++) {
    valptr[l] = k; mincode[l] = code;
    for (let i = 0; i < counts[l - 1]; i++) {
      if (l <= 9) { const base = code << (9 - l); for (let j = 0; j < 1 << (9 - l); j++) fast[base + j] = (l << 8) | syms[k]; }
      code++; k++;
    }
    maxcode[l] = counts[l - 1] ? code - 1 : -1;
    code <<= 1;
  }
  return { fast, maxcode, valptr, mincode, syms };
}

function parseHeaders() {
  const b = JD.buf;
  if (b[0] !== 0xff || b[1] !== 0xd8) return false;
  let p = 2, sof = false;
  while (p + 4 <= JD.len) {
    if (b[p] !== 0xff) return false;
    const m = b[p + 1];
    if (m === 0xff) { p++; continue; }
    const L = b[p + 2] << 8 | b[p + 3], e = p + 2 + L;
    if (m === 0xdb) {
      let q = p + 4;
      while (q < e) {
        const pq = b[q] >> 4, tq = b[q] & 15; q++;
        const t = new Float32Array(64);
        for (let i = 0; i < 64; i++) { t[ZIGZAG[i]] = pq ? (b[q] << 8 | b[q + 1]) : b[q]; q += pq ? 2 : 1; }
        JD.q[tq] = t;
      }
    } else if (m === 0xc0 || m === 0xc1) {
      JD.h = b[p + 5] << 8 | b[p + 6]; JD.w = b[p + 7] << 8 | b[p + 8];
      if (b[p + 9] !== 3) return false;
      JD.comp = [];
      const hv = b[p + 11];
      for (let i = 0; i < 3; i++) {
        const o = p + 10 + i * 3;
        if (b[o + 1] !== hv) return false; // 只处理三分量同采样
        JD.comp.push({ id: b[o], tq: b[o + 2], pred: 0, dc: null, ac: null });
      }
      JD.H = hv >> 4; JD.V = hv & 15;
      if (JD.H < 1 || JD.V < 1 || JD.H > 4 || JD.V > 4) return false;
      sof = true;
    } else if (m >= 0xc2 && m <= 0xcf && m !== 0xc4 && m !== 0xc8 && m !== 0xcc) {
      return false;
    } else if (m === 0xc4) {
      let q = p + 4;
      while (q < e) {
        const tc = b[q] >> 4, th = b[q] & 15; q++;
        const counts = Array.from(b.subarray(q, q + 16)); let n = 0; for (let i = 0; i < 16; i++) n += counts[i];
        JD.huff[tc * 4 + th] = buildHuff(counts, Array.from(b.subarray(q + 16, q + 16 + n)));
        q += 16 + n;
      }
    } else if (m === 0xdd) {
      JD.ri = b[p + 4] << 8 | b[p + 5];
    } else if (m === 0xda) {
      if (!sof || b[p + 4] !== 3) return false;
      for (let i = 0; i < 3; i++) {
        const cs = b[p + 5 + i * 2], t = b[p + 6 + i * 2];
        const c = JD.comp.find(c => c.id === cs);
        if (!c) return false;
        c.dc = JD.huff[t >> 4]; c.ac = JD.huff[4 + (t & 15)];
        if (!c.dc || !c.ac || !JD.q[c.tq]) return false;
      }
      // 扫描内分量顺序以 SOS 为准
      JD.comp = Array.from({ length: 3 }, (_, i) => JD.comp.find(c => c.id === b[p + 5 + i * 2]));
      JD.scanStart = e;
      JD.nb = JD.H * JD.V; JD.uw = 8 * JD.H; JD.uh = 8 * JD.V;
      const mw = Math.ceil(JD.w / JD.uw), mh = Math.ceil(JD.h / JD.uh), nm = mw * mh;
      if (!JD.rgb || JD.rgb.length !== JD.w * JD.h * 3 || JD.nm !== nm || JD.dcY.length !== nm * JD.nb) {
        JD.mw = mw; JD.mh = mh; JD.nm = nm;
        JD.rgb = new Uint8Array(JD.w * JD.h * 3);
        JD.mark = new Uint8Array(nm); JD.decodedAt = new Int32Array(nm).fill(-1); JD.state = new Int32Array(nm * 6);
        JD.dcY = new Int16Array(nm * JD.nb); JD.bgY = new Int16Array(nm * JD.nb); JD.bgN = new Uint8Array(nm * JD.nb);
        JD.coef = [0, 1, 2].map(() => Array.from({ length: JD.nb }, () => new Float32Array(64)));
        JD.pix = [0, 1, 2].map(() => Array.from({ length: JD.nb }, () => new Float32Array(64)));
        JD.nac = [0, 1, 2].map(() => new Int32Array(JD.nb)); JD.dcTmp = new Int32Array(JD.nb);
      }
      return true;
    }
    p = e;
  }
  return false;
}

let bpos = 0, bits = 0, nbits = 0;
function fillBits() {
  const b = JD.buf;
  while (nbits <= 24) {
    let c = 0;
    if (bpos < JD.len) {
      c = b[bpos];
      if (c === 0xff) { if (b[bpos + 1] === 0) bpos += 2; else c = 0; }
      else bpos++;
    }
    bits = ((bits << 8) | c) >>> 0; nbits += 8;
  }
}
function decodeSym(H) {
  if (nbits < 16) fillBits();
  const look = (bits >>> (nbits - 9)) & 511, f = H.fast[look];
  if (f >= 0) { nbits -= f >> 8; return f & 255; }
  let code = look;
  for (let l = 10; l <= 16; l++) {
    code = (code << 1) | ((bits >>> (nbits - l)) & 1);
    if (code <= H.maxcode[l]) { nbits -= l; return H.syms[H.valptr[l] + code - H.mincode[l]]; }
  }
  throw Error('huff');
}
function receive(s) {
  if (!s) return 0;
  if (nbits < s) fillBits();
  let v = (bits >>> (nbits - s)) & ((1 << s) - 1);
  nbits -= s;
  if (v < 1 << (s - 1)) v -= (1 << s) - 1;
  return v;
}
// 解一个块；out 为 null 时只跳过。返回非零 AC 个数
function decodeBlock(c, out) {
  c.pred += receive(decodeSym(c.dc));
  let n = 0;
  if (out) { out.fill(0); out[0] = c.pred; }
  for (let k = 1; k < 64;) {
    const rs = decodeSym(c.ac), s = rs & 15;
    if (!s) { if (rs === 0xf0) { k += 16; continue; } break; }
    k += rs >> 4;
    const v = receive(s);
    if (out && k < 64) { out[ZIGZAG[k]] = v; n++; }
    k++;
  }
  return n;
}
function restart() {
  nbits = 0; bits = 0;
  const b = JD.buf;
  while (bpos + 1 < JD.len && !(b[bpos] === 0xff && b[bpos + 1] >= 0xd0 && b[bpos + 1] <= 0xd7)) bpos++;
  bpos += 2;
  for (const c of JD.comp) c.pred = 0;
}
function idctBlock(co, q, nac, out) {
  if (!nac) { out.fill(co[0] * q[0] * 0.125); return; }
  const t = JD.tmp;
  for (let i = 0; i < 64; i++) co[i] *= q[i];
  for (let y = 0; y < 8; y++) {
    const r = y * 8;
    const c0 = co[r], c1 = co[r + 1], c2 = co[r + 2], c3 = co[r + 3], c4 = co[r + 4], c5 = co[r + 5], c6 = co[r + 6], c7 = co[r + 7];
    if (!(c1 || c2 || c3 || c4 || c5 || c6 || c7)) { const v = c0 * IC[0]; for (let x = 0; x < 8; x++) t[r + x] = v; continue; }
    for (let x = 0; x < 8; x++) {
      const ic = x * 8;
      t[r + x] = IC[ic] * c0 + IC[ic + 1] * c1 + IC[ic + 2] * c2 + IC[ic + 3] * c3 + IC[ic + 4] * c4 + IC[ic + 5] * c5 + IC[ic + 6] * c6 + IC[ic + 7] * c7;
    }
  }
  for (let x = 0; x < 8; x++) {
    const a0 = t[x], a1 = t[8 + x], a2 = t[16 + x], a3 = t[24 + x], a4 = t[32 + x], a5 = t[40 + x], a6 = t[48 + x], a7 = t[56 + x];
    for (let y = 0; y < 8; y++) {
      const ic = y * 8;
      out[y * 8 + x] = IC[ic] * a0 + IC[ic + 1] * a1 + IC[ic + 2] * a2 + IC[ic + 3] * a3 + IC[ic + 4] * a4 + IC[ic + 5] * a5 + IC[ic + 6] * a6 + IC[ic + 7] * a7;
    }
  }
}
const clampByte = v => (v < 0 ? 0 : v > 255 ? 255 : v + 0.5) | 0;
function decodeMcuFull(m) {
  const comps = JD.comp, nb = JD.nb, w = JD.w, h = JD.h, rgb = JD.rgb, coef = JD.coef, pix = JD.pix;
  for (let c = 0; c < 3; c++) for (let j = 0; j < nb; j++) JD.nac[c][j] = decodeBlock(comps[c], coef[c][j]);
  for (let j = 0; j < nb; j++) JD.dcTmp[j] = coef[0][j][0];
  for (let c = 0; c < 3; c++) { const q = JD.q[comps[c].tq]; for (let j = 0; j < nb; j++) idctBlock(coef[c][j], q, JD.nac[c][j], pix[c][j]); }
  const X0 = (m % JD.mw) * JD.uw, Y0 = ((m / JD.mw) | 0) * JD.uh;
  for (let j = 0; j < nb; j++) {
    const PY = pix[0][j], PB = pix[1][j], PR = pix[2][j];
    const x0 = X0 + (j % JD.H) * 8, y0 = Y0 + ((j / JD.H) | 0) * 8;
    const xe = Math.min(8, w - x0), ye = Math.min(8, h - y0);
    for (let y = 0; y < ye; y++) {
      let o = ((y0 + y) * w + x0) * 3, i = y * 8;
      for (let x = 0; x < xe; x++, i++, o += 3) {
        const L = PY[i] + 128, cb = PB[i], cr = PR[i];
        rgb[o] = clampByte(L + 1.402 * cr);
        rgb[o + 1] = clampByte(L - 0.344136 * cb - 0.714136 * cr);
        rgb[o + 2] = clampByte(L + 1.772 * cb);
      }
    }
  }
  JD.decodedAt[m] = JD.epoch;
}
// 解码一帧：all 全解；否则解 JD.mark 标记的单元，并对亮度直流比背景高出 hotThr 的单元及其 8 邻域补解。
// 背景：某块直流连续 4 帧变化不超过 1 时记为背景。返回热点单元列表。
function decodeFrame(all, hotThr) {
  const comps = JD.comp, nm = JD.nm, mw = JD.mw, mh = JD.mh, nb = JD.nb, st = JD.state;
  bpos = JD.scanStart; bits = 0; nbits = 0;
  for (const c of comps) c.pred = 0;
  JD.epoch++;
  const hot = [];
  let todo = JD.ri;
  for (let m = 0; m < nm; m++) {
    if (JD.ri) { if (todo === 0) { restart(); todo = JD.ri; } todo--; }
    const k = m * 6;
    st[k] = bpos; st[k + 1] = bits; st[k + 2] = nbits; st[k + 3] = comps[0].pred; st[k + 4] = comps[1].pred; st[k + 5] = comps[2].pred;
    if (all || JD.mark[m]) {
      decodeMcuFull(m);
      for (let j = 0; j < nb; j++) {
        const u = m * nb + j, dc = JD.dcTmp[j];
        if (Math.abs(dc - JD.dcY[u]) <= 1) { if (JD.bgN[u] < 250) JD.bgN[u]++; } else JD.bgN[u] = 0;
        JD.dcY[u] = dc; if (JD.bgN[u] >= 4) JD.bgY[u] = dc;
      }
      continue;
    }
    let isHot = false;
    for (let j = 0; j < nb; j++) {
      decodeBlock(comps[0], null);
      const u = m * nb + j, dc = comps[0].pred;
      if (hotThr && JD.bgN[u] >= 4 && dc - JD.bgY[u] > hotThr) isHot = true;
      if (Math.abs(dc - JD.dcY[u]) <= 1) { if (JD.bgN[u] < 250) JD.bgN[u]++; } else JD.bgN[u] = 0;
      JD.dcY[u] = dc; if (JD.bgN[u] >= 4) JD.bgY[u] = dc;
    }
    for (let j = 0; j < nb; j++) decodeBlock(comps[1], null);
    for (let j = 0; j < nb; j++) decodeBlock(comps[2], null);
    if (isHot) hot.push(m);
  }
  for (const m of hot) {
    const mx = m % mw, my = (m / mw) | 0;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      const x = mx + dx, y = my + dy;
      if (x < 0 || y < 0 || x >= mw || y >= mh) continue;
      const n = y * mw + x;
      if (JD.decodedAt[n] === JD.epoch) continue;
      const k = n * 6;
      bpos = st[k]; bits = st[k + 1]; nbits = st[k + 2]; comps[0].pred = st[k + 3]; comps[1].pred = st[k + 4]; comps[2].pred = st[k + 5];
      decodeMcuFull(n);
    }
  }
  return hot;
}
function markRect(x0, y0, x1, y1) {
  const a = Math.max(0, Math.floor(x0 / JD.uw)), b = Math.min(JD.mw - 1, Math.floor(x1 / JD.uw));
  const c = Math.max(0, Math.floor(y0 / JD.uh)), d = Math.min(JD.mh - 1, Math.floor(y1 / JD.uh));
  for (let y = c; y <= d; y++) for (let x = a; x <= b; x++) JD.mark[y * JD.mw + x] = 1;
}

// ---------- 常量 ----------
const Q = Math.PI / 2, TAU = Math.PI * 2;
const wrap = a => Math.atan2(Math.sin(a), Math.cos(a));
const wrapQ = a => a - Q * Math.round(a / Q);
const clamp = (v, lo, hi) => (v < lo ? lo : v > hi ? hi : v);
const clock = () => performance.now() / 1000;
const FW = 960, FH = 600, HUD = 80, INSET = 34;
const BULLET = 1000, MUZZLE = 42.01, ARMOR_R = 26, TURRET_RATE = 10;
const ME = lab.side, FOE = ME === 'red' ? 'blue' : 'red';
const SPAWN = { red: { x: 210, y: 300, turret: 0 }, blue: { x: 750, y: 300, turret: Math.PI } };

// ---------- 像素分类 ----------
const isDark = (r, g, b) => r < 48 && g < 48 && b < 54;
const isWhite = (r, g, b) => r > 185 && g > 185 && b > 185 && b >= r - 10;
const isFlashBody = (r, g, b) => r - b > 8 && Math.abs(r - 111) < 22 && Math.abs(g - 100) < 22 && Math.abs(b - 89) < 22;
const isRed = (r, g, b) => r > 130 && r - g > 55 && r - b > 45;
const isBlue = (r, g, b) => b > 150 && b - r > 70 && g > 90;
const isPlateFlash = (r, g, b) => r > 225 && g > 215 && r - b > 12;
const isCore = (r, g, b) => r >= 232 && g >= 220 && b >= 196 && b <= 240 && r - b >= 10;
const sideColor = { red: isRed, blue: isBlue };

// ---------- 感知（在 JD.rgb 上工作）----------
const V = { s: 1, top: 80, w: 0, h: 0 };
const toW = (px, py) => ({ x: (px + 0.5) / V.s - 0.5, y: (py + 0.5) / V.s - 0.5 - HUD });
const toPx = (x, y) => ({ x: (x + 0.5) * V.s - 0.5, y: (y + HUD + 0.5) * V.s - 0.5 });
function pixAt(x, y) { const i = (y * V.w + x) * 3, d = JD.rgb; return [d[i], d[i + 1], d[i + 2]]; }
function forDisk(cx, cy, r0, r1, fn) {
  const a = r0 * r0, b = r1 * r1, d = JD.rgb, w = V.w;
  const y0 = Math.max(V.top, Math.floor(cy - r1)), y1 = Math.min(V.h - 1, Math.ceil(cy + r1));
  const x0 = Math.max(0, Math.floor(cx - r1)), x1 = Math.min(w - 1, Math.ceil(cx + r1));
  for (let y = y0; y <= y1; y++) {
    const dy = y - cy;
    for (let x = x0; x <= x1; x++) {
      const dx = x - cx, q = dx * dx + dy * dy;
      if (q < a || q > b) continue;
      const i = (y * w + x) * 3;
      fn(d[i], d[i + 1], d[i + 2], dx, dy, x, y);
    }
  }
}
const bodyMask = (r, g, b) => isDark(r, g, b) || isWhite(r, g, b) || isFlashBody(r, g, b);
function refineBody(cx, cy) {
  const s = V.s, R = 22 * s;
  let n = 0;
  for (let it = 0; it < 5; it++) {
    let sx = 0, sy = 0; n = 0;
    forDisk(cx, cy, 0, R, (r, g, b, dx, dy, x, y) => { if (bodyMask(r, g, b)) { sx += x; sy += y; n++; } });
    if (n < 250 * s * s) return null;
    const nx = sx / n, ny = sy / n;
    const moved = Math.hypot(nx - cx, ny - cy);
    cx = nx; cy = ny;
    if (moved < 0.05) break;
  }
  return { cx, cy, n };
}
// 在像素中心 (cx,cy) 附近识别某方机器人：车体质心 → 装甲 4θ 相位 → 逐板质心精修 → 炮管
function measureRobot(side, cx, cy) {
  const s = V.s, isC = sideColor[side];
  const body = refineBody(cx, cy);
  if (!body) return null;
  cx = body.cx; cy = body.cy;
  let C = 0, S = 0, n = 0;
  const px = [];
  forDisk(cx, cy, 18 * s, 34 * s, (r, g, b, dx, dy) => {
    if (!isC(r, g, b) && !isPlateFlash(r, g, b)) return;
    const ph = 4 * Math.atan2(dy, dx); C += Math.cos(ph); S += Math.sin(ph); n++; px.push(dx, dy);
  });
  if (n < 30 * s * s) return null; // 不是这方的车
  const phase = Math.atan2(S, C) / 4;
  let ox = 0, oy = 0, plates = 0;
  for (let it = 0; it < 2; it++) {
    const cand = [];
    for (let k = 0; k < 4; k++) {
      const ang = phase + k * Q, ux = Math.cos(ang), uy = Math.sin(ang);
      let sx = 0, sy = 0, m = 0;
      for (let j = 0; j < px.length; j += 2) {
        const dx = px[j] - ox, dy = px[j + 1] - oy;
        const rad = (dx * ux + dy * uy) / s, tan = (-dx * uy + dy * ux) / s;
        if (Math.abs(rad - ARMOR_R) > 4.5 || Math.abs(tan) > 8.5) continue;
        sx += px[j]; sy += px[j + 1]; m++;
      }
      if (m >= 22 * s * s) cand.push({ x: sx / m - ARMOR_R * s * ux, y: sy / m - ARMOR_R * s * uy, m });
    }
    if (!cand.length) break;
    if (cand.length >= 3) {
      const mx = cand.map(c => c.x).sort((a, b) => a - b)[cand.length >> 1], my = cand.map(c => c.y).sort((a, b) => a - b)[cand.length >> 1];
      const kept = cand.filter(c => Math.hypot(c.x - mx, c.y - my) < 1.5 * s);
      if (kept.length >= 2) cand.splice(0, cand.length, ...kept);
    }
    let wx = 0, wy = 0, wm = 0;
    for (const c of cand) { wx += c.x * c.m; wy += c.y * c.m; wm += c.m; }
    if (Math.hypot(wx / wm - ox, wy / wm - oy) > 8 * s) break;
    ox = wx / wm; oy = wy / wm; plates = cand.length;
  }
  cx += ox; cy += oy;
  const angs = [];
  forDisk(cx, cy, 28 * s, 38 * s, (r, g, b, dx, dy) => { if (isWhite(r, g, b)) angs.push(Math.atan2(dy, dx)); });
  let turret = null;
  if (angs.length >= 6) {
    let best = 0, bestA = 0;
    for (const a0 of angs) {
      let c = 0, sc = 0, ss = 0;
      for (const a of angs) { const d = wrap(a - a0); if (Math.abs(d) < 0.25) { c++; sc += Math.cos(a); ss += Math.sin(a); } }
      if (c > best) { best = c; bestA = Math.atan2(ss, sc); }
    }
    if (best >= 5 * s * s) turret = bestA;
  }
  const p = toW(cx, cy);
  return { x: p.x, y: p.y, cx, cy, phase, turret, plates };
}
// 全图搜索（整帧已解码）：暗像素粗网格 → 候选车体 → 按装甲颜色认领
function searchRobots() {
  const d = JD.rgb, w = V.w, h = V.h, s = V.s, G = Math.max(4, Math.round(8 * s));
  const gw = Math.ceil(w / G), gh = Math.ceil(h / G), counts = new Int32Array(gw * gh);
  for (let y = V.top; y < h; y += 2) for (let x = 0; x < w; x += 2) {
    const i = (y * w + x) * 3, r = d[i], g = d[i + 1], b = d[i + 2];
    if (isDark(r, g, b) || isFlashBody(r, g, b)) counts[(y / G | 0) * gw + (x / G | 0)]++;
  }
  const B = Math.max(2, Math.ceil(48 * s / G)), cands = [];
  for (let k = 0; k < 3; k++) {
    let best = -1, bx = 0, by = 0;
    for (let y = 0; y + B <= gh; y++) for (let x = 0; x + B <= gw; x++) {
      let v = 0;
      for (let yy = y; yy < y + B; yy++) for (let xx = x; xx < x + B; xx++) v += counts[yy * gw + xx];
      if (v > best) { best = v; bx = x; by = y; }
    }
    if (best < 90 * s * s) break;
    cands.push({ cx: (bx + B / 2) * G, cy: (by + B / 2) * G });
    const rr = Math.ceil(40 * s / G), gx = bx + (B >> 1), gy = by + (B >> 1);
    for (let y = Math.max(0, gy - rr); y <= Math.min(gh - 1, gy + rr); y++) for (let x = Math.max(0, gx - rr); x <= Math.min(gw - 1, gx + rr); x++) counts[y * gw + x] = 0;
  }
  const out = {};
  for (const side of ['red', 'blue']) {
    let best = null;
    for (const c of cands) { const m = measureRobot(side, c.cx, c.cy); if (m && (!best || m.plates > best.plates)) best = m; }
    if (best) out[side] = best;
  }
  return out;
}
function readHud(side) {
  const hx = side === 'red' ? 26 : FW - 334, isC = sideColor[side], s = V.s, d = JD.rgb, w = V.w;
  const scan = (x0, len, y, fn) => {
    let last = -1;
    const py = Math.round((y + 0.5) * s - 0.5);
    for (let k = 0; k < len; k++) {
      const px = Math.round((x0 + k + 0.5) * s - 0.5); if (px >= w) break;
      const i = (py * w + px) * 3;
      if (fn(d[i], d[i + 1], d[i + 2])) last = k;
    }
    return last + 1;
  };
  const hp = scan(hx, 308, 43, isC) / 308;
  const hf = scan(hx + 211, 97, 62, (r, g, b) => r > 150 && r - b > 60);
  return { hp, heat: hf ? Math.max(0, hf - 0.5) / 97 * 100 : 0 };
}
// 弹芯：在本帧解出的单元里找高亮暖白小簇；拖尾颜色判定归属与方向
function findBullets(robots) {
  const s = V.s, d = JD.rgb, w = V.w, mw = JD.mw, uw = JD.uw, uh = JD.uh, ep = JD.epoch;
  const pts = [];
  for (let m = 0; m < JD.nm; m++) {
    if (JD.decodedAt[m] !== ep) continue;
    const x0 = (m % mw) * uw, y0 = ((m / mw) | 0) * uh;
    for (let y = Math.max(y0, V.top); y < Math.min(y0 + uh, V.h); y++) for (let x = x0; x < Math.min(x0 + uw, w); x++) {
      const i = (y * w + x) * 3;
      if (isCore(d[i], d[i + 1], d[i + 2])) pts.push(x, y);
    }
  }
  const cl = [];
  const lim = (5 * s) ** 2;
  for (let j = 0; j < pts.length; j += 2) {
    const x = pts[j], y = pts[j + 1];
    let c = null;
    for (const q of cl) { const dx = q.sx / q.n - x, dy = q.sy / q.n - y; if (dx * dx + dy * dy < lim) { c = q; break; } }
    if (!c) { c = { sx: 0, sy: 0, n: 0 }; cl.push(c); }
    c.sx += x; c.sy += y; c.n++;
  }
  const out = [];
  const rob = Object.values(robots).filter(Boolean);
  for (const c of cl) {
    if (c.n < 3 * s * s || c.n > 30 * s * s) continue;
    const cx = c.sx / c.n, cy = c.sy / c.n;
    // 装甲受击闪白与炮管附近不当作弹丸
    let bad = false;
    for (const r of rob) { const q = Math.hypot(cx - r.cx, cy - r.cy) / s; if (q < 34) bad = true; }
    if (bad) continue;
    let red = 0, blue = 0, rx = 0, ry = 0, bx = 0, by = 0;
    forDisk(cx, cy, 3 * s, 14 * s, (r, g, b, dx, dy, x, y) => {
      for (const q of rob) if (Math.hypot(x - q.cx, y - q.cy) < 32 * s) return;
      if (r - b > 45 && r > 120 && g < 200) { red++; rx += dx; ry += dy; }
      else if (b - r > 50 && b > 150) { blue++; bx += dx; by += dy; }
    });
    const owner = red > blue ? 'red' : blue > red ? 'blue' : null;
    if (!owner) continue;
    const tx = owner === 'red' ? rx / red : bx / blue, ty = owner === 'red' ? ry / red : by / blue, tl = Math.hypot(tx, ty);
    const p = toW(cx, cy);
    out.push({ x: p.x, y: p.y, owner, ux: tl > 1 ? -tx / tl : 0, uy: tl > 1 ? -ty / tl : 0, trail: tl / s });
  }
  return out;
}

// ---------- 参数 ----------
const CFG = {
  farRange: 110, closeRange: 90, heatStance: false, heatMargin: 20, heatHyst: 10, heatFree: 25, retreatRange: 320, rangeGain: 0.7,
  raidHeat: 22, raidFoeHeat: 50, raidEvery: 6, raidMax: 4.5, raidExitHeat: 80,
  closeFireD: 140, tMax: 0.2, tMaxCold: 0.25, tHeatLow: 30,
  pFar: 0.5, pFarHot: 0.7, pClose: 0.3, farHeatCap: -1, heatCap: 92,
  alignFrac: 0, syncWander: true, vFrame: true, freshPoll: true, pollMargin: 0.004, pollStep: 0.0025, pollMax: 5, cvScale: 0, defModes: 'rand', modeHold: 1.2, priorH: 1, priorM: 2, zigP: 0.9, zigSpread: 0.5, minRangeGain: 0, syncFlip: 0.7, adaptive: false, midLo: 155, midWindow: 12, midShotsThr: 3, kiteGainIn: 12, kiteGainOut: 1, probeTime: 6, kiteRange: 168, kiteFireD: 215, pKite: 0.15, tKite: 0.32, kiteHeatCap: 95, swing: true, fastSwing: false, syncSwing: true, swingWaitMax: 0.035,
  wanderMin: 0.1, wanderRand: 0.25, cWanderMin: 0.03, cWanderRand: 0.09, spinWander: 0, ageCond: true, expWander: true, wanderMean: 0.03, wanderW: 1.0, riskW: 60, spinPenalty: 0.2, wallMargin: 75,
  barrelThreat: 220, barrelJit: 0.035,
  encodeLag: 0.010, returnLag: 0.004, fireLatency: 0.004,
  posTol: 0.9, posSpan: 0.4, thTol: 0.06, thSpan: 0.5,
  minGap: 0.052, leaseMs: 120, logEvery: 15, debugShots: false,
};

// ---------- 弹道几何 ----------
// 弹丸相对车心 (bx,by)、相对速度 (vx,vy)、装甲相位 ph、角速度 om：1=打中装甲，-1=被车体挡下，0=落空
function fate(bx, by, vx, vy, ph, om) {
  const sp = Math.hypot(vx, vy), ux = vx / sp, uy = vy / sp;
  const tca = -(bx * ux + by * uy), d2 = bx * bx + by * by - tca * tca;
  if (d2 > 33 * 33) return 0;
  const half = Math.sqrt(33 * 33 - d2), s1 = tca + half;
  if (s1 < 0) return 0;
  for (let s = Math.max(0, tca - half); s <= s1; s += 0.5) {
    const x = bx + ux * s, y = by + uy * s, a = ph + om * s / sp;
    const k = Math.round((Math.atan2(y, x) - a) / Q);
    for (let j = k - 1; j <= k + 1; j++) {
      const ang = a + j * Q, c = Math.cos(ang), sn = Math.sin(ang);
      const dr = Math.max(Math.abs(x * c + y * sn - ARMOR_R) - 2, 0), dt = Math.max(Math.abs(-x * sn + y * c) - 6, 0);
      if (dr * dr + dt * dt <= 4) return 1;
    }
    if (x * x + y * y <= 625) return -1;
  }
  return 0;
}
// 命中表：弹道横向偏移 off∈[-40,40]、装甲相对来弹方向的相位 ph∈[-π/4,π/4)
const HO = 40, HP = 48, HIT = new Uint8Array((2 * HO + 1) * HP);
for (let o = -HO; o <= HO; o++) for (let p = 0; p < HP; p++) {
  const ph = -Math.PI / 4 + (p + 0.5) * Q / HP;
  HIT[(o + HO) * HP + p] = fate(-60, o, 1000, 0, Math.PI + ph, 0) === 1 ? 1 : 0;
}
const hitAt = (off, ph) => {
  const o = Math.round(off);
  if (o < -HO || o > HO) return 0;
  let p = Math.floor((wrapQ(ph) + Math.PI / 4) / Q * HP); if (p >= HP) p = HP - 1; if (p < 0) p = 0;
  return HIT[(o + HO) * HP + p];
};

// ---------- 帧时间与自校准 ----------
const frameLog = [];
let framePeriod = 1 / 30;
function captureTime(id, tr) {
  frameLog.push({ id, tr });
  while (frameLog.length > 120) frameLog.shift();
  if (frameLog.length >= 15) { const a = frameLog[0], b = frameLog.at(-1); if (b.id > a.id) framePeriod = clamp((b.tr - a.tr) / (b.id - a.id), 1 / 40, 4); }
  let base = Infinity;
  for (let i = Math.max(0, frameLog.length - 40); i < frameLog.length; i++) base = Math.min(base, frameLog[i].tr - frameLog[i].id * framePeriod);
  return base + id * framePeriod - CFG.encodeLag;
}
const cmdLog = [];
let ownSpeed = 184;
const maxSpin = () => 8 * ownSpeed / 184;
function cmdVel(a) {
  const n = Math.max(1, Math.hypot(a.moveX, a.moveY)), x = a.moveX / n, y = a.moveY / n;
  const dem = Math.max(1, Math.hypot(x, y, a.spin));
  return { ux: x / dem, uy: y / dem, us: a.spin / dem };
}
function pushCmd(tApply, a) {
  const prev = cmdLog.at(-1);
  if (prev && prev.t1 > tApply) prev.t1 = tApply;
  const u = cmdVel(a);
  cmdLog.push({ t0: tApply, t1: tApply + Math.max(1, Math.round(a.durationMs * 60 / 1000)) / 60, ...u });
  while (cmdLog.length > 240) cmdLog.shift();
}
function cmdInt(ta, tb) {
  let dx = 0, dy = 0, da = 0;
  if (!running) return { dx, dy, da };
  for (let i = cmdLog.length - 1; i >= 0; i--) {
    const c = cmdLog[i];
    if (c.t1 <= ta) break;
    const lo = Math.max(ta, c.t0), hi = Math.min(tb, c.t1);
    if (hi > lo) { dx += c.ux * (hi - lo); dy += c.uy * (hi - lo); da += c.us * (hi - lo); }
  }
  return { dx, dy, da };
}
const ownObs = [];
let timeShift = 0, shiftN = 0;
function calibrateShift() {
  const pts = ownObs.slice(-90);
  if (pts.length < 30) return;
  const errAt = d => {
    let e = 0, num = 0, den = 0;
    for (let i = 1; i < pts.length; i++) {
      const a = pts[i - 1], b = pts[i];
      if (!a.ok || !b.ok) continue;
      const c = cmdInt(a.t + d, b.t + d), ox = b.x - a.x, oy = b.y - a.y;
      num += ox * c.dx + oy * c.dy; den += c.dx * c.dx + c.dy * c.dy;
      e += (ox - c.dx * ownSpeed) ** 2 + (oy - c.dy * ownSpeed) ** 2;
    }
    return { e, k: den > 1e-6 ? num / den : ownSpeed, den };
  };
  let best = Infinity, bestD = timeShift, bestK = ownSpeed, den = 0;
  for (let d = -0.08; d <= 0.1; d += 0.002) { const r = errAt(d); if (r.e < best) { best = r.e; bestD = d; bestK = r.k; den = r.den; } }
  for (let d = bestD - 0.002; d <= bestD + 0.002; d += 0.0004) { const r = errAt(d); if (r.e < best) { best = r.e; bestD = d; bestK = r.k; } }
  if (den < 0.02) return;
  timeShift = shiftN ? 0.6 * timeShift + 0.4 * bestD : bestD;
  shiftN++;
  if (bestK > 10 && bestK < 800) ownSpeed = 0.7 * ownSpeed + 0.3 * bestK;
}
// 出膛延迟自校准：看到自己新弹丸时，按它离出膛点的距离反推出膛时刻
const fireLatS = [];
function calibrateFire(b, t) {
  const req = shotReq.filter(r => !r.cal && r.t < t && t - r.t < 0.12);
  if (!req.length) return;
  const r = req[req.length - 1];
  if (shotReq.some(o => o !== r && Math.abs(o.t - r.t) < 0.13)) return; // 只用孤立的一发
  const o = ownAt(r.t), d = Math.hypot(b.x - o.x, b.y - o.y);
  if (d < 50 || d > 150) return;
  const lat = t - (d - MUZZLE) / BULLET - r.t;
  r.cal = true;
  if (lat < -0.03 || lat > 0.08) return;
  fireLatS.push(lat); if (fireLatS.length > 15) fireLatS.shift();
  if (fireLatS.length >= 3) { const s = [...fireLatS].sort((a, b) => a - b); CFG.fireLatency = s[s.length >> 1]; }
}

// ---------- 跟踪 ----------
function lineFit(pts, key, t0) {
  const n = pts.length;
  let st = 0, sv = 0;
  for (const p of pts) { st += p.t - t0; sv += p[key]; }
  const mt = st / n, mv = sv / n;
  let num = 0, den = 0;
  for (const p of pts) { const dt = p.t - t0 - mt; num += dt * (p[key] - mv); den += dt * dt; }
  const slope = den > 1e-12 ? num / den : 0;
  let worst = 0;
  for (const p of pts) worst = Math.max(worst, Math.abs(p[key] - (mv + slope * (p.t - t0 - mt))));
  return { v: mv - slope * mt, slope, worst };
}
function segmentFit(pts, keys, tol, maxSpan) {
  const n = pts.length, t0 = pts[n - 1].t;
  let best = null;
  for (let k = 2; k <= n; k++) {
    const seg = pts.slice(n - k);
    if (t0 - seg[0].t > maxSpan) break;
    const fits = keys.map(key => lineFit(seg, key, t0));
    if (fits.some(f => f.worst > tol)) break;
    best = { fits, n: k, span: t0 - seg[0].t };
  }
  if (best) return best;
  if (n >= 2) { const a = pts[n - 2], b = pts[n - 1], dt = Math.max(1e-3, b.t - a.t); return { fits: keys.map(key => ({ v: b[key], slope: (b[key] - a[key]) / dt })), n: 2, span: dt }; }
  return { fits: keys.map(key => ({ v: pts[n - 1][key], slope: 0 })), n: 1, span: 0 };
}
// 预测误差的经验分布：按时域分桶记录「当时匀速外推 → 实际」的偏差（位置与相位）
const HB = [0.05, 0.08, 0.11, 0.14, 0.18, 0.22, 0.27, 0.33, 0.4, 0.5], NE = 90;
// 再按「距对手上次变向的时长」分三档：刚变向的运动最可预测
const AG = [0.07, 0.15], ageCls = a => (a < AG[0] ? 0 : a < AG[1] ? 1 : 2);
// 误差在「当时速度方向」坐标系下记录（par 沿速度、per 垂直），慢速时记世界坐标：能学到对手是否保持速度
const errB = [0, 1, 2, 3].map(() => HB.map(() => ({ ex: new Float32Array(NE), ey: new Float32Array(NE), ep: new Float32Array(NE), mv: new Uint8Array(NE), n: 0 })));
class Track {
  constructor() { this.s = []; this.ths = []; this.snap = []; this.n = 0; this.th = null; this.om = 0; this.vx = 0; this.vy = 0; this.span = 0; }
  add(t, o) {
    this.s.push({ t, x: o.x, y: o.y }); if (this.s.length > 16) this.s.shift();
    if (o.phase !== null) {
      const last = this.ths.at(-1);
      let th = o.phase;
      if (last) { const pred = last.th + this.om * (t - last.t); th = pred + wrapQ(o.phase - pred); }
      this.ths.push({ t, th }); if (this.ths.length > 20) this.ths.shift();
    }
    this.n++;
    const f = segmentFit(this.s, ['x', 'y'], CFG.posTol, CFG.posSpan);
    this.t = t; this.x = f.fits[0].v; this.y = f.fits[1].v; this.vx = f.fits[0].slope; this.vy = f.fits[1].slope; this.span = f.span;
    if (this.ths.length) {
      const g = segmentFit(this.ths, ['th'], CFG.thTol, CFG.thSpan);
      this.th = g.fits[0].v; this.om = g.n >= 2 ? g.fits[0].slope : 0; this.thT = this.ths.at(-1).t; this.thN = g.n;
    }
    this.turret = o.turret; this.turT = t;
    // 误差统计
    for (let b = 0; b < HB.length; b++) {
      const want = t - HB[b];
      let best = null;
      for (const p of this.snap) if (Math.abs(p.t - want) < 0.017 && (!best || Math.abs(p.t - want) < Math.abs(best.t - want))) best = p;
      if (!best) continue;
      const h = t - best.t, sc = HB[b] / h;
      const k = CFG.cvScale, ex = (o.x - (best.x + best.vx * h * k)) * sc, ey = (o.y - (best.y + best.vy * h * k)) * sc;
      const ep = o.phase === null || best.th === null ? 0 : wrapQ(o.phase - (best.th + best.om * h)) * sc;
      const sp = Math.hypot(best.vx, best.vy), mv = CFG.vFrame && sp > 25 ? 1 : 0;
      const ux = mv ? best.vx / sp : 1, uy = mv ? best.vy / sp : 0;
      const a1 = ex * ux + ey * uy, a2 = -ex * uy + ey * ux;
      for (const E of [errB[ageCls(best.age)][b], errB[3][b]]) { const j = E.n++ % NE; E.ex[j] = a1; E.ey[j] = a2; E.ep[j] = ep; E.mv[j] = mv; }
    }
    this.snap.push({ t, age: this.span, x: this.x, y: this.y, vx: this.vx, vy: this.vy, th: this.th === null ? null : this.th, om: this.om });
    while (this.snap.length && t - this.snap[0].t > 0.55) this.snap.shift();
  }
  at(t) { const dt = (t - this.t) * CFG.cvScale; return { x: clamp(this.x + this.vx * dt, INSET, FW - INSET), y: clamp(this.y + this.vy * dt, INSET, FH - INSET) }; }
  phaseAt(t) { return this.th === null ? 0 : this.th + this.om * (t - this.thT); }
}

// ---------- 状态 ----------
const foe = new Track();
const own = { t: 0, x: SPAWN[ME].x, y: SPAWN[ME].y, th: null, thT: 0, n: 0 };
let lastCapT = 0, nextIsCapture = true;
let lastFrame = -1, frames = 0, decodeMs = 0, running = false, startT = 0, matchStart = 0;
let heat = { me: 0, foe: 0, t: 0 }, hp = { me: 1, foe: 1 };
const shotReq = [];
let lastShot = -1, nShots = 0;
let turretSim = SPAWN[ME].turret, turretT = 0, sentAim = turretSim, prevAim = turretSim, sentApply = 0;
let bullets = []; // 跟踪中的弹丸 {x,y,t,ux,uy,owner,n,x0,y0}
let robotsPx = null, lostCount = 0, useFallback = false;
const stat = { polls: 0, fresh: 0, shots: 0, pSum: 0, risk: 0, loops: 0, raids: 0, hot: 0 };

function ownAt(t) {
  const d = cmdInt(own.t, t);
  return { x: clamp(own.x + d.dx * ownSpeed, INSET, FW - INSET), y: clamp(own.y + d.dy * ownSpeed, INSET, FH - INSET) };
}
function ownPhaseAt(t) { return own.th === null ? 0 : own.th + cmdInt(own.thT, t).da * maxSpin(); }
function heatNow(t) {
  const cooled = Math.max(0, heat.me - 20 * (t - heat.t));
  let pend = 0;
  for (const r of shotReq) if (r.t > heat.t - 0.05) pend++;
  return cooled + 10 * pend;
}

// ---------- 读图 ----------
function perceive(obs) {
  const img = obs.image;
  let ok = false;
  if (!useFallback) {
    try {
      b64decode(img.base64);
      ok = parseHeaders() && JD.w === img.width && JD.h === img.height;
    } catch { ok = false; }
  }
  if (!ok) {
    // 退回宿主提供的整帧解码
    const p = lab.pixels(obs);
    JD.w = p.width; JD.h = p.height; JD.rgb = p.data; JD.nm = 0; JD.epoch++;
    V.w = p.width; V.h = p.height; V.s = p.width / FW; V.top = Math.round(HUD * V.s);
    useFallback = true;
    return searchAll(true);
  }
  V.w = JD.w; V.h = JD.h; V.s = JD.w / FW; V.top = Math.round(HUD * V.s);
  const s = V.s;
  if (!robotsPx) { decodeFrame(true, 0); return searchAll(false); }
  JD.mark.fill(0);
  for (const side of ['red', 'blue']) {
    const r = robotsPx[side]; if (!r) continue;
    const R = (62 + r.slack) * s;
    markRect(r.cx - R, r.cy - R, r.cx + R, r.cy + R);
  }
  for (const hx of [26, FW - 334]) markRect(hx * s, 38 * s, (hx + 310) * s, 66 * s);
  const hot = decodeFrame(false, 4);
  stat.hot += hot.length;
  const out = { robots: {} };
  for (const side of ['red', 'blue']) {
    const r = robotsPx[side];
    const m = r ? measureRobot(side, r.cx, r.cy) : null;
    if (m) out.robots[side] = m;
  }
  if (!out.robots.red || !out.robots.blue) { lostCount++; robotsPx = null; }
  out.hud = { red: readHud('red'), blue: readHud('blue') };
  out.bullets = hot.length > 300 ? [] : findBullets(out.robots);
  return out;
}
function searchAll(fallback) {
  const robots = searchRobots();
  return { robots, hud: { red: readHud('red'), blue: readHud('blue') }, bullets: fallback ? [] : findBullets(robots) };
}

function updateBullets(list, t) {
  for (const b of bullets) b.seen = false;
  for (const d of list) {
    let m = null, bd = 1e9;
    for (const b of bullets) {
      if (b.seen || b.owner !== d.owner) continue;
      const el = (t - b.t) * BULLET, ex = d.x - (b.x + b.ux * el), ey = d.y - (b.y + b.uy * el);
      const along = ex * b.ux + ey * b.uy, across = Math.abs(-ex * b.uy + ey * b.ux);
      if (across < 10 && Math.abs(along) < 30) { const e = across * 3 + Math.abs(along); if (e < bd) { bd = e; m = b; } }
    }
    if (m) {
      const dx = d.x - m.x0, dy = d.y - m.y0, l = Math.hypot(dx, dy);
      if (l > 20) { m.ux = dx / l; m.uy = dy / l; }
      m.x = d.x; m.y = d.y; m.t = t; m.seen = true; m.n++;
    } else {
      // 新弹丸：方向优先取「发射方当时位置 → 弹丸」，与拖尾方向矛盾时取拖尾
      const shooter = d.owner === ME ? own : (foe.n ? foe : null);
      let ux = d.ux, uy = d.uy;
      if (shooter && shooter.x !== undefined) {
        const sx = d.x - shooter.x, sy = d.y - shooter.y, l = Math.hypot(sx, sy);
        if (l > 45 && (d.ux * sx + d.uy * sy) / l > 0.9) { ux = sx / l; uy = sy / l; }
        else if (!d.ux && !d.uy && l > 1) { ux = sx / l; uy = sy / l; }
      }
      const nb = { x: d.x, y: d.y, x0: d.x, y0: d.y, t, ux, uy, owner: d.owner, n: 1, seen: true };
      bullets.push(nb);
      if (d.owner === ME) calibrateFire(nb, t);
    }
  }
  bullets = bullets.filter(b => {
    if (b.seen) return true;
    const el = (t - b.t) * BULLET, x = b.x + b.ux * el, y = b.y + b.uy * el;
    return t - b.t < 0.5 && x > -5 && x < FW + 5 && y > -5 && y < FH + 5;
  });
}

function ingest(obs) {
  if (obs.frameId === lastFrame) return false;
  lastFrame = obs.frameId;
  const tRecv = clock(), t0 = performance.now();
  const a = perceive(obs);
  decodeMs += performance.now() - t0; frames++;
  const tEst = captureTime(obs.frameId, tRecv), t = tEst + timeShift;
  lastCapT = t;
  const mine = a.robots[ME], his = a.robots[FOE];
  if (mine) {
    if (!running && Math.hypot(mine.x - SPAWN[ME].x, mine.y - SPAWN[ME].y) > 2.5) { running = true; startT = t; }
    const ok = running && mine.x > INSET + 2 && mine.x < FW - INSET - 2 && mine.y > INSET + 2 && mine.y < FH - INSET - 2 && !(his && Math.hypot(mine.x - his.x, mine.y - his.y) < 60);
    ownObs.push({ t: tEst, x: mine.x, y: mine.y, ok }); if (ownObs.length > 120) ownObs.shift();
    if (running && frames % 15 === 0) calibrateShift();
    own.t = t; own.x = mine.x; own.y = mine.y; own.n++;
    if (mine.phase !== null) { own.th = mine.phase; own.thT = t; }
    if (mine.turret !== null && Math.abs(wrap(mine.turret - turretAt(t))) > 0.3) { turretSim = mine.turret; turretT = t; }
  }
  if (his) foe.add(t, his);
  const sl = Math.min(40, 6 + 200 * Math.min(0.2, framePeriod));
  robotsPx = mine && his ? { [ME]: { cx: mine.cx, cy: mine.cy, slack: sl }, [FOE]: { cx: his.cx, cy: his.cy, slack: sl } } : null;
  heat = { me: a.hud[ME].heat, foe: a.hud[FOE].heat, t };
  if (mine && his) noteFoeHeat(a.hud[FOE].heat, t, Math.hypot(mine.x - his.x, mine.y - his.y));
  if (running && hp.me - a.hud[ME].hp > 0.02) noteDefHit(t, Math.max(1, Math.round((hp.me - a.hud[ME].hp) / 0.05)));
  hp = { me: a.hud[ME].hp, foe: a.hud[FOE].hp };
  if (running) updateBullets(a.bullets, t);
  return true;
}

// ---------- 炮塔模型 ----------
const slew = (from, to, dt) => wrap(from + clamp(wrap(to - from), -TURRET_RATE * dt, TURRET_RATE * dt));
function turretAt(t) {
  let th = turretSim, tt = turretT;
  if (tt < sentApply) { const mid = Math.min(t, sentApply); th = slew(th, prevAim, Math.max(0, mid - tt)); tt = mid; }
  return slew(th, sentAim, Math.max(0, t - tt));
}
function commitTurret(t) { turretSim = turretAt(t); turretT = t; }

// ---------- 瞄准 ----------
// 在 tFire 出膛：返回各横向偏移的命中概率、最优偏移与瞄准点
const PD = new Float32Array(2 * HO + 1);
function aimSolve(tFire) {
  const c = ownAt(tFire);
  let tau = 0.2, P = foe.at(tFire + tau);
  for (let it = 0; it < 4; it++) { P = foe.at(tFire + tau); tau = Math.max(0, Math.hypot(P.x - c.x, P.y - c.y) - MUZZLE - 24) / BULLET; }
  const dist = Math.hypot(P.x - c.x, P.y - c.y) || 1, ux = (P.x - c.x) / dist, uy = (P.y - c.y) / dist, nx = -uy, ny = ux;
  const T = tFire + tau - foe.t;
  const ph0 = wrapQ(foe.phaseAt(tFire + tau) - Math.atan2(-uy, -ux) + foe.om * 0.026);
  let b = 0; while (b < HB.length - 1 && Math.abs(HB[b + 1] - T) < Math.abs(HB[b] - T)) b++;
  let E = errB[CFG.ageCond ? ageCls(foe.span) : 3][b];
  if (E.n < 20) E = errB[3][b];
  const N = Math.min(E.n, NE), sc = T / HB[b];
  PD.fill(0);
  let wsum = 0;
  const fsp = Math.hypot(foe.vx, foe.vy), fmv = CFG.vFrame && fsp > 25 ? 1 : 0;
  const fux = fmv ? foe.vx / fsp : 1, fuy = fmv ? foe.vy / fsp : 0;
  let match = 0;
  for (let i = 0; i < N; i++) if (E.mv[i] === fmv) match++;
  if (match >= 12) {
    for (let i = 0; i < N; i++) {
      if (E.mv[i] !== fmv) continue;
      const wx = E.ex[i] * fux - E.ey[i] * fuy, wy = E.ex[i] * fuy + E.ey[i] * fux;
      const lat = (wx * nx + wy * ny) * sc, eph = E.ep[i] * sc;
      for (let o = -HO; o <= HO; o++) PD[o + HO] += hitAt(o - lat, ph0 + eph);
    }
    wsum = match;
  } else {
    const sg = 2 + 30 * T;
    for (let k = -2; k <= 2; k++) {
      const lat = k * sg * 0.7, w = Math.exp(-0.5 * (k * 0.7) ** 2);
      for (let o = -HO; o <= HO; o++) PD[o + HO] += w * hitAt(o - lat, ph0);
      wsum += w;
    }
  }
  let best = 0, bo = 0;
  for (let o = -HO; o <= HO; o++) {
    const v = (PD[o + HO] * 2 + (o > -HO ? PD[o + HO - 1] : 0) + (o < HO ? PD[o + HO + 1] : 0)) / 4 / wsum;
    PD[o + HO] = PD[o + HO] / wsum;
    if (v > best) { best = v; bo = o; }
  }
  return { c, P, ux, uy, nx, ny, dist, tau, T, best, bo, ph0, A: { x: P.x + nx * bo, y: P.y + ny * bo } };
}
// 某炮塔角对应的命中概率
function pForAngle(sol, ang) {
  const tx = Math.cos(ang), ty = Math.sin(ang);
  const along = (sol.P.x - sol.c.x) * tx + (sol.P.y - sol.c.y) * ty;
  if (along <= 0) return 0;
  const qx = sol.c.x + tx * along - sol.P.x, qy = sol.c.y + ty * along - sol.P.y;
  const off = qx * sol.nx + qy * sol.ny, o = Math.round(off);
  return o < -HO || o > HO ? 0 : PD[o + HO];
}

// ---------- 交战姿态 ----------
let stance = 'far', raidT = -99, lastRaidEnd = 0;
// 对手开火画像：热量条跳升即一次出膛，按当时距离归档
const foeFire = { mid: 0, close: 0, midT: [], lastHeat: 0, lastT: 0 };
let mode = 'probe', modeT = 0;
function noteFoeHeat(h, t, D) {
  if (foeFire.lastT) {
    const dh = h - foeFire.lastHeat + 20 * (t - foeFire.lastT);
    if (dh >= 6 && running) {
      const n = Math.max(1, Math.round(dh / 10));
      if (D < 220) noteDefShot(t, n);
      if (D >= CFG.midLo) { foeFire.mid += n; for (let i = 0; i < n; i++) foeFire.midT.push(t); } else foeFire.close += n;
    }
  }
  foeFire.lastHeat = h; foeFire.lastT = t;
  while (foeFire.midT.length && t - foeFire.midT[0] > CFG.midWindow) foeFire.midT.shift();
}
function updateMode(t) {
  if (!CFG.adaptive) { mode = 'close'; return; }
  if (!running) return;
  if (!modeT) modeT = t;
  if (mode === 'probe') {
    if (foeFire.midT.length >= CFG.midShotsThr) mode = 'close';
    else if (t - modeT > CFG.probeTime) mode = 'kite';
  } else if (mode === 'kite' && foeFire.midT.length >= CFG.midShotsThr) mode = 'close';
}
function updateStance(t) {
  updateMode(t);
  if (CFG.adaptive && mode !== 'close') {
    const h0 = heatNow(t), D0 = Math.hypot(foe.x - own.x, foe.y - own.y);
    return { D: D0, pref: CFG.kiteRange, kite: true };
  }
  const h = heatNow(t), D = Math.hypot(foe.x - own.x, foe.y - own.y);
  if (CFG.heatStance) {
    // 按双方剩余热量决定是否近身：我方连发余量不少于对手时贴近，否则退远冷却
    const adv = heat.foe - h;
    if (stance === 'far' && (adv >= -CFG.heatMargin || h <= CFG.heatFree)) stance = 'close';
    else if (stance === 'close' && adv < -CFG.heatMargin - CFG.heatHyst && h > CFG.heatFree) stance = 'far';
    return { D, pref: stance === 'close' ? CFG.closeRange : CFG.retreatRange };
  }
  if (CFG.minRangeGain && stance === 'far') return { D, pref: CFG.farRange, kite: true, gIn: CFG.minRangeGain, gOut: CFG.rangeGain };
  if (stance === 'far') {
    if (h <= CFG.raidHeat && (heat.foe >= CFG.raidFoeHeat || t - lastRaidEnd > CFG.raidEvery)) { stance = 'close'; raidT = t; stat.raids++; }
  } else if (h >= CFG.raidExitHeat || t - raidT > CFG.raidMax) { stance = 'far'; lastRaidEnd = t; }
  return { D, pref: stance === 'close' ? CFG.closeRange : CFG.farRange };
}

// ---------- 走位与防御 ----------
let wander = { c: 1, s: 0, until: 0, spin: 0 }, zigSign = 1;
// ---------- 防守风格在线选择（Thompson 采样）----------
// 对手每次出膛由其热量条跳升得知，我方中弹由血条下降得知；按出膛时所用风格统计对手命中率，择优使用
const defStats = {};
let defMode = 'rand', defSince = -1;
const modeLog = [];
function gammaS(k) {
  if (k < 1) return gammaS(k + 1) * Math.pow(Math.random(), 1 / k);
  const d = k - 1 / 3, c = 1 / Math.sqrt(9 * d);
  for (;;) {
    let x, v;
    do { const u1 = Math.random() || 1e-9, u2 = Math.random(); x = Math.sqrt(-2 * Math.log(u1)) * Math.cos(TAU * u2); v = 1 + c * x; } while (v <= 0);
    v = v * v * v; const u = Math.random();
    if (u < 1 - 0.0331 * x ** 4 || Math.log(u) < 0.5 * x * x + d * (1 - v + Math.log(v))) return d * v;
  }
}
const betaS = (a, b) => { const x = gammaS(a), y = gammaS(b); return x / (x + y); };
function modeAt(t) { for (let i = modeLog.length - 1; i >= 0; i--) if (modeLog[i].t <= t) return modeLog[i].m; return defMode; }
function pickDefMode(t) {
  const modes = CFG.defModes.split(',');
  if (defSince < 0) { defMode = modes[0]; defSince = t; modeLog.push({ t, m: defMode }); return; }
  if (modes.length < 2 || t - defSince < CFG.modeHold) return;
  let best = defMode, bv = 9;
  for (const m of modes) { const st = defStats[m] ?? { s: 0, h: 0 }; const v = betaS(CFG.priorH + st.h, CFG.priorM + Math.max(0, st.s - st.h)); if (v < bv) { bv = v; best = m; } }
  defMode = best; defSince = t; modeLog.push({ t, m: defMode });
  if (modeLog.length > 200) modeLog.shift();
}
function noteDefShot(t, n) { const m = modeAt(t - 0.02); (defStats[m] ??= { s: 0, h: 0 }).s += n; }
function noteDefHit(t, n) { const m = modeAt(t - 0.06); (defStats[m] ??= { s: 0, h: 0 }).h += n; }
function threats(t, M) {
  const th = [];
  for (const b of bullets) {
    if (b.owner !== FOE) continue;
    const el = (t - b.t) * BULLET, x = b.x + b.ux * el, y = b.y + b.uy * el;
    const rx = M.x - x, ry = M.y - y, along = rx * b.ux + ry * b.uy, across = Math.abs(rx * b.uy - ry * b.ux);
    if (along < -34 || across > 40 + ownSpeed * along / BULLET) continue;
    th.push({ x, y, ux: b.ux, uy: b.uy, w: 1 });
  }
  const D = Math.hypot(foe.x - M.x, foe.y - M.y);
  if (foe.n && D < CFG.barrelThreat && foe.turret !== null && foe.turret !== undefined) {
    const F = foe.at(t);
    for (const [da, w] of [[0, 0.5], [CFG.barrelJit, 0.25], [-CFG.barrelJit, 0.25]]) {
      const a = foe.turret + da, c = Math.cos(a), s = Math.sin(a);
      th.push({ x: F.x + c * MUZZLE, y: F.y + s * MUZZLE, ux: c, uy: s, w });
    }
  }
  return th;
}
function evalMove(mx, my, spin, M, ph, th, ctx) {
  const u = cmdVel({ moveX: mx, moveY: my, spin });
  const vx = u.ux * ownSpeed, vy = u.uy * ownSpeed, om = u.us * maxSpin();
  const x1 = clamp(M.x + vx * 0.25, INSET, FW - INSET), y1 = clamp(M.y + vy * 0.25, INSET, FH - INSET);
  let c = -CFG.wanderW * (mx * wander.c + my * wander.s) + CFG.spinPenalty * Math.abs(spin - wander.spin);
  const g = CFG.wallMargin;
  if (x1 < INSET + g) c += 4 * ((INSET + g - x1) / g) ** 2;
  if (x1 > FW - INSET - g) c += 4 * ((x1 - (FW - INSET - g)) / g) ** 2;
  if (y1 < INSET + g) c += 4 * ((INSET + g - y1) / g) ** 2;
  if (y1 > FH - INSET - g) c += 4 * ((y1 - (FH - INSET - g)) / g) ** 2;
  const D1 = Math.hypot(ctx.F.x - x1, ctx.F.y - y1);
  if (ctx.kite) { const e = (D1 - ctx.pref) / 100; c += (e < 0 ? (ctx.gIn ?? CFG.kiteGainIn) : (ctx.gOut ?? CFG.kiteGainOut)) * e * e; }
  else c += CFG.rangeGain * ((D1 - ctx.pref) / 100) ** 2;
  let risk = 0;
  const evx = (x1 - M.x) * 4, evy = (y1 - M.y) * 4;
  for (const b of th) {
    const rx = b.x - M.x, ry = b.y - M.y;
    for (const [e, w] of [[0, 0.5], [3.5, 0.25], [-3.5, 0.25]]) {
      if (fate(rx - b.uy * e, ry + b.ux * e, b.ux * BULLET - evx, b.uy * BULLET - evy, ph, om) === 1) risk += w * b.w;
    }
  }
  return { c: c + risk * CFG.riskW, risk, mx, my, spin };
}
function chooseMove(t, ctx) {
  const M = ownAt(t + 0.008), ph = ownPhaseAt(t + 0.008);
  const F = foe.at(t);
  pickDefMode(t);
  const base0 = Math.atan2(F.y - M.y, F.x - M.x);
  if (defMode === 'zig') {
    // 之字：每个采样边界（大概率）反向横移，令按匀速外推的对手系统性偏向错误一侧
    if ((nextIsCapture && Math.random() < CFG.zigP) || t > wander.until) {
      zigSign = -zigSign;
      const a = base0 + zigSign * (Q + (Math.random() - 0.5) * CFG.zigSpread);
      wander = { c: Math.cos(a), s: Math.sin(a), until: t + 0.12, spin: 0 };
    }
  } else if (defMode === 'hold' ? t > wander.until : CFG.syncWander ? (nextIsCapture && Math.random() < CFG.syncFlip) || t > wander.until + 0.25 : t > wander.until) {
    const base = base0, a = base + (Math.random() < 0.5 ? 1 : -1) * (Q + (Math.random() - 0.5) * 1.5);
    const close = ctx.pref < 200 || Math.hypot(F.x - M.x, F.y - M.y) < 200;
    const dur = defMode === 'hold' ? 0.1 + Math.random() * 0.25 : CFG.expWander ? clamp(-CFG.wanderMean * Math.log(1 - Math.random()), 0.016, 0.5) : close ? CFG.cWanderMin + Math.random() * CFG.cWanderRand : CFG.wanderMin + Math.random() * CFG.wanderRand;
    wander = { c: Math.cos(a), s: Math.sin(a), until: t + dur, spin: close ? (Math.random() * 2 - 1) * CFG.spinWander : 0 };
  }
  const th = running ? threats(t, M) : [];
  ctx.F = F;
  let best = null;
  const N = 16;
  for (let i = 0; i <= N; i++) {
    const e = i < N ? evalMove(Math.cos(i * TAU / N), Math.sin(i * TAU / N), wander.spin, M, ph, th, ctx) : evalMove(0, 0, wander.spin, M, ph, th, ctx);
    if (!best || e.c < best.c) best = e;
  }
  if (th.length && best.risk > 0.05) {
    for (const spin of [1, -1, 0.5, -0.5]) {
      for (let i = 0; i <= N; i += 2) {
        const e = i < N ? evalMove(Math.cos(i * TAU / N), Math.sin(i * TAU / N), spin, M, ph, th, ctx) : evalMove(0, 0, spin, M, ph, th, ctx);
        if (e.c < best.c) best = e;
      }
    }
  }
  stat.risk += best.risk;
  return best;
}

// ---------- 主循环 ----------
function aimPointFor(sol, A) {
  // 瞄准点放在弹道上，超出场地时沿线收回
  let k = 1;
  const dx = A.x - sol.c.x, dy = A.y - sol.c.y;
  if (A.x < 1) k = Math.min(k, (1 - sol.c.x) / dx); if (A.x > FW - 1) k = Math.min(k, (FW - 1 - sol.c.x) / dx);
  if (A.y < 1) k = Math.min(k, (1 - sol.c.y) / dy); if (A.y > FH - 1) k = Math.min(k, (FH - 1 - sol.c.y) / dy);
  return { aimX: clamp((sol.c.x + dx * k) / FW, 0, 1), aimY: clamp((sol.c.y + dy * k) / FH, 0, 1) };
}
function wantFire(t, sol, ctx, p) {
  if (!running || foe.n < 3 || t - foe.t > 0.15 || t - own.t > 0.15) return false;
  if (lastShot >= 0 && t - lastShot < CFG.minGap) return false;
  const h = heatNow(t);
  if (h + 10 > CFG.heatCap) return false;
  if (CFG.adaptive && mode !== 'close' && ctx.D >= CFG.closeFireD) return ctx.D < CFG.kiteFireD && p >= CFG.pKite && sol.T <= CFG.tKite && h + 10 <= CFG.kiteHeatCap;
  if (ctx.D < CFG.closeFireD) return p >= CFG.pClose && sol.T <= (h <= CFG.tHeatLow ? CFG.tMaxCold : CFG.tMax);
  if (stance === 'close') return false;
  if (h > CFG.farHeatCap) return false;
  return p >= (h > 30 ? CFG.pFarHot : CFG.pFar);
}
const dbgLines = [];
// 新帧往往在两个控制边界之间编码完成：act 返回后若还是旧帧，就在下个边界前用 observe 主动取一次，
// 让决策赶上下一个边界生效（信息时延少一个控制周期）
let actBoundary = 0;
async function pollFresh() {
  if (!CFG.freshPoll || !running || obs.frameId !== lastFrame) return;
  const deadline = actBoundary + 1 / 60 - CFG.pollMargin;
  for (let k = 0; k < CFG.pollMax && clock() < deadline; k++) {
    const until = Math.min(deadline, clock() + CFG.pollStep);
    while (clock() < until) { /* 等待编码完成 */ }
    const o = await lab.observe(); stat.polls++;
    if (o.frameId !== lastFrame) { obs = o; stat.fresh++; return; }
  }
}
let obs = await lab.observe();
matchStart = clock();
let fails = 0, lastLog = 0;
while (clock() - matchStart < 70) {
  try {
    ingest(obs);
    let t = clock();
    commitTurret(t);
    const ctx = updateStance(t);
    const mv = foe.n && own.n ? chooseMove(t, ctx) : { mx: 0, my: 0, spin: 0 };
    let action = { moveX: mv.mx, moveY: mv.my, spin: mv.spin, aimX: 0.5, aimY: 0.5, durationMs: CFG.leaseMs };
    let sol = null, swingTo = null, fastSwing = false;
    if (foe.n && own.n) {
      sol = aimSolve(t + 0.012);
      // 近距离：平时炮口对车心（诱使对方按车心炮线摆相位），开火时再甩到最佳点
      const decoy = CFG.swing && ctx.D < 170 && running;
      // 已具备开火条件时，这一次 act 直接甩到最佳点（少等一个控制周期）
      fastSwing = decoy && (CFG.fastSwing || (CFG.syncSwing && nextIsCapture)) && wantFire(t + 0.012, sol, ctx, sol.best);
      const A = decoy && !fastSwing ? sol.P : sol.A;
      Object.assign(action, aimPointFor(sol, A));
      if (decoy && !fastSwing) swingTo = sol;
    }
    const tApply = clock();
    obs = await lab.act(action);
    actBoundary = clock();
    const tr = clock() - CFG.returnLag;
    // 采样边界相位：刚生效的这个控制边界若是采样边界，下一个就是中间边界
    { const ph = (((tr - lastCapT) % framePeriod) + framePeriod) % framePeriod / framePeriod; nextIsCapture = !(ph < 0.25 || ph > 0.75); }
    pushCmd(Math.min(tr, tApply + 0.017), action);
    commitTurret(tr);
    { const c = ownAt(tr); prevAim = sentAim; sentAim = Math.atan2(action.aimY * FH - c.y, action.aimX * FW - c.x); sentApply = tr; }
    // 开火判断：act 返回时瞄准已生效
    t = clock();
    if (foe.n && own.n) {
      let s2 = aimSolve(t + CFG.fireLatency);
      let p = pForAngle(s2, turretAt(t + CFG.fireLatency));
      if (fastSwing) {
        const need = Math.abs(wrap(sentAim - turretAt(clock()))) / TURRET_RATE;
        const until = performance.now() + Math.min(CFG.swingWaitMax, need) * 1000;
        while (performance.now() < until) { /* 等炮塔转到位 */ }
        t = clock();
        s2 = aimSolve(t + CFG.fireLatency);
        p = pForAngle(s2, turretAt(t + CFG.fireLatency));
      } else if (swingTo && (!CFG.syncSwing || nextIsCapture) && wantFire(t, s2, ctx, s2.best)) {
        // 甩炮：下达最佳瞄准点，等炮塔到位后立刻开火
        const act2 = { ...action, ...aimPointFor(s2, s2.A) };
        obs = await lab.act(act2);
        const tr2 = clock() - CFG.returnLag;
        pushCmd(tr2, act2); commitTurret(tr2);
        const c = ownAt(tr2); prevAim = sentAim; sentAim = Math.atan2(act2.aimY * FH - c.y, act2.aimX * FW - c.x); sentApply = tr2;
        const need = Math.abs(wrap(sentAim - turretAt(tr2))) / TURRET_RATE;
        const until = performance.now() + Math.min(CFG.swingWaitMax, need) * 1000;
        while (performance.now() < until) { /* 等炮塔转到位 */ }
        t = clock();
        s2 = aimSolve(t + CFG.fireLatency);
        p = pForAngle(s2, turretAt(t + CFG.fireLatency));
      }
      if (wantFire(t, s2, ctx, p) && (!CFG.alignFrac || p >= CFG.alignFrac * s2.best)) {
        lastShot = clock(); shotReq.push({ t: lastShot }); nShots++; stat.shots++; stat.pSum += p;
        while (shotReq.length > 40) shotReq.shift();
        if (CFG.debugShots) dbgLines.push(`${p.toFixed(2)},${Math.round(ctx.D)},${swingTo ? 1 : 0},${s2.best.toFixed(2)},${s2.T.toFixed(3)},${Math.round(heatNow(t))},${s2.bo},${s2.ph0.toFixed(3)},${foe.span.toFixed(3)},${(() => { const tt = turretAt(t + CFG.fireLatency), tx = Math.cos(tt), ty = Math.sin(tt), al = (s2.P.x - s2.c.x) * tx + (s2.P.y - s2.c.y) * ty; return ((s2.c.x + tx * al - s2.P.x) * s2.nx + (s2.c.y + ty * al - s2.P.y) * s2.ny).toFixed(1); })()},${turretAt(t + CFG.fireLatency).toFixed(4)},${s2.P.x.toFixed(1)},${s2.P.y.toFixed(1)},${s2.c.x.toFixed(1)},${s2.c.y.toFixed(1)}`);
        obs = await lab.fire();
      }
    }
    stat.loops++;
    await pollFresh();
    fails = 0;
    if (CFG.debugShots && dbgLines.length >= 10) { await lab.log('D' + dbgLines.join(';')); dbgLines.length = 0; }
    if (t - lastLog > CFG.logEvery) {
      lastLog = t;
      await lab.log(`${ME} t=${(t - matchStart).toFixed(1)} run=${running} shots=${nShots} p=${(stat.pSum / Math.max(1, stat.shots)).toFixed(2)} hp=${hp.me.toFixed(2)}/${hp.foe.toFixed(2)} heat=${heatNow(t).toFixed(0)}/${heat.foe.toFixed(0)} raids=${stat.raids} poll=${stat.fresh}/${stat.polls} def=${Object.entries(defStats).map(([k, v]) => k + ':' + v.h + '/' + v.s).join(',')} mode=${mode} ff=${foeFire.mid}/${foeFire.close} frames=${frames} loops=${stat.loops} dec=${(decodeMs / Math.max(1, frames)).toFixed(1)}ms v=${ownSpeed.toFixed(0)} shift=${(timeShift * 1000).toFixed(1)} fl=${(CFG.fireLatency * 1000).toFixed(1)} fb=${useFallback} lost=${lostCount} bul=${bullets.length}`);
    }
  } catch (e) {
    if (++fails > 15) break;
    if (fails === 1) { try { await lab.log('ERR ' + String(e && e.stack || e).slice(0, 300)); } catch { } }
    try { await lab.sleep(10); obs = await lab.observe(); } catch { }
  }
}
}
