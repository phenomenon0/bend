//TABLES lnc
// x32_pow: (f32)pow((double)x, (double)y), x32.h x32_yint / x32_ln / x32_pow

// 0: not an integer, 1: odd integer, 2: even integer (y finite)
fn x32w_yint(a: u32) -> u32 {
  let e = i32(a >> 23u) - 150;
  if (a == 0u || e >= 1) {
    return 2u;
  }
  if (e < -23) {
    return 0u;
  }
  let m = (a & 0x7fffffu) | 0x800000u;
  let s = u32(-e);
  if ((m & ((1u << s) - 1u)) != 0u) {
    return 0u;
  }
  return select(2u, 1u, ((m >> s) & 1u) == 1u);
}

// ln x for finite x > 0 (bits a), a signed 128-bit Q120: vec4(hi.hi, hi.lo, lo.hi, lo.lo)
fn x32w_ln(a: u32) -> vec4<u32> {
  var s: i32;
  var m: u32;
  if (a >= 0x800000u) {
    m = (a & 0x7fffffu) | 0x800000u;
    s = i32(a >> 23u) - 150;
  } else {
    let z = countLeadingZeros(a) - 8u;
    m = a << z;
    s = -149 - i32(z);
  }
  let j = ((m + 0x10000u) >> 17u) - 64u;
  let cm = (64u + j) << 17u;
  let den = m + cm;
  let wneg = m < cm;
  let num = select(m - cm, cm - m, wneg);
  // W = floor(num 2^71 / den) = x32.h's q1 << 32 | (r1 << 32) / den (q1 < 2^32), |w| Q71
  var r = num;
  var W = vec2<u32>(0u, 0u);
  for (var i = 0; i < 71; i++) {
    r = r << 1u;
    W = vec2<u32>((W.x << 1u) | (W.y >> 31u), W.y << 1u);
    if (r >= den) {
      r -= den;
      W.y |= 1u;
    }
  }
  let w2 = x32w_shr(x32w_mulhi(W, W), 14u);
  let S = x32w_add(vec2<u32>(0x55555555u, 0x55555555u),
    x32w_mulhi(w2, x32w_add(vec2<u32>(0x33333333u, 0x33333333u), x32w_mulhi(w2, vec2<u32>(0x24924924u, 0x92492492u)))));
  let at = x32w_add(W, x32w_mulhi(W, x32w_mulhi(w2, S)));
  var ahi = x32w_shr(at, 14u);
  var alo = x32w_shl(at, 50u);
  if (wneg) {
    ahi = x32w_add(vec2<u32>(~ahi.x, ~ahi.y), vec2<u32>(0u, select(0u, 1u, x32w_isz(alo))));
    alo = x32w_neg(alo);
  }
  let n = s + 23;
  let un = vec2<u32>(0u, u32(abs(n)));
  var nlo = x32w_mullo(un, vec2<u32>(0xabc9e3b3u, 0x9803f2f7u));
  var nhi = x32w_add(x32w_mullo(un, vec2<u32>(0x00b17217u, 0xf7d1cf79u)), x32w_mulhi(un, vec2<u32>(0xabc9e3b3u, 0x9803f2f7u)));
  if (n < 0) {
    nhi = x32w_add(vec2<u32>(~nhi.x, ~nhi.y), vec2<u32>(0u, select(0u, 1u, x32w_isz(nlo))));
    nlo = x32w_neg(nlo);
  }
  let c = x32w_lnc[j];
  let l = x32w_add(nlo, c.zw);
  let h = x32w_add(x32w_add(nhi, c.xy), vec2<u32>(0u, select(0u, 1u, x32w_lt(l, nlo))));
  let l2 = x32w_add(l, alo);
  let hi = x32w_add(x32w_add(h, ahi), vec2<u32>(0u, select(0u, 1u, x32w_lt(l2, l))));
  return vec4<u32>(hi, l2);
}

// est = (float)lh * 0x1p-56f * |y| > 120.0f, in integers (lh != 0 unsigned, y bits ay)
fn x32w_est_big(lh: vec2<u32>, ay: u32) -> bool {
  if (x32w_isz(lh) || ay < 0x800000u) {
    return false;   // est < 2^7 * 2^-126
  }
  if (ay >= 0x7f800000u) {
    return true;
  }
  let f = x32w_u64f(lh);
  let p = x32w_fmul(f.x, bitcast<i32>(f.y) - 56, (ay & 0x7fffffu) | 0x800000u, i32(ay >> 23u) - 150);
  let ep = bitcast<i32>(p.y);
  return ep > -17 || (ep == -17 && p.x > 0xf00000u);
}

fn x32w_pow_bits(ux: u32, uy: u32) -> u32 {
  let ax = ux & 0x7fffffffu;
  let ay = uy & 0x7fffffffu;
  if (ay == 0u || ux == 0x3f800000u) {
    return 0x3f800000u;
  }
  if (ax > 0x7f800000u || ay > 0x7f800000u) {
    return 0x7fc00000u;
  }
  var yi = 2u;
  if (ay != 0x7f800000u) {
    yi = x32w_yint(ay);
  }
  let sgn = select(0u, 0x80000000u, (ux >> 31u) != 0u && yi == 1u);
  let yneg = (uy >> 31u) != 0u;
  if (ay == 0x7f800000u) {
    if (ax == 0x3f800000u) {
      return 0x3f800000u;
    }
    return select(0u, 0x7f800000u, (ax > 0x3f800000u) == !yneg);
  }
  if (ax == 0u) {
    return select(0u, 0x7f800000u, yneg) | sgn;
  }
  if (ax == 0x7f800000u) {
    return select(0x7f800000u, 0u, yneg) | sgn;
  }
  if ((ux >> 31u) != 0u && yi == 0u) {
    return 0x7fc00000u;
  }
  let L = x32w_ln(ax);
  var lh = L.xy;
  var ll = L.zw;
  let lneg = x32w_isneg(lh);
  if (lneg) {
    lh = x32w_add(vec2<u32>(~lh.x, ~lh.y), vec2<u32>(0u, select(0u, 1u, x32w_isz(ll))));
    ll = x32w_neg(ll);
  }
  let tneg = lneg != yneg;
  if (x32w_est_big(lh, ay)) {
    return select(0x7f800000u, 0u, tneg) | sgn;
  }
  // t = my * |L| * 2^ey, Q120
  let ynorm = ay >= 0x800000u;
  let my = vec2<u32>(0u, (ay & 0x7fffffu) | select(0u, 0x800000u, ynorm));
  let ey = select(1, i32(ay >> 23u), ynorm) - 150;
  let p0 = x32w_mullo(my, ll);
  let c0 = x32w_mulhi(my, ll);
  let p1 = x32w_add(x32w_mullo(my, lh), c0);
  let p2 = x32w_add(x32w_mulhi(my, lh), vec2<u32>(0u, select(0u, 1u, x32w_lt(p1, c0))));
  var th: vec2<u32>;
  var tl: vec2<u32>;
  if (ey >= 0) {
    let e = u32(ey);
    th = p1;
    if (e != 0u) {
      th = x32w_or(x32w_shl(p1, e), x32w_shr(p0, 64u - e));
    }
    tl = x32w_shl(p0, e);
  } else {
    let sh = u32(-ey);
    if (sh >= 128u) {
      th = vec2<u32>(0u, 0u);
      tl = x32w_shr(p2, sh - 128u);
      if (sh >= 192u) {
        tl = vec2<u32>(0u, 0u);
      }
    } else if (sh >= 64u) {
      if (sh == 64u) {
        th = p2;
        tl = p1;
      } else {
        th = x32w_shr(p2, sh - 64u);
        tl = x32w_or(x32w_shr(p1, sh - 64u), x32w_shl(p2, 128u - sh));
      }
    } else {
      th = x32w_or(x32w_shr(p1, sh), x32w_shl(p2, 64u - sh));
      tl = x32w_or(x32w_shr(p0, sh), x32w_shl(p1, 64u - sh));
    }
  }
  return x32w_exp_core(tneg, th, tl) ^ sgn;
}

fn x32_pow(x: f32, y: f32) -> f32 {
  return bitcast<f32>(x32w_pow_bits(bitcast<u32>(x), bitcast<u32>(y)));
}
