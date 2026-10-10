//TABLES sinc cosc 2opi
// x32_sin / x32_cos: (f32)sin/cos((double)x), x32.h x32_sincos (Payne-Hanek, Q63 polynomials)

fn x32w_sincos_bits(u: u32, want_cos: u32) -> u32 {
  let a = u & 0x7fffffffu;
  if (a >= 0x7f800000u) {
    return 0x7fc00000u;
  }
  if (a < 0x39800000u) {
    return select(u, 0x3f800000u, want_cos == 1u);
  }
  let m = (a & 0x7fffffu) | 0x800000u;
  let s = i32(a >> 23u) - 150;
  var R: vec2<u32>;
  var er: i32;
  var N = 0u;
  var rneg = 0u;
  if (a <= 0x3f490fdau) {
    R = x32w_shl(vec2<u32>(0u, m), 40u);
    er = s + 24;
  } else {
    let p0 = s + 62;
    let w = u32(p0 >> 5u);
    let o = u32(p0 & 31);
    var W: array<u32, 6>;
    for (var i = 0u; i < 6u; i++) {
      if (o != 0u) {
        W[i] = (x32w_2opi[w + i] << o) | (x32w_2opi[w + i + 1u] >> (32u - o));
      } else {
        W[i] = x32w_2opi[w + i];
      }
    }
    var out: array<u32, 6>;
    var acc = vec2<u32>(0u, 0u);
    let m4 = m << 2u;
    for (var i = 5; i >= 0; i--) {
      acc = x32w_add(vec2<u32>(0u, acc.x), x32w_m32(m4, W[i]));
      out[i] = acc.y;
    }
    N = acc.x & 3u;
    var fh = vec2<u32>(out[0], out[1]);
    var fl = vec2<u32>(out[2], out[3]);
    if ((fh.x >> 31u) != 0u) {
      N += 1u;
      rneg = 1u;
      fh = x32w_add(vec2<u32>(~fh.x, ~fh.y), vec2<u32>(0u, select(0u, 1u, x32w_isz(fl))));
      fl = x32w_neg(fl);
    }
    var z: u32;
    if (!x32w_isz(fh)) {
      z = x32w_clz(fh);
    } else {
      z = 64u + x32w_clz(fl);
    }
    var F = vec2<u32>(0u, 0u);
    if (z == 0u) {
      F = fh;
    } else if (z < 64u) {
      F = x32w_or(x32w_shl(fh, z), x32w_shr(fl, 64u - z));
    } else if (z < 128u) {
      F = x32w_shl(fl, z - 64u);
    }
    let Rp = x32w_mulhi(F, vec2<u32>(0xc90fdaa2u, 0x2168c235u));
    let z2 = x32w_clz(Rp);
    R = x32w_shl(Rp, z2);
    er = 1 - i32(z2) - i32(z);
  }
  // r = R/2^64 * 2^er, |r| <= pi/4; zz = r^2 in Q63
  let zs = 1 - 2 * er;
  var zz = vec2<u32>(0u, 0u);
  if (zs < 64) {
    zz = x32w_shr(x32w_mulhi(R, R), u32(max(zs, 0)));
  }
  let nw = N + want_cos;
  let use_cos = (nw & 1u) == 1u;
  let neg = ((nw >> 1u) ^ select(0u, rneg, !use_cos) ^ select(0u, u >> 31u, want_cos == 0u)) & 1u;
  var M: vec2<u32>;
  var E: i32;
  if (use_cos) {
    var c = x32w_cosc[9];
    for (var k = 8; k >= 0; k--) {
      c = x32w_add(x32w_cosc[k], x32w_mul63(c, zz));
    }
    let cq = x32w_sub(vec2<u32>(0x40000000u, 0u), x32w_mulhis(zz, c));
    let l = x32w_clz(cq);
    M = x32w_shl(cq, l);
    E = 1 - i32(l);
  } else {
    var c = x32w_sinc[9];
    for (var k = 8; k >= 0; k--) {
      c = x32w_add(x32w_sinc[k], x32w_mul63(c, zz));
    }
    let sm = x32w_sub(R, x32w_shl(x32w_mulhi(R, x32w_mul63(zz, c)), 1u));
    let l = x32w_clz(sm);
    M = x32w_shl(sm, l);
    E = er - 1 - i32(l);
  }
  return x32w_round(M, E, neg << 31u);
}

fn x32_sin(x: f32) -> f32 {
  return bitcast<f32>(x32w_sincos_bits(bitcast<u32>(x), 0u));
}

fn x32_cos(x: f32) -> f32 {
  return bitcast<f32>(x32w_sincos_bits(bitcast<u32>(x), 1u));
}
