//TABLES inv_odd
// x32_softplus: kernels/ops.bend softplus1, as the C lane emits it (comp.ts):
//   20.0f < x ? x : x32_softplus(x < 88.0f ? x : 88.0f)
// where x32.h's x32_softplus(x) = (f32)log(1.0 + exp((double)x)) for x <= 88.
// Note softplus1(NaN) = 88.0 (NaN < 88 is false). x32w_softplus_core_bits = x32.h's x32_softplus.

fn x32w_softplus_core_bits(u: u32) -> u32 {
  let a = u & 0x7fffffffu;
  let sg = (u >> 31u) != 0u;
  if (a > 0x7f800000u) {
    return 0x7fc00000u;
  }
  if (a == 0x7f800000u) {
    return select(u, 0u, sg);
  }
  if (sg && a >= 0x42200000u) {
    return 0u;
  }
  if (a < 0x32800000u) {
    return 0x3f317218u;
  }
  let m = (a & 0x7fffffu) | 0x800000u;
  let me = x32w_exp_parts(sg, x32w_shl(vec2<u32>(0u, m), (a >> 23u) - 94u), vec2<u32>(0u, 0u));
  let M = me.m;
  var E = me.e;
  var D = x32w_add(x32w_shr(M, 11u), vec2<u32>(0u, (M.y >> 10u) & 1u));
  if ((D.x >> 21u) != 0u) {
    D = x32w_shr(D, 1u);
    E += 1;
  }
  var Sm: vec2<u32>;
  var Se: i32;
  if (E >= 0) {
    Se = E;
    if (E <= 52) {
      Sm = x32w_add(D, x32w_shl(vec2<u32>(0u, 1u), u32(52 - E)));
    } else if (E == 53) {
      Sm = x32w_add(D, vec2<u32>(0u, D.y & 1u));
    } else {
      Sm = D;
    }
  } else {
    let sh = u32(-E);
    var q = vec2<u32>(0u, 0u);
    if (sh <= 53u) {
      let rem = x32w_and(D, x32w_mask(sh));
      let hf = x32w_shl(vec2<u32>(0u, 1u), sh - 1u);
      q = x32w_shr(D, sh);
      if (x32w_lt(hf, rem) || (x32w_eq(rem, hf) && (q.y & 1u) == 1u)) {
        q = x32w_add(q, vec2<u32>(0u, 1u));
      }
    }
    Sm = x32w_add(vec2<u32>(0x100000u, 0u), q);
    Se = 0;
  }
  for (var g = 0; g < 4 && (Sm.x >> 21u) != 0u; g++) {
    Sm = x32w_add(x32w_shr(Sm, 1u), vec2<u32>(0u, Sm.y & (Sm.y >> 1u) & 1u));
    Se += 1;
  }
  let k = x32w_sub(Sm, vec2<u32>(0x100000u, 0u));
  let den = x32w_add(Sm, vec2<u32>(0x100000u, 0u));
  var ph = vec2<u32>(0u, 0u);
  var pl = vec2<u32>(0u, 0u);
  var i = 0;
  if (!x32w_isz(k)) {
    var W = vec2<u32>(0u, 0u);
    var r = k;
    for (var g = 0; g < 200 && (W.x >> 31u) == 0u; g++) {
      r = x32w_shl(r, 1u);
      W = x32w_shl(W, 1u);
      if (!x32w_lt(r, den)) {
        r = x32w_sub(r, den);
        W.y |= 1u;
      }
      i += 1;
    }
    let ts = 2 * i - 128;
    var t = vec2<u32>(0u, 0u);
    if (ts < 64) {
      if (ts > 0) {
        t = x32w_shr(x32w_mulhi(W, W), u32(ts));
      } else {
        t = x32w_shl(x32w_mulhi(W, W), u32(-ts));
      }
    }
    var F = vec2<u32>(0u, 0u);
    for (var n = 24; n >= 0; n--) {
      F = x32w_add(x32w_inv_odd[n], x32w_mulhi(F, t));
    }
    ph = x32w_mulhi(W, F);
    pl = x32w_mullo(W, F);
  }
  if (Se == 0) {
    if (x32w_isz(k)) {
      return 0u;
    }
    let z = x32w_clz(ph);
    var Mo = ph;
    if (z != 0u) {
      Mo = x32w_or(x32w_shl(ph, z), x32w_shr(pl, 64u - z));
    }
    return x32w_round(Mo, 65 - i32(z) - i, 0u);
  }
  // Q120: ln u = (ph:pl) >> (i - 58), plus Se ln2
  var lh = vec2<u32>(0u, 0u);
  var ll = vec2<u32>(0u, 0u);
  if (!x32w_isz(k)) {
    let sh = u32(i - 58);
    lh = x32w_shr(ph, sh);
    ll = x32w_or(x32w_shr(pl, sh), x32w_shl(ph, 64u - sh));
  }
  let un = vec2<u32>(0u, u32(Se));
  let nlo = x32w_mullo(un, vec2<u32>(0xabc9e3b3u, 0x9803f2f7u));
  let nhi = x32w_add(x32w_mullo(un, vec2<u32>(0x00b17217u, 0xf7d1cf79u)), x32w_mulhi(un, vec2<u32>(0xabc9e3b3u, 0x9803f2f7u)));
  let l = x32w_add(ll, nlo);
  let h = x32w_add(x32w_add(lh, nhi), vec2<u32>(0u, select(0u, 1u, x32w_lt(l, ll))));
  var z: u32;
  if (!x32w_isz(h)) {
    z = x32w_clz(h);
  } else {
    z = 64u + x32w_clz(l);
  }
  var Mo: vec2<u32>;
  if (z == 0u) {
    Mo = h;
  } else if (z < 64u) {
    Mo = x32w_or(x32w_shl(h, z), x32w_shr(l, 64u - z));
  } else {
    Mo = x32w_shl(l, z - 64u);
  }
  return x32w_round(Mo, 7 - i32(z), 0u);
}

// softplus1: 20 < x ? x : core(x < 88 ? x : 88), compares done on the bits
fn x32w_softplus_bits(u: u32) -> u32 {
  let a = u & 0x7fffffffu;
  let pos = (u >> 31u) == 0u;
  if (pos && a > 0x41a00000u && a <= 0x7f800000u) {
    return u;                                            // 20 < x (incl. +inf)
  }
  var v = u;
  if (a > 0x7f800000u || (pos && a >= 0x42b00000u)) {
    v = 0x42b00000u;                                     // !(x < 88): NaN (x > 20 already left)
  }
  return x32w_softplus_core_bits(v);
}

fn x32_softplus(x: f32) -> f32 {
  return bitcast<f32>(x32w_softplus_bits(bitcast<u32>(x)));
}
