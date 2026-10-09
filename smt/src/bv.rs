//! Fixed-size bit-vectors (QF_BV): operator syntax and sorts, and eager bit-blasting.
//!
//! [`Op::parse`] reads the SMT-LIB `FixedSizeBitVectors` operators (indexed ones included),
//! [`literal`] the `#b`/`#x`/`(_ bvN w)` literals, and [`Op::check`] sort-checks an application.
//! [`Blaster`] turns each term into literals (least significant bit first) from structurally
//! hashed AND/XOR/multiplexer gates: ripple-carry adders, a shift-add multiplier, a restoring
//! divider (whose result on a zero divisor is SMT-LIB's) and barrel shifters. The model
//! evaluator computes on integers instead, so the self-check does not depend on these circuits.

use crate::sexp::Sexp;
use crate::SmtBuilder;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rustc_hash::FxHashMap;
use smtrex_core::Lit;

/// A bit-vector operator. Indexed operators carry their indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Concat,
    Extract(u32, u32),
    ZeroExtend(u32),
    SignExtend(u32),
    Repeat(u32),
    RotateLeft(u32),
    RotateRight(u32),
    Not,
    And,
    Or,
    Xor,
    Nand,
    Nor,
    Xnor,
    Comp,
    Neg,
    Add,
    Sub,
    Mul,
    Udiv,
    Urem,
    Sdiv,
    Srem,
    Smod,
    Shl,
    Lshr,
    Ashr,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// The names of the non-indexed operators, which cannot be redeclared.
pub const OP_NAMES: &[&str] = &[
    "concat", "bvnot", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvcomp", "bvneg",
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr",
    "bvashr", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// The Bool-valued operators (comparisons).
pub fn is_predicate(name: &str) -> bool {
    matches!(
        name,
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
    )
}

/// The sort of a bit-vector operator's result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ret {
    Bool,
    Bits(u32),
}

impl Ret {
    pub fn sort_name(self) -> String {
        match self {
            Ret::Bool => "Bool".to_string(),
            Ret::Bits(w) => sort_name(w),
        }
    }
}

/// The canonical spelling of the sort `(_ BitVec w)`.
pub fn sort_name(w: u32) -> String {
    format!("(_ BitVec {w})")
}

/// The width of a bit-vector sort spelled by [`sort_name`], or `None` for any other sort.
pub fn width(sort: &str) -> Option<u32> {
    sort.strip_prefix("(_ BitVec ")?
        .strip_suffix(')')?
        .parse()
        .ok()
}

/// Resolve the sort expression `(_ BitVec n)`; `None` if `s` is not of that shape.
pub fn parse_sort(s: &[Sexp]) -> Option<Result<String, String>> {
    let [Sexp::Atom(u), Sexp::Atom(bv), Sexp::Atom(n)] = s else {
        return None;
    };
    if u != "_" || bv != "BitVec" {
        return None;
    }
    Some(match n.parse::<u32>() {
        Ok(w) if w >= 1 && n.bytes().all(|b| b.is_ascii_digit()) => Ok(sort_name(w)),
        _ => Err(format!(
            "bit-vector width must be a positive numeral, got '{n}'"
        )),
    })
}

fn index(s: &Sexp) -> Result<u32, String> {
    match s {
        Sexp::Atom(a) if a.bytes().all(|b| b.is_ascii_digit()) => {
            a.parse().map_err(|_| format!("index '{a}' is too large"))
        }
        _ => Err(format!("expected a numeral index, got {s}")),
    }
}

impl Op {
    /// The operator named by an application head, `None` if `head` is not a bit-vector operator.
    pub fn parse(head: &Sexp) -> Result<Option<Op>, String> {
        let name = match head {
            Sexp::Atom(a) => a.as_str(),
            Sexp::List(l) => {
                let Some((Sexp::Atom(u), rest)) = l.split_first() else {
                    return Ok(None);
                };
                if u != "_" {
                    return Ok(None);
                }
                let Some((Sexp::Atom(name), idx)) = rest.split_first() else {
                    return Err(format!("malformed indexed identifier {head}"));
                };
                let idx = idx.iter().map(index).collect::<Result<Vec<_>, _>>()?;
                let one = |f: fn(u32) -> Op| match idx[..] {
                    [k] => Ok(Some(f(k))),
                    _ => Err(format!("'{name}' takes one index in {head}")),
                };
                return match name.as_str() {
                    "extract" => match idx[..] {
                        [i, j] => Ok(Some(Op::Extract(i, j))),
                        _ => Err(format!("'extract' takes two indices in {head}")),
                    },
                    "zero_extend" => one(Op::ZeroExtend),
                    "sign_extend" => one(Op::SignExtend),
                    "repeat" => one(Op::Repeat),
                    "rotate_left" => one(Op::RotateLeft),
                    "rotate_right" => one(Op::RotateRight),
                    _ => Err(format!("unknown indexed function {head}")),
                };
            }
        };
        Ok(Some(match name {
            "concat" => Op::Concat,
            "bvnot" => Op::Not,
            "bvand" => Op::And,
            "bvor" => Op::Or,
            "bvxor" => Op::Xor,
            "bvnand" => Op::Nand,
            "bvnor" => Op::Nor,
            "bvxnor" => Op::Xnor,
            "bvcomp" => Op::Comp,
            "bvneg" => Op::Neg,
            "bvadd" => Op::Add,
            "bvsub" => Op::Sub,
            "bvmul" => Op::Mul,
            "bvudiv" => Op::Udiv,
            "bvurem" => Op::Urem,
            "bvsdiv" => Op::Sdiv,
            "bvsrem" => Op::Srem,
            "bvsmod" => Op::Smod,
            "bvshl" => Op::Shl,
            "bvlshr" => Op::Lshr,
            "bvashr" => Op::Ashr,
            "bvult" => Op::Ult,
            "bvule" => Op::Ule,
            "bvugt" => Op::Ugt,
            "bvuge" => Op::Uge,
            "bvslt" => Op::Slt,
            "bvsle" => Op::Sle,
            "bvsgt" => Op::Sgt,
            "bvsge" => Op::Sge,
            _ => return Ok(None),
        }))
    }

    /// Sort-check an application with arguments of the given widths.
    pub fn check(self, widths: &[u32]) -> Result<Ret, String> {
        let arity = |n: usize| {
            if widths.len() == n {
                Ok(())
            } else {
                Err(format!(
                    "{self:?} expects {n} argument(s), got {}",
                    widths.len()
                ))
            }
        };
        let same = |min: usize| {
            if widths.len() < min {
                return Err(format!("{self:?} expects at least {min} arguments"));
            }
            if widths.windows(2).any(|p| p[0] != p[1]) {
                return Err(format!("{self:?} expects arguments of equal width"));
            }
            Ok(widths[0])
        };
        let too_wide = || format!("{self:?}: the result is too wide");
        use Op::*;
        Ok(match self {
            Concat => {
                if widths.len() < 2 {
                    return Err("concat expects at least 2 arguments".to_string());
                }
                Ret::Bits(
                    widths
                        .iter()
                        .try_fold(0u32, |a, &w| a.checked_add(w))
                        .ok_or_else(too_wide)?,
                )
            }
            Extract(i, j) => {
                arity(1)?;
                if !(j <= i && i < widths[0]) {
                    return Err(format!(
                        "extract {i} {j} out of range for width {}",
                        widths[0]
                    ));
                }
                Ret::Bits(i - j + 1)
            }
            ZeroExtend(k) | SignExtend(k) => {
                arity(1)?;
                Ret::Bits(widths[0].checked_add(k).ok_or_else(too_wide)?)
            }
            Repeat(k) => {
                arity(1)?;
                if k == 0 {
                    return Err("repeat needs a positive index".to_string());
                }
                Ret::Bits(widths[0].checked_mul(k).ok_or_else(too_wide)?)
            }
            RotateLeft(_) | RotateRight(_) | Not | Neg => {
                arity(1)?;
                Ret::Bits(widths[0])
            }
            And | Or | Xor | Add | Mul => Ret::Bits(same(2)?),
            Nand | Nor | Xnor | Sub | Udiv | Urem | Sdiv | Srem | Smod | Shl | Lshr | Ashr => {
                arity(2)?;
                Ret::Bits(same(2)?)
            }
            Comp => {
                arity(2)?;
                same(2)?;
                Ret::Bits(1)
            }
            Ult | Ule | Ugt | Uge | Slt | Sle | Sgt | Sge => {
                arity(2)?;
                same(2)?;
                Ret::Bool
            }
        })
    }

    /// The result sort of a *well-sorted* application, asking `width_of(i)` for the width of
    /// argument `i` only when the result depends on it.
    pub fn ret(
        self,
        nargs: usize,
        mut width_of: impl FnMut(usize) -> Result<u32, String>,
    ) -> Result<Ret, String> {
        use Op::*;
        Ok(match self {
            Concat => {
                let mut w = 0u32;
                for i in 0..nargs {
                    w = w.saturating_add(width_of(i)?);
                }
                Ret::Bits(w)
            }
            Extract(i, j) => Ret::Bits(i.saturating_sub(j) + 1),
            ZeroExtend(k) | SignExtend(k) => Ret::Bits(width_of(0)?.saturating_add(k)),
            Repeat(k) => Ret::Bits(width_of(0)?.saturating_mul(k)),
            Comp => Ret::Bits(1),
            Ult | Ule | Ugt | Uge | Slt | Sle | Sgt | Sge => Ret::Bool,
            _ => Ret::Bits(width_of(0)?),
        })
    }
}

/// A bit-vector literal `#b…`, `#x…` or `(_ bvN w)` as (value, width); `None` if `t` is not one.
pub fn literal(t: &Sexp) -> Result<Option<(BigUint, u32)>, String> {
    match t {
        Sexp::Atom(a) => {
            let (radix, digits, bits) = if let Some(d) = a.strip_prefix("#b") {
                (2, d, 1)
            } else if let Some(d) = a.strip_prefix("#x") {
                (16, d, 4)
            } else {
                return Ok(None);
            };
            if digits.is_empty() {
                return Err(format!("empty bit-vector literal '{a}'"));
            }
            let v = BigUint::parse_bytes(digits.as_bytes(), radix)
                .ok_or_else(|| format!("malformed bit-vector literal '{a}'"))?;
            let w = u32::try_from(digits.len() * bits)
                .map_err(|_| format!("bit-vector literal '{a}' is too long"))?;
            Ok(Some((v, w)))
        }
        Sexp::List(l) => {
            let [Sexp::Atom(u), Sexp::Atom(bv), w] = &l[..] else {
                return Ok(None);
            };
            let Some(n) = bv.strip_prefix("bv") else {
                return Ok(None);
            };
            if u != "_" || n.is_empty() || !n.bytes().all(|b| b.is_ascii_digit()) {
                return Ok(None);
            }
            let w = index(w)?;
            if w == 0 {
                return Err(format!("bit-vector width must be positive in {t}"));
            }
            let v: BigUint = n.parse().map_err(|_| format!("malformed literal {t}"))?;
            Ok(Some((v & mask(w), w)))
        }
    }
}

/// `2^w - 1`.
pub fn mask(w: u32) -> BigUint {
    (BigUint::one() << w) - BigUint::one()
}

/// Bits, least significant first.
pub type Bits = Vec<Lit>;

/// The bit-blaster: gate construction with constant folding and structural hashing.
pub struct Blaster {
    /// The literal that is always true (forced by a unit clause).
    t: Lit,
    ands: FxHashMap<Vec<Lit>, Lit>,
    xors: FxHashMap<(Lit, Lit), Lit>,
    muxes: FxHashMap<(Lit, Lit, Lit), Lit>,
    /// Operator applications already encoded, by operator and argument bits.
    apps: FxHashMap<(Op, Vec<Bits>), Bits>,
    /// Unsigned quotient and remainder, by dividend and divisor.
    divs: FxHashMap<(Bits, Bits), (Bits, Bits)>,
}

impl Blaster {
    pub fn new(true_lit: Lit) -> Blaster {
        Blaster {
            t: true_lit,
            ands: FxHashMap::default(),
            xors: FxHashMap::default(),
            muxes: FxHashMap::default(),
            apps: FxHashMap::default(),
            divs: FxHashMap::default(),
        }
    }

    fn f(&self) -> Lit {
        !self.t
    }

    /// The bits of the constant `v` of width `w`.
    pub fn constant(&self, v: &BigUint, w: u32) -> Bits {
        (0..w as u64)
            .map(|i| if v.bit(i) { self.t } else { self.f() })
            .collect()
    }

    /// `true` or `false` if `l` is a constant.
    fn const_of(&self, l: Lit) -> Option<bool> {
        if l == self.t {
            Some(true)
        } else if l == self.f() {
            Some(false)
        } else {
            None
        }
    }

    // ----- gates -----

    /// The conjunction of `lits`.
    pub fn and_all(&mut self, b: &mut SmtBuilder, lits: &[Lit]) -> Lit {
        let mut xs: Vec<Lit> = Vec::with_capacity(lits.len());
        for &l in lits {
            match self.const_of(l) {
                Some(true) => {}
                Some(false) => return self.f(),
                None => xs.push(l),
            }
        }
        xs.sort_unstable();
        xs.dedup();
        if xs.windows(2).any(|p| p[0] == !p[1]) {
            return self.f();
        }
        match xs.len() {
            0 => return self.t,
            1 => return xs[0],
            _ => {}
        }
        if let Some(&r) = self.ands.get(&xs) {
            return r;
        }
        let r = b.fresh_var().pos();
        let mut big = Vec::with_capacity(xs.len() + 1);
        big.push(r);
        for &x in &xs {
            b.add_clause(vec![!r, x]);
            big.push(!x);
        }
        b.add_clause(big);
        self.ands.insert(xs, r);
        r
    }

    pub fn and(&mut self, b: &mut SmtBuilder, x: Lit, y: Lit) -> Lit {
        self.and_all(b, &[x, y])
    }

    pub fn or(&mut self, b: &mut SmtBuilder, x: Lit, y: Lit) -> Lit {
        !self.and_all(b, &[!x, !y])
    }

    pub fn or_all(&mut self, b: &mut SmtBuilder, lits: &[Lit]) -> Lit {
        let neg: Vec<Lit> = lits.iter().map(|&l| !l).collect();
        !self.and_all(b, &neg)
    }

    pub fn xor(&mut self, b: &mut SmtBuilder, x: Lit, y: Lit) -> Lit {
        match (self.const_of(x), self.const_of(y)) {
            (Some(cx), _) => return if cx { !y } else { y },
            (_, Some(cy)) => return if cy { !x } else { x },
            _ => {}
        }
        if x == y {
            return self.f();
        }
        if x == !y {
            return self.t;
        }
        // Normalise to positive inputs: x ^ !y = !(x ^ y).
        let flip = x.is_negated() != y.is_negated();
        let (x, y) = (x.var().pos(), y.var().pos());
        let key = if x < y { (x, y) } else { (y, x) };
        let r = match self.xors.get(&key) {
            Some(&r) => r,
            None => {
                let r = b.fresh_var().pos();
                b.add_clause(vec![!x, !y, !r]);
                b.add_clause(vec![x, y, !r]);
                b.add_clause(vec![x, !y, r]);
                b.add_clause(vec![!x, y, r]);
                self.xors.insert(key, r);
                r
            }
        };
        if flip {
            !r
        } else {
            r
        }
    }

    /// `if c then t else e`.
    pub fn mux(&mut self, b: &mut SmtBuilder, c: Lit, t: Lit, e: Lit) -> Lit {
        if let Some(cc) = self.const_of(c) {
            return if cc { t } else { e };
        }
        if t == e {
            return t;
        }
        if t == !e {
            return self.xor(b, !c, t);
        }
        match (self.const_of(t), self.const_of(e)) {
            (Some(true), _) => return self.or(b, c, e),
            (Some(false), _) => return self.and(b, !c, e),
            (_, Some(true)) => return self.or(b, !c, t),
            (_, Some(false)) => return self.and(b, c, t),
            _ => {}
        }
        if c == t {
            return self.or(b, c, e);
        }
        if c == !t {
            return self.and(b, !c, e);
        }
        if c == e {
            return self.and(b, c, t);
        }
        if c == !e {
            return self.or(b, !c, t);
        }
        let (c, t, e) = if c.is_negated() {
            (!c, e, t)
        } else {
            (c, t, e)
        };
        if let Some(&r) = self.muxes.get(&(c, t, e)) {
            return r;
        }
        let r = b.fresh_var().pos();
        b.add_clause(vec![!c, !t, r]);
        b.add_clause(vec![!c, t, !r]);
        b.add_clause(vec![c, !e, r]);
        b.add_clause(vec![c, e, !r]);
        // Redundant, but they let unit propagation see through an unassigned condition.
        b.add_clause(vec![!t, !e, r]);
        b.add_clause(vec![t, e, !r]);
        self.muxes.insert((c, t, e), r);
        r
    }

    // ----- word-level circuits -----

    pub fn mux_bits(&mut self, b: &mut SmtBuilder, c: Lit, t: &[Lit], e: &[Lit]) -> Bits {
        t.iter()
            .zip(e)
            .map(|(&x, &y)| self.mux(b, c, x, y))
            .collect()
    }

    /// `x = y`, bitwise.
    pub fn eq(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> Lit {
        let same: Vec<Lit> = x.iter().zip(y).map(|(&p, &q)| !self.xor(b, p, q)).collect();
        self.and_all(b, &same)
    }

    /// `x <u y`: scanning from the least significant bit, the highest differing bit decides.
    pub fn ult(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> Lit {
        let mut lt = self.f();
        for (&p, &q) in x.iter().zip(y) {
            let d = self.xor(b, p, q);
            lt = self.mux(b, d, q, lt);
        }
        lt
    }

    /// `x <s y`: unsigned comparison with the sign bits flipped.
    pub fn slt(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> Lit {
        let flip = |v: &[Lit]| {
            let mut v = v.to_vec();
            let m = v.len() - 1;
            v[m] = !v[m];
            v
        };
        self.ult(b, &flip(x), &flip(y))
    }

    /// `x + y + cin` (truncated) and the carry out.
    fn add(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit], cin: Lit) -> (Bits, Lit) {
        let mut c = cin;
        let mut sum = Vec::with_capacity(x.len());
        for (&p, &q) in x.iter().zip(y) {
            let h = self.xor(b, p, q);
            sum.push(self.xor(b, h, c));
            c = self.mux(b, h, c, p);
        }
        (sum, c)
    }

    fn not_bits(x: &[Lit]) -> Bits {
        x.iter().map(|&l| !l).collect()
    }

    fn neg(&mut self, b: &mut SmtBuilder, x: &[Lit]) -> Bits {
        let zero = vec![self.f(); x.len()];
        self.add(b, &Self::not_bits(x), &zero, self.t).0
    }

    fn sub(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> Bits {
        self.add(b, x, &Self::not_bits(y), self.t).0
    }

    /// Shift-add multiplication (truncated to the width).
    fn mul(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> Bits {
        // Partial products fold when the multiplier bits are constant.
        let constant = |v: &[Lit]| v.iter().all(|&l| self.const_of(l).is_some());
        let (x, y) = if constant(x) && !constant(y) {
            (y, x)
        } else {
            (x, y)
        };
        let w = x.len();
        let mut acc = vec![self.f(); w];
        for (j, &yj) in y.iter().enumerate() {
            if self.const_of(yj) == Some(false) {
                continue;
            }
            let pp: Bits = (0..w)
                .map(|i| {
                    if i < j {
                        self.f()
                    } else {
                        self.and(b, x[i - j], yj)
                    }
                })
                .collect();
            acc = self.add(b, &acc, &pp, self.f()).0;
        }
        acc
    }

    /// Restoring division: unsigned quotient and remainder. With a zero divisor every trial
    /// subtraction succeeds, so the quotient is all ones and the remainder the dividend, which
    /// is the SMT-LIB semantics.
    fn udivrem(&mut self, b: &mut SmtBuilder, x: &[Lit], y: &[Lit]) -> (Bits, Bits) {
        let key = (x.to_vec(), y.to_vec());
        if let Some(r) = self.divs.get(&key) {
            return r.clone();
        }
        let w = x.len();
        let f = self.f();
        // ~(0 ++ y): the subtrahend of the (w+1)-bit trial subtraction.
        let mut ny = Self::not_bits(y);
        ny.push(self.t);
        let mut q = vec![f; w];
        let mut r = vec![f; w];
        for i in (0..w).rev() {
            // r' = 2r + x_i, w+1 bits wide.
            let mut rs = Vec::with_capacity(w + 1);
            rs.push(x[i]);
            rs.extend_from_slice(&r);
            let (diff, no_borrow) = self.add(b, &rs, &ny, self.t);
            q[i] = no_borrow;
            // Either way the new remainder is below 2^w, so the top bit is dropped.
            r = (0..w)
                .map(|k| self.mux(b, no_borrow, diff[k], rs[k]))
                .collect();
        }
        self.divs.insert(key, (q.clone(), r.clone()));
        (q, r)
    }

    /// `|x|` (two's complement) and the sign bit.
    fn abs(&mut self, b: &mut SmtBuilder, x: &[Lit]) -> (Bits, Lit) {
        let s = x[x.len() - 1];
        let n = self.neg(b, x);
        (self.mux_bits(b, s, &n, x), s)
    }

    /// Barrel shifter. `kind` is Shl, Lshr or Ashr.
    fn shift(&mut self, b: &mut SmtBuilder, kind: Op, x: &[Lit], s: &[Lit]) -> Bits {
        let w = x.len();
        let fill = if kind == Op::Ashr { x[w - 1] } else { self.f() };
        let mut cur = x.to_vec();
        let mut overflow = Vec::new();
        for (k, &sk) in s.iter().enumerate() {
            let amount = if k < usize::BITS as usize - 1 {
                1usize << k
            } else {
                usize::MAX
            };
            if amount >= w {
                overflow.push(sk);
                continue;
            }
            let shifted: Bits = (0..w)
                .map(|i| match kind {
                    Op::Shl if i >= amount => cur[i - amount],
                    Op::Shl => self.f(),
                    _ if i + amount < w => cur[i + amount],
                    _ => fill,
                })
                .collect();
            cur = self.mux_bits(b, sk, &shifted, &cur);
        }
        let over = self.or_all(b, &overflow);
        cur.iter().map(|&l| self.mux(b, over, fill, l)).collect()
    }

    /// Encode a bit-vector operator application whose result is a bit-vector.
    pub fn apply(&mut self, b: &mut SmtBuilder, op: Op, args: &[Bits]) -> Bits {
        // Left-associative operators fold pairwise, so each step is cached separately.
        if args.len() > 2
            && matches!(
                op,
                Op::Concat | Op::And | Op::Or | Op::Xor | Op::Add | Op::Mul
            )
        {
            let mut acc = args[0].clone();
            for a in &args[1..] {
                acc = self.apply(b, op, &[acc, a.clone()]);
            }
            return acc;
        }
        let key = (op, args.to_vec());
        if let Some(r) = self.apps.get(&key) {
            return r.clone();
        }
        let r = self.encode(b, op, args);
        self.apps.insert(key, r.clone());
        r
    }

    fn encode(&mut self, b: &mut SmtBuilder, op: Op, args: &[Bits]) -> Bits {
        let x = &args[0];
        let w = x.len();
        let y = args.get(1);
        let y = || y.expect("binary operator");
        let zip = |s: &mut Self,
                   b: &mut SmtBuilder,
                   g: fn(&mut Self, &mut SmtBuilder, Lit, Lit) -> Lit| {
            x.iter()
                .zip(y())
                .map(|(&p, &q)| g(s, b, p, q))
                .collect::<Bits>()
        };
        use Op::*;
        match op {
            Concat => {
                let mut r = y().clone();
                r.extend_from_slice(x);
                r
            }
            Extract(i, j) => x[j as usize..=i as usize].to_vec(),
            ZeroExtend(k) => {
                let mut r = x.clone();
                r.extend(std::iter::repeat_n(self.f(), k as usize));
                r
            }
            SignExtend(k) => {
                let mut r = x.clone();
                r.extend(std::iter::repeat_n(x[w - 1], k as usize));
                r
            }
            Repeat(k) => x.repeat(k as usize),
            RotateLeft(k) => {
                let k = k as usize % w;
                (0..w).map(|i| x[(i + w - k) % w]).collect()
            }
            RotateRight(k) => {
                let k = k as usize % w;
                (0..w).map(|i| x[(i + k) % w]).collect()
            }
            Not => Self::not_bits(x),
            And => zip(self, b, Self::and),
            Or => zip(self, b, Self::or),
            Xor => zip(self, b, Self::xor),
            Nand => Self::not_bits(&zip(self, b, Self::and)),
            Nor => Self::not_bits(&zip(self, b, Self::or)),
            Xnor => Self::not_bits(&zip(self, b, Self::xor)),
            Comp => vec![self.eq(b, x, y())],
            Neg => self.neg(b, x),
            Add => self.add(b, x, y(), self.f()).0,
            Sub => self.sub(b, x, y()),
            Mul => self.mul(b, x, y()),
            Udiv => self.udivrem(b, x, y()).0,
            Urem => self.udivrem(b, x, y()).1,
            Sdiv => {
                let (ax, sx) = self.abs(b, x);
                let (ay, sy) = self.abs(b, y());
                let q = self.udivrem(b, &ax, &ay).0;
                let nq = self.neg(b, &q);
                let s = self.xor(b, sx, sy);
                self.mux_bits(b, s, &nq, &q)
            }
            Srem => {
                let (ax, sx) = self.abs(b, x);
                let (ay, _) = self.abs(b, y());
                let r = self.udivrem(b, &ax, &ay).1;
                let nr = self.neg(b, &r);
                self.mux_bits(b, sx, &nr, &r)
            }
            Smod => {
                // SMT-LIB: u = |x| urem |y|; u if u = 0 or both non-negative, -u + y if only x
                // is negative, u + y if only y is, -u if both are.
                let t = y().clone();
                let (ax, sx) = self.abs(b, x);
                let (ay, sy) = self.abs(b, &t);
                let u = self.udivrem(b, &ax, &ay).1;
                let nu = self.neg(b, &u);
                let nu_t = self.add(b, &nu, &t, self.f()).0;
                let u_t = self.add(b, &u, &t, self.f()).0;
                let zero = vec![self.f(); w];
                let u_zero = self.eq(b, &u, &zero);
                let if_x_neg = self.mux_bits(b, sy, &nu, &nu_t);
                let if_x_pos = self.mux_bits(b, sy, &u_t, &u);
                let r = self.mux_bits(b, sx, &if_x_neg, &if_x_pos);
                self.mux_bits(b, u_zero, &u, &r)
            }
            Shl | Lshr | Ashr => self.shift(b, op, x, y()),
            Ult | Ule | Ugt | Uge | Slt | Sle | Sgt | Sge => {
                vec![self.predicate(b, op, x, y())]
            }
        }
    }

    /// Encode a bit-vector comparison.
    pub fn predicate(&mut self, b: &mut SmtBuilder, op: Op, x: &[Lit], y: &[Lit]) -> Lit {
        use Op::*;
        match op {
            Ult => self.ult(b, x, y),
            Ugt => self.ult(b, y, x),
            Ule => !self.ult(b, y, x),
            Uge => !self.ult(b, x, y),
            Slt => self.slt(b, x, y),
            Sgt => self.slt(b, y, x),
            Sle => !self.slt(b, y, x),
            Sge => !self.slt(b, x, y),
            _ => unreachable!("{op:?} is not a comparison"),
        }
    }
}

/// The integer whose bits (least significant first) are the values of `bits` under `value`.
pub fn read_bits(bits: &[Lit], mut value: impl FnMut(Lit) -> bool) -> BigUint {
    let mut v = BigUint::zero();
    for (i, &l) in bits.iter().enumerate() {
        if value(l) {
            v.set_bit(i as u64, true);
        }
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{bv_apply, Value};
    use crate::script::{Answer, Response, Script};

    fn answers(input: &str) -> Vec<Answer> {
        Script::run(input)
            .unwrap_or_else(|e| panic!("{e}\n{input}"))
            .results
            .into_iter()
            .map(|r| r.answer)
            .collect()
    }

    /// `(term, expected value)` pairs from the SMT-LIB 2.6 definitions, worked by hand.
    const CASES: &[(&str, &str)] = &[
        // Division by zero: bvudiv gives all ones, bvurem the dividend; the signed operators
        // follow from their definitions in terms of the unsigned ones.
        ("(bvudiv #b0111 #b0000)", "#b1111"),
        ("(bvurem #b0111 #b0000)", "#b0111"),
        ("(bvsdiv #b0111 #b0000)", "#b1111"),
        ("(bvsdiv #b1001 #b0000)", "#b0001"),
        ("(bvsrem #b1001 #b0000)", "#b1001"),
        ("(bvsmod #b1001 #b0000)", "#b1001"),
        ("(bvsmod #b0011 #b0000)", "#b0011"),
        // Signs: truncating division, remainder follows the dividend, smod the divisor.
        ("(bvudiv #b1001 #b0010)", "#b0100"),
        ("(bvsdiv #b1001 #b0010)", "#b1101"),
        ("(bvsdiv #b0111 #b1110)", "#b1101"),
        ("(bvsdiv #b1001 #b1110)", "#b0011"),
        ("(bvsdiv #b1000 #b1111)", "#b1000"),
        ("(bvsrem #b1001 #b0010)", "#b1111"),
        ("(bvsrem #b0111 #b1110)", "#b0001"),
        ("(bvsrem #b1001 #b1110)", "#b1111"),
        ("(bvsmod #b1001 #b0010)", "#b0001"),
        ("(bvsmod #b0111 #b1110)", "#b1111"),
        ("(bvsmod #b1001 #b1110)", "#b1111"),
        ("(bvsmod #b1010 #b0011)", "#b0000"),
        ("(bvurem #b1001 #b0010)", "#b0001"),
        // Shifts, including amounts at and beyond the width.
        ("(bvshl #b0011 #b0001)", "#b0110"),
        ("(bvshl #b0011 #b0100)", "#b0000"),
        ("(bvshl #b0011 #b1111)", "#b0000"),
        ("(bvlshr #b1000 #b0011)", "#b0001"),
        ("(bvlshr #b1000 #b0100)", "#b0000"),
        ("(bvashr #b1010 #b0001)", "#b1101"),
        ("(bvashr #b1000 #b0101)", "#b1111"),
        ("(bvashr #b0111 #b1000)", "#b0000"),
        ("(bvshl #b011 #b101)", "#b000"),
        ("(bvashr #b100 #b011)", "#b111"),
        // Arithmetic and bitwise.
        ("(bvadd #b1111 #b0010)", "#b0001"),
        ("(bvsub #b0001 #b0010)", "#b1111"),
        ("(bvneg #b0001)", "#b1111"),
        ("(bvneg #b1000)", "#b1000"),
        ("(bvmul #b0110 #b0011)", "#b0010"),
        ("(bvadd #b0001 #b0010 #b0100)", "#b0111"),
        ("(bvnand #b1100 #b1010)", "#b0111"),
        ("(bvnor #b1100 #b1010)", "#b0001"),
        ("(bvxnor #b1100 #b1010)", "#b1001"),
        ("(bvxor #b1100 #b1010)", "#b0110"),
        ("(bvnot #b1100)", "#b0011"),
        ("(bvcomp #b1100 #b1100)", "#b1"),
        ("(bvcomp #b1100 #b1101)", "#b0"),
        // Structure.
        ("(concat #b10 #b011)", "#b10011"),
        ("((_ extract 3 1) #b10110)", "#b011"),
        ("((_ extract 0 0) #b10111)", "#b1"),
        ("((_ zero_extend 2) #b11)", "#b0011"),
        ("((_ zero_extend 0) #b11)", "#b11"),
        ("((_ sign_extend 2) #b10)", "#b1110"),
        ("((_ sign_extend 2) #b01)", "#b0001"),
        ("((_ repeat 3) #b10)", "#b101010"),
        ("((_ rotate_left 1) #b1001)", "#b0011"),
        ("((_ rotate_left 5) #b1001)", "#b0011"),
        ("((_ rotate_right 1) #b1001)", "#b1100"),
        ("((_ rotate_right 0) #b1001)", "#b1001"),
        // Literals.
        ("(_ bv18 4)", "#b0010"),
        ("#x1f", "#b00011111"),
        // Width 1.
        ("(bvadd #b1 #b1)", "#b0"),
        ("(bvmul #b1 #b1)", "#b1"),
        ("(bvneg #b1)", "#b1"),
        ("(bvsdiv #b1 #b1)", "#b1"),
        ("(bvsdiv #b0 #b1)", "#b0"),
        ("(bvsdiv #b1 #b0)", "#b1"),
        ("(bvudiv #b1 #b0)", "#b1"),
        ("(bvurem #b1 #b0)", "#b1"),
        ("(bvsrem #b1 #b1)", "#b0"),
        ("(bvsmod #b1 #b0)", "#b1"),
        ("(bvashr #b1 #b1)", "#b1"),
        ("(bvshl #b1 #b1)", "#b0"),
        ("(bvlshr #b1 #b0)", "#b1"),
    ];

    const PREDICATES: &[(&str, bool)] = &[
        ("(bvult #b0111 #b1000)", true),
        ("(bvslt #b0111 #b1000)", false),
        ("(bvsle #b1000 #b0111)", true),
        ("(bvule #b1000 #b0111)", false),
        ("(bvuge #b1000 #b1000)", true),
        ("(bvsgt #b0000 #b1111)", true),
        ("(bvugt #b0000 #b1111)", false),
        ("(bvsge #b1111 #b0000)", false),
        ("(bvslt #b1 #b0)", true),
        ("(bvult #b1 #b0)", false),
        ("(bvsle #b1 #b1)", true),
    ];

    /// Every case holds, both on constants (folded by the blaster, checked by the evaluator)
    /// and on variables pinned to the arguments (so the gates' clauses do the work).
    #[test]
    fn operator_semantics() {
        let cases = CASES
            .iter()
            .map(|&(t, v)| (t.to_string(), v.to_string()))
            .chain(
                PREDICATES
                    .iter()
                    .map(|&(t, v)| (t.to_string(), v.to_string())),
            );
        for (term, expected) in cases {
            let holds = format!("(set-logic QF_BV) (assert (= {term} {expected})) (check-sat)");
            assert_eq!(answers(&holds), vec![Answer::Sat], "{term} = {expected}");
            let fails =
                format!("(set-logic QF_BV) (assert (distinct {term} {expected})) (check-sat)");
            assert_eq!(answers(&fails), vec![Answer::Unsat], "{term} = {expected}");
            // The same with the literal arguments replaced by pinned variables.
            let sexp = crate::sexp::parse_script(&term).unwrap().remove(0);
            let Sexp::List(l) = &sexp else { continue };
            if literal(&sexp).unwrap().is_some() {
                continue;
            }
            let mut decls = String::from("(set-logic QF_BV)");
            let mut args = Vec::new();
            for (i, a) in l[1..].iter().enumerate() {
                let (_, w) = literal(a).unwrap().expect("literal arguments");
                decls.push_str(&format!(
                    " (declare-const a{i} (_ BitVec {w})) (assert (= a{i} {a}))"
                ));
                args.push(format!("a{i}"));
            }
            let pinned = format!("({} {})", l[0], args.join(" "));
            let script = format!("{decls} (assert (distinct {pinned} {expected})) (check-sat)");
            assert_eq!(
                answers(&script),
                vec![Answer::Unsat],
                "{pinned} = {expected}"
            );
        }
    }

    fn word(w: u32, v: u64) -> String {
        format!("#b{:0>w$}", format!("{v:b}"), w = w as usize)
    }

    /// The circuits agree with the integer semantics on every input of widths 1 to 4.
    #[test]
    fn circuits_match_integer_semantics_exhaustively() {
        let ops = [
            "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvcomp", "bvadd", "bvsub",
            "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
            "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
        ];
        for w in 1..=4u32 {
            for name in ops {
                let op = Op::parse(&Sexp::Atom(name.to_string())).unwrap().unwrap();
                let mut src = format!(
                    "(set-logic QF_BV) (declare-const x (_ BitVec {w})) \
                     (declare-const y (_ BitVec {w})) (define-fun r () {} ({name} x y))",
                    op.check(&[w, w]).unwrap().sort_name()
                );
                let mut expected = Vec::new();
                for a in 0..1u64 << w {
                    for b in 0..1u64 << w {
                        let v = bv_apply(op, &[(w, a.into()), (w, b.into())]).unwrap();
                        let shown = match v {
                            Value::Bool(t) => t.to_string(),
                            Value::BitVec { width, value } => {
                                word(width, u64::try_from(&value).unwrap())
                            }
                            _ => unreachable!(),
                        };
                        src.push_str(&format!(
                            " (push) (assert (= x {})) (assert (= y {})) \
                             (assert (distinct r {shown})) (check-sat) (pop)",
                            word(w, a),
                            word(w, b)
                        ));
                        expected.push(Answer::Unsat);
                    }
                }
                assert_eq!(answers(&src), expected, "{name} at width {w}");
            }
        }
    }

    #[test]
    fn sorts_are_checked() {
        let e = |body: &str| match Script::run(&format!(
            "(set-logic QF_BV) (declare-const x (_ BitVec 4)) (declare-const y (_ BitVec 3)) {body}"
        )) {
            Err(e) => e,
            Ok(_) => panic!("expected an error from {body}"),
        };
        assert!(e("(assert (= (bvadd x y) x))").contains("equal width"));
        assert!(e("(assert (= x y))").contains("mixes sorts"));
        assert!(e("(assert (= ((_ extract 4 0) x) x))").contains("out of range"));
        assert!(e("(assert (= ((_ extract 0 1) x) x))").contains("out of range"));
        assert!(e("(assert (bvult x))").contains("expects 2"));
        assert!(e("(assert (= ((_ repeat 0) x) x))").contains("positive"));
        assert!(e("(assert (bvult x true))").contains("bit-vector arguments"));
        assert!(e("(declare-const z (_ BitVec 0))").contains("positive"));
        assert!(e("(declare-fun f ((_ BitVec 4)) Bool)").contains("QF_UFBV"));
        assert!(e("(declare-fun bvadd () Bool)").contains("reserved"));
        assert!(e("(assert (= ((_ frobnicate 1) x) x))").contains("unknown indexed"));
    }

    #[test]
    fn models_print_bit_vectors() {
        let mut script = Script::new();
        let mut out = Vec::new();
        let src = "(set-logic QF_BV) (define-sort Word () (_ BitVec 6))
             (declare-const x Word) (declare-const unused (_ BitVec 3))
             (assert (= (bvadd x #b000001) #b000100))
             (check-sat) (get-model) (get-value ((concat x #b1) #x0a))";
        for cmd in &crate::sexp::parse_script(src).unwrap() {
            match script.exec(cmd).unwrap() {
                Some(Response::Text(t)) => out.push(t),
                Some(Response::Check(c)) => out.push(c.answer.as_str().to_string()),
                None => {}
            }
        }
        assert_eq!(out[0], "sat");
        assert!(
            out[1].contains("(define-fun x () (_ BitVec 6) #b000011)"),
            "{}",
            out[1]
        );
        assert!(
            out[1].contains("(define-fun unused () (_ BitVec 3) #b000)"),
            "{}",
            out[1]
        );
        assert_eq!(out[2], "(((concat x #b1) #b0000111)\n (#x0a #b00001010))");
    }

    #[test]
    fn wide_vectors_and_scoping() {
        // Above 128 bits: 2^199 + 2^199 wraps to 0 at width 200.
        let s = "(set-logic QF_BV) (declare-const x (_ BitVec 200))
             (assert (= x (concat #b1 (_ bv0 199))))
             (assert (= (bvadd x x) (_ bv0 200)))
             (check-sat)
             (push 1) (assert (bvult x (_ bv1 200))) (check-sat) (pop 1)
             (assert (let ((y (bvlshr x (_ bv199 200)))) (= y (_ bv1 200))))
             (check-sat)";
        assert_eq!(answers(s), vec![Answer::Sat, Answer::Unsat, Answer::Sat]);
        // A product that factors 143 only one way within 8 bits, no overflow allowed.
        let f = "(set-logic QF_BV) (declare-const p (_ BitVec 8)) (declare-const q (_ BitVec 8))
             (assert (= (bvmul ((_ zero_extend 8) p) ((_ zero_extend 8) q)) (_ bv143 16)))
             (assert (bvult #x01 p)) (assert (bvult p q))
             (assert (not (= p #x0b)))
             (check-sat)";
        assert_eq!(answers(f), vec![Answer::Unsat]);
    }
}
