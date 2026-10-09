//! Compact propositional variables and literals.
//!
//! A [`Lit`] is packed into a single `u32` as `var << 1 | sign`, so the literal value
//! doubles as a dense index into per-literal arrays (e.g. watch lists of size `2 * nvars`).

/// A propositional variable, identified by a dense 0-based index.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Var(u32);

impl Var {
    #[inline]
    pub fn from_index(i: usize) -> Var {
        Var(i as u32)
    }
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
    /// The positive literal of this variable.
    #[inline]
    pub fn pos(self) -> Lit {
        Lit::new(self, false)
    }
    /// The negative literal of this variable (pairs with `pos`; not `std::ops::Neg`, which
    /// would read as negating the variable itself).
    #[inline]
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Lit {
        Lit::new(self, true)
    }
}

/// A literal: a variable together with a polarity. `negated == true` means `¬var`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Lit(u32);

impl Lit {
    #[inline]
    pub fn new(var: Var, negated: bool) -> Lit {
        Lit((var.0 << 1) | (negated as u32))
    }
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }
    #[inline]
    pub fn is_negated(self) -> bool {
        (self.0 & 1) == 1
    }
    /// Dense index `0 ..= 2*nvars-1`, suitable for indexing per-literal arrays.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
    #[inline]
    pub fn code(self) -> u32 {
        self.0
    }
    #[inline]
    pub fn from_code(code: u32) -> Lit {
        Lit(code)
    }

    /// Parse a non-zero DIMACS literal (`1` -> var 0 positive, `-1` -> var 0 negative).
    #[inline]
    pub fn from_dimacs(i: i32) -> Lit {
        debug_assert!(i != 0, "DIMACS literal must be non-zero");
        Lit::new(Var(i.unsigned_abs() - 1), i < 0)
    }
    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let v = (self.var().0 as i32) + 1;
        if self.is_negated() {
            -v
        } else {
            v
        }
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;
    /// Flip the polarity.
    #[inline]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

/// Three-valued logic value used for partial assignments.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Lbool {
    False = 0,
    True = 1,
    Undef = 2,
}

impl Lbool {
    #[inline]
    pub fn from_bool(b: bool) -> Lbool {
        if b {
            Lbool::True
        } else {
            Lbool::False
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lit_packing_roundtrips() {
        for vi in 0..1000usize {
            let v = Var::from_index(vi);
            let p = v.pos();
            let n = v.neg();
            assert_eq!(p.var(), v);
            assert_eq!(n.var(), v);
            assert!(!p.is_negated());
            assert!(n.is_negated());
            assert_eq!(!p, n);
            assert_eq!(!n, p);
            assert_eq!(!!p, p);
            // index is dense and distinct
            assert_eq!(p.index(), 2 * vi);
            assert_eq!(n.index(), 2 * vi + 1);
        }
    }

    #[test]
    fn dimacs_roundtrips() {
        for d in [1, -1, 2, -2, 42, -42, 1000, -1000] {
            let l = Lit::from_dimacs(d);
            assert_eq!(l.to_dimacs(), d);
        }
        assert!(Lit::from_dimacs(-3).is_negated());
        assert_eq!(Lit::from_dimacs(3).var(), Var::from_index(2));
    }
}
