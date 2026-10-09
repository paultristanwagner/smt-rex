//! Bit-vector terms.

use crate::bv::{self, Bits, Op};
use crate::sexp::Sexp;

use super::*;

impl Encoder<'_> {
    /// The bits of a bit-vector-sorted term.
    pub(crate) fn bits(&mut self, t: &Sexp) -> Result<Bits, String> {
        if let Some(b) = self.resolve(t)? {
            return match b {
                Bound::Bits(v) => Ok(v),
                other => Err(format!(
                    "expected a bit-vector, got a value of sort {}",
                    other.sort()
                )),
            };
        }
        if let Some((v, w)) = bv::literal(t)? {
            return Ok(self.bv.constant(&v, w));
        }
        match t {
            Sexp::Atom(name) => {
                if let Some(v) = self.bv_vars.get(name) {
                    return Ok(v.clone());
                }
                let w = self
                    .sigs
                    .get(name)
                    .and_then(|(_, ret)| bv::width(ret))
                    .ok_or_else(|| format!("'{name}' is not a bit-vector constant"))?;
                let v: Bits = (0..w).map(|_| self.builder.fresh_var().pos()).collect();
                self.bv_vars.insert(name.clone(), v.clone());
                Ok(v)
            }
            Sexp::List(l) => {
                if l.first().and_then(Sexp::as_atom) == Some("ite") {
                    let [_, c, x, y] = &l[..] else {
                        return Err("ite expects 3 arguments".to_string());
                    };
                    let c = self.bool(c)?;
                    let (x, y) = (self.bits(x)?, self.bits(y)?);
                    return Ok(self.bv.mux_bits(&mut self.builder, c, &x, &y));
                }
                let op = l
                    .first()
                    .map(Op::parse)
                    .transpose()?
                    .flatten()
                    .ok_or_else(|| format!("unsupported bit-vector term {t}"))?;
                let args = self.bits_all(&l[1..])?;
                Ok(self.bv.apply(&mut self.builder, op, &args))
            }
        }
    }

    pub(crate) fn bits_all(&mut self, ts: &[Sexp]) -> Result<Vec<Bits>, String> {
        ts.iter().map(|t| self.bits(t)).collect()
    }

    // ----- polynomial arithmetic (QF_NRA) -----
}
