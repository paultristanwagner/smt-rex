//! Writing the proof: input clauses, resolution steps from the LRAT log, theory lemmas.

use crate::arith::real_literal;
use crate::sexp::quote_symbol;
use rustc_hash::{FxHashMap, FxHashSet};
use smtrex_core::Lit;
use smtrex_sat::proof::{ClauseId, Step};
use smtrex_term::TermId;
use std::io::{self, Write};

use super::*;

impl Encoder<'_> {
    /// Write the proof: the assumptions first (Carcara expects them before any step), then
    /// every other step in order.
    pub(super) fn write(&self, steps: &[Step], out: &mut impl Write) -> io::Result<()> {
        // Definitions of the shared terms, each after the ones it uses.
        let arena = self.b.euf_ref().arena();
        for i in 0..arena.num_terms() {
            let t = TermId::from_index(i);
            let args = arena.args_of(t);
            if args.is_empty() {
                continue;
            }
            let Some(sort) = self.node_sorts.get(&t) else {
                continue;
            };
            let args: Vec<String> = args.iter().map(|&a| node_text(arena, a)).collect();
            let f = quote_symbol(arena.name_of(t));
            writeln!(out, "(define-fun @t{i} () {sort} ({f} {}))", args.join(" "))?;
        }
        for (i, t) in self.terms.iter().enumerate() {
            if let Some((body, true)) = t {
                writeln!(out, "(define-fun @v{i} () Bool {body})")?;
            }
        }
        for (s, (_, how)) in steps
            .iter()
            .filter(|s| matches!(s, Step::Input { .. }))
            .zip(&self.hows)
        {
            if let (Step::Input { id, .. }, How::Assume(term)) = (s, how) {
                writeln!(out, "(assume c{id} {term})")?;
            }
        }
        let mut inputs = self.hows.iter();
        let mut bases: FxHashMap<String, usize> = FxHashMap::default();
        let mut ites: FxHashMap<String, String> = FxHashMap::default();
        for s in steps {
            match s {
                Step::Input { id, .. } => {
                    let (parts, how) = inputs.next().ok_or_else(|| {
                        io::Error::other("an input clause without a justification")
                    })?;
                    // The rule's clause, and the double negations it contains.
                    let texts: Vec<String> = parts
                        .iter()
                        .map(|&p| match p {
                            L(l) => self.render(l),
                            N(c) => format!("(not {})", self.render(c)),
                        })
                        .collect();
                    let doubled: Vec<String> = parts
                        .iter()
                        .filter_map(|&p| match p {
                            N(c) if c.is_negated() => Some(self.render(!c)),
                            _ => None,
                        })
                        .collect();
                    let cl = format!("(cl {})", texts.join(" "));
                    let name = if doubled.is_empty() {
                        format!("c{id}")
                    } else {
                        format!("c{id}_rule")
                    };
                    match how {
                        How::Assume(_) => {}
                        How::Rule(rule) => {
                            writeln!(out, "(step {name} {cl} :rule {rule})")?;
                        }
                        How::Lra => {
                            let lits: Vec<Lit> = parts.iter().map(|p| p.lit()).collect();
                            let ys = self.farkas(&lits).map_err(io::Error::other)?;
                            let args: Vec<String> = ys.iter().map(real_literal).collect();
                            writeln!(
                                out,
                                "(step {name} {cl} :rule la_generic :args ({}))",
                                args.join(" ")
                            )?;
                        }
                        How::Ite { ite, u, then } => {
                            let k = match ites.get(ite) {
                                Some(k) => k.clone(),
                                None => {
                                    // (= true (and true U)) by ite_intro, hence U.
                                    let k = format!("i{}", ites.len());
                                    let and = format!("(and true {u})");
                                    writeln!(
                                        out,
                                        "(step {k}_i (cl (= true {and})) :rule ite_intro)"
                                    )?;
                                    writeln!(out, "(step {k}_e (cl (not true) {and}) :rule equiv1 :premises ({k}_i))")?;
                                    writeln!(out, "(step {k}_t (cl true) :rule true)")?;
                                    writeln!(out, "(step {k}_r (cl {and}) :rule resolution :premises ({k}_e {k}_t))")?;
                                    writeln!(out, "(step {k}_u (cl {u}) :rule and :premises ({k}_r) :args (1))")?;
                                    ites.insert(ite.clone(), k.clone());
                                    k
                                }
                            };
                            let rule = if *then { "ite2" } else { "ite1" };
                            writeln!(out, "(step {name} {cl} :rule {rule} :premises ({k}_u))")?;
                        }
                        How::Diseq => {
                            let or = texts.join(" ");
                            writeln!(out, "(step {name}_d (cl (or {or})) :rule la_disequality)")?;
                            writeln!(out, "(step {name} {cl} :rule or :premises ({name}_d))")?;
                        }
                        How::RuleAt(rule, i) => {
                            writeln!(out, "(step {name} {cl} :rule {rule} :args ({i}))")?;
                        }
                        How::Equiv { rule, base, side } => {
                            let k = match bases.get(base) {
                                Some(&k) => k,
                                None => {
                                    let k = bases.len();
                                    writeln!(out, "(step e{k} (cl {base}) :rule {rule})")?;
                                    bases.insert(base.clone(), k);
                                    k
                                }
                            };
                            writeln!(out, "(step {name} {cl} :rule equiv{side} :premises (e{k}))")?;
                        }
                    }
                    if !doubled.is_empty() {
                        // (not (not t)) resolves against not_not's (cl (not (not (not t))) t).
                        let mut premises = vec![name];
                        for (k, t) in doubled.iter().enumerate() {
                            let n = format!("c{id}_nn{k}");
                            writeln!(
                                out,
                                "(step {n} (cl (not (not (not {t}))) {t}) :rule not_not)"
                            )?;
                            premises.push(n);
                        }
                        let lits: Vec<Lit> = parts.iter().map(|p| p.lit()).collect();
                        writeln!(
                            out,
                            "(step c{id} {} :rule resolution :premises ({}))",
                            self.render_clause(&lits),
                            premises.join(" ")
                        )?;
                    }
                }
                Step::Derived { id, lits, hints } => {
                    let cl = self.render_clause(lits);
                    let premises = hints
                        .iter()
                        .rev()
                        .map(|h| format!("c{h}"))
                        .collect::<Vec<_>>()
                        .join(" ");
                    let rule = if hints.len() == 1 {
                        "contraction"
                    } else {
                        "resolution"
                    };
                    writeln!(out, "(step c{id} {cl} :rule {rule} :premises ({premises}))")?;
                }
                Step::Theory { id, lits } => {
                    if lits
                        .iter()
                        .all(|l| self.b.lra_ref().atom_of(l.var()).is_some())
                    {
                        let ys = self.farkas(lits).map_err(io::Error::other)?;
                        let args: Vec<String> = ys.iter().map(real_literal).collect();
                        writeln!(
                            out,
                            "(step c{id} {} :rule la_generic :args ({}))",
                            self.render_clause(lits),
                            args.join(" ")
                        )?;
                    } else {
                        self.euf_lemma(*id, lits, out)?;
                    }
                }
                Step::Delete { .. } => {}
            }
        }
        Ok(())
    }

    /// Prove the EUF lemma `lits` (one equality, implied by the negations of the others) and
    /// name it `c{id}`.
    pub(super) fn euf_lemma(
        &self,
        id: ClauseId,
        lits: &[Lit],
        out: &mut impl Write,
    ) -> io::Result<()> {
        let euf = self.b.euf_ref();
        let mut premises = Vec::new();
        let mut goal = None;
        for &l in lits {
            let (a, b) = euf
                .atom(l.var())
                .ok_or_else(|| io::Error::other("a theory lemma over a non-equality atom"))?;
            if l.is_negated() {
                premises.push((a, b, self.render(!l)));
            } else if goal.replace((a, b)).is_some() {
                return Err(io::Error::other(
                    "an EUF lemma with two positive equalities",
                ));
            }
        }
        let (ga, gb) = goal.ok_or_else(|| io::Error::other("an EUF lemma without a conclusion"))?;
        let mut cc = Closure::new(euf.arena(), &premises, [ga, gb]);
        if cc.find(ga) != cc.find(gb) {
            return Err(io::Error::other(format!(
                "EUF lemma {} does not follow",
                self.render_clause(lits)
            )));
        }
        let mut w = LemmaWriter {
            cc: &mut cc,
            arena: euf.arena(),
            premises: premises.iter().map(|(_, _, t)| t.clone()).collect(),
            prefix: format!("q{id}_"),
            steps: Vec::new(),
            memo: FxHashMap::default(),
            used: FxHashSet::default(),
        };
        let top = w.prove(ga, gb);
        let used = std::mem::take(&mut w.used);
        let steps = std::mem::take(&mut w.steps);
        for (_, _, line) in &steps {
            out.write_all(line.as_bytes())?;
        }
        let Proved::Step(top_name, _) = top else {
            return Err(io::Error::other(
                "an EUF lemma whose conclusion is a premise",
            ));
        };
        // The resolvent: the used premises, negated, and the goal.
        let mut resolvent: Vec<String> = premises
            .iter()
            .enumerate()
            .filter(|(i, _)| used.contains(i))
            .map(|(_, (_, _, p))| format!("(not {p})"))
            .collect();
        resolvent.push(self.render(lits.iter().copied().find(|l| !l.is_negated()).unwrap()));
        let names: Vec<&str> = steps.iter().map(|(n, _, _)| n.as_str()).collect();
        let (last, prefix) = if names.len() == 1 {
            (top_name, steps[0].1.clone())
        } else {
            let r = format!("q{id}_r");
            // Pre-order: each clause comes after the one that needs its conclusion.
            writeln!(
                out,
                "(step {r} (cl {}) :rule resolution :premises ({}))",
                resolvent.join(" "),
                names.iter().rev().copied().collect::<Vec<_>>().join(" ")
            )?;
            (r, resolvent)
        };
        // Weakening keeps the premise's literals as a prefix and adds the lemma's other ones.
        let mut full = prefix.clone();
        for &l in lits {
            let t = self.render(l);
            if !full.contains(&t) {
                full.push(t);
            }
        }
        writeln!(
            out,
            "(step c{id} (cl {}) :rule weakening :premises ({last}))",
            full.join(" ")
        )?;
        Ok(())
    }
}
