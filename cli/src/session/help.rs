//! The `help` command and the command table it shares with tab completion.

use super::Session;
use std::io::{self, Write};

pub struct CommandHelp {
    pub name: &'static str,
    pub aliases: &'static [&'static str],
    pub usage: &'static str,
    pub summary: &'static str,
    pub details: &'static str,
}

pub const COMMANDS: &[CommandHelp] = &[
    CommandHelp {
        name: "sat",
        aliases: &[],
        usage: "sat <formula>",
        summary: "is a propositional formula satisfiable? shows a model",
        details: "Any propositional formula, not only CNF.\n\
                  Operators: ~ not, & and, | or, -> implies, <-> iff, true, false, parentheses.\n\n\
                  Examples:\n  \
                  sat (a | b) & (~a | c) & ~c\n  \
                  sat (a -> b) & (b -> c) & a & ~c\n  \
                  sat (p <-> ~q) & (q <-> ~r) & (r <-> ~p)",
    },
    CommandHelp {
        name: "allsat",
        aliases: &["models"],
        usage: "allsat [-n <limit>] <formula>",
        summary: "list the models of a propositional formula",
        details: "Lists every satisfying assignment of the formula's variables, up to the\n\
                  limit (default 100).\n\n\
                  Examples:\n  \
                  allsat a | b\n  \
                  allsat -n 5 (a | b | c | d)",
    },
    CommandHelp {
        name: "smt",
        aliases: &[],
        usage: "smt <logic> <formula>",
        summary: "equality logic or linear real arithmetic (QF_LRA)",
        details: "QF_EQ and QF_EQUF: atoms are equalities a = b and disequalities a != b,\n\
                  combined with the same operators as in sat. QF_EQUF also allows functions:\n\
                  f(x), g(x, y). The model lists which terms are equal: each line is one value.\n\n\
                  QF_LRA: atoms are linear constraints over real variables, compared with\n\
                  <=, <, >=, >, = or !=. Coefficients are integers, decimals or fractions,\n\
                  written against the variable: 2x, 0.8y, 1/2z (or 2*x). The model is exact.\n\
                  A conjunct min(t) or max(t) asks for an optimum: SMT-Rex reports the exact\n\
                  value, or that it is unbounded, or that it is approached but never reached.\n\n\
                  Examples:\n  \
                  smt QF_EQ (a = b) & (b = c) & (a != c | c != d)\n  \
                  smt QF_EQUF (x1 = x2) & (x2 = x3) & (x4 = x5) & (f(x1) != f(x5))\n  \
                  smt QF_EQUF (f(f(y)) != x) & (x = f(y)) & (y = u) & (x = y)\n  \
                  smt QF_LRA (x<=-3 | x>=3) & (y=5) & (x+y>=12)\n  \
                  smt QF_LRA (x<=0 | x>=5) & (x+y=5/2) & (y=1)\n  \
                  smt QF_LRA (x < 3) & (x > 2) & (x != 5/2)\n  \
                  smt QF_LRA (x<=-3 | x>=3) & (y=5) & (x+y>=12) & (min(x))\n  \
                  smt QF_LRA (x<=0 | x>=5) & (max(x))",
    },
    CommandHelp {
        name: "simplex",
        aliases: &[],
        usage: "simplex <constraint> ...",
        summary: "are linear constraints feasible? shows a solution",
        details: "Linear constraints over the reals, side by side, in the syntax of\n\
                  smt QF_LRA: x+y>=10 x-y<=5. A constraint may contain spaces\n\
                  (x + y >= 10); a sign that starts a word starts a new constraint\n\
                  (x>=1 -y<=5). The solution is exact. One min(t) or max(t) asks for an\n\
                  optimum; feasible problems are never reported unsat, even if unbounded.\n\n\
                  Examples:\n  \
                  simplex x+y>=10 x-y<=5 1/2x-y<=0\n  \
                  simplex a+3b+5c=30 a>=5 a<=10 b>=2 c>=1\n  \
                  simplex x+y=3 y=1 x<=1\n  \
                  simplex max(x+y) x+2y<=4 3x+y<=6 x>=0 y>=0\n  \
                  simplex min(x) x+y>=10 x-y<=5 1/2x-y<=0",
    },
    CommandHelp {
        name: "tseitin",
        aliases: &["tseytin"],
        usage: "tseitin <formula>",
        summary: "Tseitin's transformation into an equisatisfiable CNF",
        details: "Helper variables are named h0, h1, ..., skipping any name the formula uses.\n\
                  The output is valid input for sat.\n\n\
                  Examples:\n  \
                  tseitin a -> b -> c\n  \
                  tseitin ~(a <-> b | c)",
    },
    CommandHelp {
        name: "smtlib",
        aliases: &[],
        usage: "smtlib <file>",
        summary: "run an SMT-LIB 2.6 script",
        details: "Runs the script in a fresh solver and shows every response, with the time\n\
                  each check-sat took and whether it matches the file's :status. The script\n\
                  can also be given inline.\n\n\
                  Examples:\n  \
                  smtlib problem.smt2\n  \
                  smtlib (declare-const p Bool)(assert (and p (not p)))(check-sat)",
    },
    CommandHelp {
        name: "dimacs",
        aliases: &[],
        usage: "dimacs <file>",
        summary: "solve a DIMACS CNF file",
        details: "Example:\n  dimacs problem.cnf",
    },
    CommandHelp {
        name: "read",
        aliases: &[],
        usage: "read <file>",
        summary: "run the commands in a file, one per line",
        details: "Blank lines and lines starting with # are skipped. A multi-line SMT-LIB\n\
                  command is read until its parentheses balance.",
    },
    CommandHelp {
        name: "clear",
        aliases: &["cls"],
        usage: "clear",
        summary: "clear the screen",
        details: "",
    },
    CommandHelp {
        name: "help",
        aliases: &["?"],
        usage: "help [command]",
        summary: "this list, or details and examples for one command",
        details: "",
    },
    CommandHelp {
        name: "exit",
        aliases: &["quit"],
        usage: "exit",
        summary: "quit (also Ctrl-D)",
        details: "",
    },
];

pub(super) fn find_command(word: &str) -> Option<&'static CommandHelp> {
    COMMANDS
        .iter()
        .find(|c| c.name == word || c.aliases.contains(&word))
}

impl Session {
    pub(super) fn help(&self, topic: &str, out: &mut dyn Write) -> io::Result<()> {
        if !topic.is_empty() {
            let Some(cmd) = find_command(topic) else {
                return self.fail(&format!("no command '{topic}'"), out);
            };
            writeln!(
                out,
                "{}  {}",
                self.style.bold(cmd.usage),
                self.style.dim(cmd.summary)
            )?;
            if !cmd.aliases.is_empty() {
                writeln!(
                    out,
                    "{}",
                    self.style.dim(&format!("also: {}", cmd.aliases.join(", ")))
                )?;
            }
            if !cmd.details.is_empty() {
                writeln!(out, "\n{}", cmd.details)?;
            }
            return Ok(());
        }
        let width = COMMANDS.iter().map(|c| c.usage.len()).max().unwrap_or(0);
        writeln!(out, "{}", self.style.bold("Commands"))?;
        for c in COMMANDS {
            writeln!(out, "  {:<width$}  {}", c.usage, self.style.dim(c.summary))?;
        }
        writeln!(
            out,
            "  {:<width$}  {}",
            "(smt-lib command)",
            self.style
                .dim("e.g. (declare-const p Bool); state is kept between lines")
        )?;
        writeln!(
            out,
            "\n{}  ~ not  & and  | or  -> implies  <-> iff  ( )",
            self.style.bold("Formulas")
        )?;
        writeln!(
            out,
            "{}  2x + 0.8y - 1/2z <= 3  (also < >= > = !=)",
            self.style.bold("Linear  ")
        )?;
        writeln!(
            out,
            "{}",
            self.style
                .dim("Type help <command> for examples. Ctrl-C stops a long solve.")
        )
    }
}
