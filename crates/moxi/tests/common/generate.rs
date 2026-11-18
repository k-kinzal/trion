//! A generator of MoXI scripts for the differential tests and the property
//! tests.
//!
//! The generator is driven by a seed (proptest supplies and shrinks the
//! seed) and builds the text of a script that keeps every rule of MoXI's
//! static semantics by construction, so that the reference tool accepts it:
//! it declares what it uses before using it, gives each formula sort Bool,
//! primes only what the attribute admits, connects subsystems with
//! variables of matching sorts, and names only formulas it defined.
//! [`Mutation`] then breaks exactly one rule of the static semantics; the
//! reader of this crate does not check those rules, the reference tool
//! does (tests/differential.rs).

use std::fmt::Write;

/// A small deterministic generator (xorshift64*).
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    pub fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

/// The sorts the generated scripts use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int,
    Enum,
}

impl Ty {
    fn text(&self) -> &'static str {
        match self {
            Ty::Bool => "Bool",
            Ty::Int => "Int",
            Ty::Enum => "Color",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Input,
    Output,
    Local,
}

#[derive(Debug, Clone)]
pub struct Var {
    pub name: String,
    pub ty: Ty,
    pub role: Role,
}

const COLORS: [&str; 3] = ["red", "green", "blue"];

/// The variables a formula may use, and which of them it may prime.
struct Scope<'a> {
    vars: &'a [Var],
    primes: fn(Role) -> bool,
}

impl Scope<'_> {
    fn of(&self, ty: &Ty) -> Vec<String> {
        let mut out = Vec::new();
        for v in self.vars.iter().filter(|v| v.ty == *ty) {
            out.push(v.name.clone());
            if (self.primes)(v.role) {
                out.push(format!("{}'", v.name));
            }
        }
        out
    }
}

fn int_term(rng: &mut Rng, scope: &Scope, depth: usize) -> String {
    let vars = scope.of(&Ty::Int);
    if depth == 0 || rng.chance(35) {
        return if !vars.is_empty() && rng.chance(70) { rng.pick(&vars).clone() } else if rng.chance(20) { format!("(- {})", rng.below(9)) } else { rng.below(20).to_string() };
    }
    match rng.below(5) {
        0 => format!("(+ {} {})", int_term(rng, scope, depth - 1), int_term(rng, scope, depth - 1)),
        1 => format!("(- {} {})", int_term(rng, scope, depth - 1), int_term(rng, scope, depth - 1)),
        // QF_LIA admits * only as (* c x) or (* x c) with x a free constant.
        2 if !vars.is_empty() => if rng.chance(50) { format!("(* {} {})", rng.below(5), rng.pick(&vars)) } else { format!("(* {} (- {}))", rng.pick(&vars), rng.below(5)) },
        2 => rng.below(9).to_string(),
        3 => format!("(ite {} {} {})", bool_term(rng, scope, depth - 1), int_term(rng, scope, depth - 1), int_term(rng, scope, depth - 1)),
        _ => format!("(- {})", int_term(rng, scope, depth - 1)),
    }
}

fn enum_term(rng: &mut Rng, scope: &Scope, depth: usize) -> String {
    let vars = scope.of(&Ty::Enum);
    if depth == 0 || rng.chance(50) {
        return if !vars.is_empty() && rng.chance(60) { rng.pick(&vars).clone() } else { rng.pick(&COLORS).to_string() };
    }
    format!("(ite {} {} {})", bool_term(rng, scope, depth - 1), enum_term(rng, scope, depth - 1), enum_term(rng, scope, depth - 1))
}

fn bool_term(rng: &mut Rng, scope: &Scope, depth: usize) -> String {
    let vars = scope.of(&Ty::Bool);
    if depth == 0 || rng.chance(25) {
        return if !vars.is_empty() && rng.chance(75) { rng.pick(&vars).clone() } else { rng.pick(&["true", "false"]).to_string() };
    }
    let d = depth - 1;
    match rng.below(11) {
        0 => format!("(not {})", bool_term(rng, scope, d)),
        1 => format!("(and {} {})", bool_term(rng, scope, d), bool_term(rng, scope, d)),
        2 => format!("(or {} {} {})", bool_term(rng, scope, d), bool_term(rng, scope, d), bool_term(rng, scope, d)),
        3 => format!("(=> {} {})", bool_term(rng, scope, d), bool_term(rng, scope, d)),
        4 => format!("(= {} {})", int_term(rng, scope, d), int_term(rng, scope, d)),
        5 => format!("(<= {} {})", int_term(rng, scope, d), int_term(rng, scope, d)),
        6 => format!("(> {} {})", int_term(rng, scope, d), int_term(rng, scope, d)),
        7 => format!("(distinct {} {})", int_term(rng, scope, d), int_term(rng, scope, d)),
        8 => format!("(= {} {})", enum_term(rng, scope, d), enum_term(rng, scope, d)),
        9 => format!("(xor {} {})", bool_term(rng, scope, d), bool_term(rng, scope, d)),
        _ => format!("(ite {} {} {})", bool_term(rng, scope, d), bool_term(rng, scope, d), bool_term(rng, scope, d)),
    }
}

/// A generated system: its name and variables, and its text.
#[derive(Debug, Clone)]
pub struct System {
    pub name: String,
    pub vars: Vec<Var>,
}

impl System {
    fn with(&self, role: Role) -> impl Iterator<Item = &Var> {
        self.vars.iter().filter(move |v| v.role == role)
    }
}

/// A generated check-system command: the system, the renamed variables,
/// the condition labels, the query names.
pub type Check = (String, Vec<Var>, Vec<String>, Vec<String>);

/// A generated well-formed script, with what the mutations need to know.
#[derive(Debug, Clone)]
pub struct Generated {
    pub text: String,
    pub systems: Vec<System>,
    /// For each check-system: the system, the renamed variables, the
    /// condition labels, the query names.
    pub checks: Vec<Check>,
}

fn sorted(vars: &[&Var]) -> String {
    vars.iter().map(|v| format!("({} {})", v.name, v.ty.text())).collect::<Vec<_>>().join(" ")
}

fn ty(rng: &mut Rng) -> Ty {
    match rng.below(10) {
        0..=4 => Ty::Bool,
        5..=8 => Ty::Int,
        _ => Ty::Enum,
    }
}

/// A well-formed QF_LIA script: an enumeration sort, one to three atomic
/// systems, possibly a composite system over them, and a check-system
/// command for some of them.
pub fn script(seed: u64) -> Generated {
    let mut rng = Rng::new(seed);
    let mut text = String::from("(set-logic QF_LIA)\n(declare-enum-sort Color (red green blue))\n");
    let mut systems: Vec<System> = Vec::new();
    for k in 0..1 + rng.below(3) {
        let name = format!("S{k}");
        let mut vars = Vec::new();
        for (role, prefix, max) in [(Role::Input, "i", 3), (Role::Output, "o", 3), (Role::Local, "l", 2)] {
            for j in 0..rng.below(max + 1) {
                vars.push(Var { name: format!("{prefix}{j}"), ty: ty(&mut rng), role });
            }
        }
        let all = |_| true;
        let none = |_| false;
        let _ = write!(text, "(define-system {name}");
        for (role, attribute) in [(Role::Input, "input"), (Role::Output, "output"), (Role::Local, "local")] {
            let of: Vec<&Var> = vars.iter().filter(|v| v.role == role).collect();
            if !of.is_empty() || rng.chance(30) {
                let _ = write!(text, "\n :{attribute} ({})", sorted(&of));
            }
        }
        if rng.chance(80) {
            let _ = write!(text, "\n :init {}", bool_term(&mut rng, &Scope { vars: &vars, primes: none }, 3));
        }
        if rng.chance(80) {
            let _ = write!(text, "\n :trans {}", bool_term(&mut rng, &Scope { vars: &vars, primes: all }, 3));
        }
        if rng.chance(50) {
            let _ = write!(text, "\n :inv {}", bool_term(&mut rng, &Scope { vars: &vars, primes: none }, 2));
        }
        text.push_str(")\n");
        systems.push(System { name, vars });
    }
    if rng.chance(70) {
        // A composite system: one subsystem per atomic system, inputs
        // shared, outputs into locals of their own.
        let mut vars: Vec<Var> = Vec::new();
        let mut subsys = String::new();
        for (k, sub) in systems.iter().enumerate() {
            let mut args = Vec::new();
            for input in sub.with(Role::Input) {
                let existing = vars.iter().find(|v| v.ty == input.ty && v.role == Role::Input).map(|v| v.name.clone());
                let name = match existing {
                    Some(n) if rng.chance(50) => n,
                    _ => {
                        let n = format!("x{}", vars.len());
                        vars.push(Var { name: n.clone(), ty: input.ty.clone(), role: Role::Input });
                        n
                    }
                };
                args.push(name);
            }
            for output in sub.with(Role::Output) {
                let n = format!("y{}", vars.len());
                let role = if rng.chance(50) { Role::Output } else { Role::Local };
                vars.push(Var { name: n.clone(), ty: output.ty.clone(), role });
                args.push(n);
            }
            let _ = write!(subsys, "\n :subsys (N{k} ({}{}{}))", sub.name, if args.is_empty() { "" } else { " " }, args.join(" "));
        }
        let name = "Top".to_string();
        let _ = write!(text, "(define-system {name}");
        for (role, attribute) in [(Role::Input, "input"), (Role::Output, "output"), (Role::Local, "local")] {
            let of: Vec<&Var> = vars.iter().filter(|v| v.role == role).collect();
            let _ = write!(text, "\n :{attribute} ({})", sorted(&of));
        }
        text.push_str(&subsys);
        if rng.chance(50) {
            let _ = write!(text, "\n :inv {}", bool_term(&mut rng, &Scope { vars: &vars, primes: |_| false }, 2));
        }
        text.push_str(")\n");
        systems.push(System { name, vars });
    }
    let mut checks = Vec::new();
    for system in systems.clone() {
        if rng.chance(40) {
            continue;
        }
        let renamed: Vec<Var> = system.vars.iter().map(|v| Var { name: format!("{}_r", v.name), ty: v.ty.clone(), role: v.role }).collect();
        let _ = write!(text, "(check-system {}", system.name);
        for (role, attribute) in [(Role::Input, "input"), (Role::Output, "output"), (Role::Local, "local")] {
            let of: Vec<&Var> = renamed.iter().filter(|v| v.role == role).collect();
            let _ = write!(text, "\n :{attribute} ({})", sorted(&of));
        }
        let mut labels = Vec::new();
        let mut kinds = Vec::new();
        for k in 0..1 + rng.below(4) {
            let (keyword, primes): (&str, fn(Role) -> bool) = match rng.below(4) {
                0 => ("assumption", |r| r == Role::Input),
                1 => ("fairness", |r| r == Role::Input),
                2 => ("reachable", |_| true),
                _ => ("current", |_| false),
            };
            let label = format!("c{k}");
            let _ = write!(text, "\n :{keyword} ({label} {})", bool_term(&mut rng, &Scope { vars: &renamed, primes }, 2));
            labels.push(label);
            kinds.push(keyword);
        }
        let mut queries = Vec::new();
        for q in 0..1 + rng.below(3) {
            let mut chosen: Vec<String> = Vec::new();
            let mut current = false;
            for (label, kind) in labels.iter().zip(&kinds) {
                if rng.chance(60) && !(*kind == "current" && current) {
                    current |= *kind == "current";
                    chosen.push(label.clone());
                }
            }
            let name = format!("q{q}");
            let _ = write!(text, "\n :query ({name} ({}))", chosen.join(" "));
            queries.push(name);
        }
        text.push_str(")\n");
        checks.push((system.name.clone(), renamed, labels, queries));
    }
    Generated { text, systems, checks }
}

/// One rule of the static semantics, broken.
#[derive(Debug, Clone, Copy)]
pub enum Mutation {
    /// A system declares a variable twice.
    DuplicateVariable,
    /// `:init` contains a next-state variable.
    PrimeInInit,
    /// A formula has sort Int.
    IntFormula,
    /// A system is defined twice.
    Redefinition,
    /// A subsystem instantiates a system not yet defined.
    UndefinedSubsystem,
    /// A query names a formula that does not exist.
    UndefinedLabel,
    /// `check-system` renames one variable too many.
    RenamingArity,
    /// A variable has the name of a theory function symbol.
    TheorySymbolVariable,
    /// `and` with one argument.
    UnaryAnd,
    /// An assumption primes an output.
    PrimedOutputInAssumption,
}

pub const MUTATIONS: [Mutation; 10] = [
    Mutation::DuplicateVariable,
    Mutation::PrimeInInit,
    Mutation::IntFormula,
    Mutation::Redefinition,
    Mutation::UndefinedSubsystem,
    Mutation::UndefinedLabel,
    Mutation::RenamingArity,
    Mutation::TheorySymbolVariable,
    Mutation::UnaryAnd,
    Mutation::PrimedOutputInAssumption,
];

/// `generated` with `mutation` applied: a script that breaks exactly that
/// rule (and is otherwise the generated script, followed by the commands
/// the mutation adds).
pub fn mutate(generated: &Generated, mutation: Mutation) -> String {
    let mut text = generated.text.clone();
    let first = &generated.systems[0].name;
    let suffix = match mutation {
        Mutation::DuplicateVariable => "(define-system Bad :input ((a Bool)) :local ((a Int)))\n".to_string(),
        Mutation::PrimeInInit => "(define-system Bad :output ((a Int)) :init (= a' 0))\n".to_string(),
        Mutation::IntFormula => "(define-system Bad :output ((a Int)) :inv (+ a 1))\n".to_string(),
        Mutation::Redefinition => format!("(define-system {first})\n"),
        Mutation::UndefinedSubsystem => "(define-system Bad :subsys (N (Later)))\n(define-system Later)\n".to_string(),
        Mutation::UndefinedLabel => format!("(check-system {first} :query (q (nowhere)))\n").replace(&format!("(check-system {first} "), &format!("(check-system {first} {} ", renaming(&generated.systems[0], ""))),
        Mutation::RenamingArity => {
            let system = &generated.systems[0];
            let inputs: Vec<&Var> = system.with(Role::Input).collect();
            format!("(check-system {first} :input ({} (extra Bool)))\n", sorted(&inputs))
        }
        Mutation::TheorySymbolVariable => "(define-system Bad :input ((distinct Bool)))\n".to_string(),
        Mutation::UnaryAnd => "(define-system Bad :output ((a Bool)) :init (and a))\n".to_string(),
        Mutation::PrimedOutputInAssumption => "(define-system Bad :input ((a Bool)) :output ((b Bool)))\n(check-system Bad :input ((a Bool)) :output ((b Bool)) :assumption (h b') :query (q (h)))\n".to_string(),
    };
    text.push_str(&suffix);
    text
}

/// The `:input`/`:output`/`:local` attributes renaming `system`'s
/// variables with `suffix` appended.
fn renaming(system: &System, suffix: &str) -> String {
    let mut out = String::new();
    for (role, attribute) in [(Role::Input, "input"), (Role::Output, "output"), (Role::Local, "local")] {
        let of: Vec<Var> = system.with(role).map(|v| Var { name: format!("{}{suffix}", v.name), ..v.clone() }).collect();
        let refs: Vec<&Var> = of.iter().collect();
        let _ = write!(out, ":{attribute} ({}) ", sorted(&refs));
    }
    out
}
