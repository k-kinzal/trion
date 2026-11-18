//! The examples of description.md (ModelChecker/IL commit
//! b5156d5ead225fceb37a40b1ec337968ea2c767b), verbatim, section by section.
//! Each constant is the text of one fenced block, character for character
//! (line numbers of that file in the comment). Each test states whether the
//! reader accepts the example and, if not, which rule of the grammar it
//! breaks, at which line and column; where the example has a lexical or
//! syntactic slip, the test also reads the corrected text and names each
//! change. Every example that is read is printed and read back to an equal
//! value.
//!
//! Static semantics is not checked (crate documentation, "Scope"), so an
//! example that is grammatical but ill-sorted or redefines a name is read;
//! the tests say so where the document's own text makes such a point.

use std::str::FromStr;
use moxi::response::{Answer, CheckSystemResponse, ResponseItem, Verbosity};
use moxi::{CheckAttribute, Command, ErrorKind, Script};

/// Reads `text`, requires it to be read, and requires its printed form to
/// read back to the same script and to print to the same text.
fn read(text: &str) -> Script {
    let script = Script::from_str(text).unwrap_or_else(|e| panic!("rejected: {e}\n{text}"));
    let printed = script.to_string();
    let reread = Script::from_str(&printed).unwrap_or_else(|e| panic!("printed form rejected: {e}\n{printed}"));
    assert_eq!(reread, script, "{printed}");
    assert_eq!(reread.to_string(), printed);
    script
}

/// Reads `text` and requires an error of `kind` at `at` (line, column).
fn rejected(text: &str, kind: ErrorKind, at: (usize, usize)) -> moxi::Error {
    let error = Script::from_str(text).map(|s| panic!("read:\n{text}\n{s:?}")).unwrap_err();
    assert_eq!(error.kind(), kind, "{error}");
    assert_eq!((error.position().unwrap().line(), error.position().unwrap().column()), at, "{error}");
    error
}

/// The 1-based line and column of the first occurrence of `needle`.
fn line_column(text: &str, needle: &str) -> (usize, usize) {
    let offset = text.find(needle).unwrap();
    let before = &text[..offset];
    let line = before.matches('\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    (line, column)
}

fn system(script: &Script, index: usize) -> &moxi::DefineSystem {
    match &script.commands()[index] {
        Command::DefineSystem(s) => s,
        other => panic!("not a define-system: {other}"),
    }
}

// description.md lines 359-361.
const DECLARE_SORT: &str = r#"  (declare-sort A 0)
  (declare-sort Set 1)
  ; possible sorts: A, (Set A), (Set (Set A)), (Array Int Real), ...
"#;

// description.md lines 370-373.
const DEFINE_SORT: &str = r#"  (declare-sort NestedSet (X) (Set (Set X)))
  ; possible sorts: (NestedSet A), ...
  (declare-sort Array2 (X Y) (Array X (Array X Y)))
  ; possible sorts: (Array2 Int Bool), ...
"#;

// description.md lines 382-383.
const DECLARE_CONST: &str = r#"  (declare-const a A)
  (declare-const n Int)
"#;

// description.md lines 393-395.
const DEFINE_FUN: &str = r#"  (declare-fun sq ((n Int)) Int (* n n))
  (declare-fun isSqRoot ((m Int) (n Int)) Bool (= n (sq m)))
  (declare-fun max ((m Int) (n Int)) Int (ite (> m n) m n))
"#;

// description.md lines 407-407.
const SET_LOGIC: &str = r#"  (set-logic QF_BV)
"#;

// description.md lines 570-573.
const DELAY: &str = r#"(define-system Delay :input ( (i Int) ) :output ( (o Int) )
 :init (= o 0)
 :trans (= o' i) ; the new output is the old input
)
"#;

// description.md lines 579-582.
const DELAY_RANGE: &str = r#"(define-system Delay :input ( (i Int) ) :output ( (o Int) )
 :init (<= 0 o 10) ; more than one possible initial output
 :trans (= o' i)
)
"#;

// description.md lines 589-594.
const STUTTERING_CLOCKED_COPY: &str = r#"(define-system StutteringClockedCopy
 :input ((clock Bool) (i Int))
 :output ((o Int))
 :init (=> clock (= o i)) ; o is arbitrary when clock is false 
 :trans (ite clock (= o’ i’) (= o’ o)) ; ite is if-then-else
)
"#;

// description.md lines 602-605.
const EVENT: &str = r#"(declare-datatype Event (par (X) (
  (absent)
  (present (val X))
)))
"#;

// description.md lines 611-615.
const LOSSY_INT_CHANNEL: &str = r#"(define-system LossyIntChannel
 :input ((i (Event Int)))
 :output ((o (Event Int)))
 :inv (or (= o i) (= o absent))
)
"#;

// description.md lines 621-628.
const LOSSY_INT_CHANNEL_LOCAL: &str = r#"(define-system LossyIntChannel
 :input ((i (Event Int))) 
 :output ((o (Event Int)))
 :local ((s Bool))
 ; at all times, whether the input event is transmitted 
 ; or not depends on value of s
 :inv (= o (ite s i absent))
)
"#;

// description.md lines 637-657.
const TIMED_SWITCH1: &str = r#"(declare-enum-sort LightStatus (on off))

(define-system TimedSwitch1
 :input ( (press Bool) )
 :output ( (sig Bool) )
 :local ( (s LightStatus) (n Int) )
 :inv (= sig (= s on))
 :init (and
   (= n 0)
   (ite press (= s on) (= s off))
 )
 :trans (let
  (; transitions
   (stay-off (and (= s off) (not press') (= s' off) (= n' n)))
   (turn-on  (and (= s off) press' (= s' on) (= n' n)))
   (stay-on  (and (= s on) (not press') (< n 10) (= s' on) (= n' (+ n 1))))
   (turn-off (and (= s on) (or press' (>= n 10)) (= s' off) (= n' 0)))
  )
  (or stay-off turn-on turn-off stay-on)
 )
)
"#;

// description.md lines 664-683.
const TIMED_SWITCH2: &str = r#"(define-system TimedSwitch2
 :input ( (press Bool) )
 :output ( (sig Bool) )
 :local ( (s LightStatus) (n Int) )
 :inv (= sig (= s on))
 :init (and
    (= n 0)
    (ite press (= s on) (= s off))
  )
 :trans (and
   (=> (and (= s off) (not press'))
       (and (= s' off) (= n' n)))            ; off --> off
   (=> (and (= s off) press')
       (and (= s' on) (= n' n)))             ; off --> on
   (=> (and (= s on) (not press') (< 10 n))
        (and (= s' on) (= n' (+ n 1))))      ; on --> on
   (=> (and (= s on) (or press' (>= n 10)))
       (and (= s' off) (= n' 0)))            ; on --> off
  )
)
"#;

// description.md lines 689-709.
const TIMED_SWITCH3: &str = r#"(define-fun flip ((s LightStatus)) LightStatus
  (ite (= s off) on off)
)

(define-system TimedSwitch3
 :input ( (press Bool) )
 :output ( (sig Bool) )
 :local ( (s LightStatus) (n Int) )
 :inv (= sig (= s on))
 :init (and
   (= n 0)
   (= s (ite press on off))
 )
 :trans (and
   (= s' (ite press' (flip s)
            (ite (or (= s off) (>= n 10)) off
              on)))
   (= n' (ite (or (= s off) (= s' off)) 0
            (+ n 1)))
  )
)
"#;

// description.md lines 723-739.
const NON_DET_ARBITER: &str = r#"(define-system NonDetArbiter
 :input ( (r1 Bool) (r2 Bool) )
 :output ( (g1 Bool) (g2 Bool) )
 :local ( (s Bool) )
 :inv (and
  (=> (and (not r1) (not r2))
      (and (not g1) (not g2)))
  (=> (and r1 (not r2))
      (and g1 (not g2)))
  (=> (and (not r1) r2)
      (and (not g1) g2))
  (=> (and r1 r2)
      ; the unconstrained value of `s` is used as non-deterministic choice
      (ite s (and g1 (not g2))
        (and (not g1) g2)))
  )
)
"#;

// description.md lines 746-761.
const DELAYED_ARBITER: &str = r#"(define-system DelayedArbiter
 :input ( (r1 Bool) (r2 Bool) )
 :output ( (g1 Bool) (g2 Bool) )
 :local ( (s Bool) )
 :init ( and (not g1) (not g2) )  ; nothing is granted initially
 :trans (and
    (=> (and (not r1) (not r2))
        (and (not g1') (not g2')))
    (=> (and r1 (not r2))
        (and g1' (not g2')))
    (=> (and (not r1) r2)
        (and (not g1') g2'))
    (=> (and r1 r2)
        (!= g1' g2'))
  )
)
"#;

// description.md lines 767-783.
const INT_NON_DET_ARBITER: &str = r#"(define-system IntNonDetArbiter
  :input ( (r1 (Event Int)) (r2 (Event Int)) )
  :output ( (g1 (Event Int)) (g2 (Event Int)) )
  :local ( (s Bool) )
  :init (= g1 g2 absent)
  :trans (and
    (=> (= r1' r2' absent)
        (= g1' g2' absent))
    (=> (and (!= r1' absent) (= r2' absent))
        (and (= g1' r1) (= g2' absent)))
    (=> (and (= r1' absent) (!= r2' absent))
        (and (= g1' absent) (= g2' r2')))
    (=> (and (!= r1' absent) (!= r2' absent))
        (or (and (= g1' r1') (= g2' absent))
          (and (= g1' absent) (= g2' r2'))))
  )
)
"#;

// description.md lines 869-924.
const DOUBLE_DELAY: &str = r#";----------------
; Two-step delay
;----------------

;     +------------------------------------+
;     |   DoubleDelay                      |
;     |  +-----------+      +-----------+  |
;  in |  |           | temp |           |  | out
; ----+->|   Delay   |----->|   Delay   |--+---->
;     |  |           |      |           |  |
;     |  +-----------+      +-----------+  |
;     +------------------------------------+

; One-step delay
(define-system Delay :input ( (i Int) ) :output ( (o Int) )
  :local ( (s Int) )
  :inv (= s i) 
  :init (= o 0)
  :trans (= o' s)
)

; Two-step delay
(define-system DoubleDelay :input ( (in Int) ) :output ( (out Int) )
  :local ( (temp Int) )
  :subsys  (D1 (Delay in temp))
  :subsys  (D2 (Delay temp out))
)

;; DoubleDelay expanded
(define-system DoubleDelay
  :input ( (in Int) )
  :output ( (out Int) )
  :local ( 
    (temp Int)  
    (s1 Int)      ; from `(Delay in temp)`
    (s2 Int)      ; from `(Delay temp out)`
  )
  :inv (and
    (= s1 in)     ; from `(Delay in temp)`
    (= s2 temp)   ; from `(Delay temp out)`
  )
  :init (and
    (= temp 0)   ; from `(Delay in temp)`
    (= out 0)    ; from  `(Delay temp out)`
  )
  :trans (and
    (= temp' s1) ; from `(Delay in temp)`
    (= out' s2)  ; from `(Delay temp out)`
  )
)
; Example trace:
;   in = 1, 2, 3, 4, 5, 6, 7, ...
;   s1 = 1, 2, 3, 4, 5, 6, 7, ...
; temp = 0, 1, 2, 3, 4, 5, 6, ...
;   s2 = 0, 1, 2, 3, 4, 5, 6, ...
;  out = 0, 0, 1, 2, 3, 4, 5, ...
"#;

// description.md lines 941-951.
const LATCH: &str = r#"(define-system Latch  :input ( (set Bool) (reset Bool) )  :output ( (out Bool)) 
 :local ( (s Bool) (b Bool) )
 :init (and
   (= out b)
 )
 :trans (and
   (= out' s)
   (= s' (or (and set (or (not reset) b)) 
             (and (not set) (not reset) out)))
 )
)
"#;

// description.md lines 962-988.
const ONE_BIT_COUNTER: &str = r#";        +--------------------------------------------------------------+
;        |                                                              |
;        |   +--------------------------------------------------------+ |
;        |   |                                              +-------+ | |
;        | +-|-----------------------------------|``-.  set |       | | |
;        | | |                          |`-._    |    :---->|       | | |
;        | | +--|``-.                +--|   _]o--|..-`      | Latch | | |
;        | |    |    :--+----\``-.   |  |.-`          reset |       |-+----> out
;   inc ---+----|..-`   |     )   :--+--------------------->|       |   |
;        |              | +--/..-`                          +-------+   |
;        |              | |                                             |
; start ------------------+                OneBitCounter                |
;        |              |                                               |
;        +--------------|-----------------------------------------------+
;                       |    
;                       v carry

(define-system OneBitCounter :input ( (inc Bool) (start Bool) ) 
 :output ( (out Bool) (carry Bool) )
 :local ( (set Bool) (reset Bool) )
 :subsys (L (Latch set reset out))
 :inv (and 
   (= set (and inc (not reset)))
   (= reset (or carry start))
   (= carry (and inc out))
 )
)
"#;

// description.md lines 997-1018.
const THREE_BIT_COUNTER: &str = r#";        +---------------------------------------------------------+
;        |                                                         |
;        |           +-----------------------------------------------> out0
;        |           |                +------------------------------> out1
;        |           |                |                +-------------> out2
;        |           |                |                |           |   
;        |      +---------+      +---------+      +---------+      |    
;        |      |         | car0 |         | car1 |         | car2 |
;   inc ------->| OneBit  |----->| OneBit  |----->| OneBit  |----> |
;        |      | Counter |      | Counter |      | Counter |      |
; start ----+-->|         |  +-->|         |  +-->|         |      |
;        |  |   +---------+  |   +---------+  |   +---------+      |
;        |  +----------------+----------------+                    |
;        +---------------------------------------------------------+
;
(define-system ThreeBitCounter  :input ( (inc Bool) (start Bool) )
 :output ( (out0 Bool) (out1 Bool) (out2 Bool) ) 
 :local ( (car0 Bool) (car1 Bool) (car2 Bool) ) 
 :subsys (C1 (OneBitCounter inc start out0 car0))
 :subsys (C2 (OneBitCounter car0 start out1 car1)) 
 :subsys (C3 (OneBitCounter car1 start out2 car2))
)
"#;

// description.md lines 1280-1291.
const CHECK_NON_DET_ARBITER: &str = r#"(check-system NonDetArbiter
 :input ( (req1 Bool) (req2 Bool) )
 :output ( (gr1 Bool) (gr2 Bool) )
 ; There are never concurrent requests
 :assumption (a1 (not (and req1 req2)))
 ; The same request is never issued twice in a row
 :assumption (a2 (and (=> req1 (not req1')) (=> req2 (not req2'))))
 ; Neg of: every request is immediately granted
 :reachable (r (not (and (=> req1 gr1) (=> req2 gr2))))
 ; check the reachability of r under assumptions a1 and a2
 :query (q (a1 a2 r)) 
)
"#;

// description.md lines 1297-1339.
const TEMPORAL_QUERIES: &str = r#"(define-system Historically :input ((b Bool)) :output ((hb Bool)) 
 :init (= hb b) 
 :trans (= hb’ (and b’ hb))
)

(define-system Before :input ((b Bool)) :output ((bb Bool)) 
 :init (= bb' false) 
 :trans (= bb’ b)
)

(define-system Count :input ((b Bool)) :output ((c Int)) 
 :init (= c (ite b 1 0))
 :trans (= c’ (+ c (ite b 0 1)))
)

(define-system Monitor :input ((r1 Bool) (r2 Bool)) :output ((g1 Bool) (g2 Bool))  
 :local ((a1 Bool) (a2 Bool) (b Bool) (h1 Bool) (h2 Bool) (bf Bool) (c1 Int))
 :subsys (A (NonDetArbiter r1 r2 g1 g2))
 :subsys (H1 (Historically a1 h1))
 :subsys (H2 (Historically a2 h2))
 :subsys (C (Count g1 c1))
 :subsys (B (Before b bf))
 :inv (and
   ; a1 <=> no requests
   (= a1 (and (not r1) (not r2)))
   ; a2 <=> no grants
   (= a2 (and (not g1) (not g2)))
   ; b <=> c1 is 4
   (= b (= c1 4))
 )
)

(check-system Monitor :input ((r1 Bool) (r2 Bool)) :output ((g1 Bool) (g2 Bool))
 :local ((a1 Bool) (a2 Bool) (b Bool) (h1 Bool) (h2 Bool) (bf Bool) (c1 Int))
 ; no concurrent requests
 :assumption (A (not (and r1 r2))) 
 ; neg of: if there have been no requests, there have been no grants 
 :reachable (P1 (not (=> h1 h2))) 
 ; neg of: a request is granted at most 4 times
 :reachable (P2 (not (=> bf (not g1)))) 
 :query (Q1 (A P1))
 :query (Q2 (A P2))
)
"#;

// description.md lines 1378-1392.
const VERBOSE_RESPONSE: &str = r#"(check-system-response
 :verbosity full
 :query (q1 :result sat :model m :trace t)
 :query (q2 :result unsat :certificate c)
 :query (q3 :result unknown)                         ; for timeouts and other cases
 :trace (t :prefix p :lasso l)                       ; t = pl^ω
 :model (m M)                                        ; M is model in SMT-LIB format
 :trail (p ( (0 (i i₀) (o o₀) (s s₀) (r r₀) (f f₀))  ; numbered state/valuation
              ...
             (j (i iⱼ) (o oⱼ) (s sⱼ) (r rⱼ) (f fⱼ))
           )
        ) 
 :trail (l ( (... ) ... ( ...) ))
 :certificate (c :inv F :k n)
)
"#;

// description.md lines 1405-1408.
const COMPACT_RESPONSE: &str = r#"(check-system-response
 :verbosity compact
 ...
)
"#;

// "Supported SMT-LIB Commands", declare-sort: read as written.
#[test]
fn supported_commands_declare_sort() {
    let script = read(DECLARE_SORT);
    assert!(matches!(&script.commands()[1], Command::DeclareSort(s, n) if s.as_str() == "Set" && n.as_str() == "1"));
}

// "Supported SMT-LIB Commands", define-sort: the examples are written with
// declare-sort, whose second argument is a numeral (SMT-LIB §3.9.3), so
// the first is a syntax error (at the command, where smtlib reports
// the wrong number of arguments). With define-sort, as
// the bullet above them says, they are read.
#[test]
fn supported_commands_define_sort() {
    rejected(DEFINE_SORT, ErrorKind::Syntax, line_column(DEFINE_SORT, "(declare-sort NestedSet"));
    let script = read(&DEFINE_SORT.replace("declare-sort", "define-sort"));
    assert!(matches!(&script.commands()[1], Command::DefineSort(c) if c.name().as_str() == "Array2" && c.parameters().len() == 2));
}

// "Supported SMT-LIB Commands", declare-const: read as written.
#[test]
fn supported_commands_declare_const() {
    assert_eq!(read(DECLARE_CONST).commands().len(), 2);
}

// "Supported SMT-LIB Commands", define-fun: the examples are written with
// declare-fun, which MoXI does not adopt: unsupported, at the command
// name. With define-fun, as the bullet above them says, they are read.
#[test]
fn supported_commands_define_fun() {
    let error = rejected(DEFINE_FUN, ErrorKind::Unsupported, line_column(DEFINE_FUN, "declare-fun"));
    assert!(error.message().contains("declare-fun"), "{error}");
    let script = read(&DEFINE_FUN.replace("declare-fun", "define-fun"));
    assert!(script.commands().iter().all(|c| c.name() == "define-fun"));
}

// "Supported SMT-LIB Commands", set-logic: read as written.
#[test]
fn supported_commands_set_logic() {
    assert!(matches!(&read(SET_LOGIC).commands()[0], Command::SetLogic(l) if l.as_str() == "QF_BV"));
}

// "Examples — atomic systems", Delay and its variant: read. Both in one
// script are read too: that the second redefines Delay is static
// semantics.
#[test]
fn atomic_delay() {
    let delay = read(DELAY);
    let delay = system(&delay, 0);
    assert!(delay.is_atomic());
    assert_eq!(delay.input().map(<[_]>::len), Some(1));
    assert!(delay.local().is_none());
    assert_eq!(delay.trans().unwrap().to_text(&moxi::dialect()), "(= o' i)");
    read(DELAY_RANGE);
    assert_eq!(read(&format!("{DELAY}{DELAY_RANGE}")).commands().len(), 2);
}

// "Examples — atomic systems", StutteringClockedCopy: the example writes
// the next-state variables with the typographic apostrophe ’ (U+2019),
// which is not a character of the SMT-LIB lexicon: a lexical error at its
// first occurrence. With ’ written as the prime ' it is read.
#[test]
fn atomic_stuttering_clocked_copy() {
    rejected(STUTTERING_CLOCKED_COPY, ErrorKind::Lexical, line_column(STUTTERING_CLOCKED_COPY, "’"));
    read(&STUTTERING_CLOCKED_COPY.replace('’', "'"));
}

// "Examples — atomic systems", Event and LossyIntChannel: declare-datatype
// is not among the commands MoXI adopts (unsupported). The systems that
// use the sort (Event Int) are read: whether Event is declared is static
// semantics.
#[test]
fn atomic_events() {
    rejected(EVENT, ErrorKind::Unsupported, line_column(EVENT, "declare-datatype"));
    read(LOSSY_INT_CHANNEL);
    let local = read(LOSSY_INT_CHANNEL_LOCAL);
    assert_eq!(system(&local, 0).local().map(<[_]>::len), Some(1));
    read(INT_NON_DET_ARBITER);
}

// "Examples — atomic systems", TimedSwitch1, TimedSwitch2, TimedSwitch3:
// read, one after the other. TimedSwitch1 writes :inv before :init, which
// the printer moves after :trans (the order of formulas is immaterial).
#[test]
fn atomic_timed_switches() {
    let script = read(&format!("{TIMED_SWITCH1}{TIMED_SWITCH2}{TIMED_SWITCH3}"));
    assert!(matches!(&script.commands()[0], Command::DeclareEnumSort(s, values) if s.as_str() == "LightStatus" && values.len() == 2));
    for index in [1, 2, 4] {
        let switch = system(&script, index);
        assert_eq!(switch.local().map(<[_]>::len), Some(2));
        assert!(switch.init().is_some() && switch.trans().is_some() && switch.inv().is_some());
    }
    let printed = script.commands()[1].to_string();
    assert!(printed.find(":trans").unwrap() < printed.find(":inv").unwrap(), "{printed}");
}

// "Examples — atomic systems", NonDetArbiter and DelayedArbiter: read;
// DelayedArbiter uses the document's != , an ordinary symbol to the reader.
#[test]
fn atomic_arbiters() {
    read(&format!("{NON_DET_ARBITER}{DELAYED_ARBITER}"));
}

// "Examples — composite systems", DoubleDelay: the whole block is read,
// including the third definition "DoubleDelay expanded" under the same
// identifier (a redefinition, which is static semantics). The composite
// system has the two subsystems in order.
#[test]
fn composite_double_delay() {
    let script = read(DOUBLE_DELAY);
    assert_eq!(script.commands().len(), 3);
    let double = system(&script, 1);
    assert!(!double.is_atomic());
    let instances: Vec<String> = double.subsystems().iter().map(|s| format!("{} {} {:?}", s.name(), s.system(), s.arguments().iter().map(|a| a.as_str()).collect::<Vec<_>>())).collect();
    assert_eq!(instances, ["D1 Delay [\"in\", \"temp\"]", "D2 Delay [\"temp\", \"out\"]"]);
}

// "Examples — composite systems", Latch, OneBitCounter, ThreeBitCounter.
// As written, Latch is rejected: `reset` is a command name and therefore a
// reserved word, not a symbol (SMT-LIB §3.1: "each command name in Section
// 3.9 is also a reserved word"). With `reset` renamed `rst` the three
// systems are read. Latch's `(and (= out b))` applies `and` to one
// argument, which Core's `:left-assoc` forbids (SMT-LIB §3.7); that is
// static semantics, so the reader reads it.
#[test]
fn composite_three_bit_counter() {
    let text = format!("{LATCH}{ONE_BIT_COUNTER}{THREE_BIT_COUNTER}");
    let error = rejected(&text, ErrorKind::Syntax, line_column(&text, "reset"));
    assert!(error.message().contains("reset"), "{error}");
    let script = read(&text.replace("reset", "rst"));
    assert_eq!(system(&script, 2).subsystems().len(), 3);
}

// "Check-system Examples", [Non-deterministic arbiter.]: read. The command
// renames the inputs and outputs and omits :local.
#[test]
fn check_system_non_det_arbiter() {
    let script = read(CHECK_NON_DET_ARBITER);
    let Command::CheckSystem(check) = &script.commands()[0] else { panic!() };
    assert!(check.input().is_some() && check.output().is_some() && check.local().is_none());
    assert_eq!(check.conditions().map(|c| c.label().as_str()).collect::<Vec<_>>(), ["a1", "a2", "r"]);
    assert_eq!(check.queries().map(|q| q.formulas().len()).collect::<Vec<_>>(), [3]);
}

// "Check-system Examples", [Temporal queries.]: as written, the ’ of
// Historically is a lexical error. With ’ written as ', the whole example
// is read. (Before's `:init (= bb' false)` primes a variable in an initial
// condition, "a one-state formula" ("Atomic Systems"); that is static
// semantics.)
#[test]
fn check_system_temporal_queries() {
    rejected(TEMPORAL_QUERIES, ErrorKind::Lexical, line_column(TEMPORAL_QUERIES, "’"));
    let script = read(&TEMPORAL_QUERIES.replace('’', "'"));
    let Command::CheckSystem(check) = &script.commands()[4] else { panic!() };
    assert_eq!(check.local().map(<[_]>::len), Some(7));
    assert!(matches!(&check.attributes()[3], CheckAttribute::Query(q) if q.name().as_str() == "Q1"));
}

// "Verbose Response": the example has placeholders (… and the subscripted
// names i₀, iⱼ), which are not SMT-LIB tokens: a lexical error at the first
// subscript. An instance of its shape is read, prints and reads back.
#[test]
fn verbose_response() {
    let error = CheckSystemResponse::from_str(VERBOSE_RESPONSE).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Lexical, "{error}");
    let (line, column) = line_column(VERBOSE_RESPONSE, "₀");
    assert_eq!((error.position().unwrap().line(), error.position().unwrap().column()), (line, column), "{error}");
    let instance = "(check-system-response
 :verbosity full
 :query (q1 :result sat :model m :trace t)
 :query (q2 :result unsat :certificate c)
 :query (q3 :result unknown)
 :trace (t :prefix p :lasso l)
 :model (m ((define-fun k () Int 3)))
 :trail (p ( (0 (i 1) (o 0) (s true) (r false) (f false))
             (1 (i 2) (o 1) (s false) (r true) (f true))
           )
        )
 :trail (l ( (0 (i 2) (o 2) (s false) (r true) (f true)) ))
 :certificate (c :inv (>= o 0) :k 1)
)";
    let response = CheckSystemResponse::from_str(instance).unwrap();
    assert_eq!(CheckSystemResponse::from_str(&response.to_string()).unwrap(), response);
    assert_eq!(response.verbosity(), Verbosity::Full);
    assert_eq!(response.queries().map(|q| q.result()).collect::<Vec<_>>(), [Answer::Sat, Answer::Unsat, Answer::Unknown]);
    let ResponseItem::Trail(p) = &response.items()[5] else { panic!() };
    assert_eq!(p.states().len(), 2);
    assert_eq!(p.states()[1].assignments().len(), 5);
}

// "Compact Response": the example elides everything after :verbosity with
// "...", which is a symbol where an attribute (a keyword) is expected. The
// compact instance of the verbose example is read.
#[test]
fn compact_response() {
    let error = CheckSystemResponse::from_str(COMPACT_RESPONSE).unwrap_err();
    assert_eq!((error.kind(), error.position().unwrap().line(), error.position().unwrap().column()), (ErrorKind::Syntax, 3, 2), "{error}");
    let instance = "(check-system-response :verbosity compact
 :query (q1 :result sat :trace t) :trace (t :prefix p :lasso l)
 :trail (p ((0 (i 1) (o 0)) (1 (o 1)))) :trail (l ((0 (i 1) (o 1)))))";
    let response = CheckSystemResponse::from_str(instance).unwrap();
    assert_eq!(response.verbosity(), Verbosity::Compact);
    assert_eq!(CheckSystemResponse::from_str(&response.to_string()).unwrap(), response);
}
