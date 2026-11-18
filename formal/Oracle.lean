import Trion.Expansion

/-!
The oracle of the expansion: for each shape on a line of its standard input it prints what
`Trion.expand` gives. A shape is written `subjects counted whole|objects measured;…`, with
`0` and `1` for no and yes; an answer is `ok` with the parts as `phrase.subject.object`, or
`refused` with the rule.
-/

open Trion

def flag (text : String) : Option Bool :=
  match text with
  | "0" => some false
  | "1" => some true
  | _ => none

def phrase (text : String) : Option Phrase :=
  match text.splitOn " " with
  | [objects, measured] => do
    let objects ← objects.toNat?
    let measured ← flag measured
    pure ⟨objects, measured⟩
  | _ => none

def shape (line : String) : Option Shape :=
  match line.splitOn "|" with
  | [head, phrases] =>
    match head.splitOn " " with
    | [subjects, counted, whole] => do
      let subjects ← subjects.toNat?
      let counted ← flag counted
      let whole ← flag whole
      let phrases ← (phrases.splitOn ";").mapM phrase
      pure ⟨subjects, counted, phrases, whole⟩
    | _ => none
  | _ => none

def answer (shape : Shape) : String :=
  match expand shape with
  | .ok parts => "ok " ++ " ".intercalate (parts.map fun (p, s, o) => s!"{p}.{s}.{o}")
  | .error .counted => "refused counted"
  | .error .measure => "refused measure"
  | .error .whole => "refused whole"

partial def serve (input : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then
    return
  match shape line.trimAscii.toString with
  | some shape => IO.println (answer shape)
  | none => IO.println "unreadable"
  serve input

def main : IO Unit := do
  serve (← IO.getStdin)
