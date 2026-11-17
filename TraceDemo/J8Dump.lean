import Nock.V1J8.Example
import Nock.V1J8.GenJ8
import Nock.V1J8.CheckJ8
import Nock.V1J8.GenJet
import Nock.Jet.AutogenMatmul
import Nock.V1J8.GenAtom
import Nock.V1J8.GenAtomBig

/-! Executable that generates a J-8 instance (the honest example, a jet call, or an equality test on large atoms), checks it natively with `checkJ8`, and prints it as Lean definitions. -/

open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check

def pN : Noun → String
  | .atom a => s!"(.atom {a})"
  | .cell a b => s!"(.cell {pN a} {pN b})"
def pG (g : Gold) : String := s!"{g.val.toNat}"
def pK3 (k : K3) : String := s!"(K {pG k.c0} {pG k.c1} {pG k.c2})"
def pK6 (k : K6) : String := s!"⟨{pK3 k.re}, {pK3 k.im}⟩"
def pLst (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def pChip (nm : String) (q : ChipIn) : String :=
  let maxc := 400
  let colsL := (List.range maxc).map fun c => (List.range q.n).map fun i =>
    if h : i < q.n then (q.cols c ⟨i, h⟩).val else 0
  -- trim trailing all-zero columns
  let nc := (colsL.reverse.dropWhile (fun l => l.all (· == 0))).length
  let colsT := (colsL.take nc).map (fun l => pLst (l.map toString))
  s!"def {nm} : ChipIn := mkChip {q.h} {q.n} {pG q.ω} {pLst colsT}\n"
def pRows (r : RowsJ8) : String :=
  s!"⟨{r.N}, {r.D}, {r.W}, {r.Λ}, {r.A}, {r.AW}, {r.J}, {r.mb}, {r.inc}, {r.calls}, {r.heads}, {r.blocks}, {r.rd}, {r.leaves}, {r.maxlen}⟩"

def dumpI (I : InJ8) : IO Unit := do
  let M := I.M
  IO.println s!"-- frameJ8.n = {frameJ8.n}; J.n = {I.J.n}; kroots {I.kroots} krootsV {I.krootsV} g {I.g}"
  IO.println s!"def Ic : P8PublicClaim := ⟨{pN I.c.subject}, {pN I.c.formula}, {pN I.c.result}⟩"
  IO.println s!"def Imm : List (ℕ × ℕ × ℕ) := {repr ((List.finRange 3).map M.m)}"
  IO.println s!"def Irho : List K6 := {pLst ((List.finRange 5).map fun i => pK6 (M.ρ i))}"
  IO.println s!"def IrhoS : K6 := {pK6 M.ρS}"
  for (nm, f) in [("pC", M.pubsC), ("pW", M.pubsW), ("pJ", M.pubsJ), ("pA", M.pubsA), ("pV", M.pubsV)] do
    IO.println s!"def I{nm} : List K3 := {pLst ((List.range 64).map fun i => pK3 (f i))}"
  IO.println s!"def Ichi : List K3 := {pLst ((List.finRange frameJ8.n).map fun i => pK3 (I.χ i))}"
  IO.println s!"def Ir : RowsJ8 := {pRows I.r}"
  IO.print (pChip "IX" I.X); IO.print (pChip "IC" I.C); IO.print (pChip "IW" I.W)
  IO.print (pChip "IA" I.A); IO.print (pChip "IV" I.V)
  IO.println s!"def IJ : ChipIn := mkChip {I.J.h} {I.J.n} {pG I.J.ω} {pLst ((List.range 200).map fun c => pLst ((List.range I.J.n).map fun i => if h : i < I.J.n then toString (I.J.cols c ⟨i, h⟩).val else "0"))}"
  IO.println s!"def Ilay : List Nock.Jet.ChipJ8.PRow := {pLst ((List.finRange I.J.n).map fun i => reprStr (I.lay i))}"
  IO.println s!"def Iregs : List ℕ := {repr I.regs}"
  IO.println s!"def Iids : List ℕ := {repr I.ids}"
  IO.println s!"def Iidx : List ℕ := {repr ((List.range 16).map I.idx)}"
  IO.println s!"def Irk : List (ℕ × ℕ) := {repr ((List.range 16).map I.rk)}"
  IO.println s!"-- kroots {I.kroots} krootsV {I.krootsV} g {I.g} r {I.g}"

open Nock.Jet.Autogen in
def tinyT : Tpl where
  k := 2
  ax := ![12, 13]
  inTy := fun _ => .F
  outTy := .F
  body := .add (.var 0) (.var 1)

def tinyS : Noun := .cell (.atom 0) (.cell (.cell (.atom 5) (.atom 7)) (.atom 0))

def tinyProg : Noun := Nock.Jet.wildCall 7 (Nock.Jet.Autogen.compile Nock.Field.p tinyT)

def main (args : List String) : IO Unit := do
  if args.head? == some "jet" then
    match Nock.V1J8.Gen.genJ8J (fun _ => tinyT) [7] 2 tinyS tinyProg (Nock.V1J8.Gen.prngCoins 1) with
    | none => IO.println "-- genJ8J none"
    | some I =>
      IO.eprintln s!"native checkJ8: {checkJ8 I}"
      dumpI I
  else if args.head? == some "eq5" || args.head? == some "ne5" then
    -- *[p-1 [5 [4 [4 [0 1]]] [4 [4 [0 1]]]]]: op 5 on equal big atoms (atom walk present), genJ8A, coins prngCoins 1
    let inc1 : Nock.Noun := .cell (.atom 4) (.cell (.atom 0) (.atom 1))
    let inc2 : Nock.Noun := .cell (.atom 4) inc1
    let prog : Nock.Noun := if args.head? == some "ne5" then .cell (.atom 5) (.cell inc1 inc2) else .cell (.atom 5) (.cell inc2 inc2)
    match Nock.V1J8.Gen.genJ8A (fun _ => none) 1000 (.atom (Nock.Field.p - 1)) prog
        (Nock.V1J8.Gen.prngCoins 1) with
    | none => IO.println "-- genJ8A none"
    | some I =>
      IO.eprintln s!"native checkJ8: {checkJ8 I}"
      dumpI I
  else dumpI (Example.honest Example.χ0e)
