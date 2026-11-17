/-

      nockvm-d5red seq        -- 4b: the sequentiality exhibit (known-first / interactive / FS)
      nockvm-d5red tamper     -- 4a: tamper tables on J and atom records, at FS coins
      nockvm-d5red ablate ... -- 5: the ablation suite (scratch checker with source-gate families switched off)

  Everything here is a native, empirical run of the checker (`checkJ8`, `checkJ8_iff`: it IS the verifier under the
  registry premise) or of a SCRATCH variant of it (a chip's source-gate list with some indices removed: the proved
  modules are not edited).  Nothing in this file is kernel-checked unless said so.
-/
import Nock.V1J8.GenJ8
import Nock.TraceGenExe.Syntax
import Nock.TraceGenExe.Demos
import Nock.V1J8.GenJet
import Nock.Edit.GenXDemo
import Nock.V1J8.GenAtom
import Nock.V1J8.GenAtomBig
import Nock.V1J8.FastCheck
import Nock.V1J8.D5Sizes
import Nock.DriverJ8.DriverJ8

namespace Nock.V1J8.D5Abl

open Nock.TraceGenExe Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Example Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.MonolithicRAP (ChipTemplate)

private abbrev Q : ℕ := Nock.Field.p

def pad (s : String) (n : ℕ) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

def getColA (q : ChipIn) (c i : ℕ) : ZMod Q := if h : i < q.n then q.cols c ⟨i, h⟩ else 0

def layGetA (I : InJ8) (j : ℕ) : Nock.Jet.ChipJ8.PRow :=
  if h : j < I.J.n then I.lay ⟨j, h⟩ else ⟨.nil, 0, 0, 0, 0, 0⟩

open Nock.V1J8.MemX in
def srcMOff (Tm : ChipTemplate (ZMod Q)) (skip : List ℕ) : List SGM :=
  ((srcM Tm).zipIdx.filter fun x => !skip.contains x.2).map (·.1)

open Nock.V1J8.MemX in
def prepOK {n : ℕ} (T : TabM n) : Bool :=
  T.prep.all (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

open Nock.V1J8.MemX Nock.V1J8.FastEval in
/-- `checkMG` (the Gold-register evaluator of `FastEval`) over the source gates not in `skip`. -/
def checkMOff (Tm : ChipTemplate (ZMod Q)) (skip : List ℕ) {n : ℕ} (T : TabM n) : Bool :=
  let src := (srcMOff Tm skip).map SGF.comp
  let mm := 3 * (src.foldl (fun m g => max m g.mx) 0) + Tm.baseCols + 3
  let w := Tm.width 3
  let A := goldCols T.cols w
  let nxG := (Nock.V1J8.FastLag.nextArr T.nodes T.ω T.cols w).map Gold.ofZ
  let cG := GC.mk' (slotE Tm.baseCols T.chals) mm
  let pG := GC.mk' (slotE Tm.baseCols T.pubs) mm
  (List.finRange n).all (fun i => src.all (srcOKM Tm.baseCols (rowEnvM w A nxG cG pG i))) && prepOK T

open Nock.V1J8.MemX Nock.V1J8.FastEval in
/-- Gates violated at the given rows only (the honest rows hold every gate); Gold-register evaluator. -/
def violMRows (Tm : ChipTemplate (ZMod Q)) {n : ℕ} (T : TabM n) (rows : List ℕ) : List ℕ :=
  let src := (srcM Tm).map SGF.comp
  let mm := 3 * (src.foldl (fun m g => max m g.mx) 0) + Tm.baseCols + 3
  let w := Tm.width 3
  let A := goldCols T.cols w
  let nxG := (Nock.V1J8.FastLag.nextArr T.nodes T.ω T.cols w).map Gold.ofZ
  let cG := GC.mk' (slotE Tm.baseCols T.chals) mm
  let pG := GC.mk' (slotE Tm.baseCols T.pubs) mm
  let envs := rows.filterMap fun r => if h : r < n then some (rowEnvM w A nxG cG pG ⟨r, h⟩) else none
  (src.zipIdx.filterMap fun (g, j) => if envs.all (fun e => srcOKM Tm.baseCols e g) then none else some j)

open Nock.V1J8.CompX Nock.V1J8.FastEval in
def checkXOff (skip : List ℕ) {n : ℕ} (T : TabX n) : Bool :=
  let src := (srcXG.zipIdx.filter fun x => !skip.contains x.2).map (·.1)
  let A := goldCols T.cols 123
  let nxG := (Nock.V1J8.FastLag.nextArr T.nodes T.ω T.cols 123).map Gold.ofZ
  let cG := GC.mk' T.chal srcXM
  let pG := GC.mk' T.pub srcXM
  (List.finRange n).all (fun i => src.all (srcOKX (rowEnvX A nxG cG pG i))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod Q))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

open Nock.V1J8.CompX Nock.V1J8.FastEval in
def violXRows {n : ℕ} (T : TabX n) (rows : List ℕ) : List ℕ :=
  let A := goldCols T.cols 123
  let nxG := (Nock.V1J8.FastLag.nextArr T.nodes T.ω T.cols 123).map Gold.ofZ
  let cG := GC.mk' T.chal srcXM
  let pG := GC.mk' T.pub srcXM
  let envs := rows.filterMap fun r => if h : r < n then some (rowEnvX A nxG cG pG ⟨r, h⟩) else none
  (srcXG.zipIdx.filterMap fun (g, j) => if envs.all (fun e => srcOKX e g) then none else some j)

/-- A gate family: name, chip (`X C W J A V`), part (0 base, 1 mixed, 2 slot pairs [compute only]), offset in the
part, number of source gates. -/
structure Fam where
  name : String
  chip : Char
  part : ℕ
  off : ℕ
  len : ℕ
  deriving Inhabited

def seqFams (chip : Char) (part : ℕ) (start : ℕ) (xs : List (String × ℕ)) : List Fam :=
  (xs.foldl (fun (acc : ℕ × List Fam) x => (acc.1 + x.2, acc.2 ++ [⟨x.1, chip, part, acc.1, x.2⟩])) (start, [])).2

def famIdx (Tm : ChipTemplate (ZMod Q)) (f : Fam) : List ℕ :=
  if f.part = 0 then (List.range' f.off f.len).filter (· < Tm.baseTransition.length)
  else (List.range' f.off f.len).filter (· < Tm.mixedTransition.length) |>.map
    (· + Tm.baseTransition.length + Tm.extTransition.length)

def famIdxX (f : Fam) : List ℕ :=
  let nb := (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.baseGatesFX (F := ZMod Q)).length
  if f.part = 0 then List.range' f.off f.len
  else if f.part = 1 then (List.range' f.off f.len).map (· + nb)
  else (List.range' f.off f.len).map (· + nb + 8)

def qLens (qs : List (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.QE (ZMod Q))) : List ℕ :=
  qs.map fun q => (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.QE.gates q).length

/-! ## The family tables of the J-8 chips -/

section Fams
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- **The J chip** (`jetTemplateJ8T`): 4 base gates, 5 slot-inverse gates, 6 accumulator gates (2 coordinates each). -/
def famsJ : List Fam :=
  let qs := Nock.Jet.ChipJ8.slotGatesT (F := ZMod Q) deltaF ++ Nock.Jet.ChipJ8.accGates (F := ZMod Q)
  let names := ["j.slot0", "j.slot1", "j.slot2", "j.slot3", "j.slotX", "j.accT.init", "j.accT.step", "j.accT.term",
    "j.accX.init", "j.accX.step", "j.accX.term"]
  seqFams 'J' 0 0 [("j.const", 1), ("j.add", 1), ("j.mul", 1), ("j.kN", 1)] ++
  seqFams 'J' 1 0 (names.zip (qLens qs))

/-- **The atom table** (`atomTemplateHQL`): g1 .. g8, `isL·c_out`, g5 / g7.5 on the `𝕂′` side. -/
def famsA : List Fam :=
  let tm := (AtomChipHQL.atomTemplateHQL (deltaF : ZMod Q))
  let nb0 := tm.baseTransition.length - (AtomChipHQL.atomGatesL (F := ZMod Q)).length
  let nm0 := tm.mixedTransition.length - (AtomChipHQ.atomMixed (F := ZMod Q) deltaF).length
  let qn := ["a.g5.inv", "a.g5.init", "a.g5.step", "a.g5.term", "a.g7.5c.inv", "a.g7.5c.init", "a.g7.5c.step",
    "a.g7.5c.term", "a.g7.5.inv", "a.g7.5.init", "a.g7.5.step", "a.g7.5.term"]
  [⟨"a.cellBlock(base)", 'A', 0, 0, nb0⟩, ⟨"a.cellBlock(mixed)", 'A', 1, 0, nm0⟩] ++
  seqFams 'A' 0 nb0 [("a.g1", (AtomChipHQ.g1 (F := ZMod Q)).length), ("a.g2", 1), ("a.g3", 1),
    ("a.g4.mb", 2), ("a.g4.mi", 2), ("a.g7.0", (AtomChipHQ.g70 (F := ZMod Q)).length),
    ("a.g7.1", (AtomChipHQ.g71 (F := ZMod Q)).length), ("a.g7.2", (AtomChipHQ.g72 (F := ZMod Q)).length),
    ("a.g7.3", (AtomChipHQ.g73 (F := ZMod Q)).length), ("a.g7.4", (AtomChipHQ.g74 (F := ZMod Q)).length),
    ("a.g8", (AtomChipHQ.g8 (F := ZMod Q)).length), ("a.isL.cout", 1)] ++
  seqFams 'A' 1 nm0 (qn.zip (qLens (AtomChipHQ.atomQ (F := ZMod Q) deltaF)))

/-- **The cell table** (`cellTemplateHQKW`): the J-8 additions (kind bits, wire-key export). -/
def famsC : List Fam :=
  let tm := CellTwinKW.cellTemplateHQKW (deltaF : ZMod Q)
  let kg := (CellTwinK.kindGates (F := ZMod Q)).length
  let nb0 := tm.baseTransition.length - kg
  let gq := CellTwinKW.gatesQ (F := ZMod Q) deltaF
  let nm0 := tm.mixedTransition.length - (CellTwinKW.gates (F := ZMod Q) deltaF).length
  [⟨"c.40th(base)", 'C', 0, 0, nb0⟩, ⟨"c.40th(mixed)", 'C', 1, 0, nm0⟩] ++
  seqFams 'C' 0 nb0 (["L", "R"].flatMap fun sd =>
    [("c.kb" ++ sd ++ ".bool", 1), ("c.kb" ++ sd ++ ".lo", 1), ("c.kb" ++ sd ++ ".hi", 1), ("c.kb" ++ sd ++ ".w(1-kb)inv", 1),
     ("c.kb" ++ sd ++ ".kb(1-w)", 1)]) ++
  seqFams 'C' 1 nm0 (["c.kw.provInv", "c.kw.accInit", "c.kw.accStep", "c.kw.accTerm"].zip (qLens gq))

/-- **A walk chip** (`walkTemplateJ8` / `walkTemplateHQK`): base gates by name, walk gates, `𝕂′` gates. -/
def famsWalk (chip : Char) (jEight : Bool) : List Fam :=
  let tm := if jEight then WalkJ8.walkTemplateJ8 (deltaF : ZMod Q) 1 else CellTwinK.walkTemplateHQK (deltaF : ZMod Q) 1
  let nb := tm.baseTransition.length
  let nm := tm.mixedTransition.length
  let wq := (qLens (WChip.qEqs (F := ZMod Q) deltaF))
  let hq := nm - 7 - (wq.foldl (· + ·) 0)
  let certLen := nb - 4 - 13 - 2
  seqFams chip 0 0 [("w.cLR.e.u", 4), ("w.depthcert", certLen), ("w.root.q", 7), ("w.bits", 6), ("w.kindTern", 2)] ++
  seqFams chip 1 0 ([("w.ln.init", 1), ("w.ln.step", 1), ("w.cnt.init", 1), ("w.cnt.step", 1), ("w.acc.init", 1),
      ("w.acc.step", 1), ("w.acc.term", 1)] ++
    (["w.rootfp", "w.xinv", "w.pinvL", "w.pinvR", "w.xAcc.init", "w.xAcc.step", "w.xAcc.term", "w.pAcc.init",
      "w.pAcc.step", "w.pAcc.term"].zip ([(wq.take 3).foldl (· + ·) 0] ++ wq.drop 3)) ++ [("w.hqExtra", hq)])

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX in
/-- The compute chip (`srcX`: base gates = arithmetic ++ accumulators ++ equality tests; then 4 slot pairs; then the walk
gates).  The arithmetic block is cut by its named groups; kid-kind gates are the last 23. -/
def famsX : List Fam :=
  let ar := List.length (arithGatesX (F := ZMod Q))
  let nb := (baseGatesFX (F := ZMod Q)).length
  let ns := (walkGatesFX (F := ZMod Q)).length
  seqFams 'X' 0 0 [("x.oneHot", List.length (oneHotG (F := ZMod Q))), ("x.kindbits(kb,kc)", List.length (kindG (F := ZMod Q))),
    ("x.sv", List.length (svG (F := ZMod Q))), ("x.op0", List.length (op0G (F := ZMod Q))), ("x.op3", List.length (op3G (F := ZMod Q))),
    ("x.op4(fast,inv4)", List.length (op4G (F := ZMod Q))), ("x.op5(+alpha pair)", List.length (op5G (F := ZMod Q))),
    ("x.op6", List.length (op6G (F := ZMod Q))), ("x.op8", List.length (op8G (F := ZMod Q))), ("x.op9", List.length (op9G (F := ZMod Q))),
    ("x.cons", List.length (consG (F := ZMod Q))), ("x.s10", List.length (s10G (F := ZMod Q))), ("x.s10L", List.length (s10LG (F := ZMod Q))),
    ("x.s11", List.length (s11G (F := ZMod Q))), ("x.kidKind", List.length (kidKindG (F := ZMod Q)))] ++
  seqFams 'X' 0 ar [("x.acc.export", 18), ("x.acc.path", 18), ("x.acc.service", 18)] ++
  seqFams 'X' 0 (ar + 54) [("x.eq.sv", List.length (svEq (F := ZMod Q))), ("x.eq.op0", List.length (op0Eq (F := ZMod Q))),
    ("x.eq.op1", List.length (op1Eq (F := ZMod Q))), ("x.eq.op3", List.length (op3Eq (F := ZMod Q))),
    ("x.eq.op4", List.length (op4Eq (F := ZMod Q))), ("x.eq.op5", List.length (op5Eq (F := ZMod Q))),
    ("x.eq.op6", List.length (op6Eq (F := ZMod Q))), ("x.eq.op78", List.length (op78Eq (F := ZMod Q))),
    ("x.eq.op9", List.length (op9Eq (F := ZMod Q))), ("x.eq.s10", List.length (s10Eq (F := ZMod Q))),
    ("x.eq.s10L", List.length (s10LEq (F := ZMod Q))), ("x.eq.s10T", List.length (s10TEq (F := ZMod Q))),
    ("x.eq.claim", List.length (claimEq (F := ZMod Q)))] ++
  [⟨"x.slot0", 'X', 2, 0, 2⟩, ⟨"x.slot1", 'X', 2, 2, 2⟩, ⟨"x.slot2", 'X', 2, 4, 2⟩, ⟨"x.slot3(service)", 'X', 2, 6, 2⟩,
   ⟨"x.walk", 'X', 1, 0, ns⟩]

end Fams

def census : IO Unit := do
  let show1 := fun (f : Fam) => IO.println s!"  {pad f.name 22} chip {f.chip} part {f.part} off {f.off} len {f.len}"
  IO.println "J chip:"; for f in famsJ do show1 f
  IO.println "atom table:"; for f in famsA do show1 f
  IO.println "cell KW:"; for f in famsC do show1 f
  IO.println "walk J8:"; for f in famsWalk 'W' true do show1 f
  IO.println "atom walk:"; for f in famsWalk 'V' false do show1 f
  IO.println "compute:"; for f in famsX do show1 f

/-! ## The scratch checker at instance level -/

section Scratch
open Nock.V1J8.MemX Nock.NockVMROM.Thm54.VclL.Handle

abbrev Edit := ℕ → ℕ → ZMod Q → ZMod Q   -- column, row, old value ↦ new value

def tmC : ChipTemplate (ZMod Q) := CellTwinKW.cellTemplateHQKW deltaF
def tmJ : ChipTemplate (ZMod Q) := Nock.Jet.ChipJ8.jetTemplateJ8T deltaF
def tmA : ChipTemplate (ZMod Q) := AtomChipHQL.atomTemplateHQL deltaF
def tmA0 : ChipTemplate (ZMod Q) := AtomChipHQ.atomTemplateHQ deltaF
def tmW (kr : ℕ) : ChipTemplate (ZMod Q) := WalkJ8.walkTemplateJ8 deltaF kr
def tmV (kr : ℕ) : ChipTemplate (ZMod Q) := CellTwinK.walkTemplateHQK deltaF kr

def applyCols (q : ChipIn) (ed : Edit) : ChipIn := ⟨q.h, q.n, q.ω, fun c i => ed c i.val (q.cols c i)⟩

def editInst (I : InJ8) (ch : Char) (ed : Edit) : InJ8 :=
  match ch with
  | 'X' => { I with X := applyCols I.X ed }
  | 'C' => { I with C := applyCols I.C ed }
  | 'W' => { I with W := applyCols I.W ed }
  | 'J' => { I with J := applyCols I.J ed, lay := fun i => layGetA I i }
  | 'A' => { I with A := applyCols I.A ed }
  | _ => { I with V := applyCols I.V ed }

def chipN (I : InJ8) : Char → ℕ
  | 'X' => I.X.n | 'C' => I.C.n | 'W' => I.W.n | 'J' => I.J.n | 'A' => I.A.n | _ => I.V.n

def chipW : Char → ℕ
  | 'X' => 123 | 'C' => 242 | 'W' => 166 | 'J' => 71 | 'A' => 349 | _ => 166

def famsOfChip (ch : Char) : List Fam :=
  match ch with
  | 'X' => famsX | 'C' => famsC | 'W' => famsWalk 'W' true | 'J' => famsJ | 'A' => famsA | _ => famsWalk 'V' false

/-- Gate indices a family occupies in a chip's own list. -/
def idxOfFam (I : InJ8) (f : Fam) : List ℕ :=
  match f.chip with
  | 'X' => famIdxX f
  | 'C' => famIdx tmC f
  | 'W' => famIdx (tmW I.kroots) f
  | 'J' => famIdx tmJ f
  | 'A' => famIdx tmA f
  | _ => famIdx (tmV I.krootsV) f

/-- (violated gate indices at `rows`, fixed columns ok) of a chip. -/
def chipViol (I : InJ8) (ch : Char) (rows : List ℕ) : List ℕ × Bool :=
  match ch with
  | 'X' => (violXRows (tabX I) rows, ([(17, CompX.firstMaskE I.X.n), (18, CompX.lastMaskE I.X.n)] :
      List (ℕ × (Fin I.X.n → ZMod Q))).all fun q => (List.finRange I.X.n).all fun i => decide (I.X.cols q.1 i = q.2 i))
  | 'C' => (violMRows tmC (tabC I) rows, prepOK (tabC I))
  | 'W' => (violMRows (tmW I.kroots) (tabW I) rows, prepOK (tabW I))
  | 'J' => (violMRows tmJ (tabJ I) rows, prepOK (tabJ I))
  | 'A' => (violMRows tmA (tabA I) rows, prepOK (tabA I))
  | _ => (violMRows (tmV I.krootsV) (tabV I) rows, prepOK (tabV I))

def skipFor (I : InJ8) (f : Option Fam) (ch : Char) : List ℕ :=
  match f with
  | none => []
  | some f => if f.chip = ch then (match ch with
      | 'A' => [] | _ => idxOfFam I f) else []

/-- One chip's verdict, with the family `f` switched off when `f` belongs to this chip. -/
def chipVerdict (I : InJ8) (f : Option Fam) (ch : Char) : Bool :=
  let off := (f.map (·.chip)).getD ' ' == ch
  match ch with
  | 'X' => if off then checkXOff (skipFor I f 'X') (tabX I) else CompX.checkCompX (tabX I)
  | 'C' => if off then checkMOff tmC (skipFor I f 'C') (tabC I) else checkCellKW (tabC I)
  | 'W' => if off then checkMOff (tmW I.kroots) (skipFor I f 'W') (tabW I) else checkWalkJ8 I.kroots (tabW I)
  | 'J' => if off then ((checkMOff tmJ (skipFor I f 'J') (tabJ I) && MemX.nodupB (tabJ I) && decide (0 < I.J.n) &&
      MemX.adjB (tabJ I))) else checkJOK (tabJ I)
  | 'A' => if off then
      (match f with
       | some f => checkMOff tmA0 (famIdx tmA0 f) (tabA I) && checkMOff tmA (famIdx tmA f) (tabA I)
       | none => true)
    else checkAtomHQ (tabA I) && checkAtomHQL (tabA I)
  | _ => if off then
      (checkMOff (tmV I.krootsV) (skipFor I f 'V') (tabV I) && MemX.nodupB (tabV I) && MemX.adjB (tabV I) &&
        decide (1 ≤ I.krootsV) && decide (I.krootsV ≤ I.V.n) && decide (I.krootsV + I.V.n < Q))
    else checkAWOK I.krootsV (tabV I)

def chipsBOff (I : InJ8) (f : Option Fam) : Bool :=
  ['X', 'C', 'W', 'J', 'A', 'V'].all (chipVerdict I f)

/-- **The scratch checker `checkJ8Off`**: `checkJ8` with one gate family switched off (`none`: the real checker's logic). -/
def checkJ8Off (f : Option Fam) (I : InJ8) : Bool :=
  if hv : validB I = true then
    checkStaticJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g &&
    checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && chipsBOff I f
  else false

/-- The scratch verdict for an instance whose only edited chip is `ch`: validity, static, public equations and that chip
(the other chips are the honest instance's, whose verdict is reused). -/
def checkOnly (f : Option Fam) (ch : Char) (I : InJ8) : Bool :=
  if hv : validB I = true then
    checkStaticJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g &&
    checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && chipVerdict I f ch
  else false

def getColC (I : InJ8) (ch : Char) (c r : ℕ) : ZMod Q :=
  getColA (match ch with | 'X' => I.X | 'C' => I.C | 'W' => I.W | 'J' => I.J | 'A' => I.A | _ => I.V) c r

def sampleRows (n : ℕ) : List ℕ :=
  if n ≤ 5 then List.range n else ([0, 1, n / 2, n - 1].eraseDups)

structure Wit where
  fam : String
  prog : String
  chip : Char
  edit : String
  nviol : ℕ
  ed : Edit

/-- Single-cell edit search on one chip of one instance: for every edit, the violated gate set at the affected rows;
record, per family, the edit whose violated set lies INSIDE that family (non-empty) and whose fixed columns still hold.
Returns also how many edits no gate detected (dead cells) and the number of edits. -/
def fuzzChip (prog : String) (I : InJ8) (ch : Char) (pairs : Bool := false) : IO (List Wit × ℕ × ℕ) := do
  let n := chipN I ch
  if n == 0 then return ([], 0, 0)
  let fams := famsOfChip ch
  let idxs := fams.map (idxOfFam I)
  let mut wits : Array (Option Wit) := Array.replicate fams.length none
  let mut dead := 0
  let mut total := 0
  let stateRows : List ℕ := if ch == 'X' then
      (List.range 17).filterMap (fun st => (List.range n).find? fun r => getColC I 'X' st r == 1) else []
  let rows := if ch == 'X' && n > 20 then (stateRows ++ [n - 1]).eraseDups else (sampleRows n ++ stateRows).eraseDups
  let allRows := List.range n
  let mut edits : List (String × Edit × List ℕ) := []
  for c in List.range (chipW ch) do
    for r in rows do
      let aff := ([r - 1, r, n - 1].eraseDups)
      edits := edits ++ [(s!"col {c} row {r}: +1",
        (fun (c' r' : ℕ) (v : ZMod Q) => if c' = c ∧ r' = r then v + 1 else v), aff)]
      if (getColC I ch c r == 0 || getColC I ch c r == 1) then
        edits := edits ++ [(s!"col {c} row {r}: 1 - v",
          (fun (c' r' : ℕ) (v : ZMod Q) => if c' = c ∧ r' = r then 1 - v else v), aff)]
    for r in rows do
      let aff := ([r - 1, r, n - 1].eraseDups)
      for k in ([0, 1, 2] : List ℕ) do
        if getColC I ch c r != (k : ZMod Q) then
          edits := edits ++ [(s!"col {c} row {r}: := {k}",
            (fun (c' r' : ℕ) (v : ZMod Q) => if c' = c ∧ r' = r then (k : ZMod Q) else v), aff)]
    if n ≤ 20 then edits := edits ++ [(s!"col {c} all rows: +1", (fun (c' _ : ℕ) (v : ZMod Q) => if c' = c then v + 1 else v), allRows)]
  if pairs then
    edits := []
    let bw := match ch with | 'X' => 123 | 'C' => 134 | 'W' => 25 | 'J' => 29 | 'A' => 205 | _ => 25
    for r in rows do
      let aff := ([r - 1, r, n - 1].eraseDups)
      for c1 in List.range bw do
        for c2 in List.range bw do
          if c1 < c2 then
            for (dn, d1, d2) in [("+1,+1", (1 : ZMod Q), (1 : ZMod Q)), ("+1,-1", 1, -1), ("-1,+1", -1, 1)] do
              edits := edits ++ [(s!"cols {c1},{c2} row {r}: {dn}",
                (fun (c' r' : ℕ) (v : ZMod Q) => if r' = r then (if c' = c1 then v + d1 else if c' = c2 then v + d2 else v) else v), aff)]
  for (d, ed, aff) in edits do
    let I' := editInst I ch ed
    let (v, pr) := chipViol I' ch aff
    total := total + 1
    if v.isEmpty && pr then dead := dead + 1
    else if pr && !v.isEmpty then
      for k in List.range fams.length do
        if v.all (idxs[k]!.contains ·) then
          let better := match wits[k]! with
            | none => true
            | some w => v.length < w.nviol
          if better then wits := wits.set! k (some ⟨fams[k]!.name, prog, ch, d, v.length, ed⟩)
  return (wits.toList.filterMap id, dead, total)

end Scratch

end Nock.V1J8.D5Abl

namespace Nock.V1J8.D5Red

open Nock.TraceGenExe Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Example Nock.V1J8.Gen
open Nock.DriverJ8.DriverJ8 Nock.DriverJ8.TranscriptJ8
open Nock.V1J8.D5Abl (census fuzzChip famsOfChip checkOnly editInst Fam Wit pad Edit idxOfFam chipViol chipN getColA)

abbrev P : ℕ := Nock.Field.p

/-! ## 0. Small helpers -/

def flush : IO Unit := do (← IO.getStdout).flush

def timed {α} (act : IO α) : IO (α × ℕ) := do
  let t0 ← IO.monoMsNow
  let r ← act
  let t1 ← IO.monoMsNow
  return (r, t1 - t0)

def nA (n : ℕ) : Nock.Noun := .atom n
def nC (a b : Nock.Noun) : Nock.Noun := .cell a b

/-! ## 1. The FS coins of an instance, and the honest FS instance -/

/-- The Fiat-Shamir coins re-derived from an instance's public record, claim, round columns and message (what
`verify` does from the stored files). -/
def fsCoinsOf (ph : CoinsE) (I : InJ8) : CoinsE :=
  let pub := pubFields I
  let claim := claimFields I
  let cvs := chipsOf I
  let c0 := roundCommit 0 cvs
  let c1 := roundCommit 1 cvs
  let c2 := roundCommit 2 cvs
  let cfg := run (sched pub claim c0 c1 c2 (msgFlat I.M))
  coinsToE cfg.2 ph

/-- The honest instance at the Fiat-Shamir coins (the first stages of `drive`, in process). -/
def fsInstance (B : Backend) : IO InJ8 := do
  let I0 ← genIO B B.ph
  let pub := pubFields I0
  let claim := claimFields I0
  let c0 := roundCommit 0 (chipsOf I0)
  let cfg0 := runFrom initCfg (hdrEvents pub claim ++ [.absorb "commit/r0" c0])
  let cfg1 := step cfg0 (.squeeze idxS0)
  let I1 ← genIO B (coinsToE cfg1.2 B.ph)
  let c1 := roundCommit 1 (chipsOf I1)
  let cfg2 := step cfg1 (.absorb "commit/r1" c1)
  let cfg3 := step cfg2 (.squeeze idxS1)
  genIO B (coinsToE cfg3.2 B.ph)

/-- The verdict a verifier holding only the files reaches: re-derive the coins, check at them. -/
def fsVerdict (ph : CoinsE) (chk : InJ8 → Bool) (I : InJ8) : Bool :=
  chk { I with χ := fsCoinsOf ph I }

/-! ## 2. The programs -/

def ph1 : CoinsE := prngCoins 1

/-- `genJ8` of a subject / formula given as text. -/
def genText (s f : String) (χ : CoinsE) : Except String InJ8 := do
  let sn ← Nock.TraceGenExe.parseNoun s
  let fn ← Nock.TraceGenExe.parseNoun f
  match genJ8 (fun _ => none) 100000 sn fn χ with
  | some I => pure I
  | none => throw s!"no run / out of scope: *[{s} {f}]"

def backendOfGen (gen : CoinsE → Except String InJ8) (chk : InJ8 → Bool := checkFast) : Backend :=
  { gen := gen, check := chk, ph := ph1 }

/-! ### 2a. The tiny jet: `f(a, b) = a * b + b` as registry id 7, called on `[3 4]` (result `16`) -/

open Nock.Jet.Autogen in
def tinyT : Tpl where
  k := 2
  ax := ![12, 13]
  inTy := fun _ => .F
  outTy := .F
  body := .add (.mul (.var 0) (.var 1)) (.var 1)

def tinyS : Nock.Noun := nC (nA 0) (nC (nC (nA 3) (nA 4)) (nA 0))

def tinyProg : Nock.Noun :=
  Nock.Jet.wildCall 7 (Nock.Jet.Autogen.compile P tinyT)

def genTiny (χ : CoinsE) : Except String InJ8 :=
  match genJ8J (fun _ => tinyT) [7] 2 tinyS tinyProg χ with
  | some I => pure I
  | none => throw "tiny: no run / out of scope"

/-! ### 2b. The big-atom programs (as `J8CheckMain.progInput`, subject `p - 1`) -/

def pm1 : Nock.Noun := nA (P - 1)
def inc1 : Nock.Noun := nC (nA 4) (nC (nA 0) (nA 1))
def inc2 : Nock.Noun := nC (nA 4) inc1

def bigFormula (nm : String) : Option Nock.Noun :=
  if nm = "cnt" then some (nC (nA 3) (nC inc2 (nC (nA 1) (nA 0))))
  else if nm = "ne5" then some (nC (nA 5) (nC inc1 inc2))
  else if nm = "eq5" then some (nC (nA 5) (nC inc2 inc2))
  else none

def genBig (nm : String) (χ : CoinsE) : Except String InJ8 :=
  match bigFormula nm with
  | none => throw s!"unknown big program {nm}"
  | some f =>
    match genJ8A (fun _ => none) 1000 pm1 f χ with
    | some I => pure I
    | none => throw s!"{nm}: no run / jet call"

def backendOfName (nm : String) : Backend :=
  if nm = "tiny" then backendOfGen genTiny
  else if (bigFormula nm).isSome then backendOfGen (genBig nm)
  else backendOfGen fun χ => do
    let some (_, st, ft) := Nock.TraceGenExe.demos.find? (fun d => d.1 = nm) | throw s!"unknown {nm}"
    genText st ft χ

/-! ## 3. 4b: the sequentiality exhibit (B1 ported)

The program is `*[0 [1 X]] = X` with `X = [[[1 2] [3 4]] [[5 6] [7 8]]]` (D3's B1 noun).  The cell fingerprint of the claimed
result (`encE z y`, `claimRecsJ8E`) is, in its leaf coordinate, `Σ_i w_i · leaf_i` with `w_i ∈ K6` fixed by the shape and by the
coin `z`.  A prover that KNOWS `z` before committing solves `Σ_i Δ_i w_i = 0` over `𝔽_p` (6 equations, 8 unknowns: a kernel of
dimension ≥ 2) and claims the result `X + Δ` whose fingerprint equals `X`'s.  Everything else in the instance is the honest
instance for `X`. -/

def verdictStr (b : Bool) : String := if b then "ACCEPTED" else "rejected"

def b1Leaves : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8]

/-- The noun `[[[a b] [c d]] [[e f] [g h]]]` of a leaf list. -/
def mk8 (l : List ℕ) : Nock.Noun :=
  let a := fun i => nA (l.getD i 0)
  nC (nC (nC (a 0) (a 1)) (nC (a 2) (a 3))) (nC (nC (a 4) (a 5)) (nC (a 6) (a 7)))

def k6Coords (x : K6) : List ℕ :=
  [x.re.c0, x.re.c1, x.re.c2, x.im.c0, x.im.c1, x.im.c2].map fun g => g.toZ.val

/-- `a^e mod P`. -/
def powMod (a e : ℕ) : ℕ := Id.run do
  let mut r := 1
  let mut b := a % P
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := r * b % P
    b := b * b % P
    k := k / 2
  return r

def invMod (a : ℕ) : ℕ := powMod a (P - 2)

/-- The leaf weights `w_i` (6 coordinates each) of the shape `mk8` at the coins `χ`. -/
def leafWeights (χ : CoinsE) : List (List ℕ) :=
  (List.range 8).map fun i =>
    k6Coords ((encE (zE χ) (yE χ) (mk8 ((List.range 8).map fun j => if j = i then 1 else 0))).leaf)

/-- A nonzero `Δ ∈ 𝔽_p^8` (as residues) with `Σ Δ_i w_i = 0`, by Gaussian elimination mod `P`. -/
def kernelVec (w : List (List ℕ)) : Option (List ℕ) := Id.run do
  -- matrix rows = coordinates (6), columns = leaves (8)
  let mut M : Array (Array ℕ) := ((List.range 6).map fun r => ((List.range 8).map fun c => (w.getD c []).getD r 0 % P).toArray).toArray
  let mut piv : List ℕ := []   -- pivot column of row r (in order)
  let mut row := 0
  for c in List.range 8 do
    if row < 6 then
      -- find a pivot in column c at rows ≥ row
      let mut pr : Option ℕ := none
      for r in List.range 6 do
        if r ≥ row && pr.isNone && (M[r]!)[c]! != 0 then pr := some r
      match pr with
      | none => pure ()
      | some r =>
        let tmp := M[r]!
        M := M.set! r M[row]!
        M := M.set! row tmp
        let iv := invMod (M[row]!)[c]!
        M := M.set! row ((M[row]!).map fun x => x * iv % P)
        for r2 in List.range 6 do
          if r2 != row && (M[r2]!)[c]! != 0 then
            let f := (M[r2]!)[c]!
            M := M.set! r2 (((List.range 8).map fun cc => ((M[r2]!)[cc]! + (P - f) * (M[row]!)[cc]!) % P).toArray)
        piv := piv ++ [c]
        row := row + 1
  -- a free column
  let free := (List.range 8).filter fun c => !piv.contains c
  match free with
  | [] => return none
  | f :: _ =>
    -- Δ_f = 1, other free = 0; Δ_{piv r} = -M[r][f]
    let mut d : Array ℕ := Array.replicate 8 0
    d := d.set! f 1
    for (c, r) in piv.zipIdx do
      d := d.set! c ((P - (M[r]!)[f]!) % P)
    return some d.toList

def forgedLeaves (δ : List ℕ) : List ℕ := b1Leaves.zipWith (fun a d => (a + d) % P) δ

/-- Swap the claimed result of an instance. -/
def withResult (I : InJ8) (r : Nock.Noun) : InJ8 := { I with c := { I.c with result := r } }

def b1Gen (χ : CoinsE) : Except String InJ8 := genText "0" "[1 [[1 2] [3 4]] [[5 6] [7 8]]]" χ

/-- The forged result for KNOWN coins `χ`. -/
def forgeFor (χ : CoinsE) : Option Nock.Noun := (kernelVec (leafWeights χ)).map fun δ => mk8 (forgedLeaves δ)

def seqMain : IO UInt32 := do
  IO.println "# 4b: sequentiality exhibit, program *[0 [1 [[[1 2] [3 4]] [[5 6] [7 8]]]]] (honest result X)"
  let chi := ph1
  let some X' := forgeFor chi | IO.eprintln "no kernel vector"; return 2
  let honest ← match b1Gen chi with | .ok I => pure I | .error e => do IO.eprintln e; return 2
  IO.println s!"honest instance: rows compute {honest.X.n}, cell {honest.C.n}, walk {honest.W.n}"
  IO.println s!"forged result X' = {repr X'}"
  IO.println s!"X' ≠ X: {decide (X' ≠ honest.c.result)}"
  -- control: the same swap at a coin the forgery was NOT solved for
  let chi2 := prngCoins 2
  let (okH, t) ← timed (pure (checkFast honest))
  IO.println s!"[control] honest claim at the known coins: {if okH then "ACCEPT" else "REJECT"} ({t} ms)"
  -- (a) known-first
  let forged := withResult honest X'
  let (okK, t) ← timed (pure (checkJ8 forged))
  IO.println s!"[known-first] coins fixed BEFORE the commitment, forged claim X' (solved for those coins): {if okK then "ACCEPTED" else "REJECTED"} ({t} ms)"
  -- the same forged claim, the honest trace regenerated at other coins: coins drawn after commit
  let h2 ← match b1Gen chi2 with | .ok I => pure I | .error e => do IO.eprintln e; return 2
  let okO := checkFast (withResult h2 X')
  IO.println s!"[post-commit coins, random] forged claim X' at the coin vector prngCoins 2: {if okO then "ACCEPTED" else "REJECTED"}"
  -- a random (not solved) swap at the known coins
  let rnd := mk8 [1, 2, 3, 4, 5, 6, 7, 9]
  let okR := checkFast (withResult honest rnd)
  IO.println s!"[control] a wrong result NOT solved for the coins, at the known coins: {if okR then "ACCEPTED" else "REJECTED"}"
  -- (b) interactive and (c) FS: the cheating prover's backend commits to the forged claim X' (solved for ph1)
  let cheat := backendOfGen (fun χ => (b1Gen χ).map fun I => withResult I X')
  let dirFs := "/tmp/d5b-seq-fs"
  let (rFs, t) ← timed (drive cheat .fs (System.FilePath.mk dirFs) "b1-forged")
  IO.println s!"[FS] cheating prover (forged claim X'), coins squeezed from the transcript: {if rFs.accepted then "ACCEPTED" else "REJECTED"} ({t} ms)"
  let (vFs, t) ← timed (verify cheat (System.FilePath.mk dirFs))
  IO.println s!"[FS verify] re-derived from the files: {if vFs.accepted then "ACCEPTED" else "REJECTED"} ({t} ms)"
  let dirI := "/tmp/d5b-seq-int"
  let (rI, t) ← timed (drive cheat .interactive (System.FilePath.mk dirI) "b1-forged")
  IO.println s!"[interactive] coins drawn from OS randomness after each freeze: {if rI.accepted then "ACCEPTED" else "REJECTED"} ({t} ms)"
  -- honest runs accept under both
  let honestB := backendOfGen b1Gen
  let (hF, _) ← timed (drive honestB .fs (System.FilePath.mk "/tmp/d5b-seq-hfs") "b1")
  let (hI, _) ← timed (drive honestB .interactive (System.FilePath.mk "/tmp/d5b-seq-hint") "b1")
  IO.println s!"[honest] FS {if hF.accepted then "ACCEPT" else "REJECT"}, interactive {if hI.accepted then "ACCEPT" else "REJECT"}"
  return 0


/-! ### 4b'. Planted-coin exhibits (summand E's): a false claim accepted only at a coin inside a priced bad event

The coin vector is chosen BEFORE the commitment (known-first) so that the event holds; the false claim is then accepted by the
real checker.  Under Fiat-Shamir / interactive coins (drawn after the commitment) the same forged claim is rejected. -/

/-- Solve `Σ_j x_j · col_j = rhs` over `𝔽_p` (columns of 6 coordinates), free variables `0`. -/
def solveLin (cols : List (List ℕ)) (rhs : List ℕ) : Option (List ℕ) := Id.run do
  let m := cols.length
  let mut M : Array (Array ℕ) := ((List.range 6).map fun r =>
    (((List.range m).map fun c => (cols.getD c []).getD r 0 % P) ++ [rhs.getD r 0 % P]).toArray).toArray
  let mut piv : List ℕ := []
  let mut row := 0
  for c in List.range m do
    if row < 6 then
      let mut pr : Option ℕ := none
      for r in List.range 6 do
        if r ≥ row && pr.isNone && (M[r]!)[c]! != 0 then pr := some r
      match pr with
      | none => pure ()
      | some r =>
        let tmp := M[r]!
        M := M.set! r M[row]!
        M := M.set! row tmp
        let iv := invMod (M[row]!)[c]!
        M := M.set! row ((M[row]!).map fun x => x * iv % P)
        for r2 in List.range 6 do
          if r2 != row && (M[r2]!)[c]! != 0 then
            let f := (M[r2]!)[c]!
            M := M.set! r2 (((List.range (m + 1)).map fun cc => ((M[r2]!)[cc]! + (P - f) * (M[row]!)[cc]!) % P).toArray)
        piv := piv ++ [c]
        row := row + 1
  -- consistency: rows ≥ row must have rhs 0
  for r in List.range 6 do
    if r ≥ row && (M[r]!)[m]! != 0 then return none
  let mut x : Array ℕ := Array.replicate m 0
  for (c, r) in piv.zipIdx do
    x := x.set! c ((M[r]!)[m]!)
  return some x.toList

/-- Left comb `[[[a b] c] d] ...` of a leaf list. -/
def combOf (l : List ℕ) : Nock.Noun :=
  match l with
  | [] => nA 0
  | a :: r => r.foldl (fun acc x => nC acc (nA x)) (nA a)

def unitCols (χ : CoinsE) (shape : List ℕ → Nock.Noun) (k : ℕ) : List (List ℕ) :=
  (List.range k).map fun i => k6Coords ((encE (zE χ) (yE χ) (shape ((List.range k).map fun j => if j = i then 1 else 0))).leaf)

def subK6 (a b : List ℕ) : List ℕ := (a.zip b).map fun (x, y) => (x + (P - y % P)) % P

def sumFp (e : FPE) : K6 := e.size + e.dyck + e.leaf

/-- Run one planted-coin exhibit. -/
def plantedRun (name : String) (χ : CoinsE) (gen : CoinsE → Except String InJ8) (forged : Nock.Noun) : IO Unit := do
  IO.println s!"\n### {name}"
  let honest ← match gen χ with | .ok I => pure I | .error e => do IO.println s!"generator error: {e}"; return
  IO.println s!"honest claim result: {repr honest.c.result}"
  IO.println s!"forged claim result: {repr forged}"
  IO.println s!"honest at the planted coins: {verdictStr (checkFast honest)}"
  let fk := checkFast (withResult honest forged)
  IO.println s!"[known-first, planted coins] FORGED claim: {verdictStr fk}"
  flush
  let cheat := backendOfGen (fun c => (gen c).map fun I => withResult I forged)
  let chB : Backend := { cheat with ph := χ }
  let (rFs, _) ← timed (drive chB .fs (System.FilePath.mk s!"/tmp/d5b-planted-fs") name)
  IO.println s!"[FS coins after the commitment] forged claim: {verdictStr rFs.accepted}"
  let (rI, _) ← timed (drive chB .interactive (System.FilePath.mk s!"/tmp/d5b-planted-int") name)
  IO.println s!"[interactive coins after the commitment] forged claim: {verdictStr rI.accepted}"
  flush

def zeroCoins (idx : List ℕ) (χ : CoinsE) : CoinsE := fun i => if idx.contains i.val then (0 : K3) else χ i

def oneCoin (idx : ℕ) (χ : CoinsE) : CoinsE := fun i => if i.val = idx then (⟨natG 1, natG 0, natG 0⟩ : K3) else χ i

def plantedMain : IO UInt32 := do
  -- P1: seed / fingerprint coin z = 0 (zeroVS): the leaf coordinate only sees the leftmost leaf
  let χz := zeroCoins [2, 3] ph1
  plantedRun "P1 z = 0 (χ2 = χ3 = 0), program *[0 [1 [1 2]]] = [1 2], forged [1 3]" χz (genText "0" "[1 [1 2]]")
    (nC (nA 1) (nA 3))
  -- P2: the validity compression coin γ' = 1 (χ4 = 1, χ6 = 0): claim record collision with a DIFFERENT SHAPE (left comb)
  let χg := zeroCoins [6] (oneCoin 4 ph1)
  let e1 := encE (zE χg) (yE χg) (mk8 b1Leaves)
  let leafW := unitCols χg combOf 8
  let e2z := encE (zE χg) (yE χg) (combOf [0, 0, 0, 0, 0, 0, 0, 0])
  let rhs := subK6 (k6Coords (sumFp e1)) (k6Coords (e2z.size + e2z.dyck))
  match solveLin leafW rhs with
  | none => IO.println "P2: no solution"
  | some v =>
    plantedRun "P2 γ' = 1 (χ4 = 1, χ6 = 0), program *[0 [1 X]], X = balanced 8 leaves, forged: a left comb of 8 leaves" χg
      b1Gen (combOf v)
  return 0

/-! ## 4. 4a: tamper tables on J and atom records -/

def getCol (q : ChipIn) (c i : ℕ) : ZMod P := if h : i < q.n then q.cols c ⟨i, h⟩ else 0

def setCol (q : ChipIn) (c i : ℕ) (v : ZMod P) : ChipIn :=
  ⟨q.h, q.n, q.ω, fun c' i' => if c' = c ∧ (i' : ℕ) = i then v else q.cols c' i'⟩

def addCol (q : ChipIn) (c i : ℕ) (d : ZMod P) : ChipIn := setCol q c i (getCol q c i + d)

def swapCol (q : ChipIn) (c1 i1 c2 i2 : ℕ) : ChipIn :=
  let a := getCol q c1 i1
  let b := getCol q c2 i2
  setCol (setCol q c1 i1 b) c2 i2 a

/-- Delete row `k`. -/
def delRow (q : ChipIn) (k : ℕ) : ChipIn :=
  ⟨q.h, q.n - 1, q.ω, fun c i => getCol q c (if (i : ℕ) < k then i else i + 1)⟩

/-- Duplicate row `k` (the copy right after it). -/
def dupRow (q : ChipIn) (k : ℕ) : ChipIn :=
  ⟨q.h, q.n + 1, q.ω, fun c i => getCol q c (if (i : ℕ) ≤ k then i else i - 1)⟩

def firstRowWhere (q : ChipIn) (p : ℕ → Bool) : Option ℕ :=
  ((List.finRange q.n).find? fun i => p i.val).map (·.val)

/-- The J row of kind `kd` last / first in the layout. -/
def lastKd (I : InJ8) (kd : Nock.Jet.ChipJ8.Kd) : ℕ :=
  (((List.finRange I.J.n).filter fun i => (I.lay i).kd == kd).getLast?.map (·.val)).getD 0

def firstKd (I : InJ8) (kd : Nock.Jet.ChipJ8.Kd) : ℕ :=
  (((List.finRange I.J.n).filter fun i => (I.lay i).kd == kd).head?.map (·.val)).getD 0

def layGet (I : InJ8) (j : ℕ) : Nock.Jet.ChipJ8.PRow :=
  if h : j < I.J.n then I.lay ⟨j, h⟩ else ⟨.nil, 0, 0, 0, 0, 0⟩

def withJ (I : InJ8) (J' : ChipIn) : InJ8 := { I with J := J', lay := fun i => layGet I i }

/-- Layout edit consistent with a J edit: row `k`'s layout id replaced. -/
def withCallId (I : InJ8) (k nid : ℕ) : InJ8 :=
  { withJ I (setCol I.J 13 k (nid : ZMod P)) with
    lay := fun i => if (i : ℕ) = k then { layGet I i with id := nid } else layGet I i }

def dropJ (I : InJ8) (k : ℕ) : InJ8 :=
  { I with J := delRow I.J k
           lay := fun i => layGet I (if (i : ℕ) < k then i else i + 1)
           r := { I.r with J := I.r.J - 1 } }

def dupJ (I : InJ8) (k : ℕ) : InJ8 :=
  { I with J := dupRow I.J k
           lay := fun i => layGet I (if (i : ℕ) ≤ k then i else i - 1)
           r := { I.r with J := I.r.J + 1 } }

/-- **J record tampers** (jetted program with J present). -/
def jTampers (I : InJ8) : List (String × InJ8) :=
  let call := firstKd I .call
  let ad := lastKd I .add
  let ml := lastKd I .mul
  [("J1 wrong call result: the add node's value + 1 (row " ++ toString ad ++ ")", withJ I (addCol I.J 20 ad 1)),
   ("J2 wrong call result: the mul node's value + 1 (row " ++ toString ml ++ ")", withJ I (addCol I.J 20 ml 1)),
   ("J3 wrong call result handle: call row vR + 1", withJ I (addCol I.J 28 call 1)),
   ("J4 wrong argument: call row subject handle vL + 1", withJ I (addCol I.J 26 call 1)),
   ("J5 wrong function: call row formula handle vN + 1", withJ I (addCol I.J 24 call 1)),
   ("J6 wrong id in the witness column (13) only", withJ I (addCol I.J 13 call 1)),
   ("J7 wrong id in the layout and column (call to id 8)", withCallId I call 8),
   ("J8 dropped call row", dropJ I call),
   ("J9 duplicated call row", dupJ I call),
   ("J10 call multiplicity m + 1 (service provide)", withJ I (addCol I.J 18 call 1)),
   ("J11 registry row: vN + 1", withJ I (addCol I.J 24 (firstKd I .reg) 1)),
   ("J12 operand handle of the add node (v1 + 1)", withJ I (addCol I.J 21 ad 1))]

def kbCols : ℕ := 130

/-- **Atom record tampers** (big-atom program). -/
def aTampers (I : InJ8) : List (String × InJ8) :=
  let incR := firstNZ I.A 197
  let convR := firstNZ I.A 198
  let smallKbR := (firstRowWhere I.C fun i => getCol I.C 130 i == 0 && getCol I.C 6 i == 0).getD 0
  let bigKbR := firstNZ I.C 130
  let xr := (firstRowWhere I.X fun i => getCol I.X 29 i != getCol I.X 31 i).getD 0
  [("A1 wrong limb: aL + 1 on atom row 0 (bits unchanged)", { I with A := addCol I.A 7 0 1 }),
   ("A2 wrong limb together with its bit decomposition: aL + 2^32 not representable; aL ↦ aL + 1 and bit 0 flipped",
     { I with A := setCol (addCol I.A 7 0 1) 130 0 (1 - getCol I.A 130 0) }),
   (s!"A3 wrong carry: c_out flipped on atom row {incR}", { I with A := setCol I.A 199 incR (1 - getCol I.A 199 incR) }),
   (s!"A4 wrong carry on row {convR}: c_out := 1", { I with A := setCol I.A 199 convR 1 }),
   (s!"A5 wrong kind bit: kR_o flipped on atom row {incR}", { I with A := setCol I.A 202 incR (1 - getCol I.A 202 incR) }),
   (s!"A6 wrong kind bit: inc flag flipped on atom row {incR}", { I with A := setCol I.A 197 incR (1 - getCol I.A 197 incR) }),
   (s!"A8 small treated as big: cell kbL := 1 on row {smallKbR}", { I with C := setCol I.C 130 smallKbR 1 }),
   ("A9 swapped atom handles in the compute table (sf1.v <-> sf2.v on row " ++ toString xr ++ ")",
     { I with X := swapCol I.X 29 xr 31 xr }),
   ("A10 swapped atom handles: atom rows 0 and 1 exchange their serial idx",
     if I.A.n ≥ 2 then { I with A := swapCol I.A 2 0 2 1 } else I),
   ("A11 atom row's wR flag flipped (value vs handle) on row 0", { I with A := setCol I.A 6 0 (1 - getCol I.A 6 0) }),
   (s!"A12 conversion flag set on inc row {incR}", { I with A := setCol I.A 198 incR 1 })] ++
  (if (List.finRange I.C.n).any (fun i => I.C.cols 130 i != 0) then
    [(s!"A7 big treated as small: cell kbL cleared on row {bigKbR}", { I with C := setCol I.C 130 bigKbR 0 })] else [])

def failingParts (I : InJ8) : List String :=
  ((parts I).filter fun x => !x.2).map fun x => (x.1.splitOn " ").headD x.1 ++ ((x.1.splitOn " ").getD 1 "")

/-- A tamper table.  `fixed` is the verdict at the coins of the honest FS run (full checker, or for the J table only the
edited chip: the other chips are unchanged, the honest verdict is reused); `doFs` also re-derives the coins from the
tampered files (`verify`'s verdict). -/
def jWhy (I : InJ8) : String :=
  if hv : validB I = true then
    let st := checkStaticJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g
    let pb := checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M
    let ch := Nock.V1J8.D5Abl.chipVerdict I none 'J'
    ", ".intercalate ([("static", st), ("public equations", pb), ("J chip", ch)].filter (fun x => !x.2) |>.map (·.1))
  else "valid"

def tamperTable (title : String) (B : Backend) (tampers : InJ8 → List (String × InJ8)) (fixed : InJ8 → Bool)
    (doFs : Bool) (why : InJ8 → String) : IO Bool := do
  IO.println s!"\n## {title}"
  let I ← fsInstance B
  IO.println s!"honest FS instance: rows compute {I.X.n}, cell {I.C.n}, walk {I.W.n}, J {I.J.n}, atom {I.A.n}, atom walk {I.V.n}"
  flush
  let t0 ← IO.monoMsNow
  let h1 := checkFast I
  IO.println s!"honest at its FS coins: {if h1 then "ACCEPT" else "REJECT"} (full check {(← IO.monoMsNow) - t0} ms)"
  flush
  let h2 := if doFs then fsVerdict ph1 checkFast I else true
  if doFs then IO.println s!"honest, coins re-derived from the files: {if h2 then "ACCEPT" else "REJECT"}"
  IO.println "| tamper | fixed FS coins | coins re-derived from tampered files | failing components (fixed coins) |"
  IO.println "|---|---|---|---|"
  flush
  let mut allRej := true
  for (n, T) in tampers I do
    let a := fixed T
    let b := if doFs then verdictStr (fsVerdict ph1 checkFast T) else "not run (all round-1/2 columns go stale)"
    if a || b == "ACCEPTED" then allRej := false
    IO.println s!"| {n} | {verdictStr a} | {b} | {why T} |"
    flush
  return h1 && h2 && allRej

def tamperMain (which : String) (doFs : Bool) : IO UInt32 := do
  let mut ok := true
  if which == "j" || which == "all" then
    let r1 ← tamperTable "J record tampers, jetted `f(a,b)=a*b+b` on [3 4] (id 7)" (backendOfGen genTiny) jTampers
      (checkOnly none 'J') doFs jWhy
    ok := ok && r1
  if which == "a" || which == "all" then
    for nm in ["cnt", "ne5", "eq5"] do
      let r ← tamperTable s!"atom record tampers, program {nm}" (backendOfGen (genBig nm)) aTampers checkFast doFs (fun T => ", ".intercalate (failingParts T))
      ok := ok && r
  IO.println s!"\nall honest accept and all tampers rejected: {ok}"
  return (if ok then 0 else 1)


def ablateMain (progs : List String) (pairs : Bool := false) (chips : List Char := ['X', 'C', 'W', 'J', 'A', 'V']) : IO UInt32 := do
  let mut found : List Wit := []
  for nm in progs do
    let B := backendOfName nm
    let I ← genIO B B.ph
    IO.println s!"\n# {nm}: rows compute {I.X.n}, cell {I.C.n}, walk {I.W.n}, J {I.J.n}, atom {I.A.n}, atom walk {I.V.n}"
    flush
    for ch in chips do
      let (ws, dead, tot) ← fuzzChip nm I ch pairs
      IO.println s!"  chip {ch}: {tot} single-cell edits, {dead} undetected by any gate, {ws.length} families isolated"
      flush
      for w in ws do
        let fam := (famsOfChip ch).find? (·.name == w.fam)
        let I' := editInst I ch w.ed
        let on := checkOnly none ch I'
        let off := checkOnly fam ch I'
        IO.println s!"    {pad w.fam 22} {w.edit}: {w.nviol} gates violated; family on: {verdictStr on}; family OFF (scratch): {verdictStr off}"
        flush
      found := found ++ ws
  return 0


/-! ## 6. Timing columns (`--fast` checker) -/

def touchChip (q : ChipIn) (w : ℕ) : ℕ :=
  (List.finRange q.n).foldl (fun acc i => (List.range w).foldl (fun a c => a + (q.cols c i).val) acc) 0

def touchAll (I : InJ8) : ℕ :=
  touchChip I.X 123 + touchChip I.C 242 + touchChip I.W 166 + touchChip I.J 71 + touchChip I.A 349 + touchChip I.V 166

def fmtMs (t : ℕ) : String := s!"{t / 1000}.{(t % 1000) / 100} s"

def timeRow (label : String) (g : CoinsE → Option InJ8) : IO Unit := do
  let χ := prngCoins 1
  let t0 ← IO.monoMsNow
  match g χ with
  | none => IO.println s!"| {label} | none (no run / scope) | | | |"
  | some I =>
    let rs := Nock.V1J8.D5.rowsOf I
    let s := touchAll I
    IO.println s!"{label}: rows {rs}, column checksum {s % 1000003}"
    let t1 ← IO.monoMsNow
    flush
    let ok := checkFast I
    IO.println s!"{label}: checkFast = {ok}"
    let t2 ← IO.monoMsNow
    IO.println s!"| {label} | {rs} | {fmtMs (t1 - t0)} | {fmtMs (t2 - t1)} | {if ok then "ACCEPT" else "REJECT"} |"
    flush

def timeMain (which : List String) : IO UInt32 := do
  IO.println "| program | rows (compute, cell, walk, J, atom, atom walk) | tracegen + column fill | checkFast (re-evaluates columns) | verdict |"
  IO.println "|---|---|---|---|---|"
  for w in which do
    match w.splitOn ":" with
    | ["jet", n] => timeRow s!"jetted N={n}" (Nock.V1J8.D5.genJet n.toNat!)
    | ["pure", n] => timeRow s!"pure N={n}" (Nock.V1J8.D5.genPure n.toNat!)
    | [nm] => timeRow nm (fun χ => (backendOfName nm).gen χ |>.toOption)
    | _ => IO.println s!"bad spec {w}"
  return 0


def fsDbg (nm : String) : IO UInt32 := do
  let B := backendOfName nm
  let t0 ← IO.monoMsNow
  let I ← fsInstance B
  IO.println s!"fsInstance {(← IO.monoMsNow) - t0} ms"; flush
  let t1 ← IO.monoMsNow
  let pub := pubFields I
  IO.println s!"pubFields {pub.length} {(← IO.monoMsNow) - t1} ms"; flush
  let t2 ← IO.monoMsNow
  let c0 := roundCommit 0 (chipsOf I)
  IO.println s!"commit0 {c0.length} {(← IO.monoMsNow) - t2} ms"; flush
  let t3 ← IO.monoMsNow
  let cfg := run (sched pub (claimFields I) c0 (roundCommit 1 (chipsOf I)) (roundCommit 2 (chipsOf I)) (msgFlat I.M))
  IO.println s!"sched {cfg.2.length} {(← IO.monoMsNow) - t3} ms"; flush
  let t4 ← IO.monoMsNow
  let ok := checkFast { I with χ := coinsToE cfg.2 ph1 }
  IO.println s!"check {ok} {(← IO.monoMsNow) - t4} ms"; flush
  return 0


/-! ### Refill forgeries: change one multiplicity and recompute the accumulator chain, so that only the terminal gate fails -/

section Refill
open Nock.V1J8.MemX

def layGet' (I : InJ8) (j : ℕ) : Nock.Jet.ChipJ8.PRow := layGet I j

def k6At (q : ChipIn) (base i : ℕ) : K6 :=
  ⟨⟨natG (getColA q base i).val, natG (getColA q (base + 1) i).val, natG (getColA q (base + 2) i).val⟩,
   ⟨natG (getColA q (base + 3) i).val, natG (getColA q (base + 4) i).val, natG (getColA q (base + 5) i).val⟩⟩

def k6Limb (x : K6) (k : ℕ) : ZMod P := if k < 3 then limbZ x.re k else limbZ x.im (k - 3)

/-- Set the multiplicity column `mc` of row `r` to `newM` and shift the accumulator (six columns from `accBase`) of every row
`≥ r` by `Δ = sign · (newM − old) · inv_r` (`inv` six columns from `invBase`). -/
def refillEdit (q : ChipIn) (mc invBase accBase r : ℕ) (newM : ZMod P) (sign : ZMod P) : Edit :=
  let d : ZMod P := (newM - getColA q mc r) * sign
  let δ : K6 := (Nock.V1J8.Gen.fq d) * k6At q invBase r
  fun c r' v =>
    if c = mc ∧ r' = r then newM
    else if accBase ≤ c ∧ c < accBase + 6 ∧ r ≤ r' then v + k6Limb δ (c - accBase)
    else v

/-- The refill forgeries, as `(family, description, chip, edit)`. -/
def refillWitnesses (I : InJ8) : List (String × String × Char × Edit) :=
  let atomRows := List.range I.A.n
  let mbRow := atomRows.find? fun r => getColA I.A 196 r == 1
  let miRow := atomRows.find? fun r => getColA I.A 204 r == 1
  (match mbRow with
   | some r => [("a.g5.term", s!"mb := 0 on atom row {r} (an atom-root provide dropped), accumulator refilled",
       'A', refillEdit I.A 196 313 319 r 0 1)]
   | none => []) ++
  (match miRow with
   | some r => [("a.g7.5.term", s!"mi := 0 on atom row {r} (an inc-record provide dropped), accumulator refilled",
       'A', refillEdit I.A 204 331 337 r 0 1)]
   | none => []) ++
  (let kdsOf := fun (ks : List Nock.Jet.ChipJ8.Kd) =>
      (List.range I.J.n).filter fun r => ks.contains (layGet' I r).kd
   let mk := fun (nm : String) (ks : List Nock.Jet.ChipJ8.Kd) (invBase : ℕ) =>
      match kdsOf ks with
      | r :: r' :: _ => [(nm, s!"inverse limb +1 on J row {r} and -1 on row {r'} (equal weights), accumulator refilled between",
          'J', (fun (c i : ℕ) (v : ZMod P) =>
            if c = invBase ∧ i = r then v + 1 else if c = invBase ∧ i = r' then v - 1
            else if c = 59 ∧ r ≤ i ∧ i < r' then v + 1 else v : Edit))]
      | _ => []
   mk "j.slot0" [.add, .mul, .rp, .sl, .sr, .cp, .isf, .nil, .call] 29 ++ mk "j.slot1" [.add, .mul, .rp, .call] 35) ++
  (if I.C.n > 0 then
    [("c.kw.accTerm", s!"mh := mh + 1 on cell row 0 (an export provide counted once more), accumulator refilled",
      'C', refillEdit I.C 129 230 236 0 (getColA I.C 129 0 + 1) 1)] else []) ++
  (let wv := fun (ch : Char) (q : ChipIn) =>
      (if q.n > 0 then
        [("w.pAcc.term", s!"mL := mL + 1 on walk row 0 (a path consume counted once more), accumulator refilled",
          ch, refillEdit q 10 112 130 0 (getColA q 10 0 + 1) 1)] else []) ++
      (if q.n > 1 then
        [("w.xinv", "x-inverse limb +1 on row 0 and -1 on row 1 (weight 1 each), accumulator refilled between", ch,
          (fun (c i : ℕ) (v : ZMod P) =>
            if c = 106 ∧ i = 0 then v + 1 else if c = 106 ∧ i = 1 then v - 1
            else if c = 124 ∧ i = 0 then v + 1 else v : Edit))] else [])
   wv 'W' I.W ++ (if I.krootsV > 0 then wv 'V' I.V else [])) ++
  (if I.J.n > 0 then
    [("j.accT.term", "mv := mv + 1 on J row 0 (a provide counted once more), accumulator refilled",
      'J', refillEdit I.J 19 41 59 0 (getColA I.J 19 0 + 1) (-1))] else [])

end Refill

def refillMain (progs : List String) : IO UInt32 := do
  for nm in progs do
    let B := backendOfName nm
    let I ← genIO B B.ph
    IO.println s!"\n# {nm}"
    for (fam, desc, ch, ed) in refillWitnesses I do
      let f := (famsOfChip ch).find? (·.name == fam)
      let I' := editInst I ch ed
      let (v, pr) := chipViol I' ch (List.range (chipN I ch))
      let idx := match f with | some f => idxOfFam I f | none => []
      let inside := v.all (idx.contains ·)
      IO.println s!"{pad fam 14} {desc}: violated gates {v.length}, all inside the family: {inside}, fixed columns ok: {pr}; on: {verdictStr (checkOnly none ch I')}; OFF (scratch): {verdictStr (checkOnly f ch I')}"
      flush
  return 0

def infoMain (nm : String) : IO UInt32 := do
  let B := backendOfName nm
  let (r, t) ← timed (do
    let I ← genIO B B.ph
    IO.println s!"{nm}: rows compute {I.X.n}, cell {I.C.n}, walk {I.W.n}, J {I.J.n}, atom {I.A.n}, atom walk {I.V.n}"
    flush
    return I)
  IO.println s!"gen {t} ms"
  flush
  let (ok, t2) ← timed (pure (checkJ8 r))
  IO.println s!"checkJ8 {ok} {t2} ms"
  return 0

end Nock.V1J8.D5Red

open Nock.V1J8.D5Red in
open Nock.V1J8.D5Abl in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["seq"] => seqMain
  | ["planted"] => plantedMain
  | ["tamper", w] => tamperMain w false
  | ["tamper", w, "fs"] => tamperMain w true
  | "ablate" :: ps => ablateMain ps
  | "ablate1" :: chs :: ps => ablateMain ps false chs.toList
  | "ablate2" :: chs :: ps => ablateMain ps true chs.toList
  | "time" :: ws => timeMain ws
  | ["fsdbg", nm] => fsDbg nm
  | "refill" :: ps => refillMain ps
  | ["info", nm] => infoMain nm
  | ["census"] => do census; return 0
  | _ => IO.eprintln "usage: nockvm-d5red seq | tamper | ablate"; return 2
