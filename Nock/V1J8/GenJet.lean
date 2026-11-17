/-
  Nock/V1J8/GenJet.lean

  **J present in the general J-8 tracegen.**  `genJ8` (B4757, the no-jet generator, kernel-checked against the
  example in B4758) is untouched; `genJ8J` is the generator with jets.

  `genJ8J Rt regs fuel s f χe` runs `genX` at the registry `regOf Rt regs` (id `n ∈ regs` ↦ the compiled template
  `Rt n`; `RegOK` holds for it by construction, up to `WellTyped`), then, beside `genJ8`'s compute / cell / walk /
  atom tables:
  * **calls**: every `s11j` row of the run (BFS order) is a call `(id, subject)` (`id` = the row's `sf1` atom, the clue's value);
    `ids` = the calls' ids;
  * **J rows** (HJ2's builder with HJ's single-evaluation block `blockW'`, handles from the cell list): one `reg` row per
    registered id, one block per call (`honestRows` values computed once); **the `mv` fix** (HJ2 `rowsPin`): each
    provider's `mv` = its in-chip consumers + the verifier's registry pins of its key (`tlF (pinKey id idx)`);
  * **J columns** (71, `ChipJ8THonestRAP.colJ`): layout `jetPre`, witness `colOf`, then the seven `𝕂′` columns
    `sT ents0T, sT ents1T, sT ents2T, sT ents3, sX, accT, accX` at the J coins (= the handle coins `(γH, ρH)`,
    `chalsJJ8E`), `accT` / `accX` INCLUSIVE prefix sums of `termJ` / `sX`; publics `pubsJ 0/1` = `Σ termJ`,
    `pubsJ 2/3` = `Σ sX`;
  * **registry publics**: `lay = layoutJ8 Rt regs ids`, `idx id` = the cell serial of `compile (Rt id)`,
    `rk id = rkC (compile (Rt id))`, `g = |regs|`;
  * **Scope:** no big atom in any compute or J noun (`none` otherwise).
-/
import Nock.V1J8.GenJ8
import Nock.Jet.ChipJ8Toy
import Std.Data.HashMap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow WRow Kd keysOf ents3 entsX callPre regPre layoutJ8 colOf preCol)
open Nock.Jet.ChipJ8 (ents0T ents1T ents2T)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

/-! ## 1. The registry and the calls -/

/-- **The registry of a template table**: id `n ∈ regs` ↦ `⟨(Rt n).toTemplate p, compile p (Rt n)⟩`. -/
def regOf (Rt : ℕ → Tpl) (regs : List ℕ) : Nock.Jet.Registry := fun n =>
  if n ∈ regs then some ⟨(Rt n).toTemplate P, compile P (Rt n)⟩ else none

/-- The calls of a run: every `s11j` row, `(id, subject)`, in row order. -/
def callsOf (rows : Array RowNX) : List (ℕ × Noun) :=
  rows.toList.filterMap fun r => if r.st = .s11j then some (atomV r.sf1, r.s) else none

/-- The honest node values of a call (J-3a `honestRows`, computed once). -/
def callVals (Rt : ℕ → Tpl) (c : ℕ) (cl : ℕ × Noun) : List Noun :=
  (Nock.Jet.Interp.honestRows P (Rt cl.1) cl.2 c).map Nock.Jet.Interp.JRow.val

/-- The J chip's nouns: the registered compiled formulas, each call's subject and honest node values. -/
def jNouns (Rt : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) : List Noun :=
  regs.map (fun i => compile P (Rt i)) ++ (calls.zipIdx.flatMap fun (cl, c) => cl.2 :: callVals Rt c cl)

/-! ## 2. The J rows -/

/-- The honest block of call `c` (template `Rt i`, subject `s`): HJ's `blockW'` (values computed once) over the
cell list `cs` (handles `ChipJ8.hOf cs`, `= hdl cs` on the table's nouns). -/
def jBlock (cs : List Noun) (Rt : ℕ → Tpl) (c i : ℕ) (s : Noun) : List (CRow (ZMod P)) :=
  let T := Rt i
  let N := (Nock.Jet.Interp.nodesOf T).length
  let vals : Array Noun := ((Nock.Jet.Interp.honestRows P T s c).map Nock.Jet.Interp.JRow.val).toArray
  let lk : ℕ → Noun := fun n => vals.getD n Nock.Jet.Interp.z0
  ⟨callPre Rt c i, Nock.Jet.ChipJ8.mkW 1 1 0 0 0
      (Nock.Jet.ChipJ8.hOf cs (compile P T)) (Nock.Jet.ChipJ8.hOf cs s) (Nock.Jet.ChipJ8.hOf cs (lk 0))⟩ ::
    Nock.Jet.ChipJ8.nodesW cs c N lk s (N + 1) (Nock.Jet.Interp.nodesOf T)

/-- The J rows before the `mv` fix: one `reg` row per registered id, one block per call. -/
def jRowsRaw (cs : List Noun) (Rt : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) : List (CRow (ZMod P)) :=
  regs.map (fun i => (⟨regPre i, Nock.Jet.ChipJ8.mkW 0 1 0 0 0
    (Nock.Jet.ChipJ8.hOf cs (compile P (Rt i))) (0, 0) (0, 0)⟩ : CRow (ZMod P))) ++
  (calls.zipIdx.flatMap fun (cl, c) => jBlock cs Rt c cl.1 cl.2)

/-- The verifier's registry pins (`tlF (pinKey id (idx id))`, the tag-last `TAG_reg` key). -/
def pinsOf (regs : List ℕ) (idx : ℕ → ℕ) : List (List (ZMod P)) :=
  regs.map fun id => tlF (Nock.Jet.PinJ8.pinKey (F := ZMod P) id (idx id))

/-- **The `mv` fix** (HJ2 `rowsPin`, by hash map): a provider's `mv` = its in-chip consumers + the pins of its key. -/
def mvFix (rows : List (CRow (ZMod P))) (pins : List (List (ZMod P))) : List (CRow (ZMod P)) :=
  let add := fun (m : Std.HashMap (List ℕ) ℕ) (k : List (ZMod P)) =>
    let k := k.map ZMod.val; m.insert k (m.getD k 0 + 1)
  let cons : Std.HashMap (List ℕ) ℕ := pins.foldl add (rows.foldl (fun m r => (consKT r).foldl add m) {})
  rows.map fun r => match provKT r with
    | [k] => { r with w := { r.w with mv := ((cons.getD (k.map ZMod.val) 0 : ℕ) : ZMod P) } }
    | _ => { r with w := { r.w with mv := 0 } }

/-! ## 3. The J columns -/

/-- `x ∈ 𝔽` as a `𝕂′` scalar. -/
def fq (x : ZMod P) : K6 := g6 (Gold.ofZ x)

/-- `den⁻¹` of a key of length `m` at the J coins (`(γH, ρH)`: `coinsJ` = `coinsJX` at `chalsJJ8E`). -/
def dKey (χe : CoinsE) (m : ℕ) (κ : List (ZMod P)) : K6 :=
  (compressE (γHE χe) (ρHE χe) (fun c : Fin m => fq (κ.getD c 0)))⁻¹

/-- A tagged slot's honest inverse `sT es r`. -/
def sTE (χe : CoinsE) (es : List (Kd × List Nock.Jet.ChipJ8.KE)) (r : CRow (ZMod P)) : K6 :=
  ((keysOf es r).map (dKey χe 8)).foldr (· + ·) 0

/-- The export slot's honest inverse `sX r`. -/
def sXE (χe : CoinsE) (r : CRow (ZMod P)) : K6 := ((keysOf entsX r).map (dKey χe 5)).foldr (· + ·) 0

/-- The tagged accumulator's row term `termJ r`. -/
def termE (χe : CoinsE) (r : CRow (ZMod P)) : K6 :=
  sTE χe ents0T r + sTE χe ents1T r - fq r.w.mv * sTE χe ents2T r - fq r.w.m * sTE χe ents3 r

/-- The seven `𝕂′` columns of a row (`inv0 inv1 inv2 inv3 invX accT accX`). -/
def qvE (χe : CoinsE) (r : CRow (ZMod P)) (aT aX : K6) : ℕ → K6
  | 0 => sTE χe ents0T r | 1 => sTE χe ents1T r | 2 => sTE χe ents2T r | 3 => sTE χe ents3 r
  | 4 => sXE χe r | 5 => aT | 6 => aX | _ => 0

/-- **Column `c` of J row `i` of `n`** (`ChipJ8THonestRAP.colJ`). -/
def jColD (χe : CoinsE) (n i : ℕ) (r : CRow (ZMod P)) (aT aX : K6) (c : ℕ) : ZMod P :=
  if c < 18 then (if c = 11 then flag (i == 0) else if c = 12 then flag (i + 1 == n) else preCol r.pre c)
  else if c < 29 then colOf r c
  else
    let ρ := (c - 29) / 3
    let q := qvE χe r aT aX (ρ / 2)
    limbZ (if ρ % 2 = 0 then q.re else q.im) ((c - 29) % 3)

/-- **The J table** (71 columns per row) and its four publics. -/
def jGen (χe : CoinsE) (rows : List (CRow (ZMod P))) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let n := rows.length
  let aTs := scanK6 (rows.map (termE χe))
  let aXs := scanK6 (rows.map (sXE χe))
  let tbl := (rows.zipIdx).map fun (r, i) =>
    Array.ofFn (n := 71) fun c => jColD χe n i r (aTs.getD i 0) (aXs.getD i 0) c
  let tT := lastK6 aTs
  let tX := lastK6 aXs
  (tbl.toArray, fun j => if j = 0 then tT.re else if j = 1 then tT.im else if j = 2 then tX.re
    else if j = 3 then tX.im else 0)

/-! ## 4. The multiplicity additions -/

def mvPins (mv : Array ℕ) (regs : List ℕ) (idx : ℕ → ℕ) : Array ℕ := regs.foldl (fun a id => bump a (idx id) 1) mv

/-- `mh` + one per J export read (`entsX` key `(vN, …)`: the serial `vN`). -/
def mhJ (mh : Array ℕ) (rows : List (CRow (ZMod P))) : Array ℕ :=
  rows.foldl (fun a r => (keysOf entsX r).foldl (fun a κ => bump a (κ.headD 0).val 1) a) mh

/-- Every atom of a list of nouns is small. -/
def smallNouns (ns : List Noun) : Bool := (ns.flatMap leavesOf).all fun a => decide (a < P)

/-! ## 5. The generator -/

/-- **The J-8 tracegen with jets.** -/
def genJ8J (Rt : ℕ → Tpl) (regs : List ℕ) (fuel : ℕ) (s f : Noun) (χe : CoinsE) : Option InJ8 :=
  match runX (regOf Rt regs) fuel s f with
  | none => none
  | some Rn =>
    let calls := callsOf Rn.rows
    let jn := jNouns Rt regs calls
    if !(smallAtoms Rn.rows && smallNouns jn) then none else
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let cs := cellsOfRoots (rootsOf c Rn.rows ++ jn)
    let H := hdl cs
    let idx : ℕ → ℕ := fun id => idxOf cs (compile P (Rt id))
    let ids := calls.map Prod.fst
    let layL := layoutJ8 Rt regs ids
    let jr := mvFix (jRowsRaw cs Rt regs calls) (pinsOf regs idx)
    let jg := jGen χe jr
    let comp := compGen c H Rn χe
    let wg := walkGen (cs.headD (.atom 0)) (pathReads Rn.rows)
    let ws := wg.1
    let kr := wg.2
    let mv := mvPins (mvCounts cs c) regs idx
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := mhJ (mhCounts cs comp.bases ws) jr
    let k := coOf χe
    let cg := cellGen k (yE χe) cs mv mx mx1 mh
    let wr := walkGenRows k (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) cs ws kr
    let m := max (max comp.rows.size (max cg.1.size wr.1.size)) layL.length
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cg.2, pubsW := wr.2,
               pubsJ := jg.2, pubsA := fun _ => 0, pubsV := fun _ => 0 }
        χ := χe
        r := budget m
        g := regs.length
        X := chipOf comp.rows
        C := chipOf cg.1
        W := chipOf wr.1
        J := ⟨hOf layL.length, layL.length, ωOf (hOf layL.length), colsOf jg.1 layL.length⟩
        A := ⟨1, 1, Example.ω6g, Atom.cols (coOfA χe) (zE χe)⟩
        V := ⟨1, 1, Example.ω6g, fun _ _ => 0⟩
        kroots := kr
        krootsV := 0
        lay := layL.get
        Rt := Rt
        regs := regs
        ids := ids
        idx := idx
        rk := fun id => Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.rkC (compile P (Rt id)) }

/-- **J tampers** (each must be rejected): the jet result, the pins, the J publics, the `mv` fix. -/
def jTampersOf (I : InJ8) : List (String × InJ8) :=
  let callRow := I.regs.length
  let lastAdd : ℕ := (((List.finRange I.J.n).filter fun i => (I.lay i).kd == .add).getLast?.map (·.val)).getD 0
  let bumpJ := fun (j : ℕ) => { I.M with pubsJ := fun j' => if j' = j then I.M.pubsJ j + 1 else I.M.pubsJ j' }
  [("jet result: the last J add row's value + 1", { I with J := bumpCol I.J 20 lastAdd }),
   ("jet output handle on the call row (vR + 1)", { I with J := bumpCol I.J 28 callRow }),
   ("registry pin: the pinned formula's serial idx + 1", { I with idx := fun id => I.idx id + 1 }),
   ("registry pin: the pinned rank lo + 1", { I with rk := fun id => ((I.rk id).1, (I.rk id).2 + 1) }),
   ("J terminal public pubsJ 0", { I with M := bumpJ 0 }),
   ("J export public pubsJ 2", { I with M := bumpJ 2 }),
   ("mv fix undone on the reg row (mv - 1)", { I with J := ⟨I.J.h, I.J.n, I.J.ω,
      fun c' i' => if c' = 19 ∧ (i' : ℕ) = 0 then I.J.cols c' i' - 1 else I.J.cols c' i'⟩ })]

end Nock.V1J8.Gen
