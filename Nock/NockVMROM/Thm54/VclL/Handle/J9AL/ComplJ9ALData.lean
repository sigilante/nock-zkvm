/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALData.lean

  **The J-9 AL honest DATA as an overlay** on the
  J-9 A honest data `j9aDataOf` (the `j9DataOf` / `j9aDataOf` pattern `{ D with … }`). No
  existing statement is edited.  * **`j9alDataOf p Rg Rt prims hgen`** = `{ j9aDataOf p Rg Rt hgen with calls ids regs lay jrows mv mh mb }`:
    - `calls ids regs lay jrows` are J-ONLY: the primitive ids (`prims.map Prod.fst`) are filtered out of the run's
      calls (`jCallsP`), and the J rows / layout are rebuilt on the J calls exactly as `j8DataOf` builds them;
    - `mv` (cell validity) gets `+1` at `idxPOf id` (the cell-table index of `primC op`) per CALLED primitive (the
      verifier's claim-record pin `pinRecsP`, `AcceptsJ9AL.hsumC'`), on top of the base count over the J pins only;
    - `mh` (cell export) is J-9 A's `mhJP (mhCountsX9 …) jrows` at the J rows, `+1` per ALU export read (the hdr's
      `keyX` consume of the call subject `[a b]`, `aluXL`);
    - `mb` (atom validity) is J-9 A's, `+1` per ALU validity read (one per big operand / big result of a primitive
      call, the kind-2 slots under W-B: witnesses are lane rows and read nothing, `aluBL`).
  * Every other field (`t rows Rt jn idx rk roots cells bigs dupP acs H pd reads ws kr preads vs krV bases mx mxA
    mhA info`) is the base's by `rfl`, so every cell-side lemma of the base applies verbatim (`F_*` read-backs and
    the samples `cells_nodupL`, `hdlOKL`, `handle_noun_casesL`).
  * The split lemmas `jCallsP_sub`, `aCallsP_sub`, `sum_split` (every call goes to exactly one chip).
  * The J gates at the overlay (`jrows_gateL`, binder: the prim-aware `hRt` on non-primitive called ids only) and the
    layout (`jrows_preL`); the three multiplicity read-backs `mvL_getD`, `mhL_getD`, `mbL_getD`.

  **Disclosure (trivial-template caveat).** The base data still builds the cell table from ALL calls: `jn =
  jNounsP p Rt regs calls` (`ComplJ8Data.j8DataOf`) holds, for every primitive call, the compiled noun
  `compile p (Rt id)`, the call subject and the honest node values of `Rt id` on it.  The completeness theorem
  therefore runs at `rtP Rt prims` (`Rt` with every primitive id sent to the fixed trivial template `trivTpl`,
  arity 0, body `const 0`): the extra cells are ONE constant cell (`compile p trivTpl`) plus nouns already in the
  table (the subject) or atoms (`0`).  They carry no consumer beyond the cell table's own child counts, so they are
  harmless for every balance; they are not ALU data and nothing reads them as such.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT bumpAll bumpAll_getD bumpAll_size
  bigIdOfP sumAt mvFixP pinsOfP hJd mhJP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf mhCountsX9 basesA9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds jrows_gate jrows_pre)
open Nock.V1J8.Gen (callsOf idxOf hdN' tlN' atomV)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow layoutJ8 axPosB baseGatesJ envOf)
open Nock.Jet.Prim (PrimOp primC)

noncomputable section

/-! ## 1. The trivial template and the primitive-aware template table -/

/-- **The fixed trivial template** (arity 0, output `F`, body `const 0`): the template table's entry at every
primitive id (module docstring, the caveat). -/
def trivTpl : Tpl where
  k := 0
  ax := Fin.elim0
  inTy := Fin.elim0
  outTy := .F
  body := .const 0

/-- **`rtP Rt prims`**: `Rt` with every primitive id sent to `trivTpl`. -/
def rtP (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) : ℕ → Tpl := fun id =>
  if id ∈ prims.map Prod.fst then trivTpl else Rt id

theorem rtP_of_not_mem (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) {id : ℕ} (h : id ∉ prims.map Prod.fst) :
    rtP Rt prims id = Rt id := by simp [rtP, h]

theorem rtP_of_mem (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) {id : ℕ} (h : id ∈ prims.map Prod.fst) :
    rtP Rt prims id = trivTpl := by simp [rtP, h]

/-! ## 2. The call split -/

section Split

/-- The J calls: those whose id is not a primitive id. -/
def jCallsP (pids : List ℕ) (l : List (ℕ × Noun)) : List (ℕ × Noun) := l.filter fun c => c.1 ∉ pids

/-- The ALU calls: those whose id is a primitive id. -/
def aCallsP (pids : List ℕ) (l : List (ℕ × Noun)) : List (ℕ × Noun) := l.filter fun c => c.1 ∈ pids

theorem jCallsP_sub (pids : List ℕ) (l : List (ℕ × Noun)) : ∀ cl ∈ jCallsP pids l, cl ∈ l ∧ cl.1 ∉ pids := by
  intro cl h
  simpa [jCallsP] using h

theorem aCallsP_sub (pids : List ℕ) (l : List (ℕ × Noun)) : ∀ cl ∈ aCallsP pids l, cl ∈ l ∧ cl.1 ∈ pids := by
  intro cl h
  simpa [aCallsP] using h

theorem sum_filter_split {M : Type} [AddCommMonoid M] {α : Type} (g : α → M) (q : α → Bool) :
    ∀ l : List α, (l.map g).sum = ((l.filter fun c => !q c).map g).sum + ((l.filter q).map g).sum
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.sum_cons, sum_filter_split g q l]
    cases h : q x <;> simp [List.filter_cons, h] <;> abel

/-- **Every call goes to exactly one of the two chips**: a sum over the calls splits into the J sum and the ALU
sum. -/
theorem sum_split {M : Type} [AddCommMonoid M] (pids : List ℕ) (g : ℕ × Noun → M) (l : List (ℕ × Noun)) :
    (l.map g).sum = ((jCallsP pids l).map g).sum + ((aCallsP pids l).map g).sum := by
  have := sum_filter_split g (fun c => decide (c.1 ∈ pids)) l
  simpa [jCallsP, aCallsP] using this

/-- The split is a partition of the call list up to order: the lengths add up. -/
theorem length_split (pids : List ℕ) (l : List (ℕ × Noun)) :
    l.length = (jCallsP pids l).length + (aCallsP pids l).length := by
  have := sum_split pids (fun _ => (1 : ℕ)) l
  simpa using this

end Split

/-! ## 3. The ALU's call records -/

section Recs

/-- The primitive op of an id (the first `(id, op)` of `prims`; `add` off the list, never read there). -/
def opOf (prims : List (ℕ × PrimOp)) (id : ℕ) : PrimOp :=
  ((prims.find? fun q => q.1 = id).map Prod.snd).getD .add

theorem opOf_of_mem {prims : List (ℕ × PrimOp)} (hnd : (prims.map Prod.fst).Nodup) {q : ℕ × PrimOp}
    (hq : q ∈ prims) : opOf prims q.1 = q.2 := by
  induction prims with
  | nil => exact absurd hq List.not_mem_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hq with rfl | hq'
    · simp [opOf, List.find?_cons]
    · have hne : a.1 ≠ q.1 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hq')
      have := ih hnd.2 hq'
      simpa [opOf, List.find?_cons, hne] using this

/-- **The primitive calls with their results**: `(id, subject, result)` per `s11j` row whose id is a primitive
id (the ALU blocks, one per call). -/
def pcallsR (pids : List ℕ) (rows : Array RowNX) : List (ℕ × Noun × Noun) :=
  rows.toList.filterMap fun r =>
    if r.st = .s11j ∧ atomV r.sf1 ∈ pids then some (atomV r.sf1, r.s, r.e) else none

/-- Forgetting the results gives the ALU calls. -/
theorem pcallsR_fst (pids : List ℕ) (rows : Array RowNX) :
    (pcallsR pids rows).map (fun x => (x.1, x.2.1)) = aCallsP pids (callsOf rows) := by
  unfold pcallsR aCallsP callsOf
  generalize rows.toList = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    by_cases hs : r.st = .s11j
    · by_cases hi : atomV r.sf1 ∈ pids
      · simp [List.filterMap_cons, hs, hi, ih]
      · simp [List.filterMap_cons, hs, hi, ih]
    · simp [List.filterMap_cons, hs, ih]

/-- **The ALU's export reads** (`mh`): one per primitive call, the hdr's `keyX` consume of the subject cell
`[a b]` (an atom subject reads nothing; the honest run has none, a primitive has no result off a cell). -/
def aluXL (cs : List Noun) (pc : List (ℕ × Noun × Noun)) : List (ℕ × ℕ) :=
  pc.filterMap fun x => match x.2.1 with
    | .cell _ _ => some (idxOf cs x.2.1, 1)
    | .atom _ => none

/-- **The ALU's validity reads** (`mb`): one per kind-2 slot, i.e. per big operand `a = hd s`, `b = tl s` and per
big result (witnesses W-B read nothing). -/
def aluBL (p : ℕ) (acs : List Noun) (pc : List (ℕ × Noun × Noun)) : List (ℕ × ℕ) :=
  (pc.flatMap fun x => [hdN' x.2.1, tlN' x.2.1, x.2.2]).filterMap fun n => (bigIdOfP p acs n).map fun i => (i, 1)

/-- **The called primitives** (`(id, op)` of `prims` whose id is called), the honest `Pb.prims`. -/
def primsC (prims : List (ℕ × PrimOp)) (ids : List ℕ) : List (ℕ × PrimOp) :=
  prims.filter fun q => q.1 ∈ ids

/-- **The cell-table index of a primitive's formula noun** (the honest `Pb.idxP`). -/
def idxPOf (cs : List Noun) (prims : List (ℕ × PrimOp)) (id : ℕ) : ℕ := idxOf cs (primC (opOf prims id))

/-- **The public rank limbs of a primitive's formula noun** (the honest `Pb.rkP`). -/
def rkPOf (prims : List (ℕ × PrimOp)) (id : ℕ) : ℕ × ℕ := AcceptsJ8P.rkC (primC (opOf prims id))

/-- **The primitive claim-record pins** (`mv`): one per called primitive, at `idxPOf`. -/
def primPinL (cs : List Noun) (prims : List (ℕ × PrimOp)) (ids : List ℕ) : List (ℕ × ℕ) :=
  (primsC prims ids).map fun q => (idxPOf cs prims q.1, 1)

end Recs

/-! ## 4. The overlay -/

section Def
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- J-9 A's export count before the J reads (`j9aDataOf`'s `mh` argument of `mhJP`). -/
def mh0A : Array ℕ :=
  let D := j9aDataOf p Rg Rt hgen
  mhCountsX9 p D.cells
    (basesA9 p D.H D.pd (ComplJ9AChains.idOf9 p D.acs.length D.H (ComplJ9AData.fieldAx9 p (rowsOfT9 t)))
      (bfsForest [ComplJ9AGen.genX9T t])) D.ws

/-- **The J-9 AL honest data** (route F′): the J-9 A data with the J-layer fields recomputed on the J calls and
the three multiplicities carrying the ALU's consumers (module docstring). -/
def j9alDataOf : J8Data p Rg fuel s f r :=
  let D := j9aDataOf p Rg Rt hgen
  let pids := prims.map Prod.fst
  let callsJ := jCallsP pids D.calls
  let regsJ := (callsJ.map Prod.fst).dedup
  let jrowsJ := mvFixP p (Nock.Jet.ChipJ8.honestJ8G (hJd p D.cells D.acs) D.Rt regsJ callsJ) (pinsOfP p regsJ D.idx)
  let pc := pcallsR pids D.rows
  { D with
    calls := callsJ
    ids := callsJ.map Prod.fst
    regs := regsJ
    lay := layoutJ8 D.Rt regsJ (callsJ.map Prod.fst)
    jrows := jrowsJ
    mv := bumpAll (Nock.V1J8.Gen.mvPins (Nock.V1J8.Gen.mvCounts D.cells ⟨s, f, r⟩) regsJ D.idx)
      (primPinL D.cells prims (D.calls.map Prod.fst))
    mh := bumpAll (mhJP p (mh0A p Rg Rt hgen) jrowsJ) (aluXL D.cells pc)
    mb := bumpAll D.mb (aluBL p D.acs pc) }

end Def

/-! ## 5. Read-backs -/

section Back
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "PIDS" => prims.map Prod.fst

/-! ### Unchanged fields: the base's, by `rfl` -/
theorem F_t : (DL).t = t := rfl
theorem F_rows : (DL).rows = (DA).rows := rfl
theorem F_Rt : (DL).Rt = Rt := rfl
theorem F_jn : (DL).jn = (DA).jn := rfl
theorem F_idx : (DL).idx = (DA).idx := rfl
theorem F_rk : (DL).rk = (DA).rk := rfl
theorem F_roots : (DL).roots = (DA).roots := rfl
theorem F_cells : (DL).cells = (DA).cells := rfl
theorem F_bigs : (DL).bigs = (DA).bigs := rfl
theorem F_dupP : (DL).dupP = (DA).dupP := rfl
theorem F_acs : (DL).acs = (DA).acs := rfl
theorem F_H : (DL).H = (DA).H := rfl
theorem F_pd : (DL).pd = (DA).pd := rfl
theorem F_reads : (DL).reads = (DA).reads := rfl
theorem F_ws : (DL).ws = (DA).ws := rfl
theorem F_kr : (DL).kr = (DA).kr := rfl
theorem F_preads : (DL).preads = (DA).preads := rfl
theorem F_vs : (DL).vs = (DA).vs := rfl
theorem F_krV : (DL).krV = (DA).krV := rfl
theorem F_bases : (DL).bases = (DA).bases := rfl
theorem F_mx : (DL).mx = (DA).mx := rfl
theorem F_mxA : (DL).mxA = (DA).mxA := rfl
theorem F_mhA : (DL).mhA = (DA).mhA := rfl
theorem F_info : (DL).info = (DA).info := rfl

/-! ### Changed fields -/
theorem F_calls : (DL).calls = jCallsP (PIDS) (callsOf (rowsOfT t)) := rfl
theorem F_ids : (DL).ids = (DL).calls.map Prod.fst := rfl
theorem F_regs : (DL).regs = ((DL).calls.map Prod.fst).dedup := rfl
theorem F_lay : (DL).lay = layoutJ8 Rt (DL).regs (DL).ids := rfl
theorem F_jrows : (DL).jrows = mvFixP p (Nock.Jet.ChipJ8.honestJ8G (hJd p (DL).cells (DL).acs) (DL).Rt (DL).regs
    (DL).calls) (pinsOfP p (DL).regs (DL).idx) := rfl
theorem F_mv : (DL).mv = bumpAll (Nock.V1J8.Gen.mvPins (Nock.V1J8.Gen.mvCounts (DA).cells ⟨s, f, r⟩) (DL).regs (DA).idx)
    (primPinL (DA).cells prims ((DA).calls.map Prod.fst)) := rfl
theorem F_mh : (DL).mh = bumpAll (mhJP p (mh0A p Rg Rt hgen) (DL).jrows)
    (aluXL (DA).cells (pcallsR (PIDS) (rowsOfT t))) := rfl
theorem F_mb : (DL).mb = bumpAll (DA).mb (aluBL p (DA).acs (pcallsR (PIDS) (rowsOfT t))) := rfl

/-- The base's calls are the run's calls. -/
theorem DA_calls : (DA).calls = callsOf (rowsOfT t) := rfl

/-- J-9 A's `mh` is `mhJP` of `mh0A` at the base J rows. -/
theorem DA_mh : (DA).mh = mhJP p (mh0A p Rg Rt hgen) (DA).jrows := rfl

/-- With no primitive the overlay is the J-9 A data on every J field (the calls are all J calls). -/
theorem jCallsP_nil (l : List (ℕ × Noun)) : jCallsP [] l = l := by simp [jCallsP]

/-! ### Verbatim reuse: cell-side lemmas are one-line `exact`s -/

theorem cells_nodupL : (DL).cells.Nodup := ComplJ8Data.j8_cells_nodup p Rg Rt hgen

theorem hdlOKL : HonestCompX.HdlOK (ringChar (ZMod p)) (DL).H := ComplJ8Data.hdlOK p Rg Rt hgen

theorem handle_noun_casesL {row : RowNX} (hrow : row ∈ (DL).rows.toList) {n : Noun}
    (hn : n ∈ handleNounsX row) :
    ((∃ a b, n = .cell a b) ∧ n ∈ (DL).cells) ∨ (∃ v, n = .atom v ∧ v < p) ∨ (∃ v, n = .atom v ∧ p ≤ v) :=
  ComplJ8Data.handle_noun_cases p Rg Rt hgen hrow hn

theorem cellsL_pos [Fact (ringChar (ZMod p)).Prime] : 0 < (DL).cells.length :=
  ComplJ9ADataRec.cellsA_pos Rt hgen

theorem acsL_pos [Fact (ringChar (ZMod p)).Prime] : 0 < (DL).acs.length := ComplJ9ADataRec.acsA_pos Rt hgen

/-! ### The J gates at the overlay -/

/-- The layout of the overlay's J rows (`jrows_pre`, generic). -/
theorem jrows_preL : (DL).jrows.map CRow.pre = layoutJ8 Rt (DL).regs (DL).ids :=
  jrows_pre _ rfl rfl

/-- **The J calls of the overlay have a well-typed template with a result** (the prim-aware binder: `hRt` on the
non-primitive called ids only). -/
theorem callsL_of_hRt
    (hRt : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ cl ∈ (DL).calls, (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r := by
  intro cl hcl
  have hcl0 : cl ∈ jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t)) := hcl
  obtain ⟨hcl, hns⟩ := jCallsP_sub _ _ cl hcl0
  unfold callsOf at hcl
  obtain ⟨row, hrow, hrc⟩ := List.mem_filterMap.1 hcl
  have hrow' : ∃ u ∈ bfsForest [t], rowOfSkelX u.label = row := by
    simpa [rowsOfT] using hrow
  obtain ⟨u, hu, rfl⟩ := hrow'
  obtain ⟨c, hc, huc⟩ := (mem_bfsForest [t] u).1 hu
  have hct : c = t := by simpa using hc
  subst hct
  have hst : u.label.state = .s11j := by
    rw [← ComplJ8Jet.rowOfSkelX_st]
    by_contra hne
    simp [hne] at hrc
  obtain ⟨id, j, r', hRj, hftth, hsem⟩ := ComplJ8Jet.s11j_node hgen huc hst
  have hcalled : id ∈ CalledIds _ := ⟨u, huc, by rw [ComplJ8Jet.rowOfSkelX_st]; exact hst, hftth⟩
  have hcl' : cl = (id, u.label.subject) := by
    rw [if_pos (by rw [ComplJ8Jet.rowOfSkelX_st]; exact hst)] at hrc
    rw [← Option.some.inj hrc, hftth, ComplJ8Jet.rowOfSkelX_s]
    rfl
  subst hcl'
  obtain ⟨hR2, -, hwt⟩ := hRt id hcalled hns
  rw [hRj] at hR2
  have hj : j = ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ := Option.some.inj hR2
  refine ⟨hwt, r', ?_⟩
  subst hj
  exact hsem

/-- **The J chip's base gates at the overlay** (`jrows_gate`, generic, + the filtered `hcalls`). -/
theorem jrows_gateL (hp : 0 < p)
    (hRt : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ (DL).jrows, ∀ g ∈ (baseGatesJ : List (Nock.NockVMROM.Thm54.CoordinateCompiler.CoeffExpr (ZMod p))),
      g.eval (envOf x) = 0 :=
  jrows_gate _ hp rfl (callsL_of_hRt Rt prims hgen hRt)

/-! ### The multiplicities: base count + the ALU's records -/

theorem mvL_getD (j : ℕ)
    (hj : j < (Nock.V1J8.Gen.mvPins (Nock.V1J8.Gen.mvCounts (DA).cells ⟨s, f, r⟩) (DL).regs (DA).idx).size) :
    (DL).mv.getD j 0 = (Nock.V1J8.Gen.mvPins (Nock.V1J8.Gen.mvCounts (DA).cells ⟨s, f, r⟩) (DL).regs (DA).idx).getD j 0
      + sumAt (primPinL (DA).cells prims ((DA).calls.map Prod.fst)) j :=
  bumpAll_getD _ _ _ hj

theorem mhL_getD (j : ℕ) (hj : j < (mhJP p (mh0A p Rg Rt hgen) (DL).jrows).size) :
    (DL).mh.getD j 0 = (mhJP p (mh0A p Rg Rt hgen) (DL).jrows).getD j 0 +
      sumAt (aluXL (DA).cells (pcallsR (PIDS) (rowsOfT t))) j :=
  bumpAll_getD _ _ _ hj

theorem mbL_size : (DL).mb.size = (DL).acs.length := by
  rw [F_mb, bumpAll_size]
  exact (ComplJ9BAtom.mbX_size _ _).trans (ComplJ9BAtom.mb_size p Rg Rt hgen)

theorem mbL_getD (j : ℕ) (hj : j < (DL).acs.length) :
    (DL).mb.getD j 0 = (DA).mb.getD j 0 + sumAt (aluBL p (DA).acs (pcallsR (PIDS) (rowsOfT t))) j :=
  bumpAll_getD _ _ _ (by
    rw [show (DA).mb.size = (DL).acs.length from
      (ComplJ9BAtom.mbX_size _ _).trans (ComplJ9BAtom.mb_size p Rg Rt hgen)]
    exact hj)

end Back

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
#print axioms opOf_of_mem
#print axioms sum_split
#print axioms length_split
#print axioms pcallsR_fst
#print axioms cells_nodupL
#print axioms handle_noun_casesL
#print axioms jrows_preL
#print axioms jrows_gateL
#print axioms mvL_getD
#print axioms mhL_getD
#print axioms mbL_getD
end Axioms
