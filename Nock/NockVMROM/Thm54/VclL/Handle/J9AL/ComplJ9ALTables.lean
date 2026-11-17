/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALTables.lean

  **The cell table and the atom table at the J-9 AL overlay `DL`.**
  * `cellOK_L`: `ComplJ9ATables.cellOK_runA` at `DL = j9alDataOf p Rg Rt prims hgen`.  The cell table's `mv`/`mh`
    are the overlay's bumped counts (`mvL_getD`, `mhL_getD`): the cell chip's acceptance reads them only through the
    poles (`famCellV`, `famCellH`, generic in the data) and the publics, so the proof is the J-9 A one verbatim.
  * `genHyp_mbL`: `GenHyp` at the bumped `(DL).mb = bumpAll (DA).mb aluBL`.  The ALU's validity reads are at the
    big atoms among `hd s`, `tl s`, `e` of a primitive `s11j` row, all leaves of two of the row's twelve handles
    (`s`, `e`), hence members of `bigs`: no hypothesis is added.
  * `atomOK_L`: `ComplJ9ATables.atomOK_runA` at `DL`, with `genHyp_mbL` for the bumped `mb`.
  * The interface abbrevs (all but `tbR`, which needs `AluSatRun`; does not use the ALU table).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALTables

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 0. The IFACE block (`tbR` omitted: it needs `AluSatRun`, reads no ALU table) -/

section Iface
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
include hpG h31 in
theorem hFL : DvdOK (DL) := ComplJ9ARun.dvdOK_of_A (ComplJ9ARun.dvdA_of_rows hpG _ h31)
abbrev psRun : List (ℕ × PrimOp) := ComplJ9ALData.primsC prims ((DA).calls.map Prod.fst)
abbrev vcRun : ℕ → ℕ := ComplJ9ALData.idxPOf (DA).cells prims
abbrev mRun : ℕ → ℕ := fun id =>
  ((ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t)).countP fun x => x.1 = id) + 1   -- mP = c+1
include hpG h31 in
abbrev famsJL := famsOf δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.cellsL_pos ..) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.acsL_pos ..)
include hpG h31 in
abbrev AVL := ComplJ9BBalF.avOf9 δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (avOf δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.acsL_pos ..))
include hpG h31 in
abbrev B8L := honestJ8Of δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.cellsL_pos ..) (ComplJ9ALData.acsL_pos ..)
  (AVL δ b Rt hgen prims hpG h31) (famsJL δ b Rt hgen prims hpG h31)
end Iface

/-! ## 1. The cell table at `DL` -/

section Cell
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

variable (hF : DvdOK (j9alDataOf p Rg Rt prims hgen)) (hC : 0 < (j9alDataOf p Rg Rt prims hgen).cells.length)
  (hA : 0 < (j9alDataOf p Rg Rt prims hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

/-- **The cell table at the overlay record** (`ComplJ9ATables.cellOK_runA` at `DL`: honest `mv`/`mh` are
`mvL_getD`/`mhL_getD`, read only through the poles `famCellV`/`famCellH` and the publics). -/
theorem cellOK_L (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hV : famCellV δ (DL) ∈ fams)
    (hH : famCellH δ b (DL) hC (orbJ8 _ hF) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (honestJ8Of δ b (DL) hF hC hA AV fams).Good χ) :
    let B := honestJ8Of δ b (DL) hF hC hA AV fams
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DL).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  obtain ⟨hz, hrows⟩ := famCellV_good δ (DL) χ (hin _ hV)
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (DL).cells.length)
    (le_two_pow_ht _ (by simp [sizesJ8]))
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC (orbJ8 _ hF) χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hin _ hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 4) (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC (orbJ8 _ hF) χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC (orbJ8 _ hF) χ)]

end Cell

/-! ## 2. `GenHyp` at the bumped atom validity counts -/

section GenL
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables (genHypA genHyp_mbXA acs_okA)

variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem leaf_hdN (c : Noun) (a : ℕ) (h : hdN' c = Noun.atom a) : a ∈ leavesOf c := by
  cases c with
  | atom b => simp [hdN'] at h; subst h; simp [leavesOf]
  | cell u w => simp [hdN'] at h; subst h; simp [leavesOf]

theorem leaf_tlN (c : Noun) (a : ℕ) (h : tlN' c = Noun.atom a) : a ∈ leavesOf c := by
  cases c with
  | atom b => simp [tlN'] at h; subst h; simp [leavesOf]
  | cell u w => simp [tlN'] at h; subst h; simp [leavesOf]

/-- A big atom among the ALU's validity reads (`hd s`, `tl s`, `e` of a primitive `s11j` row) is a big atom of the
run: it is a leaf of the handle `s` or `e` of that row (both among the row's twelve handles). -/
theorem aluB_big (n : Noun) (a : ℕ) (hn : n ∈ (ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t)).flatMap
      fun x => [hdN' x.2.1, tlN' x.2.1, x.2.2]) (hna : n = Noun.atom a) (hp : Nock.Atoms.p ≤ a) :
    a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs := by
  show a ∈ ComplJ8Data.bigsP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).roots (j8DataOf Nock.Atoms.p Rg Rt hgen).rows
  refine (ComplJ8Atom.mem_bigsP Nock.Atoms.p _ _ a).mpr ⟨?_, hp⟩
  obtain ⟨x, hx, hnx⟩ := List.mem_flatMap.mp hn
  unfold ComplJ9ALData.pcallsR at hx
  obtain ⟨row, hrow, hrx⟩ := List.mem_filterMap.mp hx
  have hrow' : row ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList := hrow
  have hxr : x.2.1 = row.s ∧ x.2.2 = row.e := by
    by_cases hc : row.st = .s11j ∧ atomV row.sf1 ∈ prims.map Prod.fst
    · rw [if_pos hc] at hrx
      cases hrx
      exact ⟨rfl, rfl⟩
    · rw [if_neg hc] at hrx; cases hrx
  obtain ⟨hs, he⟩ := hxr
  rw [hs, he] at hnx
  have hmem : ∀ y : Noun, y ∈ rowHandleNounsX row → a ∈ leavesOf y →
      a ∈ ((j8DataOf Nock.Atoms.p Rg Rt hgen).roots ++ (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList.flatMap rowHandleNounsX).flatMap leavesOf := by
    intro y hy ha
    exact List.mem_flatMap.mpr ⟨y, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow', hy⟩), ha⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnx
  rcases hnx with h1 | h1 | h1
  · exact hmem row.s (by simp [rowHandleNounsX]) (leaf_hdN _ _ (h1.symm.trans hna))
  · exact hmem row.s (by simp [rowHandleNounsX]) (leaf_tlN _ _ (h1.symm.trans hna))
  · exact hmem row.e (by simp [rowHandleNounsX]) (by rw [show row.e = Noun.atom a from h1.symm.trans hna]; simp [leavesOf])


/-- **`GenHyp` at the bumped `mb`** (no new hypothesis): the base clauses are `genHyp_mbXA`'s (at `(DA).mb = mbX DD
[s, f, r]`, `j9aDataOf_mb`), and a nonzero ALU bump sits at the root of a big atom of the run (`aluB_big`). -/
theorem genHyp_mbL (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).mb := by
  have hg := genHyp_mbXA Rg Rt hgen hN
  refine ⟨hg.big, hg.ops, hg.dup, fun j hj h0 => ?_, hN⟩
  have hj' : j < (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs.length := hj
  rw [ComplJ9ALData.mbL_getD Rt prims hgen j hj'] at h0
  by_cases h1 : (j9aDataOf Nock.Atoms.p Rg Rt hgen).mb.getD j 0 = 0
  · rw [h1, zero_add] at h0
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ (ComplJ9ALData.aluBL Nock.Atoms.p (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs
        (ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t))).filter (fun q => q.1 = j), q.2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, ne_eq, not_not] at hc
      apply h0
      unfold ComplJ8Data.sumAt
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hc q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    simp only [ComplJ9ALData.aluBL, List.mem_filterMap, Option.map_eq_some_iff] at hq
    obtain ⟨n, hn, i, hi, rfl⟩ := hq
    cases n with
    | cell u w => simp [bigIdOfP] at hi
    | atom a =>
      simp only [bigIdOfP] at hi
      split_ifs at hi with hlt
      cases hi
      exact ⟨a, aluB_big Rg Rt prims hgen _ a hn rfl (by omega), rfl⟩
  · exact hg.mb j hj h1

end GenL

section AtomL
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables (genHypA genHyp_mbXA acs_okA atomOK_mbA)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **The rows bound from `Rows31 DL`** (`ComplJ9ATables.rows_leA` at `DL`). -/
theorem rows_leL (h31 : Rows31 (j9alDataOf Nock.Atoms.p Rg Rt prims hgen)) :
    (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
  have h : (bfsForest [(j8DataOf Nock.Atoms.p Rg Rt hgen).t]).length ≤ 2 ^ 31 :=
    h31 _ (by unfold sizesJ8; exact List.mem_cons_self ..)
  rw [ComplJ8BigBound.data_rows hgen]
  simpa [ComplJ8Data.rowsOfT, j8DataOf] using h

/-- **The atom table at the overlay record** (`ComplJ9ATables.atomOK_runA` at `DL`; the bumped `mb` meets `GenHyp`
by `genHyp_mbL`, so no hypothesis beyond `hpG`, `Rows31 DL` is added). -/
theorem atomOK_L (hpG : p = Nock.Atoms.p)
    (hF : DvdOK (DL)) (hA : 0 < (DL).acs.length) (h31 : Rows31 (DL))
    (χ : Coins frameJ8 K)
    (gZ : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) (gV : ∀ e ∈ famAV δ (DL) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAH δ b (DL) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMB : ∀ e ∈ famMB δ b (DL) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b (DL) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMI : ∀ e ∈ famMI δ b (DL) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev) :
    let o := orbJ8 (DL) hF
    let P := pubsAOf δ b (DL) hA o χ
    let tr := HonestA8.atomTraceHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (DL) hA o χ P)
      (newBA (DL))
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies tr ∧
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing tr ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) := by
  intro o P tr
  subst hpG
  have hz := famAZ_good δ χ gZ
  have hv := famAV_good δ (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) χ gV
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ gH gMB gC gMI P
  have hmA9 : (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs.length ∈ sizesJ8 (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) := by
    simp [sizesJ8]
  have hN := rows_leL Rt prims hgen h31
  obtain ⟨hcell, hrank, htl⟩ := acs_okA Rg Rt hgen hN (h31 _ hmA9)
  obtain ⟨hinj, hadj⟩ := powN_ok o (le_two_pow_ht _ hmA9)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN o _) o (chalsAJ8Z δ χ) P (γV δ χ) (ρV δ χ)
    (zA δ χ) (fun _ => none) (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _)
    hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs.length,
      let y := (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs[(i : ℕ)]
      colAH δ b _ hA o χ P Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs
            (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ P i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  exact atomOK_mbA δ b Rg Rt hgen hA (powN o _) o (chalsAJ8Z δ χ) P
    (colAH δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ P)
    (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).mb (genHyp_mbL Rg Rt prims hgen hN) hinj hadj hcol hsat0
    hpMB hpC hpMI tMB tC tMI

end AtomL

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALTables
