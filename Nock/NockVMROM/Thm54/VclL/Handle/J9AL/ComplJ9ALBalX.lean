/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalX.lean

  **J-9 AL completeness, part 1: the export balance `hGx_L`.**
  * §0 the interface abbrevs, plus
    `tbR` and the three ALU terminals `SV / SS / SX`.
  * §1 the J chip at `DL`: the honest J value rows do not read the call index (`honestRows_val_indep`), so the
    overlay's J calls are good (`goodL`); the J export key identity `hJ_L` and the J read range `jReadsL_range`
    (twins of `ComplJ8OfBalG.hJ_export` / `ComplJ8Data.jReads_range`, under the prim-aware `hRtJ`).
  * §2 the ALU export terminal: `SX n χ = wsum G (aluXL …)` (`SX_eq`), from the honest table (`tblP`): only the hdr
    rows carry `sH = 1`, and the hdr's `keyX (vS, kA, vA, kB, vB)` is the cell handle key of the call subject.
  * §3 the count identity at `DL` (`mhL_eq_cnt`), the serial range, and **`hGx_L`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalO
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARunFacts
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalX

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 0. The IFACE block -/

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
abbrev tbR (y : Quad (algebraMap (ZMod p) K δ)) :=
  AluSatRun.tblRun (p := p) δ Rt prims hgen (psRun (p := p) Rt hgen prims) (vcRun (p := p) Rt hgen prims) (mRun (t := t) prims) y
include hpG h31 in
abbrev famsJL := famsOf δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.cellsL_pos ..) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.acsL_pos ..)
include hpG h31 in
abbrev AVL := ComplJ9BBalF.avOf9 δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (avOf δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.acsL_pos ..))
include hpG h31 in
abbrev B8L := honestJ8Of δ b (DL) (hFL (Rt := Rt) (hgen := hgen) (prims := prims) (hpG := hpG) (h31 := h31)) (ComplJ9ALData.cellsL_pos ..) (ComplJ9ALData.acsL_pos ..)
  (AVL δ b Rt hgen prims hpG h31) (famsJL δ b Rt hgen prims hpG h31)
-- ALU terminals, n abstract (padding rows contribute 0):
abbrev SV (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tV δ (AluSZChipJ9.chalsALJ8 δ χ) (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)) i
abbrev SS (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tS δ (AluSZChipJ9.chalsALJ8 δ χ) (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)) i
abbrev SX (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tX δ (AluSZChipJ9.chalsALJ8 δ χ) (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)) i
end Iface

/-! ## 1. The J chip at `DL` -/

section JVals
open Nock.Jet.Interp (JRow exRows gRows gElemsR inRows honestRows)
open Nock.Jet.Autogen (Tpl Ex Ty)

theorem exRows_val (p : ℕ) {k : ℕ} (ax : Fin k → ℕ) (a : Fin k → Noun) (c c' : ℕ) :
    ∀ (e : Ex k) (b : ℕ), (exRows p ax a c b e).map JRow.val = (exRows p ax a c' b e).map JRow.val := by
  intro e
  induction e with
  | var i => intro b; rfl
  | const n => intro b; rfl
  | add e₁ e₂ ih₁ ih₂ => intro b; simp only [exRows, List.map_cons, List.map_append, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => intro b; simp only [exRows, List.map_cons, List.map_append, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => intro b; simp only [exRows, List.map_cons, List.map_append, ih₁, ih₂]
  | nth j e ih => intro b; simp only [exRows, List.map_cons, ih]

theorem gElemsR_val (g g' : ℕ → ℕ → Noun → List JRow)
    (hg : ∀ b r v, (g b r v).map JRow.val = (g' b r v).map JRow.val) (sz r : ℕ) (v : Noun) (c c' : ℕ) :
    ∀ (js : List ℕ) (b : ℕ), (gElemsR g sz r v c b js).map JRow.val = (gElemsR g' sz r v c' b js).map JRow.val
  | [], _ => rfl
  | j :: js, b => by
    simp only [gElemsR, List.map_cons, List.map_append, hg, gElemsR_val g g' hg sz r v c c' js]

theorem gRows_val (c c' : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun),
    (gRows c τ b r v).map JRow.val = (gRows c' τ b r v).map JRow.val
  | .F, _, _, _ => rfl
  | .N, _, _, _ => rfl
  | .L n τ, b, r, v => by
    simp only [gRows, List.map_cons]
    rw [gElemsR_val (gRows c τ) (gRows c' τ) (fun b r v => gRows_val c c' τ b r v)]

theorem inRows_val (T : Tpl) (a : Fin T.k → Noun) (c c' : ℕ) :
    ∀ (is : List (Fin T.k)) (b : ℕ), (inRows T a c b is).map JRow.val = (inRows T a c' b is).map JRow.val
  | [], _ => rfl
  | i :: is, b => by
    simp only [inRows, List.map_cons, List.map_append, gRows_val c c', inRows_val T a c c' is]

/-- **The honest J value rows do not read the call index.** -/
theorem honestRows_val_indep (p : ℕ) (T : Tpl) (s : Noun) (c c' : ℕ) :
    (honestRows p T s c).map JRow.val = (honestRows p T s c').map JRow.val := by
  simp only [honestRows, List.map_append, exRows_val p T.ax _ c c', inRows_val T _ c c']

theorem mem_zipIdx_of_mem {α : Type} {x : α} : ∀ {l : List α} {k : ℕ}, x ∈ l → ∃ i, (x, i) ∈ l.zipIdx k
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, k, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨k, by simp [List.zipIdx_cons]⟩
    · obtain ⟨i, hi⟩ := mem_zipIdx_of_mem (k := k + 1) h'
      exact ⟨i, by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hi⟩

end JVals

section JL
open Nock.Jet.ChipJ8 (CRow keysOf entsX honestJ8G)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC cellHx_eq fH_key honestJ8_kids mvFixP_mem')
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **The overlay's J calls are good** (their subjects and honest value rows are cells of the table or atoms). -/
theorem goodL : ∀ cl ∈ (DL).calls.zipIdx, ComplJ8Data.GoodN (DL).cells cl.1.2 ∧
    ∀ y ∈ (Nock.Jet.Interp.honestRows p (Rt cl.1.1) cl.1.2 cl.2).map Nock.Jet.Interp.JRow.val,
      ComplJ8Data.GoodN (DL).cells y := by
  intro cl hcl
  have hc1 : cl.1 ∈ (DL).calls := List.fst_mem_of_mem_zipIdx hcl
  have hcD : cl.1 ∈ (DD).calls := (ComplJ9ALData.jCallsP_sub _ _ cl.1 hc1).1
  obtain ⟨c, hc⟩ := mem_zipIdx_of_mem (k := 0) hcD
  have hjn := ComplJ8Data.jn_good p Rg Rt hgen
  refine ⟨hjn _ ?_, fun y hy => hjn _ ?_⟩
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(cl.1, c), hc, List.mem_cons_self⟩)
  · rw [honestRows_val_indep p (Rt cl.1.1) cl.1.2 cl.2 c] at hy
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(cl.1, c), hc, List.mem_cons_of_mem _ hy⟩)

/-- The overlay's J rows, unfolded. -/
theorem jrowsL_eq : (DL).jrows = ComplJ8Data.mvFixP p (honestJ8G (ComplJ8Data.hJd p (DL).cells (DL).acs) Rt (DL).regs
    (DL).calls) (ComplJ8Data.pinsOfP p (DL).regs (DL).idx) := rfl

/-- The base-gate fact `kN = 1` on export rows of the overlay's J chip (under the prim-aware `hRtJ`). -/
theorem hkNL
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ (DL).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1 :=
  fun x hx => (Nock.Jet.ChipJ8.gate_facts x
    (ComplJ9ALData.jrows_gateL Rt prims hgen (Fact.out : p.Prime).pos hRtJ x hx)).2.2.2

/-- **The overlay's J export reads are in range** (twin of `ComplJ8Data.jReads_range`). -/
theorem jReadsL_range (hlen : (DL).cells.length < p)
    (hkN : ∀ x ∈ (DL).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ q ∈ (DL).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (DL).cells.length := by
  intro q hq
  obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hkd, hhead⟩ := ComplJ8Data.keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  have hx' := hx
  rw [jrowsL_eq] at hx'
  obtain ⟨r0, hr0, hpre, hkN', hvN'⟩ := ComplJ8Data.mvFixP_mem _ _ x hx'
  have hread := ComplJ8Data.honestJ8_read (p := p) (hd := ComplJ8Data.hJd p (DL).cells (DL).acs)
    (ComplJ8Data.cells_closed _) Rt (DL).regs (DL).calls (goodL Rt hgen prims) r0 hr0 (by rw [← hpre]; exact hkd)
  obtain ⟨y, hy, hk, hv⟩ := hread
  simp only [hhead, hvN', hv]
  cases y with
  | atom v =>
    rw [hkN', hk] at hk1
    exact absurd hk1 (ComplJ8Data.hJd_atom_ne p _ _ v)
  | cell a b =>
    have hm := hy a b rfl
    have hlt : Nock.V1J8.Gen.idxOf (DL).cells (Noun.cell a b) < (DL).cells.length :=
      ComplJ8Data.idxOf_lt _ _ hm
    simp only [ComplJ8Data.hJd, ComplJ8Data.hdlP]
    rw [ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) hlt

set_option maxRecDepth 4000 in
/-- **The J export key identity at `DL`** (twin of `ComplJ8OfBalG.hJ_export`, under the prim-aware `hRtJ`). -/
theorem hJ_L
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (DL).cells.length)) (χ : Coins frameJ8 K)
    (hlen : (DL).cells.length < p)
    (hkN : ∀ x ∈ (DL).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ row ∈ (DL).jrows, ∀ κ ∈ keysOf entsX row,
      ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) =
        GC δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o χ (κ.headD 0).val := by
  have hcalls := ComplJ9ALData.callsL_of_hRt Rt prims hgen hRtJ
  intro x hx κ hκ
  have hx' := hx
  rw [jrowsL_eq] at hx'
  set D := DL with hD
  have hκ' : κ = [x.w.vN, x.w.kL, x.w.vL, x.w.kR, x.w.vR] := by
    simp only [Nock.Jet.ChipJ8.keysOf, Nock.Jet.ChipJ8.entsX, List.mem_map, List.mem_filter, List.mem_cons,
      List.not_mem_nil, or_false] at hκ
    obtain ⟨e, ⟨he, hk⟩, rfl⟩ := hκ
    rcases he with rfl | rfl | rfl <;>
      simp [Nock.Jet.ChipJ8.keyX, Nock.Jet.ChipJ8.KE.ev, Nock.Jet.ChipJ8.colOf, Nock.Jet.ChipJ8.Col.vN,
        Nock.Jet.ChipJ8.Col.kL, Nock.Jet.ChipJ8.Col.vL, Nock.Jet.ChipJ8.Col.kR, Nock.Jet.ChipJ8.Col.vR]
  obtain ⟨hkd, -⟩ := ComplJ8Data.keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  obtain ⟨r0, hr0, hpre, e1, e2, e3, e4, e5, e6⟩ := mvFixP_mem' _ _ x hx'
  have hcl : ComplJ8Data.ClP D.cells [] := ComplJ8Data.cells_closed _
  have hk := honestJ8_kids (p := p) (hd := ComplJ8Data.hJd p D.cells D.acs) hcl Rt D.regs D.calls (by
      intro cl hcl'
      have hc1 := List.fst_mem_of_mem_zipIdx hcl'
      have hc := hcalls cl.1 hc1
      obtain ⟨g1, g2⟩ := goodL Rt hgen prims cl hcl'
      exact ⟨g1, g2, hc.1, hc.2⟩)
    r0 hr0 (by rw [← hpre]; exact hkd)
  obtain ⟨y, hy, k1, k2, k3, k4, k5, k6⟩ := hk
  cases y with
  | atom v => rw [e1, k1] at hk1; exact absurd hk1 (ComplJ8Data.hJd_atom_ne p _ _ v)
  | cell yl yr =>
    have hm := hy yl yr rfl
    have hkids := hcl yl yr hm (by simp)
    have hxl : yl.isCell = true → yl ∈ D.cells := fun h => by
      cases yl with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.1 a b rfl
    have hxr : yr.isCell = true → yr ∈ D.cells := fun h => by
      cases yr with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.2 a b rfl
    have hjl := List.idxOf_lt_length_of_mem hm
    have hv : x.w.vN = ((D.cells.idxOf (Noun.cell yl yr) : ℕ) : ZMod p) := by
      rw [e2, k2]
      simp only [ComplJ8Data.hJd, ComplJ8Data.hdlP]
      rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
    have hval : (κ.headD 0).val = D.cells.idxOf (.cell yl yr) := by
      rw [hκ']
      simp only [List.headD_cons]
      rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
    rw [hval]
    simp only [GC]
    rw [cellHx_eq δ b D (ComplJ9ALData.cellsL_pos Rt prims hgen) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl)
      hxl hxr, hκ', fH_key]
    have hkl : x.w.kL = (((D.H yl).1 : ℕ) : ZMod p) ∧ x.w.vL = (((D.H yl).2 : ℕ) : ZMod p) ∧
        x.w.kR = (((D.H yr).1 : ℕ) : ZMod p) ∧ x.w.vR = (((D.H yr).2 : ℕ) : ZMod p) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e3, k3]; rfl
      · rw [e4, k4]; rfl
      · rw [e5, k5]; rfl
      · rw [e6, k6]; rfl
    rw [hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]

end JL

/-! ## 2. The ALU export terminal -/

section TableSums
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **A row-local sum over `n ≥ |tb|` rows is the list sum** (the padding row contributes `0`). -/
theorem sum_rowAt {n : ℕ} (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))
    (G : BRow F × QRow (Quad (algebraMap F K δ)) → Quad (algebraMap F K δ))
    (h0 : G (padRow, QRow.zero) = 0) (hlen : tb.length ≤ n) :
    ∑ i : Fin n, G (rowAt δ tb i) = (tb.map G).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun i => G (rowAt δ tb i)) n]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlen
  rw [Finset.sum_range_add, ← ComplJ8OfBal.sum_range_getD' (padRow, QRow.zero) G tb]
  have hz : ∑ x ∈ Finset.range m, G (rowAt δ tb (tb.length + x)) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      rw [show rowAt δ tb (tb.length + x) = (padRow, QRow.zero) from
        List.getD_eq_default _ _ (by omega)]
      exact h0
  rw [hz, add_zero]
  rfl

theorem sum_map_flatMap {α β M : Type} [AddCommMonoid M] (f : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap f g l]

/-- The export term of a row, as a function of the row. -/
def GX (chals : ℕ → K) (x : BRow F × QRow (Quad (algebraMap F K δ))) : Quad (algebraMap F K δ) :=
  liftQ δ x.1.sH * ((HQ.denKeyQ δ (AluSZChipJ9.keyXE : List (CoeffExpr F))).ev δ
    ⟨kvec δ x.2, fun _ => 0, chals, fun _ => 0⟩ (envB x.1.col (fun _ => 0)))⁻¹

theorem tX_eq {n : ℕ} (chals : ℕ → K) (tb : List (BRow F × QRow (Quad (algebraMap F K δ)))) (i : Fin n) :
    tX δ chals tb i = GX δ chals (rowAt δ tb i) := rfl

theorem GX_sH0 (chals : ℕ → K) (x : BRow F × QRow (Quad (algebraMap F K δ))) (h : x.1.sH = 0) :
    GX δ chals x = 0 := by
  simp [GX, h, liftQ]

/-- **A call block's export terms**: only the hdr row carries `sH = 1`. -/
theorem zipB_sumX (chals : ℕ → K) (p : ℕ) (y : Quad (algebraMap F K δ)) (cl : CallL) :
    ((zipB δ p y cl).map (GX δ chals)).sum =
      ((HQ.denKeyQ δ (AluSZChipJ9.keyXE : List (CoeffExpr F))).ev δ
        ⟨kvec δ ((blockQ p y cl).headD QRow.zero), fun _ => 0, chals, fun _ => 0⟩
        (envB (hdrRow (F := F) cl).col (fun _ => 0)))⁻¹ := by
  unfold zipB blockB
  rcases hq : blockQ p y cl with _ | ⟨q0, qs⟩
  · simp [blockQ] at hq
  · rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.headD_cons]
    have ht : ((((slotsOf p cl).flatMap (slotRows p cl)).zip qs).map (GX δ chals)).sum = 0 := by
      refine List.sum_eq_zero fun v hv => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      apply GX_sH0
      obtain ⟨sl, -, hr⟩ := List.mem_flatMap.mp (List.of_mem_zip hx).1
      obtain ⟨i, -, hi⟩ := List.mem_map.mp hr
      rw [← hi]; rfl
    rw [ht, add_zero]
    simp [GX, hdrRow, liftQ]

/-- **The honest table's export terms**: one per call, its hdr row's. -/
theorem tblP_sumX (chals : ℕ → K) (p : ℕ) (y : Quad (algebraMap F K δ)) (pregs : List (BRow F)) (cls : List CallL)
    (hpre : ∀ r ∈ pregs, r.sH = 0) :
    ((tblP δ p y pregs cls).map (GX δ chals)).sum = (cls.map fun cl =>
      ((HQ.denKeyQ δ (AluSZChipJ9.keyXE : List (CoeffExpr F))).ev δ
        ⟨kvec δ ((blockQ p y cl).headD QRow.zero), fun _ => 0, chals, fun _ => 0⟩
        (envB (hdrRow (F := F) cl).col (fun _ => 0)))⁻¹).sum := by
  unfold tblP
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, sum_map_flatMap]
  have h1 : ((pregs.map fun r => (r, QRow.zero)).map (GX δ chals)).sum = 0 :=
    List.sum_eq_zero fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact GX_sH0 δ chals _ (hpre r hr)
  have h3 : ([(padRow, QRow.zero)].map (GX δ chals)).sum = 0 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact GX_sH0 δ chals _ rfl
  rw [h1, h3, zero_add, add_zero]
  exact congrArg List.sum (List.map_congr_left fun cl _ => zipB_sumX δ chals p y cl)

end TableSums

section HdrKey
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The handle compress at the coins `(γH, ρH)` is `ρH + recDen 0 γH`. -/
theorem compress_recDen (χ : Coins frameJ8 K) (v : Fin 5 → ZMod p) :
    FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c => algebraMap (ZMod p) K (v c))) =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) (v 0, (v 1, v 2), (v 3, v 4)) := by
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, recDen]
  simp [IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **The hdr row's export denominator** at the ALU coins is the cell handle key `(vS, (kA, vA), (kB, vB))`. -/
theorem hdr_denX (χ : Coins frameJ8 K) (q : QRow 𝕂′) (cl : CallL) :
    (HQ.denKeyQ δ (AluSZChipJ9.keyXE : List (CoeffExpr (ZMod p)))).ev δ
        ⟨kvec δ q, fun _ => 0, AluSZChipJ9.chalsALJ8 δ χ, fun _ => 0⟩ (envB (hdrRow (F := ZMod p) cl).col (fun _ => 0)) =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        (((cl.vS : ℕ) : ZMod p), (((cl.kA : ℕ) : ZMod p), ((cl.vA : ℕ) : ZMod p)),
          (((cl.kB : ℕ) : ZMod p), ((cl.vB : ℕ) : ZMod p))) := by
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl]
  have hc : TeleHQ.coinsQ δ (⟨kvec δ q, fun _ => 0, AluSZChipJ9.chalsALJ8 δ χ, fun _ => 0⟩ : Nock.Reified.Env K) =
      ⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ := by
    unfold TeleHQ.coinsQ
    simp only
    rw [AluSZChipJ9.chalsALJ8_agree δ χ 33 (by norm_num) (by norm_num),
      AluSZChipJ9.chalsALJ8_agree δ χ 35 (by norm_num) (by norm_num),
      AluSZChipJ9.chalsALJ8_agree δ χ 34 (by norm_num) (by norm_num),
      AluSZChipJ9.chalsALJ8_agree δ χ 36 (by norm_num) (by norm_num), chals_33, chals_35, chals_34, chals_36]
    rfl
  rw [hc]
  have hk : ServeH.keyVec5 (K := K) (AluSZChipJ9.keyXE : List (CoeffExpr (ZMod p))) (envB (hdrRow (F := ZMod p) cl).col (fun _ => 0)) =
      fun c => algebraMap (ZMod p) K (![((cl.vS : ℕ) : ZMod p), ((cl.kA : ℕ) : ZMod p), ((cl.vA : ℕ) : ZMod p),
        ((cl.kB : ℕ) : ZMod p), ((cl.vB : ℕ) : ZMod p)] c) := by
    funext c
    fin_cases c <;> rfl
  rw [hk, compress_recDen]
  rfl

end HdrKey

section SXRun
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC cellHx_eq wsum)
open Nock.V1J8.Gen (hdN' tlN' atomV)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- A primitive call record comes from an `s11j` row of the run. -/
theorem mem_pcallsR {pids : List ℕ} {rows : Array RowNX} {x : ℕ × Noun × Noun}
    (hx : x ∈ ComplJ9ALData.pcallsR pids rows) :
    ∃ row ∈ rows.toList, row.st = .s11j ∧ atomV row.sf1 ∈ pids ∧ x = (atomV row.sf1, row.s, row.e) := by
  unfold ComplJ9ALData.pcallsR at hx
  obtain ⟨row, hrow, hx⟩ := List.mem_filterMap.mp hx
  by_cases hc : row.st = .s11j ∧ atomV row.sf1 ∈ pids
  · rw [if_pos hc] at hx
    exact ⟨row, hrow, hc.1, hc.2, (Option.some.inj hx).symm⟩
  · rw [if_neg hc] at hx; cases hx

/-- **Every primitive call's subject is a cell of the table, of two atoms.** -/
theorem pcall_subject (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ∀ x ∈ ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t),
      ∃ a c, x.2.1 = .cell (.atom a) (.atom c) ∧ x.2.1 ∈ (DL).cells := by
  intro x hx
  obtain ⟨row, hrow, hst, hid, rfl⟩ := mem_pcallsR hx
  obtain ⟨a, c, n, hs, -, -, -⟩ := AluCallOK.prim_row hgen hnd hprim hnoDec hrow hst hid
  refine ⟨a, c, hs, ?_⟩
  rcases ComplJ9ALData.handle_noun_casesL (p := p) Rt prims hgen (n := row.s) hrow (by simp [handleNounsX]) with
    ⟨-, hm⟩ | ⟨v, hv, -⟩ | ⟨v, hv, -⟩
  · exact hm
  · rw [hs] at hv; cases hv
  · rw [hs] at hv; cases hv

/-- With every subject a cell, the ALU export reads are one per call. -/
theorem aluXL_eq (cs : List Noun) (pc : List (ℕ × Noun × Noun))
    (hc : ∀ x ∈ pc, ∃ a c, x.2.1 = .cell (.atom a) (.atom c)) :
    ComplJ9ALData.aluXL cs pc = pc.map fun x => (Nock.V1J8.Gen.idxOf cs x.2.1, 1) := by
  unfold ComplJ9ALData.aluXL
  induction pc with
  | nil => rfl
  | cons x pc ih =>
    obtain ⟨a, c, hx⟩ := hc x (List.mem_cons_self)
    rw [List.filterMap_cons, List.map_cons, ← ih fun y hy => hc y (List.mem_cons_of_mem _ hy)]
    simp [hx]

/-- **The ALU export terminal is the `wsum` of the cell handle weights over the ALU export reads** (`aluXL`). -/
theorem SX_eq (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (n : ℕ) (χ : Coins frameJ8 K)
    (hlen : (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)).length ≤ n)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinjC : Function.Injective (powN o (DL).cells.length)) :
    SX (p := p) δ Rt hgen prims n χ =
      wsum (GC δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o χ)
        (ComplJ9ALData.aluXL (DA).cells (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t))) := by
  have hsub := pcall_subject (p := p) Rt hgen prims hnd hprim hnoDec
  unfold SX
  rw [Finset.sum_congr rfl (fun i _ => tX_eq δ _ _ i),
    sum_rowAt δ _ (GX δ (AluSZChipJ9.chalsALJ8 δ χ)) (GX_sH0 δ _ _ rfl) hlen]
  unfold tbR AluSatRun.tblRun AluSatRun.clsRun
  rw [tblP_sumX δ _ p _ _ _ (fun r hr => by
    obtain ⟨a1, a2, a3, a4, rfl⟩ := AluSatPreg.pregsP_preg _ _ _ r hr; rfl)]
  rw [aluXL_eq _ _ fun x hx => (hsub x hx).imp fun a h => h.imp fun c h => h.1]
  unfold wsum AluHonestTable.callsLOf
  rw [List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨a, c, hs, hm⟩ := hsub x hx
  simp only [Function.comp_apply]
  rw [hdr_denX]
  have hjl := List.idxOf_lt_length_of_mem hm
  have e1 : Nock.V1J8.Gen.idxOf (DA).cells x.2.1 = (DL).cells.idxOf x.2.1 := ComplJ8OfBal.genIdxOf_eq _ _ hm
  have e2 : Nock.V1J8.Gen.idxOf (DL).cells x.2.1 = (DL).cells.idxOf x.2.1 := ComplJ8OfBal.genIdxOf_eq _ _ hm
  simp only [GC]
  rw [e1, e2, cellHx_eq δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o hinjC χ rfl _ hjl ((List.getElem_idxOf hjl).trans hs)
    (by simp [Noun.isCell]) (by simp [Noun.isCell]), hs]
  simp only [Nat.cast_one, one_mul, hdN', tlN']

end SXRun

/-! ## 3. `hGx_L` -/

section Gx
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC cellHx_eq wsum wsum_append)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (bumpAll bumpAll_getD bumpAll_size sumAt cnt cellPairs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1 (xRecsOf jReadsOf csA GA balG1_gen whX_eq_gen cells_kids_gen)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (Rows31A rows31_of_A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The ALU export reads of the run. -/
abbrev aluX : List (ℕ × ℕ) :=
  ComplJ9ALData.aluXL (DA).cells (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t))

/-- **The overlay's `mh` is the count of its export consumers**: the twin compute's, the cell walk's, the
overlay's J reads, and the ALU's export reads. -/
theorem mhL_eq_cnt (j : ℕ) (hj : j < (DL).cells.length) :
    (DL).mh.getD j 0 = cnt (xRecsOf (DL) (csA (p := p) Rt hgen ++ aluX (p := p) Rt hgen prims)) j := by
  have e : (DL).mh = bumpAll (bumpAll (bumpAll (bumpAll (Array.replicate (DA).cells.length 0) (csA (p := p) Rt hgen))
      (cellPairs (DA).cells ((DA).ws.map Nock.V1J8.Gen.WRow.node))) (jReadsOf (DL))) (aluX (p := p) Rt hgen prims) := by
    show bumpAll (ComplJ8Data.mhJP p (ComplJ9ALData.mh0A p Rg Rt hgen) (DL).jrows) _ = _
    rw [ComplJ9ABalX.mhJP_eq]
    unfold ComplJ9ALData.mh0A
    simp only
    rw [ComplJ9ABalX.mhCountsX9_eq]
    rfl
  have hs0 : (Array.replicate (DA).cells.length 0).size = (DA).cells.length := Array.size_replicate
  rw [e, bumpAll_getD _ _ _ (by rw [bumpAll_size, bumpAll_size, bumpAll_size, hs0]; exact hj),
    bumpAll_getD _ _ _ (by rw [bumpAll_size, bumpAll_size, hs0]; exact hj),
    bumpAll_getD _ _ _ (by rw [bumpAll_size, hs0]; exact hj), bumpAll_getD _ _ _ (by rw [hs0]; exact hj),
    ComplJ8Data.cnt_eq_sumAt]
  have hr : (Array.replicate (DA).cells.length 0).getD j 0 = 0 := by simp [Array.getD]
  rw [hr]
  simp only [xRecsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ComplJ8Data.sumAt_append]
  have hw : cellPairs (DL).cells ((DL).ws.map Nock.V1J8.Gen.WRow.node) =
      cellPairs (DA).cells ((DA).ws.map Nock.V1J8.Gen.WRow.node) := rfl
  rw [hw]
  unfold sumAt
  ring

/-- The cell handle weight does not depend on the orbit or on the record's multiplicities (`DL` vs `DA`). -/
theorem GC_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (DL).cells.length)) (hinj' : Function.Injective (powN o' (DA).cells.length))
    (χ : Coins frameJ8 K) (j : ℕ) (hj : j < (DL).cells.length) :
    GC δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o χ j =
      GC δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o' χ j := by
  have hcl : ComplJ8Data.ClP (DD).cells [] := ComplJ8Data.cells_closed _
  obtain ⟨x, y, hxy, hx, hy⟩ := cells_kids_gen (DD).cells hcl
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) _ (List.getElem_mem hj)
  simp only [GC]
  rw [cellHx_eq δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o hinj χ rfl j hj hxy hx hy,
    cellHx_eq δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o' hinj' χ rfl j hj hxy hx hy]
  rfl

/-- **The serial range of the overlay's export consumers.** -/
theorem hrangeL (hpG : p = Nock.Atoms.p) (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (hlen : (DL).cells.length < p)
    (hkN : ∀ x ∈ (DL).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1)
    (hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells) :
    ∀ q ∈ (xRecsOf (DL) (csA (p := p) Rt hgen ++ aluX (p := p) Rt hgen prims)).flatMap ComplJ8Data.NamedRecs.recs,
      0 < q.2 → q.1 < (DL).cells.length := by
  have hrowsA := ComplJ9ARunFacts.hrowsA_run Rt hgen hpG hax9 hop5
  intro q hq _
  simp only [xRecsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with (hq | hq) | hq | hq
  · -- compute
    obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
    simp only [ComplJ9ABalX.basesA, ComplJ9ADataRec.basesA9, List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    have hl : HonestWalkX9.rowAt9 (bfsForest [ComplJ9AGen.genX9T t]) (j + 1) ∈ (rowsOfT9 t).toList := by
      simp only [rowsOfT9, List.toList_toArray, List.mem_map, HonestWalkX9.rowAt9]
      refine ⟨(bfsForest [ComplJ9AGen.genX9T t])[j], List.getElem_mem _, ?_⟩
      simp [List.getElem?_eq_getElem hj]
    obtain ⟨hok, hs3, hc⟩ := hrowsA _ hl
    exact ComplJ9ABalR.xcons9_row_range (R := Rg.R) _ _ _ _ _ _ _ (ComplJ9AGen.rowsOfT9_semN9 hgen _ hl) hok hs3 hc
      hlen q hq
  · -- ALU
    rw [aluX, aluXL_eq _ _ fun x hx =>
      (pcall_subject (p := p) Rt hgen prims hnd hprim hnoDec x hx).imp fun a h => h.imp fun c h => h.1] at hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨a, c, -, hm⟩ := pcall_subject (p := p) Rt hgen prims hnd hprim hnoDec x hx
    exact ComplJ8Data.idxOf_lt _ _ hm
  · -- walk
    refine ComplJ8Data.cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hab
    have hperm := ComplJ8OfBal.walkGen_nodes_perm (DA).cells (DA).reads
      (ComplJ9ABalGen.hall_readsA Rt hgen)
      (fun r hr => (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9 r hr).trans (by norm_num))
    have hws : (DA).ws = (Nock.V1J8.Gen.walkGen ((DA).cells.headD (.atom 0)) (DA).reads).1 := rfl
    have hw' : w ∈ (DA).ws := hw
    rw [hws] at hw'
    have hm := (hperm.mem_iff).mp (List.mem_map.mpr ⟨w, hw', rfl⟩)
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hm
    rw [e] at hue
    rw [← hue]
    exact hwcellA u hu
  · -- J
    exact jReadsL_range Rt hgen prims hlen hkN q hq

/-- The walk's handle-import terminal as a pair of publics. -/
theorem pubsW_whX (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (pubsWOf δ b D o χ WalkHQ.pubXQ) (pubsWOf δ b D o χ (WalkHQ.pubXQ + 1)) =
      whX δ b D o χ := by
  have h4 : pubsWOf δ b D o χ WalkHQ.pubXQ = pub2 δ (whX δ b D o χ) 4 := by simp [pubsWOf, WalkHQ.pubXQ]
  have h5 : pubsWOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (whX δ b D o χ) 5 := by simp [pubsWOf, WalkHQ.pubXQ]
  rw [h4, h5, pub2_mk2 δ _ 4 rfl]

/-- **The walk's handle import is the same at `DA` and `DL`** (any injective orbits). -/
theorem whX_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinjC : Function.Injective (powN o (DL).cells.length))
    (hinjW : Function.Injective (powN o (walkRows (DL).cells (DL).reads).length))
    (hinjC' : Function.Injective (powN o' (DA).cells.length))
    (hinjW' : Function.Injective (powN o' (walkRows (DA).cells (DA).reads).length))
    (hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells) (χ : Coins frameJ8 K) :
    whX δ b (DA) o' χ = whX δ b (DL) o χ := by
  have hcellsC : ∀ c ∈ (DA).cells, c.isCell = true := fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1
  rw [whX_eq_gen δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o' hinjC' hinjW' rfl (ComplJ8Data.cells_closed _)
      hcellsC hwcellA χ,
    whX_eq_gen δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o hinjC hinjW rfl (ComplJ8Data.cells_closed _)
      hcellsC hwcellA χ]
  refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
  exact (GC_LA δ b Rt hgen prims o o' hinjC hinjC' χ _ (List.idxOf_lt_length_of_mem (hwcellA u hu))).symm

end Gx

section GxRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC wsum wsum_append)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1 (csA GA balG1_gen)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (Rows31A rows31_of_A hF_run)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
local notation "BL" => B8L δ b Rt hgen prims hpG h31

/-- **`hGx_L`**: the export balance of the J-9 AL record (compute and walk publics from `BA`, the J and cell
publics from `B8L`, the ALU export terminal `SX`).  The `mh` bump `aluXL` pays for `SX`. -/
theorem hGx_L (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (χ : Coins frameJ8 K) (hχA : (BA).Good χ) (hχL : (BL).Good χ) (n : ℕ)
    (hlen : (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)).length ≤ n) :
    ((BA).M χ).ρ 3 + (Quad.mk _ (((BA).M χ).pubsW WalkHQ.pubXQ) (((BA).M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (((BL).M χ).pubsJ 2) (((BL).M χ).pubsJ 3) + SX (p := p) δ Rt hgen prims n χ) =
      Quad.mk _ (((BL).M χ).pubsC CellHQ.pubHQ) (((BL).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  set oA := orbJ8 (DA) (hF_run Rt hgen hpG h31A) with hoA
  set oL := orbJ8 (DL) (hFL Rt hgen prims hpG h31) with hoL
  have hmCA : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hmWA : (walkRows (DA).cells (DA).reads).length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hmCL : (DL).cells.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hmWL : (walkRows (DL).cells (DL).reads).length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hinjCA := (powN_ok oA (le_two_pow_ht (DA) hmCA)).1
  have hinjWA := (powN_ok oA (le_two_pow_ht (DA) hmWA)).1
  have hinjCL := (powN_ok oL (le_two_pow_ht (DL) hmCL)).1
  have hinjWL := (powN_ok oL (le_two_pow_ht (DL) hmWL)).1
  have hlenL : (DL).cells.length < p := by
    have h1 := rows31_of_A h31 _ hmCL
    have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    omega
  have hkN := hkNL Rt hgen prims hRtJ
  have hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells :=
    ComplJ9ABalGen.walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _)
      (ComplJ9ADataRec.cellsA_pos Rt hgen) (ComplJ9ABalW.hslotA hgen) (ComplJ9ABalW.hrootA hgen)
  have hρ := ComplJ9ABalCR.hC_runA δ b Rt hgen hpG h31A hax9 hop5 (ComplJ9ARunFacts.sub9_run (p := p) Rt hgen) χ hχA
  have hrange := hrangeL Rt hgen prims hpG hax9 hop5 hwalk9 hnd hprim hnoDec hlenL hkN hwcellA
  have hcsA : wsum (GA δ b Rt hgen hpG h31A χ) (csA (p := p) Rt hgen) =
      wsum (GC δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) oL χ) (csA (p := p) Rt hgen) := by
    unfold wsum
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    rcases Nat.eq_zero_or_pos q.2 with h0 | h0
    · simp [h0]
    · have hq1 := hrange q (by
        simp only [ComplJ9ABalG1.xRecsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inl (Or.inl hq)) h0
      rw [GC_LA δ b Rt hgen prims oL oA hinjCL hinjCA χ _ hq1]
  have hSX := SX_eq δ b Rt hgen prims hnd hprim hnoDec n χ hlen oL hinjCL
  have bal := balG1_gen δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) oL hinjCL hinjWL rfl
    (ComplJ8Data.cells_closed _) (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) hwcellA rfl
    (ComplJ9ABalGen.hall_readsA (p := p) Rt hgen) (ComplJ9ADataRec.walkDepthOK_readsA (p := p) Rt hgen hwalk9)
    (csA (p := p) Rt hgen ++ aluX (p := p) Rt hgen prims) (fun j hj => mhL_eq_cnt Rt hgen prims j hj) hrange χ
    (((BA).M χ).ρ 3 + SX (p := p) δ Rt hgen prims n χ) (by rw [wsum_append, ← hcsA, ← hρ, ← hSX])
    (hJ_L δ b Rt hgen prims hRtJ oL hinjCL χ hlenL hkN)
  have eWA := pubsW_whX δ b (DA) oA χ
  have eWL := pubsW_whX δ b (DL) oL χ
  have hW := whX_LA δ b Rt hgen prims oL oA hinjCL hinjWL hinjCA hinjWA hwcellA χ
  show ((BA).M χ).ρ 3 + (Quad.mk _ (pubsWOf δ b (DA) oA χ WalkHQ.pubXQ) (pubsWOf δ b (DA) oA χ (WalkHQ.pubXQ + 1)) +
      Quad.mk _ (pubsJOf δ (DL) χ 2) (pubsJOf δ (DL) χ 3) + SX (p := p) δ Rt hgen prims n χ) =
    Quad.mk _ (pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) oL χ CellHQ.pubHQ)
      (pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) oL χ (CellHQ.pubHQ + 1))
  rw [← bal, eWA, hW, ← eWL]
  ring

end GxRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalX
