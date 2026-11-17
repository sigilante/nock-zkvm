/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenClosed.lean

 **J-8 completeness over any admissible `J8Data`, continued**: the J sub-balance of `ComplJ8OfBalJ`, `ComplJ8Closed` over `j8DataGen`, and the headline theorems over any
 admissible datum: `obligations_of_fams'`, `openJ8_closed'`, `complJ8_closed'` (with `famsAll_facts'`, which
 needs no side condition), and the check `complJ8_closed_of_any` (`complJ8_closed` as the instance at
 `j8DataOf_ok`).
 Every declaration is the corresponding statement and proof over `j8DataGen … O` (suffix `G`), except where the
 free list orders need a membership or permutation step.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenOfBalG
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

noncomputable section

/-! ### Twins of `ComplJ8OfBalJ` -/

section ComplJ8OfBalJG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ
open Nock Nock.Jet.ChipJ8 Nock.Jet.Interp
open Nock.Jet.Autogen (nhd ntl)
noncomputable section
section RunJ
open Nock.Jet.RapJetJ8 (consKT provKT consKT_eq provKT_eq tlF)
open Nock.Jet.Autogen (Tpl compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data mvFixP pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Edit Nock.Edit.GenX Nock.Walk
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
variable [Fact (ringChar (ZMod p)).Prime] (Rt : ℕ → Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- The calls of the run are well typed, `axPosB`, in the template's domain, and registered. -/
theorem calls_okG (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ cl ∈ (j8DataGen p Rg Rt hgen O).calls, (Rt cl.1).WellTyped p ∧ axPosB (Rt cl.1) = true ∧
      (∃ r, (Rt cl.1).sem p cl.2 = some r) ∧ cl.1 ∈ (j8DataGen p Rg Rt hgen O).regs := by
  intro cl hcl
  have hc := ComplJ8Jet.calls_of_hregC hgen Rt hRt cl hcl
  have hid := ComplJ8Of.calls_called hgen cl hcl
  exact ⟨hc.1, (hRt _ hid).2.1, hc.2, List.mem_dedup.mpr (List.mem_map_of_mem hcl)⟩

/-- A registered template's compiled formula is a cell of the table. -/
theorem compile_memG (id : ℕ) (hid : id ∈ (j8DataGen p Rg Rt hgen O).regs) :
    compile p (Rt id) ∈ (j8DataGen p Rg Rt hgen O).cells := by
  obtain ⟨a, c, hac⟩ := ComplJ8Data.compile_isCell p (Rt id)
  have := jn_goodG p Rg Rt hgen O (compile p (Rt id))
    (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩)) a c hac
  exact this

/-- **The registry pins are provided by the registry rows.** -/
theorem pins_provG :
    ∀ κ ∈ pinsOfP p (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).idx,
      ∃ x' ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) Rt
        (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).calls, ∃ κ0 ∈ provK x', κ = tlF κ0 := by
  set D := j8DataGen p Rg Rt hgen O with hD
  intro κ hκ
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hκ
  refine ⟨⟨regPre id, mkW 0 1 0 0 0 (ComplJ8Data.hJd p D.cells D.acs (compile p (Rt id))) (0, 0) (0, 0)⟩, ?_, _,
    List.mem_singleton_self _, ?_⟩
  · unfold honestJ8G
    exact List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩)
  · have hm := compile_memG Rt hgen O id hid
    obtain ⟨a, c, hac⟩ := ComplJ8Data.compile_isCell p (Rt id)
    congr 1
    simp only [Nock.Jet.PinJ8.pinKey, mkW]
    rw [hac]
    simp [keyRg, KE.ev, colOf, Col.id, Col.kN, Col.vN, regPre, ComplJ8Data.hJd, ComplJ8Data.hdlP, hD,
      j8DataGen, hac]

/-- **The in-chip balance of the run's J rows** (existence form, before the `mv` fix). -/
theorem honest_covG (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).calls,
      ∀ κ ∈ consK x, ∃ x' ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) Rt (j8DataGen p Rg Rt hgen O).regs
        (j8DataGen p Rg Rt hgen O).calls, κ ∈ provK x' :=
  honestJ8_cov _ (fun v hv => by simpa using ComplJ8Data.hJd_small p _ _ v hv) Rt _ _ (calls_okG Rt hgen O hRt)

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK) in
/-- **The layout statics of the run** (`hsmall`, `huniq`), from `hax`, `hRt` and the row binder. -/
theorem lay_staticsG (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : ComplJ8Of.Rows31 (j8DataGen p Rg Rt hgen O))
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    (∀ q ∈ layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids,
      q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids).filterMap tvKey).Nodup := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hlt := ComplJ8Of.calls_lt hgen hax
  have hmemR : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, ∃ cl ∈ (j8DataGen p Rg Rt hgen O).calls, cl.1 = id := by
    intro id hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
    exact ⟨cl, hcl, e⟩
  have hJlen : (layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids).length < p := by
    rw [← jrows_pre_runG Rt hgen O, List.length_map]
    exact size_lt_pG Rt hgen O hp63 h31 (by simp [ComplJ8Of.sizesJ8])
  have hidsl : (j8DataGen p Rg Rt hgen O).ids.length < p := by
    have h1 : (j8DataGen p Rg Rt hgen O).ids.length ≤ (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 (size_lt_pG Rt hgen O hp63 h31 List.mem_cons_self)
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).calls
    hcalls hlt hJlen
  refine ⟨ComplJ8Jet.hsmall_of_blocks Rt _ _ (fun i hi => ?_) hidsl (fun i hi => (hblk i hi).2) hp,
    ComplJ8Jet.huniq_of_blocks Rt _ _ (fun i hi => (hblk i hi).1)⟩
  obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK) in
/-- **The three multiset facts of `termJ_sum_of_mv` at the run's J rows**: unique provides, covered consumes and
pins, and `mv` = consumers + pins. -/
theorem jrows_mv_factsG (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : ComplJ8Of.Rows31 (j8DataGen p Rg Rt hgen O))
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((j8DataGen p Rg Rt hgen O).jrows.flatMap provKT).Nodup ∧
    (∀ κ ∈ (j8DataGen p Rg Rt hgen O).jrows.flatMap consKT ++ pinsOfP p (j8DataGen p Rg Rt hgen O).regs
        (j8DataGen p Rg Rt hgen O).idx, κ ∈ (j8DataGen p Rg Rt hgen O).jrows.flatMap provKT) ∧
    (∀ x ∈ (j8DataGen p Rg Rt hgen O).jrows, ∀ κ ∈ provKT x,
      x.w.mv = (((((j8DataGen p Rg Rt hgen O).jrows.flatMap consKT).count κ +
        (pinsOfP p (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).idx).count κ : ℕ)) : ZMod p)) := by
  rw [j8DataOf_jrowsG Rt hgen O]
  obtain ⟨hsmall, huniq⟩ := lay_staticsG Rt hgen O hp63 hax h31 hRt
  refine ⟨?_, hcov_fix _ _ (honest_covG Rt hgen O hRt) (pins_provG Rt hgen O), hmv_fix _ _⟩
  rw [flatMap_provKT_fix]
  exact hnd_rows Rt _ _ _ (ComplJ8Jet.honestJ8_pre _ Rt _ _) hsmall huniq (List.nodup_dedup _)

end RunJ
section HJ
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data mvFixP pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.RapJetJ8 (keyK dJ consKT provKT tlF)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sT)
open Nock.Jet.Autogen (Tpl compile)
open Module
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- **The J side of the service sub-balance**: the J rows' service terms total the call keys' weights. -/
theorem jrows_FjG (chals : ℕ → K)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((j8DataGen p Rg Rt hgen O).jrows.map (Fj δ chals)).sum =
      ((j8DataGen p Rg Rt hgen O).calls.map fun cl => dJ δ chals (κc Rt (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) cl)).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  have hok := calls_okG Rt hgen O hRt
  rw [j8DataOf_jrowsG Rt hgen O, mvFixP_eq, List.map_map]
  have e1 : (Fj δ chals) ∘ (fun r => setMv r (mvOf (Nock.Jet.ChipJ8.honestJ8G (p := p) (ComplJ8Data.hJd p D.cells D.acs) Rt D.regs D.calls)
      (pinsOfP p D.regs D.idx) r)) = Fj δ chals := by
    funext x; simp only [Function.comp, Fj, sT, ents3_setMv]; rfl

  rw [e1]
  unfold Nock.Jet.ChipJ8.honestJ8G
  rw [List.map_append, List.sum_append, List.sum_eq_zero (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    simp [Fj, sT, ents3_nocall, Nock.Jet.ChipJ8.regPre]), zero_add, Nock.Jet.RapJetJ8.sum_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 D.calls, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  obtain ⟨⟨i, s0⟩, c⟩ := q
  obtain ⟨hT, -, ⟨r0, hsem⟩, -⟩ := hok _ (List.fst_mem_of_mem_zipIdx hq)
  exact blockW_Fj δ Rt chals (ComplJ8Data.hJd p D.cells D.acs) c i s0 hT r0 hsem

set_option maxHeartbeats 1000000 in
/-- **A compute row's jet consume is the service weight of its call's key** (`0` off `s11j`). -/
theorem jetT_rowG (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p)
    (j : ℕ) (hj : j < (bfsForest [t]).length) :
    ComplJ8OfBalG.jetT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        pubVal j = Fu δ b Rt (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) χ ((bfsForest [t])[j]'hj) := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj, hrr]
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold ComplJ8OfBalG.jetT
  rw [DX_jet δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 16 (by decide)]
  have hmap : ∀ tr : ℕ → ZMod p, ChipHX.jetRecX.map (ChipHX.RE.ev tr) =
      [tr 32, tr 41, tr 42, tr 25, tr 26, tr 29, tr 30, ((3 : ℕ) : ZMod p)] := fun tr => rfl
  rw [hmap]
  simp only [HonestCompX.cxSf1_v, HonestCompX.cxFtt_k, HonestCompX.cxFtt_v, HonestCompX.cxS_k,
    HonestCompX.cxS_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  unfold Fu
  by_cases hst : rr.st = .s11j
  · rw [if_pos hst, ← hrr, if_pos (by rw [hst]; rfl), map_one, one_mul]
    obtain ⟨id, hft, hftt, hsem⟩ := s11j_row Rt hgen hRt hin hst
    rw [← hrr] at hft hftt hsem
    have hcl : (id, rr.s) ∈ D.calls := by
      show _ ∈ Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      refine List.mem_filterMap.mpr ⟨rr, ?_, ?_⟩
      · simp only [List.toList_toArray]; exact List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩
      · simp [hst, hft, Nock.V1J8.Gen.atomV]
    obtain ⟨hT, -, -, hreg⟩ := calls_okG Rt hgen O hRt _ hcl
    have hidp : id < p := ComplJ8Of.calls_lt hgen hax _ hcl
    obtain ⟨c, hz⟩ := exists_mem_zipIdx hcl
    have hjn : ∀ y ∈ (Nock.Jet.Interp.honestRows p (Rt id) rr.s c).map Nock.Jet.Interp.JRow.val, y ∈ D.jn := by
      intro y hy
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hz, List.mem_cons_of_mem _ hy⟩)
    have hsjn : rr.s ∈ D.jn := List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hz, List.mem_cons_self⟩)
    obtain ⟨hl0, he⟩ := look0 (Rt id) hT rr.s rr.e hsem c
    have hres : res Rt p (id, rr.s) = rr.e := by simp [res, hsem]
    have hid : HonestCompX.hv D.H (.atom id) = (id : ZMod p) := by
      show (((ComplJ8Data.hdlP p D.cells D.acs (.atom id)).2 : ℕ) : ZMod p) = _
      simp [ComplJ8Data.hdlP, hidp]
    congr 2
    simp only [κc, hres, Nock.V1J8.Gen.atomV, hft, hid, hftt]
    rfl
  · have h16 : RowDecodeVSX.stIdx rr.st ≠ 16 := by
      intro h; apply hst; revert h; cases rr.st <;> simp [RowDecodeVSX.stIdx]
    rw [if_neg h16, ← hrr, if_neg hst]
    simp

theorem sum_jetTG (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataGen p Rg Rt hgen O).H
        (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((j8DataGen p Rg Rt hgen O).calls.map fun cl =>
        ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) cl))).sum := by
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataGen p Rg Rt hgen O).H
      (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Fu δ b Rt (ComplJ8Data.hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) χ ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [jetT_rowG δ b Rt hgen O hax hRt χ pubVal j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t]
  show _ = ((Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).map _).sum
  unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
  simp only [List.toList_toArray]
  rw [← sum_filterMap_ite (fun r : RowNX => r.st = .s11j) (fun r => (Nock.V1J8.Gen.atomV r.sf1, r.s)), List.map_map]
  rfl

set_option maxHeartbeats 2000000 in
/-- **`hJ`, the jet service sub-balance of `balG` clause 3, at the run, at every coin**: the compute jet consumes,
the registry pins and the J terminal sum to zero. Binders: `hpG hax hRt h31` only (no subject binder). -/
theorem hJ_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataGen p Rg Rt hgen O).H
          (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j +
        ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map
          fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) = 0 := by
  intro χ _
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o _
  -- the J terminal as `Σ termJ`
  have eJ : Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) =
      ∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k) := by
    show Quad.mk _ (pubsJOf δ D χ 0) (pubsJOf δ D χ 1) = _
    have e0 : pubsJOf δ D χ 0 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 0 := by simp [pubsJOf]
    have e1 : pubsJOf δ D χ 1 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 1 := by simp [pubsJOf]
    rw [e0, e1, pub2_mk]
  obtain ⟨hnd, hcov, hmv⟩ := jrows_mv_factsG Rt hgen O hp63 hax h31 hRt
  have hT := Nock.Jet.ChipJ8T.HonestBal.termJ_sum_of_mv_fin δ (VerJ8.chalsJJ8 χ) D.jrows.get
    (pinsOfP p D.regs D.idx) (by rw [List.ofFn_get]; exact hnd) (by rw [List.ofFn_get]; exact hcov)
    (by rw [List.ofFn_get]; exact hmv)
  rw [List.ofFn_get] at hT
  have hF := jrows_FjG δ Rt hgen O (VerJ8.chalsJJ8 χ) hRt
  -- the pins
  have eP : ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map
      fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum =
      ((pinsOfP p D.regs D.idx).map (dJ δ (VerJ8.chalsJJ8 χ))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]
    simp only [pinCons, pinsOfP, List.map_map]
    rfl
  -- the compute side
  have eC := sum_jetTG δ b Rt hgen O hax hRt χ (pubCG δ b Rt hgen O χ)
  have eCJ : ((D.calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum) =
      ((D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]; rfl
  have hF' : (D.jrows.map fun r => liftQ δ r.w.m * sT δ (VerJ8.chalsJJ8 χ) Nock.Jet.ChipJ8.ents3 r).sum =
      (D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl)).sum := hF
  rw [eC, eP, eJ, hT, eCJ, hF']
  ring

end HJ
end
end ComplJ8OfBalJG_1

/-! ### Twins of `ComplJ8Closed` -/

section ComplJ8ClosedG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ComplJ8Obligations ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
noncomputable section
section Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The honest record of the run with every family** (`hF hC hA` derived from the row binder). -/
abbrev BRunAG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) : HonestJ8 p K δ Rg fuel s f r :=
  BOfG δ b Rt hgen O o (cells_posG Rt hgen O) (acs_posG Rt hgen O)
    (avOfO δ b (j8DataGen p Rg Rt hgen O) o (acs_posG Rt hgen O))
    (famsAllO δ b (j8DataGen p Rg Rt hgen O) o (cells_posG Rt hgen O) (acs_posG Rt hgen O))

/-- **Goodness is antitone in the family list.** -/
theorem good_monoG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
    (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) (AV : AVPart p K) {fams fams' : List (List (BadSpec K))}
    (hsub : ∀ L ∈ fams, L ∈ fams') (χ : Coins frameJ8 K)
    (h : (BOfG δ b Rt hgen O o hC hA AV fams').Good χ) : (BOfG δ b Rt hgen O o hC hA AV fams).Good χ := by
  have h' : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams'),
      χ ∉ e.1 := h
  show ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams), χ ∉ e.1
  intro e he
  apply h'
  simp only [badOf, badList, List.mem_map, List.mem_append, List.mem_flatten] at he ⊢
  obtain ⟨x, hx, rfl⟩ := he
  refine ⟨x, ?_, rfl⟩
  rcases hx with hx | ⟨L, hL, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨L, hsub L hL, hx⟩

/-- `BRunAG`-good coins are `BRunG`-good. -/
theorem goodAG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (χ : Coins frameJ8 K)
    (h : (BRunAG δ b Rt hgen O o).Good χ) : (BRunG δ b Rt hgen O o).Good χ :=
  good_monoG δ b Rt hgen O _ _ _ _ (fun L hL => List.mem_append_left _ hL) χ h

/-- **`obligations_of_famsG`**: `obligations_of_run` at any family list containing `famsOf`, with its side
conditions and pin count. -/
theorem obligations_of_famsG (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t)
    (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataGen p Rg Rt hgen O).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
    (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) (fams : List (List (BadSpec K)))
    (hsub : ∀ L ∈ famsOfO δ b (j8DataGen p Rg Rt hgen O) o hC, L ∈ fams)
    (hOK : ∀ L ∈ fams, ∀ e ∈ L, e.OK) (hpin : ∀ L ∈ fams, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (hcnt : (fams.map nPins).sum ≤ 2 ^ 66)
    (OJ : OpenJ8 δ b (BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams)) :
    ComplJ8Obligations δ b (BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams) := by
  have hcl : ∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p := fun k v hv =>
    hclA k v (by rw [hv]; simp [Noun.leafList])
  have hreg := regs_calledG (p := p) Rt hgen O
  have hregLeaf : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, ∀ v ∈ (Nock.Jet.Autogen.compile p (Rt id)).leafList, v < p :=
    ComplJ8RegLeaf.compile_leaves_lt_reg (by omega) Rt _ (fun id hid => (hRt id (hreg id hid)).2.2)
      (fun id hid => hregAx id (hreg id hid))
  have mem : ∀ {L}, L ∈ famsOfO δ b (j8DataGen p Rg Rt hgen O) o hC → L ∈ fams := fun h => hsub _ h
  have m0 := mem (L := ComplJ8CompPole.compPoles (K := K) δ (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
      (bfsForest [(j8DataGen p Rg Rt hgen O).t]) (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length) List.mem_cons_self
  have m1 := mem (L := famCellV δ (j8DataGen p Rg Rt hgen O)) (List.mem_cons_of_mem _ List.mem_cons_self)
  have m2 := mem (L := famCellH δ b (j8DataGen p Rg Rt hgen O) hC (o))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m3 := mem (L := famWalkV δ (j8DataGen p Rg Rt hgen O))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have m4 := mem (L := famWalkH δ (j8DataGen p Rg Rt hgen O))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))
  have m5 := mem (L := famJ δ (j8DataGen p Rg Rt hgen O))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := compute_groupG δ b Rt hgen O o hC hA
    (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams hp63 hax hop5 hcl m0
  obtain ⟨n1, n2⟩ := nodes_okG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams
  obtain ⟨g1, g2, g3⟩ := nodes_groupG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams hp63 h31
  obtain ⟨w1, w2⟩ := bad_groupG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams hOK hpin
    (fun _ => hcnt)
  exact
    { hH := c1, hpair := c2, hN := c3, hinjX := n1, hadjX := n2,
      htrC := fun χ => htrC_runG δ b Rt hgen O o hC hA _ _ χ,
      hpIC := c4, hpS := c5, hpO := c6, hpub := c7, hρ := c8, goodC := c9,
      cellOK := fun χ hχ => cellOK_runG δ b Rt hgen O o hC hA _ _ hpG hp63 hleaf m1 m2 χ hχ,
      cellNodes := g1,
      walkOK := fun χ hχ => walkOK_runG δ b Rt hgen O o hC hA _ _ hp63 h31 hwalk m3 m4 χ hχ,
      walkNodes := g2,
      jOK := fun χ hχ => jOK_runG δ b Rt hgen O o hC hA _ _ hp63 h31 hRt m5 χ hχ,
      atomOK := OJ.atomOK, atomNodes := g3, awOK := OJ.awOK, balG := OJ.balG, balV := OJ.balV, balF := OJ.balF,
      stat := stat_runG δ b Rt hgen O o hC hA _ _ hp63 hax h31 hleaf hRt,
      claim := fun χ => claim_runG δ b Rt hgen O o hC hA _ _ hp63 h31 hclA hleaf hregLeaf χ,
      budget := budget_runG δ b Rt hgen O o hC hA _ _ hp63 h31,
      wt := w1,
      staged := staged_runG δ b Rt hgen O o hC hA _ _ (stA_runO δ b _ o hA) (stV_runO δ b _ o hA),
      fig := w2 }

/-- **`OpenJ8` at `BRunAG`, closed**: every field from a theorem above, by `exact`. `atomOK`/`awOK` are
stated at any family list containing theirs; `balG` (`balG_closedG` with `hI_runG`, `hA_runG` and
`hJ_runG`), `balV` and `balF` at `BRunG`, applied through `goodAG`. -/
theorem openJ8_closedG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    OpenJ8 δ b (BRunAG δ b Rt hgen O o) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have mA : ∀ {L}, L ∈ famsAO δ b (j8DataGen p Rg Rt hgen O) o (acs_posG Rt hgen O) →
      L ∈ famsAllO δ b (j8DataGen p Rg Rt hgen O) o (cells_posG Rt hgen O) (acs_posG Rt hgen O) :=
    fun h => List.mem_append_right _ h
  exact
    { atomOK := fun χ hχ => atomOK_runG δ b Rt hgen O hpG _ _ _ _ hax hop5 h31 hclA hRt
        (mA (by simp [famsAO])) (mA (by simp [famsAO])) (mA (by simp [famsAO])) (mA (by simp [famsAO]))
        (mA (by simp [famsAO])) (mA (by simp [famsAO])) χ hχ
      awOK := fun χ hχ => awOK_runG δ b Rt hgen O _ _ _ _ hp63 h31 hwalkA
        (mA (by simp [famsAO])) (mA (by simp [famsAO])) χ hχ
      balG := fun χ hχ => balG_closedG δ b Rt hgen O o hpG hax hop5 hRt h31 hwalk
        (hI_runG δ b Rt hgen O o hpG hax hop5 hclA hRt h31)
        (fun χ _ => hA_runG δ b Rt hgen O o hpG hop5 hclA hRt h31 χ)
        (hJ_runG δ b Rt hgen O o hpG hax hRt h31) χ (goodAG δ b Rt hgen O o χ hχ)
      balV := fun χ hχ => balV_closedG δ b Rt hgen O o hpG hax hop5 hclA hRt h31 χ
        (goodAG δ b Rt hgen O o χ hχ)
      balF := fun χ hχ => balF_closedG δ b Rt hgen O o hpG hop5 hclA hRt h31 hwalk χ
        (goodAG δ b Rt hgen O o χ hχ) }

open Classical in
/-- **`complJ8_closedG`: J-8 general completeness at Goldilocks, nothing carried.** For every generated run
`hgen` of every program over every registry `Rg` whose called jets are registered in compiled form (`hRt`,
`hregAx`), under the run binders `hax hop5`, the claim binder `hclA`, the leaf binder `hleaf`, the walk-depth
binders `hwalk` (reads) and `hwalkA` (atom reads), and every table `≤ 2^31` rows (`h31`): at the run's honest record `BRunAG` (every
pole family, cell list and read lists in the orders `O`), honest
acceptance at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the claim holds, and at `|K| = cK` the figure
`ε_c < 2^-120` with a good coin. -/
theorem complJ8_closedG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataGen p Rg Rt hgen O).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    let B := BRunAG δ b Rt hgen O o
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  intro B
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨hOK, hpin, hcnt⟩ := famsAllO_facts δ b (K := K) (j8DataGen p Rg Rt hgen O) o
    (cells_posG Rt hgen O) (acs_posG Rt hgen O) h31
  have Ob := obligations_of_famsG δ b Rt hgen O hpG hp63 hax hop5 hclA hleaf hwalk hRt hregAx h31
    o (cells_posG Rt hgen O) (acs_posG Rt hgen O) _
    (fun L hL => List.mem_append_left _ hL) hOK hpin hcnt
    (openJ8_closedG δ b Rt hgen O o hpG hax hop5 hclA hwalk hwalkA hRt h31)
  refine ⟨fun χ hχ => ComplJ8.honest_accepted_J8_of_obligations δ b B Ob hp63 hax hop5 χ hχ,
    ComplJ8.probJ8_notGood_le δ b B Ob, Ob.staged, genX_sound Rg.faithful B.hgen, fun hcK => ?_⟩
  have hrows : ComplJ8.RowsLe31 B.Pb := rowsLe31_ofG δ b Rt hgen O _ _ _ _ _ h31
  have hfig := Ob.fig hpG hcK hrows
  obtain ⟨χ, hχ⟩ := ComplJ8.exists_good δ b B Ob (lt_trans hfig (by norm_num))
  exact ⟨hfig, χ, ComplJ8.honest_accepted_J8_of_obligations δ b B Ob hp63 hax hop5 χ hχ⟩

end Closed
end
end ComplJ8ClosedG_1

/-! ### Completeness over any admissible `J8Data` -/

section ClosedAny
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ComplJ8Obligations ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- An admissible datum has a nonempty cell list. -/
theorem J8DataOK.cells_pos {D : J8Data p Rg fuel s f r} (hOK : J8DataOK D) : 0 < D.cells.length := by
  obtain ⟨Rt, t, hgen, O, rfl⟩ := hOK
  exact cells_posG Rt hgen O

/-- An admissible datum has a nonempty atom cell list. -/
theorem J8DataOK.acs_pos {D : J8Data p Rg fuel s f r} (hOK : J8DataOK D) : 0 < D.acs.length := by
  obtain ⟨Rt, t, hgen, O, rfl⟩ := hOK
  exact acs_posG Rt hgen O

/-- **The honest record of an admissible datum with every family** (`BRunA` over `D`). -/
abbrev BRunA' (D : J8Data p Rg fuel s f r) (hOK : J8DataOK D) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) :
    HonestJ8 p K δ Rg fuel s f r :=
  honestJ8OfO δ b D o hOK.cells_pos hOK.acs_pos
    (avOfO δ b D o hOK.acs_pos)
    (famsAllO δ b D o hOK.cells_pos hOK.acs_pos)

/-- **`famsAll_facts'`**: the side conditions and the pin count of `famsAll` (already stated over any `D`). -/
theorem famsAll_facts' (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length)
    (hA : 0 < D.acs.length) (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) :
    (∀ L ∈ famsAllO δ b D o hC hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsAllO δ b D o hC hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsAllO δ b D o hC hA (K := K)).map nPins).sum ≤ 2 ^ 66 :=
  famsAllO_facts δ b D o hC hA h31

/-- **`obligations_of_fams'`**: the obligations at any family list containing `famsOf`, over an admissible
datum. -/
theorem obligations_of_fams' (D : J8Data p Rg fuel s f r) (hOK : J8DataOK D) (hpG : p = Nock.Atoms.p)
    (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p D.t) (hop5 : ProgOp5OK p D.t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK D.roots)
    (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hRt : ∀ id ∈ CalledIds D.t, Rg.R id = some ⟨(hOK.Rt id).toTemplate p,
      Nock.Jet.Autogen.compile p (hOK.Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (hOK.Rt id) = true ∧ (hOK.Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds D.t, ∀ i, (hOK.Rt id).ax i < p)
    (h31 : Rows31 D) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)
    (fams : List (List (BadSpec K)))
    (hsub : ∀ L ∈ famsOfO δ b D o hC, L ∈ fams)
    (hOKf : ∀ L ∈ fams, ∀ e ∈ L, e.OK) (hpin : ∀ L ∈ fams, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (hcnt : (fams.map nPins).sum ≤ 2 ^ 66)
    (OJ : OpenJ8 δ b (honestJ8OfO δ b D o hC hA (avOfO δ b D o hA) fams)) :
    ComplJ8Obligations δ b (honestJ8OfO δ b D o hC hA (avOfO δ b D o hA) fams) := by
  obtain ⟨Rt, t, hgen, O, rfl⟩ := hOK
  exact obligations_of_famsG δ b Rt hgen O hpG hp63 hax hop5 hclA hleaf hwalk hRt hregAx h31 o hC hA fams
    hsub hOKf hpin hcnt OJ

/-- **`openJ8_closed'`**: `OpenJ8` at `BRunA'`, over an admissible datum. -/
theorem openJ8_closed' (D : J8Data p Rg fuel s f r) (hOK : J8DataOK D) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hpG : p = Nock.Atoms.p)
    (hax : ProgAxOK p D.t) (hop5 : ProgOp5OK p D.t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hRt : ∀ id ∈ CalledIds D.t, Rg.R id = some ⟨(hOK.Rt id).toTemplate p,
      Nock.Jet.Autogen.compile p (hOK.Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (hOK.Rt id) = true ∧ (hOK.Rt id).WellTyped p)
    (h31 : Rows31 D) :
    OpenJ8 δ b (BRunA' δ b D hOK o (K := K)) := by
  obtain ⟨Rt, t, hgen, O, rfl⟩ := hOK
  exact openJ8_closedG δ b Rt hgen O o hpG hax hop5 hclA hwalk hwalkA hRt h31

open Classical in
/-- **`complJ8_closed'`: J-8 general completeness over any admissible `J8Data`.** For every datum `D` that is
the generator's output up to the order of its cell list and its two read lists (`J8DataOK D`), under the run
binders `hax hop5`, the claim binder `hclA`, the leaf binder `hleaf`, the walk-depth binders `hwalk hwalkA`, the
jet registration binders `hRt hregAx` (at `D`'s template table) and every table `≤ 2^31` rows (`h31`): at the
honest record `BRunA' D`, honest acceptance at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the claim holds,
and at `|K| = cK` the figure `ε_c < 2^-120` with a good coin. -/
theorem complJ8_closed' (D : J8Data p Rg fuel s f r) (hOK : J8DataOK D) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hpG : p = Nock.Atoms.p)
    (hax : ProgAxOK p D.t) (hop5 : ProgOp5OK p D.t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK D.roots)
    (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hRt : ∀ id ∈ CalledIds D.t, Rg.R id = some ⟨(hOK.Rt id).toTemplate p,
      Nock.Jet.Autogen.compile p (hOK.Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (hOK.Rt id) = true ∧ (hOK.Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds D.t, ∀ i, (hOK.Rt id).ax i < p)
    (h31 : Rows31 D) :
    let B := BRunA' δ b D hOK o (K := K)
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  obtain ⟨Rt, t, hgen, O, rfl⟩ := hOK
  exact complJ8_closedG δ b Rt hgen O o hpG hax hop5 hclA hleaf hwalk hwalkA hRt hregAx h31

open Classical in
/-- **Check: `complJ8_closed` is the instance of `complJ8_closed'` at the honest generator** (`j8DataOf_ok`,
identity orders); the statement is `ComplJ8Closed.complJ8_closed`'s, verbatim. -/
theorem complJ8_closed_of_any {Rt : ℕ → Nock.Jet.Autogen.Tpl} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    let B := BRunA δ b Rt hgen hpG h31 (K := K)
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ8_closed' δ b (j8DataOf p Rg Rt hgen) (j8DataOf_ok p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) hpG hax hop5 hclA hleaf hwalk hwalkA
    hRt hregAx h31

end ClosedAny

end

#print axioms complJ8_closed'
#print axioms openJ8_closed'
#print axioms obligations_of_fams'
#print axioms famsAll_facts'
#print axioms complJ8_closed_of_any
#print axioms j8DataOf_ok

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
