/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalSJ.lean

  **The J side of the service balance at the J-9 AL overlay `DL`.**
  * The J chip's service sub-balance at `DL` (`hJ_LJ`, the `ComplJ9ABalSO.hJ_runA` twin): the J calls' keys, the
    registry pins of the J ids and the J terminal sum to zero.  Twins of `ComplJ8OfBalJ.calls_ok`, `compile_mem`,
    `pins_prov`, `honest_cov`, `lay_statics`, `jrows_mv_facts`, `jrows_Fj` at `DL`, under the prim-aware binder
    `hRtJ` (`hRt` on the non-primitive called ids only).
  * The compute jet consumes split by the call id (`sum_jetT_L`): every `s11j` row's consume is the service weight
    of its row key (`jetT_row_gen`, no binder); a J id's key is `κc` (`hRtJ`), a primitive id's key is `κp`, the
    ALU hdr's `keyJet` provide `(id, 1, idxP id, 1, idx s, h(e), 3)` (`prim_key`: the registry formula is `primC op`
    (`hprim`), the subject is a cell (`AluCallOK.prim_row`, `hnoDec`), the id is `< p` (`hax9`)).
  * `old_part_L`: the `ComplJ9ABalS.old_part` twin with the jet total left open (no `hRt`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalS
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluCallOK

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalSJ

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module
open Nock.Jet.ChipJ8 Nock.Jet.Interp
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf mvFixP pinsOfP rowsOfT hdlP hJd)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (Rows31A BRun9A W9 N9 idOfA)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.RapJetJ8 (keyK dJ consKT provKT tlF)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sT)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.Prim (PrimOp primC primSpec)
open Nock.V1J8.Gen (callsOf idxOf atomV)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)

noncomputable section

/-! ## 1. The J chip at `DL` (no coin) -/

section RunJL
variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl)
  (prims : List (ℕ × PrimOp)) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "PIDS" => prims.map Prod.fst

theorem callsL_sub : ∀ cl ∈ (DL).calls, cl ∈ (DD).calls ∧ cl.1 ∉ PIDS :=
  fun cl hcl => jCallsP_sub _ _ cl hcl

theorem regsL_sub : ∀ id ∈ (DL).regs, id ∈ (DD).regs := by
  intro id hid
  rw [F_regs] at hid
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
  exact List.mem_dedup.mpr (List.mem_map_of_mem (callsL_sub Rt prims hgen cl hcl).1)

theorem idxL : (DL).idx = fun id => idxOf (DL).cells (compile p (Rt id)) := rfl

/-- `ComplJ8OfBalJ.calls_ok` at `DL` under `hRtJ`. -/
theorem calls_okL (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ cl ∈ (DL).calls, (Rt cl.1).WellTyped p ∧ axPosB (Rt cl.1) = true ∧
      (∃ r, (Rt cl.1).sem p cl.2 = some r) ∧ cl.1 ∈ (DL).regs := by
  intro cl hcl
  obtain ⟨hcl0, hns⟩ := callsL_sub Rt prims hgen cl hcl
  have hid := ComplJ8Of.calls_called hgen cl hcl0
  have hc := callsL_of_hRt Rt prims hgen hRtJ cl hcl
  refine ⟨hc.1, (hRtJ _ hid hns).2.1, hc.2, ?_⟩
  rw [F_regs]
  exact List.mem_dedup.mpr (List.mem_map_of_mem hcl)

/-- `ComplJ8OfBalJ.pins_prov` at `DL`. -/
theorem pins_provL :
    ∀ κ ∈ pinsOfP p (DL).regs (DL).idx,
      ∃ x' ∈ honestJ8G (p := p) (hJd p (DL).cells (DL).acs) Rt (DL).regs (DL).calls, ∃ κ0 ∈ provK x', κ = tlF κ0 := by
  intro κ hκ
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hκ
  refine ⟨⟨regPre id, mkW 0 1 0 0 0 (hJd p (DL).cells (DL).acs (compile p (Rt id))) (0, 0) (0, 0)⟩, ?_, _,
    List.mem_singleton_self _, ?_⟩
  · unfold honestJ8G
    exact List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩)
  · obtain ⟨a, c, hac⟩ := ComplJ8Data.compile_isCell p (Rt id)
    rw [idxL]
    congr 1
    simp only [Nock.Jet.PinJ8.pinKey, mkW]
    rw [hac]
    simp [keyRg, KE.ev, colOf, Col.id, Col.kN, Col.vN, regPre, hJd, hdlP, hac]

/-- `ComplJ8OfBalJ.honest_cov` at `DL`. -/
theorem honest_covL (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ honestJ8G (p := p) (hJd p (DL).cells (DL).acs) Rt (DL).regs (DL).calls,
      ∀ κ ∈ consK x, ∃ x' ∈ honestJ8G (p := p) (hJd p (DL).cells (DL).acs) Rt (DL).regs (DL).calls,
        κ ∈ provK x' :=
  honestJ8_cov _ (fun v hv => by simpa using ComplJ8Data.hJd_small p _ _ v hv) Rt _ _ (calls_okL Rt prims hgen hRtJ)

/-- `ComplJ9ABalSO.lay_statics_A` at `DL`. -/
theorem lay_staticsL (hax9 : ProgAxOK9A p t)
    (hJl : (DL).jrows.length < p) (hbl : (bfsForest [t]).length < p)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    (∀ q ∈ layoutJ8 Rt (DL).regs (DL).ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt (DL).regs (DL).ids).filterMap tvKey).Nodup := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := callsL_of_hRt Rt prims hgen hRtJ
  have hlt : ∀ cl ∈ (DL).calls, cl.1 < p := fun cl hcl =>
    ComplJ9AOfStatic.calls_lt9 hgen hax9 cl (callsL_sub Rt prims hgen cl hcl).1
  have hmemR : ∀ id ∈ (DL).regs, ∃ cl ∈ (DL).calls, cl.1 = id := by
    intro id hid
    rw [F_regs] at hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
    exact ⟨cl, hcl, e⟩
  have hJlen : (layoutJ8 Rt (DL).regs (DL).ids).length < p := by
    rw [← jrows_preL Rt prims hgen, List.length_map]
    exact hJl
  have hidsl : (DL).ids.length < p := by
    have h1 : (DL).ids.length ≤ (bfsForest [t]).length := by
      rw [F_ids, F_calls, List.length_map]
      unfold jCallsP
      refine (List.length_filter_le _ _).trans ?_
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp)
    exact lt_of_le_of_lt h1 hbl
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (DL).regs (DL).calls hcalls hlt hJlen
  refine ⟨ComplJ8Jet.hsmall_of_blocks Rt _ _ (fun i hi => ?_) hidsl (fun i hi => (hblk i hi).2) hp,
    ComplJ8Jet.huniq_of_blocks Rt _ _ (fun i hi => (hblk i hi).1)⟩
  obtain ⟨cl, hcl', rfl⟩ := hmemR i hi
  exact hlt cl hcl'

/-- `ComplJ9ABalSO.jrows_mv_facts_A` at `DL`. -/
theorem jrows_mv_factsL (hax9 : ProgAxOK9A p t)
    (hJl : (DL).jrows.length < p) (hbl : (bfsForest [t]).length < p)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((DL).jrows.flatMap provKT).Nodup ∧
    (∀ κ ∈ (DL).jrows.flatMap consKT ++ pinsOfP p (DL).regs (DL).idx, κ ∈ (DL).jrows.flatMap provKT) ∧
    (∀ x ∈ (DL).jrows, ∀ κ ∈ provKT x,
      x.w.mv = (((((DL).jrows.flatMap consKT).count κ + (pinsOfP p (DL).regs (DL).idx).count κ : ℕ)) : ZMod p)) := by
  obtain ⟨hsmall, huniq⟩ := lay_staticsL Rt prims hgen hax9 hJl hbl hRtJ
  rw [F_jrows]
  refine ⟨?_, hcov_fix _ _ (honest_covL Rt prims hgen hRtJ) (pins_provL Rt prims hgen), hmv_fix _ _⟩
  rw [flatMap_provKT_fix]
  rw [F_regs]
  exact hnd_rows Rt _ _ _ (ComplJ8Jet.honestJ8_pre _ Rt _ _) hsmall huniq (List.nodup_dedup _)

end RunJL

/-! ## 2. The service pairing at `DL` -/

section HJL
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "PIDS" => prims.map Prod.fst

/-- `ComplJ8OfBalJ.jrows_Fj` at `DL`. -/
theorem jrows_FjL (chals : ℕ → K)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((DL).jrows.map (Fj δ chals)).sum =
      ((DL).calls.map fun cl => dJ δ chals (κc Rt (hJd p (DL).cells (DL).acs) cl)).sum := by
  have hok := calls_okL Rt prims hgen hRtJ
  rw [F_jrows, mvFixP_eq, List.map_map]
  have e1 : (Fj δ chals) ∘ (fun r => setMv r (mvOf (honestJ8G (p := p) (hJd p (DL).cells (DL).acs) (DL).Rt
      (DL).regs (DL).calls) (pinsOfP p (DL).regs (DL).idx) r)) = Fj δ chals := by
    funext x; simp only [Function.comp, Fj, sT, ents3_setMv]; rfl
  rw [e1]
  unfold honestJ8G
  rw [List.map_append, List.sum_append, List.sum_eq_zero (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    simp [Fj, sT, ents3_nocall, regPre]), zero_add, Nock.Jet.RapJetJ8.sum_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 (DL).calls, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  obtain ⟨⟨i, s0⟩, c⟩ := q
  obtain ⟨hT, -, ⟨r0, hsem⟩, -⟩ := hok _ (List.fst_mem_of_mem_zipIdx hq)
  exact blockW_Fj δ Rt chals (hJd p (DL).cells (DL).acs) c i s0 hT r0 hsem

/-- **The J chip's service sub-balance at `DL`** (`ComplJ9ABalSO.hJ_runA` at the overlay, binder `hRtJ`): the J
calls' keys, the registry pins of the J ids and the J terminal sum to zero, at every coin. -/
theorem hJ_LJ (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (h31 : Rows31A (DL))
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) :
    ((DL).calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))).sum +
      ((pinCons (p := p) (K := K) (DL).regs (DL).idx).map
        fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (pubsJOf δ (DL) χ 0) (pubsJOf δ (DL) χ 1) = 0 := by
  have hJl : (DL).jrows.length < p :=
    ComplJ9AOfStatic.lt_p hpG (h31 _ (List.mem_append_left _ (by simp [sizesJ8])))
  have hbl : (bfsForest [t]).length < p :=
    ComplJ9AOfStatic.lt_p hpG (h31 _ (List.mem_append_left _ List.mem_cons_self))
  have eJ : Quad.mk _ (pubsJOf δ (DL) χ 0) (pubsJOf δ (DL) χ 1) =
      ∑ k, termJ δ (VerJ8.chalsJJ8 χ) ((DL).jrows.get k) := by
    have e0 : pubsJOf δ (DL) χ 0 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) ((DL).jrows.get k)) 0 := by
      simp [pubsJOf]
    have e1 : pubsJOf δ (DL) χ 1 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) ((DL).jrows.get k)) 1 := by
      simp [pubsJOf]
    rw [e0, e1, pub2_mk]
  obtain ⟨hnd, hcov, hmv⟩ := jrows_mv_factsL Rt prims hgen hax9 hJl hbl hRtJ
  have hT := Nock.Jet.ChipJ8T.HonestBal.termJ_sum_of_mv_fin δ (VerJ8.chalsJJ8 χ) (DL).jrows.get
    (pinsOfP p (DL).regs (DL).idx) (by rw [List.ofFn_get]; exact hnd) (by rw [List.ofFn_get]; exact hcov)
    (by rw [List.ofFn_get]; exact hmv)
  rw [List.ofFn_get] at hT
  have hF := jrows_FjL δ Rt prims hgen (VerJ8.chalsJJ8 χ) hRtJ
  have eP : ((pinCons (p := p) (K := K) (DL).regs (DL).idx).map
      fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum =
      ((pinsOfP p (DL).regs (DL).idx).map (dJ δ (VerJ8.chalsJJ8 χ))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]
    simp only [pinCons, pinsOfP, List.map_map]
    rfl
  have eCJ : ((DL).calls.map fun cl =>
      ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))).sum =
      ((DL).calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc Rt (hJd p (DL).cells (DL).acs) cl)).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]; rfl
  have hF' : ((DL).jrows.map fun r => liftQ δ r.w.m * sT δ (VerJ8.chalsJJ8 χ) Nock.Jet.ChipJ8.ents3 r).sum =
      ((DL).calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl)).sum := hF
  rw [eP, eJ, hT, eCJ, hF']
  ring

end HJL

/-! ## 3. The compute jet consumes, split by the call id -/

section Rows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The compute `keyJet` consume of a row**: `jetRecX` at the row's handles `(v(sf1), h(ftt), h(s), h(e), 3)`. -/
def kRow (H : Noun → ℕ × ℕ) (rr : RowNX) : List (ZMod p) :=
  [HonestCompX.hv (F := ZMod p) H rr.sf1, HonestCompX.hk (F := ZMod p) H rr.ftt,
    HonestCompX.hv (F := ZMod p) H rr.ftt, HonestCompX.hk (F := ZMod p) H rr.s, HonestCompX.hv (F := ZMod p) H rr.s,
    HonestCompX.hk (F := ZMod p) H rr.e, HonestCompX.hv (F := ZMod p) H rr.e, ((3 : ℕ) : ZMod p)]

/-- A node's jet consume (`0` off `s11j`). -/
def Fk (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (u : NTree SkelX) : 𝕂′ :=
  if (rowOfSkelX u.label).st = .s11j then ComplJ8Bal.fS δ b χ (keyK 8 (kRow (p := p) H (rowOfSkelX u.label))) else 0

/-- **A compute row's jet consume is the service weight of its row key** (no binder; `jetT_row` before `hRt`). -/
theorem jetT_row_gen (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (W : List (NTree SkelX)) (j : ℕ) (hj : j < W.length) :
    ComplJ8OfBalG.jetT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j = Fk δ b H χ (W[j]'hj) := by
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj, hrr]
  have htr : (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX H pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT H pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold ComplJ8OfBalG.jetT
  rw [DX_jet δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 16 (by decide)]
  have hmap : ∀ tr : ℕ → ZMod p, ChipHX.jetRecX.map (ChipHX.RE.ev tr) =
      [tr 32, tr 41, tr 42, tr 25, tr 26, tr 29, tr 30, ((3 : ℕ) : ZMod p)] := fun tr => rfl
  rw [hmap]
  simp only [HonestCompX.cxSf1_v, HonestCompX.cxFtt_k, HonestCompX.cxFtt_v, HonestCompX.cxS_k,
    HonestCompX.cxS_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  unfold Fk
  by_cases hst : rr.st = .s11j
  · rw [if_pos hst, ← hrr, if_pos (by rw [hst]; rfl), map_one, one_mul]
    rfl
  · have h16 : RowDecodeVSX.stIdx rr.st ≠ 16 := by
      intro h; apply hst; revert h; cases rr.st <;> simp [RowDecodeVSX.stIdx]
    rw [if_neg h16, ← hrr, if_neg hst]
    simp

/-- The total of the node consumes over the BFS forest. -/
theorem sum_jetT_gen (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (t : NTree SkelX) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        pubVal j = ((bfsForest [t]).map (Fk δ b H χ)).sum := by
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b H pd (bfsForest [t])
      (VerJ8.chalVJ8 b χ) pubVal j = Fk δ b H χ ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [jetT_row_gen δ b H pd χ pubVal _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t]

/-- **The ALU hdr's `keyJet` provide of a primitive call** `(id, s, e)`: `(id, 1, idxP id, 1, idx s, h(e), 3)`
(`AluHonestRows.hdrRow` at `callsLOf`). -/
def κp (prims : List (ℕ × PrimOp)) (cs : List Noun) (H : Noun → ℕ × ℕ) (x : ℕ × Noun × Noun) : List (ZMod p) :=
  [((x.1 : ℕ) : ZMod p), 1, ((idxPOf cs prims x.1 : ℕ) : ZMod p), 1, ((idxOf cs x.2.1 : ℕ) : ZMod p),
    (((H x.2.2).1 : ℕ) : ZMod p), (((H x.2.2).2 : ℕ) : ZMod p), ((3 : ℕ) : ZMod p)]

theorem primC_cell (op : PrimOp) : ∃ a c, primC op = .cell a c := by
  cases op <;> exact ⟨_, _, rfl⟩

theorem filterMap_ite_split {α β M : Type} [AddCommMonoid M] (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : α → β) (g : β → M) (l : List α) :
    (l.map fun x => if P x ∧ Q x then g (h x) else 0).sum =
      ((l.filterMap fun x => if P x ∧ Q x then some (h x) else none).map g).sum :=
  sum_filterMap_ite (fun x => P x ∧ Q x) h g l

variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "PIDS" => prims.map Prod.fst

/-- The J part of a node's consume. -/
def FJ (χ : Coins frameJ8 K) (u : NTree SkelX) : 𝕂′ :=
  if (rowOfSkelX u.label).st = .s11j ∧ atomV (rowOfSkelX u.label).sf1 ∉ PIDS then
    ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs)
      (atomV (rowOfSkelX u.label).sf1, (rowOfSkelX u.label).s)))
  else 0

/-- The primitive part of a node's consume. -/
def FP (χ : Coins frameJ8 K) (u : NTree SkelX) : 𝕂′ :=
  if (rowOfSkelX u.label).st = .s11j ∧ atomV (rowOfSkelX u.label).sf1 ∈ PIDS then
    ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H
      (atomV (rowOfSkelX u.label).sf1, (rowOfSkelX u.label).s, (rowOfSkelX u.label).e)))
  else 0

/-- **A primitive call's compute key is the ALU hdr's `keyJet` provide** (the keys MATCH). -/
theorem prim_key (hax9 : ProgAxOK9A p t)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {u : NTree SkelX} (hu : u ∈ bfsForest [t]) (hst : (rowOfSkelX u.label).st = .s11j)
    (hid : atomV (rowOfSkelX u.label).sf1 ∈ PIDS) :
    kRow (p := p) (DD).H (rowOfSkelX u.label) =
      κp (p := p) prims (DL).cells (DL).H (atomV (rowOfSkelX u.label).sf1, (rowOfSkelX u.label).s, (rowOfSkelX u.label).e) := by
  set rr := rowOfSkelX u.label with hrr
  have hin : InTree t u := Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton hu
  have hsem := inTree_rowSem hgen hin
  unfold RowNX.SemN at hsem
  rw [← hrr, hst] at hsem
  obtain ⟨-, -, -, -, id, j, -, hft, hRj, hjc, -⟩ := hsem
  have hrowM : rr ∈ (rowsOfT t).toList := by
    simp only [rowsOfT, List.toList_toArray]
    exact List.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨x, y, n, hs, he, -, -⟩ := AluCallOK.prim_row hgen hnd hprim hnoDec hrowM hst hid
  have hcl : (id, rr.s) ∈ callsOf (rowsOfT t) := by
    unfold Nock.V1J8.Gen.callsOf
    exact List.mem_filterMap.mpr ⟨rr, hrowM, by simp [hst, hft, atomV]⟩
  have hidp : id < p := ComplJ9AOfStatic.calls_lt9 hgen hax9 _ hcl
  rw [hft] at hid
  obtain ⟨q, hq, hq1'⟩ := List.mem_map.mp hid
  have hq1 : q.1 = id := hq1'
  have hop : opOf prims id = q.2 := by rw [← hq1]; exact opOf_of_mem hnd hq
  rw [← hq1, hprim q hq] at hRj
  have hj : j = primSpec q.2 := (Option.some.inj hRj).symm
  subst hj
  have hftt : rr.ftt = primC q.2 := hjc.symm
  obtain ⟨a, c, hac⟩ := primC_cell q.2
  have hH : (DD).H = hdlP p (DL).cells (DL).acs := rfl
  have hHL : (DL).H = hdlP p (DL).cells (DL).acs := rfl
  simp only [kRow, κp, hft, hftt, hs, atomV, HonestCompX.hv, HonestCompX.hk, hH, hHL, hdlP, hidp, if_true,
    idxPOf, hop, hac]
  simp

/-- **Per node: the consume is the J part plus the primitive part.** -/
theorem Fk_split (hax9 : ProgAxOK9A p t)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (χ : Coins frameJ8 K) {u : NTree SkelX} (hu : u ∈ bfsForest [t]) :
    Fk δ b (DD).H χ u = FJ δ b Rt prims hgen χ u + FP δ b Rt prims hgen χ u := by
  unfold Fk FJ FP
  by_cases hst : (rowOfSkelX u.label).st = .s11j
  · by_cases hid : atomV (rowOfSkelX u.label).sf1 ∈ PIDS
    · rw [if_pos hst, if_neg (fun h => h.2 hid), if_pos ⟨hst, hid⟩, zero_add,
        prim_key Rt prims hgen hax9 hnd hprim hnoDec hu hst hid]
    · rw [if_pos hst, if_pos ⟨hst, hid⟩, if_neg (fun h => hid h.2), add_zero]
      set rr := rowOfSkelX u.label with hrr
      have hin : InTree t u := Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton hu
      have hsem0 := inTree_rowSem hgen hin
      unfold RowNX.SemN at hsem0
      rw [← hrr, hst] at hsem0
      obtain ⟨-, -, -, -, id, j, -, hft, hRj, hjc, hrel⟩ := hsem0
      have hcalled : id ∈ CalledIds t := ⟨u, hin, hst, hft⟩
      rw [hft] at hid
      rw [(hRtJ id hcalled (by simpa [atomV] using hid)).1] at hRj
      cases Option.some.inj hRj
      have hrowM : rr ∈ (rowsOfT t).toList := by
        simp only [rowsOfT, List.toList_toArray]
        exact List.mem_map.mpr ⟨u, hu, rfl⟩
      have hcl : (id, rr.s) ∈ callsOf (rowsOfT t) := by
        unfold Nock.V1J8.Gen.callsOf
        exact List.mem_filterMap.mpr ⟨rr, hrowM, by simp [hst, hft, atomV]⟩
      have hidp : id < p := ComplJ9AOfStatic.calls_lt9 hgen hax9 _ hcl
      have hsemR : (Rt id).sem p rr.s = some rr.e := hrel
      have hres : res Rt p (id, rr.s) = rr.e := by simp [res, hsemR]
      have hidv : HonestCompX.hv (F := ZMod p) (DD).H (.atom id) = (id : ZMod p) := by
        show (((hdlP p (DD).cells (DD).acs (.atom id)).2 : ℕ) : ZMod p) = _
        simp [hdlP, hidp]
      congr 2
      simp only [kRow, κc, hres, atomV, hft, hidv, ← hjc]
      rfl
  · rw [if_neg hst, if_neg (fun h => hst h.1), if_neg (fun h => hst h.1), add_zero]

theorem jCalls_filterMap (pids : List ℕ) (l : List RowNX) :
    jCallsP pids (l.filterMap fun r => if r.st = .s11j then some (atomV r.sf1, r.s) else none) =
      l.filterMap fun r => if r.st = .s11j ∧ atomV r.sf1 ∉ pids then some (atomV r.sf1, r.s) else none := by
  unfold jCallsP
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : a.st = .s11j <;> by_cases h2 : atomV a.sf1 ∈ pids <;>
      simp_all [List.filterMap_cons, List.filter_cons]

/-- The J parts total the J calls' keys. -/
theorem sum_FJ (χ : Coins frameJ8 K) :
    ((bfsForest [t]).map (FJ δ b Rt prims hgen χ)).sum =
      ((DL).calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))).sum := by
  have e : (bfsForest [t]).map (FJ δ b Rt prims hgen χ) = ((bfsForest [t]).map fun u => rowOfSkelX u.label).map
      (fun rr => if rr.st = .s11j ∧ atomV rr.sf1 ∉ PIDS then
        ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) (atomV rr.sf1, rr.s))) else 0) := by
    rw [List.map_map]; rfl
  rw [e, filterMap_ite_split (fun rr : RowNX => rr.st = .s11j) (fun rr => atomV rr.sf1 ∉ PIDS)
    (fun rr => (atomV rr.sf1, rr.s)) (fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))),
    F_calls, ← jCalls_filterMap]
  rfl

/-- The primitive parts total the ALU calls' keys. -/
theorem sum_FP (χ : Coins frameJ8 K) :
    ((bfsForest [t]).map (FP δ b Rt prims hgen χ)).sum =
      ((pcallsR PIDS (rowsOfT t)).map fun x => ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H x))).sum := by
  have e : (bfsForest [t]).map (FP δ b Rt prims hgen χ) = ((bfsForest [t]).map fun u => rowOfSkelX u.label).map
      (fun rr => if rr.st = .s11j ∧ atomV rr.sf1 ∈ PIDS then
        ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H (atomV rr.sf1, rr.s, rr.e))) else 0) := by
    rw [List.map_map]; rfl
  rw [e, filterMap_ite_split (fun rr : RowNX => rr.st = .s11j) (fun rr => atomV rr.sf1 ∈ PIDS)
    (fun rr => (atomV rr.sf1, rr.s, rr.e)) (fun x => ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H x)))]
  rfl

/-- **The compute jet total, split**: the J calls' keys plus the primitive calls' ALU keys. -/
theorem sum_jetT_L (hax9 : ProgAxOK9A p t)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (DD).H (DD).pd (bfsForest [t])
        (VerJ8.chalVJ8 b χ) pubVal j =
      ((DL).calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))).sum +
      ((pcallsR PIDS (rowsOfT t)).map fun x => ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H x))).sum := by
  rw [sum_jetT_gen, List.map_congr_left (fun u hu => Fk_split δ b Rt prims hgen hax9 hRtJ hnd hprim hnoDec χ hu),
    List.sum_map_add, sum_FJ, sum_FP]

end Rows

/-! ## 4. The inc total at `DL` and the old part -/

section Old
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (incT9 jetT9 awT9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
  (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

include hpG h31A in
/-- **The inc service total at `DL`** (`ComplJ9ABalSO.hI9_A` at the overlay data, its own atom orbit): the compute's
inc consumes total the overlay atom table's `MI` public. -/
theorem incT_L (hF : DvdOK (DL)) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.incT δ b (DD).H (DD).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (pubsAOf δ b (DL) (acsL_pos Rt prims hgen) (orbJ8 (DL) hF) χ AtomChipHQ.pubMI)
        (pubsAOf δ b (DL) (acsL_pos Rt prims hgen) (orbJ8 (DL) hF) χ (AtomChipHQ.pubMI + 1)) := by
  have hmA : (DL).acs.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hinjA := (powN_ok (orbJ8 (DL) hF) (le_two_pow_ht (DL) hmA)).1
  have hN : (DD).rows.size ≤ 2 ^ 31 := by
    subst hpG; exact ComplJ9ATables.rows_leA Rg Rt hgen (ComplJ9ARun.rows31_of_A h31A)
  exact ComplJ9ABalSO.hI9_A δ b Rt hgen hpG hN (DL) rfl rfl rfl rfl
    (ComplJ9ABalSO.incInfoOK_runA Rt hgen hpG hN) (ComplJ9ABalSO.idxOOK_runA Rt hgen hpG hN _)
    (acsL_pos Rt prims hgen) _ hinjA χ pubVal

include hpG h31A in
/-- **`old_part` at the overlay, jet total open** (no `hRt`): the J-9 A rows' old-row `.s` terms are the overlay atom
table's `MI`, the jet consumes and the atom-walk pair reads. -/
theorem old_part_L (hF : DvdOK (DL)) (χ : Coins frameJ8 K) :
    ∑ j ∈ Finset.range (N9 t),
        (incT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          jetT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          awT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) =
      Quad.mk _ (pubsAOf δ b (DL) (acsL_pos Rt prims hgen) (orbJ8 (DL) hF) χ AtomChipHQ.pubMI)
        (pubsAOf δ b (DL) (acsL_pos Rt prims hgen) (orbJ8 (DL) hF) χ (AtomChipHQ.pubMI + 1)) +
      ∑ j ∈ Finset.range (bfsForest [t]).length,
        ComplJ8OfBalG.jetT δ b (DD).H (DD).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
      ((DD).preads.map fun x => ComplJ9BBalG.WA9 δ (DD) χ x).sum := by
  have h1 := ComplJ9ABalS.old_sum_transfer δ (K := K) b (DA).H (DA).pd (idOfA (p := p) Rt hgen) χ (fun _ => 0) hgen
  have hI := incT_L δ b Rt prims hgen hpG h31A hF χ (fun _ => 0)
  have hA := ComplJ9ABalSO.awSum_A δ b Rt hgen hpG χ (fun _ => 0)
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  erw [hI, hA]
  rfl

end Old

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalSJ
