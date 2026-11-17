/-

  * (i) inc: `opsOK_runA`, `idxOOK_runA`, `incInfoOK_runA`, `incT_run_A`, `incT_total_A`, `hI9_A` (J-9 B's
    `hI9` copies with the run binders `hax hop5` dropped: their only use was `SmallX` at an OP4 row, which is
    `True`; `ComplJ9ATables.genHypA` / `s4_rowA`), and `incT_BA`: the inc consumes total the atom table's `MI`
    public at `BRun9A`, rewritten via `ComplJ9AOfMem.pubsA_eq`-free `rfl` projection to `pubsAOf DA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalV2
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfStatic
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO

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
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

noncomputable section

section Inc
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- `ComplJ9BBalG.opsOK_run` with no run binder. -/
theorem opsOK_runA (hpG : p = Nock.Atoms.p) (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    OpsOK p (j8DataOf p Rg Rt hgen).rows (j8DataOf p Rg Rt hgen).acs := by
  intro vc hvc
  subst hpG
  have hg := ComplJ9ATables.genHypA Rg Rt hgen hN
  have hl : ∀ a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs, 2 ≤ (Nock.Atoms.limbs a).length := by
    intro a ha
    have : Nock.Atoms.B ≤ Nock.Atoms.p := by simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
    exact HonestPairX.two_le_length_limbs (by have := hg.big a ha; omega)
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have hm := (hg.ops vc hvc).1 hp
    exact ComplJ8OfBal.comb_mem_acs Rt hgen rfl hm (hl _ hm)
  · obtain ⟨h1, h2⟩ := (hg.ops vc hvc).2 hp
    exact ⟨hg.big _ h1, ComplJ8OfBal.comb_mem_acs Rt hgen rfl h1 (hl _ h1),
      ComplJ8OfBal.comb_mem_acs Rt hgen rfl h2 (hl _ h2)⟩

/-- `ComplJ9BBalG.idxOOK_run` with no run binder. -/
theorem idxOOK_runA (hpG : p = Nock.Atoms.p) (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) (mb : Array ℕ) :
    IdxOOK ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r) := by
  subst hpG
  intro vc hvc hp hk
  rw [newBA_idxO]
  have h := ComplJ8Atom.idxO_root _ _ _ _ (ComplJ9ATables.genHypA Rg Rt hgen hN) vc hvc hp
  exact congrArg (fun n : ℕ => (n : ZMod Nock.Atoms.p)) h

/-- `ComplJ9BBalG.incInfoOK_run` with no run binder. -/
theorem incInfoOK_runA (hpG : p = Nock.Atoms.p) (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    IncInfoOK p (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows)
      (j8DataOf p Rg Rt hgen).info := by
  refine incInfoOK_infoOfP p _ _ fun vc hvc hp => ?_
  obtain ⟨h1, -, -⟩ := (opsOK_runA Rt hgen hpG hN vc hvc).2 hp
  have : Nock.Atoms.B ≤ p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  exact ⟨HonestPairX.two_le_length_limbs (by omega), HonestPairX.two_le_length_limbs (by omega)⟩

/-- `ComplJ8OfBalG.incT_run` with no run binder (`s4_rowA`). -/
theorem incT_run_A (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      (optI p (rowOfSkelX ((bfsForest [t])[j]'hj).label)).elim 0 (FI δ (j8DataOf p Rg Rt hgen) χ) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ (ComplJ8Data.rowsOfT t).toList := by
    simp only [hrr, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH : HonestCompX.HdlOK p D.H := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold incT
  rw [DX_inc δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 4 (by decide)]
  simp only [HonestCompX.cx61, HonestCompX.cxSf1_k, HonestCompX.cxSf1_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  by_cases hst : rr.st = .s4
  · obtain ⟨n, h1, h2⟩ := ComplJ9ATables.s4_rowA hgen p hrowm hst
    have ho : optI p rr = if p ≤ n + 1 then some n else none := by
      unfold optI; rw [hst, h1]
    rw [ho]
    simp only [HonestCompX.cFast, hst, h2, RowDecodeVSX.stIdx, if_true]
    by_cases hp : p ≤ n + 1
    · have hb := hH.big (n + 1) hp
      rw [if_pos hp, if_neg (by omega)]
      simp only [Option.elim, FI, h1, HonestCompX.hk, HonestCompX.hv, hb, sub_zero, mul_one, map_one, one_mul]
    · have hs := hH.small (n + 1) (by omega)
      rw [if_neg hp, if_pos (by rw [hs])]
      simp
  · have ho : optI p rr = none := by
      unfold optI
      cases h : rr.st <;> simp_all
    rw [ho, if_neg]
    · simp
    · cases h : rr.st <;> simp_all [RowDecodeVSX.stIdx]

/-- `ComplJ8OfBalG.incT_total` with no run binder. -/
theorem incT_total_A (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows).map fun vc =>
        (vc.2 : 𝕂′) * FI δ (j8DataOf p Rg Rt hgen) χ vc.1).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => (optI p (rowOfSkelX u.label)).elim 0 (FI δ D χ) with hg
  have hrow : ∀ j ∈ Finset.range W.length,
      incT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [incT_run_A δ b Rt hgen χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g, hg,
    sum_filterMap_elim (fun u => optI p (rowOfSkelX u.label)) (FI δ D χ) W, sum_count_dedup]
  have hrows : D.rows.toList = W.map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT, hW]
  have hvs : D.rows.toList.filterMap (optI p) = W.filterMap fun u => optI p (rowOfSkelX u.label) := by
    rw [hrows, List.filterMap_map]; rfl
  show _ = (((D.rows.toList.filterMap (optI p)).dedup.map fun v =>
    (v, (D.rows.toList.filterMap (optI p)).count v)).map fun vc => (vc.2 : 𝕂′) * FI δ D χ vc.1).sum
  rw [hvs]

set_option maxHeartbeats 2000000 in
/-- **`hI9` at general limbs, no run binder** (`ComplJ9BBalG.hI9` with `opsOK_runA`, `incT_total_A`). -/
theorem hI9_A (hpG : p = Nock.Atoms.p) (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (D : J8Data p Rg fuel s f r)
    (hr : D.rows = (j8DataOf p Rg Rt hgen).rows) (ha : D.acs = (j8DataOf p Rg Rt hgen).acs)
    (hH : D.H = (j8DataOf p Rg Rt hgen).H) (hc : D.cells = (j8DataOf p Rg Rt hgen).cells)
    (hinfo : IncInfoOK p D.acs (ComplJ8Data.incOpsP p D.rows) D.info) (hidxO : IdxOOK D)
    (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubMI) (pubsAOf δ b D hA o χ (AtomChipHQ.pubMI + 1)) := by
  obtain ⟨-, -, -, -, -, tMI⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  have hops : OpsOK p D.rows D.acs := by
    rw [hr, ha]; exact opsOK_runA Rt hgen hpG hN
  have hHdl : D.H = ComplJ8Data.hdlP p D.cells D.acs := by rw [hH, hc, ha]; rfl
  have hFI : FI δ D χ = FI δ (j8DataOf p Rg Rt hgen) χ := by funext v; simp only [FI, hH]
  rw [tMI, incSum_eq9 δ b hpG D hHdl hinfo hops hidxO hA o hinj χ _, incT_total_A δ b Rt hgen χ _, hFI, hr]

end Inc

section AtBA
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

/-- **(i) The inc service total at `BRun9A`** (`hI9` at `DA`, orbit `orbJ8 DA`): the compute's inc consumes total the
atom table's `MI` public.  Binders: `hpG h31A` (via the `BRun9A` record) only. -/
theorem incT_BA (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (((BA).M χ).pubsA AtomChipHQ.pubMI) (((BA).M χ).pubsA (AtomChipHQ.pubMI + 1)) := by
  have hmA : (DA).acs.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hinjA := (powN_ok (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (le_two_pow_ht (DA) hmA)).1
  show _ = Quad.mk _ (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen)
      (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ AtomChipHQ.pubMI)
    (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ
      (AtomChipHQ.pubMI + 1))
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    subst hpG; exact ComplJ9ATables.rows_leA Rg Rt hgen (rows31_of_A h31A)
  exact hI9_A δ b Rt hgen hpG hN (DA) rfl rfl rfl rfl (by
      have := incInfoOK_runA Rt hgen hpG hN
      exact this) (idxOOK_runA Rt hgen hpG hN _) (ComplJ9ADataRec.acsA_pos Rt hgen) _ hinjA χ pubVal

end AtBA

section Jet
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic (calls_lt9 lt_p p63 mem_jrows mem_bfs)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.RapJetJ8 (keyK dJ consKT provKT tlF)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sT)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- `ComplJ8OfBalJ.lay_statics` at the J-9 A binders: `hax9` for `calls_lt9`, the two size bounds as hypotheses
(at `BRun9A` they come from `h31A` by `lt_p`, `mem_jrows`, `mem_bfs`). -/
theorem lay_statics_A (hp63 : 2 ^ 63 < p) (hax9 : ProgAxOK9A p t)
    (hJl : (j8DataOf p Rg Rt hgen).jrows.length < p) (hbl : (bfsForest [t]).length < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    (∀ q ∈ layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids,
      q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).filterMap tvKey).Nodup := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hlt := calls_lt9 hgen hax9
  have hmemR : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∃ cl ∈ (j8DataOf p Rg Rt hgen).calls, cl.1 = id := by
    intro id hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
    exact ⟨cl, hcl, e⟩
  have hJlen : (layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).length < p := by
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen, List.length_map]
    exact hJl
  have hidsl : (j8DataOf p Rg Rt hgen).ids.length < p := by
    have h1 : (j8DataOf p Rg Rt hgen).ids.length ≤ (bfsForest [(j8DataOf p Rg Rt hgen).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 hbl
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls
    hcalls hlt hJlen
  refine ⟨ComplJ8Jet.hsmall_of_blocks Rt _ _ (fun i hi => ?_) hidsl (fun i hi => (hblk i hi).2) hp,
    ComplJ8Jet.huniq_of_blocks Rt _ _ (fun i hi => (hblk i hi).1)⟩
  obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'

/-- `ComplJ8OfBalJ.jrows_mv_facts` at the J-9 A binders. -/
theorem jrows_mv_facts_A (hp63 : 2 ^ 63 < p) (hax9 : ProgAxOK9A p t)
    (hJl : (j8DataOf p Rg Rt hgen).jrows.length < p) (hbl : (bfsForest [t]).length < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((j8DataOf p Rg Rt hgen).jrows.flatMap provKT).Nodup ∧
    (∀ κ ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap consKT ++ pinsOfP p (j8DataOf p Rg Rt hgen).regs
        (j8DataOf p Rg Rt hgen).idx, κ ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap provKT) ∧
    (∀ x ∈ (j8DataOf p Rg Rt hgen).jrows, ∀ κ ∈ provKT x,
      x.w.mv = (((((j8DataOf p Rg Rt hgen).jrows.flatMap consKT).count κ +
        (pinsOfP p (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).idx).count κ : ℕ)) : ZMod p)) := by
  rw [ComplJ8Jet.j8DataOf_jrows Rt hgen]
  obtain ⟨hsmall, huniq⟩ := lay_statics_A Rt hgen hp63 hax9 hJl hbl hRt
  refine ⟨?_, hcov_fix _ _ (honest_cov Rt hgen hRt) (pins_prov Rt hgen), hmv_fix _ _⟩
  rw [flatMap_provKT_fix]
  exact hnd_rows Rt _ _ _ (ComplJ8Jet.honestJ8_pre _ Rt _ _) hsmall huniq (List.nodup_dedup _)

set_option maxHeartbeats 1000000 in
/-- `ComplJ8OfBalJ.jetT_row` with `hax9` (`calls_lt9`). -/
theorem jetT_row_A (hax9 : ProgAxOK9A p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p)
    (j : ℕ) (hj : j < (bfsForest [t]).length) :
    ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        pubVal j = Fu δ b Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) χ ((bfsForest [t])[j]'hj) := by
  set D := j8DataOf p Rg Rt hgen with hD
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
    obtain ⟨hT, -, -, hreg⟩ := calls_ok Rt hgen hRt _ hcl
    have hidp : id < p := calls_lt9 hgen hax9 _ hcl
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

theorem sum_jetT_A (hax9 : ProgAxOK9A p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
        (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((j8DataOf p Rg Rt hgen).calls.map fun cl =>
        ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) cl))).sum := by
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
      (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Fu δ b Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) χ ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [jetT_row_A δ b Rt hgen hax9 hRt χ pubVal j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t]
  show _ = ((Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).map _).sum
  unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
  simp only [List.toList_toArray]
  rw [← sum_filterMap_ite (fun r : RowNX => r.st = .s11j) (fun r => (Nock.V1J8.Gen.atomV r.sf1, r.s)), List.map_map]
  rfl

variable (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

set_option maxHeartbeats 2000000 in
/-- **(ii) The jet service sub-balance at `BRun9A`** (`hJ_run` at the J-9 A binders `hpG hax9 hRt h31A`):
the compute jet consumes, the registry pins and the J terminal sum to zero, at every coin. -/
theorem hJ_runA (hax9 : ProgAxOK9A p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) (pubVal : ℕ → ZMod p) :
    ∀ χ, (BA).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
          (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j +
        ((pinCons (p := p) (K := K) (BA).Pb.regs (BA).Pb.idx).map
          fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BA).M χ).pubsJ 0) (((BA).M χ).pubsJ 1) = 0 := by
  intro χ _
  have hp63 : 2 ^ 63 < p := p63 hpG
  set D := j8DataOf p Rg Rt hgen with hD
  have hJl : D.jrows.length < p := lt_p hpG (h31A _ (ComplJ9AOfStatic.mem_jrows Rt hgen))
  have hbl : (bfsForest [t]).length < p := lt_p hpG (h31A _ (ComplJ9AOfStatic.mem_bfs Rt hgen))
  have eJ : Quad.mk _ (((BA).M χ).pubsJ 0) (((BA).M χ).pubsJ 1) =
      ∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k) := by
    show Quad.mk _ (pubsJOf δ (DA) χ 0) (pubsJOf δ (DA) χ 1) = _
    have e0 : pubsJOf δ (DA) χ 0 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 0 := by simp [pubsJOf]; rfl
    have e1 : pubsJOf δ (DA) χ 1 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 1 := by simp [pubsJOf]; rfl
    rw [e0, e1, pub2_mk]
  obtain ⟨hnd, hcov, hmv⟩ := jrows_mv_facts_A Rt hgen hp63 hax9 hJl hbl hRt
  have hT := Nock.Jet.ChipJ8T.HonestBal.termJ_sum_of_mv_fin δ (VerJ8.chalsJJ8 χ) D.jrows.get
    (pinsOfP p D.regs D.idx) (by rw [List.ofFn_get]; exact hnd) (by rw [List.ofFn_get]; exact hcov)
    (by rw [List.ofFn_get]; exact hmv)
  rw [List.ofFn_get] at hT
  have hF := jrows_Fj δ Rt hgen (VerJ8.chalsJJ8 χ) hRt
  have eP : ((pinCons (p := p) (K := K) (BA).Pb.regs (BA).Pb.idx).map
      fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum =
      ((pinsOfP p D.regs D.idx).map (dJ δ (VerJ8.chalsJJ8 χ))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]
    simp only [pinCons, pinsOfP, List.map_map]
    rfl
  have eC := sum_jetT_A δ b Rt hgen hax9 hRt χ pubVal
  have eCJ : ((D.calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum) =
      ((D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]; rfl
  have hF' : (D.jrows.map fun r => liftQ δ r.w.m * sT δ (VerJ8.chalsJJ8 χ) Nock.Jet.ChipJ8.ents3 r).sum =
      (D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl)).sum := hF
  rw [eC, eP, eJ, hT, eCJ, hF']
  ring

include hpG in
/-- **(iii) The atom-walk pair consumes at `BRun9A`'s compute side**: `ComplJ9BBalG.awSum9` verbatim (binder
`hpG` only); the compute rows are J-8's, the data record is `j8DataOf`. -/
theorem awSum_A (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((j8DataOf p Rg Rt hgen).preads.map fun x => WA9 δ (j8DataOf p Rg Rt hgen) χ x).sum :=
  awSum9 δ b Rt hgen hpG χ pubVal

end Jet

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO
#print axioms opsOK_runA
#print axioms idxOOK_runA
#print axioms incInfoOK_runA
#print axioms incT_run_A
#print axioms incT_total_A
#print axioms hI9_A
#print axioms incT_BA
#print axioms lay_statics_A
#print axioms jrows_mv_facts_A
#print axioms jetT_row_A
#print axioms sum_jetT_A
#print axioms hJ_runA
#print axioms awSum_A
end Axioms
