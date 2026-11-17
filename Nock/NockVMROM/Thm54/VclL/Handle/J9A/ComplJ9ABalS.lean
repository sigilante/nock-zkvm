/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalS.lean

Part 1 (this file so far): the `s10B`-row transfer `sumB_transfer` (the missing link between S3(c)'s
  `GS`-sum over J-8 nodes and the sums over `s10B` rows used by S6/S7).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalST
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSO
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSC
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSRow
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSK
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSL
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSS
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.Jet (Registry)
open Nock.NockVMROM.Thm54 (mapNTree mapNTree_label mapNTree_children bfsForest_mapNTree)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.J9A.NounAx (top)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalST
open Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

section B
variable {M : Type} [AddCommMonoid M] (ψ : ℕ → M)

/-- the `s10B` summand over the J-9 A tree -/
def FB (u : NTree LX9) : M := if u.label.chip = ChipSt9.s10B then ψ u.label.n else 0

/-- the J-8-side summand: an `s10B`-classified node -/
def GB (k : SkelX) : M := if (chipOf k).1 = ChipSt9.s10B then ψ (chipOf k).2 else 0

theorem liftT_FB_zero (c : NTree SkelX) : ((dfsTree (liftT c)).map (FB ψ)).sum = 0 := by
  have hp := (dfsTree_map_perm liftL c).map (FB ψ)
  rw [show liftT c = mapNTree liftL c from rfl, hp.sum_eq, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  simp [Function.comp, FB, liftL, mapNTree_label]

theorem segT_FB (n : ℕ) :
    ∀ (m : ℕ) (s e : Noun), ((dfsTree (segT n m s e)).map (FB ψ)).sum = 0
  | 0, s, e => by
    simp only [segT, segNode, tNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [liftT_FB_zero ψ]
    simp [FB, NTree.label]
  | m + 1, s, e => by
    simp only [segT, segNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [liftT_FB_zero ψ, segT_FB n m]
    simp [FB, NTree.label]

/-- the side condition `OneChain` only needs its second half here. -/
theorem sumB_tree (t : NTree SkelX) (hz : OneChain t) :
    ((dfsTree (genX9T t)).map (FB ψ)).sum = ((dfsTree t).map fun u => GB ψ u.label).sum := by
  let P : NTree SkelX → Prop := fun t => OneChain t →
    ((dfsTree (genX9T t)).map (FB ψ)).sum = ((dfsTree t).map fun u => GB ψ u.label).sum
  revert hz
  show P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro k ks ih hz
    have hk : (genX9T (.node k ks)) = .node ⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩
        (ks.map fun c => kid9 k c (genX9T c)) := by rw [genX9T]
    rw [hk]
    simp only [dfsTree, List.map_cons, List.sum_cons]
    rw [dfs_sum, dfs_sum, List.map_map]
    have e1 : ∀ ks' : List (NTree LX9),
        FB ψ (NTree.node (⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩ : LX9) ks') =
          GB ψ (NTree.node k ks).label := by
      intro ks'
      simp only [FB, GB, NTree.label]
      split_ifs <;> rfl
    rw [e1]
    congr 1
    congr 1
    apply List.map_congr_left
    intro c hc
    simp only [Function.comp]
    by_cases hB : (chipOf k).1 = ChipSt9.s10B
    · obtain ⟨-, hno⟩ := hz (.node k ks) (InTree.here _) hB
      by_cases hch : c.label.state.isChain = true
      · unfold kid9
        rw [if_pos ⟨hB, hch⟩, segT_FB ψ]
        symm
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
        simp [GB, hno c hc hch v hv]
      · unfold kid9
        rw [if_neg (by tauto)]
        exact ih c hc (OneChain.sub hz hc)
    · unfold kid9
      rw [if_neg (by tauto)]
      exact ih c hc (OneChain.sub hz hc)
  · intro c hc; simp at hc
  · intro head tail ihH ihT c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihH
    · exact ihT c hc

theorem sumB_transfer (t : NTree SkelX) (hz : OneChain t) :
    (((bfsForest [genX9T t]).map (FB ψ))).sum = (((bfsForest [t]).map fun u => GB ψ u.label)).sum := by
  rw [← ((dfsTree_perm_bfsForest (genX9T t)).map (FB ψ)).sum_eq,
    ← ((dfsTree_perm_bfsForest t).map fun u : NTree SkelX => GB ψ u.label).sum_eq]
  exact sumB_tree ψ t hz

end B

section Body
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (DX)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The J-8 `.s` row body (inc + jet + pair) at an environment: `incT`/`jetT`/`awT` are this at `env0`. -/
def sBody (e : Nock.Reified.Env (ZMod p)) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ (e.trace 4 * (1 - e.trace 61)) *
      (DX δ (Compute.TowerD.gatherEnv b e) e ChipHX.incRecX)⁻¹ +
    algebraMap (ZMod p) 𝕂′ (e.trace 16) * (DX δ (Compute.TowerD.gatherEnv b e) e ChipHX.jetRecX)⁻¹ +
    algebraMap (ZMod p) 𝕂′ (e.trace 64) *
      ((DX δ (Compute.TowerD.gatherEnv b e) e (ChipHX.walkRecAX ChipHX.xFtth ChipHX.xL1))⁻¹ +
        (DX δ (Compute.TowerD.gatherEnv b e) e (ChipHX.walkRecAX ChipHX.xFttt ChipHX.xL2))⁻¹)

/-- `sBody` reads the trace only off the first/last-flag columns `17`, `18`. -/
theorem sBody_congr (χ : Coins frameJ8 K) (e1 e2 : Nock.Reified.Env (ZMod p))
    (h1 : e1.chal = VerJ8.chalVJ8 b χ) (h2 : e2.chal = VerJ8.chalVJ8 b χ)
    (h : ∀ c, c ≠ 17 → c ≠ 18 → e1.trace c = e2.trace c) : sBody δ b e1 = sBody δ b e2 := by
  unfold sBody
  rw [ComplJ8OfBalG.DX_inc δ b e1 χ h1, ComplJ8OfBalG.DX_inc δ b e2 χ h2,
    ComplJ8OfBalG.DX_walkA δ b e1 χ h1, ComplJ8OfBalG.DX_walkA δ b e1 χ h1,
    ComplJ8OfBalG.DX_walkA δ b e2 χ h2, ComplJ8OfBalG.DX_walkA δ b e2 χ h2]
  rw [← inv_inv (DX δ (Compute.TowerD.gatherEnv b e1) e1 ChipHX.jetRecX),
    ← inv_inv (DX δ (Compute.TowerD.gatherEnv b e2) e2 ChipHX.jetRecX),
    ComplJ8OfBalJ.DX_jet δ b e1 χ h1, ComplJ8OfBalJ.DX_jet δ b e2 χ h2]
  simp only [ChipHX.jetRecX, ChipHX.xSf1, ChipHX.xFtth, ChipHX.xFttt, ChipHX.xL1, ChipHX.xL2, ChipHX.xFtt, ChipHX.xS,
    ChipHX.xE, ChipHX.hdX, ChipHX.RE.ev, List.map_cons, List.map_nil]
  simp (disch := omega) only [h]

end Body

section RhoS
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0 env1)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A W9 N9 N9_def idOfA accTA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (sSum9)
open Nock.Jet.Autogen (Tpl)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

set_option maxHeartbeats 4000000 in
/-- **Step 1 of S9: the J-9 A run's `ρS` public is the sum of the rows' `.s` terms `sSum9`.** -/
theorem rhoS_total (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
    (χ : Coins frameJ8 K)
    (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρSA δ b Rt hgen χ =
      ∑ j ∈ Finset.range (N9 t), sSum9 δ b (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd
        (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j := by
  have hg : ∀ e ∈ Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.compPoles9 (K := K) δ (j9aDataOf p Rg Rt hgen).H
      (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen) (W9 t) (N9 t), χ ∉ e.ev := fun e he =>
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.good_fam δ b Rt hgen hpG h31A hχ _
      (List.mem_append_right _ (by unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.famsNew; simp)) e he
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρSA
  show Quad.mk _ (HonestTraceX9.accV9 b δ (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd
      (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 4 (N9 t))
    (HonestTraceX9.accV9 b δ (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd
      (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 5 (N9 t)) = _
  rw [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.rhoS_rows9]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < N9 t := Finset.mem_range.mp hj
  exact Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.termQX9_s δ b _ _ _ (W9 t) _ _ j
    (ComplJ9AOfComp.s10B_rows hgen j hj')
    (ComplJ9ABalPC.hpair9_good δ b _ _ _ (W9 t) (N9 t) (fun _ => 0) χ hg j hj')

end RhoS

section Xfer
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (colX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colX9_old colS0B colS10B colS10S)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (rowAtWX)

section Gen
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- `colX` reads the first/last flags only at columns `17`, `18`. -/
theorem colX_fl (r : RowNX) (f1 l1 f2 l2 : F) (c : ℕ) (h17 : c ≠ 17) (h18 : c ≠ 18) :
    colX H pd r f1 l1 c = colX H pd r f2 l2 c := by
  simp only [colX, h17, h18, if_false]

theorem sum_rowAt9 {M : Type} [AddCommMonoid M] (G : LX9 → M) :
    ∀ W : List (NTree LX9),
      ∑ j ∈ Finset.range W.length, G (rowAt9 W (j + 1)) = (W.map fun u => G u.label).sum
  | [] => by simp
  | a :: l => by
    have h1 : ∑ i ∈ Finset.range l.length, G (rowAt9 (a :: l) (i + 1 + 1)) =
        (l.map fun u => G u.label).sum := by
      rw [← sum_rowAt9 G l]
      exact Finset.sum_congr rfl fun i _ => by simp [rowAt9]
    have h2 : G (rowAt9 (a :: l) (0 + 1)) = G a.label := by simp [rowAt9]
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, h1, h2, add_comm]

theorem sum_rowAtWX {M : Type} [AddCommMonoid M] (g : RowNX → M) :
    ∀ W : List (NTree SkelX),
      ∑ j ∈ Finset.range W.length, g (rowAtWX W (j + 1)) = (W.map fun u => g (rowOfSkelX u.label)).sum
  | [] => by simp
  | a :: l => by
    have h1 : ∑ i ∈ Finset.range l.length, g (rowAtWX (a :: l) (i + 1 + 1)) =
        (l.map fun u => g (rowOfSkelX u.label)).sum := by
      rw [← sum_rowAtWX g l]
      exact Finset.sum_congr rfl fun i _ => by simp [rowAtWX]
    have h2 : g (rowAtWX (a :: l) (0 + 1)) = g (rowOfSkelX a.label) := by simp [rowAtWX]
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, h1, h2, add_comm]

theorem rowAt9_mem (W : List (NTree LX9)) (j : ℕ) (hj : j < W.length) :
    ∃ u ∈ W, rowAt9 W (j + 1) = u.label :=
  ⟨W[j], List.getElem_mem hj, by simp [rowAt9, List.getElem?_eq_getElem hj]⟩

end Gen

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
  (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The row-intrinsic `.s` body (flags zeroed). -/
def gB (r : RowNX) : 𝕂′ :=
  sBody δ b ⟨colX H pd r 0 0, colX H pd r 0 0, VerJ8.chalVJ8 b χ, pubVal⟩

theorem sBody_zero (e : Nock.Reified.Env (ZMod p)) (h4 : e.trace 4 = 0) (h16 : e.trace 16 = 0)
    (h64 : e.trace 64 = 0) : sBody δ b e = 0 := by
  unfold sBody
  simp [h4, h16, h64]

theorem gB_zero (r : RowNX)
    (hst : r.st = StateX.s0 ∨ r.st = StateX.s10 ∨ r.st = StateX.s10L ∨ r.st = StateX.s10T) :
    gB δ b H pd χ pubVal r = 0 := by
  have hP : ¬ HonestCompX.isPair H r := fun h => by
    have := h.1
    rcases hst with h' | h' | h' | h' <;> rw [h'] at this <;> cases this
  apply sBody_zero
  · show colX H pd r 0 0 4 = 0
    rcases hst with h' | h' | h' | h' <;> simp [colX, h', RowDecodeVSX.stIdx]
  · show colX H pd r 0 0 16 = 0
    rcases hst with h' | h' | h' | h' <;> simp [colX, h', RowDecodeVSX.stIdx]
  · show colX H pd r 0 0 64 = 0
    simp [colX, HonestCompX.cPr2, hP]

/-- J-8 row `j`: the three `.s` consumes are `gB` of the row. -/
theorem j8_row_body (W : List (NTree SkelX)) (j : ℕ) :
    ComplJ8OfBalG.incT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ8OfBalG.jetT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ8OfBalG.awT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j =
      gB δ b H pd χ pubVal (rowAtWX W (j + 1)) := by
  have e : ComplJ8OfBalG.incT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ8OfBalG.jetT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ8OfBalG.awT δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j =
      sBody δ b (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pubVal j) := rfl
  rw [e]
  exact sBody_congr δ b χ _ _ rfl rfl fun c h17 h18 => colX_fl H pd _ _ _ _ _ c h17 h18

/-- J-9 row `j` (chip not `s0B`/`s10B` with a pair state): `gB` on old rows, `0` otherwise. -/
theorem j9_row_body (W : List (NTree LX9)) (j : ℕ)
    (hst : ((rowAt9 W (j + 1)).chip = .s0B ∨ (rowAt9 W (j + 1)).chip = .s10B) →
      (rowAt9 W (j + 1)).rn.st = StateX.s0 ∨ (rowAt9 W (j + 1)).rn.st = StateX.s10) :
    ComplJ9ABalSC.incT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ9ABalSC.jetT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ9ABalSC.awT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j =
      (if (rowAt9 W (j + 1)).chip = ChipSt9.old then gB δ b H pd χ pubVal (rowAt9 W (j + 1)).rn else 0) := by
  have e : ComplJ9ABalSC.incT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ9ABalSC.jetT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j +
        ComplJ9ABalSC.awT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j =
      sBody δ b (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j) := rfl
  rw [e]
  have hT : (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  generalize hl : rowAt9 W (j + 1) = l at hst hT ⊢
  cases hc : l.chip with
  | old =>
    rw [if_pos rfl]
    exact sBody_congr δ b χ _ _ rfl rfl fun c h17 h18 => by
      rw [hT, colX9_old H pd idOf l _ _ hc]
      exact colX_fl H pd _ _ _ _ _ c h17 h18
  | s0B =>
    rw [if_neg (by simp)]
    have hP : ¬ HonestCompX.isPair H l.rn := fun h => by
      have := h.1
      rcases hst (Or.inl hc) with h' | h' <;> rw [h'] at this <;> cases this
    apply sBody_zero <;> rw [show (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace = _ from hT]
    · simp [colX9, hc, colS0B]
    · simp [colX9, hc, colS0B]
    · simp [colX9, hc, colS0B, colX, HonestCompX.cPr2, hP]
  | s10B =>
    rw [if_neg (by simp)]
    have hP : ¬ HonestCompX.isPair H l.rn := fun h => by
      have := h.1
      rcases hst (Or.inr hc) with h' | h' <;> rw [h'] at this <;> cases this
    apply sBody_zero <;> rw [show (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace = _ from hT]
    · simp [colX9, hc, colS10B]
    · simp [colX9, hc, colS10B]
    · simp [colX9, hc, colS10B, colX, HonestCompX.cPr2, hP]
  | s10S =>
    rw [if_neg (by simp)]
    apply sBody_zero <;> rw [show (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace = _ from hT]
    · simp [colX9, hc, colS10S]
    · simp [colX9, hc, colS10S]
    · simp [colX9, hc, colS10S]

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def)

/-- The node facts the transfer needs: `s0B`/`s10B` rows carry a `s0`/`s10` noun row. -/
theorem w9_states {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) :
    ∀ u ∈ W9 t, (u.label.chip = ChipSt9.s0B → u.label.rn.st = StateX.s0) ∧
      (u.label.chip = ChipSt9.s10B → u.label.rn.st = StateX.s10) := by
  intro u hmem
  obtain ⟨c, hc', hcu⟩ := (mem_bfsForest _ _).1 hmem
  simp only [List.mem_singleton] at hc'
  subst hc'
  have hsem := ComplJ9AGen.semN9_of_node9 (ComplJ9AGen.genX9T_inTree hgen hcu)
  constructor
  · intro hc
    simp only [ComplJ9AGen.SemN9, hc] at hsem
    exact hsem.2.1
  · intro hc
    simp only [ComplJ9AGen.SemN9, hc] at hsem
    exact hsem.2.1

/-- **Step 2 of S9: the old-row transfer.** The J-9 A rows' `incT9 + jetT9 + awT9` sum is the J-8 rows'
`incT + jetT + awT` sum (same `H`, `pd`, any `idOf`, any publics). -/
theorem old_sum_transfer {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) :
    ∑ j ∈ Finset.range (N9 t),
        (ComplJ9ABalSC.incT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ9ABalSC.jetT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ9ABalSC.awT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j) =
      ∑ j ∈ Finset.range (bfsForest [t]).length,
        (ComplJ8OfBalG.incT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ8OfBalG.jetT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ8OfBalG.awT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j) := by
  have hg := fun r hr => gB_zero δ b H pd χ pubVal r hr
  have hz := ComplJ9ABalST.chainZ_gen (gB δ b H pd χ pubVal) hg hgen
  have hT := ComplJ9ABalST.sumT_transfer (gB δ b H pd χ pubVal) hg t hz
  have hL : ∑ j ∈ Finset.range (N9 t),
        (ComplJ9ABalSC.incT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ9ABalSC.jetT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ9ABalSC.awT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal j) =
      ∑ j ∈ Finset.range (W9 t).length,
        (fun l : LX9 => if l.chip = ChipSt9.old then gB δ b H pd χ pubVal l.rn else 0)
          (rowAt9 (W9 t) (j + 1)) := by
    rw [N9_def]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨u, hu, hrow⟩ := rowAt9_mem (W9 t) j (Finset.mem_range.1 hj)
    rw [j9_row_body δ b H pd idOf χ pubVal (W9 t) j (fun h => by
      rw [hrow] at h ⊢
      rcases h with h | h
      · exact Or.inl ((w9_states hgen u hu).1 h)
      · exact Or.inr ((w9_states hgen u hu).2 h))]
  rw [hL, sum_rowAt9 (fun l : LX9 => if l.chip = ChipSt9.old then gB δ b H pd χ pubVal l.rn else 0) (W9 t)]
  have hR : ∑ j ∈ Finset.range (bfsForest [t]).length,
        (ComplJ8OfBalG.incT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ8OfBalG.jetT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j +
          ComplJ8OfBalG.awT δ b H pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j) =
      ∑ j ∈ Finset.range (bfsForest [t]).length, gB δ b H pd χ pubVal (rowAtWX (bfsForest [t]) (j + 1)) :=
    Finset.sum_congr rfl fun j _ => j8_row_body δ b H pd χ pubVal _ j
  rw [hR, sum_rowAtWX (gB δ b H pd χ pubVal) (bfsForest [t])]
  exact hT

end Xfer

section OldPart
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A W9 N9 idOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (axPosB)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (incT9 jetT9 awT9)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
  (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

set_option maxHeartbeats 4000000 in
/-- **Step 2 of S9, complete**: the J-9 A rows' old-row `.s` terms sum to
`MI − (pins + J) + Σ_preads WA9` (all in the J-8 data's terms). -/
theorem old_part (hax9 : ProgAxOK9A p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    ∑ j ∈ Finset.range (N9 t),
        (incT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          jetT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          awT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) =
      Quad.mk _ (((BA).M χ).pubsA AtomChipHQ.pubMI) (((BA).M χ).pubsA (AtomChipHQ.pubMI + 1)) -
        (((pinCons (p := p) (K := K) (BA).Pb.regs (BA).Pb.idx).map
          fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BA).M χ).pubsJ 0) (((BA).M χ).pubsJ 1)) +
      ((j8DataOf p Rg Rt hgen).preads.map fun x => ComplJ9BBalG.WA9 δ (j8DataOf p Rg Rt hgen) χ x).sum := by
  have h1 := old_sum_transfer δ (K := K) b (DA).H (DA).pd (idOfA (p := p) Rt hgen) χ (fun _ => 0) hgen
  have hI := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO.incT_BA δ b Rt hgen hpG h31A χ (fun _ => 0)
  have hJ : ∑ j ∈ Finset.range (bfsForest [t]).length,
          ComplJ8OfBalG.jetT δ b (DA).H (DA).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
        ((pinCons (p := p) (K := K) (BA).Pb.regs (BA).Pb.idx).map
          fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BA).M χ).pubsJ 0) (((BA).M χ).pubsJ 1) = 0 :=
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO.hJ_runA δ b Rt hgen hpG h31A hax9 hRt
      (fun _ => 0) χ hχ
  have hA := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSO.awSum_A δ b Rt hgen hpG χ (fun _ => 0)
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  erw [hI, hA]
  linear_combination hJ

end OldPart

section Tag
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (gT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKey9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx (tagW tagKW)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (axRecX limbRecX)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **Step 3 of S9, per row**: the two new tag consumes of row `j` sum to the `tagKW` of its key (0 off
`s0B`/`s10B` rows). -/
theorem tag_row {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (nA : ℕ) (H : Noun → ℕ × ℕ)
    (hH : HonestCompX.HdlOK p H) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (W9 t).length) :
    gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 123
        (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j +
      gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 124
        (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j =
    match axKey9 (rowAt9 (W9 t) (j + 1)) with
    | some k => tagKW δ nA H (rowsOfT9 t) χ k
    | none => 0 := by
  obtain ⟨u, hu, hrow⟩ := rowAt9_mem (W9 t) j hj
  have hsem : ComplJ9AGen.SemN9 Rg.R (rowAt9 (W9 t) (j + 1)) := by
    rw [hrow]
    obtain ⟨c, hc', hcu⟩ := (mem_bfsForest _ _).1 hu
    simp only [List.mem_singleton] at hc'
    subst hc'
    exact ComplJ9AGen.semN9_of_node9 (ComplJ9AGen.genX9T_inTree hgen hcu)
  have hT : (env0 H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (rowAt9 (W9 t) (j + 1))
        (fl1 (j + 1)) (llW (W9 t) (j + 1)) := rfl
  cases hc : (rowAt9 (W9 t) (j + 1)).chip with
  | old =>
    rw [ComplJ9ABalSRow.gT9_old δ b H pd _ (W9 t) pubVal χ j hc 123 le_rfl,
      ComplJ9ABalSRow.gT9_old δ b H pd _ (W9 t) pubVal χ j hc 124 (by norm_num)]
    simp [axKey9, hc]
  | s0B =>
    have h124 : gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 124
        (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS0B]
    rw [ComplJ9ABalSRow.gT9_s0B δ b H pd _ (W9 t) pubVal χ j hc, h124, add_zero]
    have hk : axKey9 (rowAt9 (W9 t) (j + 1)) =
        some ((rowAt9 (W9 t) (j + 1)).rn.s, (rowAt9 (W9 t) (j + 1)).n) := by simp [axKey9, hc]
    rw [hk]
    exact ComplJ9ABalSK.tagW_s0B δ nA H (rowsOfT9 t) χ hH _ hsem hc _ hk
  | s10B =>
    have h123 : gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 123
        (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS10B]
    rw [ComplJ9ABalSRow.gT9_s10B δ b H pd _ (W9 t) pubVal χ j hc, h123, zero_add]
    have hk : axKey9 (rowAt9 (W9 t) (j + 1)) =
        some ((rowAt9 (W9 t) (j + 1)).rn.e, (rowAt9 (W9 t) (j + 1)).n) := by simp [axKey9, hc]
    rw [hk]
    exact ComplJ9ABalSK.tagW_s10B δ nA H (rowsOfT9 t) χ hH _ hsem hc _ hk
  | s10S =>
    have h123 : gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 123
        (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS10S]
    have h124 : gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 124
        (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS10S]
    rw [h123, h124]
    simp [axKey9, hc]

/-- **Step 3 of S9, total**: the two new tag consumes over all rows are the `tagKW` sum over the keys. -/
theorem tag_total {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (nA : ℕ) (H : Noun → ℕ × ℕ)
    (hH : HonestCompX.HdlOK p H) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (N9 t),
        (gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 123
            (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j +
          gT9 δ b H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t))) (W9 t) (VerJ8.chalVJ8 b χ) pubVal 124
            (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j) =
      (((rowsOfT9 t).toList.filterMap axKey9).map (tagKW δ nA H (rowsOfT9 t) χ)).sum := by
  rw [N9_def]
  rw [Finset.sum_congr rfl fun j hj => tag_row δ b hgen nA H hH pd χ pubVal j (Finset.mem_range.1 hj)]
  refine (sum_rowAt9 (fun l : LX9 => match axKey9 l with
    | some k => tagKW δ nA H (rowsOfT9 t) χ k
    | none => 0) (W9 t)).trans ?_
  rw [← ComplJ9ABalST.sum_axKey9 (tagKW δ nA H (rowsOfT9 t) χ)]
  simp only [rowsOfT9, ComplJ9AGen.rowsOfT9, List.toList_toArray, List.map_map, W9]
  rfl

end Tag

/-! ## Step 4: the limb consume (`gT9` flag column 125) -/

section Limb0
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (bitN)

/-- column 135 of `colS10S`, as a closed formula of `(n, m)`. -/
def c135 {p : ℕ} (n m : ℕ) : ZMod p :=
  let b : ℕ → ZMod p := fun i => ((bitN m i : ℕ) : ZMod p)
  let hd : ZMod p := if m = top n then 1 else 0
  let pw1 : ZMod p := (1 + b 0) * ((1 + 3 * b 1) * (1 + 15 * b 2))
  let pw2 : ZMod p := (1 + 255 * b 3) * ((1 + 65535 * b 4) * (1 + 4294967295 * b 5))
  let pw : ZMod p := 2 * (pw1 * pw2)
  hd * (pw - 1) + (1 - hd) * (2 * pw - 2)

theorem pw_nat : ∀ m < 64, 2 * (((1 + bitN m 0) * ((1 + 3 * bitN m 1) * (1 + 15 * bitN m 2))) *
    ((1 + 255 * bitN m 3) * ((1 + 65535 * bitN m 4) * (1 + 4294967295 * bitN m 5)))) = 2 ^ (m + 1) := by
  decide +kernel

theorem c135_eq {p : ℕ} (n m : ℕ) (hm : m < 64) : c135 (p := p) n m =
    if m = top n then ((2 ^ (top n + 1) : ℕ) : ZMod p) - 1 else ((2 ^ (m + 2) : ℕ) : ZMod p) - 2 := by
  have h := congrArg (Nat.cast : ℕ → ZMod p) (pw_nat m hm)
  push_cast at h
  unfold c135
  dsimp only
  by_cases hmt : m = top n
  · rw [if_pos hmt, if_pos hmt]
    rw [← hmt]
    push_cast
    linear_combination h
  · rw [if_neg hmt, if_neg hmt]
    push_cast
    linear_combination 2 * h

theorem sum_filter_ite {α M : Type} [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (g : α → M) :
    ∀ L : List α, (L.map fun l => if P l then g l else 0).sum = ((L.filter fun l => decide (P l)).map g).sum
  | [] => by simp
  | l :: ls => by
    rw [List.map_cons, List.sum_cons, sum_filter_ite P g ls, List.filter_cons]
    by_cases h : P l <;> simp [h]

end Limb0

section Limb
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (gT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (limbRecX)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- the limb weight of segment `i` of axis `n`, with column 135 as the closed formula. -/
def φL (idOf : ℕ → ℕ) (χ : Coins frameJ8 K) (n i : ℕ) : 𝕂′ :=
  ComplJ9ABalSAx.limbW δ χ (((idOf n : ℕ) : ZMod p), c135 n i,
    (0, ((n / 2 ^ (32 * i) % 2 ^ 32 : ℕ) : ZMod p)))

theorem limb_row (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ) :
    gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 125 limbRecX j =
      (fun l : LX9 => if l.chip = ChipSt9.s10S then φL δ idOf χ l.n l.m else 0) (rowAt9 W (j + 1)) := by
  have hT : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  cases hc : (rowAt9 W (j + 1)).chip with
  | old =>
    rw [ComplJ9ABalSRow.gT9_old δ b H pd idOf W pubVal χ j hc 125 (by norm_num)]
    simp [hc]
  | s0B =>
    have h0 : gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 125 limbRecX j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS0B]
    rw [h0]
    simp [hc]
  | s10B =>
    have h0 : gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 125 limbRecX j = 0 := by
      unfold gT9
      rw [hT]
      simp [colX9, hc, colS10B]
    rw [h0]
    simp [hc]
  | s10S =>
    rw [ComplJ9ABalSRow.gT9_s10S δ b H pd idOf W pubVal χ j hc]
    have h135 : colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) 135 =
        c135 (rowAt9 W (j + 1)).n (rowAt9 W (j + 1)).m := by
      simp [colX9, hc, colS10S, c135]
    rw [h135]
    simp [hc, φL]

/-- every `s10B` row's axis has `top < 63` (so the `pw` formula of column 135 is exact). -/
theorem top_lt63_of_row {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (l : LX9) (hl : l ∈ (rowsOfT9 t).toList)
    (hc : l.chip = ChipSt9.s10B) : top l.n < 63 := by
  have hmem : l.n ∈ ComplJ9AData.axAtoms9 (rowsOfT9 t) :=
    ComplJ9AData.mem_axAtoms9.2 ⟨l, hl, Or.inr hc, rfl⟩
  obtain ⟨h62, hcap⟩ := ComplJ9AData.axAtoms9_cap hgen hax9 l.n hmem
  rcases hcap with hlt | hcap
  · have := ComplJ9AReads.top_field h62 (ComplJ9AChains.lt64_of_G hpG hlt)
    omega
  · have := ComplJ9AChains.top_lt_62 hcap (by positivity)
    omega

theorem limb_total {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (N9 t),
        gT9 δ b H pd idOf (W9 t) (VerJ8.chalVJ8 b χ) pubVal 125 limbRecX j =
      ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = ChipSt9.s10B)).map fun l =>
        ((ComplJ9ABalSAx.limbRecs (p := p) (idOf l.n) l.n).map (ComplJ9ABalSAx.limbW δ χ)).sum)).sum := by
  rw [N9_def]
  rw [Finset.sum_congr rfl fun j _ => limb_row δ b H pd idOf (W9 t) χ pubVal j]
  rw [sum_rowAt9 (fun l : LX9 => if l.chip = ChipSt9.s10S then φL δ idOf χ l.n l.m else 0) (W9 t)]
  have e1 : ((W9 t).map fun u => (fun l : LX9 => if l.chip = ChipSt9.s10S then φL δ idOf χ l.n l.m else 0)
      u.label).sum = ((bfsForest [genX9T t]).map (FS (φL δ idOf χ))).sum := rfl
  rw [e1, sumS_transfer _ t (oneChain_gen hgen)]
  have e2 : (((bfsForest [t]).map fun u => GS (φL δ idOf χ) u.label)).sum =
      (((bfsForest [t]).map fun u => GB (fun n => ∑ i ∈ Finset.range (top n + 1), φL δ idOf χ n i)
        u.label)).sum := rfl
  rw [e2, ← sumB_transfer _ t (oneChain_gen hgen)]
  have e3 : (((bfsForest [genX9T t]).map (FB (fun n => ∑ i ∈ Finset.range (top n + 1), φL δ idOf χ n i)))).sum =
      (((rowsOfT9 t).toList.map fun l => if l.chip = ChipSt9.s10B then
        ∑ i ∈ Finset.range (top l.n + 1), φL δ idOf χ l.n i else 0)).sum := by
    simp only [rowsOfT9, ComplJ9AGen.rowsOfT9, List.toList_toArray, List.map_map]
    rfl
  rw [e3, sum_filter_ite (fun l : LX9 => l.chip = ChipSt9.s10B)
    (fun l => ∑ i ∈ Finset.range (top l.n + 1), φL δ idOf χ l.n i)]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨hl, hc⟩ := List.mem_filter.1 hl
  have hcb : l.chip = ChipSt9.s10B := by simpa using hc
  have ht := top_lt63_of_row hgen hpG hax9 l hl hcb
  rw [ComplJ9ABalST.limbRecs_sum (ComplJ9ABalSAx.limbW δ χ)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold φL ComplJ9ABalST.limbRecAt
  rw [c135_eq _ _ (by omega)]

end Limb

/-! ## Step 5: publics and the assembly of `hGSA` -/

section Final
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A W9 N9 N9_def idOfA spOnA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9 idOf9_big)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (axPosB)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (incT9 jetT9 awT9 gT9 sSum9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx (limbRecs limbW)

theorem split3 {α M : Type} [AddCommMonoid M] (f : α → M) (g g1 g2 : α → Bool)
    (h : ∀ a, g a = (g1 a || g2 a)) (hd : ∀ a, ¬ (g1 a = true ∧ g2 a = true)) :
    ∀ L : List α, ((L.filter g).map f).sum = ((L.filter g1).map f).sum + ((L.filter g2).map f).sum
  | [] => by simp
  | a :: L => by
    have ih := split3 f g g1 g2 h hd L
    have h1 := h a
    have h2 := hd a
    simp only [List.filter_cons]
    cases hg1 : g1 a <;> cases hg2 : g2 a <;> simp_all [add_assoc, add_left_comm, add_comm]

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
  (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

omit h31A in
theorem small_absent (hax9 : ProgAxOK9A p t) (hsp : ¬ spOnA p t = true) :
    ((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)) = [] ∧
      ((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)) = [] := by
  have hfx : fieldAx9 p (rowsOfT9 t) = [] := by
    simpa [spOnA, splitVals9] using hsp
  have hkeys : ((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)) = [] := by
    refine List.filter_eq_nil_iff.2 fun k hk => ?_
    obtain ⟨l', hl', hl'k⟩ := mem_axKeys9.1 hk
    have hat : k.2 ∈ axAtoms9 (rowsOfT9 t) := by
      refine mem_axAtoms9.2 ⟨l', hl', ?_, ?_⟩ <;> unfold axKey9 at hl'k <;>
        cases hc : l'.chip <;> simp [hc] at hl'k <;> subst hl'k <;> simp [hc]
    have : k.2 ∉ fieldAx9 p (rowsOfT9 t) := by rw [hfx]; simp
    simp only [fieldAx9, List.mem_filter, decide_eq_true_eq, not_and] at this
    simpa using this hat
  refine ⟨hkeys, ?_⟩
  refine List.filter_eq_nil_iff.2 fun l hl hd => ?_
  simp only [decide_eq_true_eq] at hd
  have hat : l.n ∈ axAtoms9 (rowsOfT9 t) := mem_axAtoms9.2 ⟨l, hl, Or.inr hd.1, rfl⟩
  have : l.n ∈ fieldAx9 p (rowsOfT9 t) := by
    simp only [fieldAx9, List.mem_filter, decide_eq_true_eq]; exact ⟨hat, hd.2⟩
  rw [hfx] at this; simp at this

/-- the axis half of the publics: `pubsX AXs = Σ_keys limbRecs − Σ tagKW`. -/
theorem pubsX_S (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs)
      (((BA).M χ).pubsX (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs + 1)) =
    ((axKeys9 (rowsOfT9 t)).map fun k =>
        ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum -
      (((rowsOfT9 t).toList.filterMap axKey9).map
        (ComplJ9ABalSAx.tagKW δ (DA).acs.length (DA).H (rowsOfT9 t) χ)).sum := by
  show Quad.mk _ (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA δ Rt hgen χ _)
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA δ Rt hgen χ _) = _
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA
  by_cases h : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.axOnA t = true
  · rw [dif_pos h, ComplJ9AChipsOK.pubsXOf_S]
    exact ComplJ9ABalSAx.axSumS_eq_run δ hgen _ _ _ _ χ
  · rw [dif_neg h]
    have hk : axKeys9 (rowsOfT9 t) = [] := by
      simpa [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.axOnA] using h
    have hf : (rowsOfT9 t).toList.filterMap axKey9 = [] := by
      refine List.filterMap_eq_nil_iff.2 fun l hl => ?_
      by_contra hne
      obtain ⟨k, hk'⟩ := Option.ne_none_iff_exists'.1 hne
      have := (mem_axKeys9 (rows := rowsOfT9 t) (k := k)).2 ⟨l, hl, hk'⟩
      rw [hk] at this; simp at this
    rw [hk, hf]
    simp [Quad.mk_zero']

/-- the split half of the publics. -/
theorem pubsS_S (hax9 : ProgAxOK9A p t) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsS Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs)
      (((BA).M χ).pubsS (Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs + 1)) =
    ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)).map fun k =>
        ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum) +
      ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)).map fun l =>
        ((limbRecs (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum).sum) := by
  show Quad.mk _ (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsSA δ Rt hgen χ _)
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsSA δ Rt hgen χ _) = _
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsSA
  by_cases hsp : spOnA p t = true
  · rw [if_pos hsp, ComplJ9AChipsOK.pubsSOf_S]
    exact ComplJ9ABalSS.spSum_run δ Rt hgen hpG hax9 χ
  · rw [if_neg hsp]
    obtain ⟨h1, h2⟩ := small_absent hax9 hsp
    rw [h1, h2]
    simp [Quad.mk_zero']

set_option maxHeartbeats 4000000 in
/-- **`hGSA`**: the `hGS` field of `ComplJ9AObligations` at `BRun9A`, verbatim, at every good coin. -/
theorem hGSA (hax9 : ProgAxOK9A p t) (hop5 : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8.ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hwalk9 : WalkDepthOK9A (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.rowsOfT t))
    (hwalkA : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk.WalkDepthOK (DD).preads)
    (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    ((BA).M χ).ρS + ((pinCons (p := p) (K := K) (BA).Pb.regs (BA).Pb.idx).map fun x =>
      (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BA).M χ).pubsJ 0) (((BA).M χ).pubsJ 1) +
      Quad.mk _ (((BA).M χ).pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs)
        (((BA).M χ).pubsX (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs + 1)) =
    Quad.mk _ (((BA).M χ).pubsA Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ.pubMI)
        (((BA).M χ).pubsA (Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (((BA).M χ).pubsV Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ)
        (((BA).M χ).pubsV (Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ + 1)) +
      Quad.mk _ (((BA).M χ).pubsS Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs)
        (((BA).M χ).pubsS (Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs + 1)) := by
  have hH : HonestCompX.HdlOK p (DA).H := ComplJ8Data.hdlOK_hdlP p (DA).cells (DA).acs
  have hρ : ((BA).M χ).ρS = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρSA δ b Rt hgen χ := rfl
  have hsplit : ∑ j ∈ Finset.range (N9 t), sSum9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t)
        (VerJ8.chalVJ8 b χ) (fun _ => 0) j =
      ∑ j ∈ Finset.range (N9 t),
        (incT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          jetT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          awT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) +
      ∑ j ∈ Finset.range (N9 t),
        (gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 123
            (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j +
          gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 124
            (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j) +
      ∑ j ∈ Finset.range (N9 t),
        gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 125
          ChipHX9.limbRecX j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ComplJ9ABalSC.sSum9_expand]
    ring
  have hold := old_part δ b Rt hgen hpG h31A hax9 hRt χ hχ
  have htag := tag_total δ b hgen (DA).acs.length (DA).H hH (DA).pd χ (fun _ => 0)
  have hlimb := limb_total δ b hgen hpG hax9 (DA).H (DA).pd (idOfA (p := p) Rt hgen) χ (fun _ => 0)
  have hX := pubsX_S δ b Rt hgen hpG h31A χ
  have hS := pubsS_S δ b Rt hgen hpG h31A hax9 χ
  have hV : Quad.mk _ (((BA).M χ).pubsV Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ)
        (((BA).M χ).pubsV (Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ + 1)) =
      ((DA).preads.map (ComplJ9BBalG.WA9 δ (DA) χ)).sum :=
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSV.vhP9_BA δ b Rt hgen hpG h31A hax9 hwalkA χ
  have hSL := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSL.axReadsK9_sum δ Rt hgen hpG χ
  rw [ComplJ9ADataRec.j9aDataOf_preads, List.map_append, List.sum_append] at hV
  have hSL' : ((Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t)).map
      (ComplJ9BBalG.WA9 δ (DA) χ)).sum = _ := hSL
  rw [hSL'] at hV
  -- the splits of the key / row sums into big and field parts
  have eK : ((axKeys9 (rowsOfT9 t)).map fun k =>
        ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum =
      ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (p ≤ k.2)).map fun k =>
          ((limbRecs (p := p) ((DA).H (.atom k.2)).2 k.2).map (limbW δ χ)).sum).sum) +
        ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)).map fun k =>
          ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum) := by
    have := split3 (fun k : Noun × ℕ => ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum)
      (fun _ => true) (fun k => decide (p ≤ k.2)) (fun k => decide (k.2 < p))
      (fun k => by simp only [Bool.true_eq, Bool.or_eq_true, decide_eq_true_eq]; omega)
      (fun k => by simp only [decide_eq_true_eq]; omega) (axKeys9 (rowsOfT9 t))
    simp only [List.filter_true] at this
    rw [this]
    congr 1
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hpk : p ≤ k.2 := by simpa using (List.mem_filter.1 hk).2
    rw [show idOfA (p := p) Rt hgen k.2 = ((DA).H (.atom k.2)).2 from idOf9_big hpk]
  have eR : ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = ChipSt9.s10B)).map fun l =>
        ((limbRecs (p := p) (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum)).sum =
      ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ p ≤ l.n)).map fun l =>
          ((limbRecs (p := p) ((DA).H (.atom l.n)).2 l.n).map (limbW δ χ)).sum).sum) +
        ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)).map fun l =>
          ((limbRecs (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum).sum) := by
    rw [split3 (fun l : LX9 => ((limbRecs (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum)
      (fun l => decide (l.chip = ChipSt9.s10B)) (fun l => decide (l.chip = .s10B ∧ p ≤ l.n))
      (fun l => decide (l.chip = .s10B ∧ l.n < p))
      (fun l => by
        by_cases h : l.chip = .s10B <;> by_cases h2 : p ≤ l.n <;> simp [h, h2] <;> omega)
      (fun l => by simp only [decide_eq_true_eq]; omega) (rowsOfT9 t).toList]
    congr 1
    congr 1
    refine List.map_congr_left fun l hl => ?_
    have hpl : p ≤ l.n := by
      have := (List.mem_filter.1 hl).2
      simp only [decide_eq_true_eq] at this
      exact this.2
    rw [show idOfA (p := p) Rt hgen l.n = ((DA).H (.atom l.n)).2 from idOf9_big hpl]
  rw [hρ, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.rhoS_total δ b Rt hgen hpG h31A χ hχ, hsplit]
  have hWA : ((DD).preads.map fun x => ComplJ9BBalG.WA9 δ (DD) χ x).sum =
      ((DD).preads.map (ComplJ9BBalG.WA9 δ (DA) χ)).sum := rfl
  linear_combination hold + htag + hlimb + hX + eK + eR - hV - hS + hWA

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.sumB_transfer
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.sBody_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.rhoS_total
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.old_sum_transfer
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.old_part
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.tag_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.tag_total
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.limb_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.limb_total
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.hGSA
