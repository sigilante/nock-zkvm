/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Comp.lean

  **The compute conjunct `hsatX` of `AcceptsJ8''''` at THE
  inhabitant** `c0 = *[[0 0] [0 1]] = [0 0]` (`InhabJ8Base`: one compute row, state `s0`, axis `1`, empty
  registry).

  For ANY honest handle map `H` (`HdlOK p H`):
  * `mC0 H` — the claim message (serial `(H x).2`, rank limbs `rkC x`), so that `pubVJ8` slots `0..5` are the
    handles `hk / hv` of `s0, f0, s0` (`hpub0`);
  * `ρC0`, `ρSC0` — the honest accumulator totals (`accV` at the one row, read at a dummy public vector: the
    totals do not read the publics, `accV_pub`); every slot `hρ` needs is a slot of `M.ρ 3`, `M.ρ 4`, `M.ρS`;
  * `trC0` — the honest trace `polyX` (at the limb data `pdX sx0`; the run has no op-5 row).
  * **`hsatX_c0`** / **`hsatX_c0_qX`** — `hsatX` holds at `n = 1`, any nodes and orbit, under two coin
    hypotheses: `χ₁₃ = αW ≠ 0` (walk-coin order) and `compress (γH′, ρH′) (lift (recF0 H)) ≠ 0` (the one
    slot pole of the row; `compress_recF0`: `ρH′ + idx f0 + γH′⁴ ≠ 0`).
  * Closed forms (`ρC0_3`, `compress_recF0`, `ρC0_4`, `ρSC0_eq`): the row consumes exactly ONE handle record,
    the cell-export record `cellRec(f0; [0], [1]) = (idx f0, 0, 0, 0, 1)`, into `ρ₃`, multiplicity 1:
    `ρ₃ = (ρH′ + idx f0 + γH′⁴)⁻¹`; `ρ₄ = 0` (axis 1: the `s0` path read is gated off by `z1`); `ρ_S = 0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX
import Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
import Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Comp

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS mapC mapM chalAlphaW chalGammaW pubIC pubSeed
  pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.SVFrame

noncomputable section

/-- The one-row BFS forest. -/
theorem bfs0 : bfsForest [t0] = [t0] := by simp [bfsForest, t0, mkX]

/-- The honest noun row of `t0`. -/
def r0 : RowNX := { st := .s0, s := s0, f := f0, e := s0, fh := .atom 0, ft := .atom 1 }

theorem row0 : rowOfSkelX t0.label = r0 := rfl

theorem rowAt0 : rowAtWX [t0] 1 = r0 := rfl

def sx0 : ℕ → ℕ → ℕ := fun _ _ => 0

section F
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ)

theorem baseT0 (c : ℕ) : baseT (F := F) H (pdX sx0) [t0] 0 c = colX H (pdX sx0) r0 1 1 c := by
  simp [baseT, rowAt0, flX, llX]

end F

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The claim message: serial = the handle value, rank limbs as the verifier computes them. -/
def mC0 (H : Noun → ℕ × ℕ) : ClaimMsgVS := fun k =>
  ((H (claimNoun c0 k)).2, Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.rkC (claimNoun c0 k))

/-- The accumulator totals, read at a dummy public vector (`ρ = 0`). -/
def accT (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (a : ℕ) : K :=
  accV b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) 0 0 χ) a 1

def ρC0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : Fin 5 → 𝕂′ := fun i =>
  if (i : ℕ) = 3 then Quad.mk _ (accT δ b H χ 0) (accT δ b H χ 1)
  else if (i : ℕ) = 4 then Quad.mk _ (accT δ b H χ 2) (accT δ b H χ 3) else 0

def ρSC0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (accT δ b H χ 4) (accT δ b H χ 5)

def pubC0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  pubVJ8 δ b c0 (mC0 H) (ρC0 δ b H χ) (ρSC0 δ b H χ) χ

def αC0 (χ : Coins frameJ8 K) : K := limbVal b (chalVJ8 b χ) chalAlphaW
def γC0 (χ : Coins frameJ8 K) : K := limbVal b (chalVJ8 b χ) chalGammaW

def trC0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) {n : ℕ} (nodes : Fin n → ZMod p) (w : ℕ) :
    Fin w → (ZMod p)[X] :=
  polyX b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubC0 δ b H χ) (lnW (αC0 b χ)) (cntW [t0] (αC0 b χ))
    (accW (F := ZMod p) H [t0] (αC0 b χ) (γC0 b χ)) nodes w

theorem limbVal_coord (x : K) (f : ℕ → ZMod p) (c : ℕ) (h : ∀ k : Fin 3, f (c + k) = coord b x k) :
    limbVal b f c = x := by
  unfold limbVal
  simp only [h]
  exact b.sum_repr x

theorem αC0_eq (χ : Coins frameJ8 K) : αC0 b χ = χ ⟨13, by decide⟩ := by
  refine limbVal_coord b _ _ _ fun k => ?_
  fin_cases k <;> simp [chalVJ8, chalVHQ, coinHQ, coinH, toVS, toVSQ, chalAlphaW, cAlphaW]

theorem γC0_eq (χ : Coins frameJ8 K) : γC0 b χ = χ ⟨14, by decide⟩ := by
  refine limbVal_coord b _ _ _ fun k => ?_
  fin_cases k <;> simp [chalVJ8, chalVHQ, coinHQ, coinH, toVS, toVSQ, chalGammaW, cGamW]

theorem pub_lo (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (j : ℕ) (hj : j < 6) :
    pubC0 δ b H χ j = (labelF (F := ZMod p) c0 (mC0 H)).getD j 0 := by
  simp [pubC0, pubVJ8, pubVHQ, pubVH, show j < 27 by omega, show j < 21 by omega, hj]

theorem hpub0 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (χ : Coins frameJ8 K) :
    pubC0 δ b H χ 0 = hk H s0 ∧ pubC0 δ b H χ 1 = hv H s0 ∧ pubC0 δ b H χ 2 = hk H f0 ∧
      pubC0 δ b H χ 3 = hv H f0 ∧ pubC0 δ b H χ 4 = hk H s0 ∧ pubC0 δ b H χ 5 = hv H s0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [pub_lo δ b H χ _ (by norm_num)] <;>
  simp [labelF, hvalF, claimH, claimNoun, c0, mC0, Nock.NockVMROM.Thm54.VclL.Handle.claimHandle, s0, f0, hk, hv,
    hH.cell]

theorem hpIC0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : limbVal b (pubC0 δ b H χ) pubIC = αC0 b χ := by
  rw [αC0_eq]
  refine limbVal_coord b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubC0, pubVJ8, pubVHQ, pubVH, toVS, toVSQ, pubIC, cAlphaW]

theorem hpO0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : limbVal b (pubC0 δ b H χ) pubOut = 0 := by
  unfold limbVal
  refine Finset.sum_eq_zero fun k _ => ?_
  fin_cases k <;> simp [pubC0, pubVJ8, pubVHQ, pubVH, pubOut]

theorem curW0 (H : Noun → ℕ × ℕ) (γ : K) :
    curW (F := ZMod p) H [t0] γ 1 = Nock.NockVMROM.Thm54.VclL.Handle.rlcL γ 0 ((hlX (F := ZMod p) H (s0, f0, s0)).map (algebraMap (ZMod p) K)) := by
  simp [curW, Walk.curCol, nodeValX, lblX, tripOf, t0, mkX]

theorem hpS0 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (χ : Coins frameJ8 K) :
    limbVal b (pubC0 δ b H χ) pubSeed = curW (F := ZMod p) H [t0] (γC0 b χ) 1 * αC0 b χ := by
  rw [αC0_eq, γC0_eq, curW0]
  rw [limbVal_coord b (seedVS (F := ZMod p) c0 (mC0 H) (toVS (toVSQ χ))) _ _ fun k => by
    fin_cases k <;> simp [pubC0, pubVJ8, pubVHQ, pubVH, pubSeed]]
  simp [seedVS, labelF, hvalF, claimH, claimNoun, c0, mC0, Nock.NockVMROM.Thm54.VclL.Handle.claimHandle,
    hlX, hk, hv, hH.cell, Nock.NockVMROM.Thm54.VclL.Handle.rlcL, toVS, toVSQ, cAlphaW, cGamW, s0, f0]
  ring

theorem slotAt_mem (k : ℕ) : slotAt (F := ZMod p) k ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p) := by
  unfold slotAt; split <;> simp [Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX]

theorem invV_pub (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pub1 pub2 : ℕ → ZMod p) (j : ℕ) {S : SlotX (ZMod p)} (hS : S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p)) :
    invV b δ H pd W chalV pub1 j S = invV b δ H pd W chalV pub2 j S := by
  obtain ⟨h1, h2⟩ := dVal_aVal_congr b δ hS (env0 H pd W chalV pub1 j) (env0 H pd W chalV pub2 j)
    (fun c _ => rfl) rfl
  simp only [invV, h1, h2]

theorem preT_pub (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pub1 pub2 : ℕ → ZMod p) (j c : ℕ) :
    preT b δ H pd W chalV pub1 j c = preT b δ H pd W chalV pub2 j c := by
  unfold preT invCol
  rw [invV_pub δ b H pd W chalV pub1 pub2 j (slotAt_mem _)]

theorem accV_pub (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pub1 pub2 : ℕ → ZMod p) (a i : ℕ) :
    accV b δ H pd W chalV pub1 a i = accV b δ H pd W chalV pub2 a i := by
  unfold accV
  refine Finset.sum_congr rfl fun j _ => ?_
  exact termVal_congr b _ _ _ _ fun c _ => preT_pub δ b H pd W chalV pub1 pub2 j c

theorem hρ0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubC0 δ b H χ (pubOfA a + k) =
      coord b (accV b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubC0 δ b H χ) a 1) k := by
  intro a ha k
  rw [accV_pub δ b H (pdX sx0) [t0] (chalVJ8 b χ) (pubC0 δ b H χ) (pubVJ8 δ b c0 (mC0 H) 0 0 χ)]
  change _ = coord b (accT δ b H χ a) k
  interval_cases a <;> fin_cases k <;>
    simp [pubOfA, pubC0, pubVJ8, pubVHQ, pubVH, ρC0, ρSC0, pubRhoX, pubRhoXIm, pubRhoP, pubRhoPIm,
      pubRhoSX, pubRhoSXi, Quad.re_mk, Quad.im_mk]



open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCQ coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX denQX_val)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

/-- The cell-handle record of `f0 = [0 1]` the compute row consumes: `(idx f0, 0, 0, 0, 1)`. -/
def recF0 (H : Noun → ℕ × ℕ) : Fin 5 → K := fun c =>
  algebraMap (ZMod p) K (![((H f0).2 : ZMod p), 0, 0, 0, 1] c)

theorem dVal_slot0 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (hp : 2 ≤ p) (χ : Coins frameJ8 K) (pv : ℕ → ZMod p) :
    dVal b δ (slot0X (F := ZMod p)) (Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv 0) =
      compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) := by
  simp only [dVal, slotDQ, slot0X, qadd_val, qconst_val, List.map_cons, List.map_nil,
    Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ.sumQ_val, qmul_val, qlift_val]
  set e := Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv 0 with he
  have hact : (⟨opStatesX, CoeffExpr.const 1, cellRecX xF xFh xFt, Bal.x⟩ : EntX (ZMod p)).act.eval e = 1 := by
    simp [he, EntX.act, selS, opStatesX, CoeffExpr.sumList, CoeffExpr.eval, cc,
      Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0, baseT0, colX, r0,
      Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx]
  have hD : Q.val δ (denQX (ZMod p) δ (cellRecX xF xFh xFt)) (gatherEnv b e) e =
      compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) := by
    rw [show Q.val δ (denQX (ZMod p) δ (cellRecX xF xFh xFt)) (gatherEnv b e) e =
      Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e (cellRecX xF xFh xFt) from rfl,
      denQX_val δ _ _ _ 5 (by decide)]
    have hc : coinsCQ δ (gatherEnv b e) = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) := by
      rw [← coinsCV_J8 δ b χ]; rfl
    rw [hc]
    congr 2
    funext c
    have h0 : H (.atom 0) = (0, 0) := hH.small 0 (by omega)
    have h1 : H (.atom 1) = (0, 1) := hH.small 1 (by omega)
    fin_cases c <;> simp [recF0, keyX, Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8.keyXN, cellRecX, recOf,
      Nock.NockVMROM.Thm54.VclL.Handle.ChipH.cellRec, RE.ev, he, Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0,
      baseT0, colX, hN, r0, hk, hv, h0, h1, xF, xFh, xFt, hdX]
  rw [hact, hD]
  simp


theorem aVal_zero (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (pv : ℕ → ZMod p) {S : SlotX (ZMod p)}
    (hS : S = slot1X ∨ S = slot2X ∨ S = slot3X) :
    aVal b δ S (Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv 0) = 0 := by
  rcases hS with rfl | rfl | rfl <;>
  simp only [aVal, slotAQ, slot1X, slot2X, slot3X, qadd_val, qlift_val, qconst_val, qmul_val] <;>
  simp [Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0, baseT0, CoeffExpr.sumList, EntX.act, CoeffExpr.eval,
    selS, cc, notC, l2X, l3X, colX, r0, Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx, cZ1, cFast, z1X, fastX,
    cPr, cPr2, isPair, prX, pr2X, Nock.NockVMROM.Thm54.VclL.Handle.ChipH.consCol, sS10, sS11j, kcE, kbE, kbX, xSf1,
    hdX, cB, hb, hN]

theorem hnb0 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (hp : 2 ≤ p) (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    (hden : compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
      (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) ≠ 0) :
    ∀ j < 1, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      dVal b δ S (Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv j) ≠ 0 ∨
        aVal b δ S (Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv j) = 0 := by
  intro j hj S hS
  obtain rfl : j = 0 := by omega
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | hS
  · left; rw [dVal_slot0 δ b H hH hp χ pv]; exact hden
  · right; exact aVal_zero δ b H χ pv hS


theorem inTree_t0 {u : NTree SkelX} (h : InTree t0 u) : u = t0 := by
  cases h with
  | here => rfl
  | sub hs _ => simp [t0, mkX] at hs

theorem formLeaf0 (hp : 2 < p) : FormLeafX (ringChar (ZMod p)) t0 := by
  intro u hu a ha
  rw [inTree_t0 hu, ZMod.ringChar_zmod_n] at *
  simp [t0, mkX, f0, leavesOf] at ha
  omega

theorem op5Depth0 : Op5DepthX 0 t0 := by
  intro u hu hs
  rw [inTree_t0 hu] at hs
  simp [t0, mkX] at hs

theorem jetKey0 (q : ℕ) : JetKeyX q t0 := by
  intro u hu hs
  rw [inTree_t0 hu] at hs
  simp [t0, mkX] at hs

theorem hord0 (χ : Coins frameJ8 K) (hα : χ ⟨13, by decide⟩ ≠ 0) : [t0].length ≤ orderOf (αC0 b χ) := by
  rw [αC0_eq]
  have hc : 1 < Fintype.card K := Fintype.one_lt_card
  have : IsOfFinOrder (χ ⟨13, by decide⟩) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨Fintype.card K - 1, by omega, FiniteField.pow_card_sub_one_eq_one _ hα⟩
  exact this.orderOf_pos


theorem hsatX_c0 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (hB : Nock.Atoms.B ≤ p) (χ : Coins frameJ8 K)
    (hα : χ ⟨13, by decide⟩ ≠ 0)
    (hden : compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
      (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) ≠ 0)
    {hh n : ℕ} (hn : 0 < n) (hN : n = 1) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 hh) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) (ρC0 δ b H χ) (ρSC0 δ b H χ) χ) orbit)
      (trC0 δ b H χ nodes (computeChipVCLHX hn nodes b δ (chalVJ8 b χ)
        (pubVJ8 δ b c0 (mC0 H) (ρC0 δ b H χ) (ρSC0 δ b H χ) χ) orbit).rap.w) := by
  have hB32 : Nock.Atoms.B = 2 ^ 32 := rfl
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hH' : HdlOK (ringChar (ZMod p)) H := by rw [hrc]; exact hH
  unfold trC0
  rw [← bfs0]
  refine computeChipVCLHX_honest_sat_tree δ gen0 H sx0 hH' (by omega) (by omega)
    (D := 0) (formLeaf0 (by omega)) op5Depth0 (jetKey0 _) (by rw [hrc]; norm_num; omega) (αC0 b χ) (γC0 b χ)
    (by rw [bfs0]; exact hord0 b χ hα) hn (by rw [bfs0, hN]; rfl) nodes ?_ b _ _ orbit ?_ rfl rfl
    (hpIC0 δ b H χ) (by rw [bfs0]; exact hpS0 δ b H hH χ) (hpO0 δ b H χ) (hpub0 δ b H hH χ)
    (by rw [bfs0, hN]; exact hρ0 δ b H χ)
    (by rw [bfs0]; intro j hj; exact hnb0 δ b H hH (by omega) χ _ hden j (hN ▸ hj))
  · intro i j _; subst hN; exact Subsingleton.elim i j
  · intro i hi; omega


theorem accT_term (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (a : ℕ) :
    accT δ b H χ a = termVal b (slotsF (accSpec a).1 (accSpec a).2)
      (env1 b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) 0 0 χ) 0) := by
  simp [accT, accV]

theorem limb_invP (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pv : ℕ → ZMod p) (j s : ℕ) (hs : s < 4) :
    limbVal b (preT b δ H pd W chalV pv j) (69 + 6 * s) = Quad.re _ (invV b δ H pd W chalV pv j (slotAt s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have h1 : (69 + 6 * s + (k : ℕ) - 69) / 6 = s := by omega
  have h2 : (69 + 6 * s + (k : ℕ) - 69) % 6 = k := by omega
  unfold preT invCol
  rw [if_neg (by omega), if_pos (by omega), h1, h2, if_pos k.isLt]

theorem limb_invImP (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pv : ℕ → ZMod p) (j s : ℕ) (hs : s < 4) :
    limbVal b (preT b δ H pd W chalV pv j) (72 + 6 * s) = Quad.im _ (invV b δ H pd W chalV pv j (slotAt s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have h1 : (72 + 6 * s + (k : ℕ) - 69) / 6 = s := by omega
  have h2 : (72 + 6 * s + (k : ℕ) - 69) % 6 = k + 3 := by omega
  unfold preT invCol
  rw [if_neg (by omega), if_pos (by omega), h1, h2, if_neg (by omega)]
  simp

theorem accT_zero (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (a : ℕ) (ha : 2 ≤ a) (ha' : a < 6) :
    accT δ b H χ a = 0 := by
  rw [accT_term]
  interval_cases a <;>
  simp [termVal, slotsF, slotsQ, Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX, Nock.NockVMROM.Thm54.VclL.Handle.castSlot, SlotX.actB, accSpec,
    slot0X, slot1X, slot2X, slot3X, mapC, CoeffExpr.sumList, EntX.act, selS, cc, notC, CoeffExpr.eval, env1,
    preT, baseT0, colX, r0, Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx, cZ1, z1X, prX, cPr, sS10,
    fastX, cFast, pr2X, cPr2, isPair, sS11j]

theorem accT_01 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) :
    accT δ b H χ 0 = Quad.re _ (invV b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) 0 0 χ) 0 slot0X) ∧
    accT δ b H χ 1 = Quad.im _ (invV b δ H (pdX sx0) [t0] (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) 0 0 χ) 0 slot0X) := by
  constructor <;> rw [accT_term] <;>
  simp [termVal, slotsF, slotsQ, Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX, Nock.NockVMROM.Thm54.VclL.Handle.castSlot, SlotX.actB, accSpec,
    slot0X, slot1X, slot2X, slot3X, mapC, CoeffExpr.sumList, EntX.act, selS, cc, notC, CoeffExpr.eval, env1,
    preT, baseT0, colX, r0, Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx, cZ1, z1X, prX, cPr, sS10,
    fastX, cFast, pr2X, cPr2, isPair, sS11j, l2X, l3X, opStatesX, Nock.NockVMROM.Thm54.VclL.Handle.ChipH.consCol]
  · exact limb_invP δ b H _ _ _ _ 0 0 (by norm_num)
  · exact limb_invImP δ b H _ _ _ _ 0 0 (by norm_num)


theorem aVal_slot0 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (pv : ℕ → ZMod p) :
    aVal b δ (slot0X (F := ZMod p)) (Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0 H (pdX sx0) [t0] (chalVJ8 b χ) pv 0) = 1 := by
  simp only [aVal, slotAQ, slot0X, qadd_val, qlift_val, qconst_val]
  simp [Nock.NockVMROM.Thm54.VclL.HonestTraceX.env0, baseT0, CoeffExpr.sumList, EntX.act, CoeffExpr.eval,
    selS, cc, colX, r0, Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx, opStatesX]

/-- **Closed form of the cell-export accumulator `ρ₃`**: the one record the compute row consumes. -/
theorem ρC0_3 (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (hp : 2 ≤ p) (χ : Coins frameJ8 K) :
    ρC0 δ b H χ 3 = (compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
      (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)))⁻¹ := by
  obtain ⟨h0, h1⟩ := accT_01 δ b H χ
  simp only [ρC0, if_pos (show ((3 : Fin 5) : ℕ) = 3 from rfl), h0, h1, Quad.mk_re_im, invV, aVal_slot0,
    dVal_slot0 δ b H hH hp, one_mul]

theorem compress_recF0 (H : Noun → ℕ × ℕ) (γ ρ : 𝕂′) :
    compress (⟨γ, ρ⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) =
      ρ + algebraMap K 𝕂′ (algebraMap (ZMod p) K ((H f0).2 : ZMod p)) + γ ^ 4 := by
  simp [compress, Walk.rlc, Fin.sum_univ_five, liftRec, recF0]
  ring

theorem ρC0_4 (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : ρC0 δ b H χ 4 = 0 := by
  simp [ρC0, accT_zero δ b H χ 2 (by norm_num) (by norm_num), accT_zero δ b H χ 3 (by norm_num) (by norm_num),
    Quad.mk]

theorem ρSC0_eq (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) : ρSC0 δ b H χ = 0 := by
  simp [ρSC0, accT_zero δ b H χ 4 (by norm_num) (by norm_num), accT_zero δ b H χ 5 (by norm_num) (by norm_num),
    Quad.mk]

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

theorem hsatX_c0_qX (H : Noun → ℕ × ℕ) (hH : HdlOK p H) (hB : Nock.Atoms.B ≤ p) (χ : Coins frameJ8 K)
    (hα : χ ⟨13, by decide⟩ ≠ 0)
    (hden : compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
      (liftRec (L := 𝕂′) (recF0 (p := p) (K := K) H)) ≠ 0)
    (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (hN : Pb.n = 1) (htr : tr.C = trC0 δ b H χ Pb.nodes 123) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) (ρC0 δ b H χ) (ρSC0 δ b H χ) χ)
        Pb.orbit)
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c0 (mC0 H) (ρC0 δ b H χ) (ρSC0 δ b H χ) χ)) := by
  have h := hsatX_c0 δ b H hH hB χ hα hden Pb.hn hN Pb.nodes Pb.orbit
  unfold qX
  rw [htr]
  exact h

end Main

end
end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Comp
