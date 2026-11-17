/-
  Nock/RedTeam/Batch4921Thm54J9ALComplToy.lean

  **J-9 AL general completeness: non-vacuity of `complJ9AL_closed`.**  The toy run of   (`J9AL/ComplJ9ALToyFacts.lean`): `*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12` over
  `addPrims empty [(id_add, add)]` (Goldilocks, `K = KC`, `δ = deltaF`, `b = powerBasis3`), one call of the primitive
  `add` on two big atoms (two limbs each, `≥ p`), so the ALU chip is on.  The template table is
  `rtP Rt0T [(id_add, add)]` with `Rt0T` constant `trivTpl` (the run calls only the primitive, so the prim-aware
  `hRt hregAx` are vacuous).  Every binder of `complJ9AL_closed` is a closed lemma: toy facts, and here the
  strict ALU size `aluLen < 2^31` (`aluLen_toy`, a bound: preg rows `≤ 1`, one `add` block `≤ 2^20` rows by the
  generic `blockB_add_le`, plus the padding row; no kernel evaluation of the table).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALClosed
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALToyFacts
import Nock.RedTeam.Batch4842Thm54J8ComplClose

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4921

open Nock Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Prim
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl j9alDataOf pcallsR primsC opOf)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (factRC charPKC algRC card_KC)

/-! ## 1. Generic ALU block length (an `add` call on atoms of at most three limbs) -/

theorem addL_len : ∀ a b : List ℤ, (CarrySZ.addL a b).length ≤ a.length + b.length
  | [], bs => by simp [CarrySZ.addL]
  | a :: as, [] => by simp [CarrySZ.addL]
  | a :: as, b :: bs => by
    simp only [CarrySZ.addL, List.length_cons]
    have := addL_len as bs
    omega

theorem packQ1_len : ∀ (n : ℕ) (l : List ℕ), l.length ≤ n → (packQ1 l).length ≤ l.length
  | _, [], _ => by simp [packQ1]
  | 0, _ :: _, h => by simp at h
  | n + 1, q :: qs, h => by
    rw [packQ1, List.length_cons]
    have h1 : ((q :: qs).drop 32).length ≤ n := by simp at h ⊢; omega
    have := packQ1_len n _ h1
    have h2 : ((q :: qs).drop 32).length ≤ qs.length := by simp
    simp only [List.length_cons]
    omega

theorem handle_words (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    (handleSlot p o lb r v k s).words.length ≤ 2 + (Nock.Atoms.limbs v).length ∧
      (handleSlot p o lb r v k s).vw.length ≤ 2 + (Nock.Atoms.limbs v).length := by
  unfold handleSlot
  split_ifs <;> simp [splitOf] <;> omega

theorem qslot_words (o : PrimOp) (qs : List ℤ) : (qSlot o true qs).words.length ≤ 1 + qs.length := by
  have := packQ1_len _ (qs.map Int.toNat) le_rfl
  simp only [List.length_map] at this
  by_cases h : qs.map Int.toNat = []
  · simp [qSlot, h]
  · simp [qSlot, h] <;> omega

theorem blockB_add_le {F : Type} [Field F] (p : ℕ) (cl : CallL) (hop : cl.op = .add)
    (ha : (Nock.Atoms.limbs cl.a).length ≤ 3) (hb : (Nock.Atoms.limbs cl.b).length ≤ 3)
    (hc : (Nock.Atoms.limbs cl.c).length ≤ 3) : (blockB (F := F) p cl).length ≤ 2 ^ 20 := by
  obtain ⟨op, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩ := cl
  simp only at hop ha hb hc
  subst hop
  simp only [blockB, slotsOf, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_append,
    slotRows, List.length_map, List.length_range, List.append_nil]
  have h1 := handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA
  have h2 := handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB
  have h3 := handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE
  have h4 := qslot_words .add (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (CarrySZ.addL
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw))
    (CarrySZ.negL (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE).vw))))
  rw [CarrySZ.carr_length] at h4
  have h5 := addL_len (CarrySZ.addL
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw))
    (CarrySZ.negL (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE).vw))
  have h6 := addL_len
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw)
  simp only [zl, CarrySZ.negL, List.length_map] at h4 h5 h6 ⊢
  omega

/-! ## 2. The toy's ALU size -/

theorem pcalls_T : pcallsR ([(idAdd, PrimOp.add)].map Prod.fst) (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.rowsOfT tT) =
    [(idAdd, sT, rT)] := by
  rw [rowsT]; decide

theorem opOf_T : opOf [(idAdd, PrimOp.add)] idAdd = .add := by decide

theorem psLen (ids : List ℕ) : (primsC [(idAdd, PrimOp.add)] ids).length ≤ 1 :=
  (List.length_filter_le _ _).trans (by simp)

open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRun
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

theorem aluLen_toy (Rt0 : ℕ → Nock.Jet.Autogen.Tpl) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen (K := KC) deltaF (RtP Rt0) genT [(idAdd, .add)] < 2 ^ 31 := by
  have hps : (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.psRun (p := pP) (RtP Rt0) genT [(idAdd, .add)]).length ≤ 1 :=
    psLen _
  have hcl : clsRun (p := pP) (RtP Rt0) [(idAdd, .add)] genT =
      callsLOf (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .add)] genT).cells
        (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .add)] genT).H [(idAdd, .add)] [(idAdd, sT, rT)] := by
    unfold clsRun
    rw [pcalls_T]
  have h1 : (Nock.Atoms.limbs (pP + 5)).length ≤ 3 := by rw [limbs_p5]; simp
  have h2 : (Nock.Atoms.limbs (pP + 7)).length ≤ 3 := by rw [limbs_p7]; simp
  have h3 : (Nock.Atoms.limbs (2 * pP + 12)).length ≤ 3 := limbs_len_le3 (by norm_num [pP, Nock.Field.p])
  obtain ⟨cl, hcl1, hop, ha, hb, hc⟩ : ∃ cl, callsLOf (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .add)] genT).cells
      (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .add)] genT).H [(idAdd, .add)] [(idAdd, sT, rT)] = [cl] ∧
      cl.op = .add ∧ cl.a = pP + 5 ∧ cl.b = pP + 7 ∧ cl.c = 2 * pP + 12 := ⟨_, rfl, opOf_T, rfl, rfl, rfl⟩
  have hB := blockB_add_le (F := ZMod pP) pP cl hop (ha ▸ h1) (hb ▸ h2) (hc ▸ h3)
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.tbR tblRun tblP
  rw [hcl, hcl1]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg.pregsP_length,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, zipB_length]
  simp only [pP] at hB ⊢
  omega

/-! ## 3. The toy -/

/-- The base template table (constant `trivTpl`; the run never reads it at a non-primitive id). -/
abbrev Rt0T : ℕ → Nock.Jet.Autogen.Tpl := fun _ => trivTpl

/-- The prim-aware `hRt`: vacuous, every called id is the primitive `id_add`. -/
theorem hRtT : ∀ id ∈ ComplJ8Jet.CalledIds tT, id ∉ [(idAdd, PrimOp.add)].map Prod.fst →
    RgT.R id = some ⟨(Rt0T id).toTemplate pP, Nock.Jet.Autogen.compile pP (Rt0T id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt0T id) = true ∧ (Rt0T id).WellTyped pP :=
  fun id h hn => absurd (by rw [calledT id h]; simp) hn

/-- The prim-aware `hregAx`: vacuous likewise. -/
theorem hregAxT : ∀ id ∈ ComplJ8Jet.CalledIds tT, id ∉ [(idAdd, PrimOp.add)].map Prod.fst →
    ∀ i, (Rt0T id).ax i < pP :=
  fun id h hn => absurd (by rw [calledT id h]; simp) hn

/-- The honest J-9 AL record of the toy run. -/
noncomputable abbrev BL := ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0T [(idAdd, PrimOp.add)]) genT [(idAdd, PrimOp.add)]
  hpGT (h31AT Rt0T)

open Classical in
/-- **`complJ9AL_toy`: J-9 AL completeness at a concrete run with an ALU primitive, every hypothesis discharged.**
The run is one call of the primitive `add` on two atoms of two limbs each (both `≥ p`) over the Goldilocks prime,
so the ALU chip is on: `*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12`.  For this run, `AcceptsJ9AL`
accepts at every good coin, the fraction of coins that are not good is at most `ε_c`, the trace family is staged
(`StJ9AL`), the claim holds (`HoldsN`), and, as `|K| = cK`, `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9AL_toy :
    (∀ χ, BL.Good χ → AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
      BL.rows BL.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BL.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BL.epsC) ∧
    RealIOJ9AL.StJ9AL BL.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sT fT rT) ∧
    (Fintype.card KC = VclL.Events.cK →
      BL.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
        BL.rows BL.g) :=
  ComplJ9ALClosed.complJ9AL_closed deltaF powerBasis3 Rt0T genT [(idAdd, PrimOp.add)] hpGT hax9T hop5T (hleafT Rt0T)
    hwalk9T (hwalkAT Rt0T) hRtT hregAxT hndT hprimT (h31AT Rt0T) (aluLen_toy Rt0T) hlimbT hnoDecT

open Classical in
/-- **The toy figure, hypothesis-free**: `ε_c < 2^-120` and an accepting coin at `KC`. -/
theorem complJ9AL_toy_figure :
    BL.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
        BL.rows BL.g :=
  complJ9AL_toy.2.2.2.2 card_KC

end Nock.RedTeam.Batch4921

#print axioms Nock.RedTeam.Batch4921.aluLen_toy
#print axioms Nock.RedTeam.Batch4921.complJ9AL_toy
#print axioms Nock.RedTeam.Batch4921.complJ9AL_toy_figure
