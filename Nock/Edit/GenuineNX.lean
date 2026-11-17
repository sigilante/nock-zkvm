/-
  Nock/Edit/GenuineNX.lean

  **Card C-2 : the ℕ-level (`HoldsN`) twin of E-0's
  `GenuineSkelFX` and its soundness, with the edit chain (C-2 step 2).**

  * `KidInputsNX` — E-0's `KidInputsX` on every state but `s11j`, where E-0 had `False`: a jetted
    row has ONE child, the clue `(s, f_ttt)` (SPEC §3.1 fanout 1).
  * `RowOutputNX R` — E-0's `RowOutputFX` at ℕ (OP4 is `Noun.lus`, Nock 4K increment, no field
    wrap), and `s11j`: the clue child's value is an atom `id` (the jet key), `R id = some j`,
    `j.c = f_tt` (the hinted body) and `j.T.rel s e` (the J record).  The hint's tag does not
    appear: `evalN` ignores it, so soundness does not need it.  The generator's `jetHit` emits jet
    rows only under the tag `%wild`; the chip pins the tag's value in the field (`ChipHX.s11j_wild`),
    which with `wildTag < p` is the atom `%wild` (`WildTagX.s11j_tag`).
  * `GenuineNX R` — the tree predicate, with E-0's `roles` field (chain positions are exactly
    `chainPosX`).
  * **`genuineNX_sem`** — every real node `HoldsN`, every chain node `ChainOK` at its atom axis.
    **`edit_chain_sound`** (step 2): an `s10` node over a `s10L … s10T` chain gives
    `HoldsN` of the edit formula, through `edit_iff_chainOK`'s direction `edit_of_slots`.
  * `holdsN_of_genuineNX` — the claim from a genuine tree with a real root.
-/
import Nock.Edit.SemanticsX
import Nock.Jet.Semantics
import Nock.Semantics

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Edit

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.Jet (Registry HoldsN JetSpec)

/-! ## §1 The ℕ-level row specs -/

/-- `KidInputsX` with the `s11j` arm: one child, the clue. -/
def KidInputsNX : StateX → Noun → Noun → List RowX → Prop
  | .s11j, s, f, [kD] => kD.subject = s ∧ kD.formula = tl (hd (tl f))
  | .s11j, _, _, _ => False
  | st, s, f, ks => KidInputsX st s f ks

/-- **The row output at ℕ** (`RowOutputFX` with exact increment, and the jet arm). -/
def RowOutputNX (R : Registry) : StateX → Noun → Noun → List RowX → Noun → Prop
  | .s0, s, f, _, e => Noun.slot (op0Axis f) s = some e
  | .s1, _, f, _, e => e = tl f
  | .cons, _, _, [k0, k1], e => e = .cell k0.evaluation k1.evaluation
  | .s3, _, _, [k0], e => e = Noun.wut k0.evaluation
  | .s4, _, _, [k0], e => Noun.lus k0.evaluation = some e
  | .s5, _, _, [k0, k1], e => e = Noun.tis k0.evaluation k1.evaluation
  | .s2, _, _, [_, _, k2], e => e = k2.evaluation
  | .s6, _, _, [kT, kC], e =>
      (kC.evaluation = .atom 0 ∨ kC.evaluation = .atom 1) ∧ e = kT.evaluation
  | .s7, _, _, [kM, _], e => e = kM.evaluation
  | .s8, _, _, [kM, _], e => e = kM.evaluation
  | .s9, _, _, [_, kI], e => e = kI.evaluation
  | .s10, _, f, [kN, _, kE], e =>
      Noun.slot (op10Axis f) e = some kN.evaluation ∧ kE.evaluation = e
  | .s10L, s, f, [k], e =>
      k.evaluation = e ∧
        ∃ x, Noun.slot (chainAxis f ^^^ 1) s = some x ∧ Noun.slot (chainAxis f ^^^ 1) e = some x
  | .s10T, _, _, [], _ => True
  | .s11s, _, _, [k], e => e = k.evaluation
  | .s11d, _, _, [_, kB], e => e = kB.evaluation
  | .s11j, s, f, [kD], e =>
      ∃ (id : ℕ) (j : JetSpec), kD.evaluation = .atom id ∧ R id = some j ∧ j.c = tl (tl f) ∧
        j.T.rel s e
  | _, _, _, _, _ => False

/-- **A genuine tree at the extended ISA, ℕ-level** (E-0's `GenuineSkelFX` twin). -/
inductive GenuineNX (R : Registry) : NTree RowX → Prop
  | node {s : RowX} {kids : List (NTree RowX)}
      (shape : FormulaShapeX s.state s.formula)
      (inputs : KidInputsNX s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutputNX R s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (roles : ∀ i (h : i < kids.length), (kids[i]'h).label.state.isChain = chainPosX s.state i)
      (children : ∀ k ∈ kids, GenuineNX R k) :
      GenuineNX R (.node s kids)

/-! ## §2 Soundness -/

/-- What a genuine node proves: a chain node its `ChainOK`, a real node `HoldsN`. -/
def SemNX (st : StateX) (s f e : Noun) : Prop :=
  if st.isChain then ChainOK (chainAxis f) s e ∧ ∃ a : ℕ, f = .atom a
  else HoldsN ⟨s, f, e⟩

theorem semNX_real {st : StateX} {s f e : Noun} (hst : st.isChain = false)
    (h : SemNX st s f e) : HoldsN ⟨s, f, e⟩ := by
  simpa [SemNX, hst] using h

theorem semNX_chain {st : StateX} {s f e : Noun} (hst : st.isChain = true)
    (h : SemNX st s f e) : ChainOK (chainAxis f) s e := by
  simp only [SemNX, hst, if_true] at h; exact h.1

/-- A common fuel for finitely many successful runs. -/
theorem common_fuel (P : NTree RowX → Prop) : ∀ (kids : List (NTree RowX)),
    (∀ k ∈ kids, P k → HoldsN ⟨k.label.subject, k.label.formula, k.label.evaluation⟩) →
    ∃ m, ∀ k ∈ kids, P k → evalN m k.label.subject k.label.formula = some k.label.evaluation
  | [], _ => ⟨0, by simp⟩
  | k :: ks, h => by
    obtain ⟨m, hm⟩ := common_fuel P ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    by_cases hp : P k
    · obtain ⟨n, hn⟩ := h k (List.mem_cons_self ..) hp
      refine ⟨max n m, fun k' hk' hp' => ?_⟩
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact evalN_mono (Nat.le_max_left _ _) hn
      · exact evalN_mono (Nat.le_max_right _ _) (hm k' hk' hp')
    · refine ⟨m, fun k' hk' hp' => ?_⟩
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact absurd hp' hp
      · exact hm k' hk' hp'

/-- **The soundness of a genuine ℕ tree** (C-2 steps 1–2 at the noun level): every real node
`HoldsN`, every chain node satisfies `ChainOK` at its atom axis. -/
theorem genuineNX_sem {R : Registry} (hR : R.Faithful) {T : NTree RowX} (hT : GenuineNX R T) :
    SemNX T.label.state T.label.subject T.label.formula T.label.evaluation := by
  induction hT with
  | @node s kids shape inputs output roles children ih =>
    obtain ⟨m, hm⟩ := common_fuel (fun k => k.label.state.isChain = false) kids
      (fun k hk hc => semNX_real hc (ih k hk))
    have run : ∀ k ∈ kids, k.label.state.isChain = false →
        evalN m k.label.subject k.label.formula = some k.label.evaluation := hm
    have chain : ∀ k ∈ kids, k.label.state.isChain = true →
        ChainOK (chainAxis k.label.formula) k.label.subject k.label.evaluation :=
      fun k hk hc => semNX_chain hc (ih k hk)
    simp only [NTree.label]
    cases hst : s.state with
    | s0 =>
      rw [hst] at shape inputs output
      obtain ⟨ax, hf⟩ := shape
      simp only [RowOutputNX, hf, op0Axis] at output
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf]; simpa [evalN] using output
    | s1 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      simp only [RowOutputNX, hf, tl, StrategyOfTraces.nounTail] at output
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN]
    | cons =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, r0, r1]
    | s3 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, r0]
    | s4 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf]; simp [evalN, r0, output]
    | s5 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, r0, r1]
    | s2 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      have r2 := run k2 (by simp) (roles 2 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      rw [hs2, hf2] at r2
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, r0, r1, r2]
    | s6 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsC, hfC, hsT, hfT⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      obtain ⟨hb, he⟩ := output
      have rC := run kC (by simp) (roles 1 (by simp))
      have rT := run kT (by simp) (roles 0 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rC
      rw [hsT, hfT, hf] at rT
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rT
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, he]
      rcases hb with hb | hb
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalN, rC, rT]
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalN, rC, rT]
    | s7 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, rH, rM]
    | s8 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, rH, rM]
    | s9 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, hf⟩ := shape
      rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsC, hfC, hsI, hslot⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have rC := run kC (by simp) (roles 0 (by simp))
      have rI := run kI (by simp) (roles 1 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [tl, StrategyOfTraces.nounTail] at rC
      rw [hsI] at rI
      rw [hf] at hslot
      simp only [op9Axis] at hslot
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, rC, hslot, rI]
    | s10 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kN, _ | ⟨kO, _ | ⟨kE, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsN, hfN, hsO, hfO, hsE, hfE⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      obtain ⟨hslot, hE⟩ := output
      have rN := run kN (by simp) (roles 0 (by simp))
      have rO := run kO (by simp) (roles 1 (by simp))
      have cE := chain kE (by simp) (roles 2 (by simp))
      rw [hsN, hfN, hf] at rN
      rw [hsO, hfO, hf] at rO
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rN rO
      rw [hfE, hsE, hE, hf] at cE
      simp only [chainAxis, op10Axis] at cE
      rw [hf] at hslot
      simp only [op10Axis] at hslot
      have hed := edit_of_slots cE hslot
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf]; simp [evalN, rN, rO, hed]
    | s10L =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, hf, hax⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      obtain ⟨hke, hsib⟩ := output
      have ck := chain k (by simp) (roles 0 (by simp))
      rw [hfk, hsk, hke, hf] at ck
      simp only [chainAxis] at ck hsib
      rw [hf] at hsib
      simp only [chainAxis] at hsib
      simp only [SemNX, StateX.isChain, if_true, hf, chainAxis]
      exact ⟨chainOK_step hax hsib ck, ax, rfl⟩
    | s10T =>
      rw [hst] at shape
      rw [shape]
      simp only [SemNX, StateX.isChain, if_true, chainAxis]
      exact ⟨chainOK_of_lt_two (by norm_num) _ _, 1, rfl⟩
    | s11s =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, body, hf⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have rk := run k (by simp) (roles 0 (by simp))
      rw [hsk, hfk, hf] at rk
      simp only [tl, StrategyOfTraces.nounTail] at rk
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, rk]
    | s11d =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, clue, body, hf⟩ := shape
      rcases kids with _ | ⟨kD, _ | ⟨kB, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsNX, KidInputsX] at inputs
      obtain ⟨hsD, hfD, hsB, hfB⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      have rD := run kD (by simp) (roles 0 (by simp))
      have rB := run kB (by simp) (roles 1 (by simp))
      rw [hsD, hfD, hf] at rD
      rw [hsB, hfB, hf] at rB
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rD rB
      simp only [SemNX, StateX.isChain]
      refine ⟨m + 1, ?_⟩
      rw [hf, output]; simp [evalN, rD, rB]
    | s11j =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, clue, body, hf⟩ := shape
      rcases kids with _ | ⟨kD, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsNX] at inputs
      obtain ⟨hsD, hfD⟩ := inputs
      simp only [RowOutputNX, List.map_cons, List.map_nil] at output
      obtain ⟨id, j, hid, hj, hc, hrel⟩ := output
      have rD := run kD (by simp) (roles 0 (by simp))
      rw [hsD, hfD, hf] at rD
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rD
      rw [hf] at hc
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at hc
      obtain ⟨n, hn⟩ := (hR id j hj).1 s.subject s.evaluation hrel
      rw [hc] at hn
      simp only [SemNX, StateX.isChain]
      refine ⟨max m n + 1, ?_⟩
      rw [hf]
      simp [evalN, evalN_mono (Nat.le_max_left m n) rD, evalN_mono (Nat.le_max_right m n) hn]

/-- **A genuine ℕ tree with a real root `HoldsN`.** -/
theorem genuineNX_holdsN {R : Registry} (hR : R.Faithful) {T : NTree RowX} (hT : GenuineNX R T)
    (hreal : T.label.state.isChain = false) :
    HoldsN ⟨T.label.subject, T.label.formula, T.label.evaluation⟩ :=
  semNX_real hreal (genuineNX_sem hR hT)

/-- A chain node of a genuine ℕ tree satisfies `ChainOK` at its atom axis. -/
theorem genuineNX_chainOK {R : Registry} (hR : R.Faithful) {T : NTree RowX} (hT : GenuineNX R T)
    (hchain : T.label.state.isChain = true) :
    ChainOK (chainAxis T.label.formula) T.label.subject T.label.evaluation :=
  semNX_chain hchain (genuineNX_sem hR hT)

/-- **The claim from a genuine ℕ tree** rooted at it. -/
theorem holdsN_of_genuineNX {R : Registry} (hR : R.Faithful) {T : NTree RowX}
    (hT : GenuineNX R T) (hreal : T.label.state.isChain = false) {x : P8PublicClaim}
    (hs : T.label.subject = x.subject) (hf : T.label.formula = x.formula)
    (he : T.label.evaluation = x.result) : HoldsN x := by
  have := genuineNX_holdsN hR hT hreal
  rw [hs, hf, he] at this; exact this

/-! ## The edit chain (`chain_sound`) -/

/-- **`chain_sound` for the edit (C-2 step 2).**  An `s10` row `[10 [[a c] d]]` whose children are
the `new` run `(s, c)`, the `old` run `(s, d)` and a genuine chain subtree `(old, a, e)` made of
`s10L` levels ending in `s10T`, with `slot a e = new` (the `s10` read), `HoldsN` the edit:
`*[s [10 [[a c] d]]] = e`.  The chain's `ChainOK` comes from the tree induction (no depth
counter); `Noun.edit a new old = e` from E-0's `edit_of_slots` (`edit_iff_chainOK`'s ← half). -/
theorem edit_chain_sound {R : Registry} (hR : R.Faithful) {s c d new old e : Noun} {a : ℕ}
    (hN : HoldsN ⟨s, c, new⟩) (hO : HoldsN ⟨s, d, old⟩) {T : NTree RowX} (hT : GenuineNX R T)
    (hchain : T.label.state.isChain = true) (hTs : T.label.subject = old)
    (hTf : T.label.formula = .atom a) (hTe : T.label.evaluation = e)
    (hslot : Noun.slot a e = some new) :
    Noun.edit a new old = some e ∧
      HoldsN ⟨s, .cell (.atom 10) (.cell (.cell (.atom a) c) d), e⟩ := by
  have hc := genuineNX_chainOK hR hT hchain
  rw [hTs, hTf, hTe] at hc
  simp only [chainAxis] at hc
  have hed := edit_of_slots hc hslot
  refine ⟨hed, ?_⟩
  obtain ⟨n1, h1⟩ := hN
  obtain ⟨n2, h2⟩ := hO
  refine ⟨max n1 n2 + 1, ?_⟩
  simp [evalN, evalN_mono (Nat.le_max_left n1 n2) h1, evalN_mono (Nat.le_max_right n1 n2) h2, hed]

end Nock.Edit
