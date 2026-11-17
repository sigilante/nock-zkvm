/-
  Nock/V1J8/GenJetMat.lean

  **Kernel facts about `genJ8J`.**

  * `genJ8J_spec` (every run): an output's layout IS `layoutJ8 Rt regs ids` (`List.ofFn I.lay`), with `I.Rt = Rt`,
    `I.regs = regs`, `I.ids` = the run's call ids (`callsOf`), and `I.g = |regs|`.
  * `genJ8J_regOK`: the registry premise `RegOK I (regOf Rt regs)` of `checkJ8_iff` holds for every output, given only
    `WellTyped` of the registered templates (the registry is built from the templates).
  * **The jetted matmul `n = 2`** (`[11 [%wild [1 7]] c_T]` on `toyS`, registry `[7 ↦ matmulT 2]`, fuel `2`):
    `mat_some` — the generator returns an input at EVERY coin vector (its guard is coin-free; small kernel `decide`s
    over the two-row run and the call's honest values), `mat_ids` — the one call is id `7`; and
    **`mat_static_cheap`**: at every coin vector the output's registry conjuncts of the static block hold —
    `hlay` (by `genJ8J_spec`, no computation), `hsmall`, `huniq`, `haxT`, `hnd` (kernel `decide` over the 237-row
    layout `layoutJ8 (fun _ => matmulT 2) [7] [7]`, as HJ's `demo2_layout` / `demo2_small` / `demo2_uniq`), and the
    budget-side `|regs| ≤ g`.
-/
import Nock.V1J8.GenJet
import Nock.Jet.AutogenMatmul
import Nock.Edit.GenXDemo

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.GenJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX
open Nock.Jet.Autogen (Tpl compile matmulT toyS)
open Nock.Jet.ChipJ8 (PRow layoutJ8 tvKey axPosB)

/-- **The registry publics of every output.** -/
theorem genJ8J_spec (Rt : ℕ → Tpl) (regs : List ℕ) (fuel : ℕ) (s f : Noun) (χe : CoinsE) (I : InJ8)
    (h : genJ8J Rt regs fuel s f χe = some I) :
    ∃ Rn, runX (regOf Rt regs) fuel s f = some Rn ∧ List.ofFn I.lay = layoutJ8 I.Rt I.regs I.ids ∧ I.Rt = Rt ∧
      I.regs = regs ∧ I.ids = (callsOf Rn.rows).map Prod.fst ∧ I.g = regs.length := by
  unfold genJ8J at h
  split at h
  · exact absurd h (by simp)
  · rename_i Rn hR
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · cases h
      exact ⟨Rn, hR, List.ofFn_get _, rfl, rfl, rfl, rfl⟩

/-- **The registry premise holds for every output** (`regOf` is built from the templates). -/
theorem genJ8J_regOK (Rt : ℕ → Tpl) (regs : List ℕ) (fuel : ℕ) (s f : Noun) (χe : CoinsE) (I : InJ8)
    (h : genJ8J Rt regs fuel s f χe = some I) (hwt : ∀ i ∈ regs, (Rt i).WellTyped Nock.Field.p) :
    RegOK I (regOf Rt regs) := by
  obtain ⟨Rn, -, -, hRt, hregs, -, -⟩ := genJ8J_spec Rt regs fuel s f χe I h
  intro i hi
  rw [hregs] at hi
  rw [hRt]
  exact ⟨by simp [regOf, hi], hwt i hi⟩

/-! ## A structural BFS (the kernel cannot unfold `bfsForest`'s well-founded recursion) -/

/-- `bfsForest` with a size budget (structural on the budget). -/
def bfsF {LT : Type} : ℕ → List (Nock.Walk.NTree LT) → List (Nock.Walk.NTree LT)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, t :: rest => (t :: rest) ++ bfsF k ((t :: rest).flatMap Nock.Walk.NTree.children)

/-- The BFS level after `k` steps. -/
def lvl {LT : Type} : ℕ → List (Nock.Walk.NTree LT) → List (Nock.Walk.NTree LT)
  | 0, l => l
  | k + 1, l => lvl k (l.flatMap Nock.Walk.NTree.children)

theorem bfsF_eq {LT : Type} : ∀ (k : ℕ) (l : List (Nock.Walk.NTree LT)), lvl k l = [] →
    bfsF k l = Nock.Walk.bfsForest l := by
  intro k
  induction k with
  | zero =>
    intro l h
    simp only [lvl] at h
    subst h
    simp [bfsF, Nock.Walk.bfsForest_nil]
  | succ m ih =>
    intro l h
    cases l with
    | nil => simp [bfsF, Nock.Walk.bfsForest_nil]
    | cons t rest =>
      simp only [lvl] at h
      rw [Nock.Walk.bfsForest_cons_eq _ (List.cons_ne_nil _ _), bfsF, ih _ h]

/-- The BFS with a budget of `64` levels (the well-founded `bfsForest` past it). -/
def bfs64 {LT : Type} (l : List (Nock.Walk.NTree LT)) : List (Nock.Walk.NTree LT) :=
  if lvl 64 l = [] then bfsF 64 l else Nock.Walk.bfsForest l

theorem bfs64_eq {LT : Type} (l : List (Nock.Walk.NTree LT)) : bfs64 l = Nock.Walk.bfsForest l := by
  unfold bfs64
  split
  · exact bfsF_eq _ _ ‹_›
  · rfl

/-- `runX` with the budgeted BFS. -/
def runXF (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) : Option RunX :=
  match genX R fuel s f with
  | some (t, r) =>
    let W := bfs64 [t]
    some ⟨t, r, W, (W.map fun u => rowOfSkelX u.label).toArray⟩
  | none => none

theorem runXF_eq (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) : runXF R fuel s f = runX R fuel s f := by
  unfold runXF runX
  rcases genX R fuel s f with _ | ⟨t, r⟩
  · rfl
  · simp only [bfs64_eq]

/-! ## The jetted matmul `n = 2` -/

/-- The template table of the demo: id `7` ↦ `matmulT 2`. -/
def matRt : ℕ → Tpl := fun _ => matmulT 2

/-- The generator's coin-free guard. -/
def guardB (Rt : ℕ → Tpl) (regs : List ℕ) (fuel : ℕ) (s f : Noun) : Bool :=
  match runXF (regOf Rt regs) fuel s f with
  | none => false
  | some Rn => smallAtoms Rn.rows && smallNouns (jNouns Rt regs (callsOf Rn.rows))

theorem genJ8J_isSome (Rt : ℕ → Tpl) (regs : List ℕ) (fuel : ℕ) (s f : Noun) (χe : CoinsE)
    (hg : guardB Rt regs fuel s f = true) : ∃ I, genJ8J Rt regs fuel s f χe = some I := by
  unfold guardB at hg
  rw [runXF_eq] at hg
  unfold genJ8J
  split at hg
  · exact absurd hg (by simp)
  · rename_i Rn hR
    rw [hR]
    dsimp only
    rw [if_neg (by simp [hg])]
    exact ⟨_, rfl⟩

theorem mat_guard : guardB matRt [7] 2 toyS Demo.matProg = true := by decide +kernel

theorem mat_ids_runF :
    (runXF (regOf matRt [7]) 2 toyS Demo.matProg).map (fun Rn => (callsOf Rn.rows).map Prod.fst) = some [7] := by
  decide +kernel

theorem mat_ids_run :
    (runX (regOf matRt [7]) 2 toyS Demo.matProg).map (fun Rn => (callsOf Rn.rows).map Prod.fst) = some [7] := by
  rw [← runXF_eq]; exact mat_ids_runF

/-- **The generator returns an input on `mat` at every coin vector.** -/
theorem mat_some (χe : CoinsE) : ∃ I, genJ8J matRt [7] 2 toyS Demo.matProg χe = some I :=
  genJ8J_isSome _ _ _ _ _ χe mat_guard

theorem mat_layout_small : ∀ q ∈ layoutJ8 matRt [7] [7],
    q.id < Nock.Field.p ∧ q.cid < Nock.Field.p ∧ q.nid < Nock.Field.p ∧ q.n1 < Nock.Field.p ∧ q.n2 < Nock.Field.p := by
  decide +kernel

theorem mat_layout_uniq : ((layoutJ8 matRt [7] [7]).filterMap tvKey).Nodup := by decide +kernel

theorem mat_axPos : ∀ i ∈ [7], axPosB (matRt i) = true := by decide +kernel

theorem mat_layout_length : (layoutJ8 matRt [7] [7]).length = 237 := by decide +kernel

/-- **`genJ8J` on `mat` produces an input whose static registry conjuncts pass** (every coin vector): `hlay`,
`hsmall`, `huniq`, `haxT`, `hnd` of `StaticJ8` at the input's publics, the J chip has `237` rows, and `|regs| ≤ g`. -/
theorem mat_static_cheap (χe : CoinsE) :
    ∃ I, genJ8J matRt [7] 2 toyS Demo.matProg χe = some I ∧
      List.ofFn I.lay = layoutJ8 I.Rt I.regs I.ids ∧
      (∀ q ∈ layoutJ8 I.Rt I.regs I.ids,
        q.id < Nock.Field.p ∧ q.cid < Nock.Field.p ∧ q.nid < Nock.Field.p ∧ q.n1 < Nock.Field.p ∧
          q.n2 < Nock.Field.p) ∧
      ((layoutJ8 I.Rt I.regs I.ids).filterMap tvKey).Nodup ∧
      (∀ i ∈ I.regs, axPosB (I.Rt i) = true) ∧ I.regs.Nodup ∧ I.J.n = 237 ∧ I.regs.length ≤ I.g := by
  obtain ⟨I, hI⟩ := mat_some χe
  obtain ⟨Rn, hR, hlay, hRt, hregs, hids, hg⟩ := genJ8J_spec _ _ _ _ _ χe I hI
  have hids' : I.ids = [7] := by
    rw [hids]
    have := mat_ids_run
    rw [hR] at this
    simpa using this
  have hn : I.J.n = (List.ofFn I.lay).length := by simp
  refine ⟨I, hI, hlay, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRt, hregs, hids']; exact mat_layout_small
  · rw [hRt, hregs, hids']; exact mat_layout_uniq
  · rw [hRt, hregs]; exact mat_axPos
  · rw [hregs]; decide
  · rw [hn, hlay, hRt, hregs, hids']; exact mat_layout_length
  · rw [hregs, hg]

end Nock.V1J8.GenJ

#print axioms Nock.V1J8.GenJ.genJ8J_spec
#print axioms Nock.V1J8.GenJ.genJ8J_regOK
#print axioms Nock.V1J8.GenJ.mat_some
#print axioms Nock.V1J8.GenJ.mat_static_cheap
