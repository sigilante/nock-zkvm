/-
  Nock/Edit/GenXDemo.lean

  **Definition-level demos of the generator twin.**  New
  module, additive.  Each demo runs the generator (`#eval` for the listings) and checks the
  load-bearing facts by kernel `decide` (`decide +kernel`; no `native_decide`):

  1. **An edit at depth 3**: `*[[[[1 2] 3] 4] [10 [[8 [1 42]] [0 1]]]] = [[[42 2] 3] 4]`; the
     `s10` row has children `(s, [1 42], 42)`, `(s, [0 1], old)` and the chain
     `s10L(8) → s10L(4) → s10L(2) → s10T(1)`.
  2. **The counter `p − 1 → p → p + 1`** at Goldilocks `p`: `*[p−1 [4 [4 [0 1]]]] = p + 1`; both
     OP4 rows are slow (`incRecX`), the closure `demandA` is `{p, p + 1}`, and A-1's carry chain
     carries both records.
  3. **A jetted matmul `n = 2`** through a `toyR`-style registry entry made by J-2's `compile`:
     the hinted call is ONE `s11j` row with ONE child (the clue `[1 0]`); the result is
     `(matmulT 2).sem` at Goldilocks; the same program without the registry generates a large tree.
-/
import Nock.Edit.GenXRows
import Nock.Jet.AutogenMatmul

set_option autoImplicit false

namespace Nock.Edit.GenX.Demo

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Jet.Autogen Nock.Edit Nock.Edit.GenX

/-- The empty registry (every hint is dynamic). -/
def noR : Registry := fun _ => none

theorem noR_faithful : noR.Faithful := by intro n j h; simp [noR] at h

/-- The rows of a tree, depth-first pre-order (a permutation of the BFS rows, `bfsForest_perm_dfsForest`). -/
def rowsX (t : NTree SkelX) : List SkelX := (dfsTree t).map NTree.label

/-- The generated rows of a run (empty on failure). -/
def runRows (R : Registry) (fuel : ℕ) (s f : Noun) : List SkelX :=
  ((genX R fuel s f).map fun p => rowsX p.1).getD []

/-! ## 1. An edit at depth 3 -/

def editS : Noun := .cell (.cell (.cell (.atom 1) (.atom 2)) (.atom 3)) (.atom 4)
def editF : Noun :=
  .cell (.atom 10) (.cell (.cell (.atom 8) (.cell (.atom 1) (.atom 42))) (.cell (.atom 0) (.atom 1)))
def editR : Noun := .cell (.cell (.cell (.atom 42) (.atom 2)) (.atom 3)) (.atom 4)

/-- The generated result is the edit. -/
theorem edit_gen : (genX noR 2 editS editF).map Prod.snd = some editR := by decide +kernel

/-- `evalN` agrees at the same fuel. -/
theorem edit_evalN : evalN 2 editS editF = some editR := by decide +kernel

/-- The rows, pre-order: `s10`, its two calls `s1`/`s0`, then the chain `s10L` at `8, 4, 2`
and `s10T` at `1` (subject `old`, evaluation `e`). -/
theorem edit_states :
    (runRows noR 2 editS editF).map (fun k => (k.state, k.formula)) =
      [(.s10, editF), (.s1, .cell (.atom 1) (.atom 42)), (.s0, .cell (.atom 0) (.atom 1)),
       (.s10L, .atom 8), (.s10L, .atom 4), (.s10L, .atom 2), (.s10T, .atom 1)] := by
  decide +kernel

/-- Every row is `SemN` (the generic theorem applied) and the chain levels' axis column is
`a_k / 2`; the edit row's axis column is `8`. -/
theorem edit_ax : (runRows noR 2 editS editF).map honestAxX = [8, 0, 1, 4, 2, 1, 0] := by
  decide +kernel

/-- The walk reads: the `s10` read `slot 8 e = 42`, then the three sibling pairs (axes `9, 5, 3`). -/
theorem edit_reads :
    walkReadsHX (runRows noR 2 editS editF) =
      [(editR, 8), (editS, 9), (editR, 9), (editS, 5), (editR, 5), (editS, 3), (editR, 3)] := by
  decide +kernel

theorem edit_holdsN : HoldsN ⟨editS, editF, editR⟩ := by
  obtain ⟨t, ht⟩ := genX_complete noR_faithful edit_evalN
  exact genX_sound noR_faithful ht

#eval (runRows noR 2 editS editF).map fun k => (k.state, k.formula, k.evaluation)

/-! ## 2. The counter `p − 1 → p → p + 1` -/

def P : ℕ := Nock.Atoms.p

def ctrF : Noun := .cell (.atom 4) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))

theorem ctr_gen : (genX noR 3 (.atom (P - 1)) ctrF).map Prod.snd = some (.atom (P + 1)) := by
  decide +kernel

theorem ctr_evalN : evalN 3 (.atom (P - 1)) ctrF = some (.atom (P + 1)) := by decide +kernel

/-- Both OP4 rows are slow and their records are `(p, p + 1)` (outer) and `(p − 1, p)` (inner). -/
theorem ctr_incRecs :
    (runRows noR 3 (.atom (P - 1)) ctrF).map (fun k => incRecX (rowOfSkelX k)) =
      [some (P, P + 1), some (P - 1, P), none] := by
  decide +kernel

/-- The atom digitisation closure is exactly `{p + 1, p}`. -/
theorem ctr_demandA : demandA (runRows noR 3 (.atom (P - 1)) ctrF) = [P + 1, P] := by
  decide +kernel

/-- The two inc records ride A-1's carry chains (the generic theorem `inc_carry`). -/
example : Nock.Atoms.Carry 1 (Nock.Atoms.limbs (P - 1)) (Nock.Atoms.limbs P) := by
  have := inc_carry (P - 1)
  rwa [show P - 1 + 1 = P by unfold P; norm_num [Nock.Field.p]] at this

example : Nock.Atoms.Carry 1 (Nock.Atoms.limbs P) (Nock.Atoms.limbs (P + 1)) := inc_carry P

theorem ctr_holdsN : HoldsN ⟨.atom (P - 1), ctrF, .atom (P + 1)⟩ := ⟨3, ctr_evalN⟩

/-- The atom table: the limbs of `p + 1` and `p` (`limbs p = [1, B − 1]`, A-1's `limbs_p`). -/
theorem ctr_atomTable :
    atomTable (runRows noR 3 (.atom (P - 1)) ctrF) = [[2, 4294967295], [1, 4294967295]] := by
  decide +kernel

/-! ## 3. A jetted matmul `n = 2` -/

/-- The compiled matmul entry at Goldilocks (J-2's `compile`). -/
def matJet : JetSpec := ⟨(matmulT 2).toTemplate Nock.Field.p, compile Nock.Field.p (matmulT 2)⟩

/-- The one-entry registry: id `7` ↦ the compiled matmul (`toyR`-style). -/
def matR : Registry := fun n => if n = 7 then some matJet else none

theorem matR_faithful : matR.Faithful := by
  intro n j h
  unfold matR at h
  split_ifs at h
  cases h
  exact matmul_jetSpec_faithful (by unfold Nock.Field.p; norm_num) 2

/-- The hinted program `[11 [%wild [1 7]] c_T]`: tag `%wild`, the jet key `7` in the clue. -/
def matProg : Noun := wildCall 7 (compile Nock.Field.p (matmulT 2))

/-- The OLD wire form `[11 [7 [1 0]] c_T]`, where the tag itself was the jet id. -/
def matProgTagged : Noun := jetCall 7 (.cell (.atom 1) (.atom 0)) (compile Nock.Field.p (matmulT 2))

/-- **The jetted run**: one `s11j` row with one `s1` child (the clue); the result is the product
`[[5 8] [15 22]]` computed by the template's semantics. -/
theorem mat_gen : (genX matR 2 toyS matProg).map Prod.snd = some toyCG := by decide +kernel

theorem mat_rows :
    (runRows matR 2 toyS matProg).map (fun k => k.state) = [.s11j, .s1] := by decide +kernel

/-- `HoldsN` of the hinted call, from the generator and the faithful registry. -/
theorem mat_holdsN : HoldsN ⟨toyS, matProg, toyCG⟩ := by
  obtain ⟨t, ht⟩ : ∃ t, genX matR 2 toyS matProg = some (t, toyCG) := by
    cases h : genX matR 2 toyS matProg with
    | none => have := mat_gen; rw [h] at this; cases this
    | some p =>
      have := mat_gen; rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨p.1, by rw [← this]⟩
  exact genX_sound matR_faithful ht

/-- Without the registry the same program is evaluated in full: many rows (`#eval` below). -/
theorem mat_unjetted : (genX noR 200 toyS matProg).map Prod.snd = some toyCG := by decide +kernel

/-- Row counts: 2 jetted, 2999 unjetted. -/
theorem mat_row_counts :
    (runRows matR 2 toyS matProg).length = 2 ∧ (runRows noR 200 toyS matProg).length = 2999 := by
  decide +kernel

/-- **A tag is a hint kind, not a jet id**: the old form, tag `7`, is no longer a jet.  It is an
ordinary dynamic hint (`s11d`), evaluated in full to the same value. -/
theorem mat_tagged_not_jet :
    ((runRows matR 200 toyS matProgTagged).map (fun k => k.state)).head? = some .s11d ∧
      (genX matR 200 toyS matProgTagged).map Prod.snd = some toyCG := by
  decide +kernel

end Nock.Edit.GenX.Demo
