/-
  Nock/RedTeam/Batch2653Thm54GenX.lean

  **2652** (`Nock/Edit/GenX.lean`,
  `Nock/Edit/GenXRows.lean`, `Nock/Edit/GenXDemo.lean`).  Restates the exact statements by `example` (a change of any
  statement breaks this file), adds negative controls, and prints the axioms.

  * Generator: `genX_label`, `genX_sound`, `genX_complete`, `genX_result_eq_evalN`,
    `honest_holdsN`, `genX_inTree_holdsN`, `genX_jet_row`, `chainOK_of_edit` / `edit_iff_chainOK`.
  * Rows: `inTree_rowSem`, `consEntriesX_sound`, `consEntriesX_root`, `rowHandleNounsX_cells`,
    `demandHX_cells_iff`, `handle_cells_mem_demandHX`, `honestAxX_s10`, `mem_demandA`,
    `incRecX_spec`, `bigPairX_spec`.
  * Demos: edit at depth 3, counter `p − 1 → p → p + 1`, jetted matmul `n = 2`.
  * Negative controls: (a) a registered jet with a CRASHING clue generates nothing (the clue
    child is load-bearing, J-1's `toy_crash_rel_but_not_holdsN` at the generator); (b) a hint
    whose body is not the registered formula is NOT jetted (an `s11d` row with both children);
    (c) an edit at axis `0` generates nothing, as `evalN` crashes.
-/
import Nock.Edit.GenXDemo

set_option autoImplicit false

namespace Nock.RedTeam.Batch2653

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Jet.Autogen Nock.Edit Nock.Edit.GenX
open Nock.Edit.GenX.Demo
open Nock.NockVMROM.Thm54.VclL (closureOf Demand)

/-! ## Statements -/

example {R : Registry} (hR : R.Faithful) {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : HoldsN ⟨s, f, r⟩ := genX_sound hR h

example {R : Registry} (hR : R.Faithful) {n : ℕ} {s f r : Noun} (h : evalN n s f = some r) :
    ∃ t, genX R n s f = some (t, r) := genX_complete hR h

example {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    t.label.subject = s ∧ t.label.formula = f ∧ t.label.evaluation = r ∧
      t.label.state.isChain = false := genX_label h

example {R : Registry} (hR : R.Faithful) {fuel : ℕ} {s f r : Noun}
    (hrun : evalN fuel s f = some r) :
    ∃ t, genX R fuel s f = some (t, r) ∧
      t.label.subject = s ∧ t.label.formula = f ∧ t.label.evaluation = r ∧
      HoldsN ⟨s, f, r⟩ ∧
      ∀ u, InTree t u →
        (u.label.state.isChain = false →
          HoldsN ⟨u.label.subject, u.label.formula, u.label.evaluation⟩) ∧
        (u.label.state.isChain = true →
          ChainOK (chainAxis u.label.formula) u.label.subject u.label.evaluation) :=
  honest_holdsN hR hrun

example {R : Registry} (hR : R.Faithful) {n m : ℕ} {s f r r' : Noun} {t : NTree SkelX}
    (h : genX R n s f = some (t, r)) (hrun : evalN m s f = some r') : t.label.evaluation = r' :=
  genX_result_eq_evalN hR h hrun

example {R : Registry} {n : ℕ} {s b clue body : Noun} {t : NTree SkelX} {r r' : Noun}
    {tD : NTree SkelX} {v : Noun}
    (h : genX R (n + 1) s (.cell (.atom 11) (.cell (.cell b clue) body)) = some (t, r))
    (hcl : genX R n s clue = some (tD, v))
    (hj : jetHit R b v body s = some r') :
    t.label.state = .s11j ∧ r = r' ∧ ∃ tD v, t.children = [tD] ∧ genX R n s clue = some (tD, v) :=
  genX_jet_row h hcl hj

example {a : ℕ} {new old e : Noun} :
    Noun.edit a new old = some e ↔ ChainOK a old e ∧ Noun.slot a e = some new := edit_iff_chainOK

example {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u) :
    (rowOfSkelX u.label).SemN R := inTree_rowSem h hu

example {R : Registry} (sk : SkelX) (hs : (rowOfSkelX sk).SemN R) :
    ∀ x ∈ consEntriesX (rowOfSkelX sk), 2 ≤ x.2.1 ∧ Noun.slot x.2.1 x.1 = some x.2.2 :=
  consEntriesX_sound sk hs

example (rows : List SkelX) (c : Noun) :
    c ∈ (demandHX rows).cells ↔
      c ∈ closureOf (rows.flatMap fun sk => handleNounsX (rowOfSkelX sk)) :=
  demandHX_cells_iff rows c

example (sk : SkelX) :
    ∀ n ∈ rowHandleNounsX (rowOfSkelX sk), n.isCell = true →
      n ∈ closureOf (handleNounsX (rowOfSkelX sk)) := rowHandleNounsX_cells sk

example {R : Registry} (sk : SkelX) (hst : sk.state = .s10) (hs : (rowOfSkelX sk).SemN R) :
    1 ≤ honestAxX sk ∧
      Noun.edit (honestAxX sk) (rowOfSkelX sk).sf1 (rowOfSkelX sk).sf2 = some sk.evaluation :=
  honestAxX_s10 sk hst hs

/-! ## Negative controls -/

/-- (a) A registered jet whose clue CRASHES: the generator produces nothing (and `evalN` too). -/
def crashProg : Noun :=
  hint (.atom wildTag) (.cell (.atom 0) (.atom 0)) (compile Nock.Field.p (matmulT 2))

theorem nc_crash_clue_jetHit :
    jetHit matR (.atom wildTag) (.atom 7) (compile Nock.Field.p (matmulT 2)) toyS =
      some toyCG := by decide +kernel

theorem nc_crash_clue : genX matR 2 toyS crashProg = none := by decide +kernel

theorem nc_crash_clue_evalN : evalN 200 toyS crashProg = none := by decide +kernel

/-- (b) A hint whose body is NOT the registered formula is not jetted: `s11d`, both children. -/
def mismatchProg : Noun := wildCall 7 (.cell (.atom 1) (.atom 5))

theorem nc_mismatch :
    (runRows matR 2 toyS mismatchProg).map (fun k => k.state) = [.s11d, .s1, .s1] ∧
      (genX matR 2 toyS mismatchProg).map Prod.snd = some (.atom 5) := by decide +kernel

/-- (c) An edit at axis `0` generates nothing; `evalN` crashes. -/
def edit0F : Noun :=
  .cell (.atom 10) (.cell (.cell (.atom 0) (.cell (.atom 1) (.atom 42))) (.cell (.atom 0) (.atom 1)))

theorem nc_edit0 : genX noR 2 editS edit0F = none ∧ evalN 2 editS edit0F = none := by
  decide +kernel

/-! ## Axioms -/

#print axioms genX_sound
#print axioms genX_complete
#print axioms genX_label
#print axioms honest_holdsN
#print axioms genX_result_eq_evalN
#print axioms genX_inTree_holdsN
#print axioms genX_jet_row
#print axioms chainOK_of_edit
#print axioms edit_iff_chainOK
#print axioms inTree_rowSem
#print axioms consEntriesX_sound
#print axioms consEntriesX_root
#print axioms rowHandleNounsX_cells
#print axioms demandHX_cells_iff
#print axioms handle_cells_mem_demandHX
#print axioms walkRead_child_mem
#print axioms honestAxX_s10
#print axioms mem_demandA
#print axioms atomTable_canonical
#print axioms incRecX_spec
#print axioms bigPairX_spec
#print axioms edit_gen
#print axioms edit_states
#print axioms edit_ax
#print axioms edit_reads
#print axioms edit_holdsN
#print axioms ctr_gen
#print axioms ctr_incRecs
#print axioms ctr_demandA
#print axioms ctr_atomTable
#print axioms ctr_holdsN
#print axioms mat_gen
#print axioms mat_rows
#print axioms mat_holdsN
#print axioms mat_unjetted
#print axioms mat_row_counts
#print axioms nc_crash_clue
#print axioms nc_mismatch
#print axioms nc_edit0

end Nock.RedTeam.Batch2653
