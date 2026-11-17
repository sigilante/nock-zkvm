/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalV.lean

  **J-9 AL completeness, part 2: the validity balance `hsumC_L`.**
  * §1 **Discharged from §0's binders (`hnd`, `hprim`) alone**: every called primitive's formula noun
    `primC op` is a cell of the table (`primC_mem_cells`), so the verifier's prim pin `claimVec (encJ8 (primC op))
    (vcRun id) (rkPOf id)` is the cell table's validity provider of row `vcRun id` (`pinP_eq_cG`).  Route: the
    `s11j` row's formula `[11 [[b clue] body]]` is a handle noun (a cell of the table), the jet hit pins
    `body = j.c = primC op` (`jetHit_spec`, `hprim`), and the table is child-closed (`cells_closed`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalV

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalX
open Nock.Jet.Prim (PrimOp primC primSpec)

noncomputable section

/-! ## 1. Design risk 4: `primC op ∈ cells` -/

section PrimCells
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

theorem primC_cell (op : PrimOp) : ∃ a c, primC op = .cell a c := by
  cases op <;> exact ⟨_, _, rfl⟩

theorem rowOfSkelX_f (sk : SkelX) : (rowOfSkelX sk).f = sk.formula := by
  unfold rowOfSkelX
  cases sk.state <;> rfl

/-- **Every called primitive's formula noun is a cell of the table** (binders `hnd`, `hprim`). -/
theorem primC_mem_cells (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ psRun (p := p) Rt hgen prims, primC q.2 ∈ (DA).cells := by
  intro q hq
  have hq' : q ∈ prims ∧ q.1 ∈ (DA).calls.map Prod.fst := by
    simpa [psRun, ComplJ9ALData.primsC] using hq
  obtain ⟨hqp, hqc⟩ := hq'
  obtain ⟨cl, hcl, hcl1⟩ := List.mem_map.mp hqc
  have hcl0 : cl ∈ Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) := hcl
  unfold Nock.V1J8.Gen.callsOf at hcl0
  obtain ⟨row, hrow, hrc⟩ := List.mem_filterMap.1 hcl0
  have hrow' : ∃ u ∈ bfsForest [t], rowOfSkelX u.label = row := by
    simpa [ComplJ8Data.rowsOfT] using hrow
  obtain ⟨u, hu, rfl⟩ := hrow'
  obtain ⟨c, hc, huc⟩ := (mem_bfsForest [t] u).1 hu
  have hct : c = t := by simpa using hc
  subst c
  have hst : u.label.state = .s11j := by
    rw [← ComplJ8Jet.rowOfSkelX_st]
    by_contra hne
    simp [hne] at hrc
  have hcl' : cl = (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).sf1, (rowOfSkelX u.label).s) := by
    rw [if_pos (by rw [ComplJ8Jet.rowOfSkelX_st]; exact hst)] at hrc
    exact (Option.some.inj hrc).symm
  rcases genX_inTree hgen huc with ⟨m, hm⟩ | hch
  · obtain ⟨bb, clue, body, v, r', hf, hj⟩ := ComplJ8Jet.genX_s11j hm hst
    obtain ⟨id0, j0, rfl, rfl, -, -, -⟩ := jetHit_spec hj
    -- the id read off the row (its clue value `sf1`) is `q.1`
    have hs := inTree_rowSem hgen huc
    unfold RowNX.SemN at hs
    rw [ComplJ8Jet.rowOfSkelX_st, hst] at hs
    obtain ⟨-, -, -, -, id, j, -, hftth, hRj, hjc, -⟩ := hs
    have hftt : (rowOfSkelX u.label).ftt = body := by
      unfold rowOfSkelX
      rw [hst]
      simp only [hf, tlN, hdN]
    rw [hftt] at hjc
    have hid : id = q.1 := by
      rw [← hcl1, hcl', hftth]; rfl
    subst hid
    rw [hprim q hqp] at hRj
    have hbody : body = primC q.2 := by
      rw [← hjc, ← Option.some.inj hRj]; rfl
    -- the formula is a cell of the table, and the table is child-closed
    have hfm : u.label.formula ∈ (DD).cells := by
      rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen (row := rowOfSkelX u.label) hrow
          (n := (rowOfSkelX u.label).f) (by simp [handleNounsX]) with ⟨-, hm'⟩ | ⟨v, hv, -⟩ | ⟨v, hv, -⟩
      · rwa [rowOfSkelX_f] at hm'
      · rw [rowOfSkelX_f, hf] at hv; cases hv
      · rw [rowOfSkelX_f, hf] at hv; cases hv
    have hcl : ComplJ8Data.ClP (DD).cells [] := ComplJ8Data.cells_closed _
    rw [hf] at hfm
    have h1 := (hcl _ _ hfm (by simp)).2 _ _ rfl
    have h2 := (hcl _ _ h1 (by simp)).2
    obtain ⟨a, c', hac⟩ := primC_cell q.2
    rw [hbody, hac] at h2
    have := h2 a c' rfl
    rw [← hac] at this
    exact this
  · have := chainNode_isChain hch
    rw [hst] at this
    exact absurd this (by decide)

/-- **The verifier's prim pin record is the cell table's validity provider of row `vcRun id`.** -/
theorem idxP_getD (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ psRun (p := p) Rt hgen prims,
      (DA).cells.getD (vcRun (p := p) Rt hgen prims q.1) (.atom 0) = primC q.2 ∧
      vcRun (p := p) Rt hgen prims q.1 < (DA).cells.length := by
  intro q hq
  have hm := primC_mem_cells Rt hgen prims hnd hprim q hq
  have hqp : q ∈ prims := (List.mem_filter.mp hq).1
  have hop : ComplJ9ALData.opOf prims q.1 = q.2 := ComplJ9ALData.opOf_of_mem hnd hqp
  have e : vcRun (p := p) Rt hgen prims q.1 = (DA).cells.idxOf (primC q.2) := by
    show Nock.V1J8.Gen.idxOf (DA).cells (primC (ComplJ9ALData.opOf prims q.1)) = _
    rw [hop, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  rw [e]
  exact ⟨ComplJ8OfBal.getD_idxOf _ _ hm, List.idxOf_lt_length_of_mem hm⟩

end PrimCells

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalV
