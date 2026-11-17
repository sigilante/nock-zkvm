/-
  Nock/RedTeam/Batch4773Thm54NVJetC.lean  
  The cell chip `checkCellKW (tabC Ijet) = true`, SPLIT: `checkCellKW = checkM` is a conjunction over the 123 rows
  (each row: every source gate) and the fixed columns; the monolithic `decide +kernel` is OOM-killed at 20 GB, so each
  chunk of rows is its own `decide +kernel` declaration.
-/
import Nock.RedTeam.Batch4771Thm54NVJetData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nock.RedTeam.Batch4773

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.RedTeam.Batch4771 Nock.V1J8.MemX
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellTemplateHQKW)


/-- Row `j` of the cell table passes every source gate (`true` off the table). -/
def rowAt (j : ℕ) : Bool :=
  if h : j < Ijet.C.n then (srcM (cellTemplateHQKW deltaF)).all (srcOK (cellTemplateHQKW deltaF).baseCols ((tabC Ijet).env (cellTemplateHQKW deltaF) ⟨j, h⟩)) else true

theorem checkM_of_rows {n : ℕ} (T : TabM n) (Tm : Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate (ZMod Nock.Field.p))
    (hrow : ∀ j : Fin n, (srcM Tm).all (srcOK Tm.baseCols (T.env Tm j)) = true)
    (hprep : T.prep.all (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i)) = true) :
    checkM Tm T = true := by
  unfold checkM
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr fun i _ => hrow i, hprep⟩

theorem ijet_C_prep : (tabC Ijet).prep.all (fun q => (List.finRange Ijet.C.n).all fun i =>
    decide ((tabC Ijet).cols q.1 i = q.2 i)) = true := by decide +kernel

theorem ijet_C_r0 : ∀ j ∈ List.range' 0 16, rowAt j = true := by decide +kernel

theorem ijet_C_r1 : ∀ j ∈ List.range' 16 16, rowAt j = true := by decide +kernel

theorem ijet_C_r2 : ∀ j ∈ List.range' 32 16, rowAt j = true := by decide +kernel

theorem ijet_C_r3 : ∀ j ∈ List.range' 48 16, rowAt j = true := by decide +kernel

theorem ijet_C_r4 : ∀ j ∈ List.range' 64 16, rowAt j = true := by decide +kernel

theorem ijet_C_r5 : ∀ j ∈ List.range' 80 16, rowAt j = true := by decide +kernel

theorem ijet_C_r6 : ∀ j ∈ List.range' 96 16, rowAt j = true := by decide +kernel

theorem ijet_C_r7 : ∀ j ∈ List.range' 112 16, rowAt j = true := by decide +kernel

theorem ijet_Cn : Ijet.C.n = 123 := by decide +kernel

/-- **The cell chip accepts `Ijet`**, from the row chunks and the fixed-column check. -/
theorem ijet_C : checkCellKW (tabC Ijet) = true := by
  unfold checkCellKW
  refine checkM_of_rows _ _ (fun j => ?_) ijet_C_prep
  have hj := j.isLt
  have hn := ijet_Cn
  have key : rowAt j.val = true := by
    by_cases h0 : j.val < 16
    · exact ijet_C_r0 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h1 : j.val < 32
    · exact ijet_C_r1 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h2 : j.val < 48
    · exact ijet_C_r2 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h3 : j.val < 64
    · exact ijet_C_r3 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h4 : j.val < 80
    · exact ijet_C_r4 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h5 : j.val < 96
    · exact ijet_C_r5 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h6 : j.val < 112
    · exact ijet_C_r6 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h7 : j.val < 128
    · exact ijet_C_r7 j.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    exfalso; omega
  simpa [rowAt, j.isLt] using key

end Nock.RedTeam.Batch4773

#print axioms Nock.RedTeam.Batch4773.ijet_C
