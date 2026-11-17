import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet
import Nock.Jet.VerifiedRegistry
import Nock.V1J8.Example

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
open Nock Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.Jet Nock.Jet.Autogen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

/-- A registry all of whose entries are compiled from `Rt`, with the chip's public template checks. -/
def CompiledBy (p : ℕ) (Rg : VerifiedRegistry) (Rt : ℕ → Tpl) : Prop :=
  ∀ id j, Rg.R id = some j →
    j = ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧
      (Rt id).WellTyped p ∧ ∀ i, (Rt id).ax i < p

/-- Every id the run calls is registered. -/
theorem called_some {R : Registry} {n : ℕ} {s f r : Noun} {t : NTree SkelX}
    (h : genX R n s f = some (t, r)) {id : ℕ} (hid : id ∈ CalledIds t) : ∃ j, R id = some j := by
  obtain ⟨u, hin, hst, hft⟩ := hid
  have hs := inTree_rowSem h hin
  unfold RowNX.SemN at hs
  rw [hst] at hs
  obtain ⟨-, -, -, -, id', j, -, hft', hR, -, -⟩ := hs
  rw [hft] at hft'
  cases hft'
  exact ⟨j, hR⟩

theorem hRt_hregAx_of {p : ℕ} {Rg : VerifiedRegistry} {Rt : ℕ → Tpl} (hC : CompiledBy p Rg Rt)
    {n : ℕ} {s f r : Noun} {t : NTree SkelX} (h : genX Rg.R n s f = some (t, r)) :
    (∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) ∧
    (∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p) := by
  refine ⟨fun id hid => ?_, fun id hid => ?_⟩
  · obtain ⟨j, hj⟩ := called_some h hid
    obtain ⟨rfl, ha, hw, -⟩ := hC id j hj
    exact ⟨hj, ha, hw⟩
  · obtain ⟨j, hj⟩ := called_some h hid
    exact (hC id j hj).2.2.2

/-- A checked registry: templates, ids, and the per-template proofs as fields. -/
structure CheckedReg (p : ℕ) where
  hp : 0 < p
  Rt : ℕ → Tpl
  regs : List ℕ
  wt : ∀ n ∈ regs, (Rt n).WellTyped p
  axPos : ∀ n ∈ regs, Nock.Jet.ChipJ8.axPosB (Rt n) = true
  axLt : ∀ n ∈ regs, ∀ i, (Rt n).ax i < p

def CheckedReg.toVR {p : ℕ} (C : CheckedReg p) : VerifiedRegistry :=
  VerifiedRegistry.ofCompiled p C.hp C.Rt C.regs C.wt

theorem CheckedReg.compiledBy {p : ℕ} (C : CheckedReg p) : CompiledBy p C.toVR C.Rt := by
  intro id j h
  simp only [CheckedReg.toVR, VerifiedRegistry.ofCompiled] at h
  by_cases hn : id ∈ C.regs
  · rw [if_pos hn, Option.some.injEq] at h
    exact ⟨h.symm, C.axPos id hn, C.wt id hn, C.axLt id hn⟩
  · rw [if_neg hn] at h; cases h

theorem compiledBy_empty (p : ℕ) (Rt : ℕ → Tpl) : CompiledBy p VerifiedRegistry.empty Rt := by
  intro id j h; cases h

/-- The checked registry for the example `RtG` (all templates are the constant-0 template). -/
def rtGReg {p : ℕ} (hp : 0 < p) (regs : List ℕ) : CheckedReg p :=
  ⟨hp, Nock.V1J8.Example.RtG, regs, fun _ _ => Nock.Jet.Autogen.HasTy.const hp, fun _ _ => rfl,
    fun _ _ i => i.elim0⟩

theorem rtGReg_compiledBy {p : ℕ} (hp : 0 < p) (regs : List ℕ) :
    CompiledBy p (rtGReg hp regs).toVR Nock.V1J8.Example.RtG := (rtGReg hp regs).compiledBy

end Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry

open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry in
#print axioms called_some
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry in
#print axioms hRt_hregAx_of
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry in
#print axioms CheckedReg.compiledBy
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry in
#print axioms compiledBy_empty
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry in
#print axioms rtGReg_compiledBy
