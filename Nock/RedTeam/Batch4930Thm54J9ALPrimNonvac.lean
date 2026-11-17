/-
  Nock/RedTeam/Batch4930Thm54J9ALPrimNonvac.lean

  **With-prims non-vacuity of `AcceptsJ9AL`.**  An accepting instance with the ALU on and the primitive
  `add` actually called (`prims = [(idAdd, add)]`), read off `complJ9AL_toy`.
-/
import Nock.RedTeam.Batch4921Thm54J9ALComplToy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4930

open Nock Nock.Jet Nock.Jet.Prim
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4921 (BL Rt0T)

theorem BL_aluOn : BL.Pb.aluOn = true := rfl

theorem BL_prims : BL.Pb.prims = [(idAdd, PrimOp.add)] := by
  show Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.psRun (p := pP) (RtP Rt0T) genT [(idAdd, .add)] = _
  have hc : (DAT Rt0T).calls = [(idAdd, sT)] := callsT Rt0T
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.psRun
  rw [hc]
  decide

open Classical in
/-- **`acceptsJ9AL_withPrims`: the J-9 AL acceptance predicate is satisfiable with the ALU on and a primitive called.**
At the claim `*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12` there are a coin and a message at which
`AcceptsJ9AL` accepts, with the ALU on (`aluOn = true`) and the primitive list exactly `[(id_add, add)]` (so
non-empty); and the claim holds (`HoldsN`). -/
theorem acceptsJ9AL_withPrims :
    ∃ χ M, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ M (BL.tr χ) BL.rows BL.g ∧
      BL.Pb.aluOn = true ∧ BL.Pb.prims = [(idAdd, PrimOp.add)] ∧ BL.Pb.prims ≠ [] ∧
      Nock.Jet.HoldsN (ComplJ8.cJ sT fT rT) := by
  have h := Nock.RedTeam.Batch4921.complJ9AL_toy
  obtain ⟨χ, hχ⟩ := Nock.RedTeam.Batch4921.complJ9AL_toy_figure.2
  refine ⟨χ, BL.M χ, hχ, BL_aluOn, BL_prims, by rw [BL_prims]; simp, h.2.2.2.1⟩

end Nock.RedTeam.Batch4930

#print axioms Nock.RedTeam.Batch4930.acceptsJ9AL_withPrims
