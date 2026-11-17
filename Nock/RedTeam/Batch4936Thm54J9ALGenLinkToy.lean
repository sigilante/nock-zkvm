/-
  Nock/RedTeam/Batch4936Thm54J9ALGenLinkToy.lean

  **Honest link for J-9 AL: a hypothesis-free instance of `checkJ9ALX_genJ9ALXJ`.**  The toy run of Batch4921
  (`*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12` over `addPrims empty [(id_add, add)]`, one call of the
  primitive `add` on two big atoms, so the ALU chip is on): at a good coin, the generator `genJ9ALXJ` produces a
  record, and the wired checker `checkJ9ALX` accepts it.  Every binder of `checkJ9ALX_genJ9ALXJ` is a closed lemma:
  Batch4921's / toy facts, `CompiledByP` of the toy registry (its only entry is the primitive), and a good
  coin from the toy's figure (`exists_good_coinEJL`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ
import Nock.RedTeam.Batch4921Thm54J9ALComplToy

set_option autoImplicit false

namespace Nock.RedTeam.Batch4936

open Nock Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Prim Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.V1J8.Exe (CoinsE)
open Nock.RedTeam.Batch4842 (card_KC)
open Nock.RedTeam.Batch4921 (Rt0T BL aluLen_toy complJ9AL_toy)

/-- The toy's primitive table. -/
abbrev primsT : List (ℕ × PrimOp) := [(idAdd, PrimOp.add)]

/-- **`CompiledByP` of the toy registry**: its only entry is the primitive `id_add`, so the template clause is
vacuous. -/
theorem hCT : CheckedRegistryP.CompiledByP pP RgT Rt0T primsT := by
  refine ⟨fun id j hj hn => ?_, hprimT⟩
  have hj' : (CheckedRegistryP.addPrims VerifiedRegistry.empty primsT).R id = some j := hj
  rw [CheckedRegistryP.addPrims_R_of_not_mem VerifiedRegistry.empty primsT id hn] at hj'
  cases hj'

/-- The generator's output on the toy run. -/
theorem genT_L (χe : CoinsE) :
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ RgT.R (rtP Rt0T primsT) primsT 2 sT fT χe =
      some (GenPortJ9ALHJRun.recJ9ALXJ (rtP Rt0T primsT) primsT sT fT χe tT rT) := by
  rw [GenPortJ9ALHJRun.genJ9ALXJ_eq]
  have hr : Nock.V1J8.Gen.runX RgT.R 2 sT fT =
      some ⟨tT, rT, bfsForest [tT], ComplJ8Data.rowsOfT tT⟩ := by
    unfold Nock.V1J8.Gen.runX; rw [genT]; rfl
  rw [hr]
  rfl

/-- **`genLink_toy`: the input generator and the executable checker agree on a concrete ALU run, with no hypothesis.**
For the run of one `add` primitive call on two big atoms (`*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12`,
ALU chip on), there is a coin vector `χe` at which `genJ9ALXJ` produces an input `I`, and `checkJ9ALX I = true`. -/
theorem genLink_toy : ∃ χe : CoinsE, ∃ I : Nock.V1J9AL.CheckJ9AL.InJ9AL,
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ RgT.R (rtP Rt0T primsT) primsT 2 sT fT χe = some I ∧
      Nock.V1J9AL.CheckJ9AL.checkJ9ALX I = true := by
  obtain ⟨-, hfrac, -, -, hfig⟩ := complJ9AL_toy
  obtain ⟨hlt, -⟩ := hfig card_KC
  obtain ⟨χe, hχ⟩ := GenPortJ9ALHGoodCoinJ.exists_good_coinEJL BL hfrac hlt
  exact ⟨χe, _, genT_L χe,
    GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ genT hpGT hax9T hop5T (hleafT Rt0T) hwalk9T (hwalkAT Rt0T) hCT hndT
      (h31AT Rt0T) (aluLen_toy Rt0T) hlimbT hnoDecT (genT_L χe) hχ⟩

end Nock.RedTeam.Batch4936

#print axioms Nock.RedTeam.Batch4936.hCT
#print axioms Nock.RedTeam.Batch4936.genLink_toy
