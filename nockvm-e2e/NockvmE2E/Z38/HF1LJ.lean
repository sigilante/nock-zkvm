/-
NockvmE2E/Z38/HF1LJ.lean   (statement frozen)

`HF1LJ XI`: the named hypothesis of the template-jet AIR side `jp_air`: the conclusion of nock's `genJ9ALXJ_honest_at'`
(Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbFree.lean:909) at our run:
  Rg = catJ.toVR, Rt0 = catJ.toCR.Rt, prims = catJ.prims (= [(8, add)]), P = Nock.Atoms.p, subject [3 (p+5)], fuel 4,
  formula = the template call (id 7, `compile p TN`) then the big-atom `add` (id 8), orbit `orbSh XI` (every chip at `(k+1, ofU64 hGen)`).
For SOME coins `χe`, `genJ9ALXJ` returns `I` and `AcceptsJ9AL` holds of the generator's record moved onto `orbSh XI`.
Not an axiom: a `def`'d `Prop`, passed as an argument.  The program is the one of `Exec/J9ALConv.jpProg` (same literal text).  Not zero-knowledge.
-/
import NockvmE2E.J9AL.LinkJ9ALBridge
import NockvmE2E.Z38.CatJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.HF1LJ

open Nock Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (withOrbL)
open Nock.V1J9AL.CheckJ9AL (InJ9AL)
open Nock.V1J9AL.CheckJ9ALIff (ValidJ9AL mkPbAL)
open Nock.TraceGenExe (deltaF powerBasis3)
open Nock.V1J8.Exe (CoinsE)
open NockvmE2E.Exec NockvmE2E.Exec.V
open NockvmE2E.J9AL.LinkJ9ALBridge (orbSh)

/-- the subject `[3 (p+5)]` -/
def sJ : Noun := .cell (.atom 3) (.atom (Nock.Field.p + 5))

/-- the formula: one template call (id 7, `compile p TN`) and one big-atom `add` (id 8), as `jpProg.2` -/
def fJ : Noun :=
  .cell (.cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) (.cell (.atom 1) (.atom 7)))
            (Nock.Jet.Autogen.compile Nock.Field.p NockvmE2E.Z38.CatJ.TN)))
         (.cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) (.cell (.atom 1) (.atom 8))) (Nock.Jet.Prim.primC .add)))

noncomputable section

/-- **`HF1LJ XI`** -/
def HF1LJ (XI : ExecInst) : Prop :=
  ∃ (χe : CoinsE) (I : InJ9AL),
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ NockvmE2E.Z38.CatJ.catJ.toVR.R (rtP NockvmE2E.Z38.CatJ.catJ.toCR.Rt NockvmE2E.Z38.CatJ.catJ.prims)
      NockvmE2E.Z38.CatJ.catJ.prims 4 sJ fJ χe = some I ∧
    ∃ hv : ValidJ9AL (withOrbL I (orbSh XI)),
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I (orbSh XI)) hv)
        NockvmE2E.Z38.CatJ.catJ.toVR.R
        (withOrbL I (orbSh XI)).c (Nock.V1J8.Exe.toχ (withOrbL I (orbSh XI)).χ) (withOrbL I (orbSh XI)).toMsgL
        (withOrbL I (orbSh XI)).toTrL (withOrbL I (orbSh XI)).toRowsL (withOrbL I (orbSh XI)).g

end

end NockvmE2E.Z38.HF1LJ
