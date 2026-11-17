/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHJRun.lean

  `genJ9AXJ` succeeds on a `genX` run and its record is explicit; its data is `j9aDataOf`'s without `hnc`.

  * `recJ9AXJRn Rt s f χe Rn` / `recJ9AXJ Rt s f χe t r`: the let-chain of `genJ9AXJ` (jets) as named terms;
  * `genJ9AXJ_some`: `genJ9AXJ R Rt fuel s f χe = some I → ∃ t r, genX R fuel s f = some (t, r) ∧ I = recJ9AXJ …`;
  * `cs_eqJ acs_eqJ HJ_eqJ pd_eqJ idOf_eqJ mv_eqJ mx_eqJ mh_eqJ jrows_eqJ` and the field equalities
    `regs_eqJ ids_eqJ idx_eqJ rk_eqJ Rt_eqJ lay_eqJ`, all at `j9aDataOf P Rg Rt hgen`;
  * `regOK_genJ9AXJ`: `RegOK I.toInJ8 Rg.R` from `CompiledBy`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.V1J9A.GenJ9AXJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axReadsK9 axKeys9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (idOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf rows9J W9J fxJ axOnJ spOnJ)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX
open Nock.V1J9A.GenJ9AXJ (genJ9AXJ)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.Jet.Autogen (compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (jNounsP mvFixP pinsOfP hJd mhJP j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

/-! ## 1. One stable def per `let` of `genJ9AXJ` -/

section defs

def cK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : P8PublicClaim := ⟨s, f, Rn.res⟩
def callsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List (ℕ × Noun) := callsOf Rn.rows
def idsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List ℕ := (callsK Rt s f χe Rn).map Prod.fst
def regsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List ℕ := (idsK Rt s f χe Rn).dedup
def jnK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List Noun := jNounsP P Rt (regsK Rt s f χe Rn) (callsK Rt s f χe Rn)
def rootsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List Noun := rootsOf (cK Rt s f χe Rn) Rn.rows ++ jnK Rt s f χe Rn
def csK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List Noun := cellsOfRoots (rootsK Rt s f χe Rn)
def acsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List Noun :=
  acsOfD (bigsOf (rootsK Rt s f χe Rn) Rn.rows) ((incOps Rn.rows).any fun x => x.1 + 1 = P)
def HK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Noun → ℕ × ℕ := hdlB (csK Rt s f χe Rn) (acsK Rt s f χe Rn)
def ptK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := ptrE (acsK Rt s f χe Rn) (stopEdges Rn.rows)
def pdK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := HonestPairX.pdX (sxE (ptK Rt s f χe Rn))
def idOfK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ → ℕ := idOf9 P (acsK Rt s f χe Rn).length (HK Rt s f χe Rn) (fxJ s f χe Rn)
def compK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := GenCompX9.compGenX9 (cK Rt s f χe Rn) (HK Rt s f χe Rn) (pdK Rt s f χe Rn)
  (idOfK Rt s f χe Rn) (W9J s f χe Rn) χe
def wsKrK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := walkGen ((csK Rt s f χe Rn).headD (.atom 0))
  (walkReadsX9 (rows9J s f χe Rn) ++ axChainReadsK9 (rows9J s f χe Rn))
def idxK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ → ℕ := fun id => idxOf (csK Rt s f χe Rn) (compile P (Rt id))
def layK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := layoutJ8 Rt (regsK Rt s f χe Rn) (idsK Rt s f χe Rn)
def jrowsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := mvFixP P (Nock.Jet.ChipJ8.honestJ8G (hJd P (csK Rt s f χe Rn) (acsK Rt s f χe Rn)) Rt
  (regsK Rt s f χe Rn) (callsK Rt s f χe Rn)) (pinsOfP P (regsK Rt s f χe Rn) (idxK Rt s f χe Rn))
def jgK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := jGen χe (jrowsK Rt s f χe Rn)
def mvK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := mvPins (mvCounts (csK Rt s f χe Rn) (cK Rt s f χe Rn)) (regsK Rt s f χe Rn) (idxK Rt s f χe Rn)
def mxK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := mxCounts (csK Rt s f χe Rn) (wsKrK Rt s f χe Rn).1
def mx1K (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := Array.replicate (csK Rt s f χe Rn).length 0
def mhK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := mhJP P (mhCountsX9E (csK Rt s f χe Rn) (compK Rt s f χe Rn).bases (wsKrK Rt s f χe Rn).1)
  (jrowsK Rt s f χe Rn)
def cRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := cellGenB (coOf χe) (yE χe) (HK Rt s f χe Rn) (bigIdOf (acsK Rt s f χe Rn)) (csK Rt s f χe Rn)
  (mvK Rt s f χe Rn) (mxK Rt s f χe Rn) (mx1K Rt s f χe Rn) (mhK Rt s f χe Rn)
def wRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (HK Rt s f χe Rn)
  (idxN (csK Rt s f χe Rn)) HonestK8.certB8 (csK Rt s f χe Rn) (wsKrK Rt s f χe Rn).1
  (wsKrK Rt s f χe Rn).2
def readsK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := pairReads (HK Rt s f χe Rn) (pdK Rt s f χe Rn) Rn.rows ++ axReadsK9 P (rows9J s f χe Rn)
def vsKrVK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : List WRow × ℕ :=
  if (readsK Rt s f χe Rn).isEmpty then ([], 0) else walkGen padN (readsK Rt s f χe Rn)
def HAK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Noun → ℕ × ℕ := Nock.V1J8.Gen.hdl (acsK Rt s f χe Rn)
def rIAK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Noun → ℕ :=
  fun n => if n = combP then lastIdxOf (acsK Rt s f χe Rn) combP else idxN (acsK Rt s f χe Rn) n
def aRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := atomGenE (ptK Rt s f χe Rn) χe (acsK Rt s f χe Rn)
  (infoOfE (acsK Rt s f χe Rn) (ptK Rt s f χe Rn) Rn.rows)
  (mbCounts9 (acsK Rt s f χe Rn) (csK Rt s f χe Rn) (cK Rt s f χe Rn))
  (wCounts (rIAK Rt s f χe Rn) (acsK Rt s f χe Rn) (vsKrVK Rt s f χe Rn).1)
  (wCounts (rIAK Rt s f χe Rn) (acsK Rt s f χe Rn) (vsKrVK Rt s f χe Rn).1)
def vRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Array (Array (ZMod P)) × (ℕ → K3) :=
  if (vsKrVK Rt s f χe Rn).2 = 0 then (#[Array.replicate 166 0], fun _ => 0)
  else walkGenRowsBE (ptK Rt s f χe Rn) (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1)
    (HAK Rt s f χe Rn) (rIAK Rt s f χe Rn) WalkJ8.certB (acsK Rt s f χe Rn) (vsKrVK Rt s f χe Rn).1
    (vsKrVK Rt s f χe Rn).2
def xRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) := GenAxE.axGenOf χe (acsK Rt s f χe Rn).length (HK Rt s f χe Rn) (rows9J s f χe Rn)
  (axOnJ s f χe Rn)
def sRPK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Array (Array (ZMod P)) × (ℕ → K3) :=
  if spOnJ s f χe Rn then
    GenSpE.spGenE χe (acsK Rt s f χe Rn).length (GenSpE.vSE (rows9J s f χe Rn))
      (GenSpE.mSE (rows9J s f χe Rn) (GenSpE.vSE (rows9J s f χe Rn)))
  else (#[Array.replicate 90 0], fun _ => (0 : K3))
def mK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ :=
  max (compK Rt s f χe Rn).rows.size (max (cRPK Rt s f χe Rn).1.size (max (wRPK Rt s f χe Rn).1.size
    (max (aRPK Rt s f χe Rn).1.size (max (vRPK Rt s f χe Rn).1.size (max (xRPK Rt s f χe Rn).1.size
      (max (sRPK Rt s f χe Rn).1.size (layK Rt s f χe Rn).length))))))
def BK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ := max 10 (2 * mK Rt s f χe Rn)

/-- **The explicit record of `genJ9AXJ`** over the run `Rn`. -/
def recJ9AXJRn (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (Rn : RunX) : InJ9A :=
  { c := cK Rt s f χe Rn
    M := { m := mOf (cK Rt s f χe Rn) (HK Rt s f χe Rn), ρ := (compK Rt s f χe Rn).ρ,
           ρS := (compK Rt s f χe Rn).ρS, pubsC := (cRPK Rt s f χe Rn).2, pubsW := (wRPK Rt s f χe Rn).2,
           pubsJ := (jgK Rt s f χe Rn).2, pubsA := (aRPK Rt s f χe Rn).2, pubsV := (vRPK Rt s f χe Rn).2 }
    χ := χe
    r := budget (mK Rt s f χe Rn)
    g := (regsK Rt s f χe Rn).length
    X := chipOf (compK Rt s f χe Rn).rows
    C := chipOf (cRPK Rt s f χe Rn).1
    W := chipOf (wRPK Rt s f χe Rn).1
    J := ⟨hOf (layK Rt s f χe Rn).length, (layK Rt s f χe Rn).length,
      ωOf (hOf (layK Rt s f χe Rn).length), colsOf (jgK Rt s f χe Rn).1 (layK Rt s f χe Rn).length⟩
    A := chipOf (aRPK Rt s f χe Rn).1
    V := chipOf (vRPK Rt s f χe Rn).1
    kroots := (wsKrK Rt s f χe Rn).2
    krootsV := (vsKrVK Rt s f χe Rn).2
    lay := (layK Rt s f χe Rn).get
    Rt := Rt
    regs := regsK Rt s f χe Rn
    ids := idsK Rt s f χe Rn
    idx := idxK Rt s f χe Rn
    rk := fun id => Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.rkC (compile P (Rt id))
    AX := chipOf (xRPK Rt s f χe Rn).1
    SP := chipOf (sRPK Rt s f χe Rn).1
    pubsX := (xRPK Rt s f χe Rn).2
    pubsS := (sRPK Rt s f χe Rn).2
    axOn := axOnJ s f χe Rn
    spOn := spOnJ s f χe Rn
    rAX := BK Rt s f χe Rn
    rSP := BK Rt s f χe Rn }
end defs

/-- **`recJ9AXJ Rt s f χe t r`**: the record over the run `⟨t, r, bfsForest [t], rowsOfT t⟩`. -/
def recJ9AXJ (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) : InJ9A :=
  recJ9AXJRn Rt s f χe (RnOf t r)

/-- `genJ9AXJ` is `recJ9AXJRn` on the run. -/
theorem genJ9AXJ_eq (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (fuel : ℕ) (s f : Noun)
    (χe : CoinsE) :
    genJ9AXJ R Rt fuel s f χe = (runX R fuel s f).map (recJ9AXJRn Rt s f χe) := by
  unfold genJ9AXJ
  cases runX R fuel s f with
  | none => rfl
  | some Rn => rfl

/-- **`genJ9AXJ` succeeds only on a `genX` run, and its record is `recJ9AXJ`.** -/
theorem genJ9AXJ_some {R : Nock.Jet.Registry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ} {s f : Noun}
    {χe : CoinsE} {I : InJ9A} (h : genJ9AXJ R Rt fuel s f χe = some I) :
    ∃ (t : NTree SkelX) (r : Noun), genX R fuel s f = some (t, r) ∧ I = recJ9AXJ Rt s f χe t r := by
  rw [genJ9AXJ_eq] at h
  have hr : runX R fuel s f = (genX R fuel s f).map fun tr =>
      (⟨tr.1, tr.2, bfsForest [tr.1], ComplJ8Data.rowsOfT tr.1⟩ : RunX) := by
    unfold runX; cases genX R fuel s f <;> rfl
  rw [hr] at h
  cases hg : genX R fuel s f with
  | none => rw [hg] at h; simp at h
  | some tr =>
    obtain ⟨t, r⟩ := tr
    rw [hg] at h
    simp only [Option.map_some] at h
    exact ⟨t, r, rfl, (Option.some.inj h).symm⟩

/-! ## 2. Data equalities at `j9aDataOf`, without `hnc` -/

section Run
variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem cs_eqJ (χe : CoinsE) :
    csK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).cells := rfl

theorem acs_eqJ (χe : CoinsE) :
    acsK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).acs := rfl

theorem HJ_eqJ (χe : CoinsE) : HK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).H := by
  show hdlB (csK Rt s f χe (RnOf t r)) (acsK Rt s f χe (RnOf t r)) = _
  rw [GenPortJ9A.hdlB_eq_hdlP]
  rfl

theorem pd_eqJ (χe : CoinsE) : pdK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).pd := by
  have hrows : (j8DataOf P Rg Rt hgen).rows = ComplJ8Data.rowsOfT t := rfl
  have hpd : (j8DataOf P Rg Rt hgen).pd =
      HonestPairX.pdX (ComplJ8Data.sxPP P (j8DataOf P Rg Rt hgen).acs (ComplJ8Data.rowsOfT t)) := rfl
  have hacs : acsK Rt s f χe (RnOf t r) = (j8DataOf P Rg Rt hgen).acs := rfl
  show HonestPairX.pdX (sxE (ptrE (acsK Rt s f χe (RnOf t r)) (stopEdges (ComplJ8Data.rowsOfT t)))) =
    (j8DataOf P Rg Rt hgen).pd
  rw [hacs, hpd]
  congr 1
  funext a e
  exact GenPortJ9.sxE_eq _ _ a e

theorem idOf_eqJ (χe : CoinsE) : idOfK Rt s f χe (RnOf t r) = idOfA (p := P) Rt hgen := by
  show idOf9 P _ _ _ = idOf9 P _ _ _
  rw [HJ_eqJ Rt hgen χe, acs_eqJ Rt hgen χe]
  rfl

theorem mv_eqJ (χe : CoinsE) : mvK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mv := rfl

theorem mx_eqJ (χe : CoinsE) : mxK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mx := rfl

theorem jrows_eqJ (χe : CoinsE) : jrowsK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).jrows := rfl

theorem mh_eqJ (χe : CoinsE) : mhK Rt s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mh := by
  have hbs : GenCompX9.basesX9 (HK Rt s f χe (RnOf t r)) (pdK Rt s f χe (RnOf t r))
      (idOfK Rt s f χe (RnOf t r)) (W9J s f χe (RnOf t r)) =
      ComplJ9ADataRec.basesA9 P (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (bfsForest [ComplJ9AGen.genX9T t]) := by
    rw [GenPortJ9A.basesX9_eq, HJ_eqJ Rt hgen χe, pd_eqJ Rt hgen χe, idOf_eqJ Rt hgen χe]
    try rfl
  show mhJP P (ComplJ9ADataRec.mhCountsX9 P (csK Rt s f χe (RnOf t r))
    (GenCompX9.basesX9 (HK Rt s f χe (RnOf t r)) (pdK Rt s f χe (RnOf t r))
      (idOfK Rt s f χe (RnOf t r)) (W9J s f χe (RnOf t r))) (wsKrK Rt s f χe (RnOf t r)).1)
    (jrowsK Rt s f χe (RnOf t r)) = _
  rw [hbs]
  rfl

theorem regs_eqJ (χe : CoinsE) : (recJ9AXJ Rt s f χe t r).regs = (j9aDataOf P Rg Rt hgen).regs := rfl
theorem ids_eqJ (χe : CoinsE) : (recJ9AXJ Rt s f χe t r).ids = (j9aDataOf P Rg Rt hgen).ids := rfl
theorem idx_eqJ (χe : CoinsE) : (recJ9AXJ Rt s f χe t r).idx = (j9aDataOf P Rg Rt hgen).idx := rfl
theorem rk_eqJ (χe : CoinsE) : (recJ9AXJ Rt s f χe t r).rk = (j9aDataOf P Rg Rt hgen).rk := rfl
theorem Rt_eqJ (χe : CoinsE) : (recJ9AXJ Rt s f χe t r).Rt = (j9aDataOf P Rg Rt hgen).Rt := rfl

theorem lay_eqJ (χe : CoinsE) : List.ofFn (recJ9AXJ Rt s f χe t r).lay = (j9aDataOf P Rg Rt hgen).lay := by
  show List.ofFn (layK Rt s f χe (RnOf t r)).get = _
  rw [List.ofFn_get]
  rfl

end Run

/-! ## 3. The registry premise -/

/-- Every id in the call list of a successful run is called (`s11j` rows carry an atom `f_tth`). -/
theorem callsIds_calledIds {R : Nock.Jet.Registry} {n : ℕ} {s f r : Noun} {t : NTree SkelX}
    (h : genX R n s f = some (t, r)) {i : ℕ} (hi : i ∈ (callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst) :
    i ∈ CalledIds t := by
  rw [List.mem_map] at hi
  obtain ⟨⟨a, b⟩, hc, rfl⟩ := hi
  unfold callsOf at hc
  rw [List.mem_filterMap] at hc
  obtain ⟨row, hrow, hrc⟩ := hc
  simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.mem_map] at hrow
  obtain ⟨u, hu, rfl⟩ := hrow
  by_cases hst : (rowOfSkelX u.label).st = .s11j
  · obtain ⟨t', ht', hin⟩ := (mem_bfsForest [t] u).1 hu
    have ht'' : t' = t := by simpa using ht'
    subst ht''
    have hs := inTree_rowSem h hin
    unfold RowNX.SemN at hs
    rw [hst] at hs
    obtain ⟨-, -, -, -, id', j, -, hft', hR, -, -⟩ := hs
    simp only [hst, if_true, Option.some.injEq, Prod.mk.injEq] at hrc
    obtain ⟨rfl, -⟩ := hrc
    refine ⟨u, hin, hst, ?_⟩
    rw [hft']
    rfl
  · simp [hst] at hrc

/-- **`RegOK` for the jet-calling record**: every registered id is called, and `CompiledBy` covers it. -/
theorem regOK_genJ9AXJ {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ} {s f : Noun}
    {χe : CoinsE} {I : InJ9A} (hC : CheckedRegistry.CompiledBy P Rg Rt)
    (hI : genJ9AXJ Rg.R Rt fuel s f χe = some I) : RegOK I.toInJ8 Rg.R := by
  obtain ⟨t, r, hg, rfl⟩ := genJ9AXJ_some hI
  intro i hi
  have hi' : i ∈ regsK Rt s f χe (RnOf t r) := hi
  have hid : i ∈ (callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst := List.mem_dedup.mp hi'
  obtain ⟨hj, -, hw⟩ := (CheckedRegistry.hRt_hregAx_of hC hg).1 i (callsIds_calledIds hg hid)
  exact ⟨hj, hw⟩

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
#print axioms recJ9AXJRn
#print axioms genJ9AXJ_eq
#print axioms genJ9AXJ_some
#print axioms cs_eqJ
#print axioms acs_eqJ
#print axioms HJ_eqJ
#print axioms pd_eqJ
#print axioms idOf_eqJ
#print axioms mv_eqJ
#print axioms mx_eqJ
#print axioms jrows_eqJ
#print axioms mh_eqJ
#print axioms regs_eqJ
#print axioms ids_eqJ
#print axioms idx_eqJ
#print axioms rk_eqJ
#print axioms Rt_eqJ
#print axioms lay_eqJ
#print axioms callsIds_calledIds
#print axioms regOK_genJ9AXJ
