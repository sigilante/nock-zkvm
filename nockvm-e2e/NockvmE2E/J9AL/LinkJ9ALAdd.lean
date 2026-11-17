/-
`HF1L` discharged at the executed add instance, and `add_air` with only the executed gate `hsh` left.

  1. `hF1L_of`: `HF1L XI` for ANY instance whose orbit is admissible (`shapeOkF` gives the order of `hGen`) and whose row bound `117 <= 3 * 2^(k+1)`
     holds, by ONE application of nock's `genJ9ALXJ_honest_at'` at Batch4936's record (`genT_L`-shaped `gen_RS`), a good coin from `exists_good_coinEJL`,
     and `OrbAdmL' (RS χe) (orbSh XI)` (sizes from `LinkJ9ALToy.sz_*`).
  2. `addShape_add`: `AddShape XL`, one `decide +kernel` per field (never over the instance).
  3. `add_air_add`: `add_air` at `XL`, hypotheses: only `hsh`.

Labels: [kernel job] = checked by Lean.  Not zero-knowledge.
-/
import NockvmE2E.J9AL.LinkJ9ALToy
import NockvmE2E.J9AL.E2EJ9ALToy
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.LinkJ9ALAdd

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9ALChips
open NockvmE2E.J8.InstJ8 (tabOf hNof)
open NockvmE2E.J9A.PbOfX9 (nOpt)
open NockvmE2E.J9AL.PbOfX9L (primsOf idxPOf rkPOf)
open NockvmE2E.J9AL.LinkJ9ALBridge (orbSh)
open NockvmE2E.J9AL.LinkJ9ALToy
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree (genJ9ALXJ_honest_at' OrbAdmL')
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (OrbFits)
open Nock.RedTeam.Batch4921 (Rt0T BL aluLen_toy complJ9AL_toy)
open Nock.RedTeam.Batch4936 (primsT hCT)
open NockvmE2E.J9AL.InstJ9AL (AccJ9AL PubP9AL)
open NockvmE2E.J9AL.DatX9LOk (DX9L)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.TraceGenExe (deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (card_KC)

noncomputable section

/-- an orbit `(k+1, ofU64 hGen)` fits a chip with at most `3 * 2^(k+1)` rows, given the order of `hGen` -/
theorem fits_sh (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (q : Nock.V1J8.Check.ChipIn)
    (hq : q.n ≤ 3 * 2 ^ (XI.k + 1)) :
    OrbFits q (⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩ : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.Orb) := by
  refine ⟨⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩, hq⟩
  show orderOf (Nock.TraceGenExe.Gold.ofU64 XI.hGen).toZ = 3 * 2 ^ (XI.k + 1)
  rw [Nock.TraceGenExe.Gold.ofU64_toZ]
  exact orbit_order_of_shapeF hsh

/-- **`hF1L_of`** [kernel job]: `HF1L XI` from the admissibility of the shared orbit (`hsh`) and the row bound `117 <= 3 * 2^(k+1)`. -/
theorem hF1L_of (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (hk : 117 ≤ 3 * 2 ^ (XI.k + 1)) : HF1L XI := by
  obtain ⟨-, hfrac, -, -, hfig⟩ := complJ9AL_toy
  obtain ⟨hlt, -⟩ := hfig card_KC
  obtain ⟨χe, hχ⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ.exists_good_coinEJL BL hfrac hlt
  have ho : OrbAdmL' (RS χe) (orbSh XI) :=
    ⟨⟨fits_sh XI hsh _ (by show (RS χe).X.n ≤ _; rw [sz_X]; omega),
      fits_sh XI hsh _ (by show (RS χe).C.n ≤ _; rw [sz_C]; omega),
      fits_sh XI hsh _ (by show (RS χe).W.n ≤ _; rw [sz_W]; omega),
      fits_sh XI hsh _ (by show (RS χe).J.n ≤ _; rw [sz_J]; omega),
      fits_sh XI hsh _ (by show (RS χe).A.n ≤ _; rw [sz_A]; omega),
      fits_sh XI hsh _ (by show (RS χe).V.n ≤ _; rw [sz_V]; omega),
      fits_sh XI hsh _ (by show (RS χe).AX.n ≤ _; rw [sz_AX]; omega),
      fits_sh XI hsh _ (by show (RS χe).SP.n ≤ _; rw [sz_SP]; omega)⟩,
      fits_sh XI hsh _ (by show (RS χe).AL.n ≤ _; rw [sz_AL]; omega)⟩
  exact ⟨χe, RS χe, gen_RS χe,
    genJ9ALXJ_honest_at' (hgen := genT) hpGT hax9T hop5T (hleafT Rt0T) hwalk9T (hwalkAT Rt0T) hCT hndT (h31AT Rt0T)
      (aluLen_toy Rt0T) hlimbT hnoDecT (gen_RS χe) hχ (orbSh XI) ho⟩

open NockvmE2E.J9AL.E2EJ9ALToy (XL facts_add hJ_add preg_add)

theorem k_add : 117 ≤ 3 * 2 ^ (XL.k + 1) := by decide +kernel

/-- **`hF1L_add`** [kernel job, modulo the executed gate `hsh`]: `HF1L` at the executed add instance. -/
theorem hF1L_add (hsh : shapeOkF famJ9AL XL = true) : HF1L XL := hF1L_of XL hsh k_add

theorem sh_X : hNof XL "computeChipVCLHX9" = 2 := by decide +kernel
theorem sh_C : hNof XL "cellChipHQKW" = 117 := by decide +kernel
theorem sh_W : hNof XL "walkChipJ8" = 1 := by decide +kernel
theorem sh_A : hNof XL "atomChipHQL" = 5 := by decide +kernel
theorem sh_V : nOpt XL "walkChipHQK" = 1 := by decide +kernel
theorem sh_AX : nOpt XL "axisChipJ9" = 1 := by decide +kernel
theorem sh_SP : nOpt XL "splitChipJ9" = 1 := by decide +kernel
theorem sh_AL : nOpt XL "aluChipJ9" = 12 := by decide +kernel
theorem sh_axo : (tabOf XL "axisChipJ9").isSome = false := by decide +kernel
theorem sh_spo : (tabOf XL "splitChipJ9").isSome = false := by decide +kernel
theorem sh_alo : (tabOf XL "aluChipJ9").isSome = true := by decide +kernel
theorem sh_prims : primsOf XL = primsT := facts_add.1
theorem sh_idx : idxPOf XL 7 = 5 := by decide +kernel
theorem sh_rk : rkPOf XL 7 = (0, 43) := by decide +kernel
theorem rt_add : NockvmE2E.J9A.RunGate9L.primsRoundTrip XL.pubIn.prims = true := by decide +kernel

/-- **`AddShape XL`** [kernel job]: per field. -/
theorem addShape_add : AddShape XL :=
  ⟨sh_X, sh_C, sh_W, sh_A, sh_V, sh_AX, sh_SP, sh_AL, sh_axo, sh_spo, sh_alo, sh_prims, sh_idx, sh_rk⟩

/-- **`add_air_add`** [kernel job]: `AccJ9AL ∧ PubP9AL` at the executed add datum; the only hypothesis is the executed gate `hsh`. -/
theorem add_air_add (hsh : shapeOkF famJ9AL XL = true) :
    ∃ χ M tr,
      AccJ9AL (DX9L XL hsh hJ_add 1 0 cAddB) χ M tr ∧
      PubP9AL (DX9L XL hsh hJ_add 1 0 cAddB) χ (M, fun j => pubVJ9 deltaF powerBasis3 cAddB M.m M.ρ M.ρS χ j) :=
  add_air XL hsh hJ_add addShape_add preg_add rt_add (hF1L_add hsh)

open NockvmE2E.J9AL.E2EJ9ALToy (cAdd)

/-- the two claims coincide: both are `⟨sT, fT, rT⟩` -/
theorem cAddB_eq : cAddB = cAdd := rfl

/-- **`add_air_datum_eq`** [kernel job,  F3]: the datum of `add_air_add` (`kroots = 1`, `krootsV = 0`, claim `cAddB`) IS the datum `add_witness` uses
(`kOfL XL`, `kVOfL XL`, claim `cAdd`).  No `decide` over the instance: `facts_add` gives the two numerals, `cAddB_eq` the claim. -/
theorem add_air_datum_eq (hsh : shapeOkF famJ9AL XL = true) :
    DX9L XL hsh hJ_add 1 0 cAddB = DX9L XL hsh hJ_add (NockvmE2E.J9A.RunGate9L.kOfL XL) (NockvmE2E.J9A.RunGate9L.kVOfL XL) cAdd := by
  obtain ⟨-, hk, hkv, -⟩ := facts_add
  have key : ∀ a b : ℕ, a = 1 → b = 0 → DX9L XL hsh hJ_add 1 0 cAddB = DX9L XL hsh hJ_add a b cAdd := by
    intro a b ha hb
    subst ha
    subst hb
    rfl
  exact key _ _ hk.symm hkv.symm

/-- **`add_air_add'`** [kernel job,  F3]: `add_air_add` stated at the witness datum of `add_witness`, so both live on one datum. -/
theorem add_air_add' (hsh : shapeOkF famJ9AL XL = true) :
    ∃ χ M tr,
      AccJ9AL (DX9L XL hsh hJ_add (NockvmE2E.J9A.RunGate9L.kOfL XL) (NockvmE2E.J9A.RunGate9L.kVOfL XL) cAdd) χ M tr ∧
      PubP9AL (DX9L XL hsh hJ_add (NockvmE2E.J9A.RunGate9L.kOfL XL) (NockvmE2E.J9A.RunGate9L.kVOfL XL) cAdd) χ (M, fun j => pubVJ9 deltaF powerBasis3 cAdd M.m M.ρ M.ρS χ j) := by
  obtain ⟨χ, M, tr, h1, h2⟩ := add_air_add hsh
  rw [add_air_datum_eq hsh] at h1 h2
  exact ⟨χ, M, tr, h1, h2⟩

end

end NockvmE2E.J9AL.LinkJ9ALAdd

#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.hF1L_of
#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.hF1L_add
#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.addShape_add
#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.add_air_add
#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.add_air_datum_eq
#print axioms NockvmE2E.J9AL.LinkJ9ALAdd.add_air_add'
