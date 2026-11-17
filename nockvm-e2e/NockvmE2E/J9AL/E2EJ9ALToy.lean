/-
the datum-side non-vacuity witness of `exec_e2e_J9AL` at the executed `add` instance
(`Exec/AddALR.lean`): `add_witness` (every datum premise `Wit9L` at `XI170 addALR`, claim = nockvm's run, and the claim holds) and `add_witness_false`
(the false twin at `addALRF`: result `2p+13`, every gate equal, `¬ HoldsN`).  `shapeOkF` stays the executed hypothesis `hsh` (as at J-9 A).
`HoldsN` of the add claim is proved here from `primSpec_faithful` / `primSpec_complete` / `binT_rel` (local copies of the three short lemmas of nock's
`Batch4923`, whose module is not built in the pinned nock package).  No `decide` over `pre` or the whole instance; gates are split per conjunct.
Not zero-knowledge.
-/
import NockvmE2E.Exec.AddALR
import NockvmE2E.J9AL.RunGate9LVRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALToyFacts
import Nock.RedTeam.Batch4936Thm54J9ALGenLinkToy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.E2EJ9ALToy

open Nock Nock.Jet Nock.Jet.Prim Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.RunGate9L NockvmE2E.J9AL.WitJ9AL NockvmE2E.J9AL.RunGate9LVRun NockvmE2E.J9AL.DatX9LOk NockvmE2E.J9AL.PbOfX9L
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open NockvmE2E.Exec.AddALR

/-! ## 1. claims and nockvm's run -/

def cAdd : P8PublicClaim := ⟨sT, fT, rT⟩
def cAddF : P8PublicClaim := ⟨sT, fT, .atom (2 * Nock.Field.p + 13)⟩

theorem hT_of_ne (op : PrimOp) (hop : op ≠ .dec) : (primSpec op).T = binT op := by
  cases op <;> first | rfl | exact absurd rfl hop

theorem holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {x y n : ℕ} (h : primSem op x y = some n) :
    HoldsN ⟨.cell (.atom x) (.atom y), primC op, .atom n⟩ := by
  have hrel : (primSpec op).T.rel (.cell (.atom x) (.atom y)) (.atom n) := by
    rw [hT_of_ne op hop]; exact binT_rel_of h
  exact (primSpec_faithful op).1 _ _ hrel

theorem not_holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {s res : Noun}
    (h : ∀ x y n, s = .cell (.atom x) (.atom y) → primSem op x y = some n → res ≠ .atom n) :
    ¬ HoldsN ⟨s, primC op, res⟩ := by
  rintro ⟨fuel, hf⟩
  have hrel := primSpec_complete op s fuel res hf
  rw [hT_of_ne op hop] at hrel
  obtain ⟨x, y, n, hs, hn, hr⟩ := binT_rel hrel
  exact h x y n hs hn hr

theorem clue_computes (s : Noun) : ∃ fuel v, Nock.evalN fuel s clueT = some v :=
  ⟨1, .atom idAdd, by simp [clueT, Nock.evalN]⟩

theorem fT_eq : fT = hint (.atom wildTag) clueT (primC .add) := rfl

theorem sem_add : primSem .add (Nock.Field.p + 5) (Nock.Field.p + 7) = some (2 * Nock.Field.p + 12) := by
  simp [primSem, Nock.Field.p]

theorem holds_add : HoldsN cAdd := by
  have : cAdd = ⟨.cell (.atom (Nock.Field.p + 5)) (.atom (Nock.Field.p + 7)), hint (.atom wildTag) clueT (primC .add), .atom (2 * Nock.Field.p + 12)⟩ := rfl
  rw [this]
  exact holdsN_hint_iff.mpr ⟨clue_computes _, holdsN_primC (by decide) sem_add⟩

theorem not_holds_addF : ¬ HoldsN cAddF := by
  intro hh
  have h : HoldsN ⟨.cell (.atom (Nock.Field.p + 5)) (.atom (Nock.Field.p + 7)), hint (.atom wildTag) clueT (primC .add), .atom (2 * Nock.Field.p + 13)⟩ := hh
  have h1 := (holdsN_hint_iff.mp h).2
  refine not_holdsN_primC (by decide) ?_ h1
  intro x y n hs hn hres
  obtain ⟨rfl, rfl⟩ : x = Nock.Field.p + 5 ∧ y = Nock.Field.p + 7 := by simpa using hs.symm
  rw [sem_add] at hn
  have : n = 2 * Nock.Field.p + 12 := (Option.some.inj hn).symm
  subst this
  have := Noun.atom.inj hres
  omega

theorem run_add : (Nock.V1J8.Gen.runX RgT.R 2 sT fT).map (·.res) = some cAdd.result := by
  have hr : Nock.V1J8.Gen.runX RgT.R 2 sT fT =
      some ⟨tT, rT, Nock.Walk.bfsForest [tT], Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.rowsOfT tT⟩ := by
    unfold Nock.V1J8.Gen.runX; rw [genT]; rfl
  rw [hr]; rfl


/-! ## 2. the datum side -/

abbrev XL : ExecInst := XI170 addALR
abbrev XLF : ExecInst := XI170 addALRF

/-- the premises `Q` of the witness: ALU on, the registry of the single primitive `(7, add)`, one walk root, no walkHQK, no axis, no split -/
def QAdd (d : NockvmE2E.J9AL.InstJ9AL.Datum9AL) : Prop :=
  d.Pb.aluOn = true ∧ d.Pb.prims = [(idAdd, .add)] ∧ d.Rg = RgT.R ∧ d.Pb.kroots = 1 ∧ d.Pb.krootsV = 0 ∧ d.Pb.axOn = false ∧ d.Pb.spOn = false

macro "link_tac" : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first | (intro t; fin_cases t <;> decide +kernel) | decide +kernel))

theorem can_add : inpCanOkL XL.pubIn = true := by decide +kernel
theorem can_addF : inpCanOkL XLF.pubIn = true := by decide +kernel

theorem link_add : LinkOK9L XL cAdd := by
  unfold LinkOK9L PrimsLink
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (intro t; fin_cases t <;> decide +kernel) | decide +kernel

theorem link_addF : LinkOK9L XLF cAddF := by
  unfold LinkOK9L PrimsLink
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (intro t; fin_cases t <;> decide +kernel) | decide +kernel

/-! ## 3. `pregOkF`: the non-ALU tables are unconstrained; the ALU's header and three preg columns one by one -/

open NockvmE2E.Exec.VF (PN)
open NockvmE2E.Exec.MaskOk (evalNodes)

theorem tabs_size : XL.tabs.size = 5 := by decide +kernel

theorem preg_hdr : (decide (XL.pubIn.prims.length ≤ addALT4.hN) &&
    XL.pubIn.prims.all (fun q => decide (q.id < PN) && decide (q.code < PN))) = true := by decide +kernel

theorem preg_k0 : (decide ((XL.pre.getD (addALT4.col0 + 2 + 0) #[]).size ≤ addALT4.hN) &&
    evalNodes (XL.pre.getD (addALT4.col0 + 2 + 0) #[]) XL.hGen addALT4.hN ==
      (Array.range addALT4.hN).map (pregVal XL.pubIn.prims 0)) = true := by decide +kernel
theorem preg_k1 : (decide ((XL.pre.getD (addALT4.col0 + 2 + 1) #[]).size ≤ addALT4.hN) &&
    evalNodes (XL.pre.getD (addALT4.col0 + 2 + 1) #[]) XL.hGen addALT4.hN ==
      (Array.range addALT4.hN).map (pregVal XL.pubIn.prims 1)) = true := by decide +kernel
theorem preg_k2 : (decide ((XL.pre.getD (addALT4.col0 + 2 + 2) #[]).size ≤ addALT4.hN) &&
    evalNodes (XL.pre.getD (addALT4.col0 + 2 + 2) #[]) XL.hGen addALT4.hN ==
      (Array.range addALT4.hN).map (pregVal XL.pubIn.prims 2)) = true := by decide +kernel

theorem preg_add : pregOkF XL = true := by
  unfold pregOkF
  rw [Array.all_eq_true]
  intro i hi
  rw [tabs_size] at hi
  interval_cases i
  · show (if (addALT0.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (addALT0.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (addALT1.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (addALT1.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (addALT2.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (addALT2.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (addALT3.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (addALT3.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (addALT4.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (addALT4.chip.id == "aluChipJ9") = true := by decide +kernel
    simp only [h, ite_true]
    rw [Bool.and_eq_true]
    refine ⟨preg_hdr, ?_⟩
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    interval_cases k
    · exact preg_k0
    · exact preg_k1
    · exact preg_k2

/-- `pregOkF` reads only the tables, the preprocessed columns, `hGen` and the primitive records -/
theorem pregOkF_congr (A B : ExecInst) (ht : A.tabs = B.tabs) (hp : A.pubIn.prims = B.pubIn.prims) (hpre : A.pre = B.pre)
    (hg : A.hGen = B.hGen) : pregOkF A = pregOkF B := by
  unfold pregOkF; rw [ht, hp, hpre, hg]

theorem preg_addF : pregOkF XLF = true := by
  rw [pregOkF_congr XLF XL rfl rfl rfl rfl]; exact preg_add

/-! ## 4. the witnesses -/

open NockvmE2E.J9AL.DatX9LOk (DX9L)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (addPrims)

theorem hQ_gen (XX : ExecInst) (hsh : shapeOkF famJ9AL XX = true) (hJ : hNof XX "jetChipJ8" = 0)
    (hp : primsOf XX = [(idAdd, .add)]) (hk : kOfL XX = 1) (hkV : kVOfL XX = 0) (hal : (tabOf XX "aluChipJ9").isSome = true)
    (hax : (tabOf XX "axisChipJ9").isSome = false) (hsp : (tabOf XX "splitChipJ9").isSome = false) (c : P8PublicClaim) :
    QAdd (DX9L XX hsh hJ (kOfL XX) (kVOfL XX) c) := by
  refine ⟨hal, hp, ?_, hk, ?_, hax, hsp⟩
  · show (addPrims Nock.Jet.VerifiedRegistry.empty (primsOf XX)).R = RgT.R
    rw [hp]; rfl
  · show (if (tabOf XX "walkChipHQK").isSome then kVOfL XX else 0) = 0
    split <;> simp [hkV]

theorem facts_add : primsOf XL = [(idAdd, .add)] ∧ kOfL XL = 1 ∧ kVOfL XL = 0 ∧ (tabOf XL "aluChipJ9").isSome = true ∧
    (tabOf XL "axisChipJ9").isSome = false ∧ (tabOf XL "splitChipJ9").isSome = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem facts_addF : primsOf XLF = [(idAdd, .add)] ∧ kOfL XLF = 1 ∧ kVOfL XLF = 0 ∧ (tabOf XLF "aluChipJ9").isSome = true ∧
    (tabOf XLF "axisChipJ9").isSome = false ∧ (tabOf XLF "splitChipJ9").isSome = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem hJ_add : hNof XL "jetChipJ8" = 0 := by decide +kernel
theorem hJ_addF : hNof XLF "jetChipJ8" = 0 := by decide +kernel

/-- **`add_witness`** [kernel job, modulo the executed gate `hsh`]: every datum premise of `exec_e2e_J9AL` (`Wit9L`) holds at the executed `add`
instance, for the claim = nockvm's run of `*[[(p+5) (p+7)] [11 [%wild [1 7]] (primC add)]] = 2p+12`; the run is nockvm's, and the claim holds. -/
theorem add_witness (hsh : shapeOkF famJ9AL XL = true) :
    Wit9L XL cAdd QAdd ∧ (Nock.V1J8.Gen.runX RgT.R 2 sT fT).map (·.res) = some cAdd.result ∧ HoldsN cAdd :=
  ⟨witness9L XL cAdd hsh preg_add (primsCan_of_inpCanOkL can_add) link_add QAdd
      (fun hJ => by obtain ⟨a, b, c, d, e, f⟩ := facts_add; exact hQ_gen XL hsh hJ a b c d e f cAdd),
    run_add, holds_add⟩

/-- **`add_witness_false`** [kernel job, modulo `hsh` at the twin]: at the twin instance `addALRF` (result record `2p+13`) every datum premise holds
for `cAddF`, the run is still nockvm's (`2p+12`), the two results differ, and `¬ HoldsN cAddF`. -/
theorem add_witness_false (hsh : shapeOkF famJ9AL XLF = true) :
    Wit9L XLF cAddF QAdd ∧ (Nock.V1J8.Gen.runX RgT.R 2 sT fT).map (·.res) = some cAdd.result ∧
      cAddF.result ≠ cAdd.result ∧ ¬ HoldsN cAddF :=
  ⟨witness9L XLF cAddF hsh preg_addF (primsCan_of_inpCanOkL can_addF) link_addF QAdd
      (fun hJ => by obtain ⟨a, b, c, d, e, f⟩ := facts_addF; exact hQ_gen XLF hsh hJ a b c d e f cAddF),
    run_add, by simp [cAddF, cAdd, rT], not_holds_addF⟩

end NockvmE2E.J9AL.E2EJ9ALToy

#print axioms NockvmE2E.J9AL.E2EJ9ALToy.holds_add
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.not_holds_addF
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.run_add
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.link_add
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.link_addF
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.preg_add
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.add_witness
#print axioms NockvmE2E.J9AL.E2EJ9ALToy.add_witness_false
