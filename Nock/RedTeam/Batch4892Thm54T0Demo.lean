import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
import Nock.TraceGenExe.K6
import Nock.TraceGenExe.PowerBasis
import Nock.Jet.Interp

set_option autoImplicit false

namespace Nock.RedTeam.Batch4892

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry (CheckedReg)
open Nock.V1J8.Exe (toχ)
open Nock.Jet.Autogen (Tpl HasTy compile Ex Ty)
open Nock.TraceGenExe (KC deltaF powerBasis3)

noncomputable section

instance factRC : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
instance charPKC : CharP KC (ringChar (ZMod Nock.Field.p)) := by
  rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
instance algRC : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra _ _

theorem card_KC : Fintype.card KC = VclL.Events.cK := by
  rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq]

/-! ## 1. The template, the registry and the run -/

/-- `x : F` at axis 2, `d : N` at axis 3; body `build [x*x, d]`. -/
def TN : Tpl where
  k := 2
  ax := ![2, 3]
  inTy := ![.F, .N]
  outTy := .L 2 .N
  body := Ex.build [.mul (.var 0) (.var 0), .var 1]

theorem TN_wt (p : ℕ) : TN.WellTyped p := by
  unfold Tpl.WellTyped TN Ex.build
  simp only [List.foldr]
  exact HasTy.pair (HasTy.weakN (HasTy.mul (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)
    (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)))
    (HasTy.pair (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 1) (HasTy.nil _))

abbrev pG : ℕ := Nock.Field.p

def CN : CheckedReg pG where
  hp := by decide
  Rt := fun _ => TN
  regs := [7]
  wt := fun _ _ => TN_wt _
  axPos := fun _ _ => by decide
  axLt := fun _ _ i => by fin_cases i <;> decide

def RgN : Nock.Jet.VerifiedRegistry := CN.toVR
abbrev RtN : ℕ → Tpl := CN.Rt

def sN : Noun := .cell (.atom 3) (.atom (pG + 5))
def fC : Noun := .cell (.atom 1) (.atom 7)
def fJ : Noun := .cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) fC) (compile pG TN))
def rN : Noun := .cell (.atom 9) (.cell (.atom (pG + 5)) (.atom 0))

theorem jetN_sem : TN.sem pG sN = some rN := by decide +kernel

theorem jetN : Nock.Edit.GenX.jetHit RgN.R (.atom Nock.Jet.wildTag) (.atom 7) (compile pG TN) sN = some rN := by
  decide +kernel


def tC : NTree SkelX := mkX .s1 sN fC (.atom 7) []
def tJ : NTree SkelX := mkX .s11j sN fJ rN [tC]

theorem gC : genX RgN.R 1 sN fC = some (tC, .atom 7) := rfl

theorem genN : genX RgN.R 2 sN fJ = some (tJ, rN) := by
  have h := gC
  simp only [genX] at h
  simp only [genX, fJ, genComputeSkeletonX, h, jetN]
  rfl

/-! ## 2. Rows and data -/

theorem bfsN : bfsForest [tJ] = [tJ, tC] := by
  simp [bfsForest, tJ, tC, mkX]

theorem rowsN : ComplJ8Data.rowsOfT tJ = #[rowOfSkelX tJ.label, rowOfSkelX tC.label] := by
  simp only [ComplJ8Data.rowsOfT, bfsN]; rfl

theorem inTree_tJ (u : NTree SkelX) (h : InTree tJ u) : u = tJ ∨ u = tC := by
  have : u ∈ bfsForest [tJ] := (mem_bfsForest [tJ] u).2 ⟨tJ, by simp, h⟩
  rw [bfsN] at this; simpa using this

abbrev DD := j8DataOf pG RgN RtN genN
abbrev DA := ComplJ9ADataRec.j9aDataOf pG RgN RtN genN

theorem callsN : DD.calls = [(7, sN)] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tJ) = _
  rw [rowsN]; decide +kernel

theorem readsN : DD.reads = [] := by
  show Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tJ) = []
  rw [rowsN]; decide +kernel

theorem preadsN : DD.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tJ) = []
  rw [rowsN]; decide +kernel

theorem rootsN : DD.roots = Nock.V1J8.Gen.rootsOf ⟨sN, fJ, rN⟩ (ComplJ8Data.rowsOfT tJ) ++
    ComplJ8Data.jNounsP pG RtN [7] [(7, sN)] := by
  show Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT tJ) ++
    ComplJ8Data.jNounsP pG RtN (List.map Prod.fst DD.calls).dedup DD.calls = _
  rw [callsN]; rfl

theorem hleafN : ComplJ8Walk.RootsLeafOK DD.roots := by
  rw [rootsN, rowsN]
  show ∀ x ∈ _, Noun.leaves x ≤ 2 ^ 109
  decide +kernel


/-! ## 3. The J-9 A tree (no axis chip, no split chip: no big or field axis is read) -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9 rowX9) in
def gT9 : NTree LX9 :=
  .node ⟨rowX9 tJ.label, .old, 0, 0, rowOfSkelX tJ.label⟩
    [.node ⟨rowX9 tC.label, .old, 0, 0, rowOfSkelX tC.label⟩ []]

theorem chipJ : ComplJ9AGen.chipOf tJ.label = (.old, 0) := rfl
theorem chipC : ComplJ9AGen.chipOf tC.label = (.old, 0) := rfl

theorem genX9T_N : ComplJ9AGen.genX9T tJ = gT9 := by
  have hC : ComplJ9AGen.genX9T tC = .node ⟨ComplJ9AGen.rowX9 tC.label, .old, 0, 0, rowOfSkelX tC.label⟩ [] := by
    show ComplJ9AGen.genX9T (.node tC.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipC]; rfl
  show ComplJ9AGen.genX9T (.node tJ.label [tC]) = _
  rw [ComplJ9AGen.genX9T_node, chipJ]
  simp only [List.map_cons, List.map_nil, hC, ComplJ9AGen.kid9, chipJ, chipC, gT9]
  simp

theorem bfs9N : bfsForest [gT9] = [gT9, .node ⟨ComplJ9AGen.rowX9 tC.label, .old, 0, 0, rowOfSkelX tC.label⟩ []] := by
  simp [bfsForest, gT9]

theorem rows9N : ComplJ9AGen.rowsOfT9 tJ =
    #[⟨ComplJ9AGen.rowX9 tJ.label, .old, 0, 0, rowOfSkelX tJ.label⟩,
      ⟨ComplJ9AGen.rowX9 tC.label, .old, 0, 0, rowOfSkelX tC.label⟩] := by
  simp only [ComplJ9AGen.rowsOfT9, genX9T_N, bfs9N]; rfl

theorem keys9N : ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 tJ) = [] := by
  rw [rows9N]; decide

theorem axAtoms9N : ComplJ9AData.axAtoms9 (ComplJ9AGen.rowsOfT9 tJ) = [] := by
  rw [rows9N]; decide

theorem fieldAx9N : ComplJ9AData.fieldAx9 pG (ComplJ9AGen.rowsOfT9 tJ) = [] := by
  unfold ComplJ9AData.fieldAx9; rw [axAtoms9N]; simp

theorem axOnA_tJ : ComplJ9ARun.axOnA tJ = false := by
  simp [ComplJ9ARun.axOnA, keys9N]

theorem spOnA_tJ : ComplJ9ARun.spOnA pG tJ = false := by
  simp [ComplJ9ARun.spOnA, fieldAx9N]

/-! ## 4. The binders -/

theorem walkReads9N : ComplJ9ABinders.walkReads9 (ComplJ8Data.rowsOfT tJ) = [] := by
  rw [rowsN]; decide +kernel

theorem hwalk9N : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT tJ) := by
  show ComplJ8Walk.WalkDepthOK (ComplJ9ABinders.walkReads9 _)
  rw [walkReads9N]; intro r hr; simp [VclL.pathReads] at hr

theorem hwalkAN : ComplJ8Walk.WalkDepthOK DD.preads := by
  rw [preadsN]; intro r hr; simp [VclL.pathReads] at hr

theorem haxN : ComplJ8.ProgAxOK pG tJ := by
  intro u hu
  rcases inTree_tJ u hu with rfl | rfl
  all_goals
    unfold ComplJ8.AxRowX
    simp [rowOfSkelX, tJ, tC, mkX, fJ, fC, VclL.hdN, VclL.tlN, kidE, SkelX.row]
  all_goals decide

theorem hax9N : ComplJ9ABinders.ProgAxOK9A pG tJ := ComplJ9ABinders.progAxOK9A_of_progAxOK haxN

theorem stJ : (rowOfSkelX tJ.label).st = .s11j := rfl
theorem stC : (rowOfSkelX tC.label).st = .s1 := rfl

theorem hop5N : ComplJ8.ProgOp5OK pG tJ := by
  intro u hu
  rcases inTree_tJ u hu with rfl | rfl
  · intro h; rw [stJ] at h; exact absurd h (by decide)
  · intro h; rw [stC] at h; exact absurd h (by decide)

/-! ## 5. The sizes -/

theorem cellsN_len' : (Nock.V1J8.Gen.cellsOfRoots (Nock.V1J8.Gen.rootsOf ⟨sN, fJ, rN⟩ (ComplJ8Data.rowsOfT tJ) ++
    ComplJ8Data.jNounsP pG RtN [7] [(7, sN)])).length ≤ 2 ^ 31 := by
  rw [rowsN]
  decide +kernel

theorem da_cells_gen {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Tpl} {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (ComplJ9ADataRec.j9aDataOf p Rg Rt hgen).cells =
      Nock.V1J8.Gen.cellsOfRoots (j8DataOf p Rg Rt hgen).roots := rfl

theorem cellsN_len : DA.cells.length ≤ 2 ^ 31 :=
  (congrArg List.length (da_cells_gen genN)).trans_le
    ((congrArg (fun r => (Nock.V1J8.Gen.cellsOfRoots r).length) rootsN).trans_le cellsN_len')

theorem jrowsN_len : DA.jrows.length ≤ 2 ^ 20 := by
  show DD.jrows.length ≤ 2 ^ 20
  rw [ComplJ8Jet.j8DataOf_jrows]
  simp only [ComplJ8Data.mvFixP, List.length_map]
  show (Nock.Jet.ChipJ8.honestJ8G _ RtN (List.map Prod.fst DD.calls).dedup DD.calls).length ≤ 2 ^ 20
  rw [callsN]
  decide +kernel

theorem walkReadsX9N : ComplJ9AReads.walkReadsX9 (ComplJ9AGen.rowsOfT9 tJ) = [] := by
  rw [rows9N]; decide

theorem readsN9 : DA.reads = [] := by
  change ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ = []
  rw [walkReadsX9N, List.nil_append]
  unfold ComplJ9AChainsRun.axChainReadsK9
  rw [keys9N]; simp

theorem preadsN9 : DA.preads = [] := by
  show DD.preads ++ ComplJ9AChainsRun.axReadsK9 pG (ComplJ9AGen.rowsOfT9 tJ) = []
  rw [preadsN, List.nil_append]
  unfold ComplJ9AChainsRun.axReadsK9
  rw [keys9N]
  have : ((ComplJ9AGen.rowsOfT9 tJ).toList.filter
      fun l => decide (l.chip = .s10B ∧ pG ≤ l.n)) = [] := by rw [rows9N]; decide
  rw [this]; simp

theorem nVN : nVOf DA ≤ 2 ^ 31 := by
  unfold nVOf
  rw [preadsN9]; simp

theorem bigsN : DD.bigs = [pG + 5] := by
  show ComplJ8Data.bigsP _ DD.roots (ComplJ8Data.rowsOfT tJ) = _
  rw [rootsN, rowsN]
  unfold ComplJ8Data.bigsP
  rw [show (List.filter _ _).dedup = [pG + 5] by decide +kernel]
  simp


theorem limbsN : Nock.Atoms.limbs (pG + 5) = [6, Nock.Atoms.B - 1] := by
  have h := ComplJ8BigBound.limbs_two (a := pG + 5) (by simp [Nock.Atoms.p, pG, Nock.Field.p])
    (by simp [Nock.Atoms.p, pG, Nock.Field.p])
  rw [h]; simp [Nock.Atoms.p, pG, Nock.Field.p]

theorem acsN_len : DA.acs.length ≤ 3 := by
  show (ComplJ8Data.acsP _ DD.bigs _).length ≤ 3
  rw [bigsN]
  unfold ComplJ8Data.acsP
  simp only [List.foldl_cons, List.foldl_nil, limbsN]
  have hsp : Nock.V1J8.Gen.spineOf [6, Nock.Atoms.B - 1] = [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] =
      [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem N9N : ComplJ9ARun.N9 tJ = 2 := by
  rw [ComplJ9ARun.N9_def, ComplJ9ARun.W9, genX9T_N, bfs9N]; rfl

theorem nXN : ComplJ9ARun.nXOf pG DA.acs.length DA.H tJ = 1 := by
  simp [ComplJ9ARun.nXOf, axOnA_tJ]

theorem nSN : ComplJ9ARun.nSOf pG tJ = 1 := by
  simp [ComplJ9ARun.nSOf, spOnA_tJ]

theorem h31N : ComplJ9ARun.Rows31A DA := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DA.t]).length = 2 := by
    show (bfsForest [tJ]).length = 2
    rw [bfsN]; rfl
  have hC := cellsN_len
  have hW : (VclL.GenWalk.walkRows DA.cells DA.reads).length ≤ 2 ^ 31 := by
    rw [readsN9]
    have := VclL.GenWalk.walkRows_length_le DA.cells []
    simp [VclL.pathReads] at this
    omega
  have hJ := jrowsN_len
  have hA := acsN_len
  have hV := nVN
  have hN : ComplJ9ARun.N9 DA.t = 2 := N9N
  have hX : ComplJ9ARun.nXOf pG DA.acs.length DA.H DA.t = 1 := nXN
  have hS : ComplJ9ARun.nSOf pG DA.t = 1 := nSN
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

/-! ## 6. `complJ9A_closed_of` at the run -/

abbrev BN := ComplJ9ARun.BRun9A deltaF powerBasis3 RtN genN rfl h31N

open Classical in
/-- **`complJ9A_closed_of_N`: J-9 A completeness at a concrete run of a jet with a natural-number-typed input,
every hypothesis discharged.**  The jet is the compiled template `TN` (input `x` a field element at axis 2, input
`d` a natural number at axis 3, output the list `[x*x, d]`) over the Goldilocks prime, run on the subject
`[3 (p+5)]`.  For this run, `AcceptsJ9A` accepts at every good coin, the fraction of coins that are not good is at
most `ε_c`, the trace family is staged (`StJ9A`), the claim `*[[3 (p+5)] [11 [7 [1 0]] (compile p TN)]] =
[9 [(p+5) 0]]` holds (`HoldsN`), and, as `|K| = cK`, `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9A_closed_of_N :
    (∀ χ, BN.Good χ → AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BN.Pb RgN.R
      (ComplJ8.cJ sN fJ rN) χ (BN.M χ) (BN.tr χ) BN.rows BN.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BN.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BN.epsC) ∧
    RealIOJ9A.StJ9A BN.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sN fJ rN) ∧
    (Fintype.card KC = VclL.Events.cK →
      BN.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BN.Pb RgN.R
        (ComplJ8.cJ sN fJ rN) χ (BN.M χ) (BN.tr χ) BN.rows BN.g) :=
  ComplClosedChecked.complJ9A_closed_of deltaF powerBasis3 RtN genN rfl hax9N hop5N hleafN hwalk9N hwalkAN
    CN.compiledBy h31N

/-- **`complJ9A_N_figure`: the completeness figure at the natural-number-typed jet run, with no hypothesis.**
For the run of `complJ9A_closed_of_N`, the error bound `ε_c` is below `2^-120` and some coin `χ` is accepted by
`AcceptsJ9A`. -/
theorem complJ9A_N_figure :
    BN.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BN.Pb RgN.R
        (ComplJ8.cJ sN fJ rN) χ (BN.M χ) (BN.tr χ) BN.rows BN.g :=
  complJ9A_closed_of_N.2.2.2.2 card_KC


/-! ## 8. The negative control: `d : F` is ill-typed at `p+5` -/

/-- The same template with `d : F`. -/
def TF : Tpl := { TN with inTy := ![.F, .F] }

theorem TF_wt (p : ℕ) : TF.WellTyped p := by
  unfold Tpl.WellTyped TF TN Ex.build
  simp only [List.foldr]
  exact HasTy.pair (HasTy.weakN (HasTy.mul (by simpa using HasTy.var (p := p) (inTy := ![.F, .F]) 0)
    (by simpa using HasTy.var (p := p) (inTy := ![.F, .F]) 0)))
    (HasTy.pair (HasTy.weakN (by simpa using HasTy.var (p := p) (inTy := ![.F, .F]) 1)) (HasTy.nil _))

theorem TN_sem : TN.sem pG sN = some rN := jetN_sem

theorem TF_sem_none : TF.sem pG sN = none := by
  cases hs : TF.sem pG sN with
  | none => rfl
  | some r =>
    obtain ⟨a, hs', hok, -⟩ := Nock.Jet.Autogen.sem_eq_some_iff.1 hs
    have h1 := hs' ⟨1, by decide⟩
    have h2 := hok ⟨1, by decide⟩
    simp [TF, TN, sN, Noun.slot] at h1
    have h3 : a ⟨1, by decide⟩ = .atom (pG + 5) := h1.symm
    rw [h3] at h2
    exact absurd h2 (by simp [TF, TN, Nock.Jet.Autogen.shapeOK, pG, Nock.Field.p])

/-- The compiled `d : F` template crashes on the run's subject (at every fuel). -/
theorem TF_crashes : ∀ fuel, evalN fuel sN (compile pG TF) = none :=
  Nock.Jet.Autogen.compile_crash_exact (by decide) TF (TF_wt pG) sN TF_sem_none


end
end Nock.RedTeam.Batch4892

#print axioms Nock.RedTeam.Batch4892.TN_wt
#print axioms Nock.RedTeam.Batch4892.genN
#print axioms Nock.RedTeam.Batch4892.h31N
#print axioms Nock.RedTeam.Batch4892.complJ9A_closed_of_N
#print axioms Nock.RedTeam.Batch4892.complJ9A_N_figure
#print axioms Nock.RedTeam.Batch4892.TN_sem
#print axioms Nock.RedTeam.Batch4892.TF_sem_none
#print axioms Nock.RedTeam.Batch4892.TF_crashes
