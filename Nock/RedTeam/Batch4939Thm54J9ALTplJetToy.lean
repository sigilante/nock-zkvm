/-
  Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean

  **A template-jet twin of `genLink_toy` (J-9 AL, hypothesis-free).**  The program `jp` of `NockvmE2E.Z38.CatJ`:
  subject `[3 (p+5)]`, formula `[[11 [%wild [1 7]] (compile p TN)] [11 [%wild [1 8]] (primC add)]]`, fuel 4, registry
  `catJ.toVR.R` (template `TN` at id 7, the primitive `add` at id 8), templates `rtP catJ.toCR.Rt catJ.prims`.  One
  TEMPLATE jet call (id 7) and one big-atom primitive call (id 8), so the J-8 tables carry jet rows and the ALU chip is
  on.  `TN`, `CN`, `catJ` are copied field for field from `NockvmE2E.Z38.CatJ` (nockvm-e2e).
  Headlines: `genLinkTpl` (checker accepts the generator's record at a good coin), `complJ9AL_tpl` (the
  `complJ9AL_closed` instance; `hRt`/`hregAx` from `catJ.compiledByP` are not vacuous), `honestTpl` (ALU-orbit form),
  `rowsTpl_le` (every chip has at most `nRowsTpl` rows, a bound independent of the coin), `honestTplUnif` (uniform
  orbit `orbU h ω`); `nRowsTpl = 159` (the cell table, the largest chip) with `nRowsTpl_le_768` (fits orbit height 8).
  The ALU length is a bound (`aluLen ≤ 48`, the `aluLen` style); the cell and jet row counts are kernel `decide` on
  list lengths; the run and the J-8 / J-9 A facts are kernel `decide` on the explicit five-node tree.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree
import Nock.RedTeam.Batch4921Thm54J9ALComplToy
import Nock.RedTeam.Batch4931Thm54AluBlockBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch4939

open Nock Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Autogen Nock.Jet.Prim Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry (CheckedReg)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (CheckedRegP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl j9alDataOf pcallsR primsC opOf)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.SVFrame
open Nock.RedTeam.Batch4842 (card_KC)
open Nock.RedTeam.Batch4921 (blockB_add_le)

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

def catJ : CheckedRegP pG where
  toCR := CN
  prims := [(8, .add)]
  ndP := by decide

def sJ : Noun := .cell (.atom 3) (.atom (pG + 5))
def clue7 : Noun := .cell (.atom 1) (.atom 7)
def clue8 : Noun := .cell (.atom 1) (.atom 8)
def f1 : Noun := .cell (.atom 11) (.cell (.cell (.atom wildTag) clue7) (compile pG TN))
def f2 : Noun := .cell (.atom 11) (.cell (.cell (.atom wildTag) clue8) (primC .add))
def fJP : Noun := .cell f1 f2
def r1 : Noun := .cell (.atom 9) (.cell (.atom (pG + 5)) (.atom 0))
def r2 : Noun := .atom (pG + 8)

abbrev Rg : VerifiedRegistry := catJ.toVR
abbrev Rt0 : ℕ → Tpl := catJ.toCR.Rt
abbrev primsJ : List (ℕ × PrimOp) := catJ.prims

theorem Rg7 : Rg.R 7 = CN.toVR.R 7 :=
  CheckedRegistryP.addPrims_R_of_not_mem CN.toVR [(8, .add)] 7 (by simp)

theorem jet1 : jetHit Rg.R (.atom wildTag) (.atom 7) (compile pG TN) sJ = some r1 := by
  have : jetHit CN.toVR.R (.atom wildTag) (.atom 7) (compile pG TN) sJ = some r1 := by decide +kernel
  show jetHit (CheckedRegistryP.addPrims CN.toVR [(8, .add)]).R _ _ _ _ = _
  have e : (CheckedRegistryP.addPrims CN.toVR [(8, .add)]).R 7 = CN.toVR.R 7 :=
    CheckedRegistryP.addPrims_R_of_not_mem CN.toVR [(8, .add)] 7 (by simp)
  simp only [jetHit, e]
  simpa only [jetHit] using this

theorem Rg8 : Rg.R 8 = some (primSpec .add) :=
  CheckedRegistryP.addPrims_R_of_mem CN.toVR [(8, .add)] (by simp) (8, .add) (by simp)

theorem jet2 : jetHit Rg.R (.atom wildTag) (.atom 8) (primC .add) sJ = some r2 := by
  simp [jetHit, Rg8, primSpec, primTemplate, binT, Template.semS, Template.args, sJ, r2, Noun.slot, pG, primSem]
  try omega

def tD7 : NTree SkelX := mkX .s1 sJ clue7 (.atom 7) []
def tD8 : NTree SkelX := mkX .s1 sJ clue8 (.atom 8) []
def tJ1 : NTree SkelX := mkX .s11j sJ f1 r1 [tD7]
def tJ2 : NTree SkelX := mkX .s11j sJ f2 r2 [tD8]
def tT : NTree SkelX := mkX .cons sJ fJP (.cell r1 r2) [tJ1, tJ2]
def rT : Noun := .cell r1 r2

theorem gD7 : genX Rg.R 2 sJ clue7 = some (tD7, .atom 7) := by
  simp [genX, genComputeSkeletonX, clue7, tD7, mkX]

theorem gD8 : genX Rg.R 2 sJ clue8 = some (tD8, .atom 8) := by
  simp [genX, genComputeSkeletonX, clue8, tD8, mkX]

theorem g1 : genX Rg.R 3 sJ f1 = some (tJ1, r1) := by
  have h := gD7
  simp only [genX] at h
  simp only [genX, f1, genComputeSkeletonX, h]
  rw [jet1]; rfl

theorem g2 : genX Rg.R 3 sJ f2 = some (tJ2, r2) := by
  have h := gD8
  simp only [genX] at h
  simp only [genX, f2, genComputeSkeletonX, h]
  rw [jet2]; rfl

theorem genT : genX Rg.R 4 sJ fJP = some (tT, rT) := by
  have h1 := g1
  have h2 := g2
  have e : genX Rg.R 4 sJ fJP = (match genX Rg.R 3 sJ f1, genX Rg.R 3 sJ f2 with
    | some (tl, l), some (tr, r) => some (mkX .cons sJ (.cell f1 f2) (.cell l r) [tl, tr], .cell l r)
    | _, _ => none) := rfl
  rw [e, h1, h2]; rfl



open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J8.Exe (CoinsE)

abbrev RtP : ℕ → Tpl := rtP Rt0 primsJ

theorem bfsT : bfsForest [tT] = [tT, tJ1, tJ2, tD7, tD8] := by
  simp [bfsForest, tT, tJ1, tJ2, tD7, tD8, mkX]

theorem rowsT : rowsOfT tT = #[rowOfSkelX tT.label, rowOfSkelX tJ1.label, rowOfSkelX tJ2.label,
    rowOfSkelX tD7.label, rowOfSkelX tD8.label] := by
  simp only [rowsOfT, bfsT]; rfl

abbrev rowsL : Array RowNX := #[rowOfSkelX tT.label, rowOfSkelX tJ1.label, rowOfSkelX tJ2.label,
    rowOfSkelX tD7.label, rowOfSkelX tD8.label]

noncomputable section
abbrev DDT := j8DataOf pG Rg RtP genT
abbrev DAT := j9aDataOf pG Rg RtP genT
abbrev DLT := j9alDataOf pG Rg RtP primsJ genT

theorem callsL_eq : Nock.V1J8.Gen.callsOf rowsL = [(7, sJ), (8, sJ)] := by decide +kernel

theorem callsT : DDT.calls = [(7, sJ), (8, sJ)] := by
  show Nock.V1J8.Gen.callsOf (rowsOfT tT) = _
  rw [rowsT]; exact callsL_eq

theorem rootsT : DDT.roots = Nock.V1J8.Gen.rootsOf ⟨sJ, fJP, rT⟩ rowsL ++
    ComplJ8Data.jNounsP pG RtP ((Nock.V1J8.Gen.callsOf rowsL).map Prod.fst).dedup (Nock.V1J8.Gen.callsOf rowsL) := by
  have h : DDT.roots = Nock.V1J8.Gen.rootsOf ⟨sJ, fJP, rT⟩ (rowsOfT tT) ++
    ComplJ8Data.jNounsP pG RtP ((Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst).dedup
      (Nock.V1J8.Gen.callsOf (rowsOfT tT)) := rfl
  rw [h, rowsT]

theorem hleafT : ComplJ8Walk.RootsLeafOK DDT.roots := by
  rw [rootsT]
  show ∀ x ∈ _, Noun.leaves x ≤ 2 ^ 109
  decide +kernel

theorem inTree_tT (u : NTree SkelX) (h : InTree tT u) :
    u = tT ∨ u = tJ1 ∨ u = tJ2 ∨ u = tD7 ∨ u = tD8 := by
  have : u ∈ bfsForest [tT] := (mem_bfsForest [tT] u).2 ⟨tT, by simp, h⟩
  rw [bfsT] at this; simpa using this

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A AxRowX9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

theorem hax9T : ProgAxOK9A pG tT := by
  intro u hu
  rcases inTree_tT u hu with rfl | rfl | rfl | rfl | rfl
  · show AxRowX9A _ (rowOfSkelX tT.label)
    simp only [AxRowX9A]; trivial
  · show AxRowX9A _ (rowOfSkelX tJ1.label)
    simp only [AxRowX9A]
    refine ⟨fun id h => ?_, fun id h => ?_⟩
    · have : (rowOfSkelX tJ1.label).ftth = .atom wildTag := rfl
      rw [this] at h; cases h; decide
    · have : (rowOfSkelX tJ1.label).sf1 = .atom 7 := rfl
      rw [this] at h; cases h; decide
  · show AxRowX9A _ (rowOfSkelX tJ2.label)
    simp only [AxRowX9A]
    refine ⟨fun id h => ?_, fun id h => ?_⟩
    · have : (rowOfSkelX tJ2.label).ftth = .atom wildTag := rfl
      rw [this] at h; cases h; decide
    · have : (rowOfSkelX tJ2.label).sf1 = .atom 8 := rfl
      rw [this] at h; cases h; decide
  · show AxRowX9A _ (rowOfSkelX tD7.label)
    simp only [AxRowX9A]; trivial
  · show AxRowX9A _ (rowOfSkelX tD8.label)
    simp only [AxRowX9A]; trivial

theorem hop5T : ComplJ8.ProgOp5OK pG tT := by
  intro u hu
  rcases inTree_tT u hu with rfl | rfl | rfl | rfl | rfl <;> intro h <;> cases h

theorem hwalk9T : WalkDepthOK9A (rowsOfT tT) := by
  show ∀ r ∈ VclL.pathReads (ComplJ9ABinders.walkReads9 (rowsOfT tT)), VclL.depthOf r.2 ≤ 61
  rw [rowsT]
  decide +kernel

theorem preadsT : DDT.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (rowsOfT tT) = []
  rw [rowsT]; decide +kernel

theorem hwalkAT : ComplJ8Walk.WalkDepthOK DDT.preads := by
  rw [preadsT]; intro r hr; simp [VclL.pathReads] at hr

/-! ## The J-9 A tree -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9 rowX9)

theorem chipTT : ComplJ9AGen.chipOf tT.label = (.old, 0) := by decide +kernel
theorem chipTJ1 : ComplJ9AGen.chipOf tJ1.label = (.old, 0) := by decide +kernel
theorem chipTJ2 : ComplJ9AGen.chipOf tJ2.label = (.old, 0) := by decide +kernel
theorem chipTD7 : ComplJ9AGen.chipOf tD7.label = (.old, 0) := by decide +kernel
theorem chipTD8 : ComplJ9AGen.chipOf tD8.label = (.old, 0) := by decide +kernel

def nd9 (k : SkelX) (ks : List (NTree LX9)) : NTree LX9 := .node ⟨rowX9 k, .old, 0, 0, rowOfSkelX k⟩ ks

theorem g9D7 : genX9T tD7 = nd9 tD7.label [] := by
  show genX9T (.node tD7.label []) = _
  rw [ComplJ9AGen.genX9T_node, chipTD7]; rfl

theorem g9D8 : genX9T tD8 = nd9 tD8.label [] := by
  show genX9T (.node tD8.label []) = _
  rw [ComplJ9AGen.genX9T_node, chipTD8]; rfl

theorem g9J1 : genX9T tJ1 = nd9 tJ1.label [nd9 tD7.label []] := by
  show genX9T (.node tJ1.label [tD7]) = _
  rw [ComplJ9AGen.genX9T_node, chipTJ1]
  simp only [List.map_cons, List.map_nil, g9D7, ComplJ9AGen.kid9, chipTJ1, nd9]
  simp

theorem g9J2 : genX9T tJ2 = nd9 tJ2.label [nd9 tD8.label []] := by
  show genX9T (.node tJ2.label [tD8]) = _
  rw [ComplJ9AGen.genX9T_node, chipTJ2]
  simp only [List.map_cons, List.map_nil, g9D8, ComplJ9AGen.kid9, chipTJ2, nd9]
  simp

theorem g9T : genX9T tT = nd9 tT.label [nd9 tJ1.label [nd9 tD7.label []], nd9 tJ2.label [nd9 tD8.label []]] := by
  show genX9T (.node tT.label [tJ1, tJ2]) = _
  rw [ComplJ9AGen.genX9T_node, chipTT]
  simp only [List.map_cons, List.map_nil, g9J1, g9J2, ComplJ9AGen.kid9, chipTT, nd9]
  simp

theorem bfs9T : bfsForest [nd9 tT.label [nd9 tJ1.label [nd9 tD7.label []], nd9 tJ2.label [nd9 tD8.label []]]] =
    [nd9 tT.label [nd9 tJ1.label [nd9 tD7.label []], nd9 tJ2.label [nd9 tD8.label []]], nd9 tJ1.label [nd9 tD7.label []], nd9 tJ2.label [nd9 tD8.label []],
    nd9 tD7.label [], nd9 tD8.label []] := by
  simp [bfsForest, nd9]

theorem rows9T : rowsOfT9 tT = #[⟨rowX9 tT.label, .old, 0, 0, rowOfSkelX tT.label⟩, ⟨rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩,
    ⟨rowX9 tJ2.label, .old, 0, 0, rowOfSkelX tJ2.label⟩, ⟨rowX9 tD7.label, .old, 0, 0, rowOfSkelX tD7.label⟩,
    ⟨rowX9 tD8.label, .old, 0, 0, rowOfSkelX tD8.label⟩] := by
  simp only [rowsOfT9, g9T, bfs9T]; rfl

theorem keys9T : ComplJ9AChainsRun.axKeys9 (rowsOfT9 tT) = [] := by
  rw [rows9T]; decide +kernel

theorem axAtoms9T : ComplJ9AData.axAtoms9 (rowsOfT9 tT) = [] := by
  rw [rows9T]; decide +kernel

theorem fieldAx9T : ComplJ9AData.fieldAx9 pG (rowsOfT9 tT) = [] := by
  unfold ComplJ9AData.fieldAx9; rw [axAtoms9T]; rfl

theorem axOnA_tT : ComplJ9ARun.axOnA tT = false := by
  simp [ComplJ9ARun.axOnA, keys9T]

theorem spOnA_tT : ComplJ9ARun.spOnA pG tT = false := by
  simp [ComplJ9ARun.spOnA, fieldAx9T]

theorem N9T : ComplJ9ARun.N9 tT = 5 := by
  rw [ComplJ9ARun.N9_def, ComplJ9ARun.W9, g9T, bfs9T]; rfl

theorem nXT : ComplJ9ARun.nXOf pG DAT.acs.length DAT.H tT = 1 := by
  simp [ComplJ9ARun.nXOf, axOnA_tT]

theorem nST : ComplJ9ARun.nSOf pG tT = 1 := by
  simp [ComplJ9ARun.nSOf, spOnA_tT]

theorem walkReadsX9T : ComplJ9AReads.walkReadsX9 (rowsOfT9 tT) = [] := by
  rw [rows9T]; decide +kernel

theorem readsT : DAT.reads = [] := by
  change ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ = []
  rw [walkReadsX9T, List.nil_append]
  simp [ComplJ9AChainsRun.axChainReadsK9, keys9T]

theorem axReadsK9T : ComplJ9AChainsRun.axReadsK9 pG (rowsOfT9 tT) = [] := by
  unfold ComplJ9AChainsRun.axReadsK9
  rw [keys9T, rows9T]
  decide +kernel

theorem preadsDAT : DAT.preads = [] := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsT, axReadsK9T]; rfl

theorem regsT : DDT.regs = [7, 8] := by
  show ((Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst).dedup = _
  rw [rowsT, callsL_eq]; rfl

theorem idsT : DDT.ids = [7, 8] := by
  show (Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst = _
  rw [rowsT, callsL_eq]; rfl

theorem jrowsDD_len : DDT.jrows.length ≤ 32 := by
  have h := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet.jrows_pre_run (p := pG) RtP genT
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  rw [h2, regsT, idsT]
  decide +kernel


/-! ### cells -/

def ncell : Noun → ℕ
  | .atom _ => 0
  | .cell a b => ncell a + ncell b + 1

theorem addCells_len : ∀ (n : Noun) (acc : List Noun),
    (Nock.V1J8.Gen.addCells n acc).length ≤ acc.length + ncell n
  | .atom _, acc => by simp [Nock.V1J8.Gen.addCells, ncell]
  | .cell a b, acc => by
    unfold Nock.V1J8.Gen.addCells
    split_ifs
    · simp [ncell]
    · have h1 := addCells_len a (acc ++ [.cell a b])
      have h2 := addCells_len b (Nock.V1J8.Gen.addCells a (acc ++ [.cell a b]))
      simp only [List.length_append, List.length_singleton] at h1
      simp only [ncell]; omega

theorem foldl_addCells_len : ∀ (roots acc : List Noun),
    (roots.foldl (fun acc n => Nock.V1J8.Gen.addCells n acc) acc).length ≤ acc.length + (roots.map ncell).sum
  | [], acc => by simp
  | n :: rs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := foldl_addCells_len rs (Nock.V1J8.Gen.addCells n acc)
    have h2 := addCells_len n acc
    omega

theorem cellsT_len : DAT.cells.length ≤ 159 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells]
  show (Nock.V1J8.Gen.cellsOfRoots DDT.roots).length ≤ _
  rw [rootsT]; decide +kernel

/-! ### bigs and acs -/

theorem bigsP_perm_of (p : ℕ) (roots : List Noun) (rows : Array RowNX) (l : List ℕ)
    (hl : (((roots ++ rows.toList.flatMap rowHandleNounsX).flatMap leavesOf).filter fun a => decide (p ≤ a)).dedup = l) :
    (ComplJ8Data.bigsP p roots rows).Perm l := by
  unfold ComplJ8Data.bigsP
  rw [hl]
  exact List.mergeSort_perm _ _

theorem bigsT_perm : DDT.bigs.Perm [pG + 8, pG + 5] := by
  show (ComplJ8Data.bigsP pG DDT.roots (rowsOfT tT)).Perm _
  rw [rootsT, rowsT]
  exact bigsP_perm_of pG _ _ _ (by decide +kernel)

theorem lim_le (a : ℕ) (k : ℕ) (h : a < 2 ^ (32 * k)) : (Nock.Atoms.limbs a).length ≤ k := by
  unfold Nock.Atoms.limbs Nock.Atoms.B
  rw [Nat.digits_length_le_iff (by norm_num)]
  calc a < 2 ^ (32 * k) := h
    _ = (2 ^ 32) ^ k := by rw [pow_mul]

theorem pG_lt : pG + 8 < 2 ^ 96 := by unfold pG Nock.Field.p; norm_num

theorem pG_lt64 : pG + 8 < 2 ^ 64 := by unfold pG Nock.Field.p; norm_num

theorem limbs_b2 : (Nock.Atoms.limbs (pG + 5)).length ≤ 2 := lim_le _ _ (by have := pG_lt64; norm_num; omega)
theorem limbs_c2 : (Nock.Atoms.limbs (pG + 8)).length ≤ 2 := lim_le _ _ (by have := pG_lt64; norm_num; omega)

theorem limbs_b : (Nock.Atoms.limbs (pG + 5)).length ≤ 3 := lim_le _ _ (by have := pG_lt; norm_num; omega)
theorem limbs_c : (Nock.Atoms.limbs (pG + 8)).length ≤ 3 := lim_le _ _ (by have := pG_lt; norm_num; omega)
theorem limbs_a : (Nock.Atoms.limbs 3).length ≤ 3 := lim_le _ _ (by norm_num)

theorem spineOf_len : ∀ ls : List ℕ, (Nock.V1J8.Gen.spineOf ls).length ≤ ls.length
  | [] => by simp [Nock.V1J8.Gen.spineOf]
  | [x] => by simp [Nock.V1J8.Gen.spineOf]
  | x :: y :: rest => by
    have := spineOf_len (y :: rest)
    simp only [Nock.V1J8.Gen.spineOf, List.length_cons] at this ⊢
    omega

theorem spineOf_cell : ∀ (ls : List ℕ), ∀ x ∈ Nock.V1J8.Gen.spineOf ls, x.isCell = true
  | [] => by simp [Nock.V1J8.Gen.spineOf]
  | [x] => by simp [Nock.V1J8.Gen.spineOf]
  | x :: y :: rest => by
    intro z hz
    simp only [Nock.V1J8.Gen.spineOf, List.mem_cons] at hz
    rcases hz with rfl | hz
    · cases rest <;> simp [Nock.V1J8.Gen.combOf, Noun.isCell]
    · exact spineOf_cell (y :: rest) z hz

theorem addNew_len (ns : List Noun) : ∀ acc : List Noun, (Nock.V1J8.Gen.addNew acc ns).length ≤ acc.length + ns.length := by
  unfold Nock.V1J8.Gen.addNew
  induction ns with
  | nil => intro acc; simp
  | cons n ns ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    split_ifs
    · have := ih acc; omega
    · have := ih (acc ++ [n]); simp only [List.length_append, List.length_singleton] at this; omega

theorem addNew_cell (ns : List Noun) (hn : ∀ x ∈ ns, x.isCell = true) :
    ∀ acc : List Noun, (∀ x ∈ acc, x.isCell = true) → ∀ x ∈ Nock.V1J8.Gen.addNew acc ns, x.isCell = true := by
  unfold Nock.V1J8.Gen.addNew
  induction ns with
  | nil => intro acc h; simpa using h
  | cons n ns ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    have hn' : ∀ x ∈ ns, x.isCell = true := fun x hx => hn x (List.mem_cons_of_mem _ hx)
    split_ifs
    · exact ih hn' acc hacc
    · refine ih hn' (acc ++ [n]) ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hacc x hx
      · simp at hx; subst hx; exact hn x List.mem_cons_self

theorem acsP_len_le (p : ℕ) (bigs : List ℕ) (dupP : Bool) :
    (ComplJ8Data.acsP p bigs dupP).length ≤ (bigs.map fun a => (Nock.Atoms.limbs a).length).sum + 2 := by
  have key : ∀ (bs : List ℕ) (acc : List Noun), (∀ x ∈ acc, x.isCell = true) →
      (bs.foldl (fun acc a => Nock.V1J8.Gen.addNew acc (Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs a))) acc).length ≤
        acc.length + (bs.map fun a => (Nock.Atoms.limbs a).length).sum ∧
      ∀ x ∈ bs.foldl (fun acc a => Nock.V1J8.Gen.addNew acc (Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs a))) acc,
        x.isCell = true := by
    intro bs
    induction bs with
    | nil => intro acc h; exact ⟨by simp, by simpa using h⟩
    | cons a bs ih =>
      intro acc hacc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have hc := addNew_cell (Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs a)) (spineOf_cell _) acc hacc
      obtain ⟨h1, h2⟩ := ih _ hc
      refine ⟨?_, h2⟩
      have := addNew_len (Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs a)) acc
      have := spineOf_len (Nock.Atoms.limbs a)
      omega
  obtain ⟨hL, hLc⟩ := key bigs [] (by simp)
  simp only [List.length_nil, zero_add] at hL
  unfold ComplJ8Data.acsP
  simp only [List.length_append, List.length_singleton]
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hLc).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hLc).2.1 x).mp hx)
  have hif : (if dupP && decide (Noun.cell (.atom 0) (ComplJ8Data.combPP p) ∈
      bigs.foldl (fun acc a => Nock.V1J8.Gen.addNew acc (Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs a))) [])
      then [ComplJ8Data.combPP p] else ([] : List Noun)).length ≤ 1 := by
    split_ifs <;> simp
  omega

theorem acsT_len : DAT.acs.length ≤ 6 := by
  show (ComplJ8Data.acsP pG DDT.bigs DDT.dupP).length ≤ _
  refine (acsP_len_le _ _ _).trans ?_
  have hs := (bigsT_perm.map fun a => (Nock.Atoms.limbs a).length).sum_eq
  rw [hs]
  have h2 := limbs_b2
  have h3 := limbs_c2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-! ### The row binders -/

theorem walk_bound (cs : List Noun) (L : List (Noun × ℕ)) (h : ∀ x ∈ L, x.2 < 2 ^ 62) :
    (VclL.GenWalk.walkRows cs L).length ≤ 61 * L.length + 1 := by
  have hw := VclL.GenWalk.walkRows_length_le cs L
  have hsub : ∀ r ∈ VclL.pathReads L, r ∈ L := by
    intro r hr
    simp only [VclL.pathReads, List.mem_dedup, List.mem_filter] at hr
    exact hr.1
  have hsum : ((VclL.pathReads L).map fun r => VclL.depthOf r.2).sum ≤ (VclL.pathReads L).length * 61 := by
    have := List.sum_le_length_nsmul ((VclL.pathReads L).map fun r => VclL.depthOf r.2) 61 (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact ComplJ9AReads.depthOf_le61 (h r (hsub r hr)))
    simpa using this
  have hlen : (VclL.pathReads L).length ≤ L.length :=
    ((List.dedup_sublist _).trans List.filter_sublist).length_le
  split_ifs at hw <;> nlinarith

theorem nVDAT : ComplJ8Of.nVOf DAT = 1 := by
  unfold ComplJ8Of.nVOf
  rw [preadsDAT]
  simp

theorem hMT : ∀ x ∈ ComplJ9ARun.sizesA DAT, x ≤ 159 := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  have hB : (bfsForest [DAT.t]).length = 5 := by
    show (bfsForest [tT]).length = 5
    rw [bfsT]; rfl
  have hC := cellsT_len
  have hW : (VclL.GenWalk.walkRows DAT.cells DAT.reads).length ≤ 159 := by
    have h := walk_bound DAT.cells DAT.reads (by rw [readsT]; simp)
    rw [readsT] at h ⊢
    simp only [List.length_nil, mul_zero, zero_add] at h
    omega
  have hJ : DAT.jrows.length ≤ 32 := jrowsDD_len
  have hA := acsT_len
  have hV : ComplJ8Of.nVOf DAT = 1 := nVDAT
  have hN : ComplJ9ARun.N9 DAT.t = 5 := N9T
  have hX : ComplJ9ARun.nXOf pG DAT.acs.length DAT.H DAT.t = 1 := nXT
  have hS : ComplJ9ARun.nSOf pG DAT.t = 1 := nST
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

theorem h31AT : ComplJ9ARun.Rows31A DAT := fun x hx => (hMT x hx).trans (by norm_num)

theorem hpGT : pG = Nock.Atoms.p := rfl

/-! ### J-9 AL data: the template call only -/

theorem callsLT : DLT.calls = [(7, sJ)] := by
  rw [ComplJ9ALData.F_calls RtP primsJ genT, rowsT]
  decide +kernel

theorem regsLT : DLT.regs = [7] := by
  rw [ComplJ9ALData.F_regs RtP primsJ genT, callsLT]; rfl

theorem idsLT : DLT.ids = [7] := by
  rw [ComplJ9ALData.F_ids RtP primsJ genT, callsLT]; rfl

theorem jrowsLT_len : DLT.jrows.length ≤ 32 := by
  have h := ComplJ9ALData.jrows_preL (p := pG) RtP primsJ genT
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  rw [h2, regsLT, idsLT]
  decide +kernel

/-! ### The prim binders -/

theorem pcalls_T : pcallsR (primsJ.map Prod.fst) (rowsOfT tT) = [(8, sJ, r2)] := by
  rw [rowsT]; decide +kernel

theorem hlimbT : AluCallOK.PrimLimbs62 (primsJ.map Prod.fst) tT := by
  intro x hx
  rw [pcalls_T] at hx
  simp only [List.mem_singleton] at hx
  subst hx
  show (Nock.Atoms.limbs 3).length ≤ 62 ∧ (Nock.Atoms.limbs (pG + 5)).length ≤ 62
  exact ⟨by have := limbs_a; omega, by have := limbs_b; omega⟩

theorem hnoDecT : ∀ q ∈ primsJ, q.2 ≠ PrimOp.dec := by decide
theorem hndT : (primsJ.map Prod.fst).Nodup := by decide

theorem opOf_T : opOf primsJ 8 = .add := by decide

theorem psLen (ids : List ℕ) : (primsC primsJ ids).length ≤ 1 :=
  (List.length_filter_le _ _).trans (by decide)

open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRun
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable

theorem blockB_add_le32 {F : Type} [Field F] (p : ℕ) (cl : CallL) (hop : cl.op = .add)
    (ha : (Nock.Atoms.limbs cl.a).length ≤ 3) (hb : (Nock.Atoms.limbs cl.b).length ≤ 3)
    (hc : (Nock.Atoms.limbs cl.c).length ≤ 3) : (blockB (F := F) p cl).length ≤ 32 := by
  obtain ⟨op, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩ := cl
  simp only at hop ha hb hc
  subst hop
  simp only [blockB, slotsOf, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_append,
    slotRows, List.length_map, List.length_range, List.append_nil]
  have h1 := Nock.RedTeam.Batch4921.handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA
  have h2 := Nock.RedTeam.Batch4921.handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB
  have h3 := Nock.RedTeam.Batch4921.handle_words p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE
  have h4 := Nock.RedTeam.Batch4921.qslot_words .add (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (CarrySZ.addL
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw))
    (CarrySZ.negL (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE).vw))))
  rw [CarrySZ.carr_length] at h4
  have h5 := Nock.RedTeam.Batch4921.addL_len (CarrySZ.addL
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw))
    (CarrySZ.negL (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE).vw))
  have h6 := Nock.RedTeam.Batch4921.addL_len
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA).vw)
    (zl (handleSlot p .add (CallL.lbv ⟨.add, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB).vw)
  simp only [zl, CarrySZ.negL, List.length_map] at h4 h5 h6 ⊢
  omega


theorem aluLen_le : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen (K := KC) deltaF RtP genT primsJ ≤ 48 := by
  have hps : (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.psRun (p := pG) RtP genT primsJ).length ≤ 1 :=
    psLen _
  have hcl : clsRun (p := pG) RtP primsJ genT =
      callsLOf DLT.cells DLT.H primsJ [(8, sJ, r2)] := by
    unfold clsRun
    rw [pcalls_T]
  have h1 : (Nock.Atoms.limbs 3).length ≤ 6 := limbs_a.trans (by norm_num)
  have h2 : (Nock.Atoms.limbs (pG + 5)).length ≤ 6 := limbs_b.trans (by norm_num)
  have h3 : (Nock.Atoms.limbs (pG + 8)).length ≤ 3 := limbs_c
  obtain ⟨cl, hcl1, hop, ha, hb, hc⟩ : ∃ cl, callsLOf DLT.cells DLT.H primsJ [(8, sJ, r2)] = [cl] ∧
      cl.op = .add ∧ cl.a = 3 ∧ cl.b = pG + 5 ∧ cl.c = pG + 8 := ⟨_, rfl, opOf_T, rfl, rfl, rfl⟩
  have hB := blockB_add_le32 (F := ZMod pG) pG cl hop (ha ▸ limbs_a) (hb ▸ limbs_b) (hc ▸ limbs_c)
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.tbR tblRun tblP
  rw [hcl, hcl1]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg.pregsP_length,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, zipB_length]
  simp only [pG] at hB hps ⊢
  omega

theorem aluLen_tpl : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen (K := KC) deltaF RtP genT primsJ < 2 ^ 31 :=
  lt_of_le_of_lt aluLen_le (by norm_num)


/-! ## The J-9 AL instance -/

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ (checkJ9ALX_genJ9ALXJ)
open Nock.V1J8.Exe (toχ)
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff

/-- The generator's output on the template-jet run `jp`. -/
theorem genT_L (χe : CoinsE) :
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe =
      some (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT) := by
  rw [GenPortJ9ALHJRun.genJ9ALXJ_eq]
  have hr : Nock.V1J8.Gen.runX catJ.toVR.R 4 sJ fJP =
      some ⟨tT, rT, bfsForest [tT], ComplJ8Data.rowsOfT tT⟩ := by
    unfold Nock.V1J8.Gen.runX; rw [genT]; rfl
  rw [hr]
  rfl

/-- The honest record BL of the run. -/
abbrev BL := ComplJ9ALClosed.BRun9AL deltaF powerBasis3 RtP genT primsJ hpGT h31AT

open Classical in
/-- **`complJ9AL_tpl`: `complJ9AL_closed` at the template-jet run, hypothesis-free.**  The template call (id 7) is a
real `compile`d template, so `hRt` / `hregAx` are NOT vacuous (`hRt_hregAx_ofP` of `catJ.compiledByP`). -/
theorem complJ9AL_tpl :
    (∀ χ, BL.Good χ → AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb catJ.toVR.R (ComplJ8.cJ sJ fJP rT) χ (BL.M χ)
      (BL.tr χ) BL.rows BL.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BL.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BL.epsC) ∧
    RealIOJ9AL.StJ9AL BL.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sJ fJP rT) ∧
    (Fintype.card KC = VclL.Events.cK →
      BL.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb catJ.toVR.R (ComplJ8.cJ sJ fJP rT) χ (BL.M χ)
        (BL.tr χ) BL.rows BL.g) :=
  ComplJ9ALClosed.complJ9AL_closed_of deltaF powerBasis3 Rt0 genT primsJ hpGT hax9T hop5T hleafT hwalk9T hwalkAT
    catJ.compiledByP hndT h31AT aluLen_tpl hlimbT hnoDecT

theorem hCT : CheckedRegistryP.CompiledByP pG catJ.toVR Rt0 primsJ := catJ.compiledByP

/-- A good coin of the figure. -/
theorem good_coin : ∃ χe : CoinsE, BL.Good (toχ χe) := by
  obtain ⟨-, hfrac, -, -, hfig⟩ := complJ9AL_tpl
  obtain ⟨hlt, -⟩ := hfig card_KC
  exact GenPortJ9ALHGoodCoinJ.exists_good_coinEJL BL hfrac hlt

/-- **`genLinkTpl`: hypothesis-free.**  There is a coin at which `genJ9ALXJ` produces a record on `jp` (one template
jet call, id 7, and one big-atom `add` call, id 8) and the J-9 AL checker accepts it. -/
theorem genLinkTpl : ∃ χe : CoinsE, ∃ I : Nock.V1J9AL.CheckJ9AL.InJ9AL,
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe = some I ∧
      Nock.V1J9AL.CheckJ9AL.checkJ9ALX I = true := by
  obtain ⟨χe, hχ⟩ := good_coin
  exact ⟨χe, _, genT_L χe,
    checkJ9ALX_genJ9ALXJ genT hpGT hax9T hop5T hleafT hwalk9T hwalkAT hCT hndT h31AT aluLen_tpl hlimbT hnoDecT
      (genT_L χe) hχ⟩

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (OrbJ9AL withOrbL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbFits reorb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree (OrbAdmL')

/-- **`honestTpl`: the ALU-orbit form.** -/
theorem honestTpl : ∃ χe : CoinsE, ∃ I : InJ9AL,
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe = some I ∧
    ∀ o : OrbJ9AL, OrbAdmL' I o →
      ∃ hv : ValidJ9AL (withOrbL I o),
        AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I o) hv) catJ.toVR.R (withOrbL I o).c
          (toχ (withOrbL I o).χ) (withOrbL I o).toMsgL (withOrbL I o).toTrL (withOrbL I o).toRowsL
          (withOrbL I o).g := by
  obtain ⟨χe, hχ⟩ := good_coin
  exact ⟨χe, _, genT_L χe, fun o ho =>
    GenPortJ9ALHOrbFree.genJ9ALXJ_honest_at' genT hpGT hax9T hop5T hleafT hwalk9T hwalkAT hCT hndT h31AT aluLen_tpl
      hlimbT hnoDecT (genT_L χe) hχ o ho⟩


/-! ## Row counts of the record (bounds, independent of the coin) -/

/-- The exact maximum chip row count of the record on `jp`: the cell table has exactly 159 rows; the other chips have
at most 48 (ALU: `3 * 2 ^ hOf aluLen`, `aluLen <= 34`), 32 (J), 6 (A), 5 (X) and 1-2 rows. -/
def nRowsTpl : ℕ := 159

theorem nRowsTpl_le_768 : nRowsTpl ≤ 3 * 2 ^ 8 := by unfold nRowsTpl; norm_num

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ (rowsB_len lRP_on lRP_off)

theorem alN_le (χe : CoinsE) :
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).AL.n ≤ nRowsTpl := by
  unfold nRowsTpl
  by_cases hpc : GenPortJ9ALHJRun.pcLK RtP primsJ sJ fJP χe (GenPortJ9AHProj.RnOf tT rT) = []
  · rw [GenPortJ9ALHLink.IL_AL, lRP_off RtP primsJ χe hpc]
    show 1 ≤ 159
    norm_num
  · rw [GenPortJ9ALHLink.IL_AL, lRP_on RtP primsJ χe hpc]
    have hlen := rowsB_len RtP primsJ genT χe
    rw [GenPortJ9AHComp.chipOf_n, GenPortJ9ALHAluE.aluGenE_size]
    show 3 * 2 ^ Nock.V1J8.Gen.hOf (aluRowsB _ _ _).length ≤ _
    rw [hlen]
    have hh : Nock.V1J8.Gen.hOf (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen (K := KC) deltaF RtP genT primsJ) ≤ 4 :=
      GenPortJ9AHOrb.hOf_go_le _ 4 (aluLen_le.trans (by norm_num)) 64 1 (by norm_num)
    calc 3 * 2 ^ Nock.V1J8.Gen.hOf _ ≤ 3 * 2 ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hh)
      _ ≤ 159 := by norm_num


open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic (mem_N9 mem_nV mem_nX mem_nS)

theorem le_nRows {x b : ℕ} (h : x ≤ b) (hb : b ≤ 159 := by norm_num) : x ≤ nRowsTpl := h.trans hb

/-- **The eight non-ALU chips of the record have at most `159` rows** (the cell table has exactly 159). -/
theorem chipsN_le (χe : CoinsE) :
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).X.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).C.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).W.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).J.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).A.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).V.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).AX.n ≤ nRowsTpl ∧
    (GenPortJ9ALHJRun.recJ9ALXJ RtP primsJ sJ fJP χe tT rT).SP.n ≤ nRowsTpl := by
  have hW : (VclL.GenWalk.walkRows DAT.cells DAT.reads).length ∈ ComplJ9ARun.sizesA DAT :=
    List.mem_append_left _ (by simp [ComplJ8Of.sizesJ8])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GenPortJ9ALHJRun.toInJ9A_X]
    exact le_nRows ((GenPortJ9AHMsgJ.size_X RtP genT hpGT h31AT χe).le.trans (hMT _ (mem_N9 RtP genT)))
  · exact le_nRows ((GenPortJ9ALHMsgJ.n_C_L RtP primsJ genT χe).le.trans cellsT_len)
  · rw [GenPortJ9ALHJRun.toInJ9A_W]
    exact le_nRows ((GenPortJ9AHMsgJ.size_W RtP genT hpGT h31AT χe hwalk9T).le.trans (hMT _ hW))
  · exact le_nRows ((GenPortJ9ALHMsgJ.n_J_L RtP primsJ genT χe).le.trans jrowsLT_len)
  · exact le_nRows ((GenPortJ9ALHMsgJ.n_A_L RtP primsJ genT χe).le.trans acsT_len)
  · rw [GenPortJ9ALHJRun.toInJ9A_V]
    exact le_nRows ((GenPortJ9AHMsgJ.size_V RtP genT hpGT h31AT χe hax9T hwalkAT).le.trans (hMT _ (mem_nV RtP genT)))
  · rw [GenPortJ9ALHJRun.toInJ9A_AX]
    exact le_nRows ((GenPortJ9AHMsgJ.size_AX RtP genT hpGT h31AT χe).le.trans (hMT _ (mem_nX RtP genT)))
  · rw [GenPortJ9ALHJRun.toInJ9A_SP]
    exact le_nRows ((GenPortJ9AHMsgJ.size_SP RtP genT hpGT h31AT χe).le.trans (hMT _ (mem_nS RtP genT)))

/-- **`rowsTpl_le`**: every chip of every record the generator produces on `jp` has at most `nRowsTpl` rows (a bound,
whatever the coin). -/
theorem rowsTpl_le (χe : CoinsE) (I : InJ9AL)
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe = some I) :
    I.X.n ≤ nRowsTpl ∧ I.C.n ≤ nRowsTpl ∧ I.W.n ≤ nRowsTpl ∧ I.J.n ≤ nRowsTpl ∧ I.A.n ≤ nRowsTpl ∧
      I.V.n ≤ nRowsTpl ∧ I.AX.n ≤ nRowsTpl ∧ I.SP.n ≤ nRowsTpl ∧ I.AL.n ≤ nRowsTpl := by
  rw [genT_L χe] at hI
  cases Option.some.inj hI
  exact ⟨(chipsN_le χe).1, (chipsN_le χe).2.1, (chipsN_le χe).2.2.1, (chipsN_le χe).2.2.2.1,
    (chipsN_le χe).2.2.2.2.1, (chipsN_le χe).2.2.2.2.2.1, (chipsN_le χe).2.2.2.2.2.2.1,
    (chipsN_le χe).2.2.2.2.2.2.2, alN_le χe⟩

/-- The uniform orbit assignment: every one of the nine chips on `⟨h, ω⟩`. -/
def orbU (h : ℕ) (ω : Nock.TraceGenExe.Gold) : OrbJ9AL :=
  ⟨⟨⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩, ⟨h, ω⟩⟩, ⟨h, ω⟩⟩

/-- **`honestTplUnif`**: at the generator's good coin, at EVERY common orbit `⟨h, ω⟩` of order `3 * 2^h` with
`nRowsTpl <= 3 * 2^h`, the record is valid and `AcceptsJ9AL` (the form the end-to-end package consumes). -/
theorem honestTplUnif : ∃ χe : CoinsE, ∃ I : InJ9AL,
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe = some I ∧
    ∀ (h : ℕ) (ω : Nock.TraceGenExe.Gold), 1 ≤ h → orderOf ω.toZ = 3 * 2 ^ h → nRowsTpl ≤ 3 * 2 ^ h →
      ∃ hv : ValidJ9AL (withOrbL I (orbU h ω)),
        AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I (orbU h ω)) hv) catJ.toVR.R
          (withOrbL I (orbU h ω)).c (toχ (withOrbL I (orbU h ω)).χ) (withOrbL I (orbU h ω)).toMsgL
          (withOrbL I (orbU h ω)).toTrL (withOrbL I (orbU h ω)).toRowsL (withOrbL I (orbU h ω)).g := by
  obtain ⟨χe, I, hI, hall⟩ := honestTpl
  refine ⟨χe, I, hI, fun h ω h1 hord hn => hall (orbU h ω) ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := rowsTpl_le χe I hI
  have hh : ∀ n : ℕ, n ≤ nRowsTpl → n ≤ 3 * 2 ^ h := fun n hn' => hn'.trans hn
  exact ⟨⟨⟨⟨h1, hord⟩, hh _ b1⟩, ⟨⟨h1, hord⟩, hh _ b2⟩, ⟨⟨h1, hord⟩, hh _ b3⟩, ⟨⟨h1, hord⟩, hh _ b4⟩,
    ⟨⟨h1, hord⟩, hh _ b5⟩, ⟨⟨h1, hord⟩, hh _ b6⟩, ⟨⟨h1, hord⟩, hh _ b7⟩, ⟨⟨h1, hord⟩, hh _ b8⟩⟩,
    ⟨⟨h1, hord⟩, hh _ b9⟩⟩

end
end Nock.RedTeam.Batch4939

#print axioms Nock.RedTeam.Batch4939.complJ9AL_tpl
#print axioms Nock.RedTeam.Batch4939.genLinkTpl
#print axioms Nock.RedTeam.Batch4939.honestTpl
#print axioms Nock.RedTeam.Batch4939.rowsTpl_le
#print axioms Nock.RedTeam.Batch4939.honestTplUnif
