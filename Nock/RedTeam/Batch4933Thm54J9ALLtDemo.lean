/-
  Nock/RedTeam/Batch4933Thm54J9ALLtDemo.lean

  **Demo: `lt` through `complJ9AL_closed`, hypothesis-free.**  The run
  `*[[aN bN] [11 [id [1 0]] (primC lt)]] = rT` over `addPrims empty [(id, lt)]` (Goldilocks, `K = KC`),
  `aN = 2 ^ 70 + 3`, `bN = 2 ^ 80 + 5` (big atoms, `>= p`), one call of the primitive `lt`, so the ALU chip is on.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALClosed
import Nock.RedTeam.Batch4921Thm54J9ALComplToy
import Nock.RedTeam.Batch4931Thm54AluBlockBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch4933


open Nock Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Prim
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl j9alDataOf pcallsR primsC opOf)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (factRC charPKC algRC card_KC)



open Nock Nock.NockVMROM.Thm54 Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Prim
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (addPrims)

abbrev pP : ℕ := Nock.Field.p
def idAdd : ℕ := 7
def aN : ℕ := 2 ^ 70 + 3
def bN : ℕ := 2 ^ 80 + 5
def sT : Noun := .cell (.atom aN) (.atom bN)
def clueT : Noun := .cell (.atom 1) (.atom idAdd)
def fT : Noun := .cell (.atom 11) (.cell (.cell (.atom wildTag) clueT) (primC .lt))
def rT : Noun := .atom (0)
def RgT : VerifiedRegistry := addPrims VerifiedRegistry.empty [(idAdd, .lt)]
def tD : NTree SkelX := mkX .s1 sT clueT (.atom idAdd) []
def tT : NTree SkelX := mkX .s11j sT fT rT [tD]

theorem RgT_R : RgT.R idAdd = some (primSpec .lt) :=
  Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.addPrims_R_of_mem VerifiedRegistry.empty [(idAdd, .lt)]
    (by simp) (idAdd, .lt) (by simp)

theorem semS_T : (primTemplate .lt).semS sT = some rT := by
  simp [primTemplate, binT, Template.semS, Template.args, sT, rT, aN, bN, primSem, Noun.slot]
  try omega

theorem genT : genX RgT.R 2 sT fT = some (tT, rT) := by
  have h1 : genX RgT.R 1 sT clueT = some (tD, .atom idAdd) := by
    simp [genX, genComputeSkeletonX, clueT, tD, mkX]
  have hj : jetHit RgT.R (.atom wildTag) (.atom idAdd) (primC .lt) sT = some rT := by
    simp [jetHit, RgT_R, semS_T, primSpec]
  simp only [genX] at h1
  simp only [genX, fT, genComputeSkeletonX]
  simp only [h1, hj]
  rfl


open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl j9alDataOf)
open Nock.Jet.Autogen (Tpl compile)

theorem bfsT : bfsForest [tT] = [tT, tD] := by simp [bfsForest, tT, tD, mkX]

theorem rowsT : rowsOfT tT = #[rowOfSkelX tT.label, rowOfSkelX tD.label] := by
  simp only [rowsOfT, bfsT]; rfl

noncomputable section
variable (Rt0 : ℕ → Tpl)
abbrev RtP : ℕ → Tpl := rtP Rt0 [(idAdd, .lt)]
abbrev DDT := j8DataOf pP RgT (RtP Rt0) genT
abbrev DAT := j9aDataOf pP RgT (RtP Rt0) genT
abbrev DLT := j9alDataOf pP RgT (RtP Rt0) [(idAdd, .lt)] genT

theorem callsT : (DDT Rt0).calls = [(idAdd, sT)] := by
  show Nock.V1J8.Gen.callsOf (rowsOfT tT) = _
  rw [rowsT]
  decide

theorem valsT : ComplJ8Data.callValsP pP (RtP Rt0) 0 (idAdd, sT) = [Noun.atom 0] := by
  rw [ComplJ8Data.callValsP]
  show (Nock.Jet.Interp.honestRows pP (RtP Rt0 idAdd) sT 0).map _ = _
  rw [show RtP Rt0 idAdd = trivTpl from Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData.rtP_of_mem Rt0 [(idAdd, .lt)] (by simp)]
  rfl


abbrev rowsL : Array RowNX := #[rowOfSkelX tT.label, rowOfSkelX tD.label]

theorem rtP_idAdd : RtP Rt0 idAdd = trivTpl :=
  Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData.rtP_of_mem Rt0 [(idAdd, .lt)] (by simp)

theorem callsL_eq : Nock.V1J8.Gen.callsOf rowsL = [(idAdd, sT)] := by decide

theorem jnT : (DDT Rt0).jn = [compile pP trivTpl, sT, .atom 0] := by
  show ComplJ8Data.jNounsP pP (RtP Rt0) ((Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst).dedup
    (Nock.V1J8.Gen.callsOf (rowsOfT tT)) = _
  rw [rowsT, callsL_eq]
  rfl

theorem rootsT : (DDT Rt0).roots = Nock.V1J8.Gen.rootsOf ⟨sT, fT, rT⟩ rowsL ++ [compile pP trivTpl, sT, .atom 0] := by
  show Nock.V1J8.Gen.rootsOf _ (rowsOfT tT) ++ (DDT Rt0).jn = _
  rw [jnT, rowsT]

theorem hleafT : ComplJ8Walk.RootsLeafOK (DDT Rt0).roots := by
  rw [rootsT]
  show ∀ x ∈ Nock.V1J8.Gen.rootsOf ⟨sT, fT, rT⟩ rowsL ++ [compile pP trivTpl, sT, .atom 0], x.leaves ≤ 2 ^ 109
  decide

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A AxRowX9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

theorem inTree_tT (u : NTree SkelX) (h : InTree tT u) : u = tT ∨ u = tD := by
  have : u ∈ bfsForest [tT] := (mem_bfsForest [tT] u).2 ⟨tT, by simp, h⟩
  rw [bfsT] at this; simpa using this

theorem st_tT : (rowOfSkelX tT.label).st = .s11j := rfl
theorem ftth_tT : (rowOfSkelX tT.label).ftth = .atom wildTag := rfl
theorem sf1_tT : (rowOfSkelX tT.label).sf1 = .atom idAdd := rfl
theorem st_tD : (rowOfSkelX tD.label).st = .s1 := rfl

theorem hax9T : ProgAxOK9A pP tT := by
  intro u hu
  rcases inTree_tT u hu with rfl | rfl
  · refine ⟨fun id h => ?_, fun id h => ?_⟩
    · rw [ftth_tT] at h
      cases h
      show wildTag < Nock.Field.p
      unfold wildTag Nock.Field.p; norm_num
    · rw [sf1_tT] at h
      cases h
      show idAdd < Nock.Field.p
      unfold idAdd Nock.Field.p; norm_num
  · show True
    trivial

theorem hop5T : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8.ProgOp5OK pP tT := by
  intro u hu
  rcases inTree_tT u hu with rfl | rfl <;> intro h
  · rw [st_tT] at h; cases h
  · rw [st_tD] at h; cases h

theorem calledT : ∀ id ∈ CalledIds tT, id = idAdd := by
  rintro id ⟨u, hu, hst, hid⟩
  rcases inTree_tT u hu with rfl | rfl
  · rw [sf1_tT] at hid; cases hid; rfl
  · rw [st_tD] at hst; cases hst

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9 rowX9)

def gT9 : NTree LX9 :=
  .node ⟨rowX9 tT.label, .old, 0, 0, rowOfSkelX tT.label⟩
    [.node ⟨rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩ []]

theorem chipTT : ComplJ9AGen.chipOf tT.label = (.old, 0) := by decide
theorem chipTD : ComplJ9AGen.chipOf tD.label = (.old, 0) := by decide

theorem genX9T_T : ComplJ9AGen.genX9T tT = gT9 := by
  have hD : ComplJ9AGen.genX9T tD = .node ⟨ComplJ9AGen.rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩ [] := by
    show ComplJ9AGen.genX9T (.node tD.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipTD]; rfl
  show ComplJ9AGen.genX9T (.node tT.label [tD]) = _
  rw [ComplJ9AGen.genX9T_node, chipTT]
  simp only [List.map_cons, List.map_nil, hD, ComplJ9AGen.kid9, chipTT, gT9]
  simp

theorem bfs9T : bfsForest [gT9] = [gT9, .node ⟨ComplJ9AGen.rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩ []] := by
  simp [bfsForest, gT9]

theorem rows9T : ComplJ9AGen.rowsOfT9 tT =
    #[⟨ComplJ9AGen.rowX9 tT.label, .old, 0, 0, rowOfSkelX tT.label⟩,
      ⟨ComplJ9AGen.rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩] := by
  simp only [ComplJ9AGen.rowsOfT9, genX9T_T, bfs9T]; rfl

theorem keys9T : ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 tT) = [] := by
  rw [rows9T]; decide

theorem axAtoms9T : ComplJ9AData.axAtoms9 (ComplJ9AGen.rowsOfT9 tT) = [] := by
  rw [rows9T]; decide

theorem fieldAx9T : ComplJ9AData.fieldAx9 pP (ComplJ9AGen.rowsOfT9 tT) = [] := by
  unfold ComplJ9AData.fieldAx9; rw [axAtoms9T]; rfl

theorem axOnA_tT : ComplJ9ARun.axOnA tT = false := by
  simp [ComplJ9ARun.axOnA, keys9T]

theorem spOnA_tT : ComplJ9ARun.spOnA pP tT = false := by
  simp [ComplJ9ARun.spOnA, fieldAx9T]

theorem N9T : ComplJ9ARun.N9 tT = 2 := by
  rw [ComplJ9ARun.N9_def, ComplJ9ARun.W9, genX9T_T, bfs9T]; rfl

theorem nXT : ComplJ9ARun.nXOf pP (DAT Rt0).acs.length (DAT Rt0).H tT = 1 := by
  simp [ComplJ9ARun.nXOf, axOnA_tT]

theorem nST : ComplJ9ARun.nSOf pP tT = 1 := by
  simp [ComplJ9ARun.nSOf, spOnA_tT]

theorem walkReadsX9T : ComplJ9AReads.walkReadsX9 (ComplJ9AGen.rowsOfT9 tT) = [] := by
  rw [rows9T]; decide

theorem readsT : (DAT Rt0).reads = [] := by
  change ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ = []
  rw [walkReadsX9T, List.nil_append]
  simp [ComplJ9AChainsRun.axChainReadsK9, keys9T]

/-! ## sizes -/

theorem preadsT : (DDT Rt0).preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (rowsOfT tT) = []
  rw [rowsT]
  simp [ComplJ8Data.pairReadsP, Nock.V1J8.FillX.isPairB, rowOfSkelX, tT, tD, mkX]

theorem axReadsK9T : ComplJ9AChainsRun.axReadsK9 pP (ComplJ9AGen.rowsOfT9 tT) = [] := by
  unfold ComplJ9AChainsRun.axReadsK9
  rw [keys9T, rows9T]
  decide

theorem preadsDAT : (DAT Rt0).preads = [] := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsT, axReadsK9T]; rfl

theorem walkReads9T : ComplJ9ABinders.walkReads9 rowsL = [] := by decide

theorem hwalk9T : WalkDepthOK9A (rowsOfT tT) := by
  show ComplJ8Walk.WalkDepthOK (ComplJ9ABinders.walkReads9 _)
  rw [rowsT, walkReads9T]; intro r hr; simp [VclL.pathReads] at hr

theorem hwalkAT : ComplJ8Walk.WalkDepthOK (DDT Rt0).preads := by
  rw [preadsT]; intro r hr; simp [VclL.pathReads] at hr

theorem regsT : (DDT Rt0).regs = [idAdd] := by
  show ((Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst).dedup = _
  rw [rowsT, callsL_eq]; rfl

theorem idsT : (DDT Rt0).ids = [idAdd] := by
  show (Nock.V1J8.Gen.callsOf (rowsOfT tT)).map Prod.fst = _
  rw [rowsT, callsL_eq]; rfl

theorem jrowsDD_len : (DDT Rt0).jrows.length ≤ 2 ^ 31 := by
  have h := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet.jrows_pre_run (p := pP) (RtP Rt0) genT
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  rw [h2, regsT, idsT]
  have e : Nock.Jet.ChipJ8.layoutJ8 (RtP Rt0) [idAdd] [idAdd] =
      Nock.Jet.ChipJ8.layoutJ8 (fun _ => trivTpl) [idAdd] [idAdd] := rfl
  rw [e]
  decide

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

theorem cellsT_len : (DAT Rt0).cells.length ≤ 2 ^ 31 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells]
  show (Nock.V1J8.Gen.cellsOfRoots (DDT Rt0).roots).length ≤ _
  have h := foldl_addCells_len (DDT Rt0).roots []
  have h2 : ((DDT Rt0).roots.map ncell).sum ≤ 2 ^ 31 := by
    rw [rootsT]; decide
  unfold Nock.V1J8.Gen.cellsOfRoots
  simp only [List.length_nil, zero_add] at h
  exact le_trans h h2

/-! ### bigs and acs -/

theorem bigsP_perm_of (p : ℕ) (roots : List Noun) (rows : Array RowNX) (l : List ℕ)
    (hl : (((roots ++ rows.toList.flatMap rowHandleNounsX).flatMap leavesOf).filter fun a => decide (p ≤ a)).dedup = l) :
    (ComplJ8Data.bigsP p roots rows).Perm l := by
  unfold ComplJ8Data.bigsP
  rw [hl]
  exact List.mergeSort_perm _ _

theorem bigsT_perm : (DDT Rt0).bigs.Perm [aN, bN] := by
  show (ComplJ8Data.bigsP pP (DDT Rt0).roots (rowsOfT tT)).Perm _
  rw [rootsT, rowsT]
  exact bigsP_perm_of pP _ _ _ (by decide)

theorem lim_le (a : ℕ) (k : ℕ) (h : a < 2 ^ (32 * k)) : (Nock.Atoms.limbs a).length ≤ k := by
  unfold Nock.Atoms.limbs Nock.Atoms.B
  rw [Nat.digits_length_le_iff (by norm_num)]
  calc a < 2 ^ (32 * k) := h
    _ = (2 ^ 32) ^ k := by rw [pow_mul]

theorem limbs_a : (Nock.Atoms.limbs aN).length ≤ 3 := lim_le _ _ (by norm_num [aN, bN])
theorem limbs_b : (Nock.Atoms.limbs bN).length ≤ 3 := lim_le _ _ (by norm_num [aN, bN])

/-- Limb count of a number below `2^96`. -/
theorem limbs_len_le3 {a : ℕ} (h : a < 2 ^ 96) : (Nock.Atoms.limbs a).length ≤ 3 := by
  unfold Nock.Atoms.limbs Nock.Atoms.B
  rw [Nat.digits_length_le_iff (by norm_num)]
  calc a < 2 ^ 96 := h
    _ = (2 ^ 32) ^ 3 := by norm_num

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

theorem acsT_len : (DAT Rt0).acs.length ≤ 2 ^ 31 := by
  show (ComplJ8Data.acsP pP (DDT Rt0).bigs (DDT Rt0).dupP).length ≤ _
  refine (acsP_len_le _ _ _).trans ?_
  have hs := ((bigsT_perm Rt0).map fun a => (Nock.Atoms.limbs a).length).sum_eq
  rw [hs]
  have h1 := limbs_a
  have h2 := limbs_b
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have : (2 : ℕ) ^ 31 ≥ 100 := by norm_num
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

theorem nVDAT : ComplJ8Of.nVOf (DAT Rt0) = 1 := by
  unfold ComplJ8Of.nVOf
  rw [preadsDAT]
  simp

theorem h31AT : ComplJ9ARun.Rows31A (DAT Rt0) := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  have hB : (bfsForest [(DAT Rt0).t]).length = 2 := by
    show (bfsForest [tT]).length = 2
    rw [bfsT]; rfl
  have hC := cellsT_len Rt0
  have hW : (VclL.GenWalk.walkRows (DAT Rt0).cells (DAT Rt0).reads).length ≤ 2 ^ 31 := by
    have h := walk_bound (DAT Rt0).cells (DAT Rt0).reads (by rw [readsT]; simp)
    rw [readsT] at h ⊢
    simp only [List.length_nil, mul_zero, zero_add] at h
    omega
  have hJ : (DAT Rt0).jrows.length ≤ 2 ^ 31 := jrowsDD_len Rt0
  have hA := acsT_len Rt0
  have hV : ComplJ8Of.nVOf (DAT Rt0) = 1 := nVDAT Rt0
  have hN : ComplJ9ARun.N9 (DAT Rt0).t = 2 := N9T
  have hX : ComplJ9ARun.nXOf pP (DAT Rt0).acs.length (DAT Rt0).H (DAT Rt0).t = 1 := nXT Rt0
  have hS : ComplJ9ARun.nSOf pP (DAT Rt0).t = 1 := nST
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

theorem callsLT : (DLT Rt0).calls = [] := by
  rw [ComplJ9ALData.F_calls (RtP Rt0) [(idAdd, .lt)] genT, rowsT, callsL_eq]
  decide

theorem jrowsLT_len : (DLT Rt0).jrows.length ≤ 2 ^ 31 := by
  have h := ComplJ9ALData.jrows_preL (p := pP) (RtP Rt0) [(idAdd, .lt)] genT
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  have hr : (DLT Rt0).regs = [] := by
    rw [ComplJ9ALData.F_regs (RtP Rt0) [(idAdd, .lt)] genT, callsLT]; rfl
  have hi : (DLT Rt0).ids = [] := by
    rw [ComplJ9ALData.F_ids (RtP Rt0) [(idAdd, .lt)] genT, callsLT]; rfl
  rw [h2, hr, hi]
  simp [Nock.Jet.ChipJ8.layoutJ8, Nock.Jet.ChipJ8.blocks]

theorem h31LT : ComplJ9ARun.Rows31A (DLT Rt0) := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  have hB : (bfsForest [(DLT Rt0).t]).length = 2 := by
    show (bfsForest [tT]).length = 2
    rw [bfsT]; rfl
  have hC : (DLT Rt0).cells.length ≤ 2 ^ 31 := cellsT_len Rt0
  have hW : (VclL.GenWalk.walkRows (DLT Rt0).cells (DLT Rt0).reads).length ≤ 2 ^ 31 := by
    have h := walk_bound (DAT Rt0).cells (DAT Rt0).reads (by rw [readsT]; simp)
    have e : (DLT Rt0).reads = (DAT Rt0).reads := rfl
    have e2 : (DLT Rt0).cells = (DAT Rt0).cells := rfl
    rw [e, e2]
    rw [readsT] at h ⊢
    simp only [List.length_nil, mul_zero, zero_add] at h
    omega
  have hJ := jrowsLT_len Rt0
  have hA : (DLT Rt0).acs.length ≤ 2 ^ 31 := acsT_len Rt0
  have hV : ComplJ8Of.nVOf (DLT Rt0) = 1 := by
    unfold ComplJ8Of.nVOf
    have : (DLT Rt0).preads = [] := preadsDAT Rt0
    rw [this]; simp
  have hN : ComplJ9ARun.N9 (DLT Rt0).t = 2 := N9T
  have hX : ComplJ9ARun.nXOf pP (DLT Rt0).acs.length (DLT Rt0).H (DLT Rt0).t = 1 := nXT Rt0
  have hS : ComplJ9ARun.nSOf pP (DLT Rt0).t = 1 := nST
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

/-! ### The prim binders -/

theorem hlimbT : AluCallOK.PrimLimbs62 ([(idAdd, PrimOp.lt)].map Prod.fst) tT := by
  intro x hx
  have e : ComplJ9ALData.pcallsR ([(idAdd, PrimOp.lt)].map Prod.fst) (rowsOfT tT) = [(idAdd, sT, rT)] := by
    rw [rowsT]; decide
  rw [e] at hx
  simp only [List.mem_singleton] at hx
  subst hx
  show (Nock.Atoms.limbs aN).length ≤ 62 ∧ (Nock.Atoms.limbs bN).length ≤ 62
  exact ⟨by have := limbs_a; omega, by have := limbs_b; omega⟩

theorem hnoDecT : ∀ q ∈ [(idAdd, PrimOp.lt)], q.2 ≠ PrimOp.dec := by simp
theorem hndT : ([(idAdd, PrimOp.lt)].map Prod.fst).Nodup := by simp
theorem hprimT : ∀ q ∈ [(idAdd, PrimOp.lt)], RgT.R q.1 = some (primSpec q.2) := by
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  exact RgT_R

theorem hRtJT : ∀ id ∈ CalledIds tT, id ∉ [(idAdd, PrimOp.lt)].map Prod.fst →
    RgT.R id = some ⟨(RtP Rt0 id).toTemplate pP, compile pP (RtP Rt0 id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (RtP Rt0 id) = true ∧ (RtP Rt0 id).WellTyped pP := by
  intro id hid hn
  exact absurd (by rw [calledT id hid]; simp) hn

theorem hregAxJT : ∀ id ∈ CalledIds tT, id ∉ [(idAdd, PrimOp.lt)].map Prod.fst → ∀ i, (RtP Rt0 id).ax i < pP := by
  intro id hid hn
  exact absurd (by rw [calledT id hid]; simp) hn

theorem hTrivT : ∀ id ∈ [(idAdd, PrimOp.lt)].map Prod.fst, RtP Rt0 id = trivTpl :=
  fun id h => Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData.rtP_of_mem Rt0 _ h

theorem hpGT : pP = Nock.Atoms.p := rfl

end



/-! ## 2. The toy's ALU size -/

theorem pcalls_T : pcallsR ([(idAdd, PrimOp.lt)].map Prod.fst) (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.rowsOfT tT) =
    [(idAdd, sT, rT)] := by
  rw [rowsT]; decide

theorem opOf_T : opOf [(idAdd, PrimOp.lt)] idAdd = .lt := by decide

theorem psLen (ids : List ℕ) : (primsC [(idAdd, PrimOp.lt)] ids).length ≤ 1 :=
  (List.length_filter_le _ _).trans (by simp)

open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRun
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

theorem aluLen_toy (Rt0 : ℕ → Nock.Jet.Autogen.Tpl) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen (K := KC) deltaF (RtP Rt0) genT [(idAdd, .lt)] < 2 ^ 31 := by
  have hps : (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.psRun (p := pP) (RtP Rt0) genT [(idAdd, .lt)]).length ≤ 1 :=
    psLen _
  have hcl : clsRun (p := pP) (RtP Rt0) [(idAdd, .lt)] genT =
      callsLOf (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .lt)] genT).cells
        (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .lt)] genT).H [(idAdd, .lt)] [(idAdd, sT, rT)] := by
    unfold clsRun
    rw [pcalls_T]
  have h1 : (Nock.Atoms.limbs aN).length ≤ 6 := limbs_a.trans (by norm_num)
  have h2 : (Nock.Atoms.limbs bN).length ≤ 6 := limbs_b.trans (by norm_num)
  have h3 : (Nock.Atoms.limbs (ltWit aN bN)).length ≤ 6 := lim_le _ 6 (by norm_num [ltWit, aN, bN])
  obtain ⟨cl, hcl1, hop, ha, hb, hc⟩ : ∃ cl, callsLOf (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .lt)] genT).cells
      (j9alDataOf pP RgT (RtP Rt0) [(idAdd, .lt)] genT).H [(idAdd, .lt)] [(idAdd, sT, rT)] = [cl] ∧
      cl.op = .lt ∧ cl.a = aN ∧ cl.b = bN ∧ cl.c = 0 := ⟨_, rfl, opOf_T, rfl, rfl, rfl⟩
  have hB := Nock.RedTeam.Batch4931.blockB_lt_le (F := ZMod pP) pP cl hop (ha ▸ h1) (hb ▸ h2) (by rw [ha, hb]; exact h3)
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.aluLen Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun.tbR tblRun tblP
  rw [hcl, hcl1]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg.pregsP_length,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, zipB_length]
  simp only [pP] at hB ⊢
  omega

/-! ## 3. The toy -/

/-- The base template table (constant `trivTpl`; the run never reads it at a non-primitive id). -/
abbrev Rt0T : ℕ → Nock.Jet.Autogen.Tpl := fun _ => trivTpl

/-- The prim-aware `hRt`: vacuous, every called id is the primitive `id_add`. -/
theorem hRtT : ∀ id ∈ ComplJ8Jet.CalledIds tT, id ∉ [(idAdd, PrimOp.lt)].map Prod.fst →
    RgT.R id = some ⟨(Rt0T id).toTemplate pP, Nock.Jet.Autogen.compile pP (Rt0T id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt0T id) = true ∧ (Rt0T id).WellTyped pP :=
  fun id h hn => absurd (by rw [calledT id h]; simp) hn

/-- The prim-aware `hregAx`: vacuous likewise. -/
theorem hregAxT : ∀ id ∈ ComplJ8Jet.CalledIds tT, id ∉ [(idAdd, PrimOp.lt)].map Prod.fst →
    ∀ i, (Rt0T id).ax i < pP :=
  fun id h hn => absurd (by rw [calledT id h]; simp) hn

/-- The honest J-9 AL record of the toy run. -/
noncomputable abbrev BL := ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0T [(idAdd, PrimOp.lt)]) genT [(idAdd, PrimOp.lt)]
  hpGT (h31AT Rt0T)

open Classical in
/-- **`complJ9AL_toy`: J-9 AL completeness at a concrete `lt` run, every hypothesis discharged.**
The run is one call of the primitive `lt` on the big atoms `2^70 + 3` and `2^80 + 5` (both `≥ p`) over the
Goldilocks prime, so the ALU chip is on.  For this run, `AcceptsJ9AL` accepts at every good coin, the fraction of
coins that are not good is at most `ε_c`, the trace family is staged (`StJ9AL`), the claim holds (`HoldsN`), and,
as `|K| = cK`, `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9AL_toy :
    (∀ χ, BL.Good χ → AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
      BL.rows BL.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BL.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BL.epsC) ∧
    RealIOJ9AL.StJ9AL BL.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sT fT rT) ∧
    (Fintype.card KC = VclL.Events.cK →
      BL.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
        BL.rows BL.g) :=
  ComplJ9ALClosed.complJ9AL_closed deltaF powerBasis3 Rt0T genT [(idAdd, PrimOp.lt)] hpGT hax9T hop5T (hleafT Rt0T)
    hwalk9T (hwalkAT Rt0T) hRtT hregAxT hndT hprimT (h31AT Rt0T) (aluLen_toy Rt0T) hlimbT hnoDecT

open Classical in
/-- **`complJ9AL_toy_figure`: the completeness figure at the concrete `lt` run, with no hypothesis.**
For the run of `complJ9AL_toy`, `ε_c < 2^-120` and some coin is accepted by `AcceptsJ9AL`. -/
theorem complJ9AL_toy_figure :
    BL.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 BL.Pb RgT.R (ComplJ8.cJ sT fT rT) χ (BL.M χ) (BL.tr χ)
        BL.rows BL.g :=
  complJ9AL_toy.2.2.2.2 card_KC


end Nock.RedTeam.Batch4933

#print axioms Nock.RedTeam.Batch4933.complJ9AL_toy
