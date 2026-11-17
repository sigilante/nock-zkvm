/-
  At an existential
  good coin, `genJ9AXJ` produces a record and the wired J-9 A checker `checkJ9AX` accepts it.  No `#eval`, no
  `native_decide`: the run `genX` and every binder fact is a kernel `decide` on the two-row tree (the J-8 `bfsForest`
  is rewritten to the explicit two-node shape first, since the kernel cannot unfold its well-founded recursion).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ
import Nock.V1J9A.GenJ9AXJ
import Nock.V1J8.GenJetMat
import Nock.RedTeam.Batch4883Thm54J9AComplToy

set_option autoImplicit false

namespace Nock.RedTeam.Batch4937

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Autogen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J8.GenJ (matRt)
open Nock.TraceGenExe (KC deltaF powerBasis3)

def RgM : VerifiedRegistry :=
  VerifiedRegistry.ofCompiled Nock.Field.p (by decide) matRt [7] (fun _ _ => matmul_wellTyped (by decide) 2)

def resM : Option (NTree SkelX × Noun) := genX RgM.R 2 toyS Demo.matProg

theorem resM_some : ∃ t r, resM = some (t, r) := by
  have : resM.isSome = true := by decide +kernel
  revert this; unfold resM; cases genX RgM.R 2 toyS Demo.matProg with
  | none => simp
  | some tr => intro _; exact ⟨tr.1, tr.2, rfl⟩

def tM : NTree SkelX := (resM.map Prod.fst).getD (.node ⟨.s1, .atom 0, .atom 0, .atom 0, []⟩ [])
def rM : Noun := (resM.map Prod.snd).getD (.atom 0)

theorem genM : genX RgM.R 2 toyS Demo.matProg = some (tM, rM) := by
  obtain ⟨t, r, h⟩ := resM_some
  have h' : genX RgM.R 2 toyS Demo.matProg = some (t, r) := h
  simp [tM, rM, h, h']

def shapeB : Bool := match tM with | .node _ [.node _ []] => true | _ => false

theorem shapeB_true : shapeB = true := by decide +kernel

theorem tM_shape : ∃ a b, tM = .node a [.node b []] := by
  have h := shapeB_true
  unfold shapeB at h
  revert h
  cases tM with
  | node a ks =>
    cases ks with
    | nil => simp
    | cons k ks =>
      cases k with
      | node b kk =>
        cases kk with
        | nil => cases ks with
          | nil => intro _; exact ⟨a, b, rfl⟩
          | cons _ _ => simp
        | cons _ _ => simp

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf)
open Nock.NockVMROM.Thm54.VclL

noncomputable section
abbrev DDM := j8DataOf Nock.Field.p RgM matRt genM
abbrev DAM := ComplJ9ADataRec.j9aDataOf Nock.Field.p RgM matRt genM

def aM : SkelX := match tM with | .node a _ => a
def bM : SkelX := match tM with | .node _ [.node b []] => b | _ => aM

theorem tM_eq : tM = .node aM [.node bM []] := by
  obtain ⟨a, b, h⟩ := tM_shape
  have ha : aM = a := by simp only [aM, h]
  have hb : bM = b := by simp only [bM, h]
  rw [ha, hb]; exact h

theorem bfsM : bfsForest [tM] = [tM, .node bM []] := by
  rw [tM_eq]; simp [bfsForest]

theorem rowsM : ComplJ8Data.rowsOfT tM = #[rowOfSkelX aM, rowOfSkelX bM] := by
  simp only [ComplJ8Data.rowsOfT, bfsM]; rw [tM_eq]; rfl

theorem inTree_tM (u : NTree SkelX) (h : InTree tM u) : u = .node aM [.node bM []] ∨ u = .node bM [] := by
  have : u ∈ bfsForest [tM] := (mem_bfsForest [tM] u).2 ⟨tM, by simp, h⟩
  rw [bfsM] at this
  rcases List.mem_cons.1 this with h1 | h1
  · exact Or.inl (h1.trans tM_eq)
  · exact Or.inr (List.mem_singleton.1 h1)

theorem stA : aM.state = .s11j := by decide +kernel
theorem stB : bM.state = .s1 := by decide +kernel
theorem rstA : (rowOfSkelX aM).st = .s11j := by decide +kernel
theorem rstB : (rowOfSkelX bM).st = .s1 := by decide +kernel
theorem ftthA : (rowOfSkelX aM).ftth = .atom Nock.Jet.wildTag := by decide +kernel
theorem sf1A : (rowOfSkelX aM).sf1 = .atom 7 := by decide +kernel

theorem matAx : Nock.Jet.ChipJ8.axPosB (matmulT 2) = true := by decide +kernel
theorem matAxLt : ∀ i, (matmulT 2).ax i < Nock.Field.p := by decide +kernel

theorem hC_M : CheckedRegistry.CompiledBy Nock.Field.p RgM matRt := by
  intro id j h
  have h' : (if id ∈ [7] then some (⟨(matRt id).toTemplate Nock.Field.p, compile Nock.Field.p (matRt id)⟩ : JetSpec) else none) = some j := h
  by_cases hn : id ∈ [7]
  · rw [if_pos hn] at h'
    exact ⟨(Option.some.inj h').symm, matAx, matmul_wellTyped (by decide) 2, matAxLt⟩
  · rw [if_neg hn] at h'; cases h'

theorem hax9M : ComplJ9ABinders.ProgAxOK9A Nock.Field.p tM := by
  intro u hu
  rcases inTree_tM u hu with rfl | rfl
  · show ComplJ9ABinders.AxRowX9A _ (rowOfSkelX aM)
    simp only [ComplJ9ABinders.AxRowX9A, rstA]
    refine ⟨fun id h => ?_, fun id h => ?_⟩
    · rw [ftthA] at h; cases h; decide
    · rw [sf1A] at h; cases h; decide
  · show ComplJ9ABinders.AxRowX9A _ (rowOfSkelX bM)
    simp only [ComplJ9ABinders.AxRowX9A, rstB]

theorem hop5M : ComplJ8.ProgOp5OK Nock.Field.p tM := by
  intro u hu
  rcases inTree_tM u hu with rfl | rfl
  · show ComplJ8.Op5RowX _ (rowOfSkelX aM)
    simp only [ComplJ8.Op5RowX, rstA]; intro h; cases h
  · show ComplJ8.Op5RowX _ (rowOfSkelX bM)
    simp only [ComplJ8.Op5RowX, rstB]; intro h; cases h


abbrev rowsL : Array RowNX := #[rowOfSkelX aM, rowOfSkelX bM]

theorem rootsM : DDM.roots = Nock.V1J8.Gen.rootsOf ⟨toyS, Demo.matProg, rM⟩ rowsL ++
    ComplJ8Data.jNounsP Nock.Field.p matRt ((Nock.V1J8.Gen.callsOf rowsL).map Prod.fst).dedup (Nock.V1J8.Gen.callsOf rowsL) := by
  have h : DDM.roots = Nock.V1J8.Gen.rootsOf ⟨toyS, Demo.matProg, rM⟩ (ComplJ8Data.rowsOfT tM) ++
    ComplJ8Data.jNounsP Nock.Field.p matRt ((Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tM)).map Prod.fst).dedup (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tM)) := rfl
  rw [h, rowsM]

theorem hleafM : ComplJ8Walk.RootsLeafOK DDM.roots := by
  rw [rootsM]
  show ∀ r ∈ _, Noun.leaves r ≤ 2 ^ 109
  decide +kernel

theorem hwalk9M : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT tM) := by
  show ∀ r ∈ pathReads (ComplJ9ABinders.walkReads9 (ComplJ8Data.rowsOfT tM)), depthOf r.2 ≤ 61
  rw [rowsM]
  decide +kernel

theorem preadsM : DDM.preads = ComplJ8Data.pairReadsP DDM.H DDM.pd rowsL := by
  have h : DDM.preads = ComplJ8Data.pairReadsP DDM.H DDM.pd (ComplJ8Data.rowsOfT tM) := rfl
  rw [h, rowsM]

theorem hwalkAM : ComplJ8Walk.WalkDepthOK DDM.preads := by
  rw [preadsM]
  show ∀ r ∈ pathReads (ComplJ8Data.pairReadsP DDM.H DDM.pd rowsL), depthOf r.2 ≤ 61
  decide +kernel

theorem bfs2 {LT : Type} (a b : LT) :
    bfsForest [NTree.node a [NTree.node b []]] = [NTree.node a [NTree.node b []], NTree.node b []] := by
  simp [bfsForest]

theorem chipA : ComplJ9AGen.chipOf aM = (.old, 0) := by decide +kernel
theorem chipB : ComplJ9AGen.chipOf bM = (.old, 0) := by decide +kernel

open ComplJ9AGen in
theorem g9M : genX9T tM = .node ⟨rowX9 aM, .old, 0, 0, rowOfSkelX aM⟩ [.node ⟨rowX9 bM, .old, 0, 0, rowOfSkelX bM⟩ []] := by
  rw [tM_eq, genX9T_node]
  simp only [List.map_cons, List.map_nil, genX9T_node, chipA, chipB, kid9]
  simp

open ComplJ9AGen in
theorem rows9M : rowsOfT9 tM = #[⟨rowX9 aM, .old, 0, 0, rowOfSkelX aM⟩, ⟨rowX9 bM, .old, 0, 0, rowOfSkelX bM⟩] := by
  simp only [rowsOfT9, g9M, bfs2]; rfl

theorem readsM : DAM.reads = [] := by
  show ComplJ9ADataRec.readsA tM = []
  unfold ComplJ9ADataRec.readsA
  rw [rows9M]; decide +kernel

theorem preadsDM : DAM.preads = [] := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsM, rows9M]
  decide +kernel

open Nock.RedTeam.Batch4883 (ncell foldl_addCells_len cells_gen walk_bound)

theorem cellsM_len : DAM.cells.length ≤ 2 ^ 31 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells, cells_gen genM]
  have h := foldl_addCells_len DDM.roots []
  have h2 : (DDM.roots.map ncell).sum ≤ 2 ^ 31 := by
    rw [rootsM]; decide +kernel
  simp only [List.length_nil, zero_add] at h
  exact le_trans h h2

theorem bigsM : DDM.bigs = [] := by
  have h : DDM.bigs = ComplJ8Data.bigsP Nock.Field.p DDM.roots (ComplJ8Data.rowsOfT tM) := rfl
  rw [h, rowsM, rootsM]; decide +kernel

theorem dupPM : DDM.dupP = false := by
  have h : DDM.dupP = ((ComplJ8Data.incOpsP Nock.Field.p (ComplJ8Data.rowsOfT tM)).any fun x => decide (x.1 + 1 = Nock.Field.p)) := rfl
  rw [h, rowsM]; decide +kernel

theorem acsM_len : DAM.acs.length ≤ 2 ^ 31 := by
  have h : DDM.acs = ComplJ8Data.acsP Nock.Field.p DDM.bigs DDM.dupP := rfl
  show DDM.acs.length ≤ 2 ^ 31
  rw [h, bigsM, dupPM]; decide +kernel

theorem callsM : DDM.calls = Nock.V1J8.Gen.callsOf rowsL := by
  have h : DDM.calls = Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tM) := rfl
  rw [h, rowsM]

theorem cellsM : DDM.cells = Nock.V1J8.Gen.cellsOfRoots DDM.roots := cells_gen genM

theorem jrowsM_len : DAM.jrows.length ≤ 2 ^ 31 := by
  show DDM.jrows.length ≤ 2 ^ 31
  have h : DDM.jrows.length = (Nock.Jet.ChipJ8.honestJ8G (ComplJ8Data.hJd Nock.Field.p DDM.cells DDM.acs) matRt
      DDM.regs DDM.calls).length := by
    simp only [DDM, j8DataOf, ComplJ8Data.mvFixP, List.length_map]
  have hr : DDM.regs = (DDM.calls.map Prod.fst).dedup := rfl
  rw [h, hr, callsM, cellsM, rootsM]
  have ha : DDM.acs = ComplJ8Data.acsP Nock.Field.p DDM.bigs DDM.dupP := rfl
  rw [ha, bigsM, dupPM]
  decide +kernel

theorem axOnM : ComplJ9ARun.axOnA tM = false := by
  unfold ComplJ9ARun.axOnA; rw [rows9M]; decide +kernel

theorem spOnM : ComplJ9ARun.spOnA Nock.Field.p tM = false := by
  unfold ComplJ9ARun.spOnA; rw [rows9M]; decide +kernel

theorem h31M : ComplJ9ARun.Rows31A DAM := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DAM.t]).length = 2 := by
    show (bfsForest [tM]).length = 2
    rw [bfsM]; rfl
  have hW : (VclL.GenWalk.walkRows DAM.cells DAM.reads).length ≤ 2 ^ 31 := by
    have := walk_bound DAM.cells DAM.reads (by rw [readsM]; intro x hx; simp at hx)
    rw [readsM] at this ⊢
    simp at this ⊢; omega
  have hV : ComplJ8Of.nVOf DAM = 1 := by simp [ComplJ8Of.nVOf, preadsDM]
  have hN : ComplJ9ARun.N9 DAM.t = 2 := by
    show ComplJ9ARun.N9 tM = 2
    rw [ComplJ9ARun.N9_def]
    show (bfsForest [ComplJ9AGen.genX9T tM]).length = 2
    rw [g9M, bfs2]; rfl
  have hX : ComplJ9ARun.nXOf Nock.Field.p DAM.acs.length DAM.H DAM.t = 1 := by
    show ComplJ9ARun.nXOf Nock.Field.p DAM.acs.length DAM.H tM = 1
    simp [ComplJ9ARun.nXOf, axOnM]
  have hS : ComplJ9ARun.nSOf Nock.Field.p DAM.t = 1 := by
    show ComplJ9ARun.nSOf Nock.Field.p tM = 1
    simp [ComplJ9ARun.nSOf, spOnM]
  have hC := cellsM_len
  have hJ := jrowsM_len
  have hA := acsM_len
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

theorem hpGM : Nock.Field.p = Nock.Atoms.p := rfl

/-- The generator's output on the matmul run. -/
theorem genM_L (χe : Nock.V1J8.Exe.CoinsE) :
    Nock.V1J9A.GenJ9AXJ.genJ9AXJ RgM.R matRt 2 toyS Demo.matProg χe =
      some (GenPortJ9AHJRun.recJ9AXJ matRt toyS Demo.matProg χe tM rM) := by
  rw [GenPortJ9AHJRun.genJ9AXJ_eq]
  have hr : Nock.V1J8.Gen.runX RgM.R 2 toyS Demo.matProg =
      some ⟨tM, rM, bfsForest [tM], ComplJ8Data.rowsOfT tM⟩ := by
    unfold Nock.V1J8.Gen.runX; rw [genM]; rfl
  rw [hr]
  rfl

/-- **`genLinkMat`: the input generator and the executable checker agree on a jetted `2 × 2` matrix multiplication,
with no hypothesis.**  For the program that calls the compiled `matmul` template of size `2` (registered as jet id
`7`) over the Goldilocks prime, there is a coin vector `χe` at which `genJ9AXJ` produces an input `I`, and
`checkJ9AX I = true`. -/
theorem genLinkMat : ∃ χe : Nock.V1J8.Exe.CoinsE, ∃ I : Nock.V1J9A.CheckJ9A.InJ9A,
    Nock.V1J9A.GenJ9AXJ.genJ9AXJ (Nock.V1J8.Gen.regOf matRt [7]) matRt 2 toyS Demo.matProg χe = some I ∧
      Nock.V1J9A.GenJ9AX.checkJ9AX I = true := by
  obtain ⟨χe, hχ⟩ := GenPortJ9AHGoodCoinJ.exists_good_coinEJ (Rg := RgM) (Rt := matRt) genM hpGM hax9M hop5M hleafM
    hwalk9M hwalkAM h31M hC_M
  exact ⟨χe, _, genM_L χe,
    GenPortJ9AHonestJ.checkJ9AX_genJ9AXJ genM hpGM hax9M hop5M hleafM hwalk9M hwalkAM h31M hC_M (genM_L χe) hχ⟩

end

end Nock.RedTeam.Batch4937

#print axioms Nock.RedTeam.Batch4937.genLinkMat
