import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree
import NockvmE2E.Z38.JpClaim
import Nock.RedTeam.Batch4936Thm54J9ALGenLinkToy
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue

set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.GenJp

open Nock Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP pcallsR)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.V1J8.Gen Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.V1J8.Exe (CoinsE)
open NockvmE2E.Z38.HF1LJ (sJ fJ)
open NockvmE2E.Z38.JpClaim (tplRes rJ fT7 fA8)
open NockvmE2E.Z38.CatJ (catJ TN)

def clueP7 : Noun := .cell (.atom 1) (.atom 7)
def clueP8 : Noun := .cell (.atom 1) (.atom 8)
def tC1 : NTree SkelX := mkX .s1 sJ clueP7 (.atom 7) []
def tC2 : NTree SkelX := mkX .s1 sJ clueP8 (.atom 8) []
def tJ1 : NTree SkelX := mkX .s11j sJ fT7 tplRes [tC1]
def tA1 : NTree SkelX := mkX .s11j sJ fA8 (.atom (Nock.Field.p + 8)) [tC2]
def tP : NTree SkelX := mkX .cons sJ fJ rJ [tJ1, tA1]

theorem hit8 : Nock.Edit.GenX.jetHit catJ.toVR.R (.atom Nock.Jet.wildTag) (.atom 8) (Nock.Jet.Prim.primC .add) sJ =
    some (.atom (Nock.Field.p + 8)) := by
  decide +kernel

theorem genP : genX catJ.toVR.R 4 sJ fJ = some (tP, rJ) := by
  have h1 : genX catJ.toVR.R 2 sJ clueP7 = some (tC1, .atom 7) := by
    simp [genX, genComputeSkeletonX, clueP7, tC1, mkX]
  have h2 : genX catJ.toVR.R 2 sJ clueP8 = some (tC2, .atom 8) := by
    simp [genX, genComputeSkeletonX, clueP8, tC2, mkX]
  have hj7 := NockvmE2E.Z38.JpClaim.hit7
  simp only [genX] at h1 h2
  simp only [genX, fJ, genComputeSkeletonX, clueP7, clueP8]
  simp only [clueP7] at h1
  simp only [clueP8] at h2
  simp only [h1, h2, hj7, hit8]
  rfl

theorem bfsP : bfsForest [tP] = [tP, tJ1, tA1, tC1, tC2] := by
  simp [bfsForest, tP, tJ1, tA1, tC1, tC2, mkX]


/-- the spelled run of `jp`: the WF `bfsForest` replaced by its five-element list -/
def Rn0 : RunX := ⟨tP, rJ, [tP, tJ1, tA1, tC1, tC2],
  #[rowOfSkelX tP.label, rowOfSkelX tJ1.label, rowOfSkelX tA1.label, rowOfSkelX tC1.label, rowOfSkelX tC2.label]⟩

theorem rowsP : ComplJ8Data.rowsOfT tP = #[rowOfSkelX tP.label, rowOfSkelX tJ1.label, rowOfSkelX tA1.label, rowOfSkelX tC1.label, rowOfSkelX tC2.label] := by
  simp only [ComplJ8Data.rowsOfT, bfsP]; rfl

theorem RnOf_eq : RnOf tP rJ = Rn0 := by
  unfold RnOf Rn0
  rw [bfsP, rowsP]

abbrev Rtt : ℕ → Nock.Jet.Autogen.Tpl := rtP catJ.toCR.Rt catJ.prims

def RS (χe : CoinsE) : Nock.V1J9AL.CheckJ9AL.InJ9AL := recJ9ALXJRn Rtt catJ.prims sJ fJ χe Rn0

theorem gen_RS (χe : CoinsE) :
    Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ catJ.toVR.R Rtt catJ.prims 4 sJ fJ χe = some (RS χe) := by
  rw [genJ9ALXJ_eq]
  have hr : runX catJ.toVR.R 4 sJ fJ = some (RnOf tP rJ) := by
    unfold runX; rw [genP]; rfl
  rw [hr]
  show some (recJ9ALXJRn Rtt catJ.prims sJ fJ χe (RnOf tP rJ)) = some (recJ9ALXJRn Rtt catJ.prims sJ fJ χe Rn0)
  rw [RnOf_eq]


/-! ## the J-9 A rows of the spelled run -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)

def gC9 : NTree LX9 := .node ⟨ComplJ9AGen.rowX9 tC1.label, .old, 0, 0, rowOfSkelX tC1.label⟩ []
def gC9b : NTree LX9 := .node ⟨ComplJ9AGen.rowX9 tC2.label, .old, 0, 0, rowOfSkelX tC2.label⟩ []
def gJ9 : NTree LX9 := .node ⟨ComplJ9AGen.rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩ [gC9]
def gA9 : NTree LX9 := .node ⟨ComplJ9AGen.rowX9 tA1.label, .old, 0, 0, rowOfSkelX tA1.label⟩ [gC9b]
def gP9 : NTree LX9 := .node ⟨ComplJ9AGen.rowX9 tP.label, .old, 0, 0, rowOfSkelX tP.label⟩ [gJ9, gA9]

theorem chipC1 : ComplJ9AGen.chipOf tC1.label = (.old, 0) := by decide
theorem chipC2 : ComplJ9AGen.chipOf tC2.label = (.old, 0) := by decide
theorem chipJ1 : ComplJ9AGen.chipOf tJ1.label = (.old, 0) := by decide
theorem chipA1 : ComplJ9AGen.chipOf tA1.label = (.old, 0) := by decide
theorem chipP : ComplJ9AGen.chipOf tP.label = (.old, 0) := by decide

theorem genX9T_P : ComplJ9AGen.genX9T tP = gP9 := by
  have hC : ComplJ9AGen.genX9T tC1 = gC9 := by
    show ComplJ9AGen.genX9T (.node tC1.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipC1]; rfl
  have hC2 : ComplJ9AGen.genX9T tC2 = gC9b := by
    show ComplJ9AGen.genX9T (.node tC2.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipC2]; rfl
  have hJ : ComplJ9AGen.genX9T tJ1 = gJ9 := by
    show ComplJ9AGen.genX9T (.node tJ1.label [tC1]) = _
    rw [ComplJ9AGen.genX9T_node, chipJ1]
    simp only [List.map_cons, List.map_nil, hC, ComplJ9AGen.kid9, chipJ1, gJ9]
    simp
  have hA : ComplJ9AGen.genX9T tA1 = gA9 := by
    show ComplJ9AGen.genX9T (.node tA1.label [tC2]) = _
    rw [ComplJ9AGen.genX9T_node, chipA1]
    simp only [List.map_cons, List.map_nil, hC2, ComplJ9AGen.kid9, chipA1, gA9]
    simp
  show ComplJ9AGen.genX9T (.node tP.label [tJ1, tA1]) = _
  rw [ComplJ9AGen.genX9T_node, chipP]
  simp only [List.map_cons, List.map_nil, hJ, hA, ComplJ9AGen.kid9, chipP, gP9]
  simp

theorem bfs9P : bfsForest [gP9] = [gP9, gJ9, gA9, gC9, gC9b] := by
  simp [bfsForest, gP9, gJ9, gA9, gC9, gC9b]

theorem rows9P : ComplJ9AGen.rowsOfT9 tP =
    #[⟨ComplJ9AGen.rowX9 tP.label, .old, 0, 0, rowOfSkelX tP.label⟩, ⟨ComplJ9AGen.rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩,
      ⟨ComplJ9AGen.rowX9 tA1.label, .old, 0, 0, rowOfSkelX tA1.label⟩, ⟨ComplJ9AGen.rowX9 tC1.label, .old, 0, 0, rowOfSkelX tC1.label⟩,
      ⟨ComplJ9AGen.rowX9 tC2.label, .old, 0, 0, rowOfSkelX tC2.label⟩] := by
  simp only [ComplJ9AGen.rowsOfT9, genX9T_P, bfs9P]; rfl

theorem hR' (χe : CoinsE) : rows9J sJ fJ χe Rn0 =
    #[⟨ComplJ9AGen.rowX9 tP.label, .old, 0, 0, rowOfSkelX tP.label⟩, ⟨ComplJ9AGen.rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩,
      ⟨ComplJ9AGen.rowX9 tA1.label, .old, 0, 0, rowOfSkelX tA1.label⟩, ⟨ComplJ9AGen.rowX9 tC1.label, .old, 0, 0, rowOfSkelX tC1.label⟩,
      ⟨ComplJ9AGen.rowX9 tC2.label, .old, 0, 0, rowOfSkelX tC2.label⟩] :=
  (show rows9J sJ fJ χe Rn0 = ComplJ9AGen.rowsOfT9 tP from rfl).trans rows9P

theorem hW' (χe : CoinsE) : W9J sJ fJ χe Rn0 = [gP9, gJ9, gA9, gC9, gC9b] :=
  (show W9J sJ fJ χe Rn0 = bfsForest [ComplJ9AGen.genX9T tP] from rfl).trans (by rw [genX9T_P]; exact bfs9P)


/-! ## sizes of the record, for every coins (cheap ones first) -/

macro "spell" : tactic => `(tactic| simp only [cK, callsK, idsK, regsK, jnK, rootsK, csK, acsK, HK, ptK, pdK, idOfK, compK, wsKrK, idxK, layK,
  jrowsK, jgK, mvK, mxK, mx1K, mhK, cRPK, wRPK, readsK, vsKrVK, HAK, rIAK, aRPK, vRPK, xRPK, sRPK, mK, BK, callsJLK, idsJLK, regsJLK, psCLK, pcLK,
  layLK, jrowsLK, jgLK, mvLK, mhLK, cRPLK, mbLK, aRPLK, aluOnLK, lRPLK, mLK, BLK, ovlJ, RS, recJ9ALXJRn, recJ9AXJRn, fxJ, axOnJ, spOnJ, hR', hW'])

/-- the sorted big atoms of the run: `mergeSort` is WF (kernel-stuck), so spelled through sortedness + permutation -/
theorem ms (l : List ℕ) (h : l.Perm [P + 5, P + 8]) :
    l.mergeSort (fun a b => decide (a ≤ b)) = [P + 5, P + 8] := by
  have h1 := List.mergeSort_perm l (fun a b => decide (a ≤ b))
  have h2 := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b)) (l := l)
    (by intro a b c hab hbc; simp at *; omega) (by intro a b; simp; omega)
  have h3 : ([P + 5, P + 8] : List ℕ).Pairwise (fun a b => decide (a ≤ b) = true) := by
    simp [P, Nock.Field.p]
  exact List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
    (by intro a _ b _ hab hba; simp at hab hba; omega) h2 h3 (h1.trans h)

theorem bigsP : bigsOf (rootsOf { subject := sJ, formula := fJ, result := Rn0.res } Rn0.rows ++
      ComplJ8Data.jNounsP P Rtt (List.map Prod.fst (callsOf Rn0.rows)).dedup (callsOf Rn0.rows)) Rn0.rows =
    [P + 5, P + 8] := by
  unfold bigsOf
  have : ((((rootsOf { subject := sJ, formula := fJ, result := Rn0.res } Rn0.rows ++
      ComplJ8Data.jNounsP P Rtt (List.map Prod.fst (callsOf Rn0.rows)).dedup (callsOf Rn0.rows)) ++
      Rn0.rows.toList.flatMap rowHandleNounsX).flatMap leavesOf |>.filter fun a => decide (P ≤ a)).dedup).Perm
      [P + 5, P + 8] := by decide +kernel
  exact ms _ this

theorem sz_V (χe : CoinsE) : (RS χe).V.n = 1 := by
  spell
  rw [bigsP]
  rfl

theorem sz_X (χe : CoinsE) : (RS χe).X.n = 5 := by spell; rfl
theorem readsP : ComplJ9AReads.walkReadsX9 #[⟨ComplJ9AGen.rowX9 tP.label, .old, 0, 0, rowOfSkelX tP.label⟩, ⟨ComplJ9AGen.rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩,
      ⟨ComplJ9AGen.rowX9 tA1.label, .old, 0, 0, rowOfSkelX tA1.label⟩, ⟨ComplJ9AGen.rowX9 tC1.label, .old, 0, 0, rowOfSkelX tC1.label⟩,
      ⟨ComplJ9AGen.rowX9 tC2.label, .old, 0, 0, rowOfSkelX tC2.label⟩] ++
    ComplJ9AChainsRun.axChainReadsK9 #[⟨ComplJ9AGen.rowX9 tP.label, .old, 0, 0, rowOfSkelX tP.label⟩, ⟨ComplJ9AGen.rowX9 tJ1.label, .old, 0, 0, rowOfSkelX tJ1.label⟩,
      ⟨ComplJ9AGen.rowX9 tA1.label, .old, 0, 0, rowOfSkelX tA1.label⟩, ⟨ComplJ9AGen.rowX9 tC1.label, .old, 0, 0, rowOfSkelX tC1.label⟩,
      ⟨ComplJ9AGen.rowX9 tC2.label, .old, 0, 0, rowOfSkelX tC2.label⟩] = [] := by
  decide +kernel

theorem sz_W (χe : CoinsE) : (RS χe).W.n = 1 := by
  spell
  rw [bigsP, readsP]
  show (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size = 1
  rw [GenPortJ9AHWalkGlue.walkGenRowsB_size]
  decide +kernel
theorem sz_AX (χe : CoinsE) : (RS χe).AX.n = 1 := by spell; rfl
theorem sz_SP (χe : CoinsE) : (RS χe).SP.n = 1 := by spell; rfl
theorem fl_kr (χe : CoinsE) : (RS χe).kroots = 1 := by spell; rfl
theorem fl_krV (χe : CoinsE) : (RS χe).krootsV = 0 := by spell; rfl
theorem fl_ax (χe : CoinsE) : (RS χe).axOn = false := by spell; rfl
theorem fl_sp (χe : CoinsE) : (RS χe).spOn = false := by spell; rfl
theorem fl_on (χe : CoinsE) : (RS χe).aluOn = true := by spell; rfl
theorem fl_prims (χe : CoinsE) : (RS χe).prims = catJ.prims := by spell; rfl
theorem fl_regs (χe : CoinsE) : (RS χe).regs = [7] := by spell; rfl
theorem fl_ids (χe : CoinsE) : (RS χe).ids = [7] := by spell; rfl


theorem L2 (ptr : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    (atomGenE ptr χe acsL info mb mxA mhA).1.size = acsL.length := by
  simp [atomGenE]

theorem sz_A (χe : CoinsE) : (RS χe).A.n = 3 := by
  show (atomGenE _ _ _ _ _ _ _).1.size = 3
  rw [L2]
  spell
  rw [bigsP]
  decide +kernel

theorem sz_J (χe : CoinsE) : (RS χe).J.n = 17 := by
  spell
  decide +kernel


theorem hon_RS (χe : CoinsE) : aluOnLK Rtt catJ.prims sJ fJ χe Rn0 = true := by
  show (!(pcallsR (List.map Prod.fst catJ.prims) Rn0.rows).isEmpty) = true
  decide +kernel

theorem sz_C (χe : CoinsE) : (RS χe).C.n = 159 := by
  spell
  show (cellGenB _ _ _ _ _ _ _ _ _).1.size = 159
  rw [GenPortJ9AHCell.cellGenB_size]
  decide +kernel

theorem sz_AL (χe : CoinsE) : (RS χe).AL.n = 12 := by
  show (chipOf (lRPLK Rtt catJ.prims sJ fJ χe Rn0).1).n = 12
  unfold lRPLK
  rw [if_pos (hon_RS χe)]
  show (Nock.V1J9AL.GenAluE.aluGenE χe _ _ _ _ _).1.size = 12
  rw [GenPortJ9ALHAluE.aluGenE_size]
  spell
  rw [bigsP]
  decide +kernel


theorem fl_g (χe : CoinsE) : (RS χe).g = 1 := by spell; rfl
theorem fl_idx (χe : CoinsE) : (RS χe).idx 7 = 6 := by spell; decide +kernel
theorem fl_rk (χe : CoinsE) : (RS χe).rk 7 = (0, 190) := by spell; decide +kernel
theorem fl_idxP (χe : CoinsE) : (RS χe).idxP 8 = 124 := by spell; decide +kernel
theorem fl_rkP (χe : CoinsE) : (RS χe).rkP 8 = (0, 43) := by spell; rfl

theorem c_X (χe : CoinsE) : (compK Rtt sJ fJ χe Rn0).rows.size = 5 := by spell; rfl
theorem c_C (χe : CoinsE) : (cRPLK Rtt catJ.prims sJ fJ χe Rn0).1.size = 159 := by
  unfold cRPLK
  spell
  rw [GenPortJ9AHCell.cellGenB_size]
  decide +kernel
theorem c_W (χe : CoinsE) : (wRPK Rtt sJ fJ χe Rn0).1.size = 1 := by
  spell
  rw [bigsP, readsP]
  rw [GenPortJ9AHWalkGlue.walkGenRowsB_size]
  decide +kernel
theorem c_A (χe : CoinsE) : (aRPLK Rtt catJ.prims sJ fJ χe Rn0).1.size = 3 := by
  unfold aRPLK
  rw [L2]
  spell
  rw [bigsP]
  decide +kernel
theorem c_V (χe : CoinsE) : (vRPK Rtt sJ fJ χe Rn0).1.size = 1 := by spell; rw [bigsP]; rfl
theorem c_AX (χe : CoinsE) : (xRPK Rtt sJ fJ χe Rn0).1.size = 1 := by spell; rw [bigsP]; rfl
theorem c_SP (χe : CoinsE) : (sRPK Rtt sJ fJ χe Rn0).1.size = 1 := by spell; rw [bigsP]; rfl
theorem c_lay (χe : CoinsE) : (layLK Rtt catJ.prims sJ fJ χe Rn0).length = 17 := by spell; decide +kernel
theorem c_AL (χe : CoinsE) : (lRPLK Rtt catJ.prims sJ fJ χe Rn0).1.size = 12 := sz_AL χe

theorem m_RS (χe : CoinsE) : mLK Rtt catJ.prims sJ fJ χe Rn0 = 159 := by
  unfold mLK
  rw [c_X, c_C, c_W, c_A, c_V, c_AX, c_SP, c_lay, c_AL]
  decide

theorem BLK_RS (χe : CoinsE) : BLK Rtt catJ.prims sJ fJ χe Rn0 = 318 := by
  unfold BLK
  rw [m_RS]
  decide

theorem rows_RS (χe : CoinsE) : (RS χe).toRowsL = ⟨⟨budget 159, 318, 318⟩, 318⟩ := by
  show (⟨⟨budget (mLK Rtt catJ.prims sJ fJ χe Rn0), BLK Rtt catJ.prims sJ fJ χe Rn0, BLK Rtt catJ.prims sJ fJ χe Rn0⟩,
    BLK Rtt catJ.prims sJ fJ χe Rn0⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL.RowsJ9AL) = _
  rw [m_RS, BLK_RS]

end NockvmE2E.Z38.GenJp
