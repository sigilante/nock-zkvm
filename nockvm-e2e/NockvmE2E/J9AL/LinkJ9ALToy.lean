/-
the AIR-side bridge of the executed `add` instance, modulo the named hypothesis `HF1L`
[nock-pending].  Twin of `J9A/LinkJ9AToy.lean` (`toy9_air`).  No literal file is imported: the instance `XI` is a VARIABLE, constrained by the explicit
shape hypothesis `AddShape XI` (the tables' row counts, presence flags and prim record of the executed `add.inst.json`, to be discharged at the literal
by `decide`).

  1. §1 `Rn0`, the spelled run of Batch4936's `add` program (`RnOf tT rT = Rn0`: the WF `bfsForest` replaced by its two-element list), the spelled
     J-9 A rows `rows9T` / `bfs9T` (nock's `ComplJ9ALToyFacts`), and `bigsT` (the `mergeSort` of the three big atoms, spelled).
  2. §2 sizes of nock's generator record `recJ9ALXJ` at the add program, FOR EVERY COINS `χe` (the table sizes, root counts, flags, `prims`, the pin
     functions at the one primitive, `regs = ids = []`, `g = 0`, the row budget `m = 117`).
  3. §3 `HF1L XI`: the conclusion shape of nock's `genJ9ALXJ_honest_at` at the shared orbit `orbSh XI`  [nock-pending: nockvm adds
     `genJ9ALXJ_honest_at'` with `OrbAdmL'` = `OrbAdmL` minus `ALh`].
  4. §4 `add_air`: `AccJ9AL ∧ PubP9AL` at `DX9L XI … cAdd` from `HF1L XI`, the instance shape, and the instance gates `hsh`, `hpreg`, `hrt`.

Labels: [kernel] = checked by the Lean kernel; [nock-pending] = the named hypothesis `HF1L`; [instance] = instance-side hypotheses, executed gates at
the literal.  Not zero-knowledge.
-/
import Nock.RedTeam.Batch4936Thm54J9ALGenLinkToy
import NockvmE2E.J9AL.LinkJ9ALBridge
import NockvmE2E.J9AL.AccCongJ9AL
import NockvmE2E.J9AL.AccMonoJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.LinkJ9ALToy

/-! ## 1. the spelled run -/

section Gen
open Nock Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP pcallsR)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.RedTeam.Batch4921 (Rt0T)
open Nock.RedTeam.Batch4936 (primsT)
open Nock.V1J8.Gen Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.V1J8.Exe (CoinsE)

/-- the run of the add program with the WF `bfsForest` spelled (`bfsT`, `rowsT`) -/
def Rn0 : RunX := ⟨tT, rT, [tT, tD], #[rowOfSkelX tT.label, rowOfSkelX tD.label]⟩

theorem RnOf_eq : RnOf tT rT = Rn0 := by
  unfold RnOf Rn0
  rw [bfsT, rowsT]

abbrev Rtt : ℕ → Nock.Jet.Autogen.Tpl := rtP Rt0T primsT

/-- the generator's record, over the spelled run -/
def RS (χe : CoinsE) : Nock.V1J9AL.CheckJ9AL.InJ9AL := recJ9ALXJRn Rtt primsT sT fT χe Rn0

/-- **[kernel] `genJ9ALXJ` on the add program is the record over `Rn0`** (any coins) -/
theorem gen_RS (χe : CoinsE) : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ RgT.R Rtt primsT 2 sT fT χe = some (RS χe) := by
  rw [Nock.RedTeam.Batch4936.genT_L]
  show some (recJ9ALXJRn Rtt primsT sT fT χe (RnOf tT rT)) = some (recJ9ALXJRn Rtt primsT sT fT χe Rn0)
  rw [RnOf_eq]

theorem hR' (χe : CoinsE) : rows9J sT fT χe Rn0 = #[⟨ComplJ9AGen.rowX9 tT.label, .old, 0, 0, rowOfSkelX tT.label⟩,
      ⟨ComplJ9AGen.rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩] :=
  (show rows9J sT fT χe Rn0 = ComplJ9AGen.rowsOfT9 tT from rfl).trans rows9T

theorem hW' (χe : CoinsE) : W9J sT fT χe Rn0 = [gT9, .node ⟨ComplJ9AGen.rowX9 tD.label, .old, 0, 0, rowOfSkelX tD.label⟩ []] :=
  ((show W9J sT fT χe Rn0 = bfsForest [ComplJ9AGen.genX9T tT] from rfl).trans (by rw [genX9T_T])).trans bfs9T

/-- the sorted big atoms of the run: `mergeSort` is WF (kernel-stuck), so spelled through sortedness + permutation -/
theorem ms (l : List ℕ) (h : l.Perm [P + 5, P + 7, 2 * P + 12]) :
    l.mergeSort (fun a b => decide (a ≤ b)) = [P + 5, P + 7, 2 * P + 12] := by
  have h1 := List.mergeSort_perm l (fun a b => decide (a ≤ b))
  have h2 := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b)) (l := l)
    (by intro a b c hab hbc; simp at *; omega) (by intro a b; simp; omega)
  have h3 : ([P + 5, P + 7, 2 * P + 12] : List ℕ).Pairwise (fun a b => decide (a ≤ b) = true) := by
    simp [P, Nock.Field.p]
  exact List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
    (by intro a _ b _ hab hba; simp at hab hba; omega) h2 h3 (h1.trans h)

theorem bigsT : bigsOf (rootsOf { subject := sT, formula := fT, result := Rn0.res } Rn0.rows ++
      ComplJ8Data.jNounsP P Rtt (List.map Prod.fst (callsOf Rn0.rows)).dedup (callsOf Rn0.rows)) Rn0.rows =
    [P + 5, P + 7, 2 * P + 12] := by
  unfold bigsOf
  have : ((((rootsOf { subject := sT, formula := fT, result := Rn0.res } Rn0.rows ++
      ComplJ8Data.jNounsP P Rtt (List.map Prod.fst (callsOf Rn0.rows)).dedup (callsOf Rn0.rows)) ++
      Rn0.rows.toList.flatMap rowHandleNounsX).flatMap leavesOf |>.filter fun a => decide (P ≤ a)).dedup).Perm
      [P + 5, P + 7, 2 * P + 12] := by decide +kernel
  exact ms _ this

theorem L2 (ptr : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    (atomGenE ptr χe acsL info mb mxA mhA).1.size = acsL.length := by
  simp [atomGenE]

/-! ## 2. sizes of the record, for every coins -/

macro "spell" : tactic => `(tactic| simp only [cK, callsK, idsK, regsK, jnK, rootsK, csK, acsK, HK, ptK, pdK, idOfK, compK, wsKrK, idxK, layK,
  jrowsK, jgK, mvK, mxK, mx1K, mhK, cRPK, wRPK, readsK, vsKrVK, HAK, rIAK, aRPK, vRPK, xRPK, sRPK, mK, BK, callsJLK, idsJLK, regsJLK, psCLK, pcLK,
  layLK, jrowsLK, jgLK, mvLK, mhLK, cRPLK, mbLK, aRPLK, aluOnLK, lRPLK, mLK, BLK, ovlJ, RS, recJ9ALXJRn, recJ9AXJRn, fxJ, axOnJ, spOnJ, hR', hW'])

theorem hon_RS (χe : CoinsE) : aluOnLK Rtt primsT sT fT χe Rn0 = true := by
  show (!(pcallsR (List.map Prod.fst primsT) Rn0.rows).isEmpty) = true
  decide +kernel

theorem sz_AL (χe : CoinsE) : (RS χe).AL.n = 12 := by
  show (chipOf (lRPLK Rtt primsT sT fT χe Rn0).1).n = 12
  unfold lRPLK
  rw [if_pos (hon_RS χe)]
  show (Nock.V1J9AL.GenAluE.aluGenE χe _ _ _ _ _).1.size = 12
  rw [GenPortJ9ALHAluE.aluGenE_size]
  spell
  decide +kernel

theorem sz_X (χe : CoinsE) : (RS χe).X.n = 2 := by spell; rfl
theorem sz_C (χe : CoinsE) : (RS χe).C.n = 117 := by spell; rfl
theorem sz_W (χe : CoinsE) : (RS χe).W.n = 1 := by spell; rfl
theorem sz_A (χe : CoinsE) : (RS χe).A.n = 5 := by
  show (atomGenE _ _ _ _ _ _ _).1.size = 5
  rw [L2]
  spell
  rw [bigsT]
  decide +kernel
theorem sz_V (χe : CoinsE) : (RS χe).V.n = 1 := by spell; rfl
theorem sz_AX (χe : CoinsE) : (RS χe).AX.n = 1 := by spell; rfl
theorem sz_SP (χe : CoinsE) : (RS χe).SP.n = 1 := by spell; rfl
theorem sz_J (χe : CoinsE) : (RS χe).J.n = 0 := by spell; rfl
theorem fl_kr (χe : CoinsE) : (RS χe).kroots = 1 := by spell; rfl
theorem fl_krV (χe : CoinsE) : (RS χe).krootsV = 0 := by spell; rfl
theorem fl_ax (χe : CoinsE) : (RS χe).axOn = false := by spell; rfl
theorem fl_sp (χe : CoinsE) : (RS χe).spOn = false := by spell; rfl
theorem fl_on (χe : CoinsE) : (RS χe).aluOn = true := by spell; rfl
theorem fl_regs (χe : CoinsE) : (RS χe).regs = [] := by spell; rfl
theorem fl_ids (χe : CoinsE) : (RS χe).ids = [] := by spell; rfl
theorem fl_prims (χe : CoinsE) : (RS χe).prims = primsT := by spell; rfl
theorem fl_idxP (χe : CoinsE) : (RS χe).idxP 7 = 5 := by spell; rfl
theorem fl_rkP (χe : CoinsE) : (RS χe).rkP 7 = (0, 43) := by spell; rfl
theorem fl_g (χe : CoinsE) : (RS χe).g = 0 := by spell; rfl

theorem c_X (χe : CoinsE) : (compK Rtt sT fT χe Rn0).rows.size = 2 := by spell; rfl
theorem c_C (χe : CoinsE) : (cRPLK Rtt primsT sT fT χe Rn0).1.size = 117 := by spell; rfl
theorem c_W (χe : CoinsE) : (wRPK Rtt sT fT χe Rn0).1.size = 1 := by spell; rfl
theorem c_A (χe : CoinsE) : (aRPLK Rtt primsT sT fT χe Rn0).1.size = 5 := by
  unfold aRPLK
  rw [L2]
  spell
  rw [bigsT]
  decide +kernel
theorem c_V (χe : CoinsE) : (vRPK Rtt sT fT χe Rn0).1.size = 1 := by spell; rfl
theorem c_AX (χe : CoinsE) : (xRPK Rtt sT fT χe Rn0).1.size = 1 := by spell; rfl
theorem c_SP (χe : CoinsE) : (sRPK Rtt sT fT χe Rn0).1.size = 1 := by spell; rfl
theorem c_lay (χe : CoinsE) : (layLK Rtt primsT sT fT χe Rn0).length = 0 := by spell; rfl
theorem c_AL (χe : CoinsE) : (lRPLK Rtt primsT sT fT χe Rn0).1.size = 12 := sz_AL χe

/-- **[kernel] the row budget of the record is `m = 117`, i.e. `budget 117` (every row parameter `234`)**, for every coins -/
theorem m_RS (χe : CoinsE) : mLK Rtt primsT sT fT χe Rn0 = 117 := by
  unfold mLK
  rw [c_X, c_C, c_W, c_A, c_V, c_AX, c_SP, c_lay, c_AL]
  decide

theorem BLK_RS (χe : CoinsE) : BLK Rtt primsT sT fT χe Rn0 = 234 := by
  unfold BLK
  rw [m_RS]
  decide

/-- the rows of the record: every parameter is `234` -/
theorem rows_RS (χe : CoinsE) :
    (RS χe).toRowsL = ⟨⟨budget 117, 234, 234⟩, 234⟩ := by
  show (⟨⟨budget (mLK Rtt primsT sT fT χe Rn0), BLK Rtt primsT sT fT χe Rn0, BLK Rtt primsT sT fT χe Rn0⟩,
    BLK Rtt primsT sT fT χe Rn0⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL.RowsJ9AL) = _
  rw [m_RS, BLK_RS]

end Gen

/-! ## 3. `HF1L` and 4. `add_air` -/

section Air
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9ALChips
open NockvmE2E.J8.InstJ8 (tabOf hNof tplDummy P)
open NockvmE2E.J8.DatXOk (layNil)
open NockvmE2E.J9A.PbOfX9 (nOpt)
open NockvmE2E.J9AL.PbOfX9L (primsOf idxPOf rkPOf PbOfX9L)
open NockvmE2E.J9AL.InstJ9AL (AccJ9AL PubP9AL stmt_pub_of_acc9L)
open NockvmE2E.J9AL.DatX9LOk (DX9L)
open NockvmE2E.J9AL.LinkJ9ALBridge (orbSh mkPbAL_withOrbL_eq preL_interp_eq heq_of_zero)
open NockvmE2E.J9AL.AccCongJ9AL (acceptsJ9AL_congr_reg0)
open NockvmE2E.J9AL.AccMonoJ9AL (acceptsJ9AL_mono_rows)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (cornerC9L PubJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALToyFacts (sT fT rT RgT idAdd)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (withOrbL)
open Nock.V1J9AL.CheckJ9AL (InJ9AL)
open Nock.V1J9AL.CheckJ9ALIff (ValidJ9AL mkPbAL)
open Nock.RedTeam.Batch4921 (Rt0T)
open Nock.RedTeam.Batch4936 (primsT)
open Nock.TraceGenExe (deltaF powerBasis3)
open Nock.V1J8.Exe (CoinsE)
open Nock.V1J8.Gen (budget)

noncomputable section

/-- the public claim of the executed `add` instance: `*[[(p+5) (p+7)] [11 [%wild [1 7]] (primC add)]] = 2p+12` -/
def cAddB : P8PublicClaim := ⟨sT, fT, rT⟩

/-- **`HF1L XI`, the named hypothesis [nock-pending]**: the conclusion shape of nockvm's `genJ9ALXJ_honest_at'` (= `genJ9ALXJ_honest_at` with `OrbAdmL'`
:= `OrbAdmL` minus `ALh`) at the add program (`Batch4936`'s `RgT`, `rtP Rt0T primsT`, `primsT`, fuel `2`, `sT`, `fT`) and at the shared orbit `orbSh XI` =
`(k+1, ofU64 hGen)` for every chip: for SOME coins `χe`, `genJ9ALXJ` returns `I`, and `AcceptsJ9AL` holds of the generator's record moved onto that orbit
(`I' := withOrbL I (orbSh XI)`), at `mkPbAL I' hv`, `I'.c`, `toχ I'.χ`, `I'.toMsgL`, `I'.toTrL`, `I'.toRowsL`, `I'.g`.  Not an axiom: a `def`'d `Prop`
passed as an argument.  It is closed with ONE `exact`: `genJ9ALXJ_honest_at'` at `Batch4936.genT_L`'s record, a good coin from `exists_good_coinEJL`, and
`OrbAdmL' I (orbSh XI)` (sizes `≤ 3 * 2^(k+1)`, order `3 * 2^(k+1)`, as `orbToy_ok`). -/
def HF1L (XI : ExecInst) : Prop :=
  ∃ (χe : CoinsE) (I : InJ9AL), Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ RgT.R (rtP Rt0T primsT) primsT 2 sT fT χe = some I ∧
    ∃ hv : ValidJ9AL (withOrbL I (orbSh XI)),
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I (orbSh XI)) hv) RgT.R
        (withOrbL I (orbSh XI)).c (Nock.V1J8.Exe.toχ (withOrbL I (orbSh XI)).χ) (withOrbL I (orbSh XI)).toMsgL
        (withOrbL I (orbSh XI)).toTrL (withOrbL I (orbSh XI)).toRowsL (withOrbL I (orbSh XI)).g

/-- **[instance] the shape of the executed `add` instance** (to be discharged at the literal `addALR` by `decide`, per table, as `hNof_toy`): table row counts
`[X 2, C 117, W 1, A 5, AL 12]`, the three optional tables absent (`n = 1`, flag off) except the ALU, the one prim record `(7, add)`
with pin index `5` and rank limbs `(0, 43)`. -/
def AddShape (XI : ExecInst) : Prop :=
  hNof XI "computeChipVCLHX9" = 2 ∧ hNof XI "cellChipHQKW" = 117 ∧ hNof XI "walkChipJ8" = 1 ∧ hNof XI "atomChipHQL" = 5 ∧
  nOpt XI "walkChipHQK" = 1 ∧ nOpt XI "axisChipJ9" = 1 ∧ nOpt XI "splitChipJ9" = 1 ∧ nOpt XI "aluChipJ9" = 12 ∧
  (tabOf XI "axisChipJ9").isSome = false ∧ (tabOf XI "splitChipJ9").isSome = false ∧ (tabOf XI "aluChipJ9").isSome = true ∧
  primsOf XI = primsT ∧ idxPOf XI 7 = 5 ∧ rkPOf XI 7 = (0, 43)

open NockvmE2E.J9AL.PbOfX9L in
theorem wOrbL_rows (I : InJ9AL) (o : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbJ9AL) :
    (withOrbL I o).toRowsL = I.toRowsL := rfl
theorem wOrbL_g (I : InJ9AL) (o : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbJ9AL) : (withOrbL I o).g = I.g := rfl
theorem wOrbL_c (I : InJ9AL) (o : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbJ9AL) : (withOrbL I o).c = I.c := rfl
theorem RS_c (χe : CoinsE) : (RS χe).c = cAddB := rfl

theorem prims_Pb (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow) :
    (PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay).prims = primsOf XI := rfl

set_option maxHeartbeats 1000000 in
/-- **`add_air`** [kernel, modulo `HF1L` (nock-pending), and the instance hypotheses `hsh hpreg hrt hJ AddShape`]: at the executed add datum
`DX9L XI … cAddB` (`kroots = 1`, `krootsV = 0`), `AccJ9AL` and `PubP9AL` hold, with the generator's own trace. -/
theorem add_air (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (hJ : hNof XI "jetChipJ8" = 0) (hS : AddShape XI)
    (hpreg : NockvmE2E.J9A.RunGate9L.pregOkF XI = true) (hrt : NockvmE2E.J9A.RunGate9L.primsRoundTrip XI.pubIn.prims = true)
    (hF : HF1L XI) :
    ∃ χ M tr,
      AccJ9AL (DX9L XI hsh hJ 1 0 cAddB) χ M tr ∧
      PubP9AL (DX9L XI hsh hJ 1 0 cAddB) χ (M, fun j => pubVJ9 deltaF powerBasis3 cAddB M.m M.ρ M.ρS χ j) := by
  obtain ⟨hX, hC, hW, hA, hV, hAXs, hSPs, hALs, hax, hsp, hon, hpp, hix, hrk⟩ := hS
  obtain ⟨χe, I, hgen, hv, hacc⟩ := hF
  rw [gen_RS] at hgen
  have hI : RS χe = I := Option.some.inj hgen
  subst hI
  have hbr := mkPbAL_withOrbL_eq XI hsh 1 0 (RS χe).Rt [] [] (RS χe).idx (RS χe).rk (layNil XI hJ) (RS χe) hv
    (by rw [sz_X, hX]) (by rw [sz_C, hC]) (by rw [sz_W, hW]) (by rw [sz_J, hJ]) (by rw [sz_A, hA]) (by rw [sz_V, hV])
    (by rw [sz_AX, hAXs]) (by rw [sz_SP, hSPs]) (by rw [sz_AL, hALs]) (fl_kr χe) (by rw [fl_krV]; simp) rfl (fl_regs χe) (fl_ids χe) rfl rfl
    (heq_of_zero _ _ (sz_J χe) hJ _ _) (by rw [fl_ax, hax]) (by rw [fl_sp, hsp]) (by rw [fl_on, hon]) (by rw [fl_prims, hpp])
    (fun k => preL_interp_eq XI hsh hpreg hrt hon k)
  rw [hbr] at hacc
  generalize hPb1 : ({ PbOfX9L XI hsh 1 0 (RS χe).Rt [] [] (RS χe).idx (RS χe).rk (layNil XI hJ) with idxP := (RS χe).idxP, rkP := (RS χe).rkP } : PubJ9AL P) = Pb1 at hacc
  have e_prims : Pb1.prims = primsOf XI := by rw [← hPb1]; rfl
  have e_idxP : Pb1.idxP = (RS χe).idxP := by rw [← hPb1]
  have e_rkP : Pb1.rkP = (RS χe).rkP := by rw [← hPb1]
  have e_regs : Pb1.regs = [] := by rw [← hPb1]; rfl
  have e_ids : Pb1.ids = [] := by rw [← hPb1]; rfl
  have eP : (DX9L XI hsh hJ 1 0 cAddB).Pb = { Pb1 with Rt := fun _ => tplDummy, idx := fun _ => 0, rk := fun _ => (0, 0), idxP := idxPOf XI, rkP := rkPOf XI } := by rw [← hPb1]; rfl
  have hiP' : ∀ q ∈ primsT, idxPOf XI q.1 = (RS χe).idxP q.1 := by
    intro q hq
    obtain rfl : q = (idAdd, .add) := by simpa using hq
    show idxPOf XI 7 = (RS χe).idxP 7
    rw [hix, fl_idxP]
  have hrP' : ∀ q ∈ primsT, rkPOf XI q.1 = (RS χe).rkP q.1 := by
    intro q hq
    obtain rfl : q = (idAdd, .add) := by simpa using hq
    show rkPOf XI 7 = (RS χe).rkP 7
    rw [hrk, fl_rkP]
  have hacc2 := acceptsJ9AL_congr_reg0 deltaF powerBasis3 (fun _ => tplDummy) (fun _ => 0) (fun _ => (0, 0)) (idxPOf XI) (rkPOf XI)
    e_regs e_ids
    (fun q hq => by rw [e_idxP]; exact hiP' q (by rw [e_prims, hpp] at hq; exact hq))
    (fun q hq => by rw [e_rkP]; exact hrP' q (by rw [e_prims, hpp] at hq; exact hq)) hacc
  have hrows : (withOrbL (RS χe) (orbSh XI)).toRowsL = ⟨⟨budget 117, 234, 234⟩, 234⟩ :=
    (wOrbL_rows _ _).trans (rows_RS χe)
  have hg : (withOrbL (RS χe) (orbSh XI)).g = 0 := (wOrbL_g _ _).trans (fl_g χe)
  rw [hrows, hg] at hacc2
  have hacc3 := acceptsJ9AL_mono_rows deltaF powerBasis3 hacc2 (r' := cornerC9L) (g' := 2 ^ 31)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Nat.zero_le _)
  have hc : (withOrbL (RS χe) (orbSh XI)).c = cAddB := (wOrbL_c _ _).trans (RS_c χe)
  rw [hc] at hacc3
  have hRg : (DX9L XI hsh hJ 1 0 cAddB).Rg = RgT.R := by
    show (Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.addPrims Nock.Jet.VerifiedRegistry.empty (primsOf XI)).R = RgT.R
    rw [hpp]; rfl
  have hfin : AccJ9AL (DX9L XI hsh hJ 1 0 cAddB) (Nock.V1J8.Exe.toχ (withOrbL (RS χe) (orbSh XI)).χ)
      (withOrbL (RS χe) (orbSh XI)).toMsgL (withOrbL (RS χe) (orbSh XI)).toTrL := by
    show Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (DX9L XI hsh hJ 1 0 cAddB).Pb
      (DX9L XI hsh hJ 1 0 cAddB).Rg cAddB _ _ _ cornerC9L (2 ^ 31)
    rw [eP, hRg]
    exact hacc3
  exact ⟨_, _, _, hfin, (stmt_pub_of_acc9L _ _ _ _ hfin).2⟩

end

end Air

#print axioms NockvmE2E.J9AL.LinkJ9ALToy.gen_RS
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.bigsT
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.sz_X
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.sz_C
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.sz_W
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.sz_A
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.sz_AL
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.fl_idxP
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.fl_rkP
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.m_RS
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.rows_RS
#print axioms NockvmE2E.J9AL.LinkJ9ALToy.add_air

end NockvmE2E.J9AL.LinkJ9ALToy
