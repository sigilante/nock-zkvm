/-
NockvmE2E/Z38/LinkJ9ALJjp.lean: the AIR side `jp_air` at the executed template-jet instance `jpX`, modulo the ONE named hypothesis `HF1LJ jpX`
(Z38/HF1LJ.lean: the conclusion of nock's `genJ9ALXJ_honest_at'` at the `jp` run over `catJ`, nockvm's deliverable).  Twin of
`J9AL/LinkJ9ALAdd.lean` (`add_air_add'`) over `Z38/GenJp.lean` (the record sizes at `jp`) and `Z38/AccCongJ9ALJ.lean` (the template twin of `acceptsJ9AL_congr_reg0`).
`AccJ9AL ∧ PubP9AL` at the datum `DX9LJ XJ ... cJ` of `jp_witnessQ`.  Not zero-knowledge.
-/
import NockvmE2E.Z38.GenJp
import NockvmE2E.Z38.AccCongJ9ALJ
import NockvmE2E.Z38.E2EJ9ALJToy
import NockvmE2E.Z38.HF1LJ
import NockvmE2E.J9AL.LinkJ9ALBridge
import NockvmE2E.J9AL.AccMonoJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.LinkJ9ALJjp

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9ALChips
open NockvmE2E.J8.InstJ8 (tabOf hNof P)
open NockvmE2E.J9A.PbOfX9 (nOpt)
open NockvmE2E.J9AL.PbOfX9L (primsOf idxPOf rkPOf PbOfX9L)
open NockvmE2E.J9AL.InstJ9AL (AccJ9AL PubP9AL stmt_pub_of_acc9L Datum9AL)
open NockvmE2E.J9AL.LinkJ9ALBridge (orbSh mkPbAL_withOrbL_eq preL_interp_eq)
open NockvmE2E.Z38.AccCongJ9ALJ (acceptsJ9AL_congr_regs)
open NockvmE2E.J9AL.AccMonoJ9AL (acceptsJ9AL_mono_rows)
open NockvmE2E.Z38.IfaceJ (DX9LJ layOfX)
open NockvmE2E.Z38.JetPre (layJ regsOfPub idxOfPub rkOfPub)
open NockvmE2E.Z38.E2EJ9ALJToy (XJ link_jp preg_jp)
open NockvmE2E.Z38.GenJp
open NockvmE2E.Z38.HF1LJ (sJ fJ)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun (layLK)
open NockvmE2E.Z38.JpClaim (cJ)
open NockvmE2E.Z38.HF1LJ (HF1LJ)
open NockvmE2E.Z38.CatJ (catJ)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (cornerC9L PubJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (withOrbL)
open Nock.TraceGenExe (deltaF powerBasis3)
open Nock.V1J8.Exe (CoinsE)
open Nock.V1J8.Gen (budget)

noncomputable section

/-! ## 1. shape facts of the executed instance, per field -/

theorem sh_X : hNof XJ "computeChipVCLHX9" = 5 := by decide +kernel
theorem sh_C : hNof XJ "cellChipHQKW" = 159 := by decide +kernel
theorem sh_W : hNof XJ "walkChipJ8" = 1 := by decide +kernel
theorem sh_J : hNof XJ "jetChipJ8" = 17 := by decide +kernel
theorem sh_A : hNof XJ "atomChipHQL" = 3 := by decide +kernel
theorem sh_V : nOpt XJ "walkChipHQK" = 1 := by decide +kernel
theorem sh_AX : nOpt XJ "axisChipJ9" = 1 := by decide +kernel
theorem sh_SP : nOpt XJ "splitChipJ9" = 1 := by decide +kernel
theorem sh_AL : nOpt XJ "aluChipJ9" = 12 := by decide +kernel
theorem sh_axo : (tabOf XJ "axisChipJ9").isSome = false := by decide +kernel
theorem sh_spo : (tabOf XJ "splitChipJ9").isSome = false := by decide +kernel
theorem sh_alo : (tabOf XJ "aluChipJ9").isSome = true := by decide +kernel
theorem sh_wvo : (tabOf XJ "walkChipHQK").isSome = false := by decide +kernel
theorem sh_prims : primsOf XJ = catJ.prims := by decide +kernel
theorem sh_idxP : idxPOf XJ 8 = 124 := by decide +kernel
theorem sh_rkP : rkPOf XJ 8 = (0, 43) := by decide +kernel
theorem sh_idx : idxOfPub XJ.pubIn 7 = 6 := by decide +kernel
theorem sh_rk : rkOfPub XJ.pubIn 7 = (0, 190) := by decide +kernel
theorem sh_regs : regsOfPub XJ.pubIn = [7] := by decide +kernel
theorem sh_calls : XJ.pubIn.calls = [7] := by decide +kernel
theorem sh_rt : NockvmE2E.J9A.RunGate9L.primsRoundTrip XJ.pubIn.prims = true := by decide +kernel
theorem sh_k : NockvmE2E.J9A.RunGate9L.kOfL XJ = 1 := by decide +kernel
theorem sh_kV : NockvmE2E.J9A.RunGate9L.kVOfL XJ = 0 := by decide +kernel
theorem sh_lay : layLK Rtt catJ.prims sJ fJ (fun _ => default) Rn0 = layJ XJ.pubIn := by decide +kernel

theorem hlen_jp : (layJ XJ.pubIn).length = hNof XJ "jetChipJ8" := link_jp.2.1

/-! ## 2. the layout as a dependent function -/

theorem heq_get {L1 L2 : List Nock.Jet.ChipJ8.PRow} (h : L1 = L2) (n : ℕ) (hn : L2.length = n) :
    HEq L1.get (fun i : Fin n => L2[(i : ℕ)]'(by have := i.2; omega)) := by
  subst h; subst hn
  exact heq_of_eq (funext fun i => rfl)

theorem heq_lay (χe : CoinsE) : HEq (RS χe).lay (layOfX XJ hlen_jp) := by
  have hL : layLK Rtt catJ.prims sJ fJ χe Rn0 = layJ XJ.pubIn := by
    have : layLK Rtt catJ.prims sJ fJ χe Rn0 = layLK Rtt catJ.prims sJ fJ (fun _ => default) Rn0 := by spell
    exact this.trans sh_lay
  exact heq_get hL _ hlen_jp


/-! ## 3. `jp_air` -/

set_option maxHeartbeats 4000000 in
/-- **`jp_air_k`** [kernel job, modulo `HF1LJ XJ` (nock-pending) and the executed gate `hsh`]: `AccJ9AL ∧ PubP9AL` at the datum `DX9LJ XJ ... 1 0 cJ`. -/
theorem jp_air_k (hsh : shapeOkF famJ9AL XJ = true) (hF : HF1LJ XJ) :
    ∃ χ M tr,
      AccJ9AL (DX9LJ XJ hsh hlen_jp 1 0 cJ) χ M tr ∧
      PubP9AL (DX9LJ XJ hsh hlen_jp 1 0 cJ) χ (M, fun j => pubVJ9 deltaF powerBasis3 cJ M.m M.ρ M.ρS χ j) := by
  obtain ⟨χe, I, hgen, hv, hacc⟩ := hF
  rw [gen_RS] at hgen
  have hI : RS χe = I := Option.some.inj hgen
  subst hI
  have hbr := mkPbAL_withOrbL_eq XJ hsh 1 0 (RS χe).Rt (regsOfPub XJ.pubIn) XJ.pubIn.calls (RS χe).idx (RS χe).rk (layOfX XJ hlen_jp) (RS χe) hv
    (by rw [sz_X, sh_X]) (by rw [sz_C, sh_C]) (by rw [sz_W, sh_W]) (by rw [sz_J, sh_J]) (by rw [sz_A, sh_A]) (by rw [sz_V, sh_V])
    (by rw [sz_AX, sh_AX]) (by rw [sz_SP, sh_SP]) (by rw [sz_AL, sh_AL]) (fl_kr χe) (by rw [fl_krV, sh_wvo]; simp) rfl
    (by rw [fl_regs, sh_regs]) (by rw [fl_ids, sh_calls]) rfl rfl (heq_lay χe)
    (by rw [fl_ax, sh_axo]) (by rw [fl_sp, sh_spo]) (by rw [fl_on, sh_alo]) (by rw [fl_prims, sh_prims])
    (fun k => preL_interp_eq XJ hsh preg_jp sh_rt sh_alo k)
  rw [hbr] at hacc
  generalize hPb1 : ({ PbOfX9L XJ hsh 1 0 (RS χe).Rt (regsOfPub XJ.pubIn) XJ.pubIn.calls (RS χe).idx (RS χe).rk (layOfX XJ hlen_jp)
    with idxP := (RS χe).idxP, rkP := (RS χe).rkP } : PubJ9AL P) = Pb1 at hacc
  have e_prims : Pb1.prims = catJ.prims := by rw [← hPb1]; exact sh_prims
  have e_idxP : Pb1.idxP = (RS χe).idxP := by rw [← hPb1]
  have e_rkP : Pb1.rkP = (RS χe).rkP := by rw [← hPb1]
  have e_regs : Pb1.regs = [7] := by rw [← hPb1]; exact sh_regs
  have e_ids : Pb1.ids = [7] := by rw [← hPb1]; exact sh_calls
  have e_Rt : Pb1.Rt = (RS χe).Rt := by rw [← hPb1]; rfl
  have e_idx : Pb1.idx = (RS χe).idx := by rw [← hPb1]; rfl
  have e_rk : Pb1.rk = (RS χe).rk := by rw [← hPb1]; rfl
  have eP : (DX9LJ XJ hsh hlen_jp 1 0 cJ).Pb =
      { Pb1 with Rt := catJ.toCR.Rt, idx := idxOfPub XJ.pubIn, rk := rkOfPub XJ.pubIn, idxP := idxPOf XJ, rkP := rkPOf XJ } := by
    rw [← hPb1]; rfl
  have hRt7 : ∀ i ∈ Pb1.regs, catJ.toCR.Rt i = Pb1.Rt i := by
    intro i hi; rw [e_regs] at hi; obtain rfl : i = 7 := by simpa using hi
    rw [e_Rt]; rfl
  have hRt7' : ∀ i ∈ Pb1.ids, catJ.toCR.Rt i = Pb1.Rt i := by
    intro i hi; rw [e_ids] at hi; obtain rfl : i = 7 := by simpa using hi
    rw [e_Rt]; rfl
  have hix : ∀ i ∈ Pb1.regs, idxOfPub XJ.pubIn i = Pb1.idx i := by
    intro i hi; rw [e_regs] at hi; obtain rfl : i = 7 := by simpa using hi
    rw [e_idx, sh_idx, fl_idx]
  have hrk : ∀ i ∈ Pb1.regs, rkOfPub XJ.pubIn i = Pb1.rk i := by
    intro i hi; rw [e_regs] at hi; obtain rfl : i = 7 := by simpa using hi
    rw [e_rk, sh_rk, fl_rk]
  have hiP : ∀ q ∈ Pb1.prims, idxPOf XJ q.1 = Pb1.idxP q.1 := by
    intro q hq
    obtain rfl : q = (8, Nock.Jet.Prim.PrimOp.add) := by rw [e_prims] at hq; simpa [catJ, NockvmE2E.Z38.CatJ.catJ] using hq
    show idxPOf XJ 8 = Pb1.idxP 8
    rw [e_idxP, sh_idxP, fl_idxP]
  have hrP : ∀ q ∈ Pb1.prims, rkPOf XJ q.1 = Pb1.rkP q.1 := by
    intro q hq
    obtain rfl : q = (8, Nock.Jet.Prim.PrimOp.add) := by rw [e_prims] at hq; simpa [catJ, NockvmE2E.Z38.CatJ.catJ] using hq
    show rkPOf XJ 8 = Pb1.rkP 8
    rw [e_rkP, sh_rkP, fl_rkP]
  have hacc2 := acceptsJ9AL_congr_regs deltaF powerBasis3 catJ.toCR.Rt (idxOfPub XJ.pubIn) (rkOfPub XJ.pubIn) (idxPOf XJ) (rkPOf XJ)
    hRt7 hRt7' hix hrk hiP hrP hacc
  have hrows : (withOrbL (RS χe) (orbSh XJ)).toRowsL = ⟨⟨budget 159, 318, 318⟩, 318⟩ := rows_RS χe
  have hg : (withOrbL (RS χe) (orbSh XJ)).g = 1 := fl_g χe
  rw [hrows, hg] at hacc2
  have hacc3 := acceptsJ9AL_mono_rows deltaF powerBasis3 hacc2 (r' := cornerC9L) (g' := 2 ^ 31)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hc : (withOrbL (RS χe) (orbSh XJ)).c = cJ := rfl
  rw [hc] at hacc3
  have hRg : (DX9LJ XJ hsh hlen_jp 1 0 cJ).Rg = catJ.toVR.R := by
    show (Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.addPrims catJ.toCR.toVR (primsOf XJ)).R = catJ.toVR.R
    rw [sh_prims]; rfl
  have hfin : AccJ9AL (DX9LJ XJ hsh hlen_jp 1 0 cJ) (Nock.V1J8.Exe.toχ (withOrbL (RS χe) (orbSh XJ)).χ)
      (withOrbL (RS χe) (orbSh XJ)).toMsgL (withOrbL (RS χe) (orbSh XJ)).toTrL := by
    show Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (DX9LJ XJ hsh hlen_jp 1 0 cJ).Pb
      (DX9LJ XJ hsh hlen_jp 1 0 cJ).Rg cJ _ _ _ cornerC9L (2 ^ 31)
    rw [eP, hRg]
    exact hacc3
  exact ⟨_, _, _, hfin, (stmt_pub_of_acc9L _ _ _ _ hfin).2⟩

/-- the datum of `jp_air_k` (`kroots = 1`, `krootsV = 0`) IS the datum of `jp_witnessQ` (`kOfL XJ`, `kVOfL XJ`) -/
theorem jp_air_datum_eq (hsh : shapeOkF famJ9AL XJ = true) :
    DX9LJ XJ hsh hlen_jp 1 0 cJ = DX9LJ XJ hsh hlen_jp (NockvmE2E.J9A.RunGate9L.kOfL XJ) (NockvmE2E.J9A.RunGate9L.kVOfL XJ) cJ := by
  have key : ∀ a b : ℕ, a = 1 → b = 0 → DX9LJ XJ hsh hlen_jp 1 0 cJ = DX9LJ XJ hsh hlen_jp a b cJ := by
    intro a b ha hb; subst ha; subst hb; rfl
  exact key _ _ sh_k.symm sh_kV.symm

/-- **`jp_air`** [kernel job, modulo `HF1LJ XJ` and `hsh`]: stated at the witness datum of `jp_witnessQ` (`kOfL XJ`, `kVOfL XJ`, claim `cJ`), so both live on one datum. -/
theorem jp_air (hsh : shapeOkF famJ9AL XJ = true) (hF : HF1LJ XJ) :
    ∃ χ M tr,
      AccJ9AL (DX9LJ XJ hsh hlen_jp (NockvmE2E.J9A.RunGate9L.kOfL XJ) (NockvmE2E.J9A.RunGate9L.kVOfL XJ) cJ) χ M tr ∧
      PubP9AL (DX9LJ XJ hsh hlen_jp (NockvmE2E.J9A.RunGate9L.kOfL XJ) (NockvmE2E.J9A.RunGate9L.kVOfL XJ) cJ) χ
        (M, fun j => pubVJ9 deltaF powerBasis3 cJ M.m M.ρ M.ρS χ j) := by
  obtain ⟨χ, M, tr, h1, h2⟩ := jp_air_k hsh hF
  rw [jp_air_datum_eq hsh] at h1 h2
  exact ⟨χ, M, tr, h1, h2⟩

/-! ## 4. bridge facts at `jpX` for nockvm's `honestTplUnif`: the orbit order and the row bounds -/

/-- the shared orbit `(k+1, ofU64 hGen)` has order `3 * 2^(k+1)` (from the executed gate `hsh`) -/
theorem hord_jp (hsh : shapeOkF famJ9AL XJ = true) :
    orderOf (Nock.TraceGenExe.Gold.ofU64 XJ.hGen).toZ = 3 * 2 ^ (XJ.k + 1) := by
  rw [Nock.TraceGenExe.Gold.ofU64_toZ]
  exact orbit_order_of_shapeF hsh

/-- every table row count of the record at `jp` is at most `3 * 2^(k+1) = 768`: X 5, C 159, W 1, J 17, A 3, V 1, AX 1, SP 1, AL 12 -/
theorem rows_le_jp : ∀ n ∈ ([5, 159, 1, 17, 3, 1, 1, 1, 12] : List ℕ), n ≤ 3 * 2 ^ (XJ.k + 1) := by decide +kernel

theorem rows_le_jp_record (χe : CoinsE) : (RS χe).X.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).C.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).W.n ≤ 3 * 2 ^ (XJ.k + 1) ∧
    (RS χe).J.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).A.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).V.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).AX.n ≤ 3 * 2 ^ (XJ.k + 1) ∧
    (RS χe).SP.n ≤ 3 * 2 ^ (XJ.k + 1) ∧ (RS χe).AL.n ≤ 3 * 2 ^ (XJ.k + 1) := by
  have h := rows_le_jp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  rw [sz_X, sz_C, sz_W, sz_J, sz_A, sz_V, sz_AX, sz_SP, sz_AL]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end

end NockvmE2E.Z38.LinkJ9ALJjp

#print axioms NockvmE2E.Z38.LinkJ9ALJjp.heq_lay
#print axioms NockvmE2E.Z38.LinkJ9ALJjp.jp_air_k
#print axioms NockvmE2E.Z38.LinkJ9ALJjp.jp_air
#print axioms NockvmE2E.Z38.LinkJ9ALJjp.hord_jp
#print axioms NockvmE2E.Z38.LinkJ9ALJjp.rows_le_jp
#print axioms NockvmE2E.Z38.LinkJ9ALJjp.rows_le_jp_record
