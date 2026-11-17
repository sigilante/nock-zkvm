/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalV2.lean

  **J-9 AL completeness, part 3: the validity balance `hsumC_L`.**

  * §1 the cell validity terminal at `DL` (`cvT_gen`, `cvT_L`): the J-8 `cvT_run` with the prim pins.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalV2

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalV
open Nock.V1J8.Gen (hdN' tlN')
open Nock.Jet.Prim (PrimOp primC primSpec)

noncomputable section

/-! ## 1. The cell validity terminal at `DL` -/

section CvT
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem ccT_eq' (γ ρ : 𝕂′) (E : Noun → Nock.ComputeTable.FP 𝕂′) (cells : List Noun) (n : Noun)
    (hn : n.isCell = true → n ∈ cells) :
    ccT δ γ ρ E cells n = if n.isCell then cG δ γ ρ E cells (Nock.V1J8.Gen.idxOf cells n) else 0 := by
  by_cases hc : n.isCell = true
  · simp only [ccT, hc, if_true, genIdxOf_eq _ _ (hn hc)]
  · simp [ccT, hc]

/-- **The cell validity terminal at a data record whose multiplicities are the J-8 counts plus a pin list `Lp`.** -/
theorem cvT_gen (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hcl : ∀ y ∈ D.cells, ((hdN y).isCell = true → hdN y ∈ D.cells) ∧ ((tlN y).isCell = true → tlN y ∈ D.cells))
    (Lp : List (ℕ × ℕ))
    (hcnt : ∀ k < D.cells.length, D.mv.getD k 0 =
      ComplJ8Data.sumAt (ComplJ8Data.cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n])) k +
      ComplJ8Data.sumAt (ComplJ8Data.cellPairs D.cells [s, f, r]) k +
      ComplJ8Data.sumAt (D.regs.map fun id => (D.idx id, 1)) k + ComplJ8Data.sumAt Lp k)
    (hr : ∀ L ∈ [ComplJ8Data.cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n]),
      ComplJ8Data.cellPairs D.cells [s, f, r], D.regs.map (fun id => (D.idx id, 1)), Lp],
      ∀ q ∈ L, 0 < q.2 → q.1 < D.cells.length) :
    cvT δ D χ =
      ([s, f, r].map fun x => if x.isCell then cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells
          (Nock.V1J8.Gen.idxOf D.cells x) else 0).sum +
      (D.regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (D.idx id)).sum +
      (Lp.map fun q => (q.2 : 𝕂′) * cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells q.1).sum -
      (D.cells.map fun y =>
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y)).sum := by
  set G := cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells with hG
  set L1 := ComplJ8Data.cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n]) with hL1
  set L2 := ComplJ8Data.cellPairs D.cells [s, f, r] with hL2
  set L3 := D.regs.map fun id => (D.idx id, 1) with hL3
  have h1 : ∑ k ∈ Finset.range D.cells.length, liftQ δ ((mvF D k : ℕ) : ZMod p) * G k =
      (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum + (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum +
        (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum + (Lp.map fun q => (q.2 : 𝕂′) * G q.1).sum := by
    rw [Finset.sum_congr rfl (fun k hk => by
      show liftQ δ ((D.mv.getD k 0 : ℕ) : ZMod p) * G k = _
      rw [hcnt k (Finset.mem_range.mp hk)])]
    simp only [liftQ, Nat.cast_add, map_add, map_natCast, add_mul, Finset.sum_add_distrib]
    rw [sum_sumAt _ _ L1 (hr L1 (by simp)), sum_sumAt _ _ L2 (hr L2 (by simp)),
      sum_sumAt _ _ L3 (hr L3 (by simp)), sum_sumAt _ _ Lp (hr Lp (by simp))]
  have hS1 : (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum =
      (D.cells.map fun y => (if (hdN' y).isCell then G (Nock.V1J8.Gen.idxOf D.cells (hdN' y)) else 0) +
        (if (tlN' y).isCell then G (Nock.V1J8.Gen.idxOf D.cells (tlN' y)) else 0)).sum := by
    rw [hL1, cellPairs_sum, sum_flatMap_two]
  have hS2 : (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum =
      ([s, f, r].map fun x => if x.isCell then G (Nock.V1J8.Gen.idxOf D.cells x) else 0).sum := by
    rw [hL2, cellPairs_sum]
  have hS3 : (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum = (D.regs.map fun id => G (D.idx id)).sum := by
    simp [hL3, List.map_map, Function.comp_def]
  have h2 : (D.cells.map fun y => ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (hdN y) +
        ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (tlN y) +
        (btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y))).sum =
      (D.cells.map fun y => (if (hdN' y).isCell then G (Nock.V1J8.Gen.idxOf D.cells (hdN' y)) else 0) +
        (if (tlN' y).isCell then G (Nock.V1J8.Gen.idxOf D.cells (tlN' y)) else 0)).sum +
        (D.cells.map fun y => btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y)).sum := by
    rw [← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [ccT_eq' δ _ _ _ _ _ (hcl y hy).1, ccT_eq' δ _ _ _ _ _ (hcl y hy).2, hdN_eq, tlN_eq]
  unfold cvT
  rw [cvSum_gen δ _ _ _ _ _ _ _ _ _ hcl, ← hG, h1, h2, hS1, hS2, hS3]
  ring

end CvT

section CvTL
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

theorem mvCounts_eq (cs : List Noun) (c : P8PublicClaim) :
    Nock.V1J8.Gen.mvCounts cs c = ComplJ8Data.bumpAll (Array.replicate cs.length 0)
      (ComplJ8Data.cellPairs cs ((cs.flatMap fun n => [hdN' n, tlN' n]) ++ [c.subject, c.formula, c.result])) := by
  unfold Nock.V1J8.Gen.mvCounts
  simp only
  generalize Array.replicate cs.length 0 = a
  generalize (cs.flatMap fun n => [hdN' n, tlN' n]) ++ [c.subject, c.formula, c.result] = l
  induction l generalizing a with
  | nil => rfl
  | cons n l ih =>
    simp only [List.foldl_cons]
    rcases n with v | ⟨x, y⟩
    · rw [ih]; simp [ComplJ8Data.cellPairs]
    · rw [ih]; simp only [ComplJ8Data.cellPairs, List.filterMap_cons]; rfl

/-- **`mv` at `DL`**: the J-8 counts over the J registry, plus the primitive pins (stated at `DA`'s cells). -/
theorem mvL_cnt (j : ℕ) (hj : j < (DA).cells.length) :
    (DL).mv.getD j 0 =
      ComplJ8Data.sumAt (ComplJ8Data.cellPairs (DA).cells ((DA).cells.flatMap fun n => [hdN' n, tlN' n])) j +
      ComplJ8Data.sumAt (ComplJ8Data.cellPairs (DA).cells [s, f, r]) j +
      ComplJ8Data.sumAt ((DL).regs.map fun id => ((DA).idx id, 1)) j +
      ComplJ8Data.sumAt (ComplJ9ALData.primPinL (DA).cells prims ((DA).calls.map Prod.fst)) j := by
  have hsz0 : (Nock.V1J8.Gen.mvCounts (DA).cells ⟨s, f, r⟩).size = (DA).cells.length := by
    rw [mvCounts_eq, ComplJ8Data.bumpAll_size]; simp
  have hsz : (Nock.V1J8.Gen.mvPins (Nock.V1J8.Gen.mvCounts (DA).cells ⟨s, f, r⟩) (DL).regs (DA).idx).size =
      (DA).cells.length := by
    simp only [Nock.V1J8.Gen.mvPins, ComplJ8Data.foldl_idBump, ComplJ8Data.bumpAll_size, hsz0]
  rw [ComplJ9ALData.mvL_getD Rt prims hgen j (by rw [hsz]; exact hj)]
  simp only [Nock.V1J8.Gen.mvPins, ComplJ8Data.foldl_idBump]
  rw [ComplJ8Data.bumpAll_getD _ _ _ (by rw [hsz0]; exact hj), mvCounts_eq,
    ComplJ8Data.bumpAll0_getD _ _ _ hj]
  have cp : ∀ (cs l l' : List Noun), ComplJ8Data.cellPairs cs (l ++ l') =
      ComplJ8Data.cellPairs cs l ++ ComplJ8Data.cellPairs cs l' := by
    intro cs l l'; simp [ComplJ8Data.cellPairs, List.filterMap_append]
  rw [cp, ComplJ8Data.sumAt_append]
  simp only [ComplJ8Data.sumAt]

theorem regsL_sub : ∀ id ∈ (DL).regs, id ∈ (DD).regs := by
  intro id hid
  have h1 : id ∈ ((DL).calls.map Prod.fst) := by
    have : (DL).regs = ((DL).calls.map Prod.fst).dedup := rfl
    rw [this] at hid
    exact List.mem_dedup.mp hid
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp h1
  have h2 := (ComplJ9ALData.jCallsP_sub _ _ cl hcl).1
  have : (DD).regs = ((DD).calls.map Prod.fst).dedup := rfl
  rw [this]
  exact List.mem_dedup.mpr (List.mem_map.mpr ⟨cl, h2, rfl⟩)

theorem cvT_L (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (χ : Coins frameJ8 K) :
    cvT δ (DL) χ =
      ([s, f, r].map fun x => if x.isCell then cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells
          (Nock.V1J8.Gen.idxOf (DD).cells x) else 0).sum +
      ((DL).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells ((DD).idx id)).sum +
      ((psRun (p := p) Rt hgen prims).map fun q =>
        cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells (vcRun (p := p) Rt hgen prims q.1)).sum -
      ((DD).cells.map fun y =>
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (tlN y)).sum := by
  have hcl : ∀ y ∈ (DL).cells, ((hdN y).isCell = true → hdN y ∈ (DL).cells) ∧
      ((tlN y).isCell = true → tlN y ∈ (DL).cells) := cells_cl_run (p := p) Rt hgen
  have key := cvT_gen δ (DL) χ hcl (ComplJ9ALData.primPinL (DA).cells prims ((DA).calls.map Prod.fst))
    (fun k hk => mvL_cnt Rt hgen prims k hk) (by
      intro L hL q hq hq0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl | rfl | rfl
      · refine ComplJ8Data.vRecs_range p Rg Rt hgen q ?_ hq0
        simp only [ComplJ8Data.vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inl hq
      · refine ComplJ8Data.vRecs_range p Rg Rt hgen q ?_ hq0
        simp only [ComplJ8Data.vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inr (Or.inl hq)
      · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hq
        refine ComplJ8Data.vRecs_range p Rg Rt hgen _ ?_ hq0
        simp only [ComplJ8Data.vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨id, regsL_sub Rt hgen prims id hid, rfl⟩))
      · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        exact (idxP_getD Rt hgen prims hnd hprim q' hq').2)
  rw [key]
  simp only [ComplJ9ALData.primPinL, List.map_map, Function.comp_def, Nat.cast_one, one_mul]
  rfl

end CvTL

section AtomL
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom (D9 mbX extraPairs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- The atom-root provider inverse of atom row `j` at `DL`, at any orbit. -/
abbrev HBL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (HonestA8.dNat δ (HonestA8.dMB δ b (ComplJ9ALData.acsL_pos Rt prims hgen) (powN o _) o
    (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ)
    (colAH δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
      (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ))
    (newBA (DL))) j)⁻¹

/-- A noun's atom-root terminal term at `DL`, at any orbit. -/
abbrev bhL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  ((ComplJ8Data.bigIdOfP p (DD).acs n).map (HBL δ b Rt hgen prims o χ)).getD 0

variable (hpG : p = Nock.Atoms.p)
include hpG

/-- **The big-atom key identity at `DL`** at any injective orbit. -/
theorem keyL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DL).acs.length))
    (χ : Coins frameJ8 K) (a : ℕ) (ha : a ∈ (DD).bigs) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a) ((ComplJ8Data.rootIdxP p (DD).acs a : ℕ) : ZMod p) =
      HBL δ b Rt hgen prims o χ (ComplJ8Data.rootIdxP p (DD).acs a) := by
  have hpa : p ≤ a := ((ComplJ8Atom.mem_bigsP p _ _ a).mp ha).2
  have hg := ComplJ9BAtom.root_get Rt hgen hpG a ha
  have hj : ComplJ8Data.rootIdxP p (DD).acs a < (DD).acs.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  exact ComplJ9BAtom.big_keyG δ b hpG (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o hinj χ _ a hpa _ hj
    (Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hg))

/-- **A child's big-atom consumer term is its atom-root provider term** (at `DL`, any injective orbit). -/
theorem bt_bhL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DL).acs.length))
    (χ : Coins frameJ8 K) (n : Noun)
    (hn : ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs) :
    btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) n = bhL δ b Rt hgen prims o χ n := by
  cases n with
  | cell u v => simp [btT, bhL, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP]
  | atom v =>
    by_cases hv : v < p
    · simp [btT, bhL, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
    · have hb : ComplJ8Cell.isBig (bigOf (DD)) (.atom v) = true := by
        simp [ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
      simp only [btT, hb, if_true, bhL, bigOf, ComplJ8Data.bigIdOfP, hv, if_false, Option.getD_some,
        Option.map_some]
      exact keyL δ b Rt hgen prims hpG o hinj χ v (hn v rfl (by omega))

/-- **The atom table's `mb` terminal at `DL`** (any injective orbit) is the sum of the cell children's atom-root
terms and the claim's. -/
theorem mbTL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DL).acs.length))
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ AtomChipHQ.pubMB)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ (AtomChipHQ.pubMB + 1)) =
      ((DD).cells.map fun y => bhL δ b Rt hgen prims o χ (hdN' y) + bhL δ b Rt hgen prims o χ (tlN' y)).sum +
      ([s, f, r].map fun n => bhL δ b Rt hgen prims o χ n).sum +
      ((ComplJ9ALData.aluBL p (DA).acs (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t))).map
        fun q => (q.2 : 𝕂′) * HBL δ b Rt hgen prims o χ q.1).sum := by
  refine ((ComplJ8OfAtom.atomTerms δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ).2.2.2.1).trans ?_
  obtain ⟨LB, hLB⟩ : ∃ LB, LB = ((DD).cells.flatMap fun n => [hdN' n, tlN' n]).filterMap
      fun n => (ComplJ8Data.bigIdOfP p (DD).acs n).map fun i => (i, 1) := ⟨_, rfl⟩
  obtain ⟨AB, hAB⟩ : ∃ AB, AB = ComplJ9ALData.aluBL p (DA).acs
      (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t)) := ⟨_, rfl⟩
  have hne : (DD).acs ≠ [] := List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen)
  have hrange0 : ∀ q ∈ extraPairs p (DD).acs [s, f, r], 0 < q.2 → q.1 < (DD).acs.length := by
    intro q hq _
    · obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hq
      cases n with
      | cell u v => simp [ComplJ8Data.bigIdOfP] at hn
      | atom v =>
        by_cases hv : v < p
        · simp [ComplJ8Data.bigIdOfP, hv] at hn
        · simp only [ComplJ8Data.bigIdOfP, hv, if_false, Option.map_some, Option.some.injEq] at hn
          rw [← hn]
          exact ComplJ8Data.rootIdxP_lt p _ hne v
  have hrangeAB : ∀ q ∈ AB, 0 < q.2 → q.1 < (DD).acs.length := by
    intro q hq _
    rw [hAB] at hq
    obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hq
    cases n with
    | cell u v => simp [ComplJ8Data.bigIdOfP] at hn
    | atom v =>
      by_cases hv : v < p
      · simp [ComplJ8Data.bigIdOfP, hv] at hn
      · simp only [ComplJ8Data.bigIdOfP, hv, if_false, Option.map_some, Option.some.injEq] at hn
        rw [← hn]
        exact ComplJ8Data.rootIdxP_lt p _ hne v
  have hrange : ∀ q ∈ LB ++ extraPairs p (DD).acs [s, f, r] ++ AB, 0 < q.2 → q.1 < (DD).acs.length := by
    intro q hq h0
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact ComplJ8Data.mbRecs_range p Rg Rt hgen q (by
          simp only [ComplJ8Data.mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [← hLB]; exact hq) h0
      · exact hrange0 q hq h0
    · exact hrangeAB q hq h0
  have hcnt : ∀ j ∈ Finset.range (DL).acs.length,
      liftQ δ (HonestA8.cNat j (newBA (DL) AtomChipHQ.mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b (ComplJ9ALData.acsL_pos Rt prims hgen) (powN o _) o
          (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ)
          (colAH δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
            (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ))
          (newBA (DL))) j)⁻¹ =
      ((ComplJ8Data.sumAt (LB ++ extraPairs p (DD).acs [s, f, r] ++ AB) j : ℕ) : 𝕂′) *
        HBL δ b Rt hgen prims o χ j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : HonestA8.cNat j (newBA (DL) AtomChipHQ.mb) =
        ((ComplJ8Data.sumAt (LB ++ extraPairs p (DD).acs [s, f, r] ++ AB) j : ℕ) : ZMod p) := by
      have h0 : (DA).mb.getD j 0 = ComplJ8Data.sumAt (LB ++ extraPairs p (DD).acs [s, f, r]) j := by
        show ((mbX (DD) [s, f, r]).getD j 0) = _
        rw [ComplJ9BAtom.mbX_getD _ _ _ (by rw [ComplJ9BAtom.mb_size p Rg Rt hgen]; exact hj'),
          ComplJ8Data.mb_eq_cnt p Rg Rt hgen j hj', ComplJ8Data.cnt_eq_sumAt, ComplJ8Data.sumAt_append]
        simp only [ComplJ8Data.mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLB]
      rw [HonestA8.cNat, dif_pos hj', newBA_mb, ComplJ9ALData.mbL_getD Rt prims hgen j hj', h0, ← hAB,
        ComplJ8Data.sumAt_append _ AB]
    rw [e]
    simp only [liftQ, map_natCast]
  refine (Finset.sum_congr rfl hcnt).trans ?_
  rw [show (DL).acs.length = (DD).acs.length from rfl]
  rw [sum_sumAt _ _ (LB ++ extraPairs p (DD).acs [s, f, r] ++ AB) hrange, List.map_append, List.sum_append,
    List.map_append, List.sum_append, ← hAB]
  unfold extraPairs
  rw [bigPairs_sum (ComplJ8Data.bigIdOfP p (DD).acs) (HBL δ b Rt hgen prims o χ) [s, f, r]]
  rw [hLB, bigPairs_sum (ComplJ8Data.bigIdOfP p (DD).acs) (HBL δ b Rt hgen prims o χ), sum_flatMap_two]

/-- **The claim's big-leaf records' inverse sum** is the claim's atom-root terms (at `DL`, any injective orbit). -/
theorem claimBig_sumL {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DL).acs.length)) (χ : Coins frameJ8 K)
    (hbig : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs) :
    ((ClaimJ9.claimBigRecs δ χ (ComplJ8.cJ s f r) (ComplJ8Comp.mCOf (DD).H (ComplJ8.cJ s f r))).map
      fun x => (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ([s, f, r].map fun n => bhL δ b Rt hgen prims o χ n).sum := by
  have hterm : ∀ x ∈ [s, f, r], (if ClaimJ9.isBigN p x = true then
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ x)
        (((DD).H x).2 : ZMod p) 0 0))⁻¹ else 0) = bhL δ b Rt hgen prims o χ x := by
    intro x hx
    cases x with
    | cell u v => simp [ClaimJ9.isBigN, bhL, ComplJ8Data.bigIdOfP]
    | atom a =>
      by_cases ha : p ≤ a
      · have hmem := hbig _ hx a rfl ha
        have hH : ((DD).H (.atom a)).2 = ComplJ8Data.rootIdxP p (DD).acs a := by
          show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom a)).2 = _
          simp [ComplJ8Data.hdlP, show ¬ a < p by omega]
        have hk := claimVec_kOf δ (AcceptsJ8.encJ8 δ χ) (.atom a)
          ((ComplJ8Data.rootIdxP p (DD).acs a : ℕ) : ZMod p)
        simp only [Noun.internal, Nat.zero_div, Nat.zero_mod, Nat.cast_zero] at hk
        have hb : bhL δ b Rt hgen prims o χ (.atom a) = HBL δ b Rt hgen prims o χ (ComplJ8Data.rootIdxP p (DD).acs a) := by
          simp [bhL, ComplJ8Data.bigIdOfP, show ¬ a < p by omega]
        rw [hb, ← keyL δ b Rt hgen prims hpG o hinj χ a hmem, if_pos (by simp [ClaimJ9.isBigN, ha]), hH, hk]
      · simp [ClaimJ9.isBigN, ha, bhL, ComplJ8Data.bigIdOfP, show a < p by omega]
  unfold ClaimJ9.claimBigRecs ClaimJ9.claimBigs
  rw [List.map_map, sum_map_ite']
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rw [← hterm s (by simp), ← hterm f (by simp), ← hterm r (by simp)]
  rfl

/-- **The J registry pin records' inverse sum**, over a layout whose registry is the overlay's `DL.regs`. -/
theorem pin_sum_L (Pb : AcceptsJ8.PubJ8 p) (hreg : Pb.regs = (DL).regs) (hRtE : Pb.Rt = Rt)
    (hidx : Pb.idx = (DD).idx)
    (hrk : ∀ id, Pb.rk id = AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.pinRecsJ8 δ Pb χ).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ((DL).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells ((DD).idx id)).sum := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map, hreg]
  refine congrArg List.sum (List.map_congr_left (l := (DL).regs) fun id hid => ?_)
  have hid' : id ∈ (DD).regs := ComplJ9ALBalV2.regsL_sub Rt hgen prims id hid
  have hmem : Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).cells := by
    have hm : Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid', rfl⟩))
    obtain ⟨a, c, hab⟩ := ComplJ8Data.compile_isCell p (Rt id)
    rw [hab] at hm ⊢
    exact ComplJ8Data.root_mem_cells p Rg Rt hgen hm
  show (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ
      (encR δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)))
      ((Pb.idx id : ℕ) : ZMod p) ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p)))⁻¹ = _
  rw [hRtE, hidx, hrk id]
  rw [show (DD).idx id = Nock.V1J8.Gen.idxOf (DD).cells (Nock.Jet.Autogen.compile p (Rt id)) from rfl,
    genIdxOf_eq _ _ hmem]
  unfold cG
  rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]

/-- **The primitive pin records' inverse sum** is the cell table's providers at `vcRun`. -/
theorem primPin_sum (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (χ : Coins frameJ8 K) :
    (((psRun (p := p) Rt hgen prims).map fun q => ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ (primC q.2))
        ((vcRun (p := p) Rt hgen prims q.1 : ℕ) : ZMod p) (((ComplJ9ALData.rkPOf prims q.1).1 : ℕ) : ZMod p)
        (((ComplJ9ALData.rkPOf prims q.1).2 : ℕ) : ZMod p)).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ((psRun (p := p) Rt hgen prims).map fun q =>
        cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells (vcRun (p := p) Rt hgen prims q.1)).sum := by
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  have hqp : q ∈ prims := (List.mem_filter.mp hq).1
  have hop : ComplJ9ALData.opOf prims q.1 = q.2 := ComplJ9ALData.opOf_of_mem hnd hqp
  have hrk : ComplJ9ALData.rkPOf prims q.1 = AcceptsJ8P.rkC (primC q.2) := by
    simp only [ComplJ9ALData.rkPOf, hop]
  have hg := (idxP_getD Rt hgen prims hnd hprim q hq).1
  show (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (encR δ χ (primC q.2))
      ((vcRun (p := p) Rt hgen prims q.1 : ℕ) : ZMod p) (((ComplJ9ALData.rkPOf prims q.1).1 : ℕ) : ZMod p)
      (((ComplJ9ALData.rkPOf prims q.1).2 : ℕ) : ZMod p)))⁻¹ = _
  rw [hrk]
  unfold cG
  rw [show (DD).cells = (DA).cells from rfl, hg, AcceptsJ8P.rkC, claimVec_kOf]


end AtomL

/-! ## 3. The ALU validity terminal -/

section SVRun
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8 chalsALJ8_ok chalsALJ8_zAt valKey)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem kvec_L (q : QRow 𝕂′) : Quad.mk (algebraMap (ZMod p) K δ) (kvec δ q 4) (kvec δ q 5) = q.L := by
  unfold kvec
  simp only [Nat.reduceMod, if_true, show ¬ (5 % 2 = 0) by decide, if_false, Nat.reduceSub]
  simp only [QRow.role]
  exact Quad.mk_re_im _ q.L

/-- **The validity denominator of a row** is the validity-coin compression of the key `[z, 0, L, 0, sv]`. -/
theorem dV_eq (χ : Coins frameJ8 K) (r : BRow (ZMod p)) (q : QRow 𝕂′) :
    (den δ (valKey : List (QE (ZMod p)))).ev δ ⟨kvec δ q, fun _ => 0, chalsALJ8 δ χ, fun _ => 0⟩
        (envB r.col (fun _ => 0)) =
      ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ ![zJ δ χ, 0, q.L, 0, liftQ δ r.sv] := by
  have hok := chalsOK_mono δ (show 5 ≤ 11 by norm_num) (chalsALJ8_ok δ χ)
  have e := den_ev_compress' δ (valKey : List (QE (ZMod p))) (m := 5) rfl
    ⟨kvec δ q, fun _ => 0, chalsALJ8 δ χ, fun _ => 0⟩ (envB r.col (fun _ => 0)) _ _ hok
  rw [e, InhabJ8Good.compress_split]
  refine congrArg (fun x => ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ x) ?_
  funext c
  fin_cases c
  · simp only [keyVec, valKey, AtomChipHQ.zAt, ev_chal, Matrix.cons_val_zero, List.getD_cons_zero]
    exact chalsALJ8_zAt δ χ
  · simp [keyVec, valKey, ev_zero]
  · simp only [keyVec, valKey, ev_var, Fin.reduceFinMk, Matrix.cons_val, List.getD_cons_succ, List.getD_cons_zero]
    exact kvec_L δ q
  · simp [keyVec, valKey, ev_zero]
  · simp [keyVec, valKey, ev_base]
    rfl

/-- The validity term of a row with `𝕂′` limb value `L`. -/
def GVL (χ : Coins frameJ8 K) (r : BRow (ZMod p)) (L : 𝕂′) : 𝕂′ :=
  liftQ δ r.aV * (ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ ![zJ δ χ, 0, L, 0, liftQ δ r.sv])⁻¹

theorem GVL_aV0 (χ : Coins frameJ8 K) (r : BRow (ZMod p)) (L : 𝕂′) (h : r.aV = 0) : GVL δ χ r L = 0 := by
  simp [GVL, h, liftQ]

theorem tV_eq' (χ : Coins frameJ8 K) {n : ℕ} (tb : List (BRow (ZMod p) × QRow 𝕂′)) (i : Fin n) :
    tV δ (chalsALJ8 δ χ) tb i = GVL δ χ (rowAt δ tb i).1 (rowAt δ tb i).2.L := by
  show liftQ δ (rowAt δ tb i).1.aV * _ = _
  unfold GVL
  rw [show dV δ (chalsALJ8 δ χ) tb i = _ from dV_eq δ χ (rowAt δ tb i).1 (rowAt δ tb i).2]

/-- **The honest table's validity terms**: the calls' blocks'. -/
theorem tblP_sumV (χ : Coins frameJ8 K) (p' : ℕ) (y : 𝕂′) (pregs : List (BRow (ZMod p))) (cls : List CallL)
    (hpre : ∀ r ∈ pregs, r.aV = 0) :
    ((tblP δ p' y pregs cls).map fun x => GVL δ χ x.1 x.2.L).sum =
      (cls.map fun cl => ((zipB δ p' y cl).map fun x => GVL δ χ x.1 x.2.L).sum).sum := by
  unfold tblP
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
    ComplJ9ALBalX.sum_map_flatMap]
  have h1 : (((pregs.map fun r => (r, QRow.zero)).map fun x => GVL δ χ x.1 x.2.L)).sum = 0 :=
    List.sum_eq_zero fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact GVL_aV0 δ χ _ _ (hpre r hr)
  have h3 : (([(padRow, QRow.zero)].map fun x => GVL δ χ x.1 x.2.L)).sum = 0 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact GVL_aV0 δ χ _ _ rfl
  rw [h1, h3, zero_add, add_zero]

theorem zip_flatMap_eq {α β γ : Type} (l : List α) (f : α → List β) (g : α → List γ)
    (h : ∀ a ∈ l, (f a).length = (g a).length) :
    (l.flatMap f).zip (l.flatMap g) = l.flatMap fun a => (f a).zip (g a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [List.zip_append (h a (List.mem_cons_self)), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem map_zip_fst_snd {α β M : Type} (g : α → M) (a : List α) (c : List β) (h : a.length ≤ c.length) :
    (a.zip c).map (fun x => g x.1) = a.map g := by
  calc (a.zip c).map (fun x => g x.1) = ((a.zip c).map Prod.fst).map g := by
        simp [List.map_map, Function.comp_def]
    _ = a.map g := by rw [List.map_fst_zip h]

theorem sum_zip_mapL {M : Type} [AddCommMonoid M] {Q : Type} (L : Q → 𝕂′) (g : BRow (ZMod p) → 𝕂′ → M) :
    ∀ (R : List (BRow (ZMod p))) (qs : List Q),
      ((R.zip qs).map fun x => g x.1 (L x.2)).sum = ((R.zip (qs.map L)).map fun x => g x.1 x.2).sum
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: R, q :: qs => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, sum_zip_mapL L g R qs]

theorem sum_zip_range (χ : Coins frameJ8 K) (rowf : ℕ → BRow (ZMod p)) (hrow : ∀ i, (rowf (i + 1)).aV = 0)
    (L : 𝕂′) :
    ∀ n : ℕ, ((((List.range n).map rowf).zip ((List.range n).map fun i => if i = 0 then L else 0)).map
      fun x => GVL δ χ x.1 x.2).sum = if 0 < n then GVL δ χ (rowf 0) L else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.zip_map', List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, if_true, Nat.succ_pos, Function.comp_def]
    rw [List.sum_eq_zero, add_zero]
    intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    exact GVL_aV0 δ χ _ _ (hrow i)

/-- The validity contribution of a slot: its first row's, at the slot's `L`. -/
def cSlot (χ : Coins frameJ8 K) (p' : ℕ) (y : 𝕂′) (cl : CallL) (s : SlotL) : 𝕂′ :=
  if 0 < s.words.length then GVL δ χ (slotRow (F := ZMod p) p' cl s 0) (slotL y s) else 0

theorem slotRow_aV_succ (p' : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := ZMod p) p' cl s (i + 1)).aV = 0 := by
  simp [slotRow, ind]

/-- **A call block's validity terms**: one per slot, at its first row. -/
theorem zipB_sumV (χ : Coins frameJ8 K) (p' : ℕ) (y : 𝕂′) (cl : CallL) :
    ((zipB δ p' y cl).map fun x => GVL δ χ x.1 x.2.L).sum =
      ((slotsOf p' cl).map fun s => cSlot δ χ p' y cl s).sum := by
  unfold zipB blockB
  have hbq : blockQ p' y cl = ⟨0, 0, 0, (hdrD (Q := 𝕂′) cl).1, (hdrD (Q := 𝕂′) cl).2, (hdrD (Q := 𝕂′) cl).1,
      (hdrD (Q := 𝕂′) cl).2, (latchOf p' y cl).1, (latchOf p' y cl).2⟩ ::
      (((laneHL y cl p').zip ((laneD p' y cl).zip (runSums (hdrD cl) (laneD p' y cl)))).map fun x =>
        ⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2, (latchOf p' y cl).1,
          (latchOf p' y cl).2⟩) := rfl
  rw [hbq, List.zip_cons_cons, List.map_cons, List.sum_cons]
  rw [GVL_aV0 δ χ _ _ rfl, zero_add]
  have hlen : (laneHL y cl p').length ≤ ((laneD p' y cl).zip (runSums (hdrD cl) (laneD p' y cl))).length := by
    simp [List.length_zip, laneHL, laneD, runSums_length, List.length_flatMap]
  have hLs : ((((laneHL y cl p').zip ((laneD p' y cl).zip (runSums (hdrD cl) (laneD p' y cl)))).map fun x =>
        (⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2, (latchOf p' y cl).1,
          (latchOf p' y cl).2⟩ : QRow 𝕂′))).map QRow.L =
      (slotsOf p' cl).flatMap fun s => (List.range s.words.length).map fun i => if i = 0 then slotL y s else 0 := by
    rw [List.map_map]
    refine (map_zip_fst_snd (fun u : 𝕂′ × 𝕂′ × 𝕂′ => u.2.2) _ _ hlen).trans ?_
    simp only [laneHL, List.map_flatMap, List.map_map, Function.comp_def]
  refine (sum_zip_mapL δ QRow.L (fun r L => GVL δ χ r L) _ _).trans ?_
  rw [hLs]
  rw [zip_flatMap_eq _ _ _ (fun s _ => by simp [slotRows]), ComplJ9ALBalX.sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  unfold cSlot slotRows
  exact sum_zip_range δ χ (slotRow p' cl s) (fun i => slotRow_aV_succ p' cl s i) (slotL y s) s.words.length

/-- The validity term of a big handle slot of value `v` at serial `sv` (`0` for a small value). -/
def ttV (χ : Coins frameJ8 K) (y : 𝕂′) (v sv : ℕ) : 𝕂′ :=
  if v < p then 0 else
    (ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩
      ![zJ δ χ, 0, horner y (Nock.Atoms.limbs v), 0, liftQ δ ((sv : ℕ) : ZMod p)])⁻¹

theorem cSlot_nonbig (χ : Coins frameJ8 K) (y : 𝕂′) (cl : CallL) (s : SlotL) (h0 : s.mode ≠ 0) (h2 : s.mode ≠ 2) :
    cSlot δ χ p y cl s = 0 := by
  unfold cSlot
  split_ifs
  · exact GVL_aV0 δ χ _ _ (by simp [slotRow, ind, h0, h2])
  · rfl

theorem cSlot_wit (χ : Coins frameJ8 K) (y : 𝕂′) (cl : CallL) (o : PrimOp) (lb r w : ℕ) :
    cSlot δ χ p y cl (witSlot o lb r w) = 0 :=
  cSlot_nonbig δ χ y cl _ (by simp [witSlot]) (by simp [witSlot])

theorem cSlot_q (χ : Coins frameJ8 K) (y : 𝕂′) (cl : CallL) (o : PrimOp) (packed : Bool) (qs : List ℤ) :
    cSlot δ χ p y cl (qSlot o packed qs) = 0 := by
  unfold qSlot
  split_ifs
  · exact cSlot_nonbig δ χ y cl _ (by simp) (by simp)
  · exact cSlot_nonbig δ χ y cl _ (by simp) (by simp)

theorem cSlot_handle (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (cl : CallL) (o : PrimOp)
    (lb r v k sv : ℕ) :
    cSlot δ χ p (AluPoles.yOf δ χ) cl (handleSlot p o lb r v k sv) = ttV δ χ (AluPoles.yOf δ χ) v sv := by
  unfold ttV
  by_cases hv : v < p
  · rw [if_pos hv]
    exact cSlot_nonbig δ χ _ cl _ (by simp [handleSlot, hv]) (by simp [handleSlot, hv])
  · rw [if_neg hv]
    have hl : 2 ≤ (Nock.Atoms.limbs v).length := ComplJ8Atom.limbs_big_len (by rw [← hpG]; omega)
    by_cases hf : isFactor o r = true
    · have e : handleSlot p o lb r v k sv = ⟨some r, 2, Nock.Atoms.limbs v, Nock.Atoms.limbs v, k, sv,
          (coefOf o lb (some r)).1, (coefOf o lb (some r)).2⟩ := by simp [handleSlot, hv, hf]
      rw [e]
      unfold cSlot
      simp only [slotRow, ind, slotL, GVL, liftQ]
      simp [hl, show 0 < (Nock.Atoms.limbs v).length by omega]
    · have e : handleSlot p o lb r v k sv = ⟨some r, 0, [0], Nock.Atoms.limbs v, k, sv,
          (coefOf o lb (some r)).1, (coefOf o lb (some r)).2⟩ := by simp [handleSlot, hv, hf]
      rw [e]
      unfold cSlot
      simp only [slotRow, ind, slotL, GVL, liftQ]
      simp

theorem ttV_small (χ : Coins frameJ8 K) (y : 𝕂′) (v sv : ℕ) (h : v < p) : ttV δ χ y v sv = 0 := by
  simp [ttV, h]

/-- **A call block's validity terms are those of its three operand handles** (`a`, `b`, `c`). -/
theorem slots_sum (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (cl : CallL) (hdec : cl.op ≠ .dec)
    (hlt : cl.op = .lt → cl.c < p) :
    ((slotsOf p cl).map fun s => cSlot δ χ p (AluPoles.yOf δ χ) cl s).sum =
      ttV δ χ (AluPoles.yOf δ χ) cl.a cl.vA + ttV δ χ (AluPoles.yOf δ χ) cl.b cl.vB +
        ttV δ χ (AluPoles.yOf δ χ) cl.c cl.vE := by
  unfold slotsOf
  cases ho : cl.op
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]; ring
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]; ring
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]
    rw [ttV_small δ χ _ _ _ (hlt ho)]; ring
  · exact absurd ho hdec
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]; ring
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]; ring
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, cSlot_handle δ hpG, cSlot_wit, cSlot_q]; ring

end SVRun

/-! ## 4. The ALU validity terminal is the `mb` read count against the atom-root providers -/

section SVEq
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ (evR)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom (D9 mbX extraPairs)
open Nock.V1J8.Gen (atomV)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

theorem horner_eq (y : 𝕂′) : ∀ ws : List ℕ, horner y ws = G5J8.horner y ws
  | [] => by simp [horner, evR, zl, G5J8.horner]
  | a :: ws => by
    have ih := horner_eq y ws
    simp only [horner, zl, List.map_cons, evR, Int.ofNat_eq_natCast, Int.cast_natCast, G5J8.horner] at ih ⊢
    rw [ih]

/-- **A big atom's validity key is the ALU's key** `[z, 0, Σ limbs·y^i, 0, sv]`. -/
theorem gOf_atom_big (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (v : ℕ) (hv : p ≤ v) (j : ℕ) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom v) ((j : ℕ) : ZMod p) =
      (ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩
        ![zJ δ χ, 0, horner (AluPoles.yOf δ χ) (Nock.Atoms.limbs v), 0, liftQ δ ((j : ℕ) : ZMod p)])⁻¹ := by
  have hlimbs : ∀ x ∈ Nock.Atoms.limbs v, x < Nock.Atoms.B := fun x hx => (Nock.Atoms.limbs_canonical v).1 x hx
  have hlv := G5J8.leafVal_val (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) hlimbs
    (by rw [Nock.Atoms.val_limbs, ← hpG]; exact hv)
  rw [Nock.Atoms.val_limbs] at hlv
  unfold gOf
  rw [InhabJ8Good.compress_split]
  refine congrArg (fun x => (ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ x)⁻¹) ?_
  funext c
  fin_cases c
  · rfl
  · rfl
  · show Nock.Atoms.leafVal (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) v = _
    rw [hlv]
    show _ = horner (AluPoles.yOf δ χ) (Nock.Atoms.limbs v)
    rw [horner_eq]; rfl
  · show Quad.mk (algebraMap (ZMod p) K δ) (algebraMap (ZMod p) K ((0 % 2 ^ 62 : ℕ) : ZMod p))
      (algebraMap (ZMod p) K ((0 / 2 ^ 62 : ℕ) : ZMod p)) = 0
    simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, map_zero]
    exact (Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩
  · rfl

theorem row_big (row : RowNX) (hrow : row ∈ (ComplJ8Data.rowsOfT t).toList) (n : Noun)
    (hn : n ∈ rowHandleNounsX row) (a : ℕ) (ha : a ∈ leavesOf n) (hp : p ≤ a) : a ∈ (DD).bigs := by
  show a ∈ ComplJ8Data.bigsP p (DD).roots (DD).rows
  refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hp⟩
  exact List.mem_flatMap.mpr ⟨n, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ha⟩

theorem hHL (a : ℕ) (ha : p ≤ a) : ((DL).H (.atom a)).2 = ComplJ8Data.rootIdxP p (DD).acs a := by
  show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom a)).2 = _
  simp [ComplJ8Data.hdlP, show ¬ a < p by omega]

variable (hpG : p = Nock.Atoms.p)
include hpG

/-- The ALU's validity term of a value `v` at its handle serial is the atom-root provider term. -/
theorem ttV_eq_bh {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DL).acs.length)) (χ : Coins frameJ8 K) (v : ℕ)
    (hbig : p ≤ v → v ∈ (DD).bigs) (sv : ℕ) (hsv : p ≤ v → sv = ComplJ8Data.rootIdxP p (DD).acs v) :
    ttV δ χ (AluPoles.yOf δ χ) v sv = bhL δ b Rt hgen prims o χ (.atom v) := by
  by_cases hv : v < p
  · rw [ttV_small δ χ _ _ _ hv]
    simp [bhL, ComplJ8Data.bigIdOfP, hv]
  · have hb : bhL δ b Rt hgen prims o χ (.atom v) = HBL δ b Rt hgen prims o χ (ComplJ8Data.rootIdxP p (DD).acs v) := by
      simp [bhL, ComplJ8Data.bigIdOfP, hv]
    rw [hb, ← keyL δ b Rt hgen prims hpG o hinj χ v (hbig (by omega)), gOf_atom_big δ hpG χ v (by omega)]
    unfold ttV
    rw [if_neg hv, hsv (by omega)]

omit hpG in
include hgen in
theorem pcall_facts (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ∀ x ∈ ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t),
      ∃ row ∈ (ComplJ8Data.rowsOfT t).toList, ∃ a c n, x = (atomV row.sf1, row.s, row.e) ∧
        row.s = .cell (.atom a) (.atom c) ∧ row.e = .atom n ∧
        Nock.Jet.Prim.primSem (ComplJ9ALData.opOf prims x.1) a c = some n ∧ ComplJ9ALData.opOf prims x.1 ≠ .dec := by
  intro x hx
  obtain ⟨row, hrow, hst, hid, hxe⟩ := mem_pcallsR hx
  obtain ⟨a, c, n, hs, he, hsem, hdec⟩ := AluCallOK.prim_row hgen hnd hprim hnoDec hrow hst hid
  refine ⟨row, hrow, a, c, n, hxe, hs, he, ?_, ?_⟩
  · rw [hxe]; exact hsem
  · rw [hxe]; exact hdec

/-- **The ALU validity terminal is the sum of the atom-root providers over the ALU's `mb` reads** (`aluBL`). -/
theorem SV_eq (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (n : ℕ) (χ : Coins frameJ8 K)
    (hlen : (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)).length ≤ n)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DL).acs.length)) :
    SV (p := p) δ Rt hgen prims n χ =
      ((ComplJ9ALData.aluBL p (DA).acs (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t))).map
        fun q => (q.2 : 𝕂′) * HBL δ b Rt hgen prims o χ q.1).sum := by
  have hfacts := pcall_facts hgen prims hnd hprim hnoDec
  unfold SV
  rw [Finset.sum_congr rfl (fun i _ => tV_eq' δ χ (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)) i)]
  rw [sum_rowAt δ _ (fun x => GVL δ χ x.1 x.2.L) (GVL_aV0 δ χ _ _ rfl) hlen]
  unfold tbR AluSatRun.tblRun AluSatRun.clsRun
  rw [tblP_sumV δ χ p _ _ _ (fun r hr => by
    obtain ⟨a1, a2, a3, a4, rfl⟩ := AluSatPreg.pregsP_preg _ _ _ r hr; rfl)]
  unfold ComplJ9ALData.aluBL
  rw [bigPairs_sum (ComplJ8Data.bigIdOfP p (DA).acs) (HBL δ b Rt hgen prims o χ), ComplJ9ALBalX.sum_map_flatMap]
  unfold AluHonestTable.callsLOf
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨row, hrow, a, c, n0, hxe, hs, he, hsem, hdec⟩ := hfacts x hx
  subst hxe
  simp only [Function.comp_apply]
  have hbA : ∀ x, x = a ∨ x = c → p ≤ x → x ∈ (DD).bigs := fun x hx hp =>
    row_big Rt hgen row hrow row.s (by simp [rowHandleNounsX]) x (by rw [hs]; rcases hx with rfl | rfl <;> simp [leavesOf]) hp
  have hbE : p ≤ n0 → n0 ∈ (DD).bigs := fun hp =>
    row_big Rt hgen row hrow row.e (by simp [rowHandleNounsX]) n0 (by rw [he]; simp [leavesOf]) hp
  rw [hs, he]
  refine (zipB_sumV δ χ p _ _).trans ((slots_sum δ hpG χ _ ?_ ?_).trans ?_)
  · simpa using hdec
  · intro hlt'
    have hp2 := (Fact.out : p.Prime).two_le
    simp only [] at hlt' hsem
    rw [hlt'] at hsem
    simp only [Nock.Jet.Prim.primSem, Option.some.injEq] at hsem
    show n0 < p
    split_ifs at hsem <;> omega
  · simp only [hdN', tlN', atomV]
    rw [ttV_eq_bh δ b Rt hgen prims hpG o hinj χ a (hbA a (Or.inl rfl)) _ (fun hp => hHL Rt hgen prims a hp),
      ttV_eq_bh δ b Rt hgen prims hpG o hinj χ c (hbA c (Or.inr rfl)) _ (fun hp => hHL Rt hgen prims c hp),
      ttV_eq_bh δ b Rt hgen prims hpG o hinj χ n0 hbE _ (fun hp => hHL Rt hgen prims n0 hp)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [add_assoc]
    rfl

end SVEq

/-! ## 5. `hsumC_L` -/

section SumC
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom (D9 mbX extraPairs)
open Nock.V1J8.Gen (atomV)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))
  (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A

include hpG h31A h31 in
/-- **`hsumC_L`**: the cell validity balance at the mixed record. -/
theorem hsumC_L (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (n : ℕ) (χ : Coins frameJ8 K)
    (hlen : (tbR (p := p) δ Rt hgen prims (AluPoles.yOf δ χ)).length ≤ n) :
    SV (p := p) δ Rt hgen prims n χ +
      ((ClaimJ9.claimRecsJ9 δ χ (ComplJ8.cJ s f r) ((BA).M χ).m ++
          AcceptsJ8P.pinRecsJ8 δ (B8L δ b Rt hgen prims hpG h31).Pb χ ++
          (psRun (p := p) Rt hgen prims).map fun q => ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ (primC q.2))
            ((vcRun (p := p) Rt hgen prims q.1 : ℕ) : ZMod p)
            (((ComplJ9ALData.rkPOf prims q.1).1 : ℕ) : ZMod p) (((ComplJ9ALData.rkPOf prims q.1).2 : ℕ) : ZMod p)).map
        fun x => (FiniteIO.compress (m := 5)
          ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((B8L δ b Rt hgen prims hpG h31).M χ).pubsC 0)
          (((B8L δ b Rt hgen prims hpG h31).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA AtomChipHQ.pubMB)
          (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA (AtomChipHQ.pubMB + 1)) := by
  have hbigC : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs :=
    fun n hn a h hp => ComplJ9BAtom.claim_leaf_big p Rg Rt hgen hn a (by subst h; simp [leavesOf]) hp
  have hmL : (DL).acs.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hinj := (powN_ok (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) (le_two_pow_ht (DL) hmL)).1
  have hm : ((BA).M χ).m = ComplJ8Comp.mCOf (DD).H (ComplJ8.cJ s f r) := rfl
  have hpC : ((B8L δ b Rt hgen prims hpG h31).M χ).pubsC = pubsCOf δ b (DL)
      (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ := rfl
  have hpA : ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA = pubsAOf δ b (DL)
      (ComplJ9ALData.acsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ := rfl
  rw [hm, hpC, hpA]
  have hcv : Quad.mk (algebraMap (ZMod p) K δ)
      (pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ 0)
      (pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ 1) =
      cvT δ (DL) χ := by
    have e0 : pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ 0 =
        pub2 δ (cvT δ (DL) χ) 0 := by
      simp [pubsCOf, pubsC0]
    have e1 : pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ 1 =
        pub2 δ (cvT δ (DL) χ) 1 := by
      simp [pubsCOf, pubsC0]
    rw [e0, e1]
    exact pub2_mk2 δ _ 0 rfl
  have hbb : ((DD).cells.map fun y =>
      btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (hdN y) +
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (tlN y)).sum =
      ((DD).cells.map fun y =>
        bhL δ b Rt hgen prims (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ (hdN' y) +
          bhL δ b Rt hgen prims (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ (tlN' y)).sum := by
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [bt_bhL δ b Rt hgen prims hpG _ hinj χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inl rfl) a ha hp,
      bt_bhL δ b Rt hgen prims hpG _ hinj χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inr rfl) a ha hp,
      hdN_eq, tlN_eq]
  have hpin := pin_sum_L δ Rt hgen prims hpG (B8L δ b Rt hgen prims hpG h31).Pb rfl rfl rfl (fun _ => rfl) χ
  unfold ClaimJ9.claimRecsJ9
  simp only [List.append_assoc, List.map_append, List.sum_append]
  rw [claim_sum δ Rt hgen χ, claimBig_sumL δ b Rt hgen prims hpG _ hinj χ hbigC, hpin,
    primPin_sum δ Rt hgen prims hpG hnd hprim χ, hcv, cvT_L δ Rt hgen prims hnd hprim χ,
    mbTL δ b Rt hgen prims hpG _ hinj χ,
    SV_eq δ b Rt hgen prims hpG hnd hprim hnoDec n χ hlen _ hinj, hbb]
  unfold ccG
  ring

end SumC

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalV2
