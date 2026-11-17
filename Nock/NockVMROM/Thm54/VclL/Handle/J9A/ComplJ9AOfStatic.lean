/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AOfStatic.lean

Targets (`ComplJ9AObl.ComplJ9AObligations` at `BA := BRun9A …`, verbatim forms):
  `hlay hsmall huniq hTpl hnd hidx hrk hlt` (`stat_A`), `hclI hclR hcen' hcellF` (`claim_A`),
  `hlenC hlenA hnAS hbud hbudV hlenX` (`budget_A`).

  * `stat_core` is J-8's `stat_run` with the three facts it takes from the row binder (`jrows`, `cells`, `bfs`
    sizes `< p`) and from `hax` (`calls_lt`: every call id `< p`) as hypotheses; they are derived from `h31A` and
    `hax9` (`calls_lt9`: the `s11j` clause of `AxRowX9A`).
  * `claim_A` copies J-9 B's `claim_run9` at `DA` (the atom count `nA` and the roots are `j8DataOf`'s).
  * `budget_A`: `BudJ9A` at `rowsA9` is linear arithmetic (`bud_generic`); `hnAS`, `hlenX` come from `h31A` and
    `2^63 < p`; no `hW` binder is needed.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A AxRowX9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

noncomputable section

/-! ## 1. The static obligation -/

section Stat
variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

include hgen in
/-- **Every call's id is `< p`** from the J-9 A axis binder (the `s11j` clause of `AxRowX9A` is `AxRowX`'s). -/
theorem calls_lt9 (hax9 : ProgAxOK9A p t) :
    ∀ cl ∈ Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t), cl.1 < p := by
  intro cl hcl
  obtain ⟨u, hu, hst, hft⟩ := calls_called hgen cl hcl
  have h := hax9 u hu
  unfold AxRowX9A at h
  rw [hst] at h
  exact h.2 _ hft

/-- **The static obligation** (J-8's `stat_run`, with `hax` replaced by the call-id bound `hlt` and the row binder
by the three sizes it reads). -/
theorem stat_core (hp63 : 2 ^ 63 < p)
    (hlt : ∀ cl ∈ Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t), cl.1 < p)
    (hjl : (j8DataOf p Rg Rt hgen).jrows.length < p) (hcells : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hbfs : (bfsForest [(j8DataOf p Rg Rt hgen).t]).length < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length) :
    List.ofFn (Nock.Jet.ChipJ8T.HonestRAP.layJ (j8DataOf p Rg Rt hgen).jrows.get) =
      layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids ∧
    (∀ q ∈ layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids,
      q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ (j8DataOf p Rg Rt hgen).regs, Rg.R i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p) ∧
    (j8DataOf p Rg Rt hgen).regs.Nodup ∧ (∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).idx id < p) ∧
    (∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).rk id ≠ (0, 0)) ∧
    (∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ((j8DataOf p Rg Rt hgen).rk id).1 < ringChar (ZMod p) ∧
      ((j8DataOf p Rg Rt hgen).rk id).2 < ringChar (ZMod p) ∧ (j8DataOf p Rg Rt hgen).idx id < ringChar (ZMod p)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hcl := calls_called hgen
  have hmemR : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∃ cl ∈ (j8DataOf p Rg Rt hgen).calls, cl.1 = id := by
    intro id hid
    have := List.mem_dedup.mp hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp this
    exact ⟨cl, hcl, e⟩
  have hlay : List.ofFn (Nock.Jet.ChipJ8T.HonestRAP.layJ (j8DataOf p Rg Rt hgen).jrows.get) =
      layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids := by
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen]
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [Nock.Jet.ChipJ8T.HonestRAP.layJ]
  have hJlen : (layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).length < p := by
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen, List.length_map]
    exact hjl
  have hidsl : (j8DataOf p Rg Rt hgen).ids.length < p := by
    have h1 : (j8DataOf p Rg Rt hgen).ids.length ≤ (bfsForest [(j8DataOf p Rg Rt hgen).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 hbfs
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls
    hcalls hlt hJlen
  have hroot : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs,
      Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).roots := by
    intro id hid
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hne : (j8DataOf p Rg Rt hgen).cells ≠ [] := List.ne_nil_of_length_pos hC
  have hidx : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).idx id < p :=
    fun id _ => lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hcells.le
  have hrk : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).rk id ≠ (0, 0) :=
    fun id _ => rk_ne _ (ComplJ8Data.compile_isCell p (Rt id))
  have hrkl : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ((j8DataOf p Rg Rt hgen).rk id).1 < p ∧
      ((j8DataOf p Rg Rt hgen).rk id).2 < p := by
    intro id hid
    have hl := hleaf _ (hroot id hid)
    have hi := ComplJ8Walk.internal_lt_leaves (Nock.Jet.Autogen.compile p (Rt id))
    have h62 : (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
    have hd : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 ≤ (Nock.Jet.Autogen.compile p (Rt id)).internal :=
      Nat.div_le_self _ _
    have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    refine ⟨?_, ?_⟩
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < p
      have : (Nock.Jet.Autogen.compile p (Rt id)).internal < 2 ^ 109 := lt_of_lt_of_le hi hl
      have h109 : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < 2 ^ 47 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 109 := this
          _ = 2 ^ 47 * 2 ^ 62 := by rw [← pow_add]
      have : (2 : ℕ) ^ 47 < 2 ^ 63 := by norm_num
      omega
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < p
      omega
  refine ComplJ8Jet.stat_of hp Rt _ _ _ _ _ ⟨Rt, hRt⟩ hRt (fun i hi => ?_) hlay (fun i hi => ?_) hidsl
    hblk (List.nodup_dedup _) hidx hrk (fun id hid => ?_)
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hcl cl hcl'
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'
  · rw [hrc]; exact ⟨(hrkl id hid).1, (hrkl id hid).2, hidx id hid⟩

end Stat

/-! ## 2. The run-level facts -/

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

/-- The size memberships of the J-9 A row binder. -/
theorem mem_cells : (DA).cells.length ∈ sizesA (DA) := List.mem_append_left _ (by simp [sizesJ8])
theorem mem_jrows : (DA).jrows.length ∈ sizesA (DA) := List.mem_append_left _ (by simp [sizesJ8])
theorem mem_acs : (DA).acs.length ∈ sizesA (DA) := List.mem_append_left _ (by simp [sizesJ8])
theorem mem_nC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
theorem mem_nV : nVOf (DA) ∈ sizesA (DA) := List.mem_append_left _ (by simp [sizesJ8])
theorem mem_bfs : (bfsForest [(DA).t]).length ∈ sizesA (DA) := List.mem_append_left _ (by simp [sizesJ8])
theorem mem_N9 : N9 t ∈ sizesA (DA) := List.mem_append_right _ List.mem_cons_self
theorem mem_nX : nXOf p (DA).acs.length (DA).H t ∈ sizesA (DA) :=
  List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_nS : nSOf p t ∈ sizesA (DA) :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem p63 (hpG : p = Nock.Atoms.p) : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]

theorem lt_p {x : ℕ} (hpG : p = Nock.Atoms.p) (hx : x ≤ 2 ^ 31) : x < p := by
  have := p63 (p := p) hpG
  have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  omega

/-- **`hlay … hlt` at `BRun9A`.** -/
theorem stat_A (hax9 : ProgAxOK9A p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    List.ofFn (BA).Pb.lay = layoutJ8 (BA).Pb.Rt (BA).Pb.regs (BA).Pb.ids ∧
    (∀ q ∈ layoutJ8 (BA).Pb.Rt (BA).Pb.regs (BA).Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 (BA).Pb.Rt (BA).Pb.regs (BA).Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ (BA).Pb.regs, Rg.R i = some ⟨((BA).Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p ((BA).Pb.Rt i)⟩ ∧
      axPosB ((BA).Pb.Rt i) = true ∧ ((BA).Pb.Rt i).WellTyped p) ∧
    (BA).Pb.regs.Nodup ∧ (∀ id ∈ (BA).Pb.regs, (BA).Pb.idx id < p) ∧
    (∀ id ∈ (BA).Pb.regs, (BA).Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ (BA).Pb.regs, ((BA).Pb.rk id).1 < ringChar (ZMod p) ∧ ((BA).Pb.rk id).2 < ringChar (ZMod p) ∧
      (BA).Pb.idx id < ringChar (ZMod p)) :=
  stat_core Rt hgen (p63 hpG) (calls_lt9 hgen hax9)
    (lt_p hpG (h31A _ (mem_jrows Rt hgen))) (lt_p hpG (h31A _ (mem_cells Rt hgen)))
    (lt_p hpG (h31A _ (mem_bfs Rt hgen))) hleaf hRt (ComplJ8Of.cells_pos Rt hgen)

/-! ## 3. The claim fields -/

/-- **`hclI hclR hcen' hcellF` at `BRun9A`** (J-9 B's `claim_run9` at `DA`). -/
theorem claim_A (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots) :
    (∀ χ : Coins frameJ8 K, ∀ k : Fin 3, (FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true ∨
        ClaimJ9.isBigN p (FrameVS.claimNoun (cJ s f r) k) = true) → (((BA).M χ).m k).1 < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true →
      (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ ClaimJ9.censusGJ9 (BA).Pb.toPubJ8 (cJ s f r),
      x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ (BA).Pb.nA + 2) ∧
    FrameVS.isCellN (cJ s f r).formula = true := by
  have hp63 := p63 (p := p) hpG
  have hroot : ∀ k : Fin 3, FrameVS.claimNoun (cJ s f r) k ∈ (DD).roots := by
    intro k
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    fin_cases k <;> simp [FrameVS.claimNoun, cJ]
  have hregR : ∀ id ∈ (DD).regs, Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots := fun id hid => by
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hA : (DA).acs.length < p := lt_p hpG (h31A _ (mem_acs Rt hgen))
  have hCl : (DA).cells.length < p := lt_p hpG (h31A _ (mem_cells Rt hgen))
  have hne : (DD).cells ≠ [] := List.ne_nil_of_length_pos (ComplJ8Of.cells_pos Rt hgen)
  have hneA : (DD).acs ≠ [] := List.ne_nil_of_length_pos (ComplJ8Of.acs_pos Rt hgen)
  have hcf : FrameVS.isCellN (cJ s f r).formula = true := by
    obtain ⟨a, c, hfc⟩ := formula_cell_of_gen hgen
    simp [cJ, hfc, FrameVS.isCellN]
  refine ⟨fun χ k hk => ?_, fun k hk => ?_, fun x hx => ?_, hcf⟩
  · show ((DD).H (FrameVS.claimNoun (cJ s f r) k)).2 < p
    generalize FrameVS.claimNoun (cJ s f r) k = x at hk
    cases x with
    | atom v =>
      rcases hk with hk | hk
      · simp [FrameVS.isCellN] at hk
      · have hv : p ≤ v := by simpa [ClaimJ9.isBigN] using hk
        show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom v)).2 < p
        simp only [ComplJ8Data.hdlP, if_neg (show ¬ v < p by omega)]
        exact lt_trans (ComplJ8Data.rootIdxP_lt p _ hneA v) hA
    | cell a c => exact lt_trans (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hCl
  · have h1 := (Noun.pbt_size (FrameVS.claimNoun (cJ s f r) k)).2
    have h2 := hleaf _ (hroot k)
    have : (FrameVS.claimNoun (cJ s f r) k).internal < 2 ^ 110 := by
      have : (2 : ℕ) ^ 109 < 2 ^ 110 := by norm_num
      omega
    have h3 : (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < 2 ^ 48 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 110 := this
        _ = 2 ^ 48 * 2 ^ 62 := by rw [← pow_add]
    have : (2 : ℕ) ^ 48 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  · have hxr : x ∈ (DD).roots := by
      simp only [ClaimJ9.censusGJ9, AcceptsJ8P.censusG, List.mem_append, List.mem_map] at hx
      rcases hx with (⟨id, hid, rfl⟩ | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
      · exact hregR id hid
      · exact hroot k
      · exact hroot k
    exact ⟨(hleaf _ hxr).trans (by unfold fuelChip; norm_num),
      fun v hv => ComplJ9BOf.lenL_root Rt hgen hpG hxr v hv⟩

/-! ## 4. The budget and length fields -/

theorem regs_le' (hbfs : (bfsForest [(DD).t]).length ≤ 2 ^ 31) : (DD).regs.length ≤ 2 ^ 31 := by
  have h1 : (DD).regs.length ≤ (DD).calls.length := by
    show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).dedup.length ≤ _
    exact (List.dedup_sublist _).length_le.trans (by simp; rfl)
  have h2 : (DD).calls.length ≤ (bfsForest [(DD).t]).length := by
    show (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).length ≤ _
    unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
    exact (List.length_filterMap_le _ _).trans (by simp; rfl)
  exact h1.trans (h2.trans hbfs)

/-- The J-9 A budget at the canonical rows, for any layout. -/
theorem bud_generic (Pb : PubJ9A p) :
    BudJ9A Pb (rowsA9 Pb) (ComplJ8Comp.canonG Pb.toPubJ8 + (rowsA9 Pb).N) ∧
    (Pb.regs.length ≤ ComplJ8Comp.canonG Pb.toPubJ8 ∧ Pb.nA ≤ (rowsA9 Pb).mb ∧ Pb.nA ≤ (rowsA9 Pb).A ∧
      Pb.nV ≤ (rowsA9 Pb).AW ∧ Pb.nX ≤ (rowsA9 Pb).AX ∧ Pb.nS ≤ (rowsA9 Pb).SP) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rowsA9, ComplJ8Comp.canonRows, ComplJ8Comp.canonG] <;> omega

/-- **`hlenC hlenA hnAS hbud hbudV hlenX` at `BRun9A`.** -/
theorem budget_A :
    3 + (BA).Pb.regs.length + 2 * (BA).Pb.nC < p ∧ (BA).Pb.nA + (BA).Pb.nV < p ∧
    (BA).Pb.nA + (BA).Pb.nS < 2 ^ 57 ∧
    BudJ9A (BA).Pb (BA).rows ((BA).g + (BA).rows.N) ∧
    ((BA).Pb.regs.length ≤ (BA).g ∧ (BA).Pb.nA ≤ (BA).rows.mb ∧ (BA).Pb.nA ≤ (BA).rows.A ∧
      (BA).Pb.nV ≤ (BA).rows.AW ∧ (BA).Pb.nX ≤ (BA).rows.AX ∧ (BA).Pb.nS ≤ (BA).rows.SP) ∧
    ((BA).Pb.nX + (BA).Pb.n < p ∧ 2 * (BA).Pb.nS < p) := by
  have hp := p63 (p := p) hpG
  have e31 : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  have e57 : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 57 := by norm_num
  have hbfs : (bfsForest [(DD).t]).length ≤ 2 ^ 31 := h31A _ (mem_bfs Rt hgen)
  have hreg : (DA).regs.length ≤ 2 ^ 31 := regs_le' Rt hgen hbfs
  have hC : (DA).cells.length ≤ 2 ^ 31 := h31A _ (mem_cells Rt hgen)
  have hAc : (DA).acs.length ≤ 2 ^ 31 := h31A _ (mem_acs Rt hgen)
  have hV : nVOf (DA) ≤ 2 ^ 31 := h31A _ (mem_nV Rt hgen)
  have hN : N9 t ≤ 2 ^ 31 := h31A _ (mem_N9 Rt hgen)
  have hX : nXOf p (DA).acs.length (DA).H t ≤ 2 ^ 31 := h31A _ (mem_nX Rt hgen)
  have hS : nSOf p t ≤ 2 ^ 31 := h31A _ (mem_nS Rt hgen)
  obtain ⟨b1, b2⟩ := bud_generic (BA).Pb
  refine ⟨?_, ?_, ?_, b1, b2, ?_, ?_⟩
  · show 3 + (DA).regs.length + 2 * (DA).cells.length < p
    omega
  · show (DA).acs.length + nVOf (DA) < p
    omega
  · show (DA).acs.length + nSOf p t < 2 ^ 57
    omega
  · show nXOf p (DA).acs.length (DA).H t + N9 t < p
    omega
  · show 2 * nSOf p t < p
    omega

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic
#print axioms calls_lt9
#print axioms stat_core
#print axioms stat_A
#print axioms claim_A
#print axioms bud_generic
#print axioms budget_A
end Axioms
