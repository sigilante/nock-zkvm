/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Jet.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.Jet.ChipJ8THonestRAP
import Nock.Jet.ChipJ8Toy
import Nock.Jet.ChipJ8HG
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet

open Nock Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Walk Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.Jet.ChipJ8 (PRow chainPre nodePre nodesPre blockPre blocks callPre regPre layoutJ8 tvKey axPosB jetChipJ8 CRow baseGatesJ envOf keysOf ents3 entsX)
open Nock.Jet.RapJetJ8 (coinsJ coinsJX consKT provKT keyK)
open Nock.Jet.ChipJ8T.HonestRAP (polyJC layJ termJ sX)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.MonolithicRAP Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsJJ8)
open Polynomial

noncomputable section

/-! ## 1. The binder `hregC` -/

/-- The jet ids the run CALLS: the atom `sf1`, the clue's value, of every `s11j` row of the generated
tree.  (The tag `f_tth` of such a row is always `%wild`.) -/
def CalledIds (t : NTree SkelX) : Set ℕ :=
  {id | ∃ u, InTree t u ∧ (rowOfSkelX u.label).st = .s11j ∧ (rowOfSkelX u.label).sf1 = .atom id}

/-- **Binder `hregC`**: every jet the run calls is registered in compiled form, i.e. as an entry of
`VerifiedRegistry.ofCompiled p _ Rt regs _` for some template table `Rt` whose called entries are well typed with
`axPosB`: `Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩`.  (A hand-added `VerifiedRegistry.add` entry
has no `Rt`, so a run that calls it does not satisfy `HregC`.) -/
def HregC (p : ℕ) (Rg : Nock.Jet.VerifiedRegistry) (t : NTree SkelX) : Prop :=
  ∃ Rt : ℕ → Nock.Jet.Autogen.Tpl, ∀ id ∈ CalledIds t,
    Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p

/-- **hregC gives the `hTpl` pin** for any id list drawn from the called ids: with `Rt` the witness of `HregC`,
`Rg.R i` is the compiled template, `axPosB`, well typed. -/
theorem hTpl_of_hregC {p : ℕ} {Rg : Nock.Jet.VerifiedRegistry} {t : NTree SkelX} (h : HregC p Rg t)
    (regs : List ℕ) (hreg : ∀ i ∈ regs, i ∈ CalledIds t) :
    ∃ Rt : ℕ → Nock.Jet.Autogen.Tpl, ∀ i ∈ regs,
      Rg.R i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
        axPosB (Rt i) = true ∧ (Rt i).WellTyped p := by
  obtain ⟨Rt, hRt⟩ := h
  exact ⟨Rt, fun i hi => hRt i (hreg i hi)⟩

/-! ## 2. The J chip at good coins -/

section JChip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- **The J tagged denominator keys** of a row list (every key whose `den` must be nonzero at the J coins). -/
def jKeysT {n : ℕ} (rows : Fin n → CRow (ZMod p)) : List (List (ZMod p)) :=
  (List.finRange n).flatMap fun i => consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i)

/-- The J export denominator keys. -/
def jKeysX {n : ℕ} (rows : Fin n → CRow (ZMod p)) : List (List (ZMod p)) :=
  (List.finRange n).flatMap fun i => keysOf entsX (rows i)

/-- **The J pole event at `chals`** (the bad event of the J chip): some tagged or export key denominator is `0`. -/
def JPole {n : ℕ} (rows : Fin n → CRow (ZMod p)) (chals : ℕ → K) : Prop :=
  (∃ κ ∈ jKeysT rows, compress (coinsJ δ chals) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) (keyK (K := K) 8 κ)) = 0) ∨
  (∃ κ ∈ jKeysX rows, compress (coinsJX δ chals) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) (keyK (K := K) 5 κ)) = 0)

/-- Outside the pole event the two denominator hypotheses of the J chip's honest theorem hold. -/
theorem noPole {n : ℕ} (rows : Fin n → CRow (ZMod p)) (chals : ℕ → K) (h : ¬ JPole δ rows chals) :
    (∀ i, ∀ κ ∈ consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i),
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0) ∧
    (∀ i, ∀ κ ∈ keysOf entsX (rows i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0) := by
  constructor
  · intro i κ hκ h0
    exact h (Or.inl ⟨κ, List.mem_flatMap.2 ⟨i, List.mem_finRange i, hκ⟩, h0⟩)
  · intro i κ hκ h0
    exact h (Or.inr ⟨κ, List.mem_flatMap.2 ⟨i, List.mem_finRange i, hκ⟩, h0⟩)

/-- **`jOK`, present case**: with at least one J row, base gates on every row, no J pole, and the four publics
equal to the honest totals `Σ termJ`, `Σ sX`, the honest J trace `polyJC` satisfies and binds the J chip. -/
theorem jOK_present {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (rows : Fin n → CRow (ZMod p))
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ i, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (rows i)) = 0)
    (hpole : ¬ JPole δ rows chals)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = ∑ i, termJ δ chals (rows i))
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i)) :
    JGenJ8.JChipOK δ b nodes orbit chals pubs (layJ rows) (polyJC δ b nodes orbit chals pubs rows) := by
  obtain ⟨hpT, hpX⟩ := noPole δ rows chals hpole
  have hsat := Nock.Jet.ChipJ8T.HonestRAP.jetChipJ8_honest_sat δ b nodes orbit chals pubs rows hinj hn hadj hgate
    hpT hpX hp01 hp23
  exact Or.inl ⟨hsat.1, hsat.2, hinj, hn, hadj⟩

/-- **`jOK`, absent case** (no call): `nJ = 0` and the four J publics are `0`. -/
theorem jOK_absent {h nJ : ℕ} (nodes : Fin nJ → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (lay : Fin nJ → Nock.Jet.ChipJ8.PRow)
    (PJ : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → Polynomial (ZMod p))
    (h0 : nJ = 0) (hp : pubs 0 = 0 ∧ pubs 1 = 0 ∧ pubs 2 = 0 ∧ pubs 3 = 0) :
    JGenJ8.JChipOK δ b nodes orbit chals pubs lay PJ :=
  Or.inr ⟨h0, hp⟩

end JChip

/-! ## 3. The static layout facts (`hsmall`, `huniq`) from per-template block checks -/

section Layout
open Nock.Jet.ChipJ8

/-- Re-index a layout row to call `c`. -/
def setC (c : ℕ) (q : PRow) : PRow := { q with cid := c }

theorem chainPre_setC (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ),
    chainPre c dst src ctr bs = (chainPre 0 dst src ctr bs).map (setC c)
  | [], src, ctr => by simp [chainPre, setC]
  | b :: bs, src, ctr => by
    simp only [chainPre, setC, List.map_cons, chainPre_setC c dst bs, List.map_map]

theorem nodePre_setC (c S ctr : ℕ) (nd : Nock.Jet.Interp.JNode) :
    nodePre c S ctr nd = (nodePre 0 S ctr nd).map (setC c) := by
  unfold nodePre
  split <;> first | (rw [chainPre_setC]) | simp [setC]

theorem nodesPre_setC (c S : ℕ) : ∀ (nds : List Nock.Jet.Interp.JNode) (ctr : ℕ),
    nodesPre c S ctr nds = (nodesPre 0 S ctr nds).map (setC c)
  | [], ctr => by simp [nodesPre]
  | nd :: nds, ctr => by simp [nodesPre, nodePre_setC c S ctr nd, nodesPre_setC c S nds]

theorem blockPre_setC (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) :
    blockPre R c i = (blockPre R 0 i).map (setC c) := by
  simp [blockPre, callPre, setC, nodesPre_setC c]

theorem tvKey_setC (c : ℕ) (q : PRow) : tvKey (setC c q) = (tvKey q).map fun k => (c, k.2) := by
  by_cases h : q.kd = .reg <;> simp [tvKey, setC, PRow.pn, h] <;> rfl

theorem blockPre_cid (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) : ∀ q ∈ blockPre R c i, q.cid = c := by
  intro q hq
  rw [blockPre_setC] at hq
  obtain ⟨q', -, rfl⟩ := List.mem_map.1 hq
  rfl

theorem blocks_cid_ge (R : ℕ → Nock.Jet.Autogen.Tpl) : ∀ (ids : List ℕ) (c0 : ℕ), ∀ q ∈ blocks R c0 ids, c0 ≤ q.cid
  | [], c0, q, hq => by simp [blocks] at hq
  | i :: is, c0, q, hq => by
    rcases List.mem_append.1 (by simpa [blocks] using hq) with h | h
    · rw [blockPre_cid R c0 i q h]
    · exact le_trans (Nat.le_succ c0) (blocks_cid_ge R is (c0 + 1) q h)

/-- Per-template block check (call-index independent, so decidable per template). -/
def BlockOK (p : ℕ) (R : ℕ → Nock.Jet.Autogen.Tpl) (i : ℕ) : Prop :=
  ((blockPre R 0 i).filterMap tvKey).Nodup ∧
    ∀ q ∈ blockPre R 0 i, q.id < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p

theorem filterMap_map_opt {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, l.filterMap (fun a => (f a).map g) = (l.filterMap f).map g
  | [] => rfl
  | a :: l => by
    cases h : f a <;> simp [List.filterMap_cons, h, filterMap_map_opt f g l]

theorem tvKey_cid {q : PRow} {k : ℕ × ℕ} (h : tvKey q = some k) : k.1 = q.cid := by
  unfold tvKey at h
  split at h
  · simp at h
  · simp at h; subst h; rfl

theorem blocks_keys_nodup (R : ℕ → Nock.Jet.Autogen.Tpl) :
    ∀ (ids : List ℕ) (c0 : ℕ), (∀ i ∈ ids, ((blockPre R 0 i).filterMap tvKey).Nodup) →
      ((blocks R c0 ids).filterMap tvKey).Nodup
  | [], c0, _ => by simp [blocks]
  | i :: is, c0, h => by
    have hb : (blockPre R c0 i).filterMap tvKey =
        ((blockPre R 0 i).filterMap tvKey).map fun k => (c0, k.2) := by
      rw [blockPre_setC, List.filterMap_map]
      have : (tvKey ∘ setC c0) = fun q => (tvKey q).map fun k => (c0, k.2) := by
        funext q; exact tvKey_setC c0 q
      rw [this, filterMap_map_opt]
    have h0 : ∀ k ∈ (blockPre R 0 i).filterMap tvKey, k.1 = 0 := by
      intro k hk
      obtain ⟨q, hq, hqk⟩ := List.mem_filterMap.1 hk
      rw [tvKey_cid hqk, blockPre_cid R 0 i q hq]
    have hnd : ((blockPre R c0 i).filterMap tvKey).Nodup := by
      rw [hb]
      refine (h i (List.mem_cons_self ..)).map_on ?_
      intro x hx y hy hxy
      have := h0 x hx; have := h0 y hy
      simp only [Prod.mk.injEq, true_and] at hxy
      exact Prod.ext (by omega) hxy
    have hrest := blocks_keys_nodup R is (c0 + 1) (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))
    simp only [blocks, List.filterMap_append]
    refine List.nodup_append.2 ⟨hnd, hrest, ?_⟩
    intro k hk k' hk' hkk
    obtain ⟨q, hq, hqk⟩ := List.mem_filterMap.1 hk
    obtain ⟨q', hq', hqk'⟩ := List.mem_filterMap.1 hk'
    have e1 := tvKey_cid hqk
    have e2 := tvKey_cid hqk'
    rw [blockPre_cid R c0 i q hq] at e1
    have := blocks_cid_ge R is (c0 + 1) q' hq'
    subst hkk
    omega

/-- **`huniq` from the per-template checks.** -/
theorem huniq_of_blocks (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ)
    (h : ∀ i ∈ ids, ((blockPre Rt 0 i).filterMap tvKey).Nodup) :
    ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup := by
  unfold layoutJ8
  rw [List.filterMap_append]
  have h1 : (regs.map regPre).filterMap tvKey = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro q hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    simp [tvKey, regPre]
  rw [h1, List.nil_append]
  exact blocks_keys_nodup Rt ids 0 h

/-- **`hsmall` from the per-template checks**: ids and regs `< p`, the number of calls `< p`. -/
theorem hsmall_of_blocks {p : ℕ} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ)
    (hreg : ∀ i ∈ regs, i < p) (hcl : ids.length < p)
    (hb : ∀ i ∈ ids, ∀ q ∈ blockPre Rt 0 i, q.id < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) (hp : 0 < p) :
    ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p := by
  have key : ∀ (ids : List ℕ) (c0 : ℕ), c0 + ids.length ≤ p → (∀ i ∈ ids, ∀ q ∈ blockPre Rt 0 i,
      q.id < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) →
      ∀ q ∈ blocks Rt c0 ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p := by
    intro ids
    induction ids with
    | nil => intro c0 _ _ q hq; simp [blocks] at hq
    | cons i is ih =>
      intro c0 hc hb q hq
      rcases List.mem_append.1 (by simpa [blocks] using hq) with h | h
      · rw [blockPre_setC] at h
        obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 h
        obtain ⟨a, b, c, d⟩ := hb i (List.mem_cons_self ..) q0 hq0
        simp only [List.length_cons] at hc
        exact ⟨a, by simp [setC]; omega, b, c, d⟩
      · exact ih (c0 + 1) (by simp only [List.length_cons] at hc; omega)
          (fun i' hi' => hb i' (List.mem_cons_of_mem _ hi')) q h
  intro q hq
  unfold layoutJ8 at hq
  rcases List.mem_append.1 hq with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    simp [regPre]
    exact ⟨hreg i hi, hp⟩
  · exact key ids 0 (by omega) hb q h

end Layout

/-! ## 4. The `stat` obligation -/

section Stat
variable {p : ℕ} [Fact p.Prime]

/-- **The J registry/layout statics from `hregC` and per-template block checks**, over plain parameters (the
registry `Rg`, the template table `Rt`, the registered ids `regs`, the call ids `ids`, the layout list `lay`, the
pin data `idx`, `rk`): `hlay hsmall huniq hTpl hnd hidx hrk hlt` of the verifier's registry block. -/
theorem stat_of {Rg : Nock.Jet.VerifiedRegistry} {t : NTree SkelX} (hp : 0 < p)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) {nJ : ℕ} (lay : Fin nJ → PRow)
    (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (hreg : HregC p Rg t) (hRtW : ∀ i ∈ CalledIds t, Rg.R i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hregs : ∀ i ∈ regs, i ∈ CalledIds t)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hregp : ∀ i ∈ regs, i < p) (hcl : ids.length < p)
    (hblk : ∀ i ∈ ids, BlockOK p Rt i)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧
      idx id < ringChar (ZMod p)) :
    List.ofFn lay = layoutJ8 Rt regs ids ∧
    (∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ regs, Rg.R i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p) ∧
    regs.Nodup ∧ (∀ id ∈ regs, idx id < p) ∧ (∀ id ∈ regs, rk id ≠ (0, 0)) ∧
    (∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p)) :=
  ⟨hlay, hsmall_of_blocks Rt regs ids hregp hcl (fun i hi => (hblk i hi).2) hp,
    huniq_of_blocks Rt regs ids (fun i hi => (hblk i hi).1), fun i hi => hRtW i (hregs i hi), hnd, hidx, hrk, hlt⟩

end Stat

/-! ## 5. The honest J rows of an arbitrary run: layout -/

section Rows
open Nock.Jet.ChipJ8 Nock.Jet.Interp
variable {p : ℕ} [Fact p.Prime]

/-- **The honest J rows have the verifier's layout** (any run: registered ids `regs`, call list `calls`). -/
theorem honestJ8_pre (hd : Noun → ZMod p × ZMod p) (R : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ)
    (calls : List (ℕ × Noun)) :
    (honestJ8G (p := p) hd R regs calls).map CRow.pre = layoutJ8 R regs (calls.map Prod.fst) :=
  honestJ8G_pre hd R regs calls

/-- The honest `mv`: in-chip consumers plus registry pins (HJ2 `rowsPin`, over any prime field). -/
def mvPinG (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) (r : CRow (ZMod p)) : ZMod p :=
  match provKT r with
  | [k] => (((rows.flatMap consKT).count k + pins.count k : ℕ) : ZMod p)
  | _ => 0

def rowsPinG (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) : List (CRow (ZMod p)) :=
  rows.map fun r => { r with w := { r.w with mv := mvPinG rows pins r } }

theorem rowsPinG_pre (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    (rowsPinG rows pins).map CRow.pre = rows.map CRow.pre := by
  simp [rowsPinG, Function.comp_def]

/-- **The J rows of a run**: the honest rows with the `mv` fix, over the run's cell memory `hd`, template
table `Rt`, registered ids `regs`, call list `calls` (all parameters) and registry pins `pins`. -/
def jRowsOf (hd : Noun → ZMod p × ZMod p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (pins : List (List (ZMod p))) : List (CRow (ZMod p)) :=
  rowsPinG (honestJ8G (p := p) hd Rt regs calls) pins

theorem jRowsOf_pre (hd : Noun → ZMod p × ZMod p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (pins : List (List (ZMod p))) :
    (jRowsOf hd Rt regs calls pins).map CRow.pre = layoutJ8 Rt regs (calls.map Prod.fst) := by
  rw [jRowsOf, rowsPinG_pre, honestJ8_pre]

/-- `layJ` of the rows (as a `Fin n` family) is the layout. -/
theorem layJ_get (rows : List (CRow (ZMod p))) :
    layJ (n := rows.length) rows.get = fun i => (rows.get i).pre := rfl

theorem ofFn_layJ_get (hd : Noun → ZMod p × ZMod p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ)
    (calls : List (ℕ × Noun)) (pins : List (List (ZMod p))) :
    List.ofFn (layJ (jRowsOf hd Rt regs calls pins).get) = layoutJ8 Rt regs (calls.map Prod.fst) := by
  rw [← jRowsOf_pre hd Rt regs calls pins]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [layJ]

end Rows

/-! ## 6. The J trace at the chip width, the `qJ` bridge, and staging -/

section Trace
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

open Nock.Jet.ChipJ8T.HonestRAP (polyJ colJ)

/-- **The J trace** at the chip width `71`: the honest column interpolants at the coins `chals`. -/
def trJ {n : ℕ} (nodes : Fin n → ZMod p) (chals : ℕ → K) (rows : Fin n → CRow (ZMod p)) :
    Fin 71 → (ZMod p)[X] := polyJ δ b chals rows nodes 71

/-- **The `qJ` bridge**: `AcceptsJ8.qJ` (a trace `tr.J` read at `Fin.cast width`) is the honest `polyJC` when
`tr.J = trJ`. -/
theorem polyJC_eq_trJ {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (rows : Fin n → CRow (ZMod p)) :
    polyJC δ b nodes orbit chals pubs rows =
      fun j => trJ δ b nodes chals rows
        (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width δ b nodes orbit chals pubs (layJ rows)) j) := rfl

/-- **`jOK`, present case, in the `qJ` form** (`tr.J = trJ`). -/
theorem jOK_present_trJ {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (rows : Fin n → CRow (ZMod p))
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ i, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (rows i)) = 0)
    (hpole : ¬ JPole δ rows chals)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = ∑ i, termJ δ chals (rows i))
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i)) :
    JGenJ8.JChipOK δ b nodes orbit chals pubs (layJ rows)
      (fun j => trJ δ b nodes chals rows
        (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width δ b nodes orbit chals pubs (layJ rows)) j)) :=
  jOK_present δ b nodes orbit chals pubs rows hinj hn hadj hgate hpole hp01 hp23

/-- Columns `< 29` of the J trace read no coin. -/
theorem trJ_coinfree {n : ℕ} (nodes : Fin n → ZMod p) (chals chals' : ℕ → K) (rows : Fin n → CRow (ZMod p))
    (j : Fin 71) (hj : (j : ℕ) < 29) :
    trJ δ b nodes chals rows j = trJ δ b nodes chals' rows j := by
  unfold trJ polyJ
  refine congrArg (Lagrange.interpolate Finset.univ nodes) (funext fun i => ?_)
  have h1 : ¬ (29 ≤ (j : ℕ)) := by omega
  simp only [colJ, hj, if_true]

/-- The J chip's challenge vector reads only the round-0 coins `11, 12, 15, 16`. -/
theorem chalsJJ8_agree (χ χ' : SVFrame.Coins FrameJ8.frameJ8 K)
    (h0 : ∀ i : Fin FrameJ8.frameJ8.n, FrameJ8.frameJ8.sampledAfter i = 0 → χ i = χ' i) :
    chalsJJ8 χ = chalsJJ8 χ' := by
  funext j
  unfold chalsJJ8
  split_ifs
  all_goals first | rfl | (exact h0 _ (by rfl))
  
end Trace

open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (crJ) in
/-- **The J trace is staged** (`StagedCols frameJ8 crJ`): if a family of traces is `trJ` at the J coins
`chalsJJ8 χ` of a fixed row list, columns `< 29` read no coin and columns `≥ 29` read only round-0 coins. -/
theorem stJ {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
    {n : ℕ} (nodes : Fin n → ZMod p) (rows : Fin n → CRow (ZMod p))
    (Q : SVFrame.Coins FrameJ8.frameJ8 K → Fin 71 → (ZMod p)[X])
    (hQ : ∀ χ, Q χ = trJ δ b nodes (chalsJJ8 χ) rows) :
    SVFrame.StagedCols FrameJ8.frameJ8 crJ Q := by
  intro j χ χ' h
  rw [hQ, hQ]
  by_cases hj : (j : ℕ) < 29
  · exact trJ_coinfree δ b nodes _ _ rows j hj
  · have hc : crJ j = 1 := by simp [crJ, hj]
    rw [chalsJJ8_agree χ χ' (fun i hi => h i (by omega))]

/-! ## 7. The base gates on the honest rows -/

section Gates
open Nock.Jet.ChipJ8 Nock.Jet.Interp Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]

/-- What the four base gates say on a row (`ChipJ8.gate_facts`, as a predicate). -/
def RowFacts (r : CRow (ZMod p)) : Prop :=
  (r.pre.kd = .cst → r.w.val = r.pre.n1) ∧ (r.pre.kd = .add → r.w.val = r.w.v1 + r.w.v2) ∧
    (r.pre.kd = .mul → r.w.val = r.w.v1 * r.w.v2) ∧
    (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr → r.w.kN = 1)

/-- **The converse of `gate_facts`**: the four facts give the base gates. -/
theorem gates_of_facts (r : CRow (ZMod p)) (h : RowFacts r) :
    ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf r) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [baseGatesJ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [CoeffExpr.eval, envOf, colOf_sel, colOf_val, colOf_v1, colOf_v2, colOf_n1, colOf_kN]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hk : r.pre.kd = .cst
    · simp [hk, h1 hk]
    · simp [hk]
  · by_cases hk : r.pre.kd = .add
    · simp [hk, h2 hk]
    · simp [hk]
  · by_cases hk : r.pre.kd = .mul
    · simp [hk, h3 hk]
    · simp [hk]
  · by_cases hk : r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr
    · rcases hk with hk | hk | hk <;> simp [hk, h4 (by simp [hk])]
    · simp only [not_or] at hk
      simp [hk.1, hk.2.1, hk.2.2]

/-- The `mv` column is in no base gate. -/
theorem rowFacts_mv (r : CRow (ZMod p)) (m : ZMod p) :
    RowFacts ({ r with w := { r.w with mv := m } } : CRow (ZMod p)) ↔ RowFacts r := Iff.rfl

theorem rowFacts_of_kd (r : CRow (ZMod p))
    (h1 : r.pre.kd ≠ .cst) (h2 : r.pre.kd ≠ .add) (h3 : r.pre.kd ≠ .mul) (h4 : r.pre.kd ≠ .rp)
    (h5 : r.pre.kd ≠ .sl) (h6 : r.pre.kd ≠ .sr) : RowFacts r :=
  ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h3,
    fun h => by rcases h with h | h | h <;> contradiction⟩

/-- A read chain along a path that exists in `x` has `kN = 1` on every `sl`/`sr` row. -/
theorem chainW_facts (hd : Noun → ZMod p × ZMod p) (hcc : ∀ l r, (hd (Noun.cell l r)).1 = 1) (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun),
    followPath bs x ≠ none → ∀ r ∈ chainWG (p := p) hd c dst src ctr bs x, RowFacts r
  | [], src, ctr, x, _, r, hr => by
    simp only [chainWG, List.mem_singleton] at hr
    subst hr
    exact rowFacts_of_kd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | b :: bs, src, ctr, x, hx, r, hr => by
    cases x with
    | atom v => simp [followPath] at hx
    | cell l rr =>
      simp only [chainWG, List.mem_cons] at hr
      rcases hr with rfl | hr
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
        · cases b <;> simp at h
        · cases b <;> simp at h
        · cases b <;> simp at h
        · cases b <;> simp [mkW, hcc]
      · refine chainW_facts hd hcc c dst bs ctr (ctr + 1) _ ?_ r hr
        cases b <;> simpa [followPath, nhd, ntl] using hx

end Gates

section NodeFacts
open Nock.Jet.ChipJ8 Nock.Jet.Interp Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]

/-- **The base gates on the rows of one node**, from the node's J-3a row: its local constraint, its genuine
read, and the lookups `lk`. -/
theorem nodeW_facts (hd : Noun → ZMod p × ZMod p) (hcc : ∀ l r, (hd (Noun.cell l r)).1 = 1) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) (row : JRow)
    (hn : row.node = nd) (hv : lk nd.id = row.val)
    (hx : 0 < nd.op.arity → lk nd.a = row.x) (hy : 1 < nd.op.arity → lk nd.b = row.y)
    (hloc : LocalOK p row) (hrd : readOK s nd.op row.val row.x row.y = true) :
    ∀ r ∈ nodeWG (p := p) hd c S ctr lk s nd, RowFacts r := by
  subst hn
  unfold LocalOK at hloc
  unfold nodeWG
  cases hop : row.node.op with
  | var i ax =>
    simp only [hop] at hrd ⊢
    simp only [readOK, decide_eq_true_eq] at hrd
    refine chainW_facts hd hcc c _ _ _ _ _ ?_
    have h0 : 0 < ax := by
      rcases Nat.eq_zero_or_pos ax with h | h
      · subst h; simp [Noun.slot] at hrd
      · exact h
    rw [← slot_axPath _ h0, hrd]; simp
  | const k =>
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨fun _ => rfl, ?_, ?_, ?_⟩ <;> intro h <;> simp at h
  | add =>
    intro r hr
    simp only [hop, List.mem_singleton] at hr
    subst hr
    simp only [hop, localOK, decide_eq_true_eq] at hloc
    have hx' := hx (by simp [hop, JOp.arity])
    have hy' := hy (by simp [hop, JOp.arity])
    refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp at h, fun h => by simp at h⟩
    simp only [mkW]
    rw [hv, hx', hy', hloc]
    simp [Nock.Jet.Autogen.atomVal, ZMod.natCast_mod]
  | mul =>
    intro r hr
    simp only [hop, List.mem_singleton] at hr
    subst hr
    simp only [hop, localOK, decide_eq_true_eq] at hloc
    have hx' := hx (by simp [hop, JOp.arity])
    have hy' := hy (by simp [hop, JOp.arity])
    refine ⟨fun h => by simp at h, fun h => by simp at h, fun _ => ?_, fun h => by simp at h⟩
    simp only [mkW]
    rw [hv, hx', hy', hloc]
    simp [Nock.Jet.Autogen.atomVal, ZMod.natCast_mod]
  | pair =>
    intro r hr
    simp only [hop, List.mem_singleton] at hr
    subst hr
    simp only [hop, readOK, decide_eq_true_eq] at hrd
    refine ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun _ => ?_⟩
    simp only [mkW]
    rw [hv, hrd]; exact hcc _ _
  | nth j =>
    simp only [hop]
    simp only [hop, readOK, decide_eq_true_eq] at hrd
    refine chainW_facts hd hcc c _ _ _ _ _ ?_
    have hx' := hx (by simp [hop, JOp.arity])
    rw [← hx', nthO_path] at hrd
    rw [hrd]; exact fun h => nomatch h
  | tlN n =>
    simp only [hop]
    simp only [hop, readOK, decide_eq_true_eq] at hrd
    refine chainW_facts hd hcc c _ _ _ _ _ ?_
    have hx' := hx (by simp [hop, JOp.arity])
    rw [← hx', tailO_path] at hrd
    rw [hrd]; exact fun h => nomatch h
  | isF =>
    intro r hr
    simp only [hop, List.mem_singleton] at hr
    subst hr
    exact rowFacts_of_kd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | isNil =>
    intro r hr
    simp only [hop, List.mem_singleton] at hr
    subst hr
    exact rowFacts_of_kd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

end NodeFacts

section BlockFacts
open Nock.Jet.ChipJ8 Nock.Jet.Interp Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]

/-- **The honest data of every node of a call** (J-3a): its row, the lookups, the local constraint and the
genuine read.  (`interp_complete`'s proof, exposed with the lookup `honestLook`.) -/
theorem honestRows_data (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (c : ℕ)
    (h : T.sem p s = some r) :
    ∀ nd ∈ nodesOf T, ∃ row ∈ honestRows p T s c, row.node = nd ∧
      honestLook (p := p) T s c nd.id = row.val ∧
      (0 < nd.op.arity → honestLook (p := p) T s c nd.a = row.x) ∧
      (1 < nd.op.arity → honestLook (p := p) T s c nd.b = row.y) ∧
      LocalOK p row ∧ readOK s nd.op row.val row.x row.y = true := by
  obtain ⟨a, hs, ha, hr⟩ := sem_eq_some_iff.1 h
  have hA := argsD_eq hs
  have hgood : ∀ row ∈ honestRows p T s c, RowGood p s c row := by
    intro row hrow
    simp only [honestRows, List.mem_append, hA] at hrow
    rcases hrow with hrow | hrow
    · exact exRows_good hp hs ha c hT 0 row hrow
    · exact inRows_good T hs ha c _ _ row hrow
  set R := honestRows p T s c with hRdef
  have hlink : LinkIn R R := by
    intro row hrow
    have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact exRows_link (p := p) T.ax _ c R T.body 0
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inl hx) row hrow'
    · exact inRows_link T _ c R _ _
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inr hx) row hrow'
  have hids := honestRows_ids p T s c
  rw [← hRdef] at hids
  intro nd hnd
  have hnodes := honestRows_nodes p T s c
  rw [← hRdef] at hnodes
  rw [← hnodes] at hnd
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hnd
  refine ⟨row, hrow, rfl, ?_, fun h0 => ?_, fun h1 => ?_, (hgood row hrow).2.1, (hgood row hrow).2.2⟩
  · show (((R[row.node.id]?).map JRow.val).getD z0) = row.val
    rw [getElem?_of_ids hids hrow]; rfl
  · obtain ⟨e, he, hid, hv⟩ := (hlink row hrow).1 h0
    show (((R[row.node.a]?).map JRow.val).getD z0) = row.x
    rw [← hid, getElem?_of_ids hids he]; simp [hv]
  · obtain ⟨e, he, hid, hv⟩ := (hlink row hrow).2 h1
    show (((R[row.node.b]?).map JRow.val).getD z0) = row.y
    rw [← hid, getElem?_of_ids hids he]; simp [hv]

theorem nodesW_facts (hp : 0 < p) (hd : Noun → ZMod p × ZMod p) (hcc : ∀ l r, (hd (Noun.cell l r)).1 = 1) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (c N : ℕ)
    (h : T.sem p s = some r) :
    ∀ (nds : List JNode), (∀ nd ∈ nds, nd ∈ nodesOf T) → ∀ ctr, ∀ x ∈ nodesWG (p := p) hd c N (honestLook (p := p) T s c) s ctr nds,
      RowFacts x
  | [], _, ctr, x, hx => by simp [nodesWG] at hx
  | nd :: nds, hsub, ctr, x, hx => by
    simp only [nodesWG, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨row, -, hn, hv, hxx, hyy, hloc, hrd⟩ :=
        honestRows_data hp T hT s r c h nd (hsub nd (List.mem_cons_self ..))
      exact nodeW_facts hd hcc c N ctr _ s nd row hn hv hxx hyy hloc hrd x hx
    · exact nodesW_facts hp hd hcc T hT s r c N h nds (fun nd' h' => hsub nd' (List.mem_cons_of_mem _ h')) _ x hx

theorem blockW_facts (hp : 0 < p) (hd : Noun → ZMod p × ZMod p) (hcc : ∀ l r, (hd (Noun.cell l r)).1 = 1) (R : ℕ → Tpl) (c i : ℕ) (s : Noun)
    (hT : (R i).WellTyped p) (hs : ∃ r, (R i).sem p s = some r) :
    ∀ x ∈ blockWG (p := p) hd R c i s, RowFacts x := by
  obtain ⟨r, hr⟩ := hs
  intro x hx
  simp only [blockWG, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact rowFacts_of_kd _ (by simp [callPre]) (by simp [callPre]) (by simp [callPre]) (by simp [callPre])
      (by simp [callPre]) (by simp [callPre])
  · exact nodesW_facts hp hd hcc (R i) hT s r c _ hr (nodesOf (R i)) (fun _ h => h) _ x hx

/-- **The base gates hold on every honest J row** of an arbitrary run: every called template is well typed
and has a result on its call subject. -/
theorem honestJ8_facts (hp : 0 < p) (hd : Noun → ZMod p × ZMod p) (hcc : ∀ l r, (hd (Noun.cell l r)).1 = 1) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (hcalls : ∀ cl ∈ calls, (R cl.1).WellTyped p ∧ ∃ r, (R cl.1).sem p cl.2 = some r) :
    ∀ x ∈ honestJ8G (p := p) hd R regs calls, RowFacts x := by
  intro x hx
  unfold honestJ8G at hx
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨⟨⟨i, s⟩, c⟩, hmem, hx⟩
  · exact rowFacts_of_kd _ (by simp [regPre]) (by simp [regPre]) (by simp [regPre]) (by simp [regPre])
      (by simp [regPre]) (by simp [regPre])
  · have hc : (i, s) ∈ calls := by
      exact List.fst_mem_of_mem_zipIdx hmem
    exact blockW_facts hp hd hcc R c i s (hcalls _ hc).1 (hcalls _ hc).2 x hx

end BlockFacts

/-! ## 8. Against L0's `J8Data`: the J rows with the counted `mv` fix -/

section Data
open Nock.Jet.ChipJ8 Nock.Jet.Autogen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (mvFixP pinsOfP J8Data hJd hJd_cell)
variable {p : ℕ} [Fact p.Prime]

theorem mvFixP_pre (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    (mvFixP p rows pins).map CRow.pre = rows.map CRow.pre := by
  unfold mvFixP
  rw [List.map_map]
  congr 1
  funext r
  simp only [Function.comp]
  split <;> rfl

theorem mvFixP_facts (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p)))
    (h : ∀ r ∈ rows, RowFacts r) : ∀ r ∈ mvFixP p rows pins, RowFacts r := by
  intro x hx
  unfold mvFixP at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  have := h r hr
  split <;> exact this

/-- **`hgate` for the J rows of a run** (`J8Data.jrows`, the honest rows with the counted `mv` fix): every called
template is well typed and has a result on its call subject. -/
theorem jrows_gate {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} (D : J8Data p Rg fuel s f r)
    (hp : 0 < p)
    (hj : D.jrows = mvFixP p (honestJ8G (hJd p D.cells D.acs) D.Rt D.regs D.calls) (pinsOfP p D.regs D.idx))
    (hcalls : ∀ cl ∈ D.calls, (D.Rt cl.1).WellTyped p ∧ ∃ r, (D.Rt cl.1).sem p cl.2 = some r) :
    ∀ x ∈ D.jrows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf x) = 0 := by
  intro x hx
  rw [hj] at hx
  exact gates_of_facts x (mvFixP_facts _ _ (honestJ8_facts hp (hJd p D.cells D.acs) (hJd_cell p D.cells D.acs) D.Rt D.regs D.calls hcalls) x hx)

/-- **The layout of `J8Data.jrows`** is `layoutJ8 Rt regs ids`. -/
theorem jrows_pre {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} (D : J8Data p Rg fuel s f r)
    (hj : D.jrows = mvFixP p (honestJ8G (hJd p D.cells D.acs) D.Rt D.regs D.calls) (pinsOfP p D.regs D.idx))
    (hids : D.ids = D.calls.map Prod.fst) :
    D.jrows.map CRow.pre = layoutJ8 D.Rt D.regs D.ids := by
  rw [hj, mvFixP_pre, honestJ8_pre, hids]

end Data

/-- **`¬ JPole` from the key-list non-vanishing** (the shape of L5's `jNoPole` conclusion with `KT := jKeysT rows`,
`KX := jKeysX rows`). -/
theorem notJPole_of_keys {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    {n : ℕ} (rows : Fin n → Nock.Jet.ChipJ8.CRow (ZMod p)) (chals : ℕ → K)
    (hT : ∀ κ ∈ jKeysT rows, compress (coinsJ δ chals)
      (liftRec (L := Quad (algebraMap (ZMod p) K δ)) (keyK (K := K) 8 κ)) ≠ 0)
    (hX : ∀ κ ∈ jKeysX rows, compress (coinsJX δ chals)
      (liftRec (L := Quad (algebraMap (ZMod p) K δ)) (keyK (K := K) 5 κ)) ≠ 0) :
    ¬ JPole δ rows chals := by
  rintro (⟨κ, hκ, h⟩ | ⟨κ, hκ, h⟩)
  · exact hT κ hκ h
  · exact hX κ hκ h

/-! ## 9. `hcalls` from `HregC` and the tree -/

section Calls
open Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Autogen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.V1J8.Gen (callsOf)

/-- **An `s11j` node is a jet hit**: a generated node whose state is `s11j` has the formula
`[11 [b clue] body]` and `jetHit R b v body s = some _` at the clue's value `v`. -/
theorem genX_s11j {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hst : t.label.state = .s11j) :
    ∃ b clue body v r', f = .cell (.atom 11) (.cell (.cell b clue) body) ∧
      jetHit R b v body s = some r' := by
  rcases n with _ | n
  · simp [genComputeSkeletonX] at h
  unfold genComputeSkeletonX at h
  split at h
  all_goals (repeat' (split at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [mkX] at hst; done)
    | (exfalso; simp at h; done)
    | skip
  all_goals exact ⟨_, _, _, _, _, rfl, by assumption⟩

theorem rowOfSkelX_st (sk : SkelX) : (rowOfSkelX sk).st = sk.state := by
  unfold rowOfSkelX
  cases sk.state <;> rfl

theorem rowOfSkelX_s (sk : SkelX) : (rowOfSkelX sk).s = sk.subject := by
  unfold rowOfSkelX
  cases sk.state <;> rfl

/-- **A jet row of a generated tree is a registered hit**: its clue value `sf1` is an atom id, the registry has
an entry there, and the entry's template has a result on the row's subject. -/
theorem s11j_node {R : Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u)
    (hst : u.label.state = .s11j) :
    ∃ id j r', R id = some j ∧ (rowOfSkelX u.label).sf1 = .atom id ∧ j.T.semS u.label.subject = some r' := by
  have hs := inTree_rowSem hgen hu
  have hst' : (rowOfSkelX u.label).st = .s11j := by rw [rowOfSkelX_st]; exact hst
  unfold RowNX.SemN at hs
  rw [hst'] at hs
  obtain ⟨-, -, -, -, id, j, -, hsf1, hRj, -, hrel⟩ := hs
  rw [rowOfSkelX_s] at hrel
  exact ⟨id, j, _, hRj, hsf1, hrel⟩

/-- **`hcalls` from `HregC` and the tree**: every call of the run has a well-typed template with a result on
the call's subject. -/
theorem calls_of_hregC {p : ℕ} {Rg : VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (Rt : ℕ → Tpl)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ cl ∈ callsOf (rowsOfT t), (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r := by
  intro cl hcl
  unfold callsOf at hcl
  obtain ⟨row, hrow, hrc⟩ := List.mem_filterMap.1 hcl
  have hrow' : ∃ u ∈ bfsForest [t], rowOfSkelX u.label = row := by
    simpa [rowsOfT] using hrow
  obtain ⟨u, hu, rfl⟩ := hrow'
  obtain ⟨c, hc, huc⟩ := (mem_bfsForest [t] u).1 hu
  have hct : c = t := by simpa using hc
  subst hct
  have hst : u.label.state = .s11j := by
    rw [← rowOfSkelX_st]
    by_contra hne
    simp [hne] at hrc
  obtain ⟨id, j, r', hRj, hftth, hsem⟩ := s11j_node hgen huc hst
  have hcalled : id ∈ CalledIds _ := ⟨u, huc, by rw [rowOfSkelX_st]; exact hst, hftth⟩
  obtain ⟨hR2, -, hwt⟩ := hRt id hcalled
  rw [hRj] at hR2
  have hj : j = ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ := Option.some.inj hR2
  have hcl' : cl = (id, u.label.subject) := by
    rw [if_pos (by rw [rowOfSkelX_st]; exact hst)] at hrc
    rw [← Option.some.inj hrc, hftth, rowOfSkelX_s]
    rfl
  subst hcl'
  refine ⟨hwt, r', ?_⟩
  subst hj
  exact hsem

end Calls

/-! ## 10. The instance: `j8DataOf` -/

section Instance
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (mvFixP pinsOfP J8Data j8DataOf rowsOfT hJd)
open Nock.Jet.ChipJ8 Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]

theorem j8DataOf_jrows {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).jrows = mvFixP p (honestJ8G (hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) Rt
      (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls)
      (pinsOfP p (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).idx) := rfl

theorem j8DataOf_ids {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).ids = (j8DataOf p Rg Rt hgen).calls.map Prod.fst := rfl

theorem j8DataOf_calls {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).calls = Nock.V1J8.Gen.callsOf (rowsOfT t) := rfl

/-- **The base gates on the J rows of a run** (`j8DataOf`): from `HregC`'s witness table alone. -/
theorem jrows_gate_run {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (hp : 0 < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ (j8DataOf p Rg Rt hgen).jrows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))),
      g.eval (envOf x) = 0 :=
  jrows_gate _ hp (j8DataOf_jrows Rt hgen) (by rw [j8DataOf_calls]; exact calls_of_hregC hgen Rt hRt)

/-- The layout of the run's J rows. -/
theorem jrows_pre_run {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).jrows.map CRow.pre =
      layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids :=
  jrows_pre _ (j8DataOf_jrows Rt hgen) (j8DataOf_ids Rt hgen)

end Instance

/-! ## 11. The J publics as table totals (`hp01`, `hp23`) -/

section Totals
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal (Tab tot tabOfRows tot_tabOfRows_fin)
open Nock.Jet.ChipJ8T.HonestRAP (termJ_eq)
open Nock.Jet.RapJetJ8 (dJX dJ)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J chip's provides**: the in-chip provides with multiplicity `mv`, the service provide with `m`. -/
def provJ (r : Nock.Jet.ChipJ8.CRow (ZMod p)) : List (List (ZMod p) × 𝕂′) :=
  (provKT r).map (fun k => (k, liftQ δ r.w.mv)) ++
    (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.ents3 r).map (fun k => (k, liftQ δ r.w.m))

/-- **A J row's term is its table total**: consumes minus multiplicity-weighted provides. -/
theorem termJ_row_eq_tot (r : Nock.Jet.ChipJ8.CRow (ZMod p)) :
    termJ δ chals r = ((consKT r).map (dJ δ chals)).sum -
      ((provJ δ r).map fun q => q.2 * dJ δ chals q.1).sum := by
  rw [termJ_eq]
  simp only [provJ, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  rw [List.sum_map_mul_left, List.sum_map_mul_left]
  ring

/-- **`hp01` as a table total**: if the J terminal public is the total of the J table (all rows' consumes and
provides), it is `Σ termJ`. -/
theorem hp01_of_tot {n : ℕ} (rows : Fin n → Nock.Jet.ChipJ8.CRow (ZMod p)) (pubs : ℕ → K)
    (h : Quad.mk _ (pubs 0) (pubs 1) =
      tot (dJ δ chals) (tabOfRows (List.ofFn rows) consKT (provJ δ))) :
    Quad.mk _ (pubs 0) (pubs 1) = ∑ i, termJ δ chals (rows i) := by
  rw [h, ← tot_tabOfRows_fin]
  exact Finset.sum_congr rfl fun i _ => (termJ_row_eq_tot δ chals (rows i)).symm

/-- **`hp23` as a table total**: the export sum is the total of the consumer-only export table. -/
theorem hp23_of_tot {n : ℕ} (rows : Fin n → Nock.Jet.ChipJ8.CRow (ZMod p)) (pubs : ℕ → K)
    (h : Quad.mk _ (pubs 2) (pubs 3) =
      tot (dJX δ chals) (tabOfRows (List.ofFn rows) (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX)
        (fun _ => ([] : List (List (ZMod p) × 𝕂′))))) :
    Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i) := by
  rw [h]
  have := tot_tabOfRows_fin (R := 𝕂′) (dJX δ chals) rows (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX)
    (fun _ => ([] : List (List (ZMod p) × 𝕂′)))
  simp only [List.map_nil, List.sum_nil, sub_zero] at this
  rw [← this]
  rfl

end Totals

/-! ## 12. `BlockOK` from the template: the key uniqueness holds for EVERY template -/

section BlockNodup
open Nock.Jet.ChipJ8 Nock.Jet.Interp Nock.Jet.Autogen

theorem chainPre_nid (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ),
    (chainPre c dst src ctr bs).map PRow.nid = List.range' ctr bs.length ++ [dst]
  | [], src, ctr => by simp [chainPre]
  | b :: bs, src, ctr => by
    simp only [chainPre, List.map_cons, chainPre_nid c dst bs, List.length_cons, List.range'_succ,
      List.cons_append]

theorem nodePre_nid (c S ctr : ℕ) (nd : JNode) :
    (nodePre c S ctr nd).map PRow.nid = List.range' ctr (nodeVirt nd) ++ [nd.id] := by
  unfold nodePre nodeVirt
  cases h : nd.op <;> simp [chainPre_nid, h]

theorem chainPre_kd (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ), ∀ q ∈ chainPre c dst src ctr bs,
    q.kd ≠ .reg ∧ q.kd ≠ .call
  | [], src, ctr, q, hq => by simp [chainPre] at hq; subst hq; simp
  | b :: bs, src, ctr, q, hq => by
    simp only [chainPre, List.mem_cons] at hq
    rcases hq with rfl | hq
    · cases b <;> simp
    · exact chainPre_kd c dst bs ctr (ctr + 1) q hq

theorem nodePre_kd (c S ctr : ℕ) (nd : JNode) : ∀ q ∈ nodePre c S ctr nd, q.kd ≠ .reg ∧ q.kd ≠ .call := by
  intro q hq
  unfold nodePre at hq
  cases h : nd.op <;> simp only [h] at hq <;>
    first | exact chainPre_kd _ _ _ _ _ q hq | (simp at hq; subst hq; simp)

theorem nodesPre_nid_nodup (c S : ℕ) : ∀ (nds : List JNode) (ctr : ℕ),
    (∀ nd ∈ nds, nd.id < ctr) → (nds.map JNode.id).Nodup →
    ((nodesPre c S ctr nds).map PRow.nid).Nodup ∧
      ∀ x ∈ (nodesPre c S ctr nds).map PRow.nid,
        x ∈ nds.map JNode.id ∨ (ctr ≤ x ∧ x < ctr + (nds.map nodeVirt).sum)
  | [], ctr, _, _ => by simp [nodesPre]
  | nd :: nds, ctr, hlt, hnd => by
    have hnd' : (nds.map JNode.id).Nodup := (List.nodup_cons.1 (by simpa using hnd)).2
    have hnotin : nd.id ∉ nds.map JNode.id := (List.nodup_cons.1 (by simpa using hnd)).1
    obtain ⟨hN, hB⟩ := nodesPre_nid_nodup c S nds (ctr + nodeVirt nd)
      (fun n hn => by have := hlt n (List.mem_cons_of_mem _ hn); omega) hnd'
    have hid : nd.id < ctr := hlt nd (List.mem_cons_self ..)
    simp only [nodesPre, List.map_append, nodePre_nid]
    refine ⟨?_, ?_⟩
    · refine List.nodup_append.2 ⟨?_, hN, ?_⟩
      · refine List.nodup_append.2 ⟨List.nodup_range', List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_range'_1, List.mem_singleton] at ha hb
        omega
      · intro a ha b hb hab
        simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha
        subst hab
        rcases hB a hb with hb' | hb'
        · obtain ⟨n, hn, hna⟩ := List.mem_map.1 hb'
          have := hlt n (List.mem_cons_of_mem _ hn)
          rcases ha with ha | ha
          · omega
          · exact hnotin (ha ▸ hb')
        · rcases ha with ha | ha <;> omega
    · intro x hx
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at hx
      simp only [List.map_cons, List.sum_cons, List.mem_cons]
      rcases hx with (⟨h1, h2⟩ | rfl) | hx
      · right; omega
      · left; left; rfl
      · rcases hB x hx with h | h
        · left; right; exact h
        · right; omega

theorem nodesPre_kd (c S : ℕ) : ∀ (nds : List JNode) (ctr : ℕ), ∀ q ∈ nodesPre c S ctr nds,
    q.kd ≠ .reg ∧ q.kd ≠ .call
  | [], ctr, q, hq => by simp [nodesPre] at hq
  | nd :: nds, ctr, q, hq => by
    simp only [nodesPre, List.mem_append] at hq
    rcases hq with hq | hq
    · exact nodePre_kd c S ctr nd q hq
    · exact nodesPre_kd c S nds _ q hq

theorem filterMap_tvKey_nonreg : ∀ (l : List PRow), (∀ q ∈ l, q.kd ≠ .reg) →
    l.filterMap tvKey = l.map fun q => (q.cid, q.pn)
  | [], _ => rfl
  | q :: l, h => by
    have h1 : tvKey q = some (q.cid, q.pn) := by simp [tvKey, h q (List.mem_cons_self ..)]
    simp only [List.filterMap_cons, h1, List.map_cons]
    rw [filterMap_tvKey_nonreg l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

/-- **The key uniqueness of a call block holds for every template** (no hypothesis on `T`): node ids are
`0 .. N-1` (`nodesOf_ids`), the subject is `N`, the read cursors are `N+1 ..`. -/
theorem blockPre_keys_nodup (R : ℕ → Tpl) (i : ℕ) : ((blockPre R 0 i).filterMap tvKey).Nodup := by
  have hids := nodesOf_ids (R i)
  have hnd : ((nodesOf (R i)).map JNode.id).Nodup := by rw [hids]; exact List.nodup_range'
  have hlt : ∀ nd ∈ nodesOf (R i), nd.id < (nodesOf (R i)).length + 1 := by
    intro nd hnd'
    have : nd.id ∈ (nodesOf (R i)).map JNode.id := List.mem_map_of_mem hnd'
    rw [hids, List.mem_range'_1, ← nodesOf_length] at this
    omega
  obtain ⟨hN1, hB⟩ := nodesPre_nid_nodup 0 (nodesOf (R i)).length (nodesOf (R i))
    ((nodesOf (R i)).length + 1) hlt hnd
  have hkd := nodesPre_kd 0 (nodesOf (R i)).length (nodesOf (R i)) ((nodesOf (R i)).length + 1)
  have e : (blockPre R 0 i).filterMap tvKey =
      (0, (nodesOf (R i)).length) :: (nodesPre 0 (nodesOf (R i)).length ((nodesOf (R i)).length + 1)
        (nodesOf (R i))).map (fun q => (0, q.nid)) := by
    unfold blockPre
    rw [List.filterMap_cons_some (b := (0, (nodesOf (R i)).length)) (by simp [tvKey, callPre, PRow.pn])]
    congr 1
    rw [filterMap_tvKey_nonreg _ (fun q hq => (hkd q hq).1)]
    refine List.map_congr_left fun q hq => ?_
    have hc := (blockPre_cid R 0 i q (by simp [blockPre, hq]))
    simp [PRow.pn, (hkd q hq).2, hc]
  rw [e]
  have e2 : (nodesPre 0 (nodesOf (R i)).length ((nodesOf (R i)).length + 1) (nodesOf (R i))).map
      (fun q => ((0 : ℕ), q.nid)) = ((nodesPre 0 (nodesOf (R i)).length ((nodesOf (R i)).length + 1)
        (nodesOf (R i))).map PRow.nid).map (fun x => ((0 : ℕ), x)) := by
    simp [List.map_map, Function.comp_def]
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  swap
  · rw [e2]; exact hN1.map (fun a b h => (Prod.mk.inj h).2)
  intro hmem
  obtain ⟨q, hq, hq'⟩ := List.mem_map.1 hmem
  have hnid : q.nid = (nodesOf (R i)).length := (Prod.mk.inj hq').2
  rcases hB q.nid (List.mem_map_of_mem hq) with h | h
  · rw [hids, List.mem_range'_1, ← nodesOf_length] at h
    omega
  · omega

end BlockNodup

/-! ## 13. Smallness of a call block from the template and its size -/

section BlockSmall
open Nock.Jet.ChipJ8 Nock.Jet.Interp Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]

theorem exRows_const_lt (hp : 0 < p) {k : ℕ} {ax : Fin k → ℕ} {inTy : Fin k → Ty} {a : Fin k → Noun} (c : ℕ)
    {e : Ex k} {τ : Ty} (h : HasTy p inTy e τ) :
    ∀ b, ∀ r ∈ exRows p ax a c b e, ∀ n, r.node.op = .const n → n < p := by
  induction h with
  | var i => intro b r hr n hn; simp [exRows] at hr; subst hr; simp at hn
  | const hc =>
    intro b r hr n hn; simp [exRows] at hr; subst hr; simp at hn; subst hn; assumption
  | nil _ =>
    intro b r hr n hn; simp [exRows] at hr; subst hr; simp at hn; subst hn; exact hp
  | weakN _ ih => exact ih
  | add _ _ ih₁ ih₂ =>
    intro b r hr n hn
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · simp at hn
    · exact ih₁ _ r hr n hn
    · exact ih₂ _ r hr n hn
  | mul _ _ ih₁ ih₂ =>
    intro b r hr n hn
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · simp at hn
    · exact ih₁ _ r hr n hn
    · exact ih₂ _ r hr n hn
  | nth _ _ ih =>
    intro b r hr n hn
    simp only [exRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp at hn
    · exact ih _ r hr n hn
  | pair _ _ ih₁ ih₂ =>
    intro b r hr n hn
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · simp at hn
    · exact ih₁ _ r hr n hn
    · exact ih₂ _ r hr n hn

theorem gRows_noconst (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun), ∀ row ∈ gRows c τ b r v,
    ∀ n, row.node.op ≠ .const n := by
  intro τ
  induction τ with
  | F => intro b r v row hrow n; simp [gRows] at hrow; subst hrow; simp
  | N => intro b r v row hrow n; simp [gRows] at hrow
  | L m τ ih =>
    intro b r v row hrow n
    have hel : ∀ (js : List ℕ) (b : ℕ), ∀ row ∈ gElemsR (gRows c τ) (gSz τ) r v c b js, ∀ n, row.node.op ≠ .const n := by
      intro js
      induction js with
      | nil => intro b row hrow; simp [gElemsR] at hrow
      | cons j js ihj =>
        intro b row hrow n
        simp only [gElemsR, List.mem_cons, List.mem_append] at hrow
        rcases hrow with rfl | hrow | hrow
        · simp
        · exact ih _ _ _ row hrow n
        · exact ihj _ row hrow n
    simp only [gRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · simp
    · simp
    · exact hel _ _ row hrow n

theorem inRows_noconst (T : Tpl) (a : Fin T.k → Noun) (c : ℕ) :
    ∀ (is : List (Fin T.k)) (b : ℕ), ∀ row ∈ inRows T a c b is, ∀ n, row.node.op ≠ .const n := by
  intro is
  induction is with
  | nil => intro b row hrow; simp [inRows] at hrow
  | cons i is ih =>
    intro b row hrow n
    simp only [inRows, List.mem_cons, List.mem_append] at hrow
    rcases hrow with rfl | hrow | hrow
    · simp
    · exact gRows_noconst c _ _ _ _ row hrow n
    · exact ih _ row hrow n

theorem honestRows_small (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (c : ℕ)
    (h : T.sem p s = some r) :
    ∀ row ∈ honestRows p T s c, row.node.id < (nodesOf T).length ∧
      (0 < row.node.op.arity → row.node.a < (nodesOf T).length) ∧
      (1 < row.node.op.arity → row.node.b < (nodesOf T).length) ∧
      (∀ n, row.node.op = .const n → n < p) := by
  obtain ⟨a, hs, ha, hr⟩ := sem_eq_some_iff.1 h
  have hA := argsD_eq hs
  set R := honestRows p T s c with hRdef
  have hlink : LinkIn R R := by
    intro row hrow
    have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact exRows_link (p := p) T.ax _ c R T.body 0
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inl hx) row hrow'
    · exact inRows_link T _ c R _ _
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inr hx) row hrow'
  have hids := honestRows_ids p T s c
  rw [← hRdef] at hids
  have hlen : (nodesOf T).length = exSz T.body + inSz T (List.finRange T.k) := nodesOf_length T
  have hidlt : ∀ row ∈ R, row.node.id < (nodesOf T).length := by
    intro row hrow
    have : row.node.id ∈ R.map (fun r => r.node.id) := List.mem_map_of_mem hrow
    rw [hids, List.mem_range'_1] at this
    omega
  intro row hrow
  refine ⟨hidlt row hrow, fun h0 => ?_, fun h1 => ?_, fun n hn => ?_⟩
  · obtain ⟨e, he, hid, -⟩ := (hlink row hrow).1 h0
    rw [← hid]; exact hidlt e he
  · obtain ⟨e, he, hid, -⟩ := (hlink row hrow).2 h1
    rw [← hid]; exact hidlt e he
  · simp only [hRdef, honestRows, List.mem_append] at hrow
    rcases hrow with hrow | hrow
    · rw [hA] at *
      exact exRows_const_lt hp c hT 0 row hrow n hn
    · exact absurd hn (inRows_noconst T _ c _ _ row hrow n)

theorem chainPre_lt (c dst B : ℕ) (hB : 0 < B) (hd : dst < B) : ∀ (bs : List Bool) (src ctr : ℕ),
    src < B → ctr + bs.length ≤ B → ∀ q ∈ chainPre c dst src ctr bs,
      q.id < B ∧ q.nid < B ∧ q.n1 < B ∧ q.n2 < B
  | [], src, ctr, hs, _, q, hq => by
    simp [chainPre] at hq; subst hq; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  | b :: bs, src, ctr, hs, hc, q, hq => by
    simp only [chainPre, List.mem_cons] at hq
    simp only [List.length_cons] at hc
    rcases hq with rfl | hq
    · cases b <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · exact chainPre_lt c dst B hB hd bs ctr (ctr + 1) (by omega) (by omega) q hq

theorem nodePre_lt (p c S ctr B : ℕ) (hB : 0 < B) (hS : S < B) (nd : JNode) (hid : nd.id < B)
    (ha : 0 < nd.op.arity → nd.a < B) (hb : 1 < nd.op.arity → nd.b < B)
    (hk : ∀ n, nd.op = .const n → n < p) (hBp : B ≤ p) (hc : ctr + nodeVirt nd ≤ B) :
    ∀ q ∈ nodePre c S ctr nd, q.id < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p := by
  intro q hq
  unfold nodePre at hq
  unfold nodeVirt at hc
  cases hop : nd.op with
  | var i ax =>
    simp only [hop] at hq hc
    have := chainPre_lt c nd.id B hB hid _ S ctr hS hc q hq
    omega
  | nth j =>
    simp only [hop] at hq hc
    have ha' := ha (by simp [hop, JOp.arity])
    have := chainPre_lt c nd.id B hB hid _ nd.a ctr ha' (by simpa using hc) q hq
    omega
  | tlN n =>
    simp only [hop] at hq hc
    have ha' := ha (by simp [hop, JOp.arity])
    have := chainPre_lt c nd.id B hB hid _ nd.a ctr ha' (by simpa using hc) q hq
    omega
  | const n =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have := hk n hop
    simp only; omega
  | add =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have ha' := ha (by simp [hop, JOp.arity]); have hb' := hb (by simp [hop, JOp.arity])
    simp only; omega
  | mul =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have ha' := ha (by simp [hop, JOp.arity]); have hb' := hb (by simp [hop, JOp.arity])
    simp only; omega
  | pair =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have ha' := ha (by simp [hop, JOp.arity]); have hb' := hb (by simp [hop, JOp.arity])
    simp only; omega
  | isF =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have ha' := ha (by simp [hop, JOp.arity])
    simp only; omega
  | isNil =>
    simp only [hop, List.mem_singleton] at hq; subst hq
    have ha' := ha (by simp [hop, JOp.arity])
    simp only; omega

theorem nodesPre_lt (p c S B : ℕ) (hB : 0 < B) (hS : S < B) (hBp : B ≤ p) :
    ∀ (nds : List JNode) (ctr : ℕ),
      (∀ nd ∈ nds, nd.id < B ∧ (0 < nd.op.arity → nd.a < B) ∧ (1 < nd.op.arity → nd.b < B) ∧
        (∀ n, nd.op = .const n → n < p)) →
      ctr + (nds.map nodeVirt).sum ≤ B →
      ∀ q ∈ nodesPre c S ctr nds, q.id < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  | [], ctr, _, _, q, hq => by simp [nodesPre] at hq
  | nd :: nds, ctr, hn, hc, q, hq => by
    simp only [List.map_cons, List.sum_cons] at hc
    simp only [nodesPre, List.mem_append] at hq
    obtain ⟨h1, h2, h3, h4⟩ := hn nd (List.mem_cons_self ..)
    rcases hq with hq | hq
    · exact nodePre_lt p c S ctr B hB hS nd h1 h2 h3 h4 hBp (by omega) q hq
    · exact nodesPre_lt p c S B hB hS hBp nds _ (fun n hn' => hn n (List.mem_cons_of_mem _ hn'))
        (by omega) q hq

/-- **`BlockOK` from the template** (answer to the scope question): a well-typed template that has a result on
some subject, called at `i < p`, whose size `N + 1 + Σ virt` is `< p`, passes `BlockOK`.  The key uniqueness
needs nothing (`blockPre_keys_nodup`); the size bound is the only extra property. -/
theorem blockOK_of_tpl (hp : 0 < p) (R : ℕ → Tpl) (i : ℕ) (hi : i < p) (hT : (R i).WellTyped p)
    (s r : Noun) (hsem : (R i).sem p s = some r)
    (hcap : (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum < p) :
    BlockOK p R i := by
  refine ⟨blockPre_keys_nodup R i, ?_⟩
  intro q hq
  simp only [blockPre, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simp only [callPre]; refine ⟨hi, hp, hp, by omega⟩
  · have hnodes : ∀ nd ∈ nodesOf (R i), nd.id < (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum ∧
        (0 < nd.op.arity → nd.a < (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum) ∧
        (1 < nd.op.arity → nd.b < (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum) ∧
        (∀ n, nd.op = .const n → n < p) := by
      intro nd hnd
      rw [← honestRows_nodes p (R i) s 0] at hnd
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hnd
      obtain ⟨a1, a2, a3, a4⟩ := honestRows_small hp (R i) hT s r 0 hsem row hrow
      exact ⟨by omega, fun h => by have := a2 h; omega, fun h => by have := a3 h; omega, a4⟩
    exact nodesPre_lt p 0 (nodesOf (R i)).length
      ((nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum) (by omega) (by omega) (by omega)
      (nodesOf (R i)) ((nodesOf (R i)).length + 1) hnodes (by omega) q hq

theorem length_nodesPre (c S : ℕ) : ∀ (nds : List JNode) (ctr : ℕ),
    (nodesPre c S ctr nds).length = (nds.map nodeVirt).sum + nds.length
  | [], ctr => by simp [nodesPre]
  | nd :: nds, ctr => by
    have h := congrArg List.length (nodePre_nid c S ctr nd)
    simp only [List.length_map, List.length_append, List.length_range', List.length_singleton] at h
    simp only [nodesPre, List.length_append, h, length_nodesPre c S nds, List.map_cons, List.sum_cons,
      List.length_cons]
    omega

/-- **The size bound is the block's row count**: `N + 1 + Σ virt = |blockPre|`. -/
theorem cap_eq_blockLen (R : ℕ → Tpl) (c i : ℕ) :
    (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum = (blockPre R c i).length := by
  simp only [blockPre, List.length_cons, length_nodesPre]
  omega

theorem blockLen_le_blocks (R : ℕ → Tpl) : ∀ (ids : List ℕ) (c0 i : ℕ), i ∈ ids →
    (blockPre R 0 i).length ≤ (blocks R c0 ids).length
  | [], c0, i, h => by simp at h
  | j :: is, c0, i, h => by
    simp only [blocks, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · have : (blockPre R c0 i).length = (blockPre R 0 i).length := by
        rw [blockPre_setC R c0 i, List.length_map]
      omega
    · have := blockLen_le_blocks R is (c0 + 1) i h
      omega

/-- **The size bound from the J table size**: `N + 1 + Σ virt ≤ nJ` for a called template. -/
theorem cap_le_layout (R : ℕ → Tpl) (regs ids : List ℕ) (i : ℕ) (hi : i ∈ ids) :
    (nodesOf (R i)).length + 1 + ((nodesOf (R i)).map nodeVirt).sum ≤ (layoutJ8 R regs ids).length := by
  rw [cap_eq_blockLen R 0 i]
  have := blockLen_le_blocks R ids 0 i hi
  simp only [layoutJ8, List.length_append]
  omega

/-- **All called templates pass `BlockOK`**, from `HregC`'s consequences (`calls_of_hregC`), the called ids
being `< p`, and the J table being smaller than `p` (`RowsLe31` with `2^63 < p`). -/
theorem blocksOK_of_calls (hp : 0 < p) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (hcalls : ∀ cl ∈ calls, (R cl.1).WellTyped p ∧ ∃ r, (R cl.1).sem p cl.2 = some r)
    (hid : ∀ cl ∈ calls, cl.1 < p) (hJ : (layoutJ8 R regs (calls.map Prod.fst)).length < p) :
    ∀ i ∈ calls.map Prod.fst, BlockOK p R i := by
  intro i hi
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hT, r, hr⟩ := hcalls cl hcl
  exact blockOK_of_tpl hp R cl.1 (hid cl hcl) hT cl.2 r hr
    (lt_of_le_of_lt (cap_le_layout R regs _ cl.1 hi) hJ)

/-- **Counterexample (the size bound is needed)**: at `p = 2` the template `0 + 0` is well typed with
`axPosB = true`, but its call block has `n2 = N = 3 ≥ p`, so `BlockOK` fails. -/
theorem blockOK_counterexample :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ∃ T : Tpl, T.WellTyped 2 ∧ axPosB T = true ∧ ¬ BlockOK 2 (fun _ => T) 0 := by
  refine ⟨⟨0, Fin.elim0, Fin.elim0, .F, .add (.const 0) (.const 0)⟩, ?_, by decide, ?_⟩
  · exact HasTy.add (HasTy.const (by decide)) (HasTy.const (by decide))
  · intro h
    have := h.2 (callPre (fun _ => (⟨0, Fin.elim0, Fin.elim0, .F, .add (.const 0) (.const 0)⟩ : Tpl)) 0 0)
      (by simp [blockPre])
    simp [callPre, nodesOf, exNodes, exSz, inNodes, List.finRange] at this

end BlockSmall

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet
