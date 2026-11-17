/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestPairX.lean

  **The honest op-5 α-pair limb data `pd` of
  `computeChipVCLHX` (123), from the atom table's comb rows, and `PairOK` on every generated pair row.**

  **The atom table's comb** (A-1 `Nock.Atoms.limbs`, A-2 `Denotes`, AW `walkRecA`): a big atom `a` with
  canonical limbs `[l₀, …, l_{k−1}]` (`k ≥ 2`) is the right comb `[l₀ [l₁ … [l_{k−2} l_{k−1}]]]`; its
  spine row at depth `d` (axis `ax_d`, `ax_0 = 1`, `ax_{d+1} = 2·ax_d + 1`) is the atom-table row
  `(aL, wR, valR) = (l_d, 1, sx (d+1))` (a suffix row, `sx` the table's row serial of atom `a`'s spine row
  at depth `d + 1`) or, at the deepest row, `(l_{k−2}, 0, l_{k−1})`.  The AW atom walk provides, per
  row, the two records `walkRecA = (rootIdx, 2·ax + b, k_b, v_b)`: `b = 0` → `(0, aL)`, `b = 1` →
  `(wR, valR)`.

  * `recsA sx d ax l` — the `(axis, k, v)` parts of the `walkRecA` records of the comb of `l` from spine
    depth `d` at axis `ax` (the honest AW provide list of one atom).
  * `combFD sxa sxb d ax xs ys` — the first difference of two combs: the axis and the two `(k, v)` there.
  * `pdX sx r` — **the honest limb data** of a row: `combFD` of the canonical limbs of the two
    first-difference leaves `f_tth, f_ttt` (atoms; junk otherwise, never read off a pair row).
  * `combFD_spec` — both returned records ARE AW records of the two combs at the SAME axis (so the two
    `walkRecA` consumes of `slot3X`'s α pair are provided by the honest atom walk), the kinds are bits,
    not both suffix rows, and two inline limbs differ and are `< B`.
  * **`pairOK_pdX`** — `RowOKX`, `HdlOK` and `B ≤ ringChar F` ⇒ `PairOK (pdX sx r)` on an `isPair` row;
    **`pairOK_of_genX`** — on every node of a generated tree (given `SmallX`).
  * **`computeChipVCLHX_honest_sat_pd`** — `computeChipVCLHX_honest_sat` at `pd := pdX sx`, with the
    `hpair` hypothesis replaced by `B ≤ ringChar F`.
  * §3 the tree-level form of the per-row `SmallX`: `FormLeafX q t` (every formula leaf `a` of every
    row has `a + 1 < q`) and `Op5DepthX D t` (every op-5 row's first-difference path has length `≤ D`)
    with `2^(D+1) ≤ q` give `SmallX q` at every row (`smallX_of_tree`), hence
    **`computeChipVCLHX_honest_sat_tree`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath fdN_spec)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (RowOKX HdlOK isPair PairOK)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX rowOKX_of_genX)

/-! ## 1. The comb records and the first difference -/

/-- **The AW records of a comb** (`(axis, k, v)` of each `walkRecA`), from spine depth `d` at axis `ax`:
row `d` provides `(2·ax, 0, l_d)` and `(2·ax + 1, wR, valR)`. -/
def recsA (sx : ℕ → ℕ) : ℕ → ℕ → List ℕ → List (ℕ × ℕ × ℕ)
  | _, ax, [x, x'] => [(2 * ax, 0, x), (2 * ax + 1, 0, x')]
  | d, ax, x :: x1 :: x2 :: xs =>
      (2 * ax, 0, x) :: (2 * ax + 1, 1, sx (d + 1)) :: recsA sx (d + 1) (2 * ax + 1) (x1 :: x2 :: xs)
  | _, _, _ => []

/-- **The first difference of two combs**: the axis and the two `(k, v)` records there. -/
def combFD (sxa sxb : ℕ → ℕ) : ℕ → ℕ → List ℕ → List ℕ → ℕ × (ℕ × ℕ) × (ℕ × ℕ)
  | _, ax, [x, x'], [y, y'] =>
      if x = y then (2 * ax + 1, (0, x'), (0, y')) else (2 * ax, (0, x), (0, y))
  | d, ax, [x, x'], y :: _ :: _ :: _ =>
      if x = y then (2 * ax + 1, (0, x'), (1, sxb (d + 1))) else (2 * ax, (0, x), (0, y))
  | d, ax, x :: _ :: _ :: _, [y, y'] =>
      if x = y then (2 * ax + 1, (1, sxa (d + 1)), (0, y')) else (2 * ax, (0, x), (0, y))
  | d, ax, x :: x1 :: x2 :: xs, y :: y1 :: y2 :: ys =>
      if x = y then combFD sxa sxb (d + 1) (2 * ax + 1) (x1 :: x2 :: xs) (y1 :: y2 :: ys)
      else (2 * ax, (0, x), (0, y))
  | _, _, _, _ => (0, (0, 0), (0, 0))

/-- What the first difference satisfies. -/
def FDOK (sxa sxb : ℕ → ℕ) (d ax : ℕ) (xs ys : List ℕ) (c : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  c.2.1.1 ≤ 1 ∧ c.2.2.1 ≤ 1 ∧ ¬ (c.2.1.1 = 1 ∧ c.2.2.1 = 1) ∧
    (c.2.1.1 = 0 → c.2.2.1 = 0 → c.2.1.2 ≠ c.2.2.2 ∧ c.2.1.2 < Nock.Atoms.B ∧ c.2.2.2 < Nock.Atoms.B) ∧
    (c.1, c.2.1) ∈ recsA sxa d ax xs ∧ (c.1, c.2.2) ∈ recsA sxb d ax ys

/-- **`combFD_spec`**: on two different limb lists of length `≥ 2` with limbs `< B`, the first
difference is a pair of AW records of the two combs at one axis, kinds bits, not both suffix rows, and
two inline limbs differ. -/
theorem combFD_spec (sxa sxb : ℕ → ℕ) :
    ∀ (xs ys : List ℕ) (d ax : ℕ), 2 ≤ xs.length → 2 ≤ ys.length → xs ≠ ys →
      (∀ x ∈ xs, x < Nock.Atoms.B) → (∀ y ∈ ys, y < Nock.Atoms.B) →
      FDOK sxa sxb d ax xs ys (combFD sxa sxb d ax xs ys)
  | [x, x'], [y, y'], d, ax, _, _, hne, hx, hy => by
    have hx0 := hx x (by simp); have hx1 := hx x' (by simp)
    have hy0 := hy y (by simp); have hy1 := hy y' (by simp)
    by_cases h : x = y
    · subst h
      have : x' ≠ y' := fun e => hne (by rw [e])
      simp [combFD, FDOK, recsA, this, hx1, hy1]
    · simp [combFD, FDOK, recsA, h, hx0, hy0]
  | [x, x'], y :: y1 :: y2 :: ys, d, ax, _, _, hne, hx, hy => by
    have hx0 := hx x (by simp); have hx1 := hx x' (by simp); have hy0 := hy y (by simp)
    by_cases h : x = y
    · subst h; simp [combFD, FDOK, recsA]
    · simp [combFD, FDOK, recsA, h, hx0, hy0]
  | x :: x1 :: x2 :: xs, [y, y'], d, ax, _, _, hne, hx, hy => by
    have hx0 := hx x (by simp); have hy0 := hy y (by simp); have hy1 := hy y' (by simp)
    by_cases h : x = y
    · subst h; simp [combFD, FDOK, recsA]
    · simp [combFD, FDOK, recsA, h, hx0, hy0]
  | x :: x1 :: x2 :: xs, y :: y1 :: y2 :: ys, d, ax, _, _, hne, hx, hy => by
    have hx0 := hx x (by simp); have hy0 := hy y (by simp)
    by_cases h : x = y
    · subst h
      have hne' : x1 :: x2 :: xs ≠ y1 :: y2 :: ys := fun e => hne (by rw [e])
      have ih := combFD_spec sxa sxb (x1 :: x2 :: xs) (y1 :: y2 :: ys) (d + 1) (2 * ax + 1)
        (by simp) (by simp) hne' (fun z hz => hx z (by simp at hz ⊢; tauto))
        (fun z hz => hy z (by simp at hz ⊢; tauto))
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
      simp only [combFD, if_true]
      refine ⟨h1, h2, h3, h4, ?_, ?_⟩
      · simp only [recsA]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h5)
      · simp only [recsA]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h6)
    · simp [combFD, FDOK, recsA, h, hx0, hy0]
  | [], _, _, _, h, _, _, _, _ => by simp at h
  | [_], _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _ :: _, [], _, _, _, h, _, _, _ => by simp at h
  | _ :: _ :: _, [_], _, _, _, h, _, _, _ => by simp at h

/-! ## 2. The honest limb data of a row -/

/-- **The honest α-pair limb data** of a row: the comb first difference of the canonical limbs of the
two first-difference leaves.  `sx a d` is the atom table's row serial of atom `a`'s spine row at depth
`d` (read only on a suffix-row record, which `PairOK` does not constrain). -/
def pdX (sx : ℕ → ℕ → ℕ) (r : RowNX) : ℕ × (ℕ × ℕ) × (ℕ × ℕ) :=
  match r.ftth, r.fttt with
  | .atom a, .atom b => combFD (sx a) (sx b) 0 1 (Nock.Atoms.limbs a) (Nock.Atoms.limbs b)
  | _, _ => (0, (0, 0), (0, 0))

theorem two_le_length_limbs {a : ℕ} (ha : Nock.Atoms.B ≤ a) : 2 ≤ (Nock.Atoms.limbs a).length := by
  by_contra h
  have h1 : (Nock.Atoms.limbs a).length ≤ 1 := by omega
  have h2 : a < Nock.Atoms.B ^ (Nock.Atoms.limbs a).length :=
    Nat.lt_base_pow_length_digits Nock.Atoms.one_lt_B
  have h3 : Nock.Atoms.B ^ (Nock.Atoms.limbs a).length ≤ Nock.Atoms.B ^ 1 :=
    Nat.pow_le_pow_right (by have := Nock.Atoms.one_lt_B; omega) h1
  rw [pow_one] at h3
  omega

theorem limbs_lt (a : ℕ) : ∀ x ∈ Nock.Atoms.limbs a, x < Nock.Atoms.B :=
  (Nock.Atoms.limbs_canonical a).1

theorem limbs_ne {a b : ℕ} (h : a ≠ b) : Nock.Atoms.limbs a ≠ Nock.Atoms.limbs b := by
  intro e; apply h; rw [← Nock.Atoms.val_limbs a, ← Nock.Atoms.val_limbs b, e]

/-- On an `isPair` row of a `RowOKX` row with an honest handle map, the two leaves are distinct atoms
`≥ ringChar F`. -/
theorem pair_atoms {F : Type} [Field F] {H : Noun → ℕ × ℕ} (hH : HdlOK (ringChar F) H) {r : RowNX}
    (hok : RowOKX (ringChar F) r) (hp : isPair H r) :
    ∃ a b, r.ftth = .atom a ∧ r.fttt = .atom b ∧ a ≠ b ∧ ringChar F ≤ a ∧ ringChar F ≤ b := by
  obtain ⟨hst, he, hk1, hk2⟩ := hp
  simp only [RowOKX, hst] at hok
  obtain ⟨-, -, -, -, -, het, h1, h2, -, -⟩ := hok
  have hne : r.sf1 ≠ r.sf2 := by
    intro e; rw [e, he] at het; simp [Noun.tis] at het
  have hd := (fdN_spec r.sf1 r.sf2 hne).2.1
  rw [← h1, ← h2] at hd
  have kind : ∀ n : Noun, (H n).1 = 2 → ∃ a, n = .atom a ∧ ringChar F ≤ a := by
    intro n hn
    cases n with
    | atom a =>
      refine ⟨a, rfl, ?_⟩
      by_contra hlt
      rw [hH.small a (by omega)] at hn; simp at hn
    | cell x y => rw [hH.cell x y] at hn; simp at hn
  obtain ⟨a, ha, hpa⟩ := kind _ hk1
  obtain ⟨b, hb, hpb⟩ := kind _ hk2
  refine ⟨a, b, ha, hb, fun e => hd (by rw [ha, hb, e]), hpa, hpb⟩

/-- **`PairOK` of the honest limb data** on a pair row (`B ≤ ringChar F`: the limbs are field
elements; Goldilocks satisfies it). -/
theorem pairOK_pdX {F : Type} [Field F] {H : Noun → ℕ × ℕ} (hH : HdlOK (ringChar F) H)
    (hB : Nock.Atoms.B ≤ ringChar F) (sx : ℕ → ℕ → ℕ) {r : RowNX}
    (hok : RowOKX (ringChar F) r) (hp : isPair H r) : PairOK (F := F) (pdX sx r) := by
  obtain ⟨a, b, ha, hb, hab, hpa, hpb⟩ := pair_atoms hH hok hp
  have hs := combFD_spec (sx a) (sx b) (Nock.Atoms.limbs a) (Nock.Atoms.limbs b) 0 1
    (two_le_length_limbs (by omega)) (two_le_length_limbs (by omega)) (limbs_ne hab)
    (limbs_lt a) (limbs_lt b)
  simp only [pdX, ha, hb]
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hs
  refine ⟨h1, h2, h3, fun k1 k2 => ?_⟩
  obtain ⟨hne, hx, hy⟩ := h4 k1 k2
  intro e
  have := (CharP.natCast_eq_natCast (R := F) (p := ringChar F)).1 e
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact hne this

/-- The honest limb data's records are AW records of the two leaves' combs, at one axis. -/
theorem pdX_records {F : Type} [Field F] {H : Noun → ℕ × ℕ} (hH : HdlOK (ringChar F) H)
    (hB : Nock.Atoms.B ≤ ringChar F) (sx : ℕ → ℕ → ℕ) {r : RowNX}
    (hok : RowOKX (ringChar F) r) (hp : isPair H r) :
    ∃ a b, r.ftth = .atom a ∧ r.fttt = .atom b ∧
      ((pdX sx r).1, (pdX sx r).2.1) ∈ recsA (sx a) 0 1 (Nock.Atoms.limbs a) ∧
      ((pdX sx r).1, (pdX sx r).2.2) ∈ recsA (sx b) 0 1 (Nock.Atoms.limbs b) := by
  obtain ⟨a, b, ha, hb, hab, hpa, hpb⟩ := pair_atoms hH hok hp
  have hs := combFD_spec (sx a) (sx b) (Nock.Atoms.limbs a) (Nock.Atoms.limbs b) 0 1
    (two_le_length_limbs (by omega)) (two_le_length_limbs (by omega)) (limbs_ne hab)
    (limbs_lt a) (limbs_lt b)
  refine ⟨a, b, ha, hb, ?_⟩
  simp only [pdX, ha, hb]
  exact ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩

/-- **`PairOK` on every generated pair row** (given the run's `SmallX` bounds). -/
theorem pairOK_of_genX {F : Type} [Field F] {R : Registry} {m : ℕ} {s f : Noun} {t : NTree SkelX}
    {r : Noun} (hgen : genX R m s f = some (t, r)) {H : Noun → ℕ × ℕ} (hH : HdlOK (ringChar F) H)
    (hB : Nock.Atoms.B ≤ ringChar F) (sx : ℕ → ℕ → ℕ)
    (hsm : ∀ u, InTree t u → SmallX (ringChar F) (rowOfSkelX u.label)) :
    ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := F) (pdX sx (rowOfSkelX u.label)) :=
  fun u hu hp => pairOK_pdX hH hB sx (rowOKX_of_genX hgen hu (hsm u hu)) hp

/-! ## 3. A tree-level form of `SmallX`: a formula-leaf bound and an op-5 depth binder -/

section Global
open Nock.NockVMROM.Thm54.VclL (hdN tlN)

/-- **The formula-leaf binder**: every atom leaf `a` of every row's formula has `a + 1 < q`. -/
def FormLeafX (q : ℕ) (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → ∀ a ∈ leavesOf u.label.formula, a + 1 < q

/-- **The op-5 depth binder**: on every op-5 row the first-difference path of the two operands has
length `≤ D` (EVERY op-5 row, the `=` rows included: `RowOKX.s5` bounds the axis unconditionally). -/
def Op5DepthX (D : ℕ) (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → u.label.state = .s5 → (fdN (kidE u.label 0) (kidE u.label 1)).1.length ≤ D

/-- **The jet-key binder**: on every jet row the clue's value, when an atom, is below `q`.  The jet
key is the VALUE of the clue, so (unlike the hint's tag) it is not a leaf of the formula and
`FormLeafX` does not bound it.  A constant clue `[1 id]` meets this binder whenever `FormLeafX`
holds. -/
def JetKeyX (q : ℕ) (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → u.label.state = .s11j → ∀ id, kidE u.label 0 = .atom id → id < q

theorem leaves_hdN {a : ℕ} : ∀ {n : Noun}, a ∈ leavesOf (hdN n) → a ∈ leavesOf n
  | .atom _, h => h
  | .cell _ _, h => by simp only [leavesOf, List.mem_append]; exact Or.inl h

theorem leaves_tlN {a : ℕ} : ∀ {n : Noun}, a ∈ leavesOf (tlN n) → a ∈ leavesOf n
  | .atom _, h => h
  | .cell _ _, h => by simp only [leavesOf, List.mem_append]; exact Or.inr h

theorem foldl_axis_lt : ∀ (l : List Bool) (a : ℕ),
    l.foldl (fun a b => 2 * a + (if b then 1 else 0)) a < (a + 1) * 2 ^ l.length
  | [], a => by simp
  | b :: l, a => by
    have ih := foldl_axis_lt l (2 * a + (if b then 1 else 0))
    simp only [List.foldl_cons, List.length_cons]
    refine lt_of_lt_of_le ih ?_
    rw [pow_succ]
    have : 2 * a + (if b then 1 else 0) + 1 ≤ (a + 1) * 2 := by split_ifs <;> omega
    calc (2 * a + (if b then 1 else 0) + 1) * 2 ^ l.length ≤ ((a + 1) * 2) * 2 ^ l.length :=
          Nat.mul_le_mul_right _ this
      _ = (a + 1) * (2 ^ l.length * 2) := by ring

theorem axisOfPath_lt (l : List Bool) : axisOfPath l < 2 ^ (l.length + 1) := by
  have := foldl_axis_lt l 1
  unfold axisOfPath; rw [pow_succ]; linarith

/-- **`SmallX` at every row of the tree** from the three tree-level binders (`2^(D+1) ≤ q`). -/
theorem smallX_of_tree {q D : ℕ} {t : NTree SkelX} (hL : FormLeafX q t) (hD : Op5DepthX D t)
    (hK : JetKeyX q t)
    (hDq : 2 ^ (D + 1) ≤ q) : ∀ u, InTree t u → SmallX q (rowOfSkelX u.label) := by
  intro u hu
  have hl := hL u hu
  have leaf : ∀ {n : Noun} {a : ℕ}, n = .atom a → a ∈ leavesOf n := by
    intro n a h; subst h; exact mem_leavesOf_atom a
  cases hst : u.label.state <;> simp only [SmallX, rowOfSkelX, hst]
  · intro ax h; have := hl ax (leaves_tlN (leaf h)); omega
  · have h5 := hD u hu hst
    have := axisOfPath_lt (fdN (kidE u.label 0) (kidE u.label 1)).1
    have : 2 ^ ((fdN (kidE u.label 0) (kidE u.label 1)).1.length + 1) ≤ 2 ^ (D + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro ax h; have := hl ax (leaves_tlN (leaves_hdN (leaf h))); omega
  · intro a h; have := hl a (leaves_tlN (leaves_hdN (leaves_hdN (leaf h)))); omega
  · intro a h; exact hl a (leaf h)
  · exact ⟨fun a h => by have := hl a (leaves_tlN (leaves_hdN (leaves_hdN (leaf h)))); omega,
      fun id h => hK u hu hst id h⟩

end Global

/-! ## 4. The honest acceptance at the honest limb data -/

section Main
open Polynomial Module
open Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX (dVal aVal)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

open Classical in
/-- **`computeChipVCLHX` accepts the honest trace at the honest limb data `pd := pdX sx`** (HC4):
`computeChipVCLHX_honest_sat` with `hpair` discharged by `pairOK_of_genX` under `B ≤ ringChar F`. -/
theorem computeChipVCLHX_honest_sat_pd {R : Registry} {m : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (hgen : genX R m s f = some (t, r))
    (H : Noun → ℕ × ℕ) (sx : ℕ → ℕ → ℕ)
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F) (hB : Nock.Atoms.B ≤ ringChar F)
    (hsm : ∀ u, InTree t u → SmallX (ringChar F) (rowOfSkelX u.label))
    (α γ : K) (hord : (bfsForest [t]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = curW (F := F) H (bfsForest [t]) γ 1 * α)
    (hpO : limbVal b pubVal pubOut = 0)
    (hpub : pubVal 0 = hk H s ∧ pubVal 1 = hv H s ∧ pubVal 2 = hk H f ∧ pubVal 3 = hv H f ∧
      pubVal 4 = hk H r ∧ pubVal 5 = hv H r)
    (hρ : ∀ a < 6, ∀ k : Fin 3, pubVal (pubOfA a + k) =
      coord b (accV b δ H (pdX sx) (bfsForest [t]) chalV pubVal a n) k)
    (hnb : ∀ j < n, ∀ S ∈ Handle.ChipHX.slotsX (F := F),
      dVal b δ S (env0 H (pdX sx) (bfsForest [t]) chalV pubVal j) ≠ 0 ∨
        aVal b δ S (env0 H (pdX sx) (bfsForest [t]) chalV pubVal j) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit)
      (polyX b δ H (pdX sx) (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α)
        (accW (F := F) H (bfsForest [t]) α γ) nodes
        (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w) :=
  computeChipVCLHX_honest_sat δ hgen H (pdX sx) hH hp hsm (pairOK_of_genX hgen hH hB sx hsm) α γ hord
    hn hN nodes hinj b chalV pubVal orbit hadj hα hγ hpIC hpS hpO hpub hρ hnb

open Classical in
/-- **The same with `SmallX` from the two tree-level binders** (`FormLeafX`, `Op5DepthX`, `smallX_of_tree`). -/
theorem computeChipVCLHX_honest_sat_tree {R : Registry} {m : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (hgen : genX R m s f = some (t, r))
    (H : Noun → ℕ × ℕ) (sx : ℕ → ℕ → ℕ)
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F) (hB : Nock.Atoms.B ≤ ringChar F)
    {D : ℕ} (hL : FormLeafX (ringChar F) t) (hD : Op5DepthX D t) (hK : JetKeyX (ringChar F) t)
    (hDq : 2 ^ (D + 1) ≤ ringChar F)
    (α γ : K) (hord : (bfsForest [t]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = curW (F := F) H (bfsForest [t]) γ 1 * α)
    (hpO : limbVal b pubVal pubOut = 0)
    (hpub : pubVal 0 = hk H s ∧ pubVal 1 = hv H s ∧ pubVal 2 = hk H f ∧ pubVal 3 = hv H f ∧
      pubVal 4 = hk H r ∧ pubVal 5 = hv H r)
    (hρ : ∀ a < 6, ∀ k : Fin 3, pubVal (pubOfA a + k) =
      coord b (accV b δ H (pdX sx) (bfsForest [t]) chalV pubVal a n) k)
    (hnb : ∀ j < n, ∀ S ∈ Handle.ChipHX.slotsX (F := F),
      dVal b δ S (env0 H (pdX sx) (bfsForest [t]) chalV pubVal j) ≠ 0 ∨
        aVal b δ S (env0 H (pdX sx) (bfsForest [t]) chalV pubVal j) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit)
      (polyX b δ H (pdX sx) (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α)
        (accW (F := F) H (bfsForest [t]) α γ) nodes
        (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w) :=
  computeChipVCLHX_honest_sat_pd δ hgen H sx hH hp hB (smallX_of_tree hL hD hK hDq) α γ hord
    hn hN nodes hinj b chalV pubVal orbit hadj hα hγ hpIC hpS hpO hpub hρ hnb

end Main

end Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX
