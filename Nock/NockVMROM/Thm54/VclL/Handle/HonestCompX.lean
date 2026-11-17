/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestCompX.lean

  **The honest ROUND-0 columns of
  `computeChipVCLHX` (123) and their base gates, per state.**  Additive: a NEW module.

  * `HdlOK p H` — what an honest handle map `H : Noun → ℕ × ℕ` (wire kind, value) satisfies: a
    small atom `v < p` is `(0, v)`, a big atom has kind `2`, a cell kind `1` (the cell / atom table
    indices are free: the base gates read only kinds, small values and handle equalities).
  * `colX H pd r fst lst` — the honest columns `0.. 68` of a noun row `r : RowNX` (`GenXRows`): the
    `StateX` one-hot, `isFirst / isLast`, `z1 v β v2 w pr`, the twelve handles `(k, v)`, `kb = [k = 2]`,
    op 4's `fast, inv4`, and the α second pair `ax2, pr2, l₁, l₂` (op 5, both first-difference leaves
    big; the limb data `pd r` is a parameter, `PairOK` its local condition).
  * `RowOKX p r` — what the gates need of a row, per state (`RowNX.SemN` plus: the small-atom bounds on
    the axis / id atoms, the op-5 first-difference shape, and the real-child formulas being cells —
    the kid-kind gates).
  * **`arith_hold` / `eq_hold`** — every arithmetic and equality base gate of `computeChipVCLHX`
    vanishes at the honest row, split per state (`restA_sX`, `restE_sX`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
import Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
import Nock.Edit.GenXRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

open Nock Nock.Noun Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath fdN_spec two_le_axisOfPath slot_cell)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS prodL heq hpub EqG Opnd consCol)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx stIdx_lt)

noncomputable section

/-! ## 1. Handles -/

/-- **What an honest handle map satisfies** at modulus `p`. -/
structure HdlOK (p : ℕ) (H : Noun → ℕ × ℕ) : Prop where
  small : ∀ v, v < p → H (.atom v) = (0, v)
  big : ∀ v, p ≤ v → (H (.atom v)).1 = 2
  cell : ∀ a b, (H (.cell a b)).1 = 1

section Cols
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

def hk (n : Noun) : F := ((H n).1 : F)
def hv (n : Noun) : F := ((H n).2 : F)
def hb (n : Noun) : F := if (H n).1 = 2 then 1 else 0

/-- The twelve handle nouns of a row, in `hdX` order. -/
def hN (r : RowNX) : ℕ → Noun
  | 0 => r.s | 1 => r.f | 2 => r.e | 3 => r.sf1 | 4 => r.sf2 | 5 => r.fh | 6 => r.ft | 7 => r.fth
  | 8 => r.ftt | 9 => r.ftth | 10 => r.fttt | _ => r.m

open Classical in
/-- The op-5 α-pair mode: `≠`, both first-difference leaves big. -/
def isPair (r : RowNX) : Prop :=
  r.st = .s5 ∧ r.e = .atom 1 ∧ (H r.ftth).1 = 2 ∧ (H r.fttt).1 = 2

open Classical in
/-- The op-5 `(v, v2, w)` on a `≠` row, by the kinds of the two first-difference leaves. -/
def op5T (r : RowNX) : F × F × F :=
  if (H r.ftth).1 = 2 ∧ (H r.fttt).1 = 2 then
    let l1 := (pd r).2.1
    let l2 := (pd r).2.2
    let pv : F := if l1.1 = 0 then (l1.2 : F) else (l2.2 : F) + 1
    let pv2 : F := if l2.1 = 0 then (l2.2 : F) else pv - 1
    (pv, pv2, (pv - pv2)⁻¹)
  else if (H r.ftth).1 = 0 ∧ (H r.fttt).1 = 0 then
    (hv H r.ftth, hv H r.fttt, (hv H r.ftth - hv H r.fttt)⁻¹)
  else if ((H r.ftth).1 = 1 ∧ (H r.fttt).1 = 2) ∨ ((H r.ftth).1 = 2 ∧ (H r.fttt).1 = 1) then
    (1, 0, -1)
  else (hv H r.ftth, hv H r.fttt, 0)

open Classical in
def cZ1 (r : RowNX) : F :=
  match r.st with
  | .s0 => if r.ft = .atom 1 then 1 else 0
  | .s5 => if r.e = .atom 1 ∧ r.m = .atom 1 then 1 else 0
  | .s9 => if r.fth = .atom 1 then 1 else 0
  | .s10 => if r.ftth = .atom 1 then 1 else 0
  | _ => 0

open Classical in
def cV (r : RowNX) : F :=
  match r.st with
  | .s0 => hv H r.ft
  | .s4 => hv H r.sf1
  | .s5 => if r.e = .atom 1 then (op5T H pd r).1 else 0
  | .s6 => hv H r.sf2
  | .s9 => hv H r.fth
  | .s10 => hv H r.ftth
  | .s10L => ((chainAxis r.f / 2 : ℕ) : F)
  | _ => 0

open Classical in
def cB (r : RowNX) : F :=
  match r.st with
  | .s3 => if r.sf1.isCell then 0 else 1
  | .s5 => if r.e = .atom 1 then 1 else 0
  | .s10L => ((chainAxis r.f % 2 : ℕ) : F)
  | _ => 0

open Classical in
def cV2 (r : RowNX) : F :=
  match r.st with
  | .s4 => hv H r.sf1 + 1
  | .s5 => if r.e = .atom 1 then (op5T H pd r).2.1 else 0
  | .s10L => ((chainAxis r.f : ℕ) : F)
  | _ => 0

open Classical in
def cW (r : RowNX) : F :=
  match r.st with
  | .s5 => if r.e = .atom 1 then (op5T H pd r).2.2 else 0
  | .s10L => (((chainAxis r.f : ℕ) : F) - 1)⁻¹
  | _ => 0

open Classical in
def cPr (r : RowNX) : F :=
  match r.st with
  | .s5 => if r.e = .atom 1 ∧ r.m ≠ .atom 1 then 1 else 0
  | .s10L => 1
  | _ => 0

open Classical in
def cFast (r : RowNX) : F :=
  match r.st with
  | .s4 => if (H r.e).1 = 0 then 1 else 0
  | _ => 0

def cInv4 (r : RowNX) : F :=
  match r.st with
  | .s4 => (hv H r.sf1 + 1)⁻¹
  | _ => 0

open Classical in
def cAx2 (r : RowNX) : F :=
  match r.st with
  | .s10L => ((chainAxis r.f ^^^ 1 : ℕ) : F)
  | .s5 => if isPair H r then ((pd r).1 : F) else 0
  | _ => 0

open Classical in
def cPr2 (r : RowNX) : F := if isPair H r then 1 else 0

open Classical in
/-- `l₁ = (65, 66)`, `l₂ = (67, 68)` (index `0..3`). -/
def cL (r : RowNX) (j : ℕ) : F :=
  if isPair H r then
    (match j with
     | 0 => ((pd r).2.1.1 : F) | 1 => ((pd r).2.1.2 : F) | 2 => ((pd r).2.2.1 : F) | _ => ((pd r).2.2.2 : F))
  else 0

/-- **The honest round-0 columns `0.. 68`** of a noun row. -/
def colX (r : RowNX) (fst lst : F) : ℕ → F := fun i =>
  if i < 17 then (if stIdx r.st = i then 1 else 0)
  else if i = 17 then fst else if i = 18 then lst
  else if i = 19 then cZ1 r else if i = 20 then cV H pd r else if i = 21 then cB r
  else if i = 22 then cV2 H pd r else if i = 23 then cW H pd r else if i = 24 then cPr r
  else if i < 49 then
    (if (i - 25) % 2 = 0 then hk H (hN r ((i - 25) / 2)) else hv H (hN r ((i - 25) / 2)))
  else if i < 61 then hb H (hN r (i - 49))
  else if i = 61 then cFast H r else if i = 62 then cInv4 H r
  else if i = 63 then cAx2 H pd r else if i = 64 then cPr2 H r
  else if i < 69 then cL H pd r (i - 65)
  else 0

/-- The honest base environment (base gates read the current row and the publics). -/
def hEnvX (r : RowNX) (fst lst : F) (pub : ℕ → F) : Env F :=
  ⟨colX H pd r fst lst, colX H pd r fst lst, fun _ => 0, pub⟩

end Cols

/-! ## 2. What the gates need of a row -/

/-- **The row facts the base gates need** (per state). -/
def RowOKX (p : ℕ) (r : RowNX) : Prop :=
  match r.st with
  | .s0 => r.fh = .atom 0 ∧ r.f = .cell r.fh r.ft ∧
      ∃ ax, ax < p ∧ r.ft = .atom ax ∧ Noun.slot ax r.s = some r.e
  | .s1 => r.fh = .atom 1 ∧ r.f = .cell r.fh r.ft ∧ r.e = r.ft
  | .s2 => r.fh = .atom 2 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth.isCell = true ∧ r.ftt.isCell = true ∧ r.sf2.isCell = true
  | .s3 => r.fh = .atom 3 ∧ r.f = .cell r.fh r.ft ∧ r.e = Noun.wut r.sf1 ∧ r.ft.isCell = true
  | .s4 => r.fh = .atom 4 ∧ r.f = .cell r.fh r.ft ∧ r.ft.isCell = true ∧
      ∃ n, r.sf1 = .atom n ∧ r.e = .atom (n + 1)
  | .s5 => r.fh = .atom 5 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth.isCell = true ∧ r.ftt.isCell = true ∧ r.e = Noun.tis r.sf1 r.sf2 ∧
      r.ftth = (fdN r.sf1 r.sf2).2.1 ∧ r.fttt = (fdN r.sf1 r.sf2).2.2 ∧
      r.m = .atom (axisOfPath (fdN r.sf1 r.sf2).1) ∧ axisOfPath (fdN r.sf1 r.sf2).1 < p
  | .s6 => r.fh = .atom 6 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.ftt = .cell r.ftth r.fttt ∧ r.e = r.sf1 ∧
      ((r.sf2 = .atom 0 ∧ r.m = r.ftth) ∨ (r.sf2 = .atom 1 ∧ r.m = r.fttt)) ∧
      r.m.isCell = true ∧ r.fth.isCell = true
  | .s7 => r.fh = .atom 7 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1 ∧
      r.ftt.isCell = true ∧ r.fth.isCell = true
  | .s8 => r.fh = .atom 8 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1 ∧
      r.m = .cell r.sf2 r.s ∧ r.ftt.isCell = true ∧ r.fth.isCell = true
  | .s9 => r.fh = .atom 9 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf2 ∧
      (∃ ax, ax < p ∧ r.fth = .atom ax ∧ Noun.slot ax r.sf1 = some r.m) ∧
      r.ftt.isCell = true ∧ r.m.isCell = true
  | .cons => r.fh.isCell = true ∧ r.f = .cell r.fh r.ft ∧ r.e = .cell r.sf1 r.sf2 ∧
      r.ft.isCell = true
  | .s10 => r.fh = .atom 10 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧
      (∃ a, a < p ∧ r.ftth = .atom a ∧ Noun.edit a r.sf1 r.sf2 = some r.e) ∧
      r.fttt.isCell = true ∧ r.ftt.isCell = true
  | .s10L => r.fh = .atom 0 ∧ ∃ a, r.f = .atom a ∧ 2 ≤ a ∧ a + 1 < p ∧ r.sf1 = r.s ∧ r.sf2 = r.e ∧
      r.m = .atom (a ^^^ 1) ∧ Noun.slot (a ^^^ 1) r.sf1 = some r.ftth ∧
      Noun.slot (a ^^^ 1) r.sf2 = some r.fttt ∧ r.ftth = r.fttt
  | .s10T => r.fh = .atom 0 ∧ r.f = .atom 1
  | .s11s => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      (∃ b, r.fth = .atom b) ∧ r.ftt.isCell = true
  | .s11d => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧ r.fttt.isCell = true ∧ r.ftt.isCell = true
  | .s11j => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧ (Nock.Jet.wildTag < p ∧ r.ftth = .atom Nock.Jet.wildTag) ∧
      (∃ id, id < p ∧ r.sf1 = .atom id) ∧ r.fttt.isCell = true

/-- **The α-pair limb data's local condition** (on an `isPair` row): limb kinds are bits, not both
suffix rows, and two small limbs differ in `F`. -/
def PairOK {F : Type} [Field F] (d : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  d.2.1.1 ≤ 1 ∧ d.2.2.1 ≤ 1 ∧ ¬ (d.2.1.1 = 1 ∧ d.2.2.1 = 1) ∧
    (d.2.1.1 = 0 → d.2.2.1 = 0 → ((d.2.1.2 : ℕ) : F) ≠ ((d.2.2.2 : ℕ) : F))


/-! ## 3. Column evaluation -/

section Eval
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (r : RowNX) (fst lst : F) (pub : ℕ → F)

theorem kind3 {p : ℕ} (hH : HdlOK p H) (n : Noun) : (H n).1 = 0 ∨ (H n).1 = 1 ∨ (H n).1 = 2 := by
  cases n with
  | atom v =>
    by_cases hv : v < p
    · left; rw [hH.small v hv]
    · right; right; exact hH.big v (by omega)
  | cell a b => right; left; exact hH.cell a b

theorem colX_st (i : ℕ) (hi : i < 17) : colX H pd r fst lst i = if stIdx r.st = i then 1 else 0 := by
  simp [colX, hi]

theorem colX_k (j : ℕ) (hj : j < 12) : colX H pd r fst lst (25 + 2 * j) = hk H (hN r j) := by
  have e1 : (25 + 2 * j - 25) / 2 = j := by omega
  have e2 : (25 + 2 * j - 25) % 2 = 0 := by omega
  unfold colX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos e2, e1]

theorem colX_v (j : ℕ) (hj : j < 12) : colX H pd r fst lst (26 + 2 * j) = hv H (hN r j) := by
  have e1 : (26 + 2 * j - 25) / 2 = j := by omega
  have e2 : ¬ (26 + 2 * j - 25) % 2 = 0 := by omega
  unfold colX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg e2, e1]

theorem colX_kb (j : ℕ) (hj : j < 12) : colX H pd r fst lst (49 + j) = hb H (hN r j) := by
  unfold colX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 49 + j - 49 = j by omega]

@[simp] theorem cx17 : colX H pd r fst lst 17 = fst := by simp [colX]
@[simp] theorem cx18 : colX H pd r fst lst 18 = lst := by simp [colX]
@[simp] theorem cx19 : colX H pd r fst lst 19 = cZ1 r := by simp [colX]
@[simp] theorem cx20 : colX H pd r fst lst 20 = cV H pd r := by simp [colX]
@[simp] theorem cx21 : colX H pd r fst lst 21 = cB r := by simp [colX]
@[simp] theorem cx22 : colX H pd r fst lst 22 = cV2 H pd r := by simp [colX]
@[simp] theorem cx23 : colX H pd r fst lst 23 = cW H pd r := by simp [colX]
@[simp] theorem cx24 : colX H pd r fst lst 24 = cPr r := by simp [colX]
@[simp] theorem cx61 : colX H pd r fst lst 61 = cFast H r := by simp [colX]
@[simp] theorem cx62 : colX H pd r fst lst 62 = cInv4 H r := by simp [colX]
@[simp] theorem cx63 : colX H pd r fst lst 63 = cAx2 H pd r := by simp [colX]
@[simp] theorem cx64 : colX H pd r fst lst 64 = cPr2 H r := by simp [colX]
@[simp] theorem cx65 : colX H pd r fst lst 65 = cL H pd r 0 := by simp [colX]
@[simp] theorem cx66 : colX H pd r fst lst 66 = cL H pd r 1 := by simp [colX]
@[simp] theorem cx67 : colX H pd r fst lst 67 = cL H pd r 2 := by simp [colX]
@[simp] theorem cx68 : colX H pd r fst lst 68 = cL H pd r 3 := by simp [colX]

/-- The handle columns by name. -/
@[simp] theorem cxS_k : colX H pd r fst lst 25 = hk H r.s := colX_k H pd r fst lst 0 (by decide)
@[simp] theorem cxS_v : colX H pd r fst lst 26 = hv H r.s := colX_v H pd r fst lst 0 (by decide)
@[simp] theorem cxF_k : colX H pd r fst lst 27 = hk H r.f := colX_k H pd r fst lst 1 (by decide)
@[simp] theorem cxF_v : colX H pd r fst lst 28 = hv H r.f := colX_v H pd r fst lst 1 (by decide)
@[simp] theorem cxE_k : colX H pd r fst lst 29 = hk H r.e := colX_k H pd r fst lst 2 (by decide)
@[simp] theorem cxE_v : colX H pd r fst lst 30 = hv H r.e := colX_v H pd r fst lst 2 (by decide)
@[simp] theorem cxSf1_k : colX H pd r fst lst 31 = hk H r.sf1 := colX_k H pd r fst lst 3 (by decide)
@[simp] theorem cxSf1_v : colX H pd r fst lst 32 = hv H r.sf1 := colX_v H pd r fst lst 3 (by decide)
@[simp] theorem cxSf2_k : colX H pd r fst lst 33 = hk H r.sf2 := colX_k H pd r fst lst 4 (by decide)
@[simp] theorem cxSf2_v : colX H pd r fst lst 34 = hv H r.sf2 := colX_v H pd r fst lst 4 (by decide)
@[simp] theorem cxFh_k : colX H pd r fst lst 35 = hk H r.fh := colX_k H pd r fst lst 5 (by decide)
@[simp] theorem cxFh_v : colX H pd r fst lst 36 = hv H r.fh := colX_v H pd r fst lst 5 (by decide)
@[simp] theorem cxFt_k : colX H pd r fst lst 37 = hk H r.ft := colX_k H pd r fst lst 6 (by decide)
@[simp] theorem cxFt_v : colX H pd r fst lst 38 = hv H r.ft := colX_v H pd r fst lst 6 (by decide)
@[simp] theorem cxFth_k : colX H pd r fst lst 39 = hk H r.fth := colX_k H pd r fst lst 7 (by decide)
@[simp] theorem cxFth_v : colX H pd r fst lst 40 = hv H r.fth := colX_v H pd r fst lst 7 (by decide)
@[simp] theorem cxFtt_k : colX H pd r fst lst 41 = hk H r.ftt := colX_k H pd r fst lst 8 (by decide)
@[simp] theorem cxFtt_v : colX H pd r fst lst 42 = hv H r.ftt := colX_v H pd r fst lst 8 (by decide)
@[simp] theorem cxFtth_k : colX H pd r fst lst 43 = hk H r.ftth := colX_k H pd r fst lst 9 (by decide)
@[simp] theorem cxFtth_v : colX H pd r fst lst 44 = hv H r.ftth := colX_v H pd r fst lst 9 (by decide)
@[simp] theorem cxFttt_k : colX H pd r fst lst 45 = hk H r.fttt := colX_k H pd r fst lst 10 (by decide)
@[simp] theorem cxFttt_v : colX H pd r fst lst 46 = hv H r.fttt := colX_v H pd r fst lst 10 (by decide)
@[simp] theorem cxM_k : colX H pd r fst lst 47 = hk H r.m := colX_k H pd r fst lst 11 (by decide)
@[simp] theorem cxM_v : colX H pd r fst lst 48 = hv H r.m := colX_v H pd r fst lst 11 (by decide)
@[simp] theorem cxS_b : colX H pd r fst lst 49 = hb H r.s := colX_kb H pd r fst lst 0 (by decide)
@[simp] theorem cxF_b : colX H pd r fst lst 50 = hb H r.f := colX_kb H pd r fst lst 1 (by decide)
@[simp] theorem cxE_b : colX H pd r fst lst 51 = hb H r.e := colX_kb H pd r fst lst 2 (by decide)
@[simp] theorem cxSf1_b : colX H pd r fst lst 52 = hb H r.sf1 := colX_kb H pd r fst lst 3 (by decide)
@[simp] theorem cxSf2_b : colX H pd r fst lst 53 = hb H r.sf2 := colX_kb H pd r fst lst 4 (by decide)
@[simp] theorem cxFh_b : colX H pd r fst lst 54 = hb H r.fh := colX_kb H pd r fst lst 5 (by decide)
@[simp] theorem cxFt_b : colX H pd r fst lst 55 = hb H r.ft := colX_kb H pd r fst lst 6 (by decide)
@[simp] theorem cxFth_b : colX H pd r fst lst 56 = hb H r.fth := colX_kb H pd r fst lst 7 (by decide)
@[simp] theorem cxFtt_b : colX H pd r fst lst 57 = hb H r.ftt := colX_kb H pd r fst lst 8 (by decide)
@[simp] theorem cxFtth_b : colX H pd r fst lst 58 = hb H r.ftth := colX_kb H pd r fst lst 9 (by decide)
@[simp] theorem cxFttt_b : colX H pd r fst lst 59 = hb H r.fttt := colX_kb H pd r fst lst 10 (by decide)
@[simp] theorem cxM_b : colX H pd r fst lst 60 = hb H r.m := colX_kb H pd r fst lst 11 (by decide)

end Eval

/-! ## 4. The state-free gate groups: one-hot and kinds -/

section Free
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (r : RowNX) (fst lst : F) (pub : ℕ → F)

theorem kbX_hdX (j : ℕ) : kbX (hdX j) = 49 + j := by simp [kbX, hdX]

theorem kind_hold (hH : HdlOK (ringChar F) H) :
    ∀ g ∈ (kindG : List (CoeffExpr ℚ)), evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  intro g hg
  obtain ⟨h, hh, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
  rw [List.mem_range] at hj
  have ek : (hEnvX H pd r fst lst pub).trace (hdX j).k = hk H (hN r j) := colX_k H pd r fst lst j hj
  have eb : (hEnvX H pd r fst lst pub).trace (kbX (hdX j)) = hb H (hN r j) := by
    rw [kbX_hdX]; exact colX_kb H pd r fst lst j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases kind3 H hH (hN r j) with hc | hc | hc
  all_goals rcases hg with rfl | rfl | rfl
  all_goals simp [boolG, kbE, kcE, evalQX, cc, ek, eb, hk, hb, hc]

theorem selS_range17 :
    evalQX (selS (List.range nStates) : CoeffExpr ℚ) (hEnvX H pd r fst lst pub) = 1 := by
  cases h : r.st <;>
    simp [selS, nStates, CoeffExpr.sumList, List.range_succ, evalQX, cc, hEnvX, colX_st, h, stIdx]

end Free

/-! ## 5. The state-dependent arithmetic gates, per state -/

/-- The arithmetic gates after the one-hot and kind groups. -/
def restA : List (CoeffExpr ℚ) :=
  svG ++ op0G ++ op3G ++ op4G ++ op5G ++ op6G ++ op8G ++ op9G ++ consG ++ s10G ++ s10LG ++ s11G ++ kidKindG

/-- The equality gates before the claim publics. -/
def restE : List (EqG ℚ) :=
  svEq ++ op0Eq ++ op1Eq ++ op3Eq ++ op4Eq ++ op5Eq ++ op6Eq ++ op78Eq ++ op9Eq ++ s10Eq ++ s10LEq ++ s10TEq

theorem eqGatesX_split : (eqGatesX : List (EqG ℚ)) = restE ++ claimEq := by
  simp [eqGatesX, restE]

theorem arithGatesX_split : (arithGatesX : List (CoeffExpr ℚ)) = oneHotG ++ kindG ++ restA := by
  simp [arithGatesX, restA]

section Facts
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ)

theorem hS_ (hH : HdlOK (ringChar F) H) {v : ℕ} (h : v < ringChar F) : H (.atom v) = (0, v) :=
  hH.small v h

theorem hC_ (hH : HdlOK (ringChar F) H) {n : Noun} (h : n.isCell = true) : (H n).1 = 1 := by
  cases n with
  | atom _ => simp [Noun.isCell] at h
  | cell a b => exact hH.cell a b

theorem castLt_ne {a b : ℕ} (ha : a < ringChar F) (hb : b < ringChar F) (h : a ≠ b) :
    ((a : ℕ) : F) ≠ ((b : ℕ) : F) := by
  intro he; apply h
  haveI := ringChar.charP F
  exact Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast F (ringChar F)).mp he) ha hb

theorem small_of_k0 (hH : HdlOK (ringChar F) H) {n : Noun} (h : (H n).1 = 0) :
    ∃ v, v < ringChar F ∧ n = .atom v ∧ H n = (0, v) := by
  cases n with
  | atom v =>
    by_cases hv : v < ringChar F
    · exact ⟨v, hv, rfl, hH.small v hv⟩
    · have := hH.big v (by omega); omega
  | cell a b => have := hH.cell a b; omega

theorem cell_of_k1 (hH : HdlOK (ringChar F) H) {n : Noun} (h : (H n).1 = 1) : n.isCell = true := by
  cases n with
  | atom v =>
    by_cases hv : v < ringChar F
    · rw [hH.small v hv] at h; simp at h
    · have := hH.big v (by omega); omega
  | cell a b => rfl

end Facts

open Lean in
macro "xnorm" : tactic => `(tactic| simp only [restA, restE, svG, op0G, op3G, op4G, op5G, op6G, op8G, op9G,
    consG, s10G, s10LG, s11G, kidKindG, kidFormsX, svEq, op0Eq, op1Eq, op3Eq, op4Eq, op5Eq, op6Eq, op78Eq,
    op9Eq, s10Eq, s10LEq, s10TEq, heq, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, List.range_succ,
    List.range_zero, List.forall_mem_map, and_true])

open Lean in
macro "xsimp" : tactic => `(tactic| simp [restA, svG, op0G, op3G, op4G, op5G, op6G, op8G, op9G, consG,
    s10G, s10LG, s11G, kidKindG, kidFormsX, evalQX, CoeffExpr.sumList, selS, prodL, cc, notC, kbE, kcE,
    smallE, boolG, oneMinus, neGateX, prGateX, pr2GateX, hEnvX, colX_st, stIdx, xS, xF, xE, xSf1, xSf2,
    xFh, xFt, xFth, xFtt, xFtth, xFttt, xM, hdX, kbX, l2X, l3X, consCol, z1X, vX, betaX, v2X, wX, prX,
    fastX, inv4X, ax2X, pr2X, xL1, xL2, sS10, sS10L, sS10T, sS11s, sS11d, sS11j, cZ1, cV, cB, cV2, cW,
    cPr, cFast, cInv4, cAx2, cPr2, cL, isPair, op5T, hk, hv, hb, restE, svEq, op0Eq, op1Eq, op3Eq, op4Eq, op5Eq,
    op6Eq, op78Eq, op9Eq, s10Eq, s10LEq, s10TEq, EqG.gate, Opnd.expr, heq, Noun.wut, Noun.isCell, chainAxis, *])


theorem edit_cell : ∀ (a : ℕ) {n o e : Noun}, Noun.edit a n o = some e → a ≠ 1 → e.isCell = true := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro n o e h ha
    match a, ih, h, ha with
    | 0, _, h, _ => simp [Noun.edit] at h
    | 1, _, _, ha => exact absurd rfl ha
    | a + 2, ih, h, _ =>
      rw [Noun.edit] at h
      simp only at h
      split at h
      · rename_i sib _
        by_cases h1 : (a + 2) / 2 = 1
        · rw [h1] at h; simp [Noun.edit] at h; subst h; split <;> rfl
        · exact ih _ (by omega) h h1
      · simp at h

section States
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (r : RowNX) (fst lst : F) (pub : ℕ → F) (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)

include hH hp in
theorem restA_s0 (hst : r.st = .s0) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  obtain ⟨hfh, hf, ax, hax, hft, hsl⟩ := hok
  have e1 := hS_ H hH (v := 0) (by omega)
  have e2 := hS_ H hH hax
  have e3 := hC_ H hH (n := r.f) (by rw [hf]; rfl)
  clear hf
  have e4 : ax ≠ 1 → (H r.s).1 = 1 := fun h => hC_ H hH (slot_cell ax r.s r.e hsl h)
  by_cases ha1 : ax = 1
  · subst ha1; xsimp
  · have e5 := e4 ha1; clear e4; xsimp

include hH hp in
theorem restE_s0 (hst : r.st = .s0) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  obtain ⟨hfh, hf, ax, hax, hft, hsl⟩ := hok
  have e1 := hS_ H hH (v := 0) (by omega)
  have e2 := hS_ H hH hax
  clear hf
  by_cases ha1 : ax = 1
  · subst ha1
    have hse : r.e = r.s := by simpa [Noun.slot] using hsl.symm
    xnorm; xsimp
  · xnorm; xsimp

include hH hp in
theorem restA_s1 (hst : r.st = .s1) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, he⟩ := hok
  have et := hS_ H hH (v := 1) (by omega)

  xnorm; xsimp

include hH hp in
theorem restE_s1 (hst : r.st = .s1) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, he⟩ := hok
  have et := hS_ H hH (v := 1) (by omega)

  xnorm; xsimp

include hH hp in
theorem restA_s2 (hst : r.st = .s2) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, c1, c2, c3⟩ := hok
  have et := hS_ H hH (v := 2) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  have k3 := hC_ H hH c3

  xnorm; xsimp

include hH hp in
theorem restE_s2 (hst : r.st = .s2) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, c1, c2, c3⟩ := hok
  have et := hS_ H hH (v := 2) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  have k3 := hC_ H hH c3

  xnorm; xsimp

include hH hp in
theorem restA_s3 (hst : r.st = .s3) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, he, c1⟩ := hok
  have et := hS_ H hH (v := 3) (by omega)
  have k1 := hC_ H hH c1
  have e1 := hS_ H hH (v := 1) (by omega)

  rcases hs1 : r.sf1 with v | ⟨a, b⟩
  · by_cases hv : v < ringChar F
    · have := hS_ H hH hv; xnorm; xsimp
    · have := hH.big v (by omega); xnorm; xsimp
  · xnorm; xsimp

include hH hp in
theorem restE_s3 (hst : r.st = .s3) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, he, c1⟩ := hok
  have et := hS_ H hH (v := 3) (by omega)
  have k1 := hC_ H hH c1
  have e1 := hS_ H hH (v := 1) (by omega)

  rcases hs1 : r.sf1 with v | ⟨a, b⟩ <;> (xnorm; xsimp)

include hH hp in
theorem restA_s4 (hst : r.st = .s4) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, c1, n, hs1, he⟩ := hok
  have et := hS_ H hH (v := 4) (by omega)
  have k1 := hC_ H hH c1

  rcases lt_trichotomy (n + 1) (ringChar F) with hlt | heq1 | hgt
  · have e2 := hS_ H hH (v := n) (by omega)
    have e3 := hS_ H hH (v := n + 1) hlt
    have hne : ((n : ℕ) : F) + 1 ≠ 0 := by
      have := castLt_ne (F := F) (a := n + 1) (b := 0) hlt (by omega) (by omega)
      push_cast at this; exact this
    xnorm; xsimp
  · have e2 := hS_ H hH (v := n) (by omega)
    have e3 := hH.big (n + 1) (by omega)
    have hz : ((n : ℕ) : F) + 1 = 0 := by
      have : (((n + 1 : ℕ)) : F) = 0 := by rw [heq1]; exact ringChar.Nat.cast_ringChar
      push_cast at this; exact this
    have hz2 : -((n : ℕ) : F) - 1 = 0 := by linear_combination -hz
    clear heq1
    xnorm; xsimp
  · have e2 := hH.big n (by omega)
    have e3 := hH.big (n + 1) (by omega)
    xnorm; xsimp

include hH hp in
theorem restE_s4 (hst : r.st = .s4) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, c1, n, hs1, he⟩ := hok
  have et := hS_ H hH (v := 4) (by omega)
  have k1 := hC_ H hH c1

  rcases lt_trichotomy (n + 1) (ringChar F) with hlt | heq1 | hgt
  · have e2 := hS_ H hH (v := n) (by omega)
    have e3 := hS_ H hH (v := n + 1) hlt
    have hne : ((n : ℕ) : F) + 1 ≠ 0 := by
      have := castLt_ne (F := F) (a := n + 1) (b := 0) hlt (by omega) (by omega)
      push_cast at this; exact this
    xnorm; xsimp
  · have e2 := hS_ H hH (v := n) (by omega)
    have e3 := hH.big (n + 1) (by omega)
    have hz : ((n : ℕ) : F) + 1 = 0 := by
      have : (((n + 1 : ℕ)) : F) = 0 := by rw [heq1]; exact ringChar.Nat.cast_ringChar
      push_cast at this; exact this
    have hz2 : -((n : ℕ) : F) - 1 = 0 := by linear_combination -hz
    clear heq1
    xnorm; xsimp
  · have e2 := hH.big n (by omega)
    have e3 := hH.big (n + 1) (by omega)
    xnorm; xsimp

include hH hp in
theorem restA_s6 (hst : r.st = .s6) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hftt, he, hm, c1, c2⟩ := hok
  have et := hS_ H hH (v := 6) (by omega)
  have e1 := hS_ H hH (v := 1) (by omega)
  have k2 := hC_ H hH c2
  rcases hm with ⟨h2, hmm⟩ | ⟨h2, hmm⟩
  · rw [hmm] at c1; have k1 := hC_ H hH c1
    xnorm; xsimp
  · rw [hmm] at c1; have k1 := hC_ H hH c1
    xnorm; xsimp

include hH hp in
theorem restE_s6 (hst : r.st = .s6) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hftt, he, hm, c1, c2⟩ := hok
  have et := hS_ H hH (v := 6) (by omega)
  have e1 := hS_ H hH (v := 1) (by omega)
  have k2 := hC_ H hH c2
  rcases hm with ⟨h2, hmm⟩ | ⟨h2, hmm⟩
  · rw [hmm] at c1; have k1 := hC_ H hH c1
    xnorm; xsimp
  · rw [hmm] at c1; have k1 := hC_ H hH c1
    xnorm; xsimp

include hH hp in
theorem restA_s7 (hst : r.st = .s7) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, c1, c2⟩ := hok
  have et := hS_ H hH (v := 7) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restE_s7 (hst : r.st = .s7) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, c1, c2⟩ := hok
  have et := hS_ H hH (v := 7) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restA_s8 (hst : r.st = .s8) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, hm, c1, c2⟩ := hok
  have et := hS_ H hH (v := 8) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restE_s8 (hst : r.st = .s8) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, hm, c1, c2⟩ := hok
  have et := hS_ H hH (v := 8) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restA_s9 (hst : r.st = .s9) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, ⟨ax, hax, hfth, hsl⟩, c1, c2⟩ := hok
  have et := hS_ H hH (v := 9) (by omega)
  have e2 := hS_ H hH hax
  have k1 := hC_ H hH c1
  by_cases ha1 : ax = 1
  · subst ha1
    have hm : r.m = r.sf1 := by simpa [Noun.slot] using hsl.symm
    rw [hm] at c2; have k2 := hC_ H hH c2
    xnorm; xsimp
  · have k2 := hC_ H hH c2
    have k3 := hC_ H hH (slot_cell ax r.sf1 r.m hsl ha1)
    xnorm; xsimp

include hH hp in
theorem restE_s9 (hst : r.st = .s9) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, he, ⟨ax, hax, hfth, hsl⟩, c1, c2⟩ := hok
  have et := hS_ H hH (v := 9) (by omega)
  have e2 := hS_ H hH hax
  have k1 := hC_ H hH c1
  by_cases ha1 : ax = 1
  · subst ha1
    have hm : r.m = r.sf1 := by simpa [Noun.slot] using hsl.symm
    rw [hm] at c2; have k2 := hC_ H hH c2
    xnorm; xsimp
  · have k2 := hC_ H hH c2
    have k3 := hC_ H hH (slot_cell ax r.sf1 r.m hsl ha1)
    xnorm; xsimp

include hH hp in
theorem restA_cons (hst : r.st = .cons) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨c0, hf, he, c1⟩ := hok
  have k0 := hC_ H hH c0
  have k1 := hC_ H hH c1

  xnorm; xsimp

include hH hp in
theorem restE_cons (hst : r.st = .cons) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨c0, hf, he, c1⟩ := hok
  have k0 := hC_ H hH c0
  have k1 := hC_ H hH c1

  xnorm; xsimp

include hH hp in
theorem restA_s10 (hst : r.st = .s10) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, ⟨a, ha, hftth, hed⟩, c1, c2⟩ := hok
  have et := hS_ H hH (v := 10) (by omega)
  have e2 := hS_ H hH ha
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  by_cases ha1 : a = 1
  · subst ha1
    have hee : r.e = r.sf1 := by simpa [Noun.edit] using hed.symm
    xnorm; xsimp
  · have k3 := hC_ H hH (edit_cell a hed ha1)
    xnorm; xsimp

include hH hp in
theorem restE_s10 (hst : r.st = .s10) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, ⟨a, ha, hftth, hed⟩, c1, c2⟩ := hok
  have et := hS_ H hH (v := 10) (by omega)
  have e2 := hS_ H hH ha
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  by_cases ha1 : a = 1
  · subst ha1
    have hee : r.e = r.sf1 := by simpa [Noun.edit] using hed.symm
    xnorm; xsimp
  · have k3 := hC_ H hH (edit_cell a hed ha1)
    xnorm; xsimp

include hH hp in
theorem restA_s10L (hst : r.st = .s10L) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, a, hfa, ha2, hap, hs1, hs2, hm, hsl1, hsl2, hft⟩ := hok
  have hx2 : 2 ≤ a ^^^ 1 := two_le_xor_one ha2
  have hxl : a ^^^ 1 ≤ a + 1 := by rw [xor_one_eq]; split <;> omega
  have e2 := hS_ H hH (v := a) (by omega)
  have e3 := hS_ H hH (v := a ^^^ 1) (by omega)
  have k1 := hC_ H hH (slot_cell _ _ _ hsl1 (by omega))
  have k2 := hC_ H hH (slot_cell _ _ _ hsl2 (by omega))
  rw [hs1] at k1; rw [hs2] at k2
  have hdm : ((a : ℕ) : F) - 2 * ((a / 2 : ℕ) : F) - ((a % 2 : ℕ) : F) = 0 := by
    have := congrArg (Nat.cast (R := F)) (Nat.div_add_mod a 2).symm
    push_cast at this; linear_combination this
  have hxo : ((a ^^^ 1 : ℕ) : F) = (a : F) + 1 - 2 * ((a % 2 : ℕ) : F) := by
    rw [xor_one_eq]
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · rw [if_pos h0, h0]; push_cast; ring
    · rw [if_neg (by omega), h1]
      have : a - 1 + 1 = a := by omega
      have h' : ((a - 1 : ℕ) : F) + 1 = (a : F) := by rw [← Nat.cast_add_one, this]
      push_cast; linear_combination h'
  have hne1 : ((a : ℕ) : F) - 1 ≠ 0 := by
    have := castLt_ne (F := F) (a := a) (b := 1) (by omega) (by omega) (by omega)
    intro h; apply this; push_cast; linear_combination h
  xnorm; xsimp
  all_goals ring

include hH hp in
theorem restE_s10L (hst : r.st = .s10L) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, a, hfa, ha2, hap, hs1, hs2, hm, hsl1, hsl2, hft⟩ := hok
  have hx2 : 2 ≤ a ^^^ 1 := two_le_xor_one ha2
  have hxl : a ^^^ 1 ≤ a + 1 := by rw [xor_one_eq]; split <;> omega
  have e2 := hS_ H hH (v := a) (by omega)
  have e3 := hS_ H hH (v := a ^^^ 1) (by omega)
  have k1 := hC_ H hH (slot_cell _ _ _ hsl1 (by omega))
  have k2 := hC_ H hH (slot_cell _ _ _ hsl2 (by omega))
  rw [hs1] at k1; rw [hs2] at k2
  have hdm : ((a : ℕ) : F) - 2 * ((a / 2 : ℕ) : F) - ((a % 2 : ℕ) : F) = 0 := by
    have := congrArg (Nat.cast (R := F)) (Nat.div_add_mod a 2).symm
    push_cast at this; linear_combination this
  have hxo : ((a ^^^ 1 : ℕ) : F) = (a : F) + 1 - 2 * ((a % 2 : ℕ) : F) := by
    rw [xor_one_eq]
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · rw [if_pos h0, h0]; push_cast; ring
    · rw [if_neg (by omega), h1]
      have : a - 1 + 1 = a := by omega
      have h' : ((a - 1 : ℕ) : F) + 1 = (a : F) := by rw [← Nat.cast_add_one, this]
      push_cast; linear_combination h'
  have hne1 : ((a : ℕ) : F) - 1 ≠ 0 := by
    have := castLt_ne (F := F) (a := a) (b := 1) (by omega) (by omega) (by omega)
    intro h; apply this; push_cast; linear_combination h
  xnorm; xsimp

include hH hp in
theorem restA_s10T (hst : r.st = .s10T) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf⟩ := hok
  have e1 := hS_ H hH (v := 1) (by omega)

  xnorm; xsimp

include hH hp in
theorem restE_s10T (hst : r.st = .s10T) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf⟩ := hok
  have e1 := hS_ H hH (v := 1) (by omega)

  xnorm; xsimp

include hH hp in
theorem restA_s11s (hst : r.st = .s11s) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, ⟨b, hb⟩, c1⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have k1 := hC_ H hH c1
  by_cases hbp : b < ringChar F
  · have e2 := hS_ H hH hbp
    xnorm; xsimp
  · have e2 := hH.big b (by omega)
    xnorm; xsimp

include hH hp in
theorem restE_s11s (hst : r.st = .s11s) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, ⟨b, hb⟩, c1⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have k1 := hC_ H hH c1
  by_cases hbp : b < ringChar F
  · have e2 := hS_ H hH hbp
    xnorm; xsimp
  · have e2 := hH.big b (by omega)
    xnorm; xsimp

include hH hp in
theorem restA_s11d (hst : r.st = .s11d) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, c1, c2⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restE_s11d (hst : r.st = .s11d) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, c1, c2⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2

  xnorm; xsimp

include hH hp in
theorem restA_s11j (hst : r.st = .s11j) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, ⟨hwp, hftth⟩, ⟨id, hid, hsf1⟩, c1⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have e2 := hS_ H hH hwp
  have e3 := hS_ H hH hid
  have k1 := hC_ H hH c1

  xnorm; xsimp

include hH hp in
theorem restE_s11j (hst : r.st = .s11j) (hok : RowOKX (ringChar F) r) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  obtain ⟨hfh, hf, hft, hfth, ⟨hwp, hftth⟩, ⟨id, hid, hsf1⟩, c1⟩ := hok
  have et := hS_ H hH (v := 11) (by omega)
  have e2 := hS_ H hH hwp
  have e3 := hS_ H hH hid
  have k1 := hC_ H hH c1

  xnorm; xsimp

set_option maxHeartbeats 1000000 in
include hH hp in
theorem restA_s5 (hst : r.st = .s5) (hok : RowOKX (ringChar F) r)
    (hpair : isPair H r → PairOK (F := F) (pd r)) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  have et := hS_ H hH (v := 5) (by omega)
  have e1 := hS_ H hH (v := 1) (by omega)
  have hn1 : (1 : F) - 2 + 1 = 0 := by ring
  obtain ⟨hfh, hf, hft, c1, c2, he, hx1, hx2, hm, hax⟩ := hok
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  rcases hpd : pd r with ⟨a2, ⟨l1k, l1v⟩, ⟨l2k, l2v⟩⟩
  by_cases hd : r.sf1 = r.sf2
  · have he' : r.e = .atom 0 := by rw [he]; simp [Noun.tis, hd]
    clear he hx1 hx2
    xnorm; xsimp
  · obtain ⟨hnc, hne, hz, hpn⟩ := fdN_spec _ _ hd
    have he' : r.e = .atom 1 := by rw [he]; simp [Noun.tis, hd]
    clear he
    rw [← hx1, ← hx2] at hnc hne hz
    have hPair : isPair H r → PairOK (F := F) (pd r) := hpair
    rw [hpd] at hPair
    simp only [isPair, hst, he', true_and, PairOK] at hPair
    by_cases hp0 : (fdN r.sf1 r.sf2).1 = []
    · have hm1 : r.m = .atom 1 := by rw [hm, hp0]; rfl
      obtain ⟨q1, q2⟩ := hz hp0
      clear hm hax hx1 hx2 hpn hz
      rw [q1, q2] at hne hnc hPair
      rcases kind3 H hH r.sf1 with h1 | h1 | h1 <;> rcases kind3 H hH r.sf2 with h2 | h2 | h2
      · obtain ⟨u, hu, hu1, hu2⟩ := small_of_k0 H hH h1
        obtain ⟨u', hu', hu1', hu2'⟩ := small_of_k0 H hH h2
        have hw : ((u : ℕ) : F) - ((u' : ℕ) : F) ≠ 0 :=
          sub_ne_zero.mpr (castLt_ne hu hu' (fun h => hne (by rw [hu1, hu1', h])))
        rw [hu1] at hu2; rw [hu1'] at hu2'
        xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · exact absurd ⟨cell_of_k1 H hH h1, cell_of_k1 H hH h2⟩ hnc
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · obtain ⟨hl1, hl2, hl12, hl0⟩ := hPair ⟨h1, h2⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with hk1 | hk1 <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl2 with hk2 | hk2
        · have hl0' := sub_ne_zero.mpr (hl0 hk1 hk2)
          xnorm; xsimp
        · xnorm; xsimp
        · xnorm; xsimp
        · exact absurd ⟨hk1, hk2⟩ hl12
    · have hax1 : axisOfPath (fdN r.sf1 r.sf2).1 ≠ 1 := by
        have := two_le_axisOfPath hp0; omega
      have em := hS_ H hH hax
      obtain ⟨cs1, cs2⟩ := hpn hp0
      have ks1 := hC_ H hH cs1
      have ks2 := hC_ H hH cs2
      clear hx1 hx2 hz hpn
      generalize axisOfPath (fdN r.sf1 r.sf2).1 = A at hm hax hax1 em
      clear hp0
      rcases kind3 H hH r.ftth with h1 | h1 | h1 <;> rcases kind3 H hH r.fttt with h2 | h2 | h2
      · obtain ⟨u, hu, hu1, hu2⟩ := small_of_k0 H hH h1
        obtain ⟨u', hu', hu1', hu2'⟩ := small_of_k0 H hH h2
        have hw : ((u : ℕ) : F) - ((u' : ℕ) : F) ≠ 0 :=
          sub_ne_zero.mpr (castLt_ne hu hu' (fun h => hne (by rw [hu1, hu1', h])))
        rw [hu1] at hu2; rw [hu1'] at hu2'
        xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · exact absurd ⟨cell_of_k1 H hH h1, cell_of_k1 H hH h2⟩ hnc
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · obtain ⟨hl1, hl2, hl12, hl0⟩ := hPair ⟨h1, h2⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with hk1 | hk1 <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl2 with hk2 | hk2
        · have hl0' := sub_ne_zero.mpr (hl0 hk1 hk2)
          xnorm; xsimp
        · xnorm; xsimp
        · xnorm; xsimp
        · exact absurd ⟨hk1, hk2⟩ hl12

set_option maxHeartbeats 1000000 in
include hH hp in
theorem restE_s5 (hst : r.st = .s5) (hok : RowOKX (ringChar F) r)
    (hpair : isPair H r → PairOK (F := F) (pd r)) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [RowOKX, hst] at hok
  have hc := hH.cell
  have e0 := hS_ H hH (v := 0) (by omega)
  have et := hS_ H hH (v := 5) (by omega)
  have e1 := hS_ H hH (v := 1) (by omega)
  have hn1 : (1 : F) - 2 + 1 = 0 := by ring
  obtain ⟨hfh, hf, hft, c1, c2, he, hx1, hx2, hm, hax⟩ := hok
  have k1 := hC_ H hH c1
  have k2 := hC_ H hH c2
  rcases hpd : pd r with ⟨a2, ⟨l1k, l1v⟩, ⟨l2k, l2v⟩⟩
  by_cases hd : r.sf1 = r.sf2
  · have he' : r.e = .atom 0 := by rw [he]; simp [Noun.tis, hd]
    clear he hx1 hx2
    xnorm; xsimp
  · obtain ⟨hnc, hne, hz, hpn⟩ := fdN_spec _ _ hd
    have he' : r.e = .atom 1 := by rw [he]; simp [Noun.tis, hd]
    clear he
    rw [← hx1, ← hx2] at hnc hne hz
    have hPair : isPair H r → PairOK (F := F) (pd r) := hpair
    rw [hpd] at hPair
    simp only [isPair, hst, he', true_and, PairOK] at hPair
    by_cases hp0 : (fdN r.sf1 r.sf2).1 = []
    · have hm1 : r.m = .atom 1 := by rw [hm, hp0]; rfl
      obtain ⟨q1, q2⟩ := hz hp0
      clear hm hax hx1 hx2 hpn hz
      rw [q1, q2] at hne hnc hPair
      rcases kind3 H hH r.sf1 with h1 | h1 | h1 <;> rcases kind3 H hH r.sf2 with h2 | h2 | h2
      · obtain ⟨u, hu, hu1, hu2⟩ := small_of_k0 H hH h1
        obtain ⟨u', hu', hu1', hu2'⟩ := small_of_k0 H hH h2
        have hw : ((u : ℕ) : F) - ((u' : ℕ) : F) ≠ 0 :=
          sub_ne_zero.mpr (castLt_ne hu hu' (fun h => hne (by rw [hu1, hu1', h])))
        rw [hu1] at hu2; rw [hu1'] at hu2'
        xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · exact absurd ⟨cell_of_k1 H hH h1, cell_of_k1 H hH h2⟩ hnc
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · obtain ⟨hl1, hl2, hl12, hl0⟩ := hPair ⟨h1, h2⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with hk1 | hk1 <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl2 with hk2 | hk2
        · have hl0' := sub_ne_zero.mpr (hl0 hk1 hk2)
          xnorm; xsimp
        · xnorm; xsimp
        · xnorm; xsimp
        · exact absurd ⟨hk1, hk2⟩ hl12
    · have hax1 : axisOfPath (fdN r.sf1 r.sf2).1 ≠ 1 := by
        have := two_le_axisOfPath hp0; omega
      have em := hS_ H hH hax
      obtain ⟨cs1, cs2⟩ := hpn hp0
      have ks1 := hC_ H hH cs1
      have ks2 := hC_ H hH cs2
      clear hx1 hx2 hz hpn
      generalize axisOfPath (fdN r.sf1 r.sf2).1 = A at hm hax hax1 em
      clear hp0
      rcases kind3 H hH r.ftth with h1 | h1 | h1 <;> rcases kind3 H hH r.fttt with h2 | h2 | h2
      · obtain ⟨u, hu, hu1, hu2⟩ := small_of_k0 H hH h1
        obtain ⟨u', hu', hu1', hu2'⟩ := small_of_k0 H hH h2
        have hw : ((u : ℕ) : F) - ((u' : ℕ) : F) ≠ 0 :=
          sub_ne_zero.mpr (castLt_ne hu hu' (fun h => hne (by rw [hu1, hu1', h])))
        rw [hu1] at hu2; rw [hu1'] at hu2'
        xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · exact absurd ⟨cell_of_k1 H hH h1, cell_of_k1 H hH h2⟩ hnc
      · xnorm; xsimp
      · xnorm; xsimp
      · xnorm; xsimp
      · obtain ⟨hl1, hl2, hl12, hl0⟩ := hPair ⟨h1, h2⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with hk1 | hk1 <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl2 with hk2 | hk2
        · have hl0' := sub_ne_zero.mpr (hl0 hk1 hk2)
          xnorm; xsimp
        · xnorm; xsimp
        · xnorm; xsimp
        · exact absurd ⟨hk1, hk2⟩ hl12

end States

/-! ## 6. Assembly: one-hot, the claim publics, every arithmetic and equality gate -/

section Assemble
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (r : RowNX) (fst lst : F) (pub : ℕ → F)

theorem bool01 {x : F} (h : x = 0 ∨ x = 1) : x * (x - 1) = 0 := by
  rcases h with rfl | rfl <;> simp

theorem oneHot_hold (hpair : isPair H r → PairOK (F := F) (pd r)) :
    ∀ g ∈ (oneHotG : List (CoeffExpr ℚ)), evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  have hst : ∀ j < 17, (hEnvX H pd r fst lst pub).trace j = 0 ∨ (hEnvX H pd r fst lst pub).trace j = 1 := by
    intro j hj
    show colX H pd r fst lst j = 0 ∨ colX H pd r fst lst j = 1
    rw [colX_st H pd r fst lst j hj]; split <;> simp
  have hz : cZ1 (F := F) r = 0 ∨ cZ1 (F := F) r = 1 := by
    unfold cZ1; split <;> (try split) <;> simp
  have hb : cB (F := F) r = 0 ∨ cB (F := F) r = 1 := by
    unfold cB; split
    · split <;> simp
    · split <;> simp
    · rcases Nat.mod_two_eq_zero_or_one (chainAxis r.f) with h | h <;> simp [h, Nat.cast_one]
    · simp
  have hf : cFast (F := F) H r = 0 ∨ cFast (F := F) H r = 1 := by
    unfold cFast; split
    · split <;> simp
    · simp
  have hl : ∀ j, j = 0 ∨ j = 2 → cL (F := F) H pd r j = 0 ∨ cL (F := F) H pd r j = 1 := by
    intro j hj
    unfold cL
    split
    · rename_i hp
      obtain ⟨h1, h2, -, -⟩ := hpair hp
      rcases hj with rfl | rfl
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h <;> simp [h, Nat.cast_one]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h <;> simp [h, Nat.cast_one]
    · simp
  simp only [oneHotG, List.forall_mem_append, List.forall_mem_map, List.mem_range, List.forall_mem_cons,
    List.forall_mem_nil, and_true]
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [boolG, cc, evalQX, Rat.cast_one]; exact bool01 (hst j hj)
  · have := selS_range17 H pd r fst lst pub
    simp only [evalQX, Rat.cast_one] at this ⊢; rw [this]; simp
  · simp only [boolG, cc, evalQX, Rat.cast_one, z1X, hEnvX, cx19]; exact bool01 hz
  · simp only [boolG, cc, evalQX, Rat.cast_one, betaX, hEnvX, cx21]; exact bool01 hb
  · simp only [boolG, cc, evalQX, Rat.cast_one, fastX, hEnvX, cx61]; exact bool01 hf
  · simp only [boolG, cc, evalQX, Rat.cast_one, xL1, hEnvX, cx65]; exact bool01 (hl 0 (Or.inl rfl))
  · simp only [boolG, cc, evalQX, Rat.cast_one, xL2, hEnvX, cx67]
    exact ⟨bool01 (hl 2 (Or.inr rfl)), fun x hx => absurd hx List.not_mem_nil⟩

/-- The claim publics: the first row's `s f e` handles. -/
def PubOK (r : RowNX) (fst : F) (pub : ℕ → F) : Prop :=
  fst = 0 ∨ (pub 0 = hk H r.s ∧ pub 1 = hv H r.s ∧ pub 2 = hk H r.f ∧ pub 3 = hv H r.f ∧
    pub 4 = hk H r.e ∧ pub 5 = hv H r.e)

theorem claim_hold (hpub : PubOK H r fst pub) :
    ∀ g ∈ (claimEq : List (EqG ℚ)).map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  simp only [claimEq, hpub, ChipH.hpub, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.forall_mem_nil, and_true]
  rcases hpub with h0 | ⟨q0, q1, q2, q3, q4, q5⟩
  · simp [EqG.gate, Opnd.expr, evalQX, cc, hEnvX, firstX, xS, xF, xE, hdX, h0]
  · simp [EqG.gate, Opnd.expr, evalQX, cc, hEnvX, firstX, xS, xF, xE, hdX, q0, q1, q2, q3, q4, q5]

variable (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)

include hH hp in
theorem restA_hold (hok : RowOKX (ringChar F) r) (hpair : isPair H r → PairOK (F := F) (pd r)) :
    ∀ g ∈ restA, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  cases hst : r.st
  · exact restA_s0 H pd r fst lst pub hH hp hst hok
  · exact restA_s1 H pd r fst lst pub hH hp hst hok
  · exact restA_s2 H pd r fst lst pub hH hp hst hok
  · exact restA_s3 H pd r fst lst pub hH hp hst hok
  · exact restA_s4 H pd r fst lst pub hH hp hst hok
  · exact restA_s5 H pd r fst lst pub hH hp hst hok hpair
  · exact restA_s6 H pd r fst lst pub hH hp hst hok
  · exact restA_s7 H pd r fst lst pub hH hp hst hok
  · exact restA_s8 H pd r fst lst pub hH hp hst hok
  · exact restA_s9 H pd r fst lst pub hH hp hst hok
  · exact restA_cons H pd r fst lst pub hH hp hst hok
  · exact restA_s10 H pd r fst lst pub hH hp hst hok
  · exact restA_s10L H pd r fst lst pub hH hp hst hok
  · exact restA_s10T H pd r fst lst pub hH hp hst hok
  · exact restA_s11s H pd r fst lst pub hH hp hst hok
  · exact restA_s11d H pd r fst lst pub hH hp hst hok
  · exact restA_s11j H pd r fst lst pub hH hp hst hok

include hH hp in
theorem restE_hold (hok : RowOKX (ringChar F) r) (hpair : isPair H r → PairOK (F := F) (pd r)) :
    ∀ g ∈ restE.map EqG.gate, evalQX g (hEnvX H pd r fst lst pub) = 0 := by
  cases hst : r.st
  · exact restE_s0 H pd r fst lst pub hH hp hst hok
  · exact restE_s1 H pd r fst lst pub hH hp hst hok
  · exact restE_s2 H pd r fst lst pub hH hp hst hok
  · exact restE_s3 H pd r fst lst pub hH hp hst hok
  · exact restE_s4 H pd r fst lst pub hH hp hst hok
  · exact restE_s5 H pd r fst lst pub hH hp hst hok hpair
  · exact restE_s6 H pd r fst lst pub hH hp hst hok
  · exact restE_s7 H pd r fst lst pub hH hp hst hok
  · exact restE_s8 H pd r fst lst pub hH hp hst hok
  · exact restE_s9 H pd r fst lst pub hH hp hst hok
  · exact restE_cons H pd r fst lst pub hH hp hst hok
  · exact restE_s10 H pd r fst lst pub hH hp hst hok
  · exact restE_s10L H pd r fst lst pub hH hp hst hok
  · exact restE_s10T H pd r fst lst pub hH hp hst hok
  · exact restE_s11s H pd r fst lst pub hH hp hst hok
  · exact restE_s11d H pd r fst lst pub hH hp hst hok
  · exact restE_s11j H pd r fst lst pub hH hp hst hok

include hH hp in
/-- **Every arithmetic and equality base gate of `computeChipVCLHX` vanishes at an honest row.** -/
theorem arith_eq_hold (hok : RowOKX (ringChar F) r) (hpair : isPair H r → PairOK (F := F) (pd r))
    (hpub : PubOK H r fst pub) :
    (∀ g ∈ (arithGatesX : List (CoeffExpr ℚ)), evalQX g (hEnvX H pd r fst lst pub) = 0) ∧
      (∀ g ∈ (eqGatesX : List (EqG ℚ)), evalQX g.gate (hEnvX H pd r fst lst pub) = 0) := by
  refine ⟨?_, ?_⟩
  · rw [arithGatesX_split]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact oneHot_hold H pd r fst lst pub hpair g hg
      · exact kind_hold H pd r fst lst pub hH g hg
    · exact restA_hold H pd r fst lst pub hH hp hok hpair g hg
  · rw [eqGatesX_split]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact restE_hold H pd r fst lst pub hH hp hok hpair _ (List.mem_map_of_mem hg)
    · exact claim_hold H pd r fst lst pub hpub _ (List.mem_map_of_mem hg)

end Assemble

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
