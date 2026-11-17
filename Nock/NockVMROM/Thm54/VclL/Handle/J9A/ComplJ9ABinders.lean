/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABinders.lean

* `AxRowX9A` / **`ProgAxOK9A`** (replaces `hax`): on `s0` / `s10` / `s10L` rows the axis atom is either the
    J-9 B-admissible `< p` (resp. `a + 1 < p`) OR within the cap (served by the axis chip: big axes `≥ p` through
    the atom table, field axes `[2^62, p)` through the split chip).  Every other row condition (`s9`, `s11j`) is
    J-9 B's verbatim (the axis chip serves op 0 and op 10 only).
  * **`progAxOK9A_of_progAxOK`**: `ProgAxOK p t → ProgAxOK9A p t`.
  * `routedX` / `walkReads9` / **`WalkDepthOK9A`** (replaces `hwalk`): the depth bound on the reads the J-9 A
    generator still routes through the J-9 B walk; an `s0` / `s10` / `s10L` read at an axis `≥ 2^62` is routed to
    the axis chip (segment chains, axis `< 2^33`) and is exempt.  The `s9` and `s5` reads are kept.
  * **`walkDepthOK9A_of_walkDepthOK`**: `WalkDepthOK (pathReads rows) → WalkDepthOK9A rows`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (AxRowX ProgAxOK)

/-! ## 1. `hax` → `ProgAxOK9A` -/

/-- **The limb cap**: at most 62 limbs of `2^32`. -/
def AxCap (a : ℕ) : Prop := (Nock.Atoms.limbs a).length ≤ 62

/-- **The J-9 A axis condition at one row**: J-9 B's `AxRowX`, with the op-0 / op-10 axis (and the op-10 chain
level) either J-9 B-admissible or within the cap. -/
def AxRowX9A (p : ℕ) (r : RowNX) : Prop :=
  match r.st with
  | .s0 => ∀ ax, r.ft = .atom ax → ax < p ∨ AxCap ax
  | .s9 => ∀ ax, r.fth = .atom ax → ax < p
  | .s10 => ∀ a, r.ftth = .atom a → a < p ∨ AxCap a
  | .s10L => ∀ a, r.f = .atom a → a + 1 < p ∨ AxCap a
  | .s11j => (∀ id, r.ftth = .atom id → id < p) ∧ (∀ id, r.sf1 = .atom id → id < p)
  | _ => True

/-- **Binder `hax9` (replaces `hax`)**: every row of the generated tree satisfies `AxRowX9A p`. -/
def ProgAxOK9A (p : ℕ) (t : NTree SkelX) : Prop := ∀ u, InTree t u → AxRowX9A p (rowOfSkelX u.label)

theorem axRowX9A_of_axRowX {p : ℕ} {r : RowNX} (h : AxRowX p r) : AxRowX9A p r := by
  unfold AxRowX at h
  unfold AxRowX9A
  cases hst : r.st <;> simp only [hst] at h ⊢
  · exact fun ax hax => Or.inl (h ax hax)
  · exact h
  · exact fun a ha => Or.inl (h a ha)
  · exact fun a ha => Or.inl (h a ha)
  · exact h

/-- **`hax → hax9`**: the J-9 A binder is implied by J-9 B's. -/
theorem progAxOK9A_of_progAxOK {p : ℕ} {t : NTree SkelX} (h : ProgAxOK p t) : ProgAxOK9A p t :=
  fun u hu => axRowX9A_of_axRowX (h u hu)

/-- Non-vacuity: an op-0 row with a big axis within the cap meets `AxRowX9A` and fails `AxRowX`. -/
theorem progAxOK9A_big_s0 {p : ℕ} {r : RowNX} (hst : r.st = .s0) {ax : ℕ} (hft : r.ft = .atom ax)
    (hp : p ≤ ax) (hcap : AxCap ax) : AxRowX9A p r ∧ ¬ AxRowX p r := by
  refine ⟨?_, ?_⟩
  · unfold AxRowX9A; rw [hst]
    intro a ha; rw [hft] at ha; cases ha; exact Or.inr hcap
  · unfold AxRowX; rw [hst]
    intro h; exact absurd (h ax hft) (by omega)

/-! ## 2. `hwalk` → `WalkDepthOK9A` -/

/-- A read of an `s0` / `s10` / `s10L` row at an axis `≥ 2^62` is routed to the axis chip. -/
def routedX (r : RowNX) (ax : ℕ) : Bool :=
  (decide (r.st = .s0) || decide (r.st = .s10) || decide (r.st = .s10L)) && decide (2 ^ 62 ≤ ax)

/-- **The reads the J-9 A generator routes through the J-9 B walk**: J-8's `pathReads`, minus the routed ones. -/
def walkReads9 (rows : Array RowNX) : List (Noun × ℕ) :=
  (rows.toList.flatMap fun r =>
    ((consEntriesX r).filter fun x => !routedX r x.2.1).map fun x => (x.1, x.2.1)).filter fun q => 2 ≤ q.2

/-- **Binder `hwalk9` (replaces `hwalk`)**: depth `≤ 61` on the reads still routed through the J-9 B walk. -/
def WalkDepthOK9A (rows : Array RowNX) : Prop := ComplJ8Walk.WalkDepthOK (walkReads9 rows)

theorem walkReads9_sub (rows : Array RowNX) : ∀ x ∈ walkReads9 rows, x ∈ Nock.V1J8.Gen.pathReads rows := by
  intro x hx
  simp only [walkReads9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨r, hr, y, ⟨hy, _⟩, rfl⟩, h2⟩ := hx
  simp only [Nock.V1J8.Gen.pathReads, List.mem_filter, List.mem_flatMap, List.mem_map]
  exact ⟨⟨r, hr, y, hy, rfl⟩, h2⟩

theorem walkDepthOK_mono {l l' : List (Noun × ℕ)} (hsub : ∀ x ∈ l', x ∈ l) (h : ComplJ8Walk.WalkDepthOK l) :
    ComplJ8Walk.WalkDepthOK l' := by
  intro x hx
  apply h x
  simp only [pathReads, List.mem_dedup, List.mem_filter] at hx ⊢
  exact ⟨hsub x hx.1, hx.2⟩

/-- **`hwalk → hwalk9`**: the J-9 A walk binder is implied by J-9 B's (`hwalk : WalkDepthOK (DD).reads`, and
`(DD).reads = pathReads (rowsOfT t)` by definition of `j8DataOf`). -/
theorem walkDepthOK9A_of_walkDepthOK {rows : Array RowNX}
    (h : ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads rows)) : WalkDepthOK9A rows :=
  walkDepthOK_mono (walkReads9_sub rows) h

/-- Non-vacuity: a lone op-0 row at a field / big axis (`≥ 2^62`) has no J-9 B walk read. -/
theorem walkReads9_routed_s0 {r : RowNX} (hst : r.st = .s0) {ax : ℕ} (hft : r.ft = .atom ax)
    (hax : 2 ^ 62 ≤ ax) : walkReads9 #[r] = [] := by
  simp [walkReads9, consEntriesX, hst, hft, routedX, atomVal, hax]
  omega

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
#print axioms progAxOK9A_of_progAxOK
#print axioms progAxOK9A_big_s0
#print axioms walkDepthOK9A_of_walkDepthOK
end Axioms
