/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestRowX.lean

  **`RowOKX` on every row of a generated
  tree.**  Additive: a NEW module.

  * `SmallX p r` — the run's resource bounds at one row (the small-atom bounds the base gates need:
    the op-0 / op-9 axes, the op-10 edit axis, the chain level `a + 1`, the jet id, the op-5
    first-difference axis, all `< p`).
  * `genX_isCell` — a generated run has a cell formula.
  * **`rowOKX_of_genX`** — every node `u` of a `genX R n s f` tree satisfies `RowOKX p` at its honest
    row, given `SmallX p` there.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified
open Nock.NockVMROM.Thm54.VclL (hdN tlN)
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (RowOKX)

/-- **The run's small-atom bounds at one row** (the resource binders of the base gates). -/
def SmallX (p : ℕ) (r : RowNX) : Prop :=
  match r.st with
  | .s0 => ∀ ax, r.ft = .atom ax → ax < p
  | .s5 => axisOfPath (fdN r.sf1 r.sf2).1 < p
  | .s9 => ∀ ax, r.fth = .atom ax → ax < p
  | .s10 => ∀ a, r.ftth = .atom a → a < p
  | .s10L => ∀ a, r.f = .atom a → a + 1 < p
  | .s11j => (∀ id, r.ftth = .atom id → id < p) ∧ (∀ id, r.sf1 = .atom id → id < p)
  | _ => True

/-- **A generated run has a cell formula.** -/
theorem genX_isCell {R : Registry} : ∀ {n : ℕ} {s f : Noun} {x : NTree SkelX × Noun},
    genX R n s f = some x → f.isCell = true
  | 0, _, _, _, h => by simp [genComputeSkeletonX] at h
  | _ + 1, _, .atom _, _, h => by simp [genComputeSkeletonX] at h
  | _ + 1, _, .cell _ _, _, _ => rfl

open Lean Elab Tactic Meta in
/-- For every hypothesis `genComputeSkeletonX R n s f = some x`, add `f.isCell = true`. -/
elab "gen_cells" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, lhs, _) := ty.eq? then
      if lhs.isAppOf ``genComputeSkeletonX then
        try
          let pr ← mkAppM ``genX_isCell #[d.toExpr]
          liftMetaTactic fun g => do
            let g ← g.assert `hcell (← inferType pr) pr
            let (_, g) ← g.intro1P
            return [g]
        catch _ => pure ()
        try
          let pr ← mkAppM ``genX_label #[d.toExpr]
          liftMetaTactic fun g => do
            let g ← g.assert `hlab (← inferType pr) pr
            let (_, g) ← g.intro1P
            return [g]
        catch _ => pure ()

set_option hygiene false in
macro "fin_row" : tactic => `(tactic| (
  simp only [mkX_label, rowOfSkelX, RowOKX, SmallX, kidE, kidF, SkelX.row, List.map_cons,
    List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some,
    Option.getD_some] at hs ⊢
  simp_all [hdN, tlN]))

/-- **A generated row satisfies `RowOKX`** under the run's small-atom bounds there. -/
theorem genX_rowOK {R : Registry} {p n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    SmallX p (rowOfSkelX t.label) → RowOKX p (rowOfSkelX t.label) := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case5 n s ax r' hs' =>
    simp only [genComputeSkeletonX, hs', Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    cases b with
    | cell b1 b2 => simp [jetHit] at hj
    | atom b =>
      obtain ⟨id, j, hb, rfl, -⟩ := jetHit_spec hj
      obtain rfl : b = wildTag := by injection hb
      fin_row
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hs
    gen_cells
    fin_row

/-- **A chain row satisfies `RowOKX`** under its level bound (`s10L`: `a + 1 < p`). -/
theorem chain_rowOK {p : ℕ} {u : NTree SkelX} (hu : ChainNode u) :
    SmallX p (rowOfSkelX u.label) → RowOKX p (rowOfSkelX u.label) := by
  obtain ⟨old, e, k, a, rfl, hc, h1, h2⟩ := hu
  cases k with
  | zero =>
    obtain rfl : a = 1 := by omega
    simp [genChainF, rowOfSkelX, RowOKX, SmallX]
  | succ k =>
    by_cases ha : 2 ≤ a
    · obtain ⟨x, hxo, hxe⟩ := hc 0 (by simpa using ha)
      simp only [pow_zero, Nat.div_one] at hxo hxe
      simp [genChainF, ha, rowOfSkelX, RowOKX, SmallX, chainAxis, sibX, hxo, hxe]
    · obtain rfl : a = 1 := by omega
      simp [genChainF, rowOfSkelX, RowOKX, SmallX]

/-- **`RowOKX` on every row of a generated tree** (HC2 step 1), given the run's small-atom bounds
`SmallX p` at that row. -/
theorem rowOKX_of_genX {R : Registry} {p n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u)
    (hs : SmallX p (rowOfSkelX u.label)) : RowOKX p (rowOfSkelX u.label) := by
  rcases genX_inTree h hu with ⟨m, hm⟩ | hc
  · exact genX_rowOK hm hs
  · exact chain_rowOK hc hs

end Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX
