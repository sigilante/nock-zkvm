/-
  Nock/Edit/GenXRows.lean

  **The honest noun rows, demand, walk reads, axes and the
  atom digitisation closure of the generator twin.**

  * New states (SPEC §3.3): `s10`: `ftth = a`,
    `fttt = c`, `sf1 = new`, `sf2 = old`; `s10L` (formula the ATOM `a_k`): `sf1 = s = old`,
    `sf2 = e`, `m = a_k xor 1`, `ftth = fttt = ` the sibling; `s11s`: `sf1` = body value;
    `s11d`: `ftth = b`, `fttt = clue`, `sf1` = clue value, `sf2` = body value; `s11j`: as `s11d`
    with no body child.
  * `RowNX.SemN R` — what the chip's gates need of a row, at ℕ-level (big atoms native).
    `genX_rowSem` / `inTree_rowSem`: EVERY node of a generated tree satisfies it.
  * `consEntriesX_sound`: every entry of a `SemN` row is a defined slot read at axis `≥ 2`.
  * `handleNounsX`, `demandHX` — the six root handles per row; the walk reads as `preads`.
  * `honestAxX` — the axis column with the edit axes: OP0 / OP9 as `honestAx`, `s10` the edit
    axis `a`, `s10L` `a_k / 2` (its `vC`).  `honestAxX_s10`: `#[a new old] = e` with `1 ≤ a`.
  * `demandA` / `atomTable` — the atom digitisation closure: every big leaf (`≥ p`) of every
    handle, its canonical limbs (A-1).  `mem_demandA`, `atomTable_canonical`; `incRecX`
    (the slow OP4 record, SPEC §3.3) with `incRecX_carry` (A-1's carry chain is the honest one)
    and `incRecX_mem`; `bigPairX` (the OP5 big ≠ big second pair, the limb first difference
    `lfd`) with `lfd_ne`.
-/
import Nock.Edit.GenX
import Nock.Atoms.Carry
import Nock.NockVMROM.Thm54.VclL.Handle.PathConsH

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.Edit.GenX

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit
open Nock.NockVMROM.Thm54.VclL (closureOf cellsOf hdN tlN mem_closureOf mem_cellsOf_trans Demand)
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath atomVal fdN_slot two_le_axisOfPath fdN_spec
  hdN_cells tlN_cells fdN_cells PEnt)

/-! ## §1 The noun row -/

/-- **The twelve handle nouns of one row** at the extended ISA. -/
structure RowNX where
  st : StateX
  s : Noun
  f : Noun
  e : Noun
  fh : Noun := .atom 0
  ft : Noun := .atom 0
  fth : Noun := .atom 0
  ftt : Noun := .atom 0
  ftth : Noun := .atom 0
  fttt : Noun := .atom 0
  sf1 : Noun := .atom 0
  sf2 : Noun := .atom 0
  m : Noun := .atom 0
deriving DecidableEq, Repr

/-- The `i`-th child's evaluation (`atom 0` if absent). -/
def kidE (sk : SkelX) (i : ℕ) : Noun := ((sk.kids[i]?).map RowX.evaluation).getD (.atom 0)

/-- The `i`-th child's formula (`atom 0` if absent). -/
def kidF (sk : SkelX) (i : ℕ) : Noun := ((sk.kids[i]?).map RowX.formula).getD (.atom 0)

/-- The sibling noun read by a chain level `a` of `old` (`atom 0` if undefined). -/
def sibX (a : ℕ) (old : Noun) : Noun := (Noun.slot (a ^^^ 1) old).getD (.atom 0)

/-- **The honest (effective) noun row of a generated row.** -/
def rowOfSkelX (sk : SkelX) : RowNX :=
  let s := sk.subject
  let f := sk.formula
  let e := sk.evaluation
  let ft := tlN f
  let ftt := tlN ft
  let c0 := kidE sk 0
  let c1 := kidE sk 1
  match sk.state with
  | .s0 => { st := .s0, s, f, e, fh := hdN f, ft }
  | .s1 => { st := .s1, s, f, e, fh := hdN f, ft }
  | .s2 => { st := .s2, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0, sf2 := c1 }
  | .s3 => { st := .s3, s, f, e, fh := hdN f, ft, ftth := hdN c0, fttt := tlN c0, sf1 := c0 }
  | .s4 => { st := .s4, s, f, e, fh := hdN f, ft, sf1 := c0 }
  | .s5 => { st := .s5, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0, sf2 := c1,
             ftth := (fdN c0 c1).2.1, fttt := (fdN c0 c1).2.2,
             m := .atom (axisOfPath (fdN c0 c1).1) }
  | .s6 => { st := .s6, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, ftth := hdN ftt,
             fttt := tlN ftt, sf1 := c0, sf2 := c1,
             m := if c1 = .atom 0 then hdN ftt else tlN ftt }
  | .s7 => { st := .s7, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0, sf2 := c1 }
  | .s8 => { st := .s8, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0, sf2 := c1,
             m := .cell c1 s }
  | .s9 => { st := .s9, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0, sf2 := c1,
             m := kidF sk 1 }
  | .cons => { st := .cons, s, f, e, fh := hdN f, ft, sf1 := c0, sf2 := c1 }
  | .s10 => { st := .s10, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, ftth := hdN (hdN ft),
              fttt := tlN (hdN ft), sf1 := c0, sf2 := c1 }
  | .s10L => { st := .s10L, s, f, e, sf1 := s, sf2 := e, m := .atom (chainAxis f ^^^ 1),
               ftth := sibX (chainAxis f) s, fttt := sibX (chainAxis f) e }
  | .s10T => { st := .s10T, s, f, e }
  | .s11s => { st := .s11s, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, sf1 := c0 }
  | .s11d => { st := .s11d, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, ftth := hdN (hdN ft),
               fttt := tlN (hdN ft), sf1 := c0, sf2 := c1 }
  | .s11j => { st := .s11j, s, f, e, fh := hdN f, ft, fth := hdN ft, ftt, ftth := hdN (hdN ft),
               fttt := tlN (hdN ft), sf1 := c0 }

/-- **What the gates need of a row** (ℕ-level; SPEC §3.3). -/
def RowNX.SemN (R : Registry) (r : RowNX) : Prop :=
  match r.st with
  | .s0 => r.fh = .atom 0 ∧ r.f = .cell r.fh r.ft ∧ ∃ ax, r.ft = .atom ax ∧ Noun.slot ax r.s = some r.e
  | .s1 => r.fh = .atom 1 ∧ r.f = .cell r.fh r.ft ∧ r.e = r.ft
  | .s2 => r.fh = .atom 2 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt
  | .s3 => r.fh = .atom 3 ∧ r.f = .cell r.fh r.ft ∧ r.e = Noun.wut r.sf1
  | .s4 => r.fh = .atom 4 ∧ r.f = .cell r.fh r.ft ∧ ∃ n, r.sf1 = .atom n ∧ r.e = .atom (n + 1)
  | .s5 => r.fh = .atom 5 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.e = Noun.tis r.sf1 r.sf2
  | .s6 => r.fh = .atom 6 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.ftt = .cell r.ftth r.fttt ∧ r.e = r.sf1 ∧
      ((r.sf2 = .atom 0 ∧ r.m = r.ftth) ∨ (r.sf2 = .atom 1 ∧ r.m = r.fttt))
  | .s7 => r.fh = .atom 7 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1
  | .s8 => r.fh = .atom 8 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1 ∧
      r.m = .cell r.sf2 r.s
  | .s9 => r.fh = .atom 9 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf2 ∧
      ∃ ax, r.fth = .atom ax ∧ Noun.slot ax r.sf1 = some r.m
  | .cons => (∃ a b, r.fh = .cell a b) ∧ r.f = .cell r.fh r.ft ∧ r.e = .cell r.sf1 r.sf2
  | .s10 => r.fh = .atom 10 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧ ∃ a, r.ftth = .atom a ∧ Noun.edit a r.sf1 r.sf2 = some r.e
  | .s10L => ∃ a, r.f = .atom a ∧ 2 ≤ a ∧ r.sf1 = r.s ∧ r.sf2 = r.e ∧ r.m = .atom (a ^^^ 1) ∧
      Noun.slot (a ^^^ 1) r.sf1 = some r.ftth ∧ Noun.slot (a ^^^ 1) r.sf2 = some r.fttt ∧
      r.ftth = r.fttt
  | .s10T => r.f = .atom 1
  | .s11s => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      (∃ b, r.fth = .atom b) ∧ r.e = r.sf1
  | .s11d => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧ r.e = r.sf2
  | .s11j => r.fh = .atom 11 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.fth = .cell r.ftth r.fttt ∧
      ∃ id j, r.ftth = .atom wildTag ∧ r.sf1 = .atom id ∧ R id = some j ∧ j.c = r.ftt ∧
        j.T.rel r.s r.e

/-! ## §2 Every generated row satisfies `SemN` -/

theorem genX_rowSem {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : (rowOfSkelX t.label).SemN R := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [rowOfSkelX, RowNX.SemN, hdN, tlN]
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hd).2.2.1
    try have := (genX_label hbc).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hs).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hc).2.2.1
    try have := (genX_label hm).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hx).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hx).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hc).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hc).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hc).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hm).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hb).2.2.1
    try have := (genX_label hm).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hc).2.2.1
    try have := (genX_label harm).2.2.1
    try have := (genX_label hm).2.2.1
    have := (genX_label hm).2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hc).2.2.1
    try have := (genX_label hd).2.2.1
    try have := (genX_label he).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hcl).2.2.1
    try have := (genX_label hj).2.2.1
    obtain ⟨id, j, rfl, rfl, hj1, hj2, hj3⟩ := jetHit_spec hj
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hcl).2.2.1
    try have := (genX_label hj).2.2.1
    try have := (genX_label hB).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    try have := (genX_label hB).2.2.1
    try clear ih1
    try clear ih2
    try clear ih3
    try clear ih
    simp only [mkX_label, rowOfSkelX, RowNX.SemN, kidE, kidF, SkelX.row, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    simp_all [hdN, tlN]

/-- A chain node's row satisfies `SemN` (`s10L`: the sibling agrees; `s10T`: the atom `1`). -/
theorem chainNode_rowSem (R : Registry) {u : NTree SkelX} (hu : ChainNode u) :
    (rowOfSkelX u.label).SemN R := by
  obtain ⟨old, e, k, a, rfl, hc, h1, h2⟩ := hu
  cases k with
  | zero =>
    obtain rfl : a = 1 := by omega
    simp [genChainF, rowOfSkelX, RowNX.SemN]
  | succ k =>
    by_cases ha : 2 ≤ a
    · obtain ⟨x, hxo, hxe⟩ := hc 0 (by simpa using ha)
      simp only [pow_zero, Nat.div_one] at hxo hxe
      simp [genChainF, ha, rowOfSkelX, RowNX.SemN, chainAxis, sibX, hxo, hxe]
    · obtain rfl : a = 1 := by omega
      simp [genChainF, rowOfSkelX, RowNX.SemN]

/-- **Every node of a generated tree satisfies `SemN`.** -/
theorem inTree_rowSem {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u) :
    (rowOfSkelX u.label).SemN R := by
  rcases genX_inTree h hu with ⟨m, hm⟩ | hc
  · exact genX_rowSem hm
  · exact chainNode_rowSem R hc

/-! ## §3 Walk reads -/

def consEntriesX (r : RowNX) : List PEnt :=
  (if r.st = .s0 ∧ r.ft ≠ .atom 1 then [(r.s, atomVal r.ft, r.e)] else []) ++
  (if r.st = .s9 ∧ r.fth ≠ .atom 1 then [(r.sf1, atomVal r.fth, r.m)] else []) ++
  (if r.st = .s5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ [] then
    [(r.sf1, atomVal r.m, r.ftth), (r.sf2, atomVal r.m, r.fttt)] else []) ++
  (if r.st = .s10 ∧ r.ftth ≠ .atom 1 then [(r.e, atomVal r.ftth, r.sf1)] else []) ++
  (if r.st = .s10L then [(r.sf1, atomVal r.m, r.ftth), (r.sf2, atomVal r.m, r.fttt)] else [])

def handleNounsX (r : RowNX) : List Noun := [r.s, r.f, r.e, r.sf1, r.sf2, r.m]

/-- The twelve handles of a row. -/
def rowHandleNounsX (r : RowNX) : List Noun :=
  [r.s, r.f, r.e, r.sf1, r.sf2, r.fh, r.ft, r.fth, r.ftt, r.ftth, r.fttt, r.m]

/-- **The walk's reads** of a list of rows. -/
def walkReadsHX (rows : List SkelX) : List (Noun × ℕ) :=
  (rows.flatMap fun sk => consEntriesX (rowOfSkelX sk)).map fun x => (x.1, x.2.1)

/-- **The demand**: handle nouns as binds, no export reads, the walk reads (edit spine included:
the `s10` read and every `s10L` sibling pair are rooted at handle nouns `e`, `old`). -/
def demandHX (rows : List SkelX) : Demand :=
  ⟨rows.flatMap (fun sk => handleNounsX (rowOfSkelX sk)), [], walkReadsHX rows⟩

theorem slot_zero (n : Noun) : Noun.slot 0 n = none := by simp [Noun.slot]

theorem two_le_xor_one {a : ℕ} (ha : 2 ≤ a) : 2 ≤ a ^^^ 1 := by
  rw [xor_one_eq]; split <;> omega

/-- **Every walk read of a semantically valid generated row is a defined slot read at an axis
`≥ 2`.** -/
theorem consEntriesX_sound {R : Registry} (sk : SkelX) (hs : (rowOfSkelX sk).SemN R) :
    ∀ x ∈ consEntriesX (rowOfSkelX sk), 2 ≤ x.2.1 ∧ Noun.slot x.2.1 x.1 = some x.2.2 := by
  intro x hx
  cases hst : sk.state <;>
    simp only [rowOfSkelX, hst, RowNX.SemN, consEntriesX] at hs hx <;>
    simp at hx
  case s0 =>
    obtain ⟨hne, rfl⟩ := hx
    obtain ⟨-, -, ax, hax, hsl⟩ := hs
    rw [hax] at hne ⊢
    refine ⟨?_, by simpa [atomVal] using hsl⟩
    rcases Nat.lt_or_ge ax 2 with h | h
    · interval_cases ax
      · simp [slot_zero] at hsl
      · simp at hne
    · simpa [atomVal] using h
  case s9 =>
    obtain ⟨hne, rfl⟩ := hx
    obtain ⟨-, -, -, -, ax, hax, hsl⟩ := hs
    rw [hax] at hne ⊢
    refine ⟨?_, by simpa [atomVal] using hsl⟩
    rcases Nat.lt_or_ge ax 2 with h | h
    · interval_cases ax
      · simp [slot_zero] at hsl
      · simp at hne
    · simpa [atomVal] using h
  case s5 =>
    obtain ⟨⟨-, hne⟩, rfl | rfl⟩ := hx
    · exact ⟨by simpa [atomVal] using two_le_axisOfPath hne, by simpa [atomVal] using (fdN_slot _ _).1⟩
    · exact ⟨by simpa [atomVal] using two_le_axisOfPath hne, by simpa [atomVal] using (fdN_slot _ _).2⟩
  case s10 =>
    obtain ⟨hne, rfl⟩ := hx
    obtain ⟨-, -, -, -, a, ha, hed⟩ := hs
    rw [ha] at hne ⊢
    have h2 : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · interval_cases a
        · simp [Noun.edit] at hed
        · simp at hne
      · exact h
    exact ⟨by simpa [atomVal] using h2, by simpa [atomVal] using (chainOK_of_edit a hed).2⟩
  case s10L =>
    obtain ⟨a, ha, h2, -, -, -, hs1, hs2, -⟩ := hs
    have hca : chainAxis sk.formula = a := by rw [ha]; rfl
    rcases hx with rfl | rfl
    · simp only [atomVal, hca] at hs1 ⊢; exact ⟨two_le_xor_one h2, hs1⟩
    · simp only [atomVal, hca] at hs2 ⊢; exact ⟨two_le_xor_one h2, hs2⟩

/-- Every walk-read root is a root handle of its row (no `SemN` needed). -/
theorem consEntriesX_root (r : RowNX) : ∀ x ∈ consEntriesX r, x.1 ∈ handleNounsX r := by
  intro x hx
  simp only [consEntriesX, List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h <;> split_ifs at h <;>
    simp at h <;> rcases h with rfl | rfl <;> simp [handleNounsX]

/-! ## §4 The closure: no cell beyond `closureOf` of the handles -/

/-- `x` lies below `root` as far as cells go. -/
def Below (x root : Noun) : Prop := x.isCell = true → x ∈ cellsOf root

theorem below_self (x : Noun) : Below x x := by
  intro h; cases x with
  | atom _ => simp [Noun.isCell] at h
  | cell a b => exact Nock.NockVMROM.Thm54.VclL.mem_cellsOf_self

theorem below_atom (a : ℕ) (root : Noun) : Below (.atom a) root := by
  intro h; simp [Noun.isCell] at h

theorem below_hd {x root : Noun} (h : Below x root) : Below (hdN x) root := by
  intro hc
  have hx : x.isCell = true := by
    cases x with
    | atom _ => simp [hdN, Noun.isCell] at hc
    | cell _ _ => rfl
  exact mem_cellsOf_trans (h hx) (hdN_cells hc)

theorem below_tl {x root : Noun} (h : Below x root) : Below (tlN x) root := by
  intro hc
  have hx : x.isCell = true := by
    cases x with
    | atom _ => simp [tlN, Noun.isCell] at hc
    | cell _ _ => rfl
  exact mem_cellsOf_trans (h hx) (tlN_cells hc)

theorem below_slot (a : ℕ) : ∀ {x root : Noun}, Noun.slot a root = some x → Below x root := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro x root h
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · simp [slot_zero] at h
    · simp only [Noun.slot, Option.some.injEq] at h; subst h; exact below_self _
  · obtain ⟨l, r, hp, rfl⟩ := (slot_some_iff ha root x).1 h
    have hb := ih (a / 2) (by omega) hp
    have hlr : Noun.cell l r ∈ cellsOf root := hb rfl
    intro hc
    split_ifs at hc ⊢
    · exact mem_cellsOf_trans hlr (by
        cases l with
        | atom _ => simp [Noun.isCell] at hc
        | cell _ _ => simp [cellsOf])
    · exact mem_cellsOf_trans hlr (by
        cases r with
        | atom _ => simp [Noun.isCell] at hc
        | cell _ _ => simp [cellsOf])

theorem below_sibX (a : ℕ) (root : Noun) : Below (sibX a root) root := by
  unfold sibX
  cases h : Noun.slot (a ^^^ 1) root with
  | none => exact below_atom 0 root
  | some x => exact below_slot _ h

theorem below_fdN1 (a b : Noun) : Below (fdN a b).2.1 a := (fdN_cells a b).1
theorem below_fdN2 (a b : Noun) : Below (fdN a b).2.2 b := (fdN_cells a b).2

theorem mem_closure_of_below {L : List Noun} {x root : Noun} (hr : root ∈ L) (hb : Below x root)
    (hc : x.isCell = true) : x ∈ closureOf L :=
  mem_closureOf.mpr ⟨root, hr, hb hc⟩

/-- **Every cell among the twelve handles of a generated row is in `closureOf` of its six root
handles** (no hypothesis: by construction of `rowOfSkelX`). -/
theorem rowHandleNounsX_cells (sk : SkelX) :
    ∀ n ∈ rowHandleNounsX (rowOfSkelX sk), n.isCell = true →
      n ∈ closureOf (handleNounsX (rowOfSkelX sk)) := by
  intro n hn hc
  have key : ∃ root ∈ handleNounsX (rowOfSkelX sk), Below n root := by
    cases hst : sk.state <;>
      simp only [rowOfSkelX, hst, rowHandleNounsX, handleNounsX, List.mem_cons,
        List.not_mem_nil, or_false] at hn ⊢ <;>
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (refine ⟨_, ?_, below_self _⟩; simp; done)
        | (refine ⟨sk.subject, ?_, below_atom _ _⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_hd (below_self _)⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_tl (below_self _)⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_hd (below_tl (below_self _))⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_tl (below_tl (below_self _))⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_hd (below_tl (below_tl (below_self _)))⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_tl (below_tl (below_tl (below_self _)))⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_hd (below_hd (below_tl (below_self _)))⟩; simp; done)
        | (refine ⟨sk.formula, ?_, below_tl (below_hd (below_tl (below_self _)))⟩; simp; done)
        | (refine ⟨kidE sk 0, ?_, below_hd (below_self _)⟩; simp; done)
        | (refine ⟨kidE sk 0, ?_, below_tl (below_self _)⟩; simp; done)
        | (refine ⟨kidE sk 0, ?_, below_fdN1 _ _⟩; simp; done)
        | (refine ⟨kidE sk 1, ?_, below_fdN2 _ _⟩; simp; done)
        | (refine ⟨sk.subject, ?_, below_sibX _ _⟩; simp; done)
        | (refine ⟨sk.evaluation, ?_, below_sibX _ _⟩; simp; done)
  obtain ⟨root, hr, hb⟩ := key
  exact mem_closure_of_below hr hb hc

theorem demandHX_cells_iff (rows : List SkelX) (c : Noun) :
    c ∈ (demandHX rows).cells ↔ c ∈ closureOf (rows.flatMap fun sk => handleNounsX (rowOfSkelX sk)) := by
  simp only [Demand.cells, Demand.roots, demandHX, mem_closureOf, List.map_nil, List.append_nil]
  constructor
  · rintro ⟨n, hn, hc⟩
    rw [List.mem_append] at hn
    rcases hn with hn | hn
    · exact ⟨n, hn, hc⟩
    · simp only [walkReadsHX, List.map_map, List.mem_map, List.mem_flatMap] at hn
      obtain ⟨x, ⟨sk, hsk, hx⟩, rfl⟩ := hn
      exact ⟨x.1, List.mem_flatMap.mpr ⟨sk, hsk, consEntriesX_root _ x hx⟩, hc⟩
  · rintro ⟨n, hn, hc⟩
    exact ⟨n, List.mem_append_left _ hn, hc⟩

/-- Every cell among the twelve handles of every row is a row of the demand's cell table. -/
theorem handle_cells_mem_demandHX (rows : List SkelX) {sk : SkelX} (hsk : sk ∈ rows) :
    ∀ n ∈ rowHandleNounsX (rowOfSkelX sk), n.isCell = true → n ∈ (demandHX rows).cells := by
  intro n hn hc
  rw [demandHX_cells_iff]
  obtain ⟨root, hr, hb⟩ := mem_closureOf.mp (rowHandleNounsX_cells sk n hn hc)
  exact mem_closureOf.mpr ⟨root, List.mem_flatMap.mpr ⟨sk, hsk, hr⟩, hb⟩

/-- Every cell on a walk read's path (the read child and everything between) is below its root,
hence in the demand's closure. -/
theorem walkRead_child_mem {R : Registry} (rows : List SkelX) {sk : SkelX} (hsk : sk ∈ rows)
    (hs : (rowOfSkelX sk).SemN R) {x : PEnt} (hx : x ∈ consEntriesX (rowOfSkelX sk))
    (hc : x.2.2.isCell = true) : x.2.2 ∈ (demandHX rows).cells := by
  rw [demandHX_cells_iff]
  exact mem_closureOf.mpr ⟨x.1, List.mem_flatMap.mpr ⟨sk, hsk, consEntriesX_root _ x hx⟩,
    below_slot _ (consEntriesX_sound sk hs x hx).2 hc⟩

/-! ## §5 The axis column with edit axes -/

def honestAxX (sk : SkelX) : ℕ :=
  match sk.state, sk.formula with
  | .s0, .cell _ (.atom b) => b
  | .s9, .cell _ (.cell (.atom b) _) => b
  | .s10, f => op10Axis f
  | .s10L, f => chainAxis f / 2
  | _, _ => 0

/-- **The `s10` axis**: on a semantically valid edit row the axis column is the edit axis,
`≥ 1`, and `#[a sf1 sf2] = e`. -/
theorem honestAxX_s10 {R : Registry} (sk : SkelX) (hst : sk.state = .s10)
    (hs : (rowOfSkelX sk).SemN R) :
    1 ≤ honestAxX sk ∧
      Noun.edit (honestAxX sk) (rowOfSkelX sk).sf1 (rowOfSkelX sk).sf2 = some sk.evaluation := by
  simp only [rowOfSkelX, hst, RowNX.SemN] at hs
  obtain ⟨h10, hf, hft, hfth, a, ha, hed⟩ := hs
  have hax : honestAxX sk = a := by
    have h1 : op10Axis sk.formula = a := by
      rw [hf, hft, hfth, ha]; rfl
    simp only [honestAxX, hst]; exact h1
  refine ⟨?_, ?_⟩
  · rw [hax]
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp [Noun.edit] at hed
    · exact h
  · rw [hax]; simpa [rowOfSkelX, hst] using hed

/-- On a chain level row the axis column is `a_k / 2`, the next level's axis. -/
theorem honestAxX_s10L (sk : SkelX) (hst : sk.state = .s10L) (a : ℕ) (hf : sk.formula = .atom a) :
    honestAxX sk = a / 2 := by
  simp only [honestAxX, hst, hf, chainAxis]

/-! ## §6 The atom digitisation closure `demandA` -/

/-- The atom leaves of a noun. -/
def leavesOf : Noun → List ℕ
  | .atom a => [a]
  | .cell x y => leavesOf x ++ leavesOf y

/-- **The atom digitisation closure**: every BIG leaf (`≥ p`, Goldilocks) of every handle of
every row, once. -/
def demandA (rows : List SkelX) : List ℕ :=
  (((rows.flatMap fun sk => rowHandleNounsX (rowOfSkelX sk)).flatMap leavesOf).filter
    fun a => decide (Nock.Atoms.p ≤ a)).dedup

/-- The atom table's rows: the canonical limbs (A-1) of each big atom of the closure. -/
def atomTable (rows : List SkelX) : List (List ℕ) := (demandA rows).map Nock.Atoms.limbs

theorem mem_leavesOf_atom (a : ℕ) : a ∈ leavesOf (.atom a) := by simp [leavesOf]

/-- **Every big leaf of every handle of every row is in the closure.** -/
theorem mem_demandA {rows : List SkelX} {sk : SkelX} (hsk : sk ∈ rows) {n : Noun}
    (hn : n ∈ rowHandleNounsX (rowOfSkelX sk)) {a : ℕ} (ha : a ∈ leavesOf n)
    (hbig : Nock.Atoms.p ≤ a) : a ∈ demandA rows := by
  simp only [demandA, List.mem_dedup, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
  exact ⟨⟨n, ⟨sk, hsk, hn⟩, ha⟩, hbig⟩

/-- Every atom of the closure is big. -/
theorem demandA_big {rows : List SkelX} {a : ℕ} (ha : a ∈ demandA rows) : Nock.Atoms.IsBig a := by
  simp only [demandA, List.mem_dedup, List.mem_filter, decide_eq_true_eq] at ha
  exact ha.2

/-- The atom table is canonical and decodes to the closure. -/
theorem atomTable_canonical (rows : List SkelX) :
    ∀ l ∈ atomTable rows, Nock.Atoms.Canonical l ∧ Nock.Atoms.val l ∈ demandA rows := by
  intro l hl
  simp only [atomTable, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  exact ⟨Nock.Atoms.limbs_canonical a, by rw [Nock.Atoms.val_limbs]; exact ha⟩

/-- **The slow OP4 record** (SPEC §3.3): a row `s4` whose increment is not small → small,
i.e. `v + 1 ≥ p`; its record is `(v, v + 1)`. -/
def incRecX (r : RowNX) : Option (ℕ × ℕ) :=
  match r.st, r.sf1 with
  | .s4, .atom v => if Nock.Atoms.p ≤ v + 1 then some (v, v + 1) else none
  | _, _ => none

/-- **The honest inc chain is A-1's carry chain**: `Carry 1 (limbs v) (limbs (v + 1))`. -/
theorem inc_carry (v : ℕ) : Nock.Atoms.Carry 1 (Nock.Atoms.limbs v) (Nock.Atoms.limbs (v + 1)) := by
  obtain ⟨l', h⟩ := Nock.Atoms.carry_exists (le_refl 1) (Nock.Atoms.limbs_canonical v).1
  have := Nock.Atoms.inc_eq_limbs (Nock.Atoms.limbs_canonical v) h
  rw [Nock.Atoms.val_limbs] at this
  rwa [this] at h

/-- A slow OP4 record of a `SemN` row: the result is `v + 1`, it is BIG and in the closure; the
operand is big (then in the closure) or exactly `p − 1`; the limb chain is A-1's `Carry 1`. -/
theorem incRecX_spec {R : Registry} {rows : List SkelX} {sk : SkelX} (hsk : sk ∈ rows)
    (hs : (rowOfSkelX sk).SemN R) {v w : ℕ} (hrec : incRecX (rowOfSkelX sk) = some (v, w)) :
    w = v + 1 ∧ (rowOfSkelX sk).e = .atom w ∧ w ∈ demandA rows ∧
      (v ∈ demandA rows ∨ v + 1 = Nock.Atoms.p) ∧
      Nock.Atoms.Carry 1 (Nock.Atoms.limbs v) (Nock.Atoms.limbs w) := by
  cases hst : sk.state <;> simp [rowOfSkelX, hst, incRecX] at hrec
  simp only [rowOfSkelX, hst, RowNX.SemN] at hs
  obtain ⟨-, -, n, hn, he⟩ := hs
  simp only [rowOfSkelX, hst, hn] at hrec
  split_ifs at hrec with hbig
  obtain ⟨rfl, rfl⟩ := hrec
  have hmemE : sk.evaluation ∈ rowHandleNounsX (rowOfSkelX sk) := by
    simp [rowOfSkelX, hst, rowHandleNounsX]
  have hmemS : kidE sk 0 ∈ rowHandleNounsX (rowOfSkelX sk) := by
    simp [rowOfSkelX, hst, rowHandleNounsX]
  refine ⟨rfl, by simpa [rowOfSkelX, hst] using he, ?_, ?_, inc_carry v⟩
  · rw [he] at hmemE
    exact mem_demandA hsk hmemE (mem_leavesOf_atom _) hbig
  · rcases Nat.lt_or_ge v Nock.Atoms.p with h | h
    · right; omega
    · left; rw [hn] at hmemS; exact mem_demandA hsk hmemS (mem_leavesOf_atom _) h

/-- The limb-level first difference: index, and the two limbs there (`none` = past the top). -/
def lfd : List ℕ → List ℕ → ℕ × Option ℕ × Option ℕ
  | x :: xs, y :: ys => if x = y then ((lfd xs ys).1 + 1, (lfd xs ys).2) else (0, some x, some y)
  | xs, ys => (0, xs.head?, ys.head?)

/-- **`lfd` finds a real difference**: the two limbs at its index are the lists' entries there,
they differ, and they are not both past the top. -/
theorem lfd_spec : ∀ (xs ys : List ℕ), xs ≠ ys →
    (lfd xs ys).2.1 = xs[(lfd xs ys).1]? ∧ (lfd xs ys).2.2 = ys[(lfd xs ys).1]? ∧
      (lfd xs ys).2.1 ≠ (lfd xs ys).2.2
  | [], [], h => absurd rfl h
  | [], y :: ys, _ => by simp [lfd]
  | x :: xs, [], _ => by simp [lfd]
  | x :: xs, y :: ys, h => by
    by_cases hxy : x = y
    · subst hxy
      have hne : xs ≠ ys := fun e => h (by rw [e])
      obtain ⟨h1, h2, h3⟩ := lfd_spec xs ys hne
      simp only [lfd, if_true]
      exact ⟨by simpa using h1, by simpa using h2, h3⟩
    · simp [lfd, hxy]

/-- **The OP5 big ≠ big second pair** (SPEC §3.3, the atom-walk α instance): on an OP5 "≠" row
whose first-difference leaves are both big atoms `a ≠ b`, the limb index and the two limbs. -/
def bigPairX (r : RowNX) : Option (ℕ × ℕ × ℕ × Option ℕ × Option ℕ) :=
  match r.st, r.ftth, r.fttt with
  | .s5, .atom a, .atom b =>
    if Nock.Atoms.p ≤ a ∧ Nock.Atoms.p ≤ b ∧ a ≠ b then
      some (a, b, (lfd (Nock.Atoms.limbs a) (Nock.Atoms.limbs b)).1,
        (lfd (Nock.Atoms.limbs a) (Nock.Atoms.limbs b)).2)
    else none
  | _, _, _ => none

/-- The second pair is a real limb difference (`k₁·k₂ = 0`: not both past the top) between the
canonical limbs of two closure atoms. -/
theorem bigPairX_spec {rows : List SkelX} {sk : SkelX} (hsk : sk ∈ rows) {a b i : ℕ}
    {l₁ l₂ : Option ℕ} (h : bigPairX (rowOfSkelX sk) = some (a, b, i, l₁, l₂)) :
    a ∈ demandA rows ∧ b ∈ demandA rows ∧
      l₁ = (Nock.Atoms.limbs a)[i]? ∧ l₂ = (Nock.Atoms.limbs b)[i]? ∧ l₁ ≠ l₂ := by
  have hst : sk.state = .s5 := by
    cases hst : sk.state <;> simp [rowOfSkelX, hst, bigPairX] at h ⊢
  revert h
  simp only [rowOfSkelX, hst, bigPairX]
  generalize hA : (fdN (kidE sk 0) (kidE sk 1)).2.1 = A
  generalize hB : (fdN (kidE sk 0) (kidE sk 1)).2.2 = B
  intro h
  rcases A with a | _ <;> rcases B with b | _ <;> simp at h
  obtain ⟨⟨ha, hb, hab⟩, rfl, rfl, hl⟩ := h
  have hmA : Noun.atom a ∈ rowHandleNounsX (rowOfSkelX sk) := by
    simp [rowOfSkelX, hst, rowHandleNounsX, hA]
  have hmB : Noun.atom b ∈ rowHandleNounsX (rowOfSkelX sk) := by
    simp [rowOfSkelX, hst, rowHandleNounsX, hB]
  have hne : Nock.Atoms.limbs a ≠ Nock.Atoms.limbs b := by
    intro e; apply hab; rw [← Nock.Atoms.val_limbs a, ← Nock.Atoms.val_limbs b, e]
  obtain ⟨h1, h2, h3⟩ := lfd_spec _ _ hne
  rw [hl] at h1 h2 h3
  exact ⟨mem_demandA hsk hmA (mem_leavesOf_atom _) ha, mem_demandA hsk hmB (mem_leavesOf_atom _) hb,
    h1, h2, h3⟩

end Nock.Edit.GenX
