/-
  Nock/Edit/GenX.lean

  **The generator twin at the extended ISA.**  `Gen.lean` is NOT edited (it is read as a
  pattern only: `genComputeSkeleton`'s per-opcode arms and child conventions).

  Semantics: `Nock.evalN` (ℕ-Nock, Nock 4K
  atoms: op 4 is `n ↦ n + 1` with no wrap, so big atoms are native), J-1's `Registry`.

  * `SkelX` — a compute row of the extended ISA (state `StateX`, `(s, f, e)`, and the labels of
    its children, in E-0's `KidInputsX` order, which is the chip's `sf1 / sf2` order).
  * `genChain old e a` — the edit chain pseudo-rows `s10L` (one per level `a_k ≥ 2`) ending in
    `s10T` at the atom `1`.
  * `jetHit R b v c s` — jet dispatch on a dynamic hint `[11 [b clue] c]` whose clue has value
    `v`.  A jet is ONE KIND of hint: the tag `b` must be the atom `%wild` (`wildTag`), and the jet
    key is the clue's VALUE `v`, an atom `id` with `R id` registered at exactly the formula `c`.
    Then the row is `s11j` with ONE child (the clue) and its result is
    `r`, computed by the template's semantics — the generator never descends into `c`.
    Otherwise a dynamic hint is an `s11d` row (clue, then body).  `wildCall id c` is the wire
    form `[11 [%wild [1 id]] c]`.  (J-1's `Nock.Jet.jetCall`, tag = id, is the earlier form and
    is no longer a jet here.)
  * `genComputeSkeletonX R fuel s f` — the generator: every opcode `0 … 11` and autocons, ℕ-atoms
    (so op 4 / op 5 on big atoms), op 10 with its chain, op 11 static / dynamic / jet.
  * **Key lemmas.**  `genX_complete`: an `evalN` run at fuel `n` has a generated tree at the same
    fuel with the SAME result (needs only the registry's `Complete` half).  `genX_sound`: a
    generated tree's result `HoldsN` (needs `Registry.Faithful`).  `genX_label`: the root row is
    `(s, f, r)` and is not a chain row.  `genX_inTree`: every node of a generated tree is either
    itself a generated run (non-chain), or a chain subtree `genChain old e a` with `ChainOK a old
    e` (E-0); `genX_inTree_holdsN`: every non-chain node `HoldsN`.  `honest_holdsN`: the honest run
    gives `HoldsN` and the root result is `evalN`'s.
-/
import Nock.Edit.SemanticsX
import Nock.Jet.Semantics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Nock.Edit.GenX

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit

/-! ## §1 Rows and trees -/

/-- **A compute row at the extended ISA**: state, `(s, f, e)`, and its children's labels. -/
structure SkelX where
  state : StateX
  subject : Noun
  formula : Noun
  evaluation : Noun
  kids : List RowX
deriving DecidableEq, Repr

/-- The `RowX` label of a row. -/
def SkelX.row (k : SkelX) : RowX := ⟨k.state, k.subject, k.formula, k.evaluation⟩

/-- A node whose `kids` field is its children's rows. -/
def mkX (st : StateX) (s f e : Noun) (ks : List (NTree SkelX)) : NTree SkelX :=
  .node ⟨st, s, f, e, ks.map fun k => k.label.row⟩ ks

@[simp] theorem mkX_label (st : StateX) (s f e : Noun) (ks : List (NTree SkelX)) :
    (mkX st s f e ks).label = ⟨st, s, f, e, ks.map fun k => k.label.row⟩ := rfl

@[simp] theorem mkX_children (st : StateX) (s f e : Noun) (ks : List (NTree SkelX)) :
    (mkX st s f e ks).children = ks := rfl

/-! ## §2 The edit chain -/

/-- The chain pseudo-rows below an `s10` row (fuel `k` bounds the depth): `s10L` at every level
`a ≥ 2` (subject `old`, formula the ATOM `a`, evaluation `e`, one child at `a / 2`), `s10T` at the
atom `1`. -/
def genChainF (old e : Noun) : ℕ → ℕ → NTree SkelX
  | 0, a => mkX .s10T old (.atom a) e []
  | k + 1, a =>
    if 2 ≤ a then mkX .s10L old (.atom a) e [genChainF old e k (a / 2)]
    else mkX .s10T old (.atom a) e []

/-- **The chain of `#[a new old] = e`** (depth fuel `a`). -/
def genChain (old e : Noun) (a : ℕ) : NTree SkelX := genChainF old e a a


/-- **Jet dispatch.**  `b` is the hint's tag, `v` the VALUE of its clue, `c` its body.  A hit needs
the reserved tag `%wild`, an atomic clue value `id` (the jet key), an entry registered at `id`
whose formula is exactly `c`, and a template that answers on `s`.  The tag names the hint kind;
the key is the clue's payload. -/
def jetHit (R : Registry) (b v c s : Noun) : Option Noun :=
  match b, v with
  | .atom w, .atom id =>
    if w = wildTag then
      match R id with
      | some j => if j.c = c then j.T.semS s else none
      | none => none
    else none
  | _, _ => none

/-! ## §4 The generator -/

/-- **`genComputeSkeletonX`**: the compute tree of `*[s f]` at the extended ISA, with its result.
Children are in E-0's `KidInputsX` order. -/
def genComputeSkeletonX (R : Registry) : ℕ → Noun → Noun → Option (NTree SkelX × Noun)
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | n + 1, s, .cell (.cell b c) d =>
    match genComputeSkeletonX R n s (.cell b c), genComputeSkeletonX R n s d with
    | some (tl, l), some (tr, r) =>
      some (mkX .cons s (.cell (.cell b c) d) (.cell l r) [tl, tr], .cell l r)
    | _, _ => none
  | _ + 1, s, .cell (.atom 0) (.atom ax) =>
    match Noun.slot ax s with
    | some r => some (mkX .s0 s (.cell (.atom 0) (.atom ax)) r [], r)
    | none => none
  | _ + 1, s, .cell (.atom 1) t => some (mkX .s1 s (.cell (.atom 1) t) t [], t)
  | n + 1, s, .cell (.atom 2) (.cell b c) =>
    match genComputeSkeletonX R n s b, genComputeSkeletonX R n s c with
    | some (t0, sb), some (t1, sc) =>
      match genComputeSkeletonX R n sb sc with
      | some (t2, r) => some (mkX .s2 s (.cell (.atom 2) (.cell b c)) r [t0, t1, t2], r)
      | none => none
    | _, _ => none
  | n + 1, s, .cell (.atom 3) t =>
    match genComputeSkeletonX R n s t with
    | some (t0, v) => some (mkX .s3 s (.cell (.atom 3) t) (Noun.wut v) [t0], Noun.wut v)
    | none => none
  | n + 1, s, .cell (.atom 4) t =>
    match genComputeSkeletonX R n s t with
    | some (t0, .atom v) =>
      some (mkX .s4 s (.cell (.atom 4) t) (.atom (v + 1)) [t0], .atom (v + 1))
    | _ => none
  | n + 1, s, .cell (.atom 5) (.cell b c) =>
    match genComputeSkeletonX R n s b, genComputeSkeletonX R n s c with
    | some (t0, x), some (t1, y) =>
      some (mkX .s5 s (.cell (.atom 5) (.cell b c)) (Noun.tis x y) [t0, t1], Noun.tis x y)
    | _, _ => none
  | n + 1, s, .cell (.atom 6) (.cell b (.cell c d)) =>
    match genComputeSkeletonX R n s b with
    | some (tC, .atom 0) =>
      match genComputeSkeletonX R n s c with
      | some (tT, r) => some (mkX .s6 s (.cell (.atom 6) (.cell b (.cell c d))) r [tT, tC], r)
      | none => none
    | some (tC, .atom 1) =>
      match genComputeSkeletonX R n s d with
      | some (tT, r) => some (mkX .s6 s (.cell (.atom 6) (.cell b (.cell c d))) r [tT, tC], r)
      | none => none
    | _ => none
  | n + 1, s, .cell (.atom 7) (.cell b c) =>
    match genComputeSkeletonX R n s b with
    | some (tH, sb) =>
      match genComputeSkeletonX R n sb c with
      | some (tM, r) => some (mkX .s7 s (.cell (.atom 7) (.cell b c)) r [tM, tH], r)
      | none => none
    | none => none
  | n + 1, s, .cell (.atom 8) (.cell b c) =>
    match genComputeSkeletonX R n s b with
    | some (tH, sb) =>
      match genComputeSkeletonX R n (.cell sb s) c with
      | some (tM, r) => some (mkX .s8 s (.cell (.atom 8) (.cell b c)) r [tM, tH], r)
      | none => none
    | none => none
  | n + 1, s, .cell (.atom 9) (.cell (.atom ax) c) =>
    match genComputeSkeletonX R n s c with
    | some (tC, core) =>
      match Noun.slot ax core with
      | some arm =>
        match genComputeSkeletonX R n core arm with
        | some (tI, r) =>
          some (mkX .s9 s (.cell (.atom 9) (.cell (.atom ax) c)) r [tC, tI], r)
        | none => none
      | none => none
    | none => none
  | n + 1, s, .cell (.atom 10) (.cell (.cell (.atom ax) c) d) =>
    match genComputeSkeletonX R n s c, genComputeSkeletonX R n s d with
    | some (tN, new), some (tO, old) =>
      match Noun.edit ax new old with
      | some e =>
        some (mkX .s10 s (.cell (.atom 10) (.cell (.cell (.atom ax) c) d)) e
          [tN, tO, genChain old e ax], e)
      | none => none
    | _, _ => none
  | n + 1, s, .cell (.atom 11) (.cell (.cell b clue) body) =>
    match genComputeSkeletonX R n s clue with
    | some (tD, v) =>
      match jetHit R b v body s with
      | some r => some (mkX .s11j s (.cell (.atom 11) (.cell (.cell b clue) body)) r [tD], r)
      | none =>
        match genComputeSkeletonX R n s body with
        | some (tB, r) =>
          some (mkX .s11d s (.cell (.atom 11) (.cell (.cell b clue) body)) r [tD, tB], r)
        | none => none
    | none => none
  | n + 1, s, .cell (.atom 11) (.cell (.atom b) body) =>
    match genComputeSkeletonX R n s body with
    | some (tB, r) => some (mkX .s11s s (.cell (.atom 11) (.cell (.atom b) body)) r [tB], r)
    | none => none
  | _ + 1, _, .cell (.atom _) _ => none

/-- Short name. -/
abbrev genX := genComputeSkeletonX


/-! ## §5 Root, soundness, completeness -/

/-- **The root row** of a generated tree is `(s, f, r)`, and it is not a chain row. -/
theorem genX_label {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    t.label.subject = s ∧ t.label.formula = f ∧ t.label.evaluation = r ∧
      t.label.state.isChain = false := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals (simp_all [genComputeSkeletonX]; try (obtain ⟨rfl, rfl⟩ := h; simp [StateX.isChain]))

/-- What a jet hit means: the tag is `%wild`, the clue's value is an atom `id`, the registry has
an entry at `id` with exactly that formula, and the entry's relation holds. -/
theorem jetHit_spec {R : Registry} {b v c s r : Noun} (h : jetHit R b v c s = some r) :
    ∃ id j, b = .atom wildTag ∧ v = .atom id ∧ R id = some j ∧ j.c = c ∧ j.T.rel s r := by
  unfold jetHit at h
  rcases b with w | _
  · rcases v with id | _
    · simp only at h
      split_ifs at h with hw
      subst hw
      cases hj : R id with
      | none => simp [hj] at h
      | some j =>
        simp only [hj] at h
        split_ifs at h with hc
        exact ⟨id, j, rfl, rfl, hj, hc, h⟩
    · simp at h
  · simp at h

/-- A run at some fuel is a run at every larger fuel. -/
theorem holds_ge {s f r : Noun} (h : HoldsN ⟨s, f, r⟩) :
    ∃ N, ∀ m, N ≤ m → evalN m s f = some r := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun m hm => evalN_mono hm hN⟩

/-- **Soundness**: a generated result `HoldsN` (a jet row's result is grounded by `Faithful`). -/
theorem genX_sound {R : Registry} (hR : R.Faithful) {n : ℕ} {s f : Noun} {t : NTree SkelX}
    {r : Noun} (h : genX R n s f = some (t, r)) : HoldsN ⟨s, f, r⟩ := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hbc); obtain ⟨N2, e2⟩ := holds_ge (ih2 hd)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨1, by simp [evalN, hs]⟩
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨1, by simp [evalN]⟩
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hc)
    obtain ⟨N3, e3⟩ := holds_ge (ih3 hm)
    exact ⟨N1 + N2 + N3 + 1, by
      simp [evalN, e1 (N1 + N2 + N3) (by omega), e2 (N1 + N2 + N3) (by omega),
        e3 (N1 + N2 + N3) (by omega)]⟩
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih hx)
    exact ⟨N1 + 1, by simp [evalN, e1 N1 le_rfl]⟩
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih hx)
    exact ⟨N1 + 1, by simp [evalN, e1 N1 le_rfl, Noun.lus]⟩
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hc)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hc)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hc)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hm)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hb); obtain ⟨N2, e2⟩ := holds_ge (ih2 hm)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hc); obtain ⟨N2, e2⟩ := holds_ge (ih2 hm)
    exact ⟨N1 + N2 + 1, by
      simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega), harm]⟩
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hc); obtain ⟨N2, e2⟩ := holds_ge (ih2 hd)
    exact ⟨N1 + N2 + 1, by
      simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega), he]⟩
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨id, j, rfl, rfl, hRj, hc, hrel⟩ := jetHit_spec hj
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hcl)
    obtain ⟨N2, e2⟩ := holds_ge ((hR id j hRj).1 s r1 hrel)
    change ∀ m, N2 ≤ m → evalN m s j.c = some r1 at e2
    rw [hc] at e2
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hcl); obtain ⟨N2, e2⟩ := holds_ge (ih2 hB)
    exact ⟨N1 + N2 + 1, by simp [evalN, e1 (N1 + N2) (by omega), e2 (N1 + N2) (by omega)]⟩
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨N1, e1⟩ := holds_ge (ih1 hB)
    exact ⟨N1 + 1, by simp [evalN, e1 N1 le_rfl]⟩
/-- **Completeness at the same fuel**: an `evalN` run has a generated tree with the SAME result
(a jet hit agrees with the body's run by the entry's `Complete` half). -/
theorem genX_complete {R : Registry} (hR : R.Faithful) {n : ℕ} {s f r : Noun}
    (h : evalN n s f = some r) : ∃ t, genX R n s f = some (t, r) := by
  induction n, s, f using evalN.induct generalizing r
  all_goals first | (simp_all [evalN]; done) | skip
  case case3 fuel s b c d l r1 hd hbc ih1 ih2 =>
    simp only [evalN, hd, hbc, Option.some.injEq] at h; subst h
    obtain ⟨t1, g1⟩ := ih1 hbc; obtain ⟨t2, g2⟩ := ih2 hd
    simp [genComputeSkeletonX, g1, g2]
  case case5 fuel s ax =>
    simp only [evalN] at h
    simp [genComputeSkeletonX, h]
  case case7 fuel s u =>
    simp only [evalN, Option.some.injEq] at h; subst h
    simp [genComputeSkeletonX]
  case case8 fuel s b c l r1 hc hb ih1 ih2 ih3 =>
    simp only [evalN, hb, hc] at h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 hc; obtain ⟨t3, g3⟩ := ih3 h
    simp [genComputeSkeletonX, g1, g2, g3]
  case case11 fuel s u ih =>
    simp only [evalN, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    obtain ⟨t1, g1⟩ := ih hv
    simp [genComputeSkeletonX, g1]
  case case12 fuel s u ih =>
    simp only [evalN, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hl⟩ := h
    obtain ⟨t1, g1⟩ := ih hv
    cases v with
    | atom m =>
      simp only [Noun.lus, Option.some.injEq] at hl; subst hl
      simp [genComputeSkeletonX, g1]
    | cell _ _ => simp [Noun.lus] at hl
  case case13 fuel s b c l r1 hc hb ih1 ih2 =>
    simp only [evalN, hb, hc, Option.some.injEq] at h; subst h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 hc
    simp [genComputeSkeletonX, g1, g2]
  case case16 fuel s b c d hb ih1 ih2 =>
    simp only [evalN, hb] at h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 h
    simp [genComputeSkeletonX, g1, g2]
  case case17 fuel s b c d hb ih1 ih2 =>
    simp only [evalN, hb] at h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 h
    simp [genComputeSkeletonX, g1, g2]
  case case20 fuel s b c sb hb ih1 ih2 =>
    simp only [evalN, hb] at h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 h
    simp [genComputeSkeletonX, g1, g2]
  case case23 fuel s b c sb hb ih1 ih2 =>
    simp only [evalN, hb] at h
    obtain ⟨t1, g1⟩ := ih1 hb; obtain ⟨t2, g2⟩ := ih2 h
    simp [genComputeSkeletonX, g1, g2]
  case case26 fuel s ax c core hc arm harm ih1 ih2 =>
    simp only [evalN, hc, harm] at h
    obtain ⟨t1, g1⟩ := ih1 hc; obtain ⟨t2, g2⟩ := ih2 h
    simp [genComputeSkeletonX, g1, g2, harm]
  case case30 fuel s ax c d new old hd hc ih1 ih2 =>
    simp only [evalN, hd, hc] at h
    obtain ⟨t1, g1⟩ := ih1 hc; obtain ⟨t2, g2⟩ := ih2 hd
    simp [genComputeSkeletonX, g1, g2, h]
  case case33 fuel s a clue body v hcl ih1 ih2 =>
    simp only [evalN, hcl] at h
    obtain ⟨t1, g1⟩ := ih1 hcl
    cases hj : jetHit R a v body s with
    | none =>
      obtain ⟨t2, g2⟩ := ih2 h
      simp [genComputeSkeletonX, g1, g2, hj]
    | some r' =>
      obtain ⟨id, j, rfl, rfl, hRj, hc, hrel⟩ := jetHit_spec hj
      have hrel' : j.T.rel s r := (hR id j hRj).2 s fuel r (by rw [hc]; exact h)
      obtain rfl := Template.rel_functional hrel hrel'
      simp [genComputeSkeletonX, g1, hj]
  case case35 fuel s a body ih =>
    simp only [evalN] at h
    obtain ⟨t1, g1⟩ := ih h
    simp [genComputeSkeletonX, g1]
/-! ## §6 The edit chain is honest -/

/-- **The converse of E-0's `edit_of_slots`**: a successful edit puts `new` at `a` in `e` and
leaves every off-spine sibling of the path unchanged. -/
theorem chainOK_of_edit (a : ℕ) : ∀ {new old e : Noun}, Noun.edit a new old = some e →
    ChainOK a old e ∧ Noun.slot a e = some new := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro new old e h
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · simp [Noun.edit] at h
    · simp only [Noun.edit, Option.some.injEq] at h; subst h
      exact ⟨chainOK_of_lt_two (by norm_num) _ _, by simp [Noun.slot]⟩
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
    have hsibB : (if ((m + 2) % 2 == 0) = true then m + 2 + 1 else m + 2 - 1) = (m + 2) ^^^ 1 := by
      rw [xor_one_eq]; by_cases hm : (m + 2) % 2 = 0 <;> simp [hm]
    simp only [Noun.edit] at h
    rw [hsibB] at h
    cases hx : Noun.slot ((m + 2) ^^^ 1) old with
    | none => simp [hx] at h
    | some x =>
      simp only [hx] at h
      by_cases hm : (m + 2) % 2 = 0
      · have hb : ((m + 2) % 2 == 0) = true := by simp [hm]
        simp only [hb, if_true] at h
        obtain ⟨hup, hpar⟩ := ih ((m + 2) / 2) (by omega) h
        have hx' : (m + 2) ^^^ 1 = m + 3 := by rw [xor_one_eq, if_pos hm]
        have h1 : Noun.slot (m + 2) e = some new :=
          (slot_some_iff ha e new).2 ⟨new, x, hpar, by rw [if_pos hm]⟩
        have h2 : Noun.slot ((m + 2) ^^^ 1) e = some x := by
          rw [hx', slot_some_iff (by omega)]
          refine ⟨new, x, ?_, ?_⟩
          · rw [show (m + 3) / 2 = (m + 2) / 2 by omega]; exact hpar
          · have : ¬ (m + 3) % 2 = 0 := by omega
            simp [this]
        exact ⟨chainOK_step ha ⟨x, hx, h2⟩ hup, h1⟩
      · have hb : ((m + 2) % 2 == 0) = false := by simpa using hm
        simp only [hb, if_false, Bool.false_eq_true] at h
        obtain ⟨hup, hpar⟩ := ih ((m + 2) / 2) (by omega) h
        have hx' : (m + 2) ^^^ 1 = m + 1 := by rw [xor_one_eq, if_neg hm]; omega
        have h1 : Noun.slot (m + 2) e = some new :=
          (slot_some_iff ha e new).2 ⟨x, new, hpar, by rw [if_neg hm]⟩
        have h2 : Noun.slot ((m + 2) ^^^ 1) e = some x := by
          rw [hx', slot_some_iff (by omega)]
          refine ⟨x, new, ?_, ?_⟩
          · rw [show (m + 1) / 2 = (m + 2) / 2 by omega]; exact hpar
          · have : (m + 1) % 2 = 0 := by omega
            simp [this]
        exact ⟨chainOK_step ha ⟨x, hx, h2⟩ hup, h1⟩

/-- `edit` ⟺ chain + slot (E-0's `edit_of_slots` and its converse). -/
theorem edit_iff_chainOK {a : ℕ} {new old e : Noun} :
    Noun.edit a new old = some e ↔ ChainOK a old e ∧ Noun.slot a e = some new :=
  ⟨chainOK_of_edit a, fun h => edit_of_slots h.1 h.2⟩
/-! ## §7 Every node of a generated tree -/

/-- A chain subtree: `genChainF old e k a` with the chain invariant at `a` and enough depth fuel
(`1 ≤ a ≤ k + 1`, so it ends at the atom `1`). -/
def ChainNode (u : NTree SkelX) : Prop :=
  ∃ old e k a, u = genChainF old e k a ∧ ChainOK a old e ∧ 1 ≤ a ∧ a ≤ k + 1

/-- A generated node: it is itself the tree of a generated run. -/
def GenNode (R : Registry) (u : NTree SkelX) : Prop :=
  ∃ m, genX R m u.label.subject u.label.formula = some (u, u.label.evaluation)

theorem genNode_of {R : Registry} {m : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R m s f = some (t, r)) : GenNode R t := by
  obtain ⟨h1, h2, h3, -⟩ := genX_label h
  exact ⟨m, by rw [h1, h2, h3]; exact h⟩

theorem genChainF_label (old e : Noun) (k a : ℕ) :
    (genChainF old e k a).label.subject = old ∧ (genChainF old e k a).label.evaluation = e ∧
      (genChainF old e k a).label.formula = .atom a ∧
      (genChainF old e k a).label.state.isChain = true := by
  cases k with
  | zero => simp [genChainF, StateX.isChain]
  | succ k => by_cases h2 : 2 ≤ a <;> simp [genChainF, h2, StateX.isChain]

theorem chainNode_children {u : NTree SkelX} (hu : ChainNode u) :
    ∀ k ∈ u.children, ChainNode k := by
  obtain ⟨old, e, k, a, rfl, hc, h1, h2⟩ := hu
  cases k with
  | zero => simp [genChainF]
  | succ k =>
    by_cases ha : 2 ≤ a
    · simp only [genChainF, ha, if_true, mkX_children, List.mem_singleton]
      rintro _ rfl
      exact ⟨old, e, k, a / 2, rfl, chainOK_half hc, by omega, by omega⟩
    · simp [genChainF, ha]

/-- The chain of a successful edit is a chain node. -/
theorem chainNode_genChain {a : ℕ} {new old e : Noun} (h : Noun.edit a new old = some e) :
    ChainNode (genChain old e a) := by
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [Noun.edit] at h
    · exact ha
  exact ⟨old, e, a, a, rfl, (chainOK_of_edit a h).1, ha, by omega⟩

/-- Every child of a generated row is a generated row or the edit chain. -/
theorem genX_children {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : ∀ k ∈ t.children, GenNode R k ∨ ChainNode k := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl | rfl)
    · exact Or.inl (genNode_of hc)
    · exact Or.inl (genNode_of hd)
    · exact Or.inr (chainNode_genChain he)
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))

/-- **Every node of a tree rooted at a generated or chain node is a generated or chain node.** -/
theorem nodes_ok {R : Registry} {t u : NTree SkelX} (hu : InTree t u)
    (ht : GenNode R t ∨ ChainNode t) : GenNode R u ∨ ChainNode u := by
  induction hu with
  | here => exact ht
  | sub hs _ ih =>
    apply ih
    rcases ht with ⟨m, hm⟩ | hc
    · exact genX_children hm _ hs
    · exact Or.inr (chainNode_children hc _ hs)

theorem genX_inTree {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u) :
    GenNode R u ∨ ChainNode u :=
  nodes_ok hu (Or.inl (genNode_of h))

theorem chainNode_isChain {u : NTree SkelX} (hu : ChainNode u) : u.label.state.isChain = true := by
  obtain ⟨old, e, k, a, rfl, -⟩ := hu
  exact (genChainF_label old e k a).2.2.2

/-- A chain node carries E-0's chain invariant at its own (atom) axis. -/
theorem chainNode_chainOK {u : NTree SkelX} (hu : ChainNode u) :
    ChainOK (chainAxis u.label.formula) u.label.subject u.label.evaluation ∧
      ∃ a, u.label.formula = .atom a := by
  obtain ⟨old, e, k, a, rfl, hc, -⟩ := hu
  obtain ⟨h1, h2, h3, -⟩ := genChainF_label old e k a
  rw [h1, h2, h3]
  exact ⟨hc, a, rfl⟩

/-- **Every non-chain node of a generated tree `HoldsN`.** -/
theorem genX_inTree_holdsN {R : Registry} (hR : R.Faithful) {n : ℕ} {s f : Noun}
    {t : NTree SkelX} {r : Noun} (h : genX R n s f = some (t, r)) {u : NTree SkelX}
    (hu : InTree t u) (hc : u.label.state.isChain = false) :
    HoldsN ⟨u.label.subject, u.label.formula, u.label.evaluation⟩ := by
  rcases genX_inTree h hu with ⟨m, hm⟩ | hch
  · exact genX_sound hR hm
  · rw [chainNode_isChain hch] at hc; cases hc

/-- **The honest run.**  An `evalN` run has a generated tree at the same fuel whose root is the
run's `(s, f, r)`; every non-chain node `HoldsN`; every chain node satisfies `ChainOK`. -/
theorem honest_holdsN {R : Registry} (hR : R.Faithful) {fuel : ℕ} {s f r : Noun}
    (hrun : evalN fuel s f = some r) :
    ∃ t, genX R fuel s f = some (t, r) ∧
      t.label.subject = s ∧ t.label.formula = f ∧ t.label.evaluation = r ∧
      HoldsN ⟨s, f, r⟩ ∧
      ∀ u, InTree t u →
        (u.label.state.isChain = false →
          HoldsN ⟨u.label.subject, u.label.formula, u.label.evaluation⟩) ∧
        (u.label.state.isChain = true →
          ChainOK (chainAxis u.label.formula) u.label.subject u.label.evaluation) := by
  obtain ⟨t, ht⟩ := genX_complete hR hrun
  obtain ⟨h1, h2, h3, -⟩ := genX_label ht
  refine ⟨t, ht, h1, h2, h3, ⟨fuel, hrun⟩, fun u hu => ⟨genX_inTree_holdsN hR ht hu, fun hc => ?_⟩⟩
  rcases genX_inTree ht hu with ⟨m, hm⟩ | hch
  · rw [(genX_label hm).2.2.2] at hc; cases hc
  · exact (chainNode_chainOK hch).1

/-- **The root result is `evalN`'s**: any generated result agrees with any `evalN` run. -/
theorem genX_result_eq_evalN {R : Registry} (hR : R.Faithful) {n m : ℕ} {s f r r' : Noun}
    {t : NTree SkelX} (h : genX R n s f = some (t, r)) (hrun : evalN m s f = some r') :
    t.label.evaluation = r' := by
  obtain ⟨fuel, hf⟩ := genX_sound hR h
  rw [(genX_label h).2.2.1]
  exact evalN_deterministic hf hrun

/-- **A jetted row never descends into the body**: its only child is the clue.  The clue's run
`hcl` is a hypothesis because dispatch reads the clue's value `v`; a successful `h` always has
one, and it is unique. -/
theorem genX_jet_row {R : Registry} {n : ℕ} {s b clue body : Noun} {t : NTree SkelX} {r r' : Noun}
    {tD : NTree SkelX} {v : Noun}
    (h : genX R (n + 1) s (.cell (.atom 11) (.cell (.cell b clue) body)) = some (t, r))
    (hcl : genX R n s clue = some (tD, v))
    (hj : jetHit R b v body s = some r') :
    t.label.state = .s11j ∧ r = r' ∧ t.children = [tD] := by
  have hcl' := hcl
  unfold genX at hcl'
  simp only [genX, genComputeSkeletonX, hcl', hj, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

end Nock.Edit.GenX
