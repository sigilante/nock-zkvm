/-
  Nock/NockVMROM/Thm54/VclL/Handle/LocalVSX.lean

  New module, additive, pure noun logic (no chip, no coin).

  * `RowVSX` — a decoded J-8 compute row: its `StateX` and twelve handles `(k, v)` with the WIRE
    kind `k ∈ {0, 1, 2}` (small atom, cell serial, big-atom row) of `computeChipVCLHX`;
    `kidsX` — the child labels, exactly `ChipHX.childrenX` (`labAtom` at `s10L`).
  * `DenOKX p D` — what `D` must satisfy: kind 0 denotes the atom itself, kind 1 a cell, kind 2 an
    atom `≥ p`.  `DifferX` — the certified differences (kinds, small values, and two big atoms of
    different value — the α-pair case, discharged chip-side from the atom walk's records).
  * **`RowSemX0 D R p r`** — what the gates and the served, genuine records say about a row, per
    state `0..16`, at ℕ (op 4 is `n ↦ n + 1`; op 11 jet: the registry entry and `T.rel`);
    **`RowSemX`** = `RowSemX0 ∧ KidKinds` (C-2 part 2: the kid-kind clause is a gate fact).
  * **`local_stepX`** — `RowSemX0` + children carrying `kidsX` + the kid-kind clause ⇒ E-0's
    `FormulaShapeX`, C-2's `KidInputsNX`, `RowOutputNX` and the `roles` (chain positions are
    exactly `chainPosX`) on denotations.
  * **`state_of_formulaX`** (weakened, SPEC §3.1): the same formula fixes the state up to
    `s11d ~ s11j`, both of which give the same `RowOutputNX` conclusion `HoldsN`-wise.
  * **`holdsN_of_rowsVSX`** — a row tree with `RowsOKX` and a real root whose `(s, f, e)` denote
    the claim proves `HoldsN` of the claim (through `GenuineNX` / `genuineNX_holdsN`).

  **FINDING (C-2, U for C-1/J-8a, noun-level witness compiled: `kidKinds_load_bearing`).**  The
  walk labels are tag-free, and a chain pseudo-row (`s10L`, `s10T`) has an ATOM formula, so it can
  serve ANY child label whose formula handle is a small atom.  `s10T` constrains only `f = 1`: an
  OP4 row `[4 1]` whose child `(s, 1, sf1)` is served by an `s10T` row with an arbitrary `e`
  satisfies every row semantics and every link, yet `*[s [4 1]]` crashes.  `RowsOKX` therefore
  carried the premise `KidKinds`: every REAL child position's formula handle has wire kind `1`
  (a cell).  It costs no completeness (an atom formula crashes `evalN`).
-/
import Nock.Edit.GenuineNX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX

open Nock Nock.Walk Nock.Edit
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow (FormulaShape op0Axis op9Axis condBit hd tl)
open Nock.Jet (Registry HoldsN JetSpec)

/-! ## 1. Rows, child labels, the row semantics -/

/-- A handle: wire kind `k` (`0` small atom, `1` cell serial, `2` big-atom row) and value. -/
abbrev HX := ℕ × ℕ

/-- **A decoded J-8 compute row** (`ChipHX.hdX 0.. 11`). -/
structure RowVSX where
  st : StateX
  s : HX
  f : HX
  e : HX
  sf1 : HX
  sf2 : HX
  fh : HX
  ft : HX
  fth : HX
  ftt : HX
  ftth : HX
  fttt : HX
  m : HX

abbrev TripX := HX × HX × HX

def RowVSX.trip (r : RowVSX) : TripX := (r.s, r.f, r.e)

/-- **The child labels per state** (`ChipHX.childrenX`; `s10L`'s child is `labAtom (s, a/2, e)`). -/
def kidsX (r : RowVSX) : List TripX :=
  match r.st with
  | .s2 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2), (r.sf1, r.sf2, r.e)]
  | .s3 => [(r.s, r.ft, r.sf1)]
  | .s4 => [(r.s, r.ft, r.sf1)]
  | .s5 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2)]
  | .s6 => [(r.s, r.m, r.sf1), (r.s, r.fth, r.sf2)]
  | .s7 => [(r.sf2, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s8 => [(r.m, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s9 => [(r.s, r.ftt, r.sf1), (r.sf1, r.m, r.sf2)]
  | .cons => [(r.s, r.fh, r.sf1), (r.s, r.ft, r.sf2)]
  | .s10 => [(r.s, r.fttt, r.sf1), (r.s, r.ftt, r.sf2), (r.sf2, r.ftth, r.e)]
  | .s10L => [(r.s, (0, r.f.2 / 2), r.e)]
  | .s11s => [(r.s, r.ftt, r.e)]
  | .s11d => [(r.s, r.fttt, r.sf1), (r.s, r.ftt, r.e)]
  | .s11j => [(r.s, r.fttt, r.sf1)]
  | _ => []

section Sem
variable (p : ℕ) (D : HX → Option Noun)

def Cell3 (a b c : HX) : Prop := ∃ A B, D a = some (.cell A B) ∧ D b = some A ∧ D c = some B

/-- **Certified differences** (`neGate` over `(kc, kb, v)`, SPEC §3.3): kinds that name disjoint
noun classes (a small value is `< p`, a big atom `≥ p`), two different small values, or two big
atoms of different value (the α pair, certified chip-side by the atom walk).  Serial inequality
alone is never a difference. -/
def DifferX (a b : HX) : Prop :=
  (a.1 = 0 ∧ a.2 < p ∧ (b.1 = 1 ∨ b.1 = 2)) ∨ (b.1 = 0 ∧ b.2 < p ∧ (a.1 = 1 ∨ a.1 = 2)) ∨
  (a.1 = 1 ∧ b.1 = 2) ∨ (a.1 = 2 ∧ b.1 = 1) ∨ (a.1 = 0 ∧ b.1 = 0 ∧ a.2 ≠ b.2) ∨
  (∃ n1 n2 : ℕ, D a = some (.atom n1) ∧ D b = some (.atom n2) ∧ n1 ≠ n2)

/-- **OP5**: "=" by handle equality; "≠" by `DifferX` of the results or of the first-difference
leaves at a common axis. -/
def Op5SemX (r : RowVSX) : Prop :=
  (r.sf1 = r.sf2 ∧ r.e = (0, 0)) ∨
  (r.e = (0, 1) ∧
    (DifferX p D r.sf1 r.sf2 ∨
     ∃ (ax : ℕ) (X1 X2 A1 A2 : Noun), D r.sf1 = some X1 ∧ D r.sf2 = some X2 ∧
       Noun.slot ax X1 = some A1 ∧ Noun.slot ax X2 = some A2 ∧ D r.ftth = some A1 ∧
       D r.fttt = some A2 ∧ DifferX p D r.ftth r.fttt))

/-- **The J-8 row semantics on denotations.** -/
def RowSemX0 (R : Registry) (r : RowVSX) : Prop :=
  match r.st with
  | .s0 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 0) ∧ ∃ ax : ℕ, r.ft = (0, ax) ∧
      ((ax = 1 ∧ r.e = r.s) ∨ ∃ S E, D r.s = some S ∧ D r.e = some E ∧ Noun.slot ax S = some E)
  | .s1 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 1) ∧ r.e = r.ft
  | .s2 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 2) ∧ Cell3 D r.ft r.fth r.ftt
  | .s3 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 3) ∧
      (((∃ A B, D r.sf1 = some (.cell A B)) ∧ r.e = (0, 0)) ∨
        ((r.sf1.1 = 0 ∨ r.sf1.1 = 2) ∧ r.e = (0, 1)))
  | .s4 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 4) ∧
      ∃ n : ℕ, D r.sf1 = some (.atom n) ∧ D r.e = some (.atom (n + 1))
  | .s5 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 5) ∧ Cell3 D r.ft r.fth r.ftt ∧ Op5SemX p D r
  | .s6 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 6) ∧ Cell3 D r.ft r.fth r.ftt ∧
      Cell3 D r.ftt r.ftth r.fttt ∧
      ∃ c : ℕ, (c = 0 ∨ c = 1) ∧ r.sf2 = (0, c) ∧ r.m = (if c = 0 then r.ftth else r.fttt) ∧
        r.e = r.sf1
  | .s7 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 7) ∧ Cell3 D r.ft r.fth r.ftt ∧ r.e = r.sf1
  | .s8 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 8) ∧ Cell3 D r.ft r.fth r.ftt ∧
      Cell3 D r.m r.sf2 r.s ∧ r.e = r.sf1
  | .s9 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 9) ∧ Cell3 D r.ft r.fth r.ftt ∧
      (∃ ax : ℕ, r.fth = (0, ax) ∧
        ((ax = 1 ∧ r.m = r.sf1) ∨ ∃ C A, D r.sf1 = some C ∧ D r.m = some A ∧
          Noun.slot ax C = some A)) ∧ r.e = r.sf2
  | .cons => Cell3 D r.f r.fh r.ft ∧ r.fh.1 = 1 ∧ Cell3 D r.e r.sf1 r.sf2
  | .s10 => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 10) ∧ Cell3 D r.ft r.fth r.ftt ∧
      Cell3 D r.fth r.ftth r.fttt ∧ ∃ a : ℕ, r.ftth = (0, a) ∧
        ((a = 1 ∧ r.e = r.sf1) ∨ ∃ E N, D r.e = some E ∧ D r.sf1 = some N ∧ Noun.slot a E = some N)
  | .s10L => ∃ a : ℕ, r.f = (0, a) ∧ 2 ≤ a ∧ ∃ S E x, D r.s = some S ∧ D r.e = some E ∧
      Noun.slot (a ^^^ 1) S = some x ∧ Noun.slot (a ^^^ 1) E = some x
  | .s10T => r.f = (0, 1)
  | .s11s => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 11) ∧ Cell3 D r.ft r.fth r.ftt ∧
      ∃ b : ℕ, D r.fth = some (.atom b)
  | .s11d => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 11) ∧ Cell3 D r.ft r.fth r.ftt ∧
      Cell3 D r.fth r.ftth r.fttt
  | .s11j => Cell3 D r.f r.fh r.ft ∧ r.fh = (0, 11) ∧ Cell3 D r.ft r.fth r.ftt ∧
      Cell3 D r.fth r.ftth r.fttt ∧ ∃ (id : ℕ) (j : JetSpec), r.sf1 = (0, id) ∧ R id = some j ∧
        D r.ftt = some j.c ∧ ∃ S E, D r.s = some S ∧ D r.e = some E ∧ j.T.rel S E

/-- **The kid-kind clause**: every REAL child position's formula handle is a cell (wire kind `1`).
Part 1 carried it as a premise of `RowsOKX` (the FINDING `kidKinds_load_bearing`); since C-2 part 2
it is what `computeChipVCLHX`'s kid-kind gates `st · (1 − kc(h)) = 0` say
(`ChipHX.kid_cell`, `RowDecodeVSX.kidKinds_of_gates`), so it is a clause of the row semantics. -/
def KidKinds (r : RowVSX) : Prop :=
  ∀ i (h : i < (kidsX r).length), chainPosX r.st i = false → ((kidsX r)[i]'h).2.1.1 = 1

/-- **The J-8 row semantics** (C-2 part 2): the per-state clauses `RowSemX0` and the kid-kind
clause, both read off the gates and the served, genuine records. -/
def RowSemX (R : Registry) (r : RowVSX) : Prop := RowSemX0 p D R r ∧ KidKinds r

def nd (h : HX) : Noun := (D h).getD (.atom 0)

/-- The `RowX` a row denotes. -/
def rx (r : RowVSX) : RowX := ⟨r.st, nd D r.s, nd D r.f, nd D r.e⟩

end Sem

/-! ## 2. Local lemmas -/

section Local
variable {p : ℕ} {D : HX → Option Noun}

theorem nd_of {h : HX} {X : Noun} (hX : D h = some X) : nd D h = X := by simp [nd, hX]

/-- What `D` satisfies (as the decoded cell table + atom table do). -/
structure DenOKX (p : ℕ) (D : HX → Option Noun) : Prop where
  atom : ∀ v, D (0, v) = some (.atom v)
  cell : ∀ i X, D (1, i) = some X → ∃ a b, X = .cell a b
  big : ∀ i X, D (2, i) = some X → ∃ n, X = .atom n ∧ p ≤ n

theorem atom_nd (hD : DenOKX p D) (v : ℕ) : nd D (0, v) = .atom v := nd_of (hD.atom v)

theorem cell3_of {a b c : HX} (h : Cell3 D a b c) : nd D a = .cell (nd D b) (nd D c) := by
  obtain ⟨A, B, ha, hb, hc⟩ := h
  rw [nd_of ha, nd_of hb, nd_of hc]

theorem ne_none_of {h : HX} {X : Noun} (hX : D h = some X) : D h ≠ none := by simp [hX]

theorem cell3_ne {a b c : HX} (h : Cell3 D a b c) : D a ≠ none ∧ D b ≠ none ∧ D c ≠ none := by
  obtain ⟨A, B, ha, hb, hc⟩ := h
  exact ⟨ne_none_of ha, ne_none_of hb, ne_none_of hc⟩

/-- A `Cell3` parent handle is never a small atom. -/
theorem cell3_kind (hD : DenOKX p D) {a b c : HX} (h : Cell3 D a b c) : a.1 ≠ 0 := by
  obtain ⟨A, B, ha, -, -⟩ := h
  intro h0
  obtain ⟨k, v⟩ := a
  simp only at h0; subst h0
  rw [hD.atom] at ha; cases ha

/-- **`DifferX` certifies noun inequality.** -/
theorem differX_ne (hD : DenOKX p D) {a b : HX} {X Y : Noun} (hX : D a = some X)
    (hY : D b = some Y) (h : DifferX p D a b) : X ≠ Y := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  rcases h with ⟨h0, hv, h12⟩ | ⟨h0, hv, h12⟩ | ⟨h1, h2⟩ | ⟨h2, h1⟩ | ⟨h0, h0', hne⟩ |
      ⟨n1, n2, h1, h2, hne⟩
  · subst h0; rw [hD.atom] at hX; cases hX
    rcases h12 with rfl | rfl
    · obtain ⟨u, w, rfl⟩ := hD.cell _ _ hY; simp
    · obtain ⟨n, rfl, hn⟩ := hD.big _ _ hY
      intro h; cases h; omega
  · subst h0; rw [hD.atom] at hY; cases hY
    rcases h12 with rfl | rfl
    · obtain ⟨u, w, rfl⟩ := hD.cell _ _ hX; simp
    · obtain ⟨n, rfl, hn⟩ := hD.big _ _ hX
      intro h; cases h; omega
  · subst h1; subst h2
    obtain ⟨u, w, rfl⟩ := hD.cell _ _ hX
    obtain ⟨n, rfl, -⟩ := hD.big _ _ hY
    simp
  · subst h1; subst h2
    obtain ⟨u, w, rfl⟩ := hD.cell _ _ hY
    obtain ⟨n, rfl, -⟩ := hD.big _ _ hX
    simp
  · subst h0; subst h0'
    rw [hD.atom] at hX hY; cases hX; cases hY
    intro h; exact hne (Noun.atom.inj h)
  · rw [hX] at h1; rw [hY] at h2
    cases h1; cases h2
    intro h; exact hne (Noun.atom.inj h)

theorem slot_ne {ax : ℕ} {X1 X2 A1 A2 : Noun} (h1 : Noun.slot ax X1 = some A1)
    (h2 : Noun.slot ax X2 = some A2) (hne : A1 ≠ A2) : X1 ≠ X2 := by
  intro h; subst h; rw [h1] at h2; exact hne (Option.some.inj h2)

theorem slot_one (X : Noun) : Noun.slot 1 X = some X := by simp [Noun.slot]

/-- A row's chain-ness is read off its own formula handle's kind. -/
theorem chain_iff_kind (hD : DenOKX p D) {R : Registry} {r : RowVSX} (h : RowSemX0 p D R r) :
    r.st.isChain = true ↔ r.f.1 = 0 := by
  cases hst : r.st <;> simp only [RowSemX0, hst] at h <;> simp only [hst, StateX.isChain, true_iff,
    false_iff, Bool.false_eq_true, not_false_eq_true, Bool.true_eq_false]
  all_goals first
    | exact cell3_kind hD h.1
    | (obtain ⟨a, hf, -⟩ := h; rw [hf])
    | (rw [h])

/-- Chain positions carry a small-atom formula handle. -/
theorem chainPos_kind {R : Registry} {r : RowVSX} (h : RowSemX0 p D R r) (i : ℕ)
    (hi : i < (kidsX r).length) (hc : chainPosX r.st i = true) : ((kidsX r)[i]'hi).2.1.1 = 0 := by
  rcases i with _ | _ | _ | i <;> cases hst : r.st <;> simp [chainPosX, hst] at hc <;>
    simp only [kidsX, hst]
  · simp
  · simp only [RowSemX0, hst] at h
    obtain ⟨-, -, -, -, a, ha, -⟩ := h
    simp [ha]

/-- **The roles** (E-0's `roles` field): child `i` is a chain row iff `i` is a chain position. -/
theorem roles_of (hD : DenOKX p D) {R : Registry} {r : RowVSX} (h : RowSemX0 p D R r)
    (hkk : KidKinds r) (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hks : ∀ k ∈ ks, RowSemX0 p D R k) :
    ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i := by
  intro i hi
  have hlen : ks.length = (kidsX r).length := by rw [← hk, List.length_map]
  have hi' : i < (kidsX r).length := hlen ▸ hi
  have hfi : (ks[i]'hi).f = ((kidsX r)[i]'hi').2.1 := by
    have := congrArg (fun l => l[i]?) hk
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    rw [← this]; rfl
  have hc := chain_iff_kind hD (hks _ (List.getElem_mem hi))
  cases hpos : chainPosX r.st i
  · have := hkk i hi' hpos
    rw [← hfi] at this
    cases h' : (ks[i]'hi).st.isChain
    · rfl
    · have := hc.1 h'; omega
  · have := chainPos_kind h i hi' hpos
    rw [← hfi] at this
    exact hc.2 this

/-- **The local step** (C-2 step 1): a row satisfying `RowSemX0`, whose children carry its `kidsX`
labels, satisfy `RowSemX0` and have denoting results where real, obeys `FormulaShapeX`,
`KidInputsNX` and `RowOutputNX` on denotations. -/
theorem local_stepX (hD : DenOKX p D) {R : Registry} (r : RowVSX) (hsem : RowSemX0 p D R r)
    (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i)
    (hdef : ∀ k ∈ ks, k.st.isChain = false → D k.e ≠ none) :
    FormulaShapeX r.st (nd D r.f) ∧ KidInputsNX r.st (nd D r.s) (nd D r.f) (ks.map (rx D)) ∧
      RowOutputNX R r.st (nd D r.s) (nd D r.f) (ks.map (rx D)) (nd D r.e) := by
  cases hst : r.st <;> simp only [RowSemX0, hst] at hsem <;> simp only [kidsX, hst] at hk <;>
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, ks⟩⟩⟩⟩ <;>
    simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
      List.nil_eq, List.cons_ne_nil, RowVSX.trip, Prod.mk.injEq, and_true] at hk <;>
    simp only [FormulaShapeX, KidInputsNX, KidInputsX, RowOutputNX, List.map_cons, List.map_nil,
      rx]
  · -- s0
    obtain ⟨hf3, hfh, ax, hft, hcase⟩ := hsem
    have hF := cell3_of hf3
    rw [hfh, atom_nd hD, hft, atom_nd hD] at hF
    refine ⟨⟨ax, hF⟩, trivial, ?_⟩
    simp only [hF, op0Axis]
    rcases hcase with ⟨rfl, he⟩ | ⟨S, E, hS, hE, hsl⟩
    · rw [he]; exact slot_one _
    · rw [nd_of hS, nd_of hE]; exact hsl
  · -- s1
    obtain ⟨hf3, hfh, he⟩ := hsem
    have hF := cell3_of hf3
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, trivial, ?_⟩
    simp only [hF, he, tl, StrategyOfTraces.nounTail]
  · -- s2
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩, ⟨h2s, h2f, h2e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h0e, h1s, h1f, h1e, h2s, h2f, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h2e]
  · -- s3
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hf3, hfh, hcase⟩ := hsem
    have hF := cell3_of hf3
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, tl, StrategyOfTraces.nounTail, and_self]
    · simp only [h0e]
      rcases hcase with ⟨⟨A, B, hN⟩, he⟩ | ⟨hk1, he⟩
      · rw [nd_of hN, he, atom_nd hD]; rfl
      · have d0 := hdef k0 (List.mem_cons_self ..)
          (by simpa [chainPosX, hst] using hrole 0 (by simp))
        rw [h0e] at d0
        obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp d0
        rw [nd_of hX, he, atom_nd hD]
        rcases hk1 with hk1 | hk1
        · rw [show r.sf1 = (0, r.sf1.2) from Prod.ext hk1 rfl, hD.atom] at hX; cases hX; rfl
        · rw [show r.sf1 = (2, r.sf1.2) from Prod.ext hk1 rfl] at hX
          obtain ⟨n, rfl, -⟩ := hD.big _ _ hX; rfl
  · -- s4
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hf3, hfh, n, hN, he⟩ := hsem
    have hF := cell3_of hf3
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, tl, StrategyOfTraces.nounTail, and_self]
    · simp only [h0e, nd_of hN, nd_of he, Noun.lus]
  · -- s5
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, hop⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h0e, h1e]
      rcases hop with ⟨heq, he⟩ | ⟨he, hne⟩
      · rw [heq, he, atom_nd hD]; simp [Noun.tis]
      · have d1 := hdef k0 (List.mem_cons_self ..)
          (by simpa [chainPosX, hst] using hrole 0 (by simp))
        have d2 := hdef k1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (by simpa [chainPosX, hst] using hrole 1 (by simp))
        rw [h0e] at d1; rw [h1e] at d2
        obtain ⟨X1, hX1⟩ := Option.ne_none_iff_exists'.mp d1
        obtain ⟨X2, hX2⟩ := Option.ne_none_iff_exists'.mp d2
        have hX : X1 ≠ X2 := by
          rcases hne with hd' | ⟨ax, Y1, Y2, A1, A2, hY1, hY2, hs1, hs2, hA1, hA2, hdA⟩
          · exact differX_ne hD hX1 hX2 hd'
          · rw [hX1] at hY1; rw [hX2] at hY2
            cases Option.some.inj hY1; cases Option.some.inj hY2
            exact slot_ne hs1 hs2 (differX_ne hD hA1 hA2 hdA)
        rw [he, atom_nd hD, nd_of hX1, nd_of hX2]
        simp [Noun.tis, hX]
  · -- s6
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, htt3, c, hc, hsf2, hm, he⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hTT := cell3_of htt3
    rw [hTT] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, h1e, hsf2, atom_nd hD, condBit, hm, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, true_and]
      rcases hc with rfl | rfl <;> simp
    · simp only [h0e, h1e, hsf2, atom_nd hD, he]
      rcases hc with rfl | rfl <;> simp
  · -- s7
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, he⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, h1e, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h0e, he]
  · -- s8
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, hm3, he⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hM := cell3_of hm3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, h1e, hM, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h0e, he]
  · -- s9
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, ⟨ax, hth, hcase⟩, he⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    rw [hth, atom_nd hD] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h0e, h1s, h1f, op9Axis, tl, StrategyOfTraces.nounTail, true_and]
      rcases hcase with ⟨rfl, hm⟩ | ⟨C, A, hC, hA, hsl⟩
      · rw [hm]; exact slot_one _
      · rw [nd_of hC, nd_of hA]; exact hsl
    · simp only [h1e, he]
  · -- cons
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hk1, he3⟩ := hsem
    have hF := cell3_of hf3
    have hE := cell3_of he3
    obtain ⟨a, b, hab⟩ : ∃ a b, nd D r.fh = .cell a b := by
      obtain ⟨Fh, Ft, -, hfhD, -⟩ := hf3
      have hfe : r.fh = (1, r.fh.2) := Prod.ext hk1 rfl
      rw [hfe] at hfhD
      obtain ⟨a, b, rfl⟩ := hD.cell _ _ hfhD
      exact ⟨a, b, by rw [hfe]; exact nd_of hfhD⟩
    refine ⟨⟨a, b, _, by rw [hF, hab]⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h0e, h1e, hE]
  · -- s10
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩, ⟨h2s, h2f, h2e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, hth3, a, ha, hcase⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hTH := cell3_of hth3
    rw [ha, atom_nd hD] at hTH
    rw [hTH] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨a, _, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, h1e, h2s, h2f, ha, atom_nd hD, op10Axis, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [hF, h0e, h2e, op10Axis, and_true]
      rcases hcase with ⟨rfl, he⟩ | ⟨E, N, hE, hN, hsl⟩
      · rw [he]; exact slot_one _
      · rw [nd_of hE, nd_of hN]; exact hsl
  · -- s10L
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨a, hf, ha, S, E, x, hS, hE, hx1, hx2⟩ := hsem
    rw [hf, atom_nd hD]
    refine ⟨⟨a, rfl, ha⟩, ?_, ?_⟩
    · simp only [h0s, h0f, chainAxis, hf, atom_nd hD, and_self]
    · simp only [h0e, chainAxis, true_and]
      exact ⟨x, by rw [nd_of hS]; exact hx1, by rw [nd_of hE]; exact hx2⟩
  · -- s10T
    rw [hsem, atom_nd hD]
    exact ⟨rfl, trivial, trivial⟩
  · -- s11s
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hf3, hfh, ht3, b, hb⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    rw [nd_of hb] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨b, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, tl, StrategyOfTraces.nounTail, and_self]
    · simp only [h0e]
  · -- s11d
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, hth3⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hTH := cell3_of hth3
    rw [hTH] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, hd, tl, StrategyOfTraces.nounHead,
        StrategyOfTraces.nounTail, and_self]
    · simp only [h1e]
  · -- s11j
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hf3, hfh, ht3, hth3, id, j, hkey, hj, hc, S, E, hS, hE, hrel⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hTH := cell3_of hth3
    rw [hTH] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail,
        and_self]
    · refine ⟨id, j, ?_, hj, ?_, ?_⟩
      · simp only [h0e, hkey, atom_nd hD]
      · simp only [hF, tl, StrategyOfTraces.nounTail, nd_of hc]
      · rw [nd_of hS, nd_of hE]; exact hrel

/-- **Weakened `state_of_formula` (SPEC §3.1)**: one formula fixes the state, except that `s11d`
and `s11j` share their shape (the registry decides; both conclude the same `HoldsN`). -/
theorem state_of_formulaX {st1 st2 : StateX} {f : Noun} (h1 : FormulaShapeX st1 f)
    (h2 : FormulaShapeX st2 f) :
    st1 = st2 ∨ (st1 = .s11d ∧ st2 = .s11j) ∨ (st1 = .s11j ∧ st2 = .s11d) := by
  cases st1 <;> cases st2 <;> simp only [FormulaShapeX, FormulaShape] at h1 h2 <;>
    simp only [reduceCtorEq, false_or, or_false, true_or, and_self, and_true, true_and] <;>
    first
    | (obtain ⟨w, rfl, hw⟩ := h1; simp at h2; omega)
    | (obtain ⟨_, rfl⟩ := h1; simp at h2)
    | (obtain ⟨_, _, rfl⟩ := h1; simp at h2)
    | (obtain ⟨_, _, _, rfl⟩ := h1; simp at h2)
    | (obtain ⟨_, rfl, _⟩ := h1; simp at h2)

/-- **The per-row definedness step**: the row's subject denotes, and every REAL child whose
subject denotes has a denoting result; then every child subject denotes, and (on a real row) the
result denotes. -/
theorem defined_stepX (hD : DenOKX p D) {R : Registry} (r : RowVSX) (hsem : RowSemX0 p D R r)
    (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i)
    (hs : D r.s ≠ none)
    (hch : ∀ k ∈ ks, k.st.isChain = false → D k.s ≠ none → D k.e ≠ none) :
    (∀ k ∈ ks, D k.s ≠ none) ∧ (r.st.isChain = false → D r.e ≠ none) := by
  cases hst : r.st <;> simp only [RowSemX0, hst] at hsem <;> simp only [kidsX, hst] at hk <;>
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, ks⟩⟩⟩⟩ <;>
    simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
      List.nil_eq, List.cons_ne_nil, RowVSX.trip, Prod.mk.injEq, and_true] at hk <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, true_and, hst, StateX.isChain, Bool.false_eq_true,
      false_implies, and_true, forall_const, Bool.true_eq_false]
  · obtain ⟨-, -, ax, -, h | ⟨S, E, -, hE, -⟩⟩ := hsem
    · exact h.2 ▸ hs
    · exact ne_none_of hE
  · rw [hsem.2.2]; exact (cell3_ne hsem.1).2.2
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, h1e⟩, ⟨h2s, -, h2e⟩⟩ := hk
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hs)
    have e2 := hch k2 (by simp) (by simpa [chainPosX, hst] using hrole 2 (by simp))
      (by rw [h2s, ← h0e]; exact e0)
    exact ⟨⟨h0s ▸ hs, h1s ▸ hs, h2s ▸ h0e ▸ e0⟩, h2e ▸ e2⟩
  · obtain ⟨h0s, -, -⟩ := hk
    obtain ⟨-, -, ⟨-, he⟩ | ⟨-, he⟩⟩ := hsem <;> exact ⟨h0s ▸ hs, by rw [he, hD.atom]; simp⟩
  · obtain ⟨h0s, -, -⟩ := hk
    obtain ⟨-, -, n, -, hN⟩ := hsem; exact ⟨h0s ▸ hs, ne_none_of hN⟩
  · obtain ⟨⟨h0s, -, -⟩, ⟨h1s, -, -⟩⟩ := hk
    refine ⟨⟨h0s ▸ hs, h1s ▸ hs⟩, ?_⟩
    obtain ⟨-, -, -, ⟨-, he⟩ | ⟨he, -⟩⟩ := hsem <;> rw [he, hD.atom] <;> simp
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, -⟩⟩ := hk
    obtain ⟨-, -, -, -, c, -, -, -, he⟩ := hsem
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hs)
    exact ⟨⟨h0s ▸ hs, h1s ▸ hs⟩, he ▸ h0e ▸ e0⟩
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, h1e⟩⟩ := hk
    obtain ⟨-, -, -, he⟩ := hsem
    have e1 := hch k1 (by simp) (by simpa [chainPosX, hst] using hrole 1 (by simp))
      (by rw [h1s]; exact hs)
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s, ← h1e]; exact e1)
    exact ⟨⟨h0s ▸ h1e ▸ e1, h1s ▸ hs⟩, he ▸ h0e ▸ e0⟩
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, -⟩⟩ := hk
    obtain ⟨-, -, -, hm, he⟩ := hsem
    have hm' := (cell3_ne hm).1
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hm')
    exact ⟨⟨h0s ▸ hm', h1s ▸ hs⟩, he ▸ h0e ▸ e0⟩
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, h1e⟩⟩ := hk
    obtain ⟨-, -, -, -, he⟩ := hsem
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hs)
    have e1 := hch k1 (by simp) (by simpa [chainPosX, hst] using hrole 1 (by simp))
      (by rw [h1s, ← h0e]; exact e0)
    exact ⟨⟨h0s ▸ hs, h1s ▸ h0e ▸ e0⟩, he ▸ h1e ▸ e1⟩
  · obtain ⟨⟨h0s, -, -⟩, ⟨h1s, -, -⟩⟩ := hk
    exact ⟨⟨h0s ▸ hs, h1s ▸ hs⟩, (cell3_ne hsem.2.2).1⟩
  · obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, h1e⟩, ⟨h2s, -, -⟩⟩ := hk
    obtain ⟨-, -, -, -, a, -, hcase⟩ := hsem
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hs)
    have e1 := hch k1 (by simp) (by simpa [chainPosX, hst] using hrole 1 (by simp))
      (by rw [h1s]; exact hs)
    refine ⟨⟨h0s ▸ hs, h1s ▸ hs, h2s ▸ h1e ▸ e1⟩, ?_⟩
    rcases hcase with ⟨-, he⟩ | ⟨E, N, hE, -, -⟩
    · exact he ▸ h0e ▸ e0
    · exact ne_none_of hE
  · obtain ⟨h0s, -, -⟩ := hk; exact h0s ▸ hs
  · obtain ⟨h0s, -, h0e⟩ := hk
    have e0 := hch k0 (by simp) (by simpa [chainPosX, hst] using hrole 0 (by simp))
      (by rw [h0s]; exact hs)
    exact ⟨h0s ▸ hs, h0e ▸ e0⟩
  · obtain ⟨⟨h0s, -, -⟩, ⟨h1s, -, h1e⟩⟩ := hk
    have e1 := hch k1 (by simp) (by simpa [chainPosX, hst] using hrole 1 (by simp))
      (by rw [h1s]; exact hs)
    exact ⟨⟨h0s ▸ hs, h1s ▸ hs⟩, h1e ▸ e1⟩
  · obtain ⟨h0s, -, -⟩ := hk
    obtain ⟨-, -, -, -, -, -, -, -, -, S, E, -, hE, -⟩ := hsem
    exact ⟨h0s ▸ hs, ne_none_of hE⟩

end Local

/-! ## 3. The tree -/

section Tree
variable {p : ℕ} {D : HX → Option Noun} {R : Registry} {L : Type} (rw : L → RowVSX)

/-- Relabel a tree (as `ExactTraversal.mapNTree`, kept local to stay import-light). -/
def mapT {α β : Type} (g : α → β) : NTree α → NTree β
  | .node l cs => .node (g l) (cs.map (mapT g))

@[simp] theorem mapT_label {α β : Type} (g : α → β) (t : NTree α) : (mapT g t).label = g t.label := by
  cases t; simp [mapT, NTree.label]

@[simp] theorem mapT_children {α β : Type} (g : α → β) (t : NTree α) :
    (mapT g t).children = t.children.map (mapT g) := by
  cases t; simp [mapT, NTree.children]

theorem inTree_trans {t u w : NTree L} (h1 : InTree t u) (h2 : InTree u w) : InTree t w := by
  induction h1 with
  | here => exact h2
  | sub hs _ ih => exact InTree.sub hs (ih h2)

/-- **The tree hypotheses**: every node satisfies `RowSemX` (its gate semantics, the kid-kind
clause included: no separate premise since C-2 part 2), and its children carry exactly its `kidsX`
labels (`(s, f, e)` only: tag-free). -/
structure RowsOKX (p : ℕ) (D : HX → Option Noun) (R : Registry) (t : NTree L) : Prop where
  sem : ∀ u, InTree t u → RowSemX p D R (rw u.label)
  link : ∀ u, InTree t u → u.children.map (fun c => (rw c.label).trip) = kidsX (rw u.label)

theorem RowsOKX.sub {t : NTree L} (h : RowsOKX rw p D R t) {c : NTree L} (hc : c ∈ t.children) :
    RowsOKX rw p D R c :=
  ⟨fun u hu => h.sem u (InTree.sub hc hu), fun u hu => h.link u (InTree.sub hc hu)⟩

theorem RowsOKX.kids {t : NTree L} (h : RowsOKX rw p D R t) {u : NTree L} (hu : InTree t u) :
    (u.children.map fun c => rw c.label).map RowVSX.trip = kidsX (rw u.label) := by
  rw [List.map_map]; exact h.link u hu

theorem RowsOKX.kidSem {t : NTree L} (h : RowsOKX rw p D R t) {u : NTree L} (hu : InTree t u) :
    ∀ k ∈ u.children.map (fun c => rw c.label), RowSemX0 p D R k := by
  intro k hk
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
  exact (h.sem c (inTree_trans hu (InTree.sub hc (InTree.here _)))).1

theorem RowsOKX.roles (hD : DenOKX p D) {t : NTree L} (h : RowsOKX rw p D R t) {u : NTree L}
    (hu : InTree t u) :
    ∀ i (hi : i < (u.children.map fun c => rw c.label).length),
      ((u.children.map fun c => rw c.label)[i]'hi).st.isChain = chainPosX (rw u.label).st i :=
  roles_of hD (h.sem u hu).1 (h.sem u hu).2 _ (h.kids rw hu) (h.kidSem rw hu)

/-- **Definedness**: once the root subject denotes, every node's subject denotes and every real
node's result denotes. -/
theorem defined_treeX (hD : DenOKX p D) : ∀ t : NTree L, RowsOKX rw p D R t →
    D (rw t.label).s ≠ none → ∀ u, InTree t u →
      D (rw u.label).s ≠ none ∧ ((rw u.label).st.isChain = false → D (rw u.label).e ≠ none)
  | .node l cs, h, hs => by
    have ih : ∀ c ∈ cs, D (rw c.label).s ≠ none → ∀ u, InTree c u →
        D (rw u.label).s ≠ none ∧ ((rw u.label).st.isChain = false → D (rw u.label).e ≠ none) :=
      fun c hc => defined_treeX hD c (h.sub rw (by simpa [NTree.children] using hc))
    have hu0 : InTree (NTree.node l cs) (NTree.node l cs) := InTree.here _
    have step := defined_stepX hD (rw l) (h.sem _ hu0).1 (cs.map fun c => rw c.label)
      (h.kids rw hu0) (h.roles rw hD hu0) hs (by
        intro k hk hc hks
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
        exact (ih c hc' hks c (InTree.here _)).2 hc)
    intro u hu
    cases hu with
    | here => exact ⟨hs, step.2⟩
    | sub hc hu' =>
      exact ih _ hc (step.1 _ (List.mem_map_of_mem hc)) u hu'

/-- A tree whose every node meets `GenuineNX`'s local clauses is `GenuineNX`. -/
theorem genuine_of_local (g : L → RowX) : ∀ t : NTree L,
    (∀ u, InTree t u →
      FormulaShapeX (g u.label).state (g u.label).formula ∧
      KidInputsNX (g u.label).state (g u.label).subject (g u.label).formula
        (u.children.map fun c => g c.label) ∧
      RowOutputNX R (g u.label).state (g u.label).subject (g u.label).formula
        (u.children.map fun c => g c.label) (g u.label).evaluation ∧
      ∀ i (hi : i < u.children.length),
        (g (u.children[i]'hi).label).state.isChain = chainPosX (g u.label).state i) →
    GenuineNX R (mapT g t)
  | .node l cs, h => by
    obtain ⟨hsh, hin, hout, hrole⟩ := h _ (InTree.here _)
    simp only [NTree.label_node, NTree.children_node] at hsh hin hout hrole
    rw [show mapT g (NTree.node l cs) = NTree.node (g l) (cs.map (mapT g)) by simp [mapT]]
    refine GenuineNX.node hsh ?_ ?_ ?_ ?_
    · simpa [List.map_map, Function.comp_def] using hin
    · simpa [List.map_map, Function.comp_def] using hout
    · intro i hi
      simp only [List.length_map] at hi
      simpa using hrole i hi
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact genuine_of_local g c (fun u hu => h u (InTree.sub (by simpa using hc) hu))

/-- **`GenuineNX` of the decoded tree** (C-2 step 1 at the tree level). -/
theorem genuineNX_of_rowsX (hD : DenOKX p D) (t : NTree L) (h : RowsOKX rw p D R t)
    (hs : D (rw t.label).s ≠ none) : GenuineNX R (mapT (fun l => rx D (rw l)) t) := by
  refine genuine_of_local (fun l => rx D (rw l)) t (fun u hu => ?_)
  have hk := h.kids rw hu
  have hdef : ∀ k ∈ u.children.map (fun c => rw c.label), k.st.isChain = false → D k.e ≠ none := by
    intro k hk' hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk'
    exact (defined_treeX rw hD t h hs c (inTree_trans hu (InTree.sub hc' (InTree.here _)))).2 hc
  have key := local_stepX hD (rw u.label) (h.sem u hu).1 _ hk (h.roles rw hD hu) hdef
  rw [List.map_map] at key
  refine ⟨key.1, key.2.1, key.2.2, fun i hi => ?_⟩
  have := h.roles rw hD hu i (by simpa using hi)
  simpa [rx] using this

/-- **The claim from a decoded row tree (C-2 step 1, closed over `HoldsN`)**: a row tree with
`RowsOKX`, a real root, and root handles denoting the claim's nouns proves `HoldsN` of the claim,
for a faithful registry. -/
theorem holdsN_of_rowsVSX (hR : R.Faithful) (hD : DenOKX p D) (t : NTree L)
    (h : RowsOKX rw p D R t) (hreal : (rw t.label).st.isChain = false) (x : P8PublicClaim)
    (hs : D (rw t.label).s = some x.subject) (hf : D (rw t.label).f = some x.formula)
    (he : D (rw t.label).e = some x.result) : HoldsN x := by
  have hG := genuineNX_of_rowsX rw hD t h (by simp [hs])
  refine holdsN_of_genuineNX hR hG ?_ ?_ ?_ ?_ <;> simp [rx, hreal, nd_of hs, nd_of hf, nd_of he]

end Tree

/-! ## 4. The FINDING: the kid-kind premise is load-bearing -/

/-- A denotation: small atoms denote themselves, serial `1·0` the cell `[4 1]`. -/
def ncD : HX → Option Noun := fun h =>
  if h.1 = 0 then some (.atom h.2) else if h = (1, 0) then some (.cell (.atom 4) (.atom 1)) else none

/-- An OP4 row `*[0 [4 1]] = 7` whose child `(0, 1, 6)` is an `s10T` pseudo-row. -/
def ncRow : RowVSX :=
  ⟨.s4, (0, 0), (1, 0), (0, 7), (0, 6), (0, 0), (0, 4), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0)⟩
def ncKid : RowVSX :=
  ⟨.s10T, (0, 0), (0, 1), (0, 6), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0)⟩

/-- **FINDING, compiled at the noun level**: both rows satisfy `RowSemX0`, the link holds, `D` is
`DenOKX`, yet `*[0 [4 1]]` crashes, so the claim `HoldsN ⟨0, [4 1], 7⟩` is FALSE; the only clause
of `RowsOKX` that fails is `KidKinds` (the child formula handle `(0, 1)` is a small atom).
Since C-2 part 2 the kid-kind clause is part of `RowSemX`, so the parent row fails `RowSemX`
(the conjunct `¬ RowSemX`), and at the chip `ChipHX.swapped_s10T_child_rejected` rejects it. -/
theorem kidKinds_load_bearing (p : ℕ) (R : Registry) :
    DenOKX p ncD ∧ RowSemX0 p ncD R ncRow ∧ RowSemX0 p ncD R ncKid ∧
      [ncKid].map RowVSX.trip = kidsX ncRow ∧ ¬ KidKinds ncRow ∧ ¬ RowSemX p ncD R ncRow ∧
      ¬ HoldsN ⟨.atom 0, .cell (.atom 4) (.atom 1), .atom 7⟩ := by
  have hnk : ¬ KidKinds ncRow := by
    intro h
    have := h 0 (by simp [kidsX, ncRow]) (by simp [chainPosX, ncRow])
    simp [kidsX, ncRow] at this
  refine ⟨⟨fun v => by simp [ncD], fun i X h => ?_, fun i X h => by simp [ncD] at h⟩,
    ⟨⟨.atom 4, .atom 1, by simp [ncD, ncRow], by simp [ncD, ncRow], by simp [ncD, ncRow]⟩, rfl, 6,
      by simp [ncD, ncRow], by simp [ncD, ncRow]⟩, rfl, rfl, hnk, fun h => hnk h.2, ?_⟩
  · simp only [ncD] at h
    by_cases hi : i = 0
    · subst hi; simp at h; exact ⟨_, _, h.symm⟩
    · simp [hi] at h
  · rintro ⟨fuel, hf⟩
    rcases fuel with _ | _ | fuel <;> simp [evalN] at hf

end Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
