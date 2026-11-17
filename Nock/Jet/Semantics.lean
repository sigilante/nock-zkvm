/-
  Nock/Jet/Semantics.lean

  **The semantics of the generic jet `J` on op 11.**

  * **§A `HoldsN`**: the ℕ-Nock claim predicate, run under `Nock.evalN`.
  * **§B `Template`, `JetSpec`, `Registry`.**  `args T s` reads the axes from the subject (all must exist).  A `JetSpec` is a
    template plus the registered Nock formula `c`; `Registry := ℕ → Option JetSpec`.
  * `JetSpec.faithful_iff`: an entry is
    faithful iff `T.rel s r ↔ HoldsN ⟨s, c, r⟩` for every `s r`.
  * **§D `evalN_hint_jet`** — `*[s [11 [id d] c]]`: `d` is evaluated and discarded, the result is
    `*[s c]`; a crashing `d` crashes the call (the op-11 arm of `Reference.lean`).  The
    `HoldsN` form `holdsN_hint_iff`, and the registry lemmas `registry_hint_holdsN` /
    `registry_hint_rel` / `registry_hint_iff`: a faithful entry's relation gives (and is given by)
    the `evalN` result of the hinted formula, provided the clue computes.
  * **§E the `s11j` row specs, standalone** — `FormulaShapeJ`, `KidInputsJ`
    (one child: `(s, d)`), `RowOutputJ R` (the row's output is grounded by a registry entry whose
    `c` is the hinted body and whose relation holds), with `rowJ_holdsN` (kid computed + faithful
    registry ⇒ `HoldsN` of the row), `rowOutputJ_unique`, `rowOutputJ_of_holdsN` (honest side).
  * **§F toys** — a two-argument `swap` jet (`c = [[0 3] [0 2]]`, axes `2, 3`) with its faithfulness
    proof, the one-entry registry `toyR` (id `7`), the hinted program
    `*[[5 6] [11 [7 [1 42]] [[0 3] [0 2]]]] = [6 5]` derived from the registry, its uniqueness, and
    the negative control: with a crashing clue the relation still holds but `HoldsN` fails, so the
    kid hypothesis of `rowJ_holdsN` is load-bearing.
-/
import Nock.NockVMROM.Thm54.SemanticStrategy

set_option autoImplicit false

namespace Nock.Jet

open Nock Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy

/-! ## §A `HoldsN` -/

/-- **The ℕ-Nock claim predicate**: the claim's formula, run on its subject
under the reference interpreter `Nock.evalN` (Nock 4K atoms, increment `n ↦ n + 1`), returns its
result at some fuel. -/
def HoldsN (x : P8PublicClaim) : Prop :=
  ∃ fuel, Nock.evalN fuel x.subject x.formula = some x.result

/-! ## §B Templates, jet specs, the registry -/

/-- A jet template: arity `k`, the subject axes of its arguments, and its extractable semantic
function on the arguments (`none` = outside the template's domain). -/
structure Template where
  k : ℕ
  ax : Fin k → ℕ
  sem : (Fin k → Noun) → Option Noun

/-- The template's arguments read from the subject by axis; `none` if some axis is missing. -/
def Template.args (T : Template) (s : Noun) : Option (Fin T.k → Noun) :=
  if h : ∀ i, (Noun.slot (T.ax i) s).isSome then
    some (fun i => (Noun.slot (T.ax i) s).get (h i))
  else none

/-- The template's semantics on a whole subject: read the arguments, apply `sem`. -/
def Template.semS (T : Template) (s : Noun) : Option Noun := (T.args s).bind T.sem

/-- The template relation on (subject, result): the graph of `semS`. -/
def Template.rel (T : Template) (s r : Noun) : Prop := T.semS s = some r

theorem Template.args_eq_some {T : Template} {s : Noun} {a : Fin T.k → Noun} :
    T.args s = some a ↔ ∀ i, Noun.slot (T.ax i) s = some (a i) := by
  unfold Template.args
  split_ifs with h
  · constructor
    · intro e i
      cases e
      exact (Option.some_get (h i)).symm
    · intro H
      congr 1
      funext i
      obtain ⟨_, hg⟩ := Option.eq_some_iff_get_eq.1 (H i)
      exact hg
  · constructor
    · intro e; cases e
    · intro H
      exact absurd (fun i => by simp [H i]) h

/-- The relation unfolded: the axes exist with values `a` and `sem a = some r`. -/
theorem Template.rel_iff {T : Template} {s r : Noun} :
    T.rel s r ↔ ∃ a : Fin T.k → Noun, (∀ i, Noun.slot (T.ax i) s = some (a i)) ∧ T.sem a = some r := by
  unfold Template.rel Template.semS
  rw [Option.bind_eq_some_iff]
  simp only [Template.args_eq_some]

/-- A template's evaluation relation is functional: one subject gives at most one result. -/
theorem Template.rel_functional {T : Template} {s r r' : Noun} (h : T.rel s r) (h' : T.rel s r') :
    r = r' :=
  Option.some.inj (h.symm.trans h')

/-- A registered jet: its template and the Nock formula `c` the registry binds to its id. -/
structure JetSpec where
  T : Template
  c : Noun

/-- The registry: hint id ↦ entry.  Verifier-fixed public data; never in the statement. -/
abbrev Registry := ℕ → Option JetSpec

/-! ## §C Faithfulness, against `evalN` only -/

/-- Soundness direction: every relation instance is an `evalN` run of `c`. -/
def Faithful (T : Template) (c : Noun) : Prop :=
  ∀ s r, T.rel s r → ∃ fuel, Nock.evalN fuel s c = some r

/-- Completeness direction: every successful `evalN` run of `c` is a relation instance. -/
def Complete (T : Template) (c : Noun) : Prop :=
  ∀ s fuel r, Nock.evalN fuel s c = some r → T.rel s r

/-- An entry is faithful: its relation is exactly the `evalN` semantics of its formula. -/
def JetSpec.Faithful (j : JetSpec) : Prop := Jet.Faithful j.T j.c ∧ Complete j.T j.c

/-- **`Faithful R`**: every registered entry is faithful. -/
def Registry.Faithful (R : Registry) : Prop := ∀ n j, R n = some j → j.Faithful

/-- An entry is faithful iff `T.rel ⟺ HoldsN` of its formula, pointwise. -/
theorem JetSpec.faithful_iff (j : JetSpec) :
    j.Faithful ↔ ∀ s r, j.T.rel s r ↔ HoldsN ⟨s, j.c, r⟩ := by
  constructor
  · rintro ⟨hF, hC⟩ s r
    exact ⟨hF s r, fun ⟨fuel, h⟩ => hC s fuel r h⟩
  · intro H
    exact ⟨fun s r h => (H s r).1 h, fun s fuel r h => (H s r).2 ⟨fuel, h⟩⟩

/-! ## §D The hinted call `[11 [id d] c]` under `evalN` -/

/-- The dynamic hint `[11 [id d] c]`. -/
def hint (id d c : Noun) : Noun := .cell (.atom 11) (.cell (.cell id d) c)

/-- The dynamic hint with an atomic tag `n`.  This is the EARLIER jet-call wire form, in which the
tag itself was the jet id; §D–§F below state that form.  The generator (`Nock/Edit/GenX.lean`)
now dispatches on the tag `%wild` with the id as the clue's value (`wildCall`), so a `jetCall`
is an ordinary dynamic hint there.  The `evalN` facts in §D hold for any dynamic hint. -/
def jetCall (n : ℕ) (d c : Noun) : Noun := hint (.atom n) d c

/-- **`evalN_hint_jet`**: if the clue `d` computes, the hinted call evaluates as its body `c`. -/
theorem evalN_hint_jet {fuel : ℕ} {s id d c v : Noun} (hd : Nock.evalN fuel s d = some v) :
    Nock.evalN (fuel + 1) s (hint id d c) = Nock.evalN fuel s c := by
  simp [hint, Nock.evalN, hd]

/-- A crashing clue crashes the call. -/
theorem evalN_hint_crash {fuel : ℕ} {s id d c : Noun} (hd : Nock.evalN fuel s d = none) :
    Nock.evalN (fuel + 1) s (hint id d c) = none := by
  simp [hint, Nock.evalN, hd]

theorem evalN_hint_some_iff {fuel : ℕ} {s id d c r : Noun} :
    Nock.evalN (fuel + 1) s (hint id d c) = some r ↔
      (∃ v, Nock.evalN fuel s d = some v) ∧ Nock.evalN fuel s c = some r := by
  cases hd : Nock.evalN fuel s d with
  | none => simp [evalN_hint_crash hd]
  | some v => simp [evalN_hint_jet (c := c) (id := id) hd]

/-- `HoldsN` of a hinted call: the clue computes and the body holds. -/
theorem holdsN_hint_iff {s id d c r : Noun} :
    HoldsN ⟨s, hint id d c, r⟩ ↔ (∃ fuel v, Nock.evalN fuel s d = some v) ∧ HoldsN ⟨s, c, r⟩ := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [Nock.evalN] at h
    | succ fuel =>
        obtain ⟨⟨v, hv⟩, hc⟩ := evalN_hint_some_iff.1 h
        exact ⟨⟨fuel, v, hv⟩, ⟨fuel, hc⟩⟩
  · rintro ⟨⟨f₁, v, hv⟩, ⟨f₂, hc⟩⟩
    refine ⟨max f₁ f₂ + 1, evalN_hint_some_iff.2 ⟨⟨v, ?_⟩, ?_⟩⟩
    · exact evalN_mono (Nat.le_max_left _ _) hv
    · exact evalN_mono (Nat.le_max_right _ _) hc

/-- **A faithful registry entry gives the `evalN` result of the hinted formula.** -/
theorem registry_hint_holdsN {R : Registry} (hR : Registry.Faithful R) {n : ℕ} {j : JetSpec}
    (hj : R n = some j) {s d r : Noun} (hd : ∃ fuel v, Nock.evalN fuel s d = some v)
    (hrel : j.T.rel s r) : HoldsN ⟨s, jetCall n d j.c, r⟩ :=
  holdsN_hint_iff.2 ⟨hd, (hR n j hj).1 s r hrel⟩

/-- Conversely, a successful run of the hinted formula is a relation instance. -/
theorem registry_hint_rel {R : Registry} (hR : Registry.Faithful R) {n : ℕ} {j : JetSpec}
    (hj : R n = some j) {s d r : Noun} (h : HoldsN ⟨s, jetCall n d j.c, r⟩) : j.T.rel s r := by
  obtain ⟨-, fuel, hc⟩ := holdsN_hint_iff.1 h
  exact (hR n j hj).2 s fuel r hc

theorem registry_hint_iff {R : Registry} (hR : Registry.Faithful R) {n : ℕ} {j : JetSpec}
    (hj : R n = some j) {s d r : Noun} :
    HoldsN ⟨s, jetCall n d j.c, r⟩ ↔ (∃ fuel v, Nock.evalN fuel s d = some v) ∧ j.T.rel s r :=
  ⟨fun h => ⟨(holdsN_hint_iff.1 h).1, registry_hint_rel hR hj h⟩,
   fun ⟨hd, hrel⟩ => registry_hint_holdsN hR hj hd hrel⟩

/-! ## §E The `s11j` row specs (standalone; not wired into `RowOutputF`)

These specs read the jet id from the hint's TAG (`f = jetCall n d j.c`).  They predate the
`%wild` form and do not describe the rows `Nock/Edit/GenX.lean` now generates; the live row
semantics is `RowNX.SemN` in `Nock/Edit/GenXRows.lean`. -/

/-- The clue `d` of `[11 [id d] c]` (junk `0` off shape). -/
def jetClue : Noun → Noun
  | .cell _ (.cell (.cell _ d) _) => d
  | _ => .atom 0

@[simp] theorem jetClue_jetCall (n : ℕ) (d c : Noun) : jetClue (jetCall n d c) = d := rfl

/-- `FormulaShape` arm for `s11j`: a dynamic hint with an atomic id. -/
def FormulaShapeJ (f : Noun) : Prop := ∃ (n : ℕ) (d c : Noun), f = jetCall n d c

/-- `KidInputs` arm for `s11j`: ONE child, the clue `(s, d)`; the body is not a child. -/
def KidInputsJ (s f : Noun) : List ComputeRowSkeleton → Prop
  | [k0] => k0.subject = s ∧ k0.formula = jetClue f
  | _ => False

/-- `RowOutputF` arm for `s11j`: the output is grounded by a registry entry whose formula is the
hinted body and whose relation holds on `(s, e)`.  Independent of the field characteristic. -/
def RowOutputJ (R : Registry) (s f : Noun) : List ComputeRowSkeleton → Noun → Prop
  | [_], e => ∃ (n : ℕ) (d : Noun) (j : JetSpec), f = jetCall n d j.c ∧ R n = some j ∧ j.T.rel s e
  | _, _ => False

theorem formulaShapeJ_of_rowOutputJ {R : Registry} {s f : Noun} {ks : List ComputeRowSkeleton}
    {e : Noun} (h : RowOutputJ R s f ks e) : FormulaShapeJ f := by
  rcases ks with _ | ⟨k0, _ | ⟨k1, ks⟩⟩
  · exact h.elim
  · obtain ⟨n, d, j, hf, -, -⟩ := h
    exact ⟨n, d, j.c, hf⟩
  · exact h.elim

/-- **Grounding of a jet row**: a faithful registry, a computed clue child and the row output give
`HoldsN` of the row's `(s, f, e)`. -/
theorem rowJ_holdsN {R : Registry} (hR : Registry.Faithful R) {s f e : Noun}
    {ks : List ComputeRowSkeleton} (hin : KidInputsJ s f ks)
    (hkid : ∀ k ∈ ks, HoldsN ⟨k.subject, k.formula, k.evaluation⟩)
    (hout : RowOutputJ R s f ks e) : HoldsN ⟨s, f, e⟩ := by
  rcases ks with _ | ⟨k0, _ | ⟨k1, ks⟩⟩
  · exact hin.elim
  · obtain ⟨hs, hf0⟩ := hin
    obtain ⟨n, d, j, rfl, hj, hrel⟩ := hout
    obtain ⟨fuel, hk⟩ := hkid k0 (List.mem_singleton_self _)
    simp only [hs, hf0, jetClue_jetCall] at hk
    exact registry_hint_holdsN hR hj ⟨fuel, _, hk⟩ hrel
  · exact hin.elim

/-- The row output is unique (the registry is a function, the relation is functional). -/
theorem rowOutputJ_unique {R : Registry} {s f : Noun} {ks : List ComputeRowSkeleton} {e₁ e₂ : Noun}
    (h₁ : RowOutputJ R s f ks e₁) (h₂ : RowOutputJ R s f ks e₂) : e₁ = e₂ := by
  rcases ks with _ | ⟨k0, _ | ⟨k1, ks⟩⟩
  · exact h₁.elim
  · obtain ⟨n, d, j, hf, hj, hr⟩ := h₁
    obtain ⟨n', d', j', hf', hj', hr'⟩ := h₂
    rw [hf] at hf'
    simp only [jetCall, hint, Noun.cell.injEq, Noun.atom.injEq, true_and] at hf'
    obtain ⟨⟨hn, -⟩, -⟩ := hf'
    subst hn
    rw [hj] at hj'
    cases hj'
    exact Template.rel_functional hr hr'
  · exact h₁.elim

/-- Honest side: a successful run of a registered hinted call satisfies the row output (any single
child skeleton), and its clue computes. -/
theorem rowOutputJ_of_holdsN {R : Registry} (hR : Registry.Faithful R) {n : ℕ} {j : JetSpec}
    (hj : R n = some j) {s d e : Noun} (h : HoldsN ⟨s, jetCall n d j.c, e⟩)
    (k0 : ComputeRowSkeleton) :
    RowOutputJ R s (jetCall n d j.c) [k0] e ∧ ∃ fuel v, Nock.evalN fuel s d = some v :=
  ⟨⟨n, d, j, rfl, hj, registry_hint_rel hR hj h⟩, (holdsN_hint_iff.1 h).1⟩

/-! ## §F Toys -/

/-- The `swap` template: arguments at axes `2, 3`, result `[a₁ a₀]`. -/
def swapT : Template := ⟨2, ![2, 3], fun a => some (.cell (a 1) (a 0))⟩

/-- Its Nock formula: `[[0 3] [0 2]]` (autocons of two slot reads). -/
def swapC : Noun := .cell (.cell (.atom 0) (.atom 3)) (.cell (.atom 0) (.atom 2))

def swapJet : JetSpec := ⟨swapT, swapC⟩

theorem swapT_rel_iff {s r : Noun} : swapT.rel s r ↔ ∃ a b, s = .cell a b ∧ r = .cell b a := by
  rw [Template.rel_iff]
  constructor
  · rintro ⟨x, hx, hr⟩
    have h0 := hx ⟨0, by decide⟩
    have h1 := hx ⟨1, by decide⟩
    cases s with
    | atom m => simp [swapT, Noun.slot] at h0
    | cell a b =>
        simp [swapT, Noun.slot] at h0 h1 hr
        exact ⟨a, b, rfl, by rw [← hr, ← h0, ← h1]⟩
  · rintro ⟨a, b, rfl, rfl⟩
    refine ⟨![a, b], ?_, rfl⟩
    intro i
    fin_cases i <;> simp [swapT, Noun.slot]

theorem evalN_swapC {fuel : ℕ} {s r : Noun} (h : Nock.evalN fuel s swapC = some r) :
    ∃ a b, s = .cell a b ∧ r = .cell b a := by
  rcases fuel with _ | _ | fuel
  · simp [Nock.evalN] at h
  · simp [Nock.evalN, swapC] at h
  · cases s with
    | atom m => simp [Nock.evalN, swapC, Noun.slot] at h
    | cell a b =>
        simp [Nock.evalN, swapC, Noun.slot] at h
        exact ⟨a, b, rfl, h.symm⟩

/-- **The toy jet is faithful** (both directions, `evalN` only). -/
theorem swapJet_faithful : swapJet.Faithful := by
  refine ⟨fun s r h => ?_, fun s fuel r h => swapT_rel_iff.2 (evalN_swapC h)⟩
  obtain ⟨a, b, rfl, rfl⟩ := swapT_rel_iff.1 h
  exact ⟨2, by simp [swapJet, Nock.evalN, swapC, Noun.slot]⟩

/-- The one-entry registry: id `7` ↦ `swap`. -/
def toyR : Registry := fun n => if n = 7 then some swapJet else none

theorem toyR_faithful : Registry.Faithful toyR := by
  intro n j h
  unfold toyR at h
  split_ifs at h
  cases h
  exact swapJet_faithful

theorem toyR_seven : toyR 7 = some swapJet := rfl

/-- The hinted program `[11 [7 [1 42]] [[0 3] [0 2]]]`. -/
def toyProg : Noun := jetCall 7 (.cell (.atom 1) (.atom 42)) swapC

def toySubj : Noun := .cell (.atom 5) (.atom 6)

/-- **`*[[5 6] toyProg] = [6 5]`, derived from the registry** (not by running `swapC`). -/
theorem toy_holdsN : HoldsN ⟨toySubj, toyProg, .cell (.atom 6) (.atom 5)⟩ :=
  registry_hint_holdsN toyR_faithful toyR_seven ⟨1, .atom 42, rfl⟩
    (swapT_rel_iff.2 ⟨_, _, rfl, rfl⟩)

/-- Cross-check by running `evalN` directly. -/
theorem toy_evalN : Nock.evalN 3 toySubj toyProg = some (.cell (.atom 6) (.atom 5)) := by
  simp [toyProg, toySubj, jetCall, hint, swapC, Nock.evalN, Noun.slot]

/-- The registry pins the result: any `HoldsN` result of the toy program is `[6 5]`. -/
theorem toy_result_unique {r : Noun} (h : HoldsN ⟨toySubj, toyProg, r⟩) :
    r = .cell (.atom 6) (.atom 5) := by
  obtain ⟨a, b, hs, hr⟩ := swapT_rel_iff.1 (registry_hint_rel toyR_faithful toyR_seven h)
  simp only [toySubj, Noun.cell.injEq] at hs
  rw [hr, ← hs.1, ← hs.2]

/-- The toy as a jet row: one clue child `(s, [1 42])`, grounded by the registry. -/
theorem toy_row_holdsN (k0 : ComputeRowSkeleton) (hs : k0.subject = toySubj)
    (hf : k0.formula = .cell (.atom 1) (.atom 42)) (he : k0.evaluation = .atom 42) :
    HoldsN ⟨toySubj, toyProg, .cell (.atom 6) (.atom 5)⟩ :=
  rowJ_holdsN toyR_faithful (ks := [k0]) ⟨hs, hf⟩
    (fun k hk => by
      rw [List.mem_singleton] at hk
      subst hk
      exact ⟨1, by rw [hf, he]; rfl⟩)
    ⟨7, _, swapJet, rfl, toyR_seven, swapT_rel_iff.2 ⟨_, _, rfl, rfl⟩⟩

/-- **Negative control (crashing clue).**  With `d = [0 0]` the relation still holds on
`([5 6], [6 5])` and the row output is satisfiable, yet the hinted program does NOT hold: the clue
child's `HoldsN` in `rowJ_holdsN` is load-bearing (the chip must keep `d` as a real walk child). -/
def toyCrash : Noun := jetCall 7 (.cell (.atom 0) (.atom 0)) swapC

theorem toy_crash_rel_but_not_holdsN :
    swapT.rel toySubj (.cell (.atom 6) (.atom 5)) ∧
      (∀ k0 : ComputeRowSkeleton,
        RowOutputJ toyR toySubj toyCrash [k0] (.cell (.atom 6) (.atom 5))) ∧
      ∀ r, ¬ HoldsN ⟨toySubj, toyCrash, r⟩ := by
  refine ⟨swapT_rel_iff.2 ⟨_, _, rfl, rfl⟩,
    fun _ => ⟨7, _, swapJet, rfl, toyR_seven, swapT_rel_iff.2 ⟨_, _, rfl, rfl⟩⟩, ?_⟩
  intro r h
  obtain ⟨⟨fuel, v, hv⟩, -⟩ := holdsN_hint_iff.1 h
  rcases fuel with _ | fuel <;> simp [Nock.evalN, Noun.slot] at hv

end Nock.Jet
