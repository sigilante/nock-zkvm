/-
NockvmE2E/Z38/JpClaim.lean: the claims of the template-jet program `jp` and their semantic truth.
  `cJ = ⟨[3 (p+5)], [fJ-hint fP-hint], [[9 [(p+5) 0]] (p+8)]⟩`; `cJF` = the same with result `p+9` in the last atom (the false-claim twin of `jpXF`).
  * `run_jp`    : nockvm's generator run of `jp` over `catJ.toVR.R`, fuel 4, returns the result `rJ` (the kernel run; fields by `rfl`/`decide +kernel`);
  * `holds_jp`  : `HoldsN cJ`  (autocons of a faithful template hint and a faithful `add` hint; registry faithfulness of `catJ.toVR`);
  * `not_holds_jpF` : `¬ HoldsN cJF`.
Not zero-knowledge.
-/
import Nock.Jet.PrimJ9
import NockvmE2E.Z38.HF1LJ

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.JpClaim

open Nock Nock.Jet Nock.Jet.Prim Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open NockvmE2E.Z38.HF1LJ (sJ fJ)
open NockvmE2E.Z38.CatJ (catJ TN)

theorem hT_of_ne (op : PrimOp) (hop : op ≠ .dec) : (primSpec op).T = binT op := by
  cases op <;> first | rfl | exact absurd rfl hop

theorem holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {x y n : ℕ} (h : primSem op x y = some n) :
    HoldsN ⟨.cell (.atom x) (.atom y), primC op, .atom n⟩ := by
  have hrel : (primSpec op).T.rel (.cell (.atom x) (.atom y)) (.atom n) := by
    rw [hT_of_ne op hop]; exact binT_rel_of h
  exact (primSpec_faithful op).1 _ _ hrel

theorem not_holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {s res : Noun}
    (h : ∀ x y n, s = .cell (.atom x) (.atom y) → primSem op x y = some n → res ≠ .atom n) :
    ¬ HoldsN ⟨s, primC op, res⟩ := by
  rintro ⟨fuel, hf⟩
  have hrel := primSpec_complete op s fuel res hf
  rw [hT_of_ne op hop] at hrel
  obtain ⟨x, y, n, hs, hn, hr⟩ := binT_rel hrel
  exact h x y n hs hn hr

/-- the call result of the template `TN` at `[3 (p+5)]`: `[9 [(p+5) 0]]` -/
def tplRes : Noun := .cell (.atom 9) (.cell (.atom (Nock.Field.p + 5)) (.atom 0))
/-- the result of `jp`: the template result consed with `3 + (p+5) = p+8` -/
def rJ : Noun := .cell tplRes (.atom (Nock.Field.p + 8))
def rJF : Noun := .cell tplRes (.atom (Nock.Field.p + 9))

def cJ : P8PublicClaim := ⟨sJ, fJ, rJ⟩
def cJF : P8PublicClaim := ⟨sJ, fJ, rJF⟩

/-- the two hinted calls -/
def fT7 : Noun := wildCall 7 (Nock.Jet.Autogen.compile Nock.Field.p TN)
def fA8 : Noun := wildCall 8 (primC .add)

theorem fJ_eq : fJ = .cell fT7 fA8 := rfl

/-- `genX` of `jp` over the catalogue registry: nockvm's run, by the kernel -/
theorem hit7 : Nock.Edit.GenX.jetHit catJ.toVR.R (.atom Nock.Jet.wildTag) (.atom 7) (Nock.Jet.Autogen.compile Nock.Field.p TN) sJ =
    some tplRes := by
  decide +kernel

theorem run_jp : (Nock.V1J8.Gen.runX catJ.toVR.R 4 sJ fJ).map (·.res) = some rJ := by
  decide +kernel

/-! ## semantic truth -/

theorem holdsN_cons_iff {s b c d r : Noun} :
    HoldsN ⟨s, .cell (.cell b c) d, r⟩ ↔ ∃ l rr, r = .cell l rr ∧ HoldsN ⟨s, .cell b c, l⟩ ∧ HoldsN ⟨s, d, rr⟩ := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [Nock.evalN] at h
    | succ n =>
      simp only [Nock.evalN] at h
      cases h1 : Nock.evalN n s (.cell b c) <;> cases h2 : Nock.evalN n s d <;> simp [h1, h2] at h
      rename_i l rr
      exact ⟨l, rr, h.symm, ⟨n, h1⟩, ⟨n, h2⟩⟩
  · rintro ⟨l, rr, rfl, ⟨f1, h1⟩, ⟨f2, h2⟩⟩
    refine ⟨max f1 f2 + 1, ?_⟩
    simp only [Nock.evalN]
    rw [Nock.evalN_mono (Nat.le_max_left f1 f2) h1, Nock.evalN_mono (Nat.le_max_right f1 f2) h2]

theorem rel_tpl : (TN.toTemplate Nock.Field.p).rel sJ tplRes := by
  unfold Template.rel
  decide +kernel

theorem holds_tpl : HoldsN ⟨sJ, fT7, tplRes⟩ := by
  refine holdsN_hint_iff.mpr ⟨⟨1, .atom 7, rfl⟩, ?_⟩
  have hj : catJ.toVR.R 7 = some ⟨(TN.toTemplate Nock.Field.p), Nock.Jet.Autogen.compile Nock.Field.p TN⟩ := rfl
  exact ((catJ.toVR.faithful 7 _ hj).1 _ _ rel_tpl)

theorem sem_jp : primSem .add 3 (Nock.Field.p + 5) = some (Nock.Field.p + 8) := by
  simp [primSem, Nock.Field.p]

theorem holds_add8 : HoldsN ⟨sJ, fA8, .atom (Nock.Field.p + 8)⟩ :=
  holdsN_hint_iff.mpr ⟨⟨1, .atom 8, rfl⟩, holdsN_primC (by decide) sem_jp⟩

theorem holds_jp : HoldsN cJ := by
  show HoldsN ⟨sJ, .cell fT7 fA8, rJ⟩
  exact holdsN_cons_iff.mpr ⟨_, _, rfl, holds_tpl, holds_add8⟩

theorem not_holds_jpF : ¬ HoldsN cJF := by
  intro h
  have h' : HoldsN ⟨sJ, .cell fT7 fA8, rJF⟩ := h
  obtain ⟨l, rr, hr, -, h2⟩ := holdsN_cons_iff.mp h'
  have hrr : rr = .atom (Nock.Field.p + 9) := by
    have := hr; simp only [rJF, Noun.cell.injEq] at this; exact this.2.symm
  subst hrr
  have h1 := (holdsN_hint_iff.mp h2).2
  refine not_holdsN_primC (by decide) ?_ h1
  intro x y n hs hn hres
  obtain ⟨rfl, rfl⟩ : x = 3 ∧ y = Nock.Field.p + 5 := by simpa [sJ] using hs.symm
  rw [sem_jp] at hn
  have : n = Nock.Field.p + 8 := (Option.some.inj hn).symm
  subst this
  have := Noun.atom.inj hres
  omega

theorem rJ_ne : rJF ≠ rJ := by
  simp [rJF, rJ, Noun.cell.injEq]

end NockvmE2E.Z38.JpClaim

#print axioms NockvmE2E.Z38.JpClaim.run_jp
#print axioms NockvmE2E.Z38.JpClaim.holds_jp
#print axioms NockvmE2E.Z38.JpClaim.not_holds_jpF
