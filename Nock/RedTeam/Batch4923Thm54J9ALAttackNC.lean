/-
  **Negative controls for the ALU attacks, at the predicate level of `AcceptsJ9AL`.**  (`opConfusion_rejected` is the
  predicate-level form of the op-confusion claim.)

  ## What is checked (kernel; std3 `#print axioms` at the end of the file)
  For each ALU attack a CONCRETE FALSE CLAIM is built: the claim a prover that exploited the attack would assert
  for a primitive call `*[[x y] [11 [%wild [1 id]] primC op]] = r`, where the true result differs.
  (a) `<name>_false : ¬ HoldsN claim` (pure Nock-level fact, via `primSpec_complete` + `binT_rel`), with positive
      controls `ctl_*` (`HoldsN` of the true call, via `primSpec_faithful`), so the NC lemma is not vacuous;
  (b) `<name>_rejected_AL`: at EVERY in-regime J-9 AL verifier datum (`RegimeAL`, any `Pb`, any faithful `Rg`, any
      staged prover `Q`), `Pr_χ[∃ M, AcceptsJ9AL … claim …] < 2^-155` (`false_claim_rejected_AL`).
  The `Pb` is arbitrary: the primitive table may or may not contain `(id, op)`; the bound does not depend on it.

  ## Labels (honest scope)
  * (b) is the SOUNDNESS bound read at the attack's false claim: it says no attack on ANY chip gate can produce
    an accepted false claim except with probability `< 2^-155`.  It does NOT exhibit which gate fires at which
    row (that is the gate-equation level: `Batch4920Thm54AluSZChipNC` for booleanity / link / `< p`, and the ALU
    lemmas `AluSat*`, `AluCallOK`).  The named attack is the claim an attacker would want, not a trace.
  * REPRESENTATION attacks (a non-canonical big output with top limb 0; a kind-2 handle for a value below
    `p`) change no claim noun: the noun denoted is the same atom, so there is no false claim to reject.  They are
    chip-gate items (atom table g3 / `bnd mb`; ALU kind gate); at the predicate they are covered by the
    soundness theorem as a whole (every accepted trace's read-off is the honest one); no theorem here.
  * The increment attack is stated at Nock's increment, on a big atom, claimed with mod-`p` semantics.
  * The cell-operand attack is stated as a prim call on a cell operand (the honest run crashes).
  * All arms: `primSpec_faithful_all` (all seven arms faithful) and `primUnreg_rejected`.
  * `RegimeAL` for a with-primitives datum is satisfiable only by the completeness capstone's witness;
    (b) are therefore conditional on the regime, as `probJ9AL_final_clean` is.
-/
import Nock.RedTeam.Batch4922Thm54J9ALPredNC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4923

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
open Nock.Jet Nock.Jet.Prim Nock.Jet.Autogen
open Nock.RedTeam.Batch4922 (RegimeAL false_claim_rejected_AL)

noncomputable section

/-! ## 1. Primitive-call claims and their Nock-level falsity -/

/-- The field modulus `p = 2^64 - 2^32 + 1`. -/
abbrev P : ℕ := Nock.Atoms.p

/-- The primitive call `*[s [11 [%wild [1 id]] primC op]] = res`. -/
def primClaimS (id : ℕ) (op : PrimOp) (s res : Noun) : P8PublicClaim :=
  ⟨s, hint (.atom Nock.Jet.wildTag) (op1 (A id)) (primC op), res⟩

/-- The binary primitive call on atoms. -/
def primClaim (id : ℕ) (op : PrimOp) (x y res : ℕ) : P8PublicClaim :=
  primClaimS id op (.cell (.atom x) (.atom y)) (.atom res)

theorem hT_of_ne (op : PrimOp) (hop : op ≠ .dec) : (primSpec op).T = binT op := by
  cases op <;> first | rfl | exact absurd rfl hop

/-- **NC lemma**: a claim about `primC op` whose result is not the `primSem` result is false (Nock level). -/
theorem not_holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {s res : Noun}
    (h : ∀ x y n, s = .cell (.atom x) (.atom y) → primSem op x y = some n → res ≠ .atom n) :
    ¬ HoldsN ⟨s, primC op, res⟩ := by
  rintro ⟨fuel, hf⟩
  have hrel := primSpec_complete op s fuel res hf
  rw [hT_of_ne op hop] at hrel
  obtain ⟨x, y, n, hs, hn, hr⟩ := binT_rel hrel
  exact h x y n hs hn hr

/-- Positive control: a true primitive call holds (Nock level). -/
theorem holdsN_primC {op : PrimOp} (hop : op ≠ .dec) {x y n : ℕ} (h : primSem op x y = some n) :
    HoldsN ⟨.cell (.atom x) (.atom y), primC op, .atom n⟩ := by
  have hrel : (primSpec op).T.rel (.cell (.atom x) (.atom y)) (.atom n) := by
    rw [hT_of_ne op hop]; exact binT_rel_of h
  exact (primSpec_faithful op).1 _ _ hrel

theorem clue_computes (id : ℕ) (s : Noun) : ∃ fuel v, Nock.evalN fuel s (op1 (A id)) = some v :=
  ⟨1, .atom id, by simp [op1, A, Nock.evalN]⟩

theorem not_holdsN_primClaim {id : ℕ} {op : PrimOp} (hop : op ≠ .dec) (x y res : ℕ)
    (h : primSem op x y ≠ some res) : ¬ HoldsN (primClaim id op x y res) := by
  intro hh
  have h1 := (holdsN_hint_iff.mp hh).2
  refine not_holdsN_primC hop ?_ h1
  intro x' y' n hs hn hres
  obtain ⟨rfl, rfl⟩ : x' = x ∧ y' = y := by simpa using hs.symm
  have : res = n := by simpa using hres
  exact h (this ▸ hn)

theorem holdsN_primClaim {id : ℕ} {op : PrimOp} (hop : op ≠ .dec) {x y n : ℕ} (h : primSem op x y = some n) :
    HoldsN (primClaim id op x y n) :=
  holdsN_hint_iff.mpr ⟨clue_computes _ _, holdsN_primC hop h⟩

/-- Every primitive arm is faithful (the positive side: a registered `primSpec` agrees with `evalN`). -/
theorem primSpec_faithful_all : ∀ op : PrimOp, (primSpec op).Faithful := primSpec_faithful

/-- **Op confusion, the predicate form**: the arm formulas of distinct primitives are distinct, so a
registry entry `primSpec op'` at the id of `(id, op)` with `op' ≠ op` is a different registration: `hPrim` rejects it. -/
theorem primC_injective {op op' : PrimOp} (h : primC op = primC op') : op = op' := by
  cases op <;> cases op' <;> first | rfl | exact absurd h (by decide)

theorem primSpec_injective {op op' : PrimOp} (h : primSpec op = primSpec op') : op = op' :=
  primC_injective (congrArg JetSpec.c h)

/-! ## 2. The attack claims -/

/-- (3) a result `>= p` emitted as the kind-0 value `1`: `(p-1)+2 = p+1`, claimed `1`. -/
def nc3a_wrap_add : P8PublicClaim := primClaim 1 .add (P - 1) (2) (1)

/-- (3) `p + 5` emitted as kind 0 `5`. -/
def nc3b_p_as_zero : P8PublicClaim := primClaim 1 .add (P) (5) (5)

/-- (4) product-split wrap: `3*5 = 15`, claimed `15 + p` (the second `(lo, hi)` of `ab + p`). -/
def nc4_product_split_wrap : P8PublicClaim := primClaim 1 .mul (3) (5) (15 + P)

/-- (5) dropped top carry: `(2^64 - 1) + 1 = 2^64`, claimed `0`. -/
def nc5a_dropped_top_carry : P8PublicClaim := primClaim 1 .add (2 ^ 64 - 1) (1) (0)

/-- (5) non-boolean carry: `1 + 1 = 2`, claimed `2 + 2^32` (carry `= 2^32 + ...`). -/
def nc5b_nonboolean_carry : P8PublicClaim := primClaim 1 .add (1) (1) (2 + 2 ^ 32)

/-- (6) truncated reader (drops the top limb): `(2^96 + 5) + 7`, claimed `5 + 7`. -/
def nc6_truncated_reader : P8PublicClaim := primClaim 1 .add (2 ^ 96 + 5) (7) (12)

/-- (7) limbs spliced from another atom: `5 + 7 = 12`, claimed `9 + 7`. -/
def nc7_spliced_limbs : P8PublicClaim := primClaim 1 .add (5) (7) (16)

/-- (8) sub underflow accepted: `3 - 5` crashes, claimed the wrapped `p - 2`. -/
def nc8a_sub_underflow_wrap : P8PublicClaim := primClaim 1 .sub (3) (5) (P - 2)

/-- (8) sub underflow: `3 - 5` crashes, claimed `0`. -/
def nc8b_sub_underflow_zero : P8PublicClaim := primClaim 1 .sub (3) (5) (0)

/-- (9) division by zero: crashes, claimed `0`. -/
def nc9a_div_by_zero : P8PublicClaim := primClaim 1 .div (7) (0) (0)

/-- (9) modulus by zero: crashes, claimed `7`. -/
def nc9b_mod_by_zero : P8PublicClaim := primClaim 1 .mod (7) (0) (7)

/-- (9) `r >= d`: `7 = 2*2 + 3`, claimed `7 mod 2 = 3`. -/
def nc9c_remainder_ge_divisor : P8PublicClaim := primClaim 1 .mod (7) (2) (3)

/-- (9) `r >= d`: `q = 2, r = 3`, claimed `7 div 2 = 2`. -/
def nc9d_quotient_for_big_remainder : P8PublicClaim := primClaim 1 .div (7) (2) (2)

/-- (10) forged lt: `a < b` claimed (loobean 0) while `b < a`. -/
def nc10a_forged_lt : P8PublicClaim := primClaim 1 .lt (2 ^ 64 + 5) (2 ^ 64 + 1) (0)

/-- (10) forged lt: `a < b` claimed while a higher limb of `a` is nonzero. -/
def nc10b_forged_lt_high_limb : P8PublicClaim := primClaim 1 .lt (2 ^ 64) (5) (0)

/-- (10) the equal outcome: `5 < 5` claimed (loobean 0). -/
def nc10c_lt_equal : P8PublicClaim := primClaim 1 .lt (5) (5) (0)

/-- (11) mul column overflow mod p: `(p-1)^2 = 1` in `F_p`, claimed `1`. -/
def nc11_column_overflow : P8PublicClaim := primClaim 1 .mul (P - 1) (P - 1) (1)

/-- (12) a missing product pair: `(B^2+1)^2 = B^4 + 2B^2 + 1`, claimed `B^4 + B^2 + 1`. -/
def nc12a_missing_pair : P8PublicClaim := primClaim 1 .mul (2 ^ 64 + 1) (2 ^ 64 + 1) (2 ^ 128 + 2 ^ 64 + 1)

/-- (12) a duplicated product pair: claimed `B^4 + 3B^2 + 1`. -/
def nc12b_duplicated_pair : P8PublicClaim := primClaim 1 .mul (2 ^ 64 + 1) (2 ^ 64 + 1) (2 ^ 128 + 3 * 2 ^ 64 + 1)

/-- (14) an F-op (Nock increment) on a big atom with mod-`p` semantics: `inc (p + 4) = p + 5`, claimed `5`. -/
def nc14a_inc_big : P8PublicClaim := ⟨.atom (P + 4), .cell (.atom 4) (.cell (.atom 0) (.atom 1)), .atom 5⟩

/-- (14) the wrap at the top of the field: `inc (p - 1) = p`, claimed `0`. -/
def nc14b_inc_wrap : P8PublicClaim := ⟨.atom (P - 1), .cell (.atom 4) (.cell (.atom 0) (.atom 1)), .atom 0⟩

/-- (16) a cell passed as an A-operand: `add [[1 2] 3]` (the honest run crashes), claimed `3`. -/
def nc16_cell_operand : P8PublicClaim :=
  primClaimS 1 .add (.cell (.cell (.atom 1) (.atom 2)) (.atom 3)) (.atom 3)

/-- (16) a cell as the right operand: `mul [5 [1 2]]`, claimed `5`. -/
def nc16b_cell_right : P8PublicClaim :=
  primClaimS 1 .mul (.cell (.atom 5) (.cell (.atom 1) (.atom 2))) (.atom 5)

/-! ## 3. Each attack claim is FALSE (Nock level, kernel-checked) -/

theorem nc3a_wrap_add_false : ¬ HoldsN nc3a_wrap_add :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc3b_p_as_zero_false : ¬ HoldsN nc3b_p_as_zero :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc4_product_split_wrap_false : ¬ HoldsN nc4_product_split_wrap :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc5a_dropped_top_carry_false : ¬ HoldsN nc5a_dropped_top_carry :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc5b_nonboolean_carry_false : ¬ HoldsN nc5b_nonboolean_carry :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc6_truncated_reader_false : ¬ HoldsN nc6_truncated_reader :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc7_spliced_limbs_false : ¬ HoldsN nc7_spliced_limbs :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc8a_sub_underflow_wrap_false : ¬ HoldsN nc8a_sub_underflow_wrap :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc8b_sub_underflow_zero_false : ¬ HoldsN nc8b_sub_underflow_zero :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc9a_div_by_zero_false : ¬ HoldsN nc9a_div_by_zero :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc9b_mod_by_zero_false : ¬ HoldsN nc9b_mod_by_zero :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc9c_remainder_ge_divisor_false : ¬ HoldsN nc9c_remainder_ge_divisor :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc9d_quotient_for_big_remainder_false : ¬ HoldsN nc9d_quotient_for_big_remainder :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc10a_forged_lt_false : ¬ HoldsN nc10a_forged_lt :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc10b_forged_lt_high_limb_false : ¬ HoldsN nc10b_forged_lt_high_limb :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc10c_lt_equal_false : ¬ HoldsN nc10c_lt_equal :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc11_column_overflow_false : ¬ HoldsN nc11_column_overflow :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc12a_missing_pair_false : ¬ HoldsN nc12a_missing_pair :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem nc12b_duplicated_pair_false : ¬ HoldsN nc12b_duplicated_pair :=
  not_holdsN_primClaim (by decide) _ _ _ (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

/-- Nock's increment on an atom `v` yields `v + 1`: any other claimed result is false. -/
theorem not_holdsN_inc (v w : ℕ) (h : w ≠ v + 1) :
    ¬ HoldsN ⟨.atom v, .cell (.atom 4) (.cell (.atom 0) (.atom 1)), .atom w⟩ := by
  rintro ⟨fuel, hf⟩
  cases fuel with
  | zero => simp [Nock.evalN] at hf
  | succ n =>
    cases n with
    | zero => simp [Nock.evalN, Nock.Noun.slot] at hf
    | succ m => simp [Nock.evalN, Nock.Noun.slot, Nock.Noun.lus] at hf; omega

theorem nc14a_false : ¬ HoldsN nc14a_inc_big :=
  not_holdsN_inc _ _ (by norm_num [Nock.Atoms.p, Nock.Field.p])

theorem nc14b_false : ¬ HoldsN nc14b_inc_wrap :=
  not_holdsN_inc _ _ (by norm_num [Nock.Atoms.p, Nock.Field.p])

theorem nc16_false : ¬ HoldsN nc16_cell_operand := by
  intro hh
  have h1 := (holdsN_hint_iff.mp hh).2
  refine not_holdsN_primC (by decide) ?_ h1
  intro x y n hs
  simp at hs

theorem nc16b_false : ¬ HoldsN nc16b_cell_right := by
  intro hh
  have h1 := (holdsN_hint_iff.mp hh).2
  refine not_holdsN_primC (by decide) ?_ h1
  intro x y n hs
  simp at hs

/-! ## 4. Positive controls: the true calls HOLD (the NC lemma is not vacuous) -/

theorem ctl_add : HoldsN (primClaim 1 .add (3) (5) (8)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_add_big : HoldsN (primClaim 1 .add (P - 1) (2) (P + 1)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_sub : HoldsN (primClaim 1 .sub (5) (3) (2)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_lt_big : HoldsN (primClaim 1 .lt (2 ^ 64 + 1) (2 ^ 64 + 5) (0)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_lt_big_no : HoldsN (primClaim 1 .lt (2 ^ 64 + 5) (2 ^ 64 + 1) (1)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_mul_big : HoldsN (primClaim 1 .mul (2 ^ 64 + 1) (2 ^ 64 + 1) (2 ^ 128 + 2 * 2 ^ 64 + 1)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_div : HoldsN (primClaim 1 .div (7) (2) (3)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

theorem ctl_mod : HoldsN (primClaim 1 .mod (7) (2) (1)) :=
  holdsN_primClaim (by decide) (by norm_num [primSem, Nock.Atoms.p, Nock.Field.p])

/-! ## 5. Rejection at `AcceptsJ9AL` -/

section Reject
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {g : ℕ}

open Classical in
/-- The soundness bound at one claim, as a proposition. -/
def Rej155 (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p))
    (r : RowsJ9AL) (g : ℕ) : Prop :=
  ((Finset.univ.filter fun χ : Coins frameJ8 K =>
      ∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g).card : ℚ) /
    Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155

/-- **A false claim is rejected at J-9 AL** (the bound, as `Rej155`). -/
theorem rej_of_false [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) {c : P8PublicClaim} (hc : ¬ HoldsN c)
    (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q) (hreg : RegimeAL K Pb c r g) :
    Rej155 δ b Pb Rg c Q r g :=
  false_claim_rejected_AL δ b Pb hRg c hc Q hQ hreg

/-- **`nc3a_wrap_add`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc3a_wrap_add_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc3a_wrap_add r g) : Rej155 δ b Pb Rg nc3a_wrap_add Q r g :=
  rej_of_false δ b Pb hRg nc3a_wrap_add_false Q hQ hreg

/-- **`nc3b_p_as_zero`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc3b_p_as_zero_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc3b_p_as_zero r g) : Rej155 δ b Pb Rg nc3b_p_as_zero Q r g :=
  rej_of_false δ b Pb hRg nc3b_p_as_zero_false Q hQ hreg

/-- **`nc4_product_split_wrap`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc4_product_split_wrap_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc4_product_split_wrap r g) : Rej155 δ b Pb Rg nc4_product_split_wrap Q r g :=
  rej_of_false δ b Pb hRg nc4_product_split_wrap_false Q hQ hreg

/-- **`nc5a_dropped_top_carry`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc5a_dropped_top_carry_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc5a_dropped_top_carry r g) : Rej155 δ b Pb Rg nc5a_dropped_top_carry Q r g :=
  rej_of_false δ b Pb hRg nc5a_dropped_top_carry_false Q hQ hreg

/-- **`nc5b_nonboolean_carry`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc5b_nonboolean_carry_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc5b_nonboolean_carry r g) : Rej155 δ b Pb Rg nc5b_nonboolean_carry Q r g :=
  rej_of_false δ b Pb hRg nc5b_nonboolean_carry_false Q hQ hreg

/-- **`nc6_truncated_reader`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc6_truncated_reader_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc6_truncated_reader r g) : Rej155 δ b Pb Rg nc6_truncated_reader Q r g :=
  rej_of_false δ b Pb hRg nc6_truncated_reader_false Q hQ hreg

/-- **`nc7_spliced_limbs`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc7_spliced_limbs_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc7_spliced_limbs r g) : Rej155 δ b Pb Rg nc7_spliced_limbs Q r g :=
  rej_of_false δ b Pb hRg nc7_spliced_limbs_false Q hQ hreg

/-- **`nc8a_sub_underflow_wrap`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc8a_sub_underflow_wrap_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc8a_sub_underflow_wrap r g) : Rej155 δ b Pb Rg nc8a_sub_underflow_wrap Q r g :=
  rej_of_false δ b Pb hRg nc8a_sub_underflow_wrap_false Q hQ hreg

/-- **`nc8b_sub_underflow_zero`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc8b_sub_underflow_zero_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc8b_sub_underflow_zero r g) : Rej155 δ b Pb Rg nc8b_sub_underflow_zero Q r g :=
  rej_of_false δ b Pb hRg nc8b_sub_underflow_zero_false Q hQ hreg

/-- **`nc9a_div_by_zero`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc9a_div_by_zero_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc9a_div_by_zero r g) : Rej155 δ b Pb Rg nc9a_div_by_zero Q r g :=
  rej_of_false δ b Pb hRg nc9a_div_by_zero_false Q hQ hreg

/-- **`nc9b_mod_by_zero`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc9b_mod_by_zero_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc9b_mod_by_zero r g) : Rej155 δ b Pb Rg nc9b_mod_by_zero Q r g :=
  rej_of_false δ b Pb hRg nc9b_mod_by_zero_false Q hQ hreg

/-- **`nc9c_remainder_ge_divisor`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc9c_remainder_ge_divisor_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc9c_remainder_ge_divisor r g) : Rej155 δ b Pb Rg nc9c_remainder_ge_divisor Q r g :=
  rej_of_false δ b Pb hRg nc9c_remainder_ge_divisor_false Q hQ hreg

/-- **`nc9d_quotient_for_big_remainder`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc9d_quotient_for_big_remainder_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc9d_quotient_for_big_remainder r g) : Rej155 δ b Pb Rg nc9d_quotient_for_big_remainder Q r g :=
  rej_of_false δ b Pb hRg nc9d_quotient_for_big_remainder_false Q hQ hreg

/-- **`nc10a_forged_lt`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc10a_forged_lt_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc10a_forged_lt r g) : Rej155 δ b Pb Rg nc10a_forged_lt Q r g :=
  rej_of_false δ b Pb hRg nc10a_forged_lt_false Q hQ hreg

/-- **`nc10b_forged_lt_high_limb`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc10b_forged_lt_high_limb_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc10b_forged_lt_high_limb r g) : Rej155 δ b Pb Rg nc10b_forged_lt_high_limb Q r g :=
  rej_of_false δ b Pb hRg nc10b_forged_lt_high_limb_false Q hQ hreg

/-- **`nc10c_lt_equal`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc10c_lt_equal_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc10c_lt_equal r g) : Rej155 δ b Pb Rg nc10c_lt_equal Q r g :=
  rej_of_false δ b Pb hRg nc10c_lt_equal_false Q hQ hreg

/-- **`nc11_column_overflow`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc11_column_overflow_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc11_column_overflow r g) : Rej155 δ b Pb Rg nc11_column_overflow Q r g :=
  rej_of_false δ b Pb hRg nc11_column_overflow_false Q hQ hreg

/-- **`nc12a_missing_pair`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc12a_missing_pair_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc12a_missing_pair r g) : Rej155 δ b Pb Rg nc12a_missing_pair Q r g :=
  rej_of_false δ b Pb hRg nc12a_missing_pair_false Q hQ hreg

/-- **`nc12b_duplicated_pair`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc12b_duplicated_pair_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc12b_duplicated_pair r g) : Rej155 δ b Pb Rg nc12b_duplicated_pair Q r g :=
  rej_of_false δ b Pb hRg nc12b_duplicated_pair_false Q hQ hreg

/-- **`nc14a_inc_big`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc14a_inc_big_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc14a_inc_big r g) : Rej155 δ b Pb Rg nc14a_inc_big Q r g :=
  rej_of_false δ b Pb hRg nc14a_false Q hQ hreg

/-- **`nc14b_inc_wrap`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc14b_inc_wrap_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc14b_inc_wrap r g) : Rej155 δ b Pb Rg nc14b_inc_wrap Q r g :=
  rej_of_false δ b Pb hRg nc14b_false Q hQ hreg

/-- **`nc16_cell_operand_rejected_AL`: the cell-operand primitive claim is accepted with probability below `2^-155`.**
The claim is that the primitive `add` applied to the operand `[[1 2] 3]` (a cell as the left operand, on which the
honest run crashes) returns `3`.  For a faithful registry, any staged trace family `Q` and public data in the
J-9 AL regime, the fraction of coins for which some message makes `AcceptsJ9AL` accept is `< 1 / 2^155`. -/
theorem nc16_cell_operand_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc16_cell_operand r g) : Rej155 δ b Pb Rg nc16_cell_operand Q r g :=
  rej_of_false δ b Pb hRg nc16_false Q hQ hreg

/-- **`nc16b_cell_right`** is rejected at `AcceptsJ9AL` (`Pr < 2^-155`, in regime). -/
theorem nc16b_cell_right_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb nc16b_cell_right r g) : Rej155 δ b Pb Rg nc16b_cell_right Q r g :=
  rej_of_false δ b Pb hRg nc16b_false Q hQ hreg

/-- **`opConfusion_rejected`: a primitive table entry whose id is registered under a different operation is rejected.**
If `(id, op)` is among the public primitives `Pb.prims` while the registry registers `id` at the primitive spec
of an operation `op' ≠ op`, then `AcceptsJ9AL` does not hold, for every claim, coin, message and trace.  This is a
direct refutation, not a probability bound. -/
theorem opConfusion_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {q : ℕ × PrimOp} (hq : q ∈ Pb.prims) {op' : PrimOp}
    (hreg : Rg q.1 = some (primSpec op')) (hne : op' ≠ q.2) : ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := by
  intro hacc
  have h := hacc.hPrim q hq
  rw [hreg] at h
  exact hne (primSpec_injective (Option.some.inj h))

end Reject

end

end Nock.RedTeam.Batch4923

section Axioms
open Nock.RedTeam.Batch4923
#print axioms primSpec_faithful_all
#print axioms primC_injective
#print axioms primSpec_injective
#print axioms not_holdsN_primC
#print axioms holdsN_primC
#print axioms rej_of_false
#print axioms opConfusion_rejected
#print axioms nc3a_wrap_add_false
#print axioms nc3a_wrap_add_rejected_AL
#print axioms nc3b_p_as_zero_false
#print axioms nc3b_p_as_zero_rejected_AL
#print axioms nc4_product_split_wrap_false
#print axioms nc4_product_split_wrap_rejected_AL
#print axioms nc5a_dropped_top_carry_false
#print axioms nc5a_dropped_top_carry_rejected_AL
#print axioms nc5b_nonboolean_carry_false
#print axioms nc5b_nonboolean_carry_rejected_AL
#print axioms nc6_truncated_reader_false
#print axioms nc6_truncated_reader_rejected_AL
#print axioms nc7_spliced_limbs_false
#print axioms nc7_spliced_limbs_rejected_AL
#print axioms nc8a_sub_underflow_wrap_false
#print axioms nc8a_sub_underflow_wrap_rejected_AL
#print axioms nc8b_sub_underflow_zero_false
#print axioms nc8b_sub_underflow_zero_rejected_AL
#print axioms nc9a_div_by_zero_false
#print axioms nc9a_div_by_zero_rejected_AL
#print axioms nc9b_mod_by_zero_false
#print axioms nc9b_mod_by_zero_rejected_AL
#print axioms nc9c_remainder_ge_divisor_false
#print axioms nc9c_remainder_ge_divisor_rejected_AL
#print axioms nc9d_quotient_for_big_remainder_false
#print axioms nc9d_quotient_for_big_remainder_rejected_AL
#print axioms nc10a_forged_lt_false
#print axioms nc10a_forged_lt_rejected_AL
#print axioms nc10b_forged_lt_high_limb_false
#print axioms nc10b_forged_lt_high_limb_rejected_AL
#print axioms nc10c_lt_equal_false
#print axioms nc10c_lt_equal_rejected_AL
#print axioms nc11_column_overflow_false
#print axioms nc11_column_overflow_rejected_AL
#print axioms nc12a_missing_pair_false
#print axioms nc12a_missing_pair_rejected_AL
#print axioms nc12b_duplicated_pair_false
#print axioms nc12b_duplicated_pair_rejected_AL
#print axioms nc14a_false
#print axioms nc14a_inc_big_rejected_AL
#print axioms nc14b_false
#print axioms nc14b_inc_wrap_rejected_AL
#print axioms nc16_false
#print axioms nc16_cell_operand_rejected_AL
#print axioms nc16b_false
#print axioms nc16b_cell_right_rejected_AL
#print axioms ctl_add
#print axioms ctl_add_big
#print axioms ctl_sub
#print axioms ctl_lt_big
#print axioms ctl_lt_big_no
#print axioms ctl_mul_big
#print axioms ctl_div
#print axioms ctl_mod
end Axioms
