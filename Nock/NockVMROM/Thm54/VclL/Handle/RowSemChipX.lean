/-
  Nock/NockVMROM/Thm54/VclL/Handle/RowSemChipX.lean

  **Card C-2 part 2 : step 3 — a `computeChipVCLHX` row decodes to
  `LocalVSX.RowSemX`, every state `0..16`.**  New module, additive.

  * `activeX env` — the records a row consumes, with their balance (`x` export, `p` walk path,
    `s` service): every slot entry at activity `1`, and a slot's pair under an active flag.
  * **`RecOK D R limbA`** — what a SERVED, GENUINE record says on a denotation `D` (the memory facts,
    entering as the named hypothesis `hOK : ∀ r ∈ activeX env, RecOK D R limbA r`; discharged by the
    lanes that state them, NOT here):
    - export `(p, l, r)` (`x`): `D (1, p) = [D l, D r]` (A-3s `cell_row_genuine2` / `exportHK_genuine`);
    - `TAG_inc` `(old, new, 4)` (`s`): `D old = n`, `D new = n + 1` (A-2 `inc_chain_sound_of_served` +
      A-3s `consumeServedQ_of_balance` + the big-atom denotation);
    - `TAG_jet` `(id, h_c, h_S, h_E, 3)` (`s`): `R id = j`, `D h_c = j.c`, `j.T.rel (D h_S) (D h_E)`
      (J-3b `jetChip_holds` + J-1's registry);
    - `walkRecA` `(root, ax, l)` (`s`): `D (2, root) = atom n` and `limbA n ax = l` (AW
      `atomWalk_records_genuine_atom`; `limbA` is the atom table's limb function, only its
      functionality is used).
  * **`rowSemX_of_chip`** — base gates + one-hot at `stIdx st` + `hOK` ⇒ `RowSemX p D R (rowOfX env st)`
    (the per-state clauses and the kid-kind clause), for `17 < p`, under ONE extra named hypothesis on
    `s10L` rows, `hv : 1 ≤ val v ∧ 2·val v + 1 < p` (the halving `a = 2v + β` is exact) — see the
    FINDING in `Batch2903`: the gates alone do not give it, and at Goldilocks a wrapped `v` is a
    63-bit axis.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

open Nock Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV kind_zero op4_fast_sem)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.Jet (Registry JetSpec)

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. Consumed records and what a served genuine record says -/

def reVal (env : Env (ZMod p)) : RE → ℕ
  | .col i => (env.trace i).val
  | .k c => c

def pairRecsX (env : Env (ZMod p)) (S : SlotX ℚ) : List (List ℕ × Bal) :=
  match S.pair with
  | some (fl, a, b, bl) =>
      if env.trace fl = 1 then [(a.map (reVal env), bl), (b.map (reVal env), bl)] else []
  | none => []

/-- **The records a row consumes** (entries at activity `1`, pairs under an active flag). -/
def activeX (env : Env (ZMod p)) : List (List ℕ × Bal) :=
  (slotsX (F := ℚ)).flatMap fun S =>
    ((S.ents.filter fun x => decide (evalQX x.act env = 1)).map fun x =>
      (x.rcd.map (reVal env), x.bal)) ++ pairRecsX env S

def RecOK (D : HX → Option Noun) (R : Registry) (limbA : ℕ → ℕ → HX) : List ℕ × Bal → Prop
  | ([pv, lk, lv, rk, rv], .x) => Cell3 D (1, pv) (lk, lv) (rk, rv)
  | ([rv, ax, ck, cv], .p) =>
      ∃ Rt C, D (1, rv) = some Rt ∧ D (ck, cv) = some C ∧ Noun.slot ax Rt = some C
  | ([rv, ax, lk, lv], .s) => ∃ n, D (2, rv) = some (.atom n) ∧ limbA n ax = (lk, lv)
  | ([ok, ov, nk, nv, 4], .s) =>
      ∃ n : ℕ, D (ok, ov) = some (.atom n) ∧ D (nk, nv) = some (.atom (n + 1))
  | ([id, ck, cv, sk, sv, ek, ev, 3], .s) =>
      ∃ j : JetSpec, R id = some j ∧ D (ck, cv) = some j.c ∧
        ∃ S E, D (sk, sv) = some S ∧ D (ek, ev) = some E ∧ j.T.rel S E
  | _ => True

/-! ## 2. Gate facts at a row -/

section Facts
variable {env : Env (ZMod p)}

theorem val_one' : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  exact ZMod.val_one p

theorem val_nat {n : ℕ} (hn : n < p) : ((n : ZMod p)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

theorem oh_one {j : ℕ} (hOH : OneHotAt env j) (hj : j < nStates) : env.trace j = 1 := by
  simpa using hOH j hj

theorem oh_zero {j i : ℕ} (hOH : OneHotAt env j) (hi : i < nStates) (hne : i ≠ j) :
    env.trace i = 0 := by
  simpa [hne] using hOH i hi

theorem eqg (hB : BaseHoldsX env) {g : EqG ℚ} (hg : g ∈ eqGatesX) (hσ : evalQX g.σ env = 1) :
    env.trace g.x = evalQX g.y.expr env := by
  have := eq_of_base hB hg
  simp only [EqG.gate, evalQX, cc, hσ, one_mul] at this
  exact sub_eq_zero.mp this

theorem eqCol (hB : BaseHoldsX env) {σ : CoeffExpr ℚ} {x y : ℕ} (hg : (⟨σ, x, .col y⟩ : EqG ℚ) ∈ eqGatesX)
    (hσ : evalQX σ env = 1) : env.trace x = env.trace y := by
  simpa [Opnd.expr, evalQX, cc] using eqg hB hg hσ

theorem hdEq (hB : BaseHoldsX env) {σ : CoeffExpr ℚ} {a b : Hd}
    (hg : ∀ g ∈ heq σ a b, g ∈ (eqGatesX (F := ℚ))) (hσ : evalQX σ env = 1) :
    hdV env a = hdV env b := by
  have h1 := eqCol hB (hg ⟨σ, a.k, .col b.k⟩ (by simp [heq])) hσ
  have h2 := eqCol hB (hg ⟨σ, a.v, .col b.v⟩ (by simp [heq])) hσ
  simp [hdV, h1, h2]

theorem k1_of_kc (hB : BaseHoldsX env) {h : Hd} (hh : h ∈ allHandlesX) (hc : kcV env h = 1) :
    env.trace h.k = 1 := by
  rcases kind_split hB h hh with ⟨hc', -⟩ | ⟨-, hb⟩ | ⟨hc', -⟩
  · rw [hc] at hc'; exact absurd hc' one_ne_zero
  · simp only [kcV, kbV] at hc hb; rw [hb] at hc; linear_combination hc
  · rw [hc] at hc'; exact absurd hc' one_ne_zero

theorem k2_of_kb (hB : BaseHoldsX env) {h : Hd} (hh : h ∈ allHandlesX) (hb : kbV env h = 1) :
    env.trace h.k = 2 := by
  rcases kind_split hB h hh with ⟨-, hb'⟩ | ⟨-, hb'⟩ | ⟨hc, -⟩
  · rw [hb] at hb'; exact absurd hb' one_ne_zero
  · rw [hb] at hb'; exact absurd hb' one_ne_zero
  · simp only [kcV, kbV] at hc hb; rw [hb] at hc; linear_combination hc

theorem hdV_of_k {h : Hd} {c : ℕ} (hc : c < p) (hk : env.trace h.k = (c : ZMod p)) :
    hdV env h = (c, (env.trace h.v).val) := by
  simp [hdV, hk, val_nat hc]

theorem hdV_k0 {h : Hd} (hk : env.trace h.k = 0) : hdV env h = (0, (env.trace h.v).val) := by
  simp [hdV, hk]

theorem hdV_k1 {h : Hd} (hk : env.trace h.k = 1) : hdV env h = (1, (env.trace h.v).val) := by
  simp [hdV, hk, val_one']

/-- Activity of a slot entry at a one-hot row. -/
theorem act_eval {j : ℕ} (hOH : OneHotAt env j) (x : EntX ℚ) (hl : ∀ i ∈ x.states, i < nStates)
    (hnd : x.states.Nodup) (hj : j ∈ x.states) : evalQX x.act env = evalQX x.extra env := by
  simp only [EntX.act, evalQX, selS_onehot hOH x.states hl hnd, if_pos hj, one_mul]

theorem ent_mem {S : SlotX ℚ} (hS : S ∈ (slotsX : List (SlotX ℚ))) {x : EntX ℚ} (hx : x ∈ S.ents)
    (he : evalQX x.act env = 1) : (x.rcd.map (reVal env), x.bal) ∈ activeX env :=
  List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _
    (List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp [he]⟩, rfl⟩)⟩

theorem pair_mem {S : SlotX ℚ} (hS : S ∈ (slotsX : List (SlotX ℚ))) {fl : ℕ} {a b : List RE} {bl : Bal}
    (hp : S.pair = some (fl, a, b, bl)) (hf : env.trace fl = 1) :
    (a.map (reVal env), bl) ∈ activeX env ∧ (b.map (reVal env), bl) ∈ activeX env := by
  have : pairRecsX env S = [(a.map (reVal env), bl), (b.map (reVal env), bl)] := by
    simp [pairRecsX, hp, hf]
  exact ⟨List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ (by rw [this]; simp)⟩,
    List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ (by rw [this]; simp)⟩⟩

variable {D : HX → Option Noun} {R : Registry} {limbA : ℕ → ℕ → HX}

theorem cell_of_rec (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) {P L Q : Hd}
    (hm : ((cellRecX P L Q).map (reVal env), Bal.x) ∈ activeX env) (hk : env.trace P.k = 1) :
    Cell3 D (hdV env P) (hdV env L) (hdV env Q) := by
  have := hOK _ hm
  simp only [cellRecX, recOf, cellRec, List.map_cons, List.map_nil, reVal, RecOK] at this
  rw [hdV_k1 hk]; exact this

theorem walk_of_rec (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) {root ch : Hd} {ax : ℕ}
    (hm : ((walkRecX root ax ch).map (reVal env), Bal.p) ∈ activeX env) (hk : env.trace root.k = 1) :
    ∃ Rt C, D (hdV env root) = some Rt ∧ D (hdV env ch) = some C ∧
      Noun.slot (env.trace ax).val Rt = some C := by
  have := hOK _ hm
  simp only [walkRecX, recOf, walkRec, List.map_cons, List.map_nil, reVal, RecOK] at this
  rw [hdV_k1 hk]; exact this

end Facts

/-! ## 3. Arm memberships and common row facts -/

theorem oneHotG_sub : ∀ x ∈ (oneHotG : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op0G_sub : ∀ x ∈ (op0G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op3G_sub : ∀ x ∈ (op3G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op6G_sub : ∀ x ∈ (op6G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op8G_sub : ∀ x ∈ (op8G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op9G_sub : ∀ x ∈ (op9G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem consG_sub : ∀ x ∈ (consG : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op0Eq_sub : ∀ x ∈ (op0Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op1Eq_sub : ∀ x ∈ (op1Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op3Eq_sub : ∀ x ∈ (op3Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op6Eq_sub : ∀ x ∈ (op6Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op78Eq_sub : ∀ x ∈ (op78Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op9Eq_sub : ∀ x ∈ (op9Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]

/-- Evaluate a gate fact. -/
macro "gsimp" " at " h:ident : tactic =>
  `(tactic| simp only [prodL, List.foldr, cc, notC, kcE, kbE, oneMinus, smallE, boolG, EqG.gate,
    Opnd.expr, evalQX, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_natCast, one_mul,
    mul_one, sub_zero, zero_mul, mul_zero] at $h:ident)

section Common
variable {env : Env (ZMod p)} {D : HX → Option Noun} {R : Registry} {limbA : ℕ → ℕ → HX}

theorem bool_of {x : ZMod p} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem col_bool (hB : BaseHoldsX env) {i : ℕ} (hi : (boolG (cc i) : CoeffExpr ℚ) ∈ oneHotG) :
    env.trace i = 0 ∨ env.trace i = 1 := by
  have a := arith_of_base hB (oneHotG_sub _ hi)
  gsimp at a
  exact bool_of a

theorem ent_active {j : ℕ} (hOH : OneHotAt env j) {S : SlotX ℚ} (hS : S ∈ (slotsX : List (SlotX ℚ)))
    {x : EntX ℚ} (hx : x ∈ S.ents) (hl : ∀ i ∈ x.states, i < nStates) (hnd : x.states.Nodup)
    (hj : j ∈ x.states) (he : evalQX x.extra env = 1) : (x.rcd.map (reVal env), x.bal) ∈ activeX env :=
  ent_mem hS hx (by rw [act_eval hOH x hl hnd hj, he])

theorem f_k1 (hB : BaseHoldsX env) {j : ℕ} (hOH : OneHotAt env j) (h12 : j ≠ 12) (h13 : j ≠ 13) :
    env.trace xF.k = 1 := by
  have a := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T) : CoeffExpr ℚ) ∈ svG))
  gsimp at a
  rw [oh_zero hOH (i := sS10L) (by decide) (by simpa [sS10L] using Ne.symm h12),
    oh_zero hOH (i := sS10T) (by decide) (by simpa [sS10T] using Ne.symm h13)] at a
  linear_combination a

/-- **L1**: on a non-chain row, `f = [f_h f_t]` (the `slot0` export record). -/
theorem L0 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) {j : ℕ}
    (hOH : OneHotAt env j) (hj : j ∈ opStatesX) :
    Cell3 D (hdV env xF) (hdV env xFh) (hdV env xFt) := by
  have hj' : j ≠ 12 ∧ j ≠ 13 := by simp [opStatesX] at hj; omega
  exact cell_of_rec hOK (ent_active hOH (S := slot0X) (by simp [slotsX])
    (x := ⟨opStatesX, .const 1, cellRecX xF xFh xFt, .x⟩) (by simp [slot0X]) (by decide) (by decide)
    hj (by simp [evalQX])) (f_k1 hB hOH hj'.1 hj'.2)

theorem fh_k0 (hB : BaseHoldsX env) {j : ℕ} (hOH : OneHotAt env j) (h10 : j ≠ 10) :
    env.trace xFh.k = 0 := by
  have a1 := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.sub (cc consCol) (kcE xFh) : CoeffExpr ℚ) ∈ svG))
  have a2 := arith_of_base hB (svG_sub _ (by simp [svG] : (kbE xFh : CoeffExpr ℚ) ∈ svG))
  gsimp at a1; gsimp at a2
  rw [oh_zero hOH (i := consCol) (by decide) (by simpa [consCol] using Ne.symm h10), a2] at a1
  linear_combination -a1

theorem fhv_op (hB : BaseHoldsX env) {j : ℕ} (hOH : OneHotAt env j) (hj : j < 10) :
    env.trace xFh.v = (j : ZMod p) := by
  have := eqg hB (g := ⟨cc j, xFh.v, .cst ((j : ℕ) : ℚ)⟩)
    (svEq_sub _ (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    (by simp only [cc, evalQX]; exact oh_one hOH (by simp [nStates]; omega))
  simpa [Opnd.expr, evalQX] using this

theorem fh_small (hB : BaseHoldsX env) {j : ℕ} (hOH : OneHotAt env j) (h10 : j ≠ 10) {c : ℕ}
    (hc : c < p) (hv : env.trace xFh.v = (c : ZMod p)) : hdV env xFh = (0, c) := by
  rw [hdV_k0 (fh_k0 hB hOH h10), hv, val_nat hc]

/-- An opcode row's head is the small atom `j` (`j < 10`). -/
theorem fh_op (hB : BaseHoldsX env) (hp : 17 < p) {j : ℕ} (hOH : OneHotAt env j) (hj : j < 10) :
    hdV env xFh = (0, j) :=
  fh_small hB hOH (by omega) (by omega) (fhv_op hB hOH hj)

/-- An `s10 / s11*` row's head is `10` / `11`. -/
theorem fh_new (hB : BaseHoldsX env) (hp : 17 < p) {j : ℕ} (hOH : OneHotAt env j) {c : ℚ} {n : ℕ}
    (hg : (⟨cc j, xFh.v, .cst c⟩ : EqG ℚ) ∈ (svEq : List (EqG ℚ))) (hj : j < nStates) (h10 : j ≠ 10)
    (hc : ((c : ℚ) : ZMod p) = (n : ZMod p)) (hn : n < p) : hdV env xFh = (0, n) := by
  have := eqg hB (svEq_sub _ hg) (by simp only [cc, evalQX]; exact oh_one hOH hj)
  simp only [Opnd.expr, evalQX] at this
  exact fh_small hB hOH h10 hn (this.trans hc)

/-- **L2**: on `l2X`, `f_t` is a cell and `f_t = [f_th f_tt]`. -/
theorem L2 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) {j : ℕ}
    (hOH : OneHotAt env j) (hj : j ∈ l2X) :
    env.trace xFt.k = 1 ∧ Cell3 D (hdV env xFt) (hdV env xFth) (hdV env xFtt) := by
  have a := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.mul (selS l2X) (oneMinus (kcE xFt)) : CoeffExpr ℚ) ∈ svG))
  have hs := selS_onehot hOH l2X (by decide) (by decide)
  rw [if_pos hj] at hs
  simp only [evalQX, hs, oneMinus, kcE, kbE, cc, Rat.cast_one, Rat.cast_ofNat, one_mul] at a
  have hk := k1_of_kc hB (by decide) (show kcV env xFt = 1 by simp only [kcV]; linear_combination -a)
  exact ⟨hk, cell_of_rec hOK (ent_active hOH (S := slot1X) (by simp [slotsX])
    (x := ⟨l2X, .const 1, cellRecX xFt xFth xFtt, .x⟩) (by simp [slot1X]) (by decide) (by decide) hj
    (by simp [evalQX])) hk⟩

/-- **L3**: on `l3X` (`s10, s11d, s11j`), `f_th = [f_tth f_ttt]`. -/
theorem L3 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) {j : ℕ}
    (hOH : OneHotAt env j) (hj : j ∈ l3X) :
    Cell3 D (hdV env xFth) (hdV env xFtth) (hdV env xFttt) := by
  have a := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.mul (selS l3X) (oneMinus (kcE xFth)) : CoeffExpr ℚ) ∈ svG))
  have hs := selS_onehot hOH l3X (by decide) (by decide)
  rw [if_pos hj] at hs
  simp only [evalQX, hs, oneMinus, kcE, kbE, cc, Rat.cast_one, Rat.cast_ofNat, one_mul] at a
  have hk := k1_of_kc hB (by decide) (show kcV env xFth = 1 by simp only [kcV]; linear_combination -a)
  exact cell_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
    (x := ⟨l3X, .const 1, cellRecX xFth xFtth xFttt, .x⟩) (by simp [slot2X]) (by decide) (by decide)
    hj (by simp [evalQX])) hk

end Common

/-! ## 4. -/

section Old
variable {env : Env (ZMod p)} {D : HX → Option Noun} {R : Registry} {limbA : ℕ → ℕ → HX}

theorem sem_s0 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 0) : RowSemX0 p D R (rowOfX env .s0) := by
  have h0 : env.trace 0 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (op0G_sub _ (by simp [op0G] : (.mul (cc 0) (cc xFt.k) : CoeffExpr ℚ) ∈ op0G))
  have a2 := arith_of_base hB (op0G_sub _ (by simp [op0G] :
    (prodL [cc 0, notC z1X, oneMinus (kcE xS)] : CoeffExpr ℚ) ∈ op0G))
  have a3 := arith_of_base hB (op0G_sub _ (by simp [op0G] :
    (prodL [cc 0, cc z1X, .sub (cc vX) (.const 1)] : CoeffExpr ℚ) ∈ op0G))
  have e1 := eqCol hB (op0Eq_sub _ (by simp [op0Eq] : (⟨cc 0, vX, .col xFt.v⟩ : EqG ℚ) ∈ op0Eq))
    (by simp [cc, evalQX, h0])
  gsimp at a1; gsimp at a2; gsimp at a3
  rw [h0, one_mul] at a1 a2 a3
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (env.trace xFt.v).val,
    hdV_k0 a1, ?_⟩
  rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
  · right
    rw [hz] at a2
    have hs : env.trace xS.k = 1 := k1_of_kc hB (by decide) (by simp only [kcV]; linear_combination -a2)
    have := walk_of_rec hOK (ent_active hOH (S := slot1X) (by simp [slotsX])
      (x := ⟨[0], notC z1X, walkRecX xS xFt.v xE, .p⟩) (by simp [slot1X]) (by decide) (by decide)
      (by simp) (by simp [notC, cc, evalQX, hz])) hs
    exact this
  · left
    rw [hz, one_mul] at a3
    refine ⟨?_, hdEq hB (σ := .mul (cc 0) (cc z1X)) (fun g hg => op0Eq_sub _ (by simp [op0Eq]; exact Or.inr hg))
      (by simp [cc, evalQX, h0, hz])⟩
    rw [← e1, sub_eq_zero.mp a3, val_one']

theorem sem_s1 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 1) : RowSemX0 p D R (rowOfX env .s1) := by
  have h1 : env.trace 1 = 1 := oh_one hOH (by decide)
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide),
    hdEq hB (σ := cc 1) (fun g hg => op1Eq_sub _ (by simpa [op1Eq] using hg)) (by simp [cc, evalQX, h1])⟩

theorem sem_s2 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 2) : RowSemX0 p D R (rowOfX env .s2) := by
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2⟩

theorem sem_s7 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 7) : RowSemX0 p D R (rowOfX env .s7) := by
  have h7 : env.trace 7 = 1 := oh_one hOH (by decide)
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2,
    hdEq hB (σ := cc 7) (fun g hg => op78Eq_sub _ (by simp [op78Eq]; exact Or.inl hg))
      (by simp [cc, evalQX, h7])⟩

theorem sem_s8 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 8) : RowSemX0 p D R (rowOfX env .s8) := by
  have h8 : env.trace 8 = 1 := oh_one hOH (by decide)
  have a := arith_of_base hB (op8G_sub _ (by simp [op8G] :
    (.mul (cc 8) (oneMinus (kcE xM)) : CoeffExpr ℚ) ∈ op8G))
  gsimp at a; rw [h8, one_mul] at a
  have hk := k1_of_kc hB (by decide) (show kcV env xM = 1 by simp only [kcV]; linear_combination -a)
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2,
    cell_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
      (x := ⟨[8], .const 1, cellRecX xM xSf2 xS, .x⟩) (by simp [slot2X]) (by decide) (by decide)
      (by simp) (by simp [evalQX])) hk,
    hdEq hB (σ := cc 8) (fun g hg => op78Eq_sub _ (by simp [op78Eq]; exact Or.inr hg))
      (by simp [cc, evalQX, h8])⟩

theorem sem_cons (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hOH : OneHotAt env 10) : RowSemX0 p D R (rowOfX env .cons) := by
  have h10 : env.trace 10 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.sub (cc consCol) (kcE xFh) : CoeffExpr ℚ) ∈ svG))
  have a2 := arith_of_base hB (consG_sub _ (by simp [consG] :
    (.mul (cc consCol) (oneMinus (kcE xE)) : CoeffExpr ℚ) ∈ consG))
  gsimp at a1; gsimp at a2
  simp only [consCol] at a1 a2
  rw [h10] at a1 a2; rw [one_mul] at a2
  have hfh := k1_of_kc hB (by decide) (show kcV env xFh = 1 by simp only [kcV]; linear_combination -a1)
  have he := k1_of_kc hB (by decide) (show kcV env xE = 1 by simp only [kcV]; linear_combination -a2)
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), by rw [hdV_k1 hfh],
    cell_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
      (x := ⟨[consCol], .const 1, cellRecX xE xSf1 xSf2, .x⟩) (by simp [slot2X]) (by decide) (by decide)
      (by simp [consCol]) (by simp [evalQX])) he⟩

theorem sem_s3 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 3) : RowSemX0 p D R (rowOfX env .s3) := by
  have h3 : env.trace 3 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (op3G_sub _ (by simp [op3G] : (.mul (cc 3) (cc xE.k) : CoeffExpr ℚ) ∈ op3G))
  have a2 := arith_of_base hB (op3G_sub _ (by simp [op3G] :
    (.mul (cc 3) (.add (.sub (cc betaX) (.const 1)) (kcE xSf1)) : CoeffExpr ℚ) ∈ op3G))
  have e1 := eqCol hB (op3Eq_sub _ (by simp [op3Eq] : (⟨cc 3, xE.v, .col betaX⟩ : EqG ℚ) ∈ op3Eq))
    (by simp [cc, evalQX, h3])
  gsimp at a1; gsimp at a2
  rw [h3, one_mul] at a1 a2
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), ?_⟩
  rcases kind_split hB xSf1 (by decide) with ⟨hc, hb⟩ | ⟨hc, hb⟩ | ⟨hc, hb⟩
  · right
    simp only [kcV] at hc
    have hk : env.trace xSf1.k = 0 := by simp only [kbV] at hb; rw [hb] at hc; linear_combination hc
    have hβ : env.trace betaX = 1 := by rw [hc] at a2; linear_combination a2
    refine ⟨Or.inl (by simp [hdV, hk]), ?_⟩
    rw [hdV_k0 a1, e1, hβ, val_one']
  · left
    have hk := k1_of_kc hB (by decide) hc
    simp only [kcV] at hc
    have hβ : env.trace betaX = 0 := by rw [hc] at a2; linear_combination a2
    have hc3 := cell_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
      (x := ⟨[3], kcE xSf1, cellRecX xSf1 xFtth xFttt, .x⟩) (by simp [slot2X]) (by decide) (by decide)
      (by simp) (by simpa [kcE, kbE, cc, evalQX] using hc)) hk
    obtain ⟨A, B, hAB, -, -⟩ := hc3
    exact ⟨⟨A, B, hAB⟩, by rw [hdV_k0 a1, e1, hβ, ZMod.val_zero]⟩
  · right
    have hk := k2_of_kb hB (by decide) hb
    simp only [kcV] at hc
    have hβ : env.trace betaX = 1 := by rw [hc] at a2; linear_combination a2
    refine ⟨Or.inr ?_, ?_⟩
    · rw [hdV_of_k (c := 2) (by omega) (by rw [hk]; norm_num)]
    · rw [hdV_k0 a1, e1, hβ, val_one']

theorem sem_s6 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 6) : RowSemX0 p D R (rowOfX env .s6) := by
  have h6 : env.trace 6 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (op6G_sub _ (by simp [op6G] : (.mul (cc 6) (cc xSf2.k) : CoeffExpr ℚ) ∈ op6G))
  have a2 := arith_of_base hB (op6G_sub _ (by simp [op6G] :
    (prodL [cc 6, cc vX, .sub (cc vX) (.const 1)] : CoeffExpr ℚ) ∈ op6G))
  have a3 := arith_of_base hB (svG_sub _ (by simp [svG] :
    (.mul (cc 6) (oneMinus (kcE xFtt)) : CoeffExpr ℚ) ∈ svG))
  have e1 := eqCol hB (op6Eq_sub _ (by simp [op6Eq] : (⟨cc 6, vX, .col xSf2.v⟩ : EqG ℚ) ∈ op6Eq))
    (by simp [cc, evalQX, h6])
  gsimp at a1; gsimp at a2; gsimp at a3
  rw [h6, one_mul] at a1 a2 a3
  have hk := k1_of_kc hB (by decide) (show kcV env xFtt = 1 by simp only [kcV]; linear_combination -a3)
  have hE := hdEq hB (σ := cc 6) (a := xE) (b := xSf1)
    (fun g hg => op6Eq_sub _ (by simp only [op6Eq, List.mem_append]; tauto)) (by simp [cc, evalQX, h6])
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2,
    cell_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
      (x := ⟨[6], .const 1, cellRecX xFtt xFtth xFttt, .x⟩) (by simp [slot2X]) (by decide) (by decide)
      (by simp) (by simp [evalQX])) hk, (env.trace vX).val, ?_, by rw [hdV_k0 a1, ← e1], ?_, hE⟩
  · rcases bool_of a2 with h | h <;> simp [h, val_one']
  · rcases bool_of a2 with h | h
    · simp only [h, ZMod.val_zero, if_true]
      exact hdEq hB (σ := .mul (cc 6) (notC vX))
        (fun g hg => op6Eq_sub _ (by simp only [op6Eq, List.mem_append]; tauto))
        (by simp [cc, notC, evalQX, h6, h])
    · simp only [h, val_one', one_ne_zero, if_false]
      exact hdEq hB (σ := .mul (cc 6) (cc vX))
        (fun g hg => op6Eq_sub _ (by simp only [op6Eq, List.mem_append]; tauto))
        (by simp [cc, evalQX, h6, h])

theorem sem_s9 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 9) : RowSemX0 p D R (rowOfX env .s9) := by
  have h9 : env.trace 9 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (op9G_sub _ (by simp [op9G] : (.mul (cc 9) (cc xFth.k) : CoeffExpr ℚ) ∈ op9G))
  have a2 := arith_of_base hB (op9G_sub _ (by simp [op9G] :
    (prodL [cc 9, notC z1X, oneMinus (kcE xSf1)] : CoeffExpr ℚ) ∈ op9G))
  have a3 := arith_of_base hB (op9G_sub _ (by simp [op9G] :
    (prodL [cc 9, cc z1X, .sub (cc vX) (.const 1)] : CoeffExpr ℚ) ∈ op9G))
  have e1 := eqCol hB (op9Eq_sub _ (by simp [op9Eq] : (⟨cc 9, vX, .col xFth.v⟩ : EqG ℚ) ∈ op9Eq))
    (by simp [cc, evalQX, h9])
  gsimp at a1; gsimp at a2; gsimp at a3
  rw [h9, one_mul] at a1 a2 a3
  have hE := hdEq hB (σ := cc 9) (a := xE) (b := xSf2)
    (fun g hg => op9Eq_sub _ (by simp only [op9Eq, List.mem_append]; tauto)) (by simp [cc, evalQX, h9])
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2,
    ⟨(env.trace xFth.v).val, hdV_k0 a1, ?_⟩, hE⟩
  rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
  · right
    rw [hz] at a2
    have hs : env.trace xSf1.k = 1 :=
      k1_of_kc hB (by decide) (by simp only [kcV]; linear_combination -a2)
    exact walk_of_rec hOK (ent_active hOH (S := slot2X) (by simp [slotsX])
      (x := ⟨[9], notC z1X, walkRecX xSf1 xFth.v xM, .p⟩) (by simp [slot2X]) (by decide) (by decide)
      (by simp) (by simp [notC, cc, evalQX, hz])) hs
  · left
    rw [hz, one_mul] at a3
    refine ⟨by rw [← e1, sub_eq_zero.mp a3, val_one'], hdEq hB (σ := .mul (cc 9) (cc z1X))
      (fun g hg => op9Eq_sub _ (by simp only [op9Eq, List.mem_append]; tauto))
      (by simp [cc, evalQX, h9, hz])⟩

end Old

/-! ## 5. The new arms: op 4, op 5, op 10, op 11 -/

section New
variable {env : Env (ZMod p)} {D : HX → Option Noun} {R : Registry} {limbA : ℕ → ℕ → HX}

theorem inc_of_rec (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hm : (incRecX.map (reVal env), Bal.s) ∈ activeX env) :
    ∃ n : ℕ, D (hdV env xSf1) = some (.atom n) ∧ D (hdV env xE) = some (.atom (n + 1)) := by
  have := hOK _ hm
  simpa [incRecX, reVal, RecOK, hdV] using this

/-- **op 4** (fast from the gates, slow from the served `TAG_inc` record). -/
theorem sem_s4 (hD : DenOKX p D) (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hp : 17 < p) (hOH : OneHotAt env 4) : RowSemX0 p D R (rowOfX env .s4) := by
  have h4 : env.trace 4 = 1 := oh_one hOH (by decide)
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), ?_⟩
  rcases col_bool hB (i := fastX) (by simp [oneHotG]) with hf | hf
  · exact inc_of_rec hOK (ent_active hOH (S := slot1X) (by simp [slotsX])
      (x := ⟨[4], notC fastX, incRecX, .s⟩) (by simp [slot1X]) (by decide) (by decide) (by simp)
      (by simp [notC, cc, evalQX, hf]))
  · exact op4_fast_sem hB h4 hf hD

/-- **op 5 "≠", the first-difference leaves differ** (`neGate` over `(kc, kb, v)`; both big: the
α pair's `walkRecA` records and the functionality of `limbA`). -/
theorem differ_leaves (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hp : 17 < p) (h5 : env.trace 5 = 1) (hβ : env.trace betaX = 1) :
    DifferX p D (hdV env xFtth) (hdV env xFttt) := by
  have aN := arith_of_base hB (op5G_sub _ (by simp [op5G] : (neGateX : CoeffExpr ℚ) ∈ op5G))
  have aK := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (prodL [cc 5, cc betaX, kcE xFtth, kcE xFttt] : CoeffExpr ℚ) ∈ op5G))
  have ev1 := eqCol hB (op5Eq_sub _ (by simp [op5Eq] :
    (⟨prodL [cc 5, cc betaX, smallE xFtth], vX, .col xFtth.v⟩ : EqG ℚ) ∈ op5Eq))
  have ev2 := eqCol hB (op5Eq_sub _ (by simp [op5Eq] :
    (⟨prodL [cc 5, cc betaX, smallE xFttt], v2X, .col xFttt.v⟩ : EqG ℚ) ∈ op5Eq))
  simp only [neGateX] at aN
  gsimp at aN; gsimp at aK
  rw [h5, hβ, one_mul, one_mul] at aN aK
  have lt := fun x : ZMod p => ZMod.val_lt x
  have k2 : ((2 : ZMod p)).val = 2 := by simpa using val_nat (p := p) (n := 2) (by omega)
  rcases kind_split hB xFtth (by decide) with ⟨c1, b1⟩ | ⟨c1, b1⟩ | ⟨c1, b1⟩ <;>
  rcases kind_split hB xFttt (by decide) with ⟨c2, b2⟩ | ⟨c2, b2⟩ | ⟨c2, b2⟩ <;>
  simp only [kcV, kbV] at c1 b1 c2 b2
  · -- small, small
    have hk1 : env.trace xFtth.k = 0 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 0 := by rw [b2] at c2; linear_combination c2
    rw [c1, c2, b1, b2] at aN
    have e1 := ev1 (by simp [prodL, cc, smallE, kbE, evalQX, h5, hβ, hk1, b1])
    have e2 := ev2 (by simp [prodL, cc, smallE, kbE, evalQX, h5, hβ, hk2, b2])
    have hne : env.trace xFtth.v ≠ env.trace xFttt.v := by
      intro h; rw [e1, e2, h] at aN; simp at aN
    rw [hdV_k0 hk1, hdV_k0 hk2]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => hne (ZMod.val_injective p h)⟩))))
  · have hk1 : env.trace xFtth.k = 0 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 1 := by rw [b2] at c2; linear_combination c2
    rw [hdV_k0 hk1, hdV_k1 hk2]
    exact Or.inl ⟨rfl, lt _, Or.inl rfl⟩
  · have hk1 : env.trace xFtth.k = 0 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 2 := by rw [b2] at c2; linear_combination c2
    rw [hdV_k0 hk1, hdV_of_k (c := 2) (by omega) (by rw [hk2]; norm_num)]
    exact Or.inl ⟨rfl, lt _, Or.inr rfl⟩
  · have hk1 : env.trace xFtth.k = 1 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 0 := by rw [b2] at c2; linear_combination c2
    rw [hdV_k1 hk1, hdV_k0 hk2]
    exact Or.inr (Or.inl ⟨rfl, lt _, Or.inl rfl⟩)
  · rw [c1, c2] at aK; simp at aK
  · have hk1 : env.trace xFtth.k = 1 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 2 := by rw [b2] at c2; linear_combination c2
    rw [hdV_k1 hk1, hdV_of_k (c := 2) (by omega) (by rw [hk2]; norm_num)]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have hk1 : env.trace xFtth.k = 2 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 0 := by rw [b2] at c2; linear_combination c2
    rw [hdV_of_k (c := 2) (by omega) (by rw [hk1]; norm_num), hdV_k0 hk2]
    exact Or.inr (Or.inl ⟨rfl, lt _, Or.inr rfl⟩)
  · have hk1 : env.trace xFtth.k = 2 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 1 := by rw [b2] at c2; linear_combination c2
    rw [hdV_of_k (c := 2) (by omega) (by rw [hk1]; norm_num), hdV_k1 hk2]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · -- big, big: the α pair
    have hk1 : env.trace xFtth.k = 2 := by rw [b1] at c1; linear_combination c1
    have hk2 : env.trace xFttt.k = 2 := by rw [b2] at c2; linear_combination c2
    obtain ⟨hpr2, hkk, hlv⟩ := op5_pair_row hB h5 hβ (by simpa [kbV] using b1) (by simpa [kbV] using b2)
    have hpm := pair_mem (env := env) (S := slot3X) (fl := pr2X) (a := walkRecAX xFtth xL1)
      (b := walkRecAX xFttt xL2) (bl := .s) (by simp [slotsX]) rfl hpr2
    have r1 := hOK _ hpm.1
    have r2 := hOK _ hpm.2
    simp only [walkRecAX, List.map_cons, List.map_nil, reVal, RecOK] at r1 r2
    obtain ⟨n1, hn1, hl1⟩ := r1
    obtain ⟨n2, hn2, hl2⟩ := r2
    rw [hdV_of_k (c := 2) (by omega) (by rw [hk1]; norm_num),
      hdV_of_k (c := 2) (by omega) (by rw [hk2]; norm_num)]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n1, n2, hn1, hn2, fun h => ?_⟩))))
    subst h
    rw [hl1] at hl2
    simp only [Prod.mk.injEq] at hl2
    have ek := ZMod.val_injective p hl2.1
    have ev := ZMod.val_injective p hl2.2
    simp only [tr] at hkk hlv
    have h0 : env.trace xL1.k = 0 := by
      have : env.trace xL1.k * env.trace xL1.k = 0 := by
        calc env.trace xL1.k * env.trace xL1.k = env.trace xL1.k * env.trace xL2.k := by rw [ek]
          _ = 0 := hkk
      exact mul_self_eq_zero.mp this
    exact hlv h0 (ek ▸ h0) ev

/-- **op 5**: `=` by handle equality, `≠` by the certified difference of the results (axis `1`) or of
the first-difference leaves read at a common axis. -/
theorem sem_s5 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 5) : RowSemX0 p D R (rowOfX env .s5) := by
  have h5 : env.trace 5 = 1 := oh_one hOH (by decide)
  have a1 := arith_of_base hB (op5G_sub _ (by simp [op5G] : (.mul (cc 5) (cc xE.k) : CoeffExpr ℚ) ∈ op5G))
  have aP := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
  have aS1 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (.mul (cc prX) (oneMinus (kcE xSf1)) : CoeffExpr ℚ) ∈ op5G))
  have aS2 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (.mul (cc prX) (oneMinus (kcE xSf2)) : CoeffExpr ℚ) ∈ op5G))
  have e1 := eqCol hB (op5Eq_sub _ (by simp [op5Eq] : (⟨cc 5, xE.v, .col betaX⟩ : EqG ℚ) ∈ op5Eq))
    (by simp [cc, evalQX, h5])
  simp only [prGateX] at aP
  gsimp at a1; gsimp at aP; gsimp at aS1; gsimp at aS2
  rw [h5, one_mul] at a1
  have h12 : env.trace sS10L = 0 := oh_zero hOH (by decide) (by decide)
  rw [h12, h5, one_mul, sub_zero] at aP
  simp only [RowSemX0, rowOfX, Op5SemX]
  refine ⟨L0 hB hOK hOH (by decide), fh_op hB hp hOH (by decide), (L2 hB hOK hOH (by decide)).2, ?_⟩
  rcases col_bool hB (i := betaX) (by simp [oneHotG]) with hβ | hβ
  · left
    refine ⟨hdEq hB (σ := prodL [cc 5, notC betaX])
      (fun g hg => op5Eq_sub _ (by simp only [op5Eq, List.mem_append]; tauto))
      (by simp [prodL, cc, notC, evalQX, h5, hβ]), ?_⟩
    rw [hdV_k0 a1, e1, hβ, ZMod.val_zero]
  · right
    refine ⟨by rw [hdV_k0 a1, e1, hβ, val_one'], ?_⟩
    have hdl := differ_leaves hB hOK hp h5 hβ
    rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
    · right
      rw [hβ, hz, one_mul] at aP
      have hpr : env.trace prX = 1 := by linear_combination aP
      rw [hpr, one_mul] at aS1 aS2
      have k1 := k1_of_kc hB (by decide) (show kcV env xSf1 = 1 by simp only [kcV]; linear_combination -aS1)
      have k2 := k1_of_kc hB (by decide) (show kcV env xSf2 = 1 by simp only [kcV]; linear_combination -aS2)
      have hpm := pair_mem (env := env) (S := slot2X) (fl := prX) (a := walkRecX xSf1 xM.v xFtth)
        (b := walkRecX xSf2 xM.v xFttt) (bl := .p) (by simp [slotsX]) rfl hpr
      obtain ⟨X1, A1, hX1, hA1, hs1⟩ := walk_of_rec hOK hpm.1 k1
      obtain ⟨X2, A2, hX2, hA2, hs2⟩ := walk_of_rec hOK hpm.2 k2
      exact ⟨_, X1, X2, A1, A2, hX1, hX2, hs1, hs2, hA1, hA2, hdl⟩
    · left
      have q1 := hdEq hB (σ := prodL [cc 5, cc betaX, cc z1X]) (a := xFtth) (b := xSf1)
        (fun g hg => op5Eq_sub _ (by simp only [op5Eq, List.mem_append]; tauto))
        (by simp [prodL, cc, evalQX, h5, hβ, hz])
      have q2 := hdEq hB (σ := prodL [cc 5, cc betaX, cc z1X]) (a := xFttt) (b := xSf2)
        (fun g hg => op5Eq_sub _ (by simp only [op5Eq, List.mem_append]; tauto))
        (by simp [prodL, cc, evalQX, h5, hβ, hz])
      rw [q1, q2] at hdl; exact hdl

/-- **op 10, `s10`**: `f = [10 [[a c] d]]` with a small axis atom `a`; axis `1` makes `e = new`,
otherwise the served walk read `slot a e = new` (`inv3`). -/
theorem sem_s10 (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 11) : RowSemX0 p D R (rowOfX env .s10) := by
  have h11 : env.trace sS10 = 1 := oh_one hOH (by decide)
  obtain ⟨hfh, hk, hv, hz1, hz0⟩ := s10_row hB h11
  simp only [tr] at hfh hk hv hz1 hz0
  have v10 : ((10 : ZMod p)).val = 10 := by simpa using val_nat (p := p) (n := 10) (by omega)
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), by rw [hdV_k0 (fh_k0 hB hOH (by decide)), hfh, v10],
    (L2 hB hOK hOH (by decide)).2, L3 hB hOK hOH (by decide), (env.trace xFtth.v).val, hdV_k0 hk, ?_⟩
  rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
  · right
    have he := k1_of_kc hB (by decide) (hz0 hz)
    have := walk_of_rec hOK (ent_active hOH (S := slot3X) (by simp [slotsX])
      (x := ⟨[sS10], notC z1X, walkRecX xE vX xSf1, .p⟩) (by simp [slot3X]) (by decide) (by decide)
      (by simp [sS10]) (by simp [notC, cc, evalQX, hz])) he
    rw [hv] at this
    exact this
  · left
    obtain ⟨h1, hek, hev⟩ := hz1 hz
    refine ⟨by rw [← hv, h1, val_one'], by simp [hdV, hek, hev]⟩

theorem two_mul_xor (V b : ℕ) (hb : b = 0 ∨ b = 1) : (2 * V + b) ^^^ 1 = 2 * V + 1 - b := by
  rw [xor_one_eq]
  rcases hb with rfl | rfl
  · simp
  · simp [Nat.add_mod]

/-- **op 10, `s10L`**: the chain level `a = 2v + β ≥ 2`, the sibling axis `a xor 1` read in `old` and
`e` with ONE agreed leaf — under the named halving hypothesis `hv` (`2·val v + 1 < p`, `1 ≤ val v`),
which the gates alone do NOT give (`Batch2903` FINDING). -/
theorem sem_s10L (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hOH : OneHotAt env 12) (hv : 1 ≤ (env.trace vX).val ∧ 2 * (env.trace vX).val + 1 < p) :
    RowSemX0 p D R (rowOfX env .s10L) := by
  have h12 : env.trace sS10L = 1 := oh_one hOH (by decide)
  obtain ⟨hfk, hfv, -, hmv, hpr, -, h1v, h1k, h2v, h2k, htv, htk⟩ :=
    s10L_row hB h12 (oh_zero hOH (by decide) (by decide)) (oh_zero hOH (by decide) (by decide))
  simp only [tr] at hfk hfv hmv hpr h1v h1k h2v h2k htv htk
  have aS1 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (.mul (cc prX) (oneMinus (kcE xSf1)) : CoeffExpr ℚ) ∈ op5G))
  have aS2 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (.mul (cc prX) (oneMinus (kcE xSf2)) : CoeffExpr ℚ) ∈ op5G))
  gsimp at aS1; gsimp at aS2
  rw [hpr, one_mul] at aS1 aS2
  have k1 := k1_of_kc hB (by decide) (show kcV env xSf1 = 1 by simp only [kcV]; linear_combination -aS1)
  have k2 := k1_of_kc hB (by decide) (show kcV env xSf2 = 1 by simp only [kcV]; linear_combination -aS2)
  have hpm := pair_mem (env := env) (S := slot2X) (fl := prX) (a := walkRecX xSf1 xM.v xFtth)
    (b := walkRecX xSf2 xM.v xFttt) (bl := .p) (by simp [slotsX]) rfl hpr
  obtain ⟨X1, A1, hX1, hA1, hs1⟩ := walk_of_rec hOK hpm.1 k1
  obtain ⟨X2, A2, hX2, hA2, hs2⟩ := walk_of_rec hOK hpm.2 k2
  have hsf1 : hdV env xSf1 = hdV env xS := by simp [hdV, h1v, h1k]
  have hsf2 : hdV env xSf2 = hdV env xE := by simp [hdV, h2v, h2k]
  have htt : hdV env xFtth = hdV env xFttt := by simp [hdV, htv, htk]
  rw [htt, hA2] at hA1
  cases Option.some.inj hA1
  set V := (env.trace vX).val with hV
  have hvV : env.trace vX = (V : ZMod p) := by rw [hV, ZMod.natCast_zmod_val]
  rcases col_bool hB (i := betaX) (by simp [oneHotG]) with hβ | hβ
  · have hfa : (env.trace xF.v).val = 2 * V + 0 := by
      rw [hfv, hβ, hvV, add_zero, show (2 : ZMod p) * (V : ZMod p) = ((2 * V : ℕ) : ZMod p) by push_cast; ring,
        val_nat (by omega)] <;> omega
    have hma : (env.trace xM.v).val = 2 * V + 1 - 0 := by
      rw [hmv, hfv, hβ, hvV, show (2 : ZMod p) * (V : ZMod p) + 0 + 1 - 2 * 0 = ((2 * V + 1 : ℕ) : ZMod p) by
        push_cast; ring, val_nat (by omega)] <;> omega
    simp only [RowSemX0, rowOfX]
    refine ⟨_, by rw [hdV_k0 hfk], by rw [hfa]; omega, X1, X2, A1, by rw [← hsf1]; exact hX1,
      by rw [← hsf2]; exact hX2, ?_, ?_⟩
    · rw [hfa, two_mul_xor V 0 (Or.inl rfl), ← hma]; exact hs1
    · rw [hfa, two_mul_xor V 0 (Or.inl rfl), ← hma]; exact hs2
  · have hfa : (env.trace xF.v).val = 2 * V + 1 := by
      rw [hfv, hβ, hvV, show (2 : ZMod p) * (V : ZMod p) + 1 = ((2 * V + 1 : ℕ) : ZMod p) by push_cast; ring,
        val_nat (by omega)] <;> omega
    have hma : (env.trace xM.v).val = 2 * V + 1 - 1 := by
      rw [hmv, hfv, hβ, hvV, show (2 : ZMod p) * (V : ZMod p) + 1 + 1 - 2 * 1 = ((2 * V : ℕ) : ZMod p) by
        push_cast; ring, val_nat (by omega)] <;> omega
    simp only [RowSemX0, rowOfX]
    refine ⟨_, by rw [hdV_k0 hfk], by rw [hfa]; omega, X1, X2, A1, by rw [← hsf1]; exact hX1,
      by rw [← hsf2]; exact hX2, ?_, ?_⟩
    · rw [hfa, two_mul_xor V 1 (Or.inr rfl), ← hma]; exact hs1
    · rw [hfa, two_mul_xor V 1 (Or.inr rfl), ← hma]; exact hs2

/-- **op 10, `s10T`**: the chain terminal's formula is the small atom `1`. -/
theorem sem_s10T (hB : BaseHoldsX env) (hOH : OneHotAt env 13) : RowSemX0 p D R (rowOfX env .s10T) := by
  obtain ⟨hk, hv⟩ := s10T_row hB (oh_one hOH (by decide)) (oh_zero hOH (by decide) (by decide))
  simp only [tr] at hk hv
  simp only [RowSemX0, rowOfX]
  rw [hdV_k0 hk, hv, val_one']

theorem fh11 (hB : BaseHoldsX env) (hp : 17 < p) {j : ℕ} (hOH : OneHotAt env j) (h10 : j ≠ 10)
    (hv : env.trace xFh.v = 11) : hdV env xFh = (0, 11) := by
  rw [hdV_k0 (fh_k0 hB hOH h10), hv]
  simpa using val_nat (p := p) (n := 11) (by omega)

theorem sem_s11s (hD : DenOKX p D) (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hp : 17 < p) (hOH : OneHotAt env 14) : RowSemX0 p D R (rowOfX env .s11s) := by
  obtain ⟨hfh, -, hs, -, -⟩ := s11_row hB hOH (Or.inl rfl)
  have hc := hs rfl
  have L2' := (L2 hB hOK hOH (by decide)).2
  simp only [RowSemX0, rowOfX]
  refine ⟨L0 hB hOK hOH (by decide), fh11 hB hp hOH (by decide) hfh, L2', ?_⟩
  obtain ⟨A, B, -, hA, -⟩ := L2'
  rcases kind_split hB xFth (by decide) with ⟨c, b⟩ | ⟨c, -⟩ | ⟨-, b⟩
  · simp only [kcV, kbV] at c b
    have hk : env.trace xFth.k = 0 := by rw [b] at c; linear_combination c
    rw [hdV_k0 hk, hD.atom] at hA ⊢
    exact ⟨_, rfl⟩
  · rw [hc] at c; exact absurd c.symm one_ne_zero
  · have hk := k2_of_kb hB (by decide) b
    rw [hdV_of_k (c := 2) (by omega) (by rw [hk]; norm_num)] at hA ⊢
    obtain ⟨n, rfl, -⟩ := hD.big _ _ hA
    exact ⟨n, hA⟩

theorem sem_s11d (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 15) : RowSemX0 p D R (rowOfX env .s11d) := by
  obtain ⟨hfh, -, -, -, -⟩ := s11_row hB hOH (Or.inr (Or.inl rfl))
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh11 hB hp hOH (by decide) hfh, (L2 hB hOK hOH (by decide)).2,
    L3 hB hOK hOH (by decide)⟩

/-- **op 11, `s11j`**: the served `TAG_jet` record names a registered template whose relation holds
between the row's subject and result (J-3b `jetChip_holds` + J-1's registry, as `RecOK`).  The
record's id is the clue's value `sf1`, a small atom by the gate (`s11j_wild`). -/
theorem sem_s11j (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r) (hp : 17 < p)
    (hOH : OneHotAt env 16) : RowSemX0 p D R (rowOfX env .s11j) := by
  obtain ⟨hfh, -, -, -, -⟩ := s11_row hB hOH (Or.inr (Or.inr rfl))
  have hk : env.trace xSf1.k = 0 := (s11j_wild hB hOH).2
  have := hOK _ (ent_active hOH (S := slot3X) (by simp [slotsX])
    (x := ⟨[sS11j], .const 1, jetRecX, .s⟩) (by simp [slot3X]) (by decide) (by decide)
    (by simp [sS11j]) (by simp [evalQX]))
  simp only [jetRecX, List.map_cons, List.map_nil, reVal, RecOK] at this
  obtain ⟨j, hR, hc, S, E, hS, hE, hrel⟩ := this
  simp only [RowSemX0, rowOfX]
  exact ⟨L0 hB hOK hOH (by decide), fh11 hB hp hOH (by decide) hfh, (L2 hB hOK hOH (by decide)).2,
    L3 hB hOK hOH (by decide), _, j, hdV_k0 hk, hR, hc, S, E, hS, hE, hrel⟩

end New

/-! ## 6. The decode -/

section Main
variable {env : Env (ZMod p)} {D : HX → Option Noun} {R : Registry} {limbA : ℕ → ℕ → HX}

/-- **The named halving hypothesis on `s10L` rows** (see `Batch2903`'s FINDING): the chain level's
`v` is the exact half, `1 ≤ val v` and `2·val v + 1 < p`. -/
def HalvingOK (env : Env (ZMod p)) (st : StateX) : Prop :=
  st = .s10L → 1 ≤ (env.trace vX).val ∧ 2 * (env.trace vX).val + 1 < p

/-- **A `computeChipVCLHX` row decodes to `RowSemX`** — every state `0..16`, the
per-state clauses from the base gates and the served genuine records (`hOK`), the kid-kind clause from
the kid-kind gates. -/
theorem rowSemX_of_chip (hD : DenOKX p D) (hp : 17 < p) (hB : BaseHoldsX env) (st : StateX)
    (hOH : OneHotAt env (stIdx st)) (hOK : ∀ r ∈ activeX env, RecOK D R limbA r)
    (hv : HalvingOK env st) : RowSemX p D R (rowOfX env st) := by
  refine ⟨?_, kidKinds_of_gates hB st (oh_one hOH (stIdx_lt st))⟩
  cases st
  · exact sem_s0 hB hOK hp hOH
  · exact sem_s1 hB hOK hp hOH
  · exact sem_s2 hB hOK hp hOH
  · exact sem_s3 hB hOK hp hOH
  · exact sem_s4 hD hB hOK hp hOH
  · exact sem_s5 hB hOK hp hOH
  · exact sem_s6 hB hOK hp hOH
  · exact sem_s7 hB hOK hp hOH
  · exact sem_s8 hB hOK hp hOH
  · exact sem_s9 hB hOK hp hOH
  · exact sem_cons hB hOK hOH
  · exact sem_s10 hB hOK hp hOH
  · exact sem_s10L hB hOK hOH (hv rfl)
  · exact sem_s10T hB hOH
  · exact sem_s11s hD hB hOK hp hOH
  · exact sem_s11d hB hOK hp hOH
  · exact sem_s11j hB hOK hp hOH

end Main

end Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
