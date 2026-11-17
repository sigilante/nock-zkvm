/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluCallOK.lean

  **`CallOK` from the run.**

  Every primitive call of a generated run, read as a `CallL` by `AluHonestTable.callsLOf` (cell list and handle map of
  the J-9 AL honest data `j9alDataOf`), is a call the ALU serves honestly (`AluHonestRows.CallOK`):
  * `genX_s11j_eval`: a generated `s11j` node is a jet hit whose result IS the node's evaluation (the row's `e`);
  * the registry entry at a primitive id is `primSpec op` (`CompiledByP.2`), `op ≠ dec` (`hnoDec`), so the template
    is `binT op`: the subject is `[a b]` of two atoms and the result is the atom `primSem op a b` (`binT_rel`);
  * the handle kinds from `HdlOK` (`hdlOKL`), the subject serial `vS < p` from the cell table (`cells.length < p`,
    given by the J-9 A row binder `Rows31A` at `p = Nock.Atoms.p`);
  * `limbs62` from the NEW binder **`PrimLimbs62`** (`hlimb`): each primitive call's two operands have at most 62
    limbs.  Results and witnesses need no binder: a factor result (`div`'s quotient) and every W-B witness is
    `≤` an operand, and a non-factor big result is a one-row read (`mR`, no lane words).

  **Why `hlimb` is a binder and not derived.**  No hypothesis of `complJ9A_closed` bounds the size of an atom the
  run computes on: `ProgAxOK9A` caps only op-0 / op-10 axes (`AxCap`), `s11j` rows only need `id < p`, and
  `Rows31A` bounds table heights (`≤ 2^31` rows), not one atom's limb count.  A run calling `add` on two 63-limb
  atoms meets every J-9 A binder, and the ALU's Horner value slots carry at most 62 limbs (`CallOK.limbs62`), so the
  bound is a genuine restriction of the covered runs.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestTable
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluCallOK

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable (callsLOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.V1J8.Gen (idxOf hdN' tlN' atomV)
open Nock.Jet Nock.Jet.Autogen
open Nock.Jet.Prim (PrimOp primSem primSpec binT)

noncomputable section

/-! ## 1. Slot word counts -/

section Words

theorem limbs_len_mono {v w : ℕ} (h : v ≤ w) : (Nock.Atoms.limbs v).length ≤ (Nock.Atoms.limbs w).length :=
  Nat.le_length_digits_le _ _ _ h

theorem wordsOf_len (w : ℕ) : (wordsOf w).length ≤ max 1 (Nock.Atoms.limbs w).length := by
  unfold wordsOf
  split_ifs <;> simp

/-- A handle slot of value `v`: mode `1` has two words, mode `2` is a factor's view (`limbs v`), mode `0` has
no lane words; mode `3` never occurs. -/
theorem handleSlot_words (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    let sl := handleSlot p o lb r v k s
    (sl.mode = 1 → sl.words.length = 2) ∧ (sl.mode = 2 → isFactor o r = true ∧ sl.words = Nock.Atoms.limbs v) ∧
      sl.mode ≠ 3 := by
  intro sl
  simp only [sl, handleSlot]
  split_ifs with h1 h2 <;> simp [splitOf, *]

/-- A handle slot whose value has `≤ 62` limbs: every lane word list is `≤ 62` long. -/
theorem handleSlot_le62 (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) (hv : (Nock.Atoms.limbs v).length ≤ 62) :
    let sl := handleSlot p o lb r v k s
    (sl.mode = 1 ∨ sl.mode = 2 ∨ sl.mode = 3) → sl.words.length ≤ 62 := by
  intro sl hm
  obtain ⟨h1, h2, h3⟩ := handleSlot_words p o lb r v k s
  rcases hm with hm | hm | hm
  · rw [h1 hm]; norm_num
  · rw [(h2 hm).2]; exact hv
  · exact absurd hm h3

/-- A handle slot at a non-factor role: modes `1/2/3` have `≤ 62` words whatever the value. -/
theorem handleSlot_nf (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) (hf : isFactor o r = false) :
    let sl := handleSlot p o lb r v k s
    (sl.mode = 1 ∨ sl.mode = 2 ∨ sl.mode = 3) → sl.words.length ≤ 62 := by
  intro sl hm
  obtain ⟨h1, h2, h3⟩ := handleSlot_words p o lb r v k s
  rcases hm with hm | hm | hm
  · rw [h1 hm]; norm_num
  · rw [(h2 hm).1] at hf; cases hf
  · exact absurd hm h3

theorem witSlot_le62 (o : PrimOp) (lb r w : ℕ) (hw : (Nock.Atoms.limbs w).length ≤ 62) :
    (witSlot o lb r w).words.length ≤ 62 :=
  (wordsOf_len w).trans (max_le (by norm_num) hw)

theorem qSlot_mode (o : PrimOp) (b : Bool) (qs : List ℤ) :
    ¬ ((qSlot o b qs).mode = 1 ∨ (qSlot o b qs).mode = 2 ∨ (qSlot o b qs).mode = 3) := by
  unfold qSlot
  cases b <;> simp

/-- **`limbs62` from operand bounds**: if `a` and `b` have `≤ 62` limbs and the result is `primSem`, every Horner
value slot of the call has `≤ 62` words. -/
theorem limbs62_of (p : ℕ) (cl : CallL) (hsem : primSem cl.op cl.a cl.b = some cl.c)
    (hA : (Nock.Atoms.limbs cl.a).length ≤ 62) (hB : (Nock.Atoms.limbs cl.b).length ≤ 62) :
    ∀ s ∈ slotsOf p cl, (s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3) → s.words.length ≤ 62 := by
  have hle : ∀ w, w ≤ cl.a ∨ w ≤ cl.b → (Nock.Atoms.limbs w).length ≤ 62 := by
    intro w hw
    rcases hw with hw | hw
    · exact (limbs_len_mono hw).trans hA
    · exact (limbs_len_mono hw).trans hB
  intro s hs hm
  have hHA := handleSlot_le62 p cl.op cl.lbv 0 cl.a cl.kA cl.vA hA
  have hHB := handleSlot_le62 p cl.op cl.lbv 1 cl.b cl.kB cl.vB hB
  cases hop : cl.op
  all_goals rw [hop] at hHA hHB hsem
  all_goals simp only [slotsOf, hop, List.mem_cons, List.not_mem_nil, or_false] at hs
  case add =>
    rcases hs with rfl | rfl | rfl | rfl
    · exact hHA hm
    · exact hHB hm
    · exact handleSlot_nf p .add _ 2 _ _ _ rfl hm
    · exact absurd hm (qSlot_mode _ _ _)
  case sub =>
    rcases hs with rfl | rfl | rfl | rfl
    · exact hHA hm
    · exact hHB hm
    · exact handleSlot_nf p .sub _ 2 _ _ _ rfl hm
    · exact absurd hm (qSlot_mode _ _ _)
  case lt =>
    rcases hs with rfl | rfl | rfl | rfl
    · exact hHA hm
    · exact hHB hm
    · refine witSlot_le62 _ _ _ _ (hle _ ?_)
      unfold ltWit
      split_ifs
      · right; omega
      · left; omega
    · exact absurd hm (qSlot_mode _ _ _)
  case mul =>
    rcases hs with rfl | rfl | rfl | rfl
    · exact hHA hm
    · exact hHB hm
    · exact handleSlot_nf p .mul _ 2 _ _ _ rfl hm
    · exact absurd hm (qSlot_mode _ _ _)
  case div =>
    have hc : cl.c ≤ cl.a := by
      simp only [primSem] at hsem
      split_ifs at hsem
      rw [← Option.some.inj hsem]
      exact Nat.div_le_self _ _
    rcases hs with h | h | h | h | h | h | h <;> subst h
    · exact hHA hm
    · exact handleSlot_le62 p .div _ 4 _ _ _ (hle _ (Or.inl hc)) hm
    · exact hHB hm
    · exact witSlot_le62 _ _ _ _ (hle _ (Or.inl (Nat.mod_le _ _)))
    · exact witSlot_le62 _ _ _ _ (hle _ (Or.inr (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))))
    · exact absurd hm (qSlot_mode _ _ _)
    · exact absurd hm (qSlot_mode _ _ _)
  case mod =>
    rcases hs with h | h | h | h | h | h | h <;> subst h
    · exact hHA hm
    · exact witSlot_le62 _ _ _ _ (hle _ (Or.inl (Nat.div_le_self _ _)))
    · exact hHB hm
    · exact handleSlot_nf p .mod _ 5 _ _ _ rfl hm
    · exact witSlot_le62 _ _ _ _ (hle _ (Or.inr (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))))
    · exact absurd hm (qSlot_mode _ _ _)
    · exact absurd hm (qSlot_mode _ _ _)

end Words

/-! ## 2. A generated `s11j` node's result -/

section Gen

/-- **A generated `s11j` node is a jet hit with the node's own result**: the formula is `[11 [b clue] body]` and
`jetHit R b body s` is the evaluation `r`. -/
theorem genX_s11j_eval {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hst : t.label.state = .s11j) :
    ∃ b clue body, f = .cell (.atom 11) (.cell (.cell b clue) body) ∧ jetHit R b body s = some r := by
  rcases n with _ | n
  · simp [genComputeSkeletonX] at h
  unfold genComputeSkeletonX at h
  split at h
  all_goals (repeat' (split at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [mkX] at hst; done)
    | (exfalso; simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨_, _, _, rfl, by assumption⟩)

/-- **The run's view of one primitive call**: the `s11j` row of a generated tree whose id is a primitive id of a
registry carrying `primSpec` there, with `op ≠ dec`, has subject `[x y]` (atoms), result `primSem op x y`. -/
theorem prim_row {Rg : VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) {prims : List (ℕ × PrimOp)}
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) {row : RowNX} (hrow : row ∈ (rowsOfT t).toList)
    (hst : row.st = .s11j) (hid : atomV row.sf1 ∈ prims.map Prod.fst) :
    ∃ x y n, row.s = .cell (.atom x) (.atom y) ∧ row.e = .atom n ∧
      primSem (opOf prims (atomV row.sf1)) x y = some n ∧ opOf prims (atomV row.sf1) ≠ .dec := by
  have hrow' : ∃ u ∈ bfsForest [t], rowOfSkelX u.label = row := by
    simpa [rowsOfT] using hrow
  obtain ⟨u, hu, rfl⟩ := hrow'
  obtain ⟨c, hc, huc⟩ := (mem_bfsForest [t] u).1 hu
  have hct : c = t := by simpa using hc
  subst hct
  have hstu : u.label.state = .s11j := by rw [← ComplJ8Jet.rowOfSkelX_st]; exact hst
  rcases genX_inTree hgen huc with ⟨m, hm⟩ | hch
  · obtain ⟨b, clue, body, hf, hj⟩ := genX_s11j_eval hm hstu
    obtain ⟨id, j, rfl, hRj, -, hrel⟩ := jetHit_spec hj
    have hftth : (rowOfSkelX u.label).ftth = .atom id := by
      unfold rowOfSkelX
      rw [hstu]
      simp only [hf, tlN, hdN]
    rw [hftth] at hid ⊢
    obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hid
    simp only [atomV] at hq1 ⊢
    subst hq1
    have hop : opOf prims q.1 = q.2 := opOf_of_mem hnd hq
    rw [hprim q hq] at hRj
    have hj' : j = primSpec q.2 := (Option.some.inj hRj).symm
    subst hj'
    have hd := hnoDec q hq
    have hT : (primSpec q.2).T = binT q.2 := by
      rcases hq2 : q.2 with _ | _ | _ | _ | _ | _ | _
      all_goals first | rfl | exact absurd hq2 hd
    rw [hT] at hrel
    obtain ⟨x, y, n, hs, hn, he⟩ := Nock.Jet.Prim.binT_rel hrel
    refine ⟨x, y, n, ?_, ?_, ?_, ?_⟩
    · rw [ComplJ8Jet.rowOfSkelX_s]; exact hs
    · rw [ComplJ9ABase.rowOfSkelX_e]; exact he
    · rw [hop]; exact hn
    · rw [hop]; exact hd
  · have := chainNode_isChain hch
    rw [hstu] at this
    exact absurd this (by decide)

end Gen

/-! ## 3. `CallOK` at every primitive call of the run -/

section Run
variable {p : ℕ} [Fact p.Prime] {Rg : VerifiedRegistry} (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **NEW disclosed binder `hlimb`** (route F′, stage 4).  Every primitive call of the run has operands of at most
62 limbs: for each `(id, [a b], c)` of `pcallsR`, `(limbs a).length ≤ 62` and `(limbs b).length ≤ 62`.

It RESTRICTS the covered runs to those whose primitive calls have operands of `≤ 62` limbs of `2^32` (the ALU's
Horner value slots carry at most 62 limbs, `CallOK.limbs62`).  It is not implied by the J-9 A binders (module
docstring).  Results need no bound (a factor result is `≤` an operand; a non-factor big result is a one-row read). -/
def PrimLimbs62 (pids : List ℕ) (t : NTree SkelX) : Prop :=
  ∀ x ∈ pcallsR pids (rowsOfT t),
    (Nock.Atoms.limbs (atomV (hdN' x.2.1))).length ≤ 62 ∧ (Nock.Atoms.limbs (atomV (tlN' x.2.1))).length ≤ 62

theorem ringChar_eq : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p

/-- **`CallOK` at every primitive call of the run** (the cell list and handle map of `j9alDataOf`). -/
theorem callOK_run (hp32 : Bn < p) (hcs : (j9alDataOf p Rg Rt prims hgen).cells.length < p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hlimb : PrimLimbs62 (prims.map Prod.fst) t) :
    ∀ cl ∈ callsLOf (j9alDataOf p Rg Rt prims hgen).cells (j9alDataOf p Rg Rt prims hgen).H prims
        (pcallsR (prims.map Prod.fst) (rowsOfT t)), CallOK p cl := by
  intro cl hcl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcl
  have hx0 := hx
  unfold pcallsR at hx
  obtain ⟨row, hrow, hrx⟩ := List.mem_filterMap.mp hx
  by_cases hc : row.st = .s11j ∧ atomV row.sf1 ∈ prims.map Prod.fst
  · rw [if_pos hc] at hrx
    have hxe : x = (atomV row.sf1, row.s, row.e) := (Option.some.inj hrx).symm
    obtain ⟨a, b, n, hs, he, hsem, hd⟩ := prim_row hgen hnd hprim hnoDec hrow hc.1 hc.2
    obtain ⟨hlA, hlB⟩ := hlimb x hx0
    subst hxe
    have hH := hdlOKL (p := p) Rt prims hgen
    rw [ringChar_eq] at hH
    simp only [hs, hdN', tlN', atomV] at hlA hlB
    have hkind : ∀ v, (v < p → ((j9alDataOf p Rg Rt prims hgen).H (.atom v)).1 = 0 ∧
        ((j9alDataOf p Rg Rt prims hgen).H (.atom v)).2 = v) ∧
        (p ≤ v → ((j9alDataOf p Rg Rt prims hgen).H (.atom v)).1 = 2) := by
      intro v
      refine ⟨fun hv => ?_, fun hv => hH.big v hv⟩
      rw [hH.small v hv]; exact ⟨rfl, rfl⟩
    have hmem : row.s ∈ (j9alDataOf p Rg Rt prims hgen).cells := by
      have hrowD : row ∈ (j9alDataOf p Rg Rt prims hgen).rows.toList := hrow
      rcases handle_noun_casesL (p := p) Rt prims hgen hrowD (n := row.s) (by simp [handleNounsX]) with
        ⟨-, hm⟩ | ⟨v, hv, -⟩ | ⟨v, hv, -⟩
      · exact hm
      · rw [hs] at hv; cases hv
      · rw [hs] at hv; cases hv
    rw [hs] at hmem
    rw [hs, he]
    refine
      { notDec := hd
        sem := hsem
        hp := hp32
        kAok := hkind a
        kBok := hkind b
        kEok := fun _ => hkind n
        kElt := fun hlt => ?_
        vSok := ?_
        limbs62 := limbs62_of p _ hsem hlA hlB }
    · have hn1 : n < p := by
        have hlt' : opOf prims (atomV row.sf1) = .lt := hlt
        rw [hlt'] at hsem
        simp only [primSem, Option.some.injEq] at hsem
        have : n ≤ 1 := by rw [← hsem]; split_ifs <;> norm_num
        have : 2 ≤ p := (Fact.out : p.Prime).two_le
        omega
      exact hkind n |>.1 hn1
    · exact lt_trans (ComplJ8Data.idxOf_lt _ _ hmem) hcs
  · rw [if_neg hc] at hrx
    cases hrx

/-- **The cell table fits the field** under the J-9 A row binder at the Goldilocks prime. -/
theorem cells_lt_p (hpG : p = Nock.Atoms.p) (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen)) :
    (j9alDataOf p Rg Rt prims hgen).cells.length < p := by
  have h1 : (j9alDataOf p Rg Rt prims hgen).cells.length ≤ 2 ^ 31 :=
    h31 _ (by simp [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8])
  have h2 : 2 ^ 63 < p := ComplJ9AChains.hp63_of_G hpG
  omega

/-- **`CallOK` at every primitive call of the run**, at the Goldilocks prime under `Rows31A`. -/
theorem callOK_run_G (hpG : p = Nock.Atoms.p) (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hlimb : PrimLimbs62 (prims.map Prod.fst) t) :
    ∀ cl ∈ callsLOf (j9alDataOf p Rg Rt prims hgen).cells (j9alDataOf p Rg Rt prims hgen).H prims
        (pcallsR (prims.map Prod.fst) (rowsOfT t)), CallOK p cl :=
  callOK_run Rt prims hgen (by have := ComplJ9AChains.hp63_of_G hpG; simp only [Bn]; omega)
    (cells_lt_p Rt prims hgen hpG h31) hnd hprim hnoDec hlimb

/-- **`hblk` in per-call form** at the run's calls: the block obligations `∀ cl, CallOK p cl → …` give the
per-call satisfaction `aluSZChipJ9_honest_sat_preg` takes. -/
theorem hblk_run {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))]
    (hblk : ∀ cl, CallOK p cl → BlockBaseSat (F := F) p cl ∧ BlockIdentSat (K := K) δ p cl)
    (hok : ∀ cl ∈ callsLOf (j9alDataOf p Rg Rt prims hgen).cells (j9alDataOf p Rg Rt prims hgen).H prims
        (pcallsR (prims.map Prod.fst) (rowsOfT t)), CallOK p cl) :
    ∀ cl ∈ callsLOf (j9alDataOf p Rg Rt prims hgen).cells (j9alDataOf p Rg Rt prims hgen).H prims
        (pcallsR (prims.map Prod.fst) (rowsOfT t)),
      BlockBaseSat (F := F) p cl ∧ BlockIdentSat (K := K) δ p cl :=
  fun cl hcl => hblk cl (hok cl hcl)

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluCallOK
