/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8BigBound.lean

  **The big-atom bound and the single `p` row.**

  * **§1–§4 the run bound** (`gen_bnd`): along a generated run (`genX`) every handle noun of every row, and the
    result, has all leaves `< M + |t|` when the subject and formula have leaves `< M` (`M ≥ p`): the only source
    of a new atom above the inputs is an op-4 increment (one per row); op 3 / op 5 give `0 / 1`, op 0 / 9 / 10 and
    the edit chain return sub-nouns, a jet hit (`HregC`) evaluates a well-typed template (`Autogen.ev`: `add` /
    `mul` are `% p`, `nth` / `pair` rebuild sub-nouns), and op 5's first-difference axis is `< p` (`hop5`).
  * **§5 the J nouns**: every row of a call's honest table (`honestRows`) is bounded by its subject's bound; each
    registered compiled formula is the body (`ftt`) of an `s11j` row of the run.
  * **§6 `bigs_lt`**: at `j8DataOf p Rg Rt hgen`, every big atom `a ∈ D.bigs` satisfies `a < p + D.rows.size`
    (binders: `hclA` at the subject and formula, `hRt` = L4's `HregC` at the witness `Rt`, `hop5`).
  * **§7 the single `p` row** (Goldilocks, rows `≤ 2^31`): every big atom has the limbs `[1 + k, B − 1]`
    (`k < 2^31`), so `[0 combPP] ∉ spineL bigs`, the `p` duplicate is off, `D.acs` is duplicate-free, and
    `lastIdxOf D.acs combPP = idxOf D.acs combPP`; `rIAP p D.acs = idxN D.acs`; `rootIdxP` is the first index.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound

open Nock Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL (hdN tlN)
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgOp5OK Op5RowX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

/-! ## 1. Bounded nouns -/

/-- Every leaf of the noun is `< M`. -/
def Bnd (M : ℕ) : Noun → Prop
  | .atom a => a < M
  | .cell x y => Bnd M x ∧ Bnd M y

@[simp] theorem bnd_atom (M a : ℕ) : Bnd M (.atom a) ↔ a < M := Iff.rfl
@[simp] theorem bnd_cell (M : ℕ) (x y : Noun) : Bnd M (.cell x y) ↔ Bnd M x ∧ Bnd M y := Iff.rfl

theorem bnd_mono {M M' : ℕ} (h : M ≤ M') : ∀ {n : Noun}, Bnd M n → Bnd M' n
  | .atom a, hn => by simp at hn ⊢; omega
  | .cell x y, hn => ⟨bnd_mono h hn.1, bnd_mono h hn.2⟩

theorem bnd_mono' {M M' : ℕ} {n : Noun} (hn : Bnd M n) (h : M ≤ M') : Bnd M' n := bnd_mono h hn

theorem bnd_hdN {M : ℕ} : ∀ {n : Noun}, Bnd M n → Bnd M (hdN n)
  | .atom _, h => h
  | .cell _ _, h => h.1

theorem bnd_tlN {M : ℕ} : ∀ {n : Noun}, Bnd M n → Bnd M (tlN n)
  | .atom _, h => h
  | .cell _ _, h => h.2

theorem bnd_slot {M : ℕ} (ax : ℕ) (n : Noun) : ∀ {m : Noun}, Noun.slot ax n = some m → Bnd M n → Bnd M m := by
  induction ax, n using Nock.Noun.slot.induct with
  | case1 x => intro m h; simp [Noun.slot] at h
  | case2 n =>
      intro m h hn
      simp only [Noun.slot] at h
      obtain rfl := Option.some.inj h
      exact hn
  | case3 a n l r hrec ih =>
      intro m h hn
      have hlr := ih hrec hn
      simp only [Noun.slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h; exact hlr.1
      · obtain rfl := Option.some.inj h; exact hlr.2
  | case4 a n hno _ =>
      intro m h
      simp only [Noun.slot] at h
      cases hs : Noun.slot ((a + 2) / 2) n with
      | none => simp [hs] at h
      | some w =>
        cases w with
        | atom k => simp [hs] at h
        | cell l r => exact (hno l r hs).elim

theorem bnd_edit {M : ℕ} (ax : ℕ) :
    ∀ (new old : Noun) {e : Noun}, Noun.edit ax new old = some e → Bnd M new → Bnd M old → Bnd M e := by
  induction ax using Nat.strong_induction_on with
  | _ ax ih =>
    intro new old e h hn ho
    match ax, ih, h with
    | 0, _, h => simp [Noun.edit] at h
    | 1, _, h => simp only [Noun.edit, Option.some.injEq] at h; subst h; exact hn
    | a + 2, ih, h =>
      rw [Noun.edit] at h
      split at h
      · rename_i sib hs
        refine ih ((a + 2) / 2) (by omega) _ old h ?_ ho
        have hsb := bnd_slot _ _ hs ho
        split <;> exact ⟨by assumption, by assumption⟩
      · simp at h

theorem bnd_fd : ∀ {M : ℕ} (a b : Noun), Bnd M a → Bnd M b → Bnd M (fdN a b).2.1 ∧ Bnd M (fdN a b).2.2
  | _, .cell a1 a2, .cell b1 b2, ha, hb => by
    simp only [fdN]
    split_ifs
    · exact bnd_fd a2 b2 ha.2 hb.2
    · exact bnd_fd a1 b1 ha.1 hb.1
  | _, .atom _, .atom _, ha, hb => by simp only [fdN]; exact ⟨ha, hb⟩
  | _, .atom _, .cell _ _, ha, hb => by simp only [fdN]; exact ⟨ha, hb⟩
  | _, .cell _ _, .atom _, ha, hb => by simp only [fdN]; exact ⟨ha, hb⟩

theorem bnd_fd1 {M : ℕ} {a b : Noun} (ha : Bnd M a) (hb : Bnd M b) : Bnd M (fdN a b).2.1 := (bnd_fd a b ha hb).1
theorem bnd_fd2 {M : ℕ} {a b : Noun} (ha : Bnd M a) (hb : Bnd M b) : Bnd M (fdN a b).2.2 := (bnd_fd a b ha hb).2

theorem bnd_wut {M : ℕ} (hM : 2 ≤ M) (n : Noun) : Bnd M (Noun.wut n) := by
  cases n <;> simp [Noun.wut] <;> omega

theorem bnd_tis {M : ℕ} (hM : 2 ≤ M) (a b : Noun) : Bnd M (Noun.tis a b) := by
  unfold Noun.tis; split_ifs <;> simp <;> omega

theorem bnd_leavesOf {M : ℕ} : ∀ {n : Noun}, Bnd M n → ∀ a ∈ leavesOf n, a < M
  | .atom b, h, a, ha => by simp [leavesOf] at ha; subst ha; exact h
  | .cell x y, h, a, ha => by
    simp only [leavesOf, List.mem_append] at ha
    rcases ha with ha | ha
    · exact bnd_leavesOf h.1 a ha
    · exact bnd_leavesOf h.2 a ha

theorem bnd_of_leafList {M : ℕ} : ∀ {n : Noun}, (∀ v ∈ n.leafList, v < M) → Bnd M n
  | .atom b, h => by simpa [Noun.leafList] using h
  | .cell x y, h => by
    simp only [Noun.leafList, List.mem_append] at h
    exact ⟨bnd_of_leafList fun v hv => h v (Or.inl hv), bnd_of_leafList fun v hv => h v (Or.inr hv)⟩

/-! ## 2. The edit chain -/

theorem xor_one_le (a : ℕ) : a ^^^ 1 ≤ a + 1 := by
  rw [xor_one_eq]; split_ifs <;> omega

theorem inTree_mkX {st : StateX} {s f e : Noun} {ks : List (NTree SkelX)} {u : NTree SkelX}
    (hu : InTree (mkX st s f e ks) u) : u = mkX st s f e ks ∨ ∃ k ∈ ks, InTree k u := by
  cases hu with
  | here => exact Or.inl rfl
  | sub hs h => exact Or.inr ⟨_, by simpa using hs, h⟩

/-- **Every row of an edit chain** has handles bounded by `K + 1` when `old`, `e` and the chain axis are `< K`;
it is not a jet row. -/
theorem chain_bnd {K : ℕ} (hK : 0 < K) {old e : Noun} (ho : Bnd K old) (he : Bnd K e) :
    ∀ (k a : ℕ), a < K → ∀ u, InTree (genChainF old e k a) u →
      (∀ x ∈ rowHandleNounsX (rowOfSkelX u.label), Bnd (K + 1) x) ∧ (rowOfSkelX u.label).st ≠ .s11j := by
  have hsib : ∀ (b : ℕ) (n : Noun), Bnd K n → Bnd (K + 1) (sibX b n) := by
    intro b n hn
    unfold sibX
    cases hs : Noun.slot (b ^^^ 1) n with
    | none => simp
    | some m => exact bnd_mono (Nat.le_succ K) (bnd_slot _ _ hs hn)
  have hrow : ∀ (st : StateX) (a : ℕ) (ks : List RowX), a < K → (st = .s10L ∨ st = .s10T) →
      (∀ x ∈ rowHandleNounsX (rowOfSkelX ⟨st, old, .atom a, e, ks⟩), Bnd (K + 1) x) ∧
        (rowOfSkelX ⟨st, old, .atom a, e, ks⟩).st ≠ .s11j := by
    intro st a ks ha hst
    refine ⟨fun x hx => ?_, by rcases hst with rfl | rfl <;> simp [rowOfSkelX]⟩
    rcases hst with rfl | rfl
    · simp only [rowOfSkelX, rowHandleNounsX, chainAxis, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact bnd_mono (Nat.le_succ K) ho
        | exact bnd_mono (Nat.le_succ K) he
        | exact hsib _ _ ho
        | exact hsib _ _ he
        | (simp only [bnd_atom]; have := xor_one_le a; omega)
        | (simp only [bnd_atom]; omega)
    · simp only [rowOfSkelX, rowHandleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact bnd_mono (Nat.le_succ K) ho
        | exact bnd_mono (Nat.le_succ K) he
        | (simp only [bnd_atom]; omega)
  intro k
  induction k with
  | zero =>
    intro a ha u hu
    simp only [genChainF] at hu
    rcases inTree_mkX hu with rfl | ⟨k, hk, -⟩
    · exact hrow .s10T a _ ha (Or.inr rfl)
    · simp at hk
  | succ k ih =>
    intro a ha u hu
    simp only [genChainF] at hu
    split_ifs at hu with h2
    · rcases inTree_mkX hu with rfl | ⟨c, hc, hcu⟩
      · exact hrow .s10L a _ ha (Or.inl rfl)
      · simp only [List.mem_singleton] at hc; subst hc
        exact ih (a / 2) (by omega) u hcu
    · rcases inTree_mkX hu with rfl | ⟨k, hk, -⟩
      · exact hrow .s10T a _ ha (Or.inr rfl)
      · simp at hk

/-! ## 3. Jet templates -/

section Jet
open Nock.Jet.Autogen (Ex Ty HasTy Tpl ev nhd ntl ntail compile)
open Nock.Jet.Interp (honestRows exRows inRows gRows gElemsR argsD JRow z0)

/-- Every constant of an expression is `< p`. -/
def CL (p : ℕ) {k : ℕ} : Ex k → Prop
  | .var _ => True
  | .const c => c < p
  | .add a b => CL p a ∧ CL p b
  | .mul a b => CL p a ∧ CL p b
  | .nth _ e => CL p e
  | .pair a b => CL p a ∧ CL p b

theorem cl_of_hasTy {p k : ℕ} (hp : 0 < p) {inTy : Fin k → Ty} {e : Ex k} {τ : Ty}
    (h : HasTy p inTy e τ) : CL p e := by
  induction h with
  | var i => trivial
  | const hc => exact hc
  | nil τ => exact hp
  | weakN _ ih => exact ih
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | nth _ _ ih => exact ih
  | pair _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

theorem bnd_nhd {K : ℕ} (hK : 0 < K) : ∀ {n : Noun}, Bnd K n → Bnd K (nhd n)
  | .atom _, _ => by simp [nhd]; exact hK
  | .cell _ _, h => h.1

theorem bnd_ntl {K : ℕ} (hK : 0 < K) : ∀ {n : Noun}, Bnd K n → Bnd K (ntl n)
  | .atom _, _ => by simp [ntl]; exact hK
  | .cell _ _, h => h.2

theorem bnd_ntail {K : ℕ} (hK : 0 < K) : ∀ (j : ℕ) {n : Noun}, Bnd K n → Bnd K (ntail j n)
  | 0, _, h => h
  | j + 1, _, h => bnd_ntl hK (bnd_ntail hK j h)

theorem bnd_ev {p K k : ℕ} (hp : 0 < p) (hK : p ≤ K) {a : Fin k → Noun} (ha : ∀ i, Bnd K (a i)) :
    ∀ e : Ex k, CL p e → Bnd K (ev p a e)
  | .var i, _ => ha i
  | .const c, hc => by simp only [ev, bnd_atom]; exact lt_of_lt_of_le hc hK
  | .add _ _, _ => by simp only [ev, bnd_atom]; exact lt_of_lt_of_le (Nat.mod_lt _ hp) hK
  | .mul _ _, _ => by simp only [ev, bnd_atom]; exact lt_of_lt_of_le (Nat.mod_lt _ hp) hK
  | .nth j e, hc => bnd_nhd (by omega) (bnd_ntail (by omega) j (bnd_ev hp hK ha e hc))
  | .pair e1 e2, hc => ⟨bnd_ev hp hK ha e1 hc.1, bnd_ev hp hK ha e2 hc.2⟩

/-- **A well-typed template's semantics** stays below the subject's bound (`K ≥ p`). -/
theorem bnd_semS {p K : ℕ} (hp : 0 < p) (hK : p ≤ K) (T : Tpl) (hT : T.WellTyped p) {s r : Noun}
    (h : (T.toTemplate p).semS s = some r) (hs : Bnd K s) : Bnd K r := by
  unfold Template.semS at h
  cases ha : (T.toTemplate p).args s with
  | none => simp [ha] at h
  | some a =>
    rw [ha, Option.bind_some] at h
    have hsl := Template.args_eq_some.1 ha
    simp only [Autogen.Tpl.toTemplate] at h
    split_ifs at h
    obtain rfl := Option.some.inj h
    exact bnd_ev hp hK (fun i => bnd_slot _ _ (hsl i) hs) _ (cl_of_hasTy hp hT)

theorem bnd_exRows {p K k : ℕ} (hp : 0 < p) (hK : p ≤ K) (ax : Fin k → ℕ) {a : Fin k → Noun}
    (ha : ∀ i, Bnd K (a i)) (c : ℕ) : ∀ (e : Ex k) (b : ℕ), CL p e → ∀ x ∈ exRows p ax a c b e, Bnd K x.val
  | .var i, b, _, x, hx => by simp [exRows] at hx; subst hx; exact ha i
  | .const n, b, hc, x, hx => by
    simp [exRows] at hx; subst hx; simp only [bnd_atom]; exact lt_of_lt_of_le hc hK
  | .add e1 e2, b, hc, x, hx => by
    simp only [exRows, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact bnd_ev hp hK ha _ hc
    · exact bnd_exRows hp hK ax ha c e1 _ hc.1 x hx
    · exact bnd_exRows hp hK ax ha c e2 _ hc.2 x hx
  | .mul e1 e2, b, hc, x, hx => by
    simp only [exRows, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact bnd_ev hp hK ha _ hc
    · exact bnd_exRows hp hK ax ha c e1 _ hc.1 x hx
    · exact bnd_exRows hp hK ax ha c e2 _ hc.2 x hx
  | .pair e1 e2, b, hc, x, hx => by
    simp only [exRows, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact bnd_ev hp hK ha _ hc
    · exact bnd_exRows hp hK ax ha c e1 _ hc.1 x hx
    · exact bnd_exRows hp hK ax ha c e2 _ hc.2 x hx
  | .nth j e, b, hc, x, hx => by
    simp only [exRows, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact bnd_ev hp hK ha (.nth j e) hc
    · exact bnd_exRows hp hK ax ha c e _ hc x hx

theorem bnd_gElemsR {K : ℕ} (hK : 0 < K) (g : ℕ → ℕ → Noun → List JRow)
    (hg : ∀ b r v, Bnd K v → ∀ x ∈ g b r v, Bnd K x.val) (sz r : ℕ) {v : Noun} (hv : Bnd K v) (c : ℕ) :
    ∀ (js : List ℕ) (b : ℕ), ∀ x ∈ gElemsR g sz r v c b js, Bnd K x.val
  | [], b, x, hx => by simp [gElemsR] at hx
  | j :: js, b, x, hx => by
    simp only [gElemsR, List.mem_cons, List.mem_append] at hx
    have hj : Bnd K (nhd (ntail j v)) := bnd_nhd hK (bnd_ntail hK j hv)
    rcases hx with rfl | hx | hx
    · exact hj
    · exact hg _ _ _ hj x hx
    · exact bnd_gElemsR hK g hg sz r hv c js _ x hx

theorem bnd_gRows {K : ℕ} (hK : 0 < K) (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun), Bnd K v →
    ∀ x ∈ gRows c τ b r v, Bnd K x.val
  | .F, b, r, v, hv, x, hx => by simp [gRows] at hx; subst hx; exact hv
  | .N, b, r, v, hv, x, hx => by simp [gRows] at hx
  | .L n τ, b, r, v, hv, x, hx => by
    simp only [gRows, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact bnd_ntail hK n hv
    · exact bnd_ntail hK n hv
    · exact bnd_gElemsR hK _ (fun b r v hv => bnd_gRows hK c τ b r v hv) _ r hv c _ _ x hx

theorem bnd_inRows {K : ℕ} (hK : 0 < K) (T : Tpl) {a : Fin T.k → Noun} (ha : ∀ i, Bnd K (a i)) (c : ℕ) :
    ∀ (is : List (Fin T.k)) (b : ℕ), ∀ x ∈ inRows T a c b is, Bnd K x.val
  | [], b, x, hx => by simp [inRows] at hx
  | i :: is, b, x, hx => by
    simp only [inRows, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact ha i
    · exact bnd_gRows hK c _ _ _ _ (ha i) x hx
    · exact bnd_inRows hK T ha c is _ x hx

/-- **Every honest J row of a call** (`honestRows`) is bounded by the call subject's bound (`K ≥ p`). -/
theorem bnd_honestRows {p K : ℕ} (hp : 0 < p) (hK : p ≤ K) (T : Tpl) (hT : T.WellTyped p) {s : Noun}
    (hs : Bnd K s) (c : ℕ) : ∀ x ∈ honestRows p T s c, Bnd K x.val := by
  have ha : ∀ i, Bnd K (argsD T s i) := by
    intro i
    unfold argsD
    cases h : Noun.slot (T.ax i) s with
    | none => simp [z0]; omega
    | some m => exact bnd_slot _ _ h hs
  intro x hx
  simp only [honestRows, List.mem_append] at hx
  rcases hx with hx | hx
  · exact bnd_exRows hp hK _ ha c _ _ (cl_of_hasTy hp hT) x hx
  · exact bnd_inRows (by omega) T ha c _ _ x hx

end Jet

/-! ## 4. The run bound -/

section Run
open Nock.Jet.Autogen (Tpl compile)

/-- **Binder `hRt` in run form**: every called id is a compiled, well-typed template. -/
def JetB (p : ℕ) (R : Registry) (t : NTree SkelX) : Prop :=
  ∀ id ∈ CalledIds t, ∃ T : Tpl, R id = some ⟨T.toTemplate p, compile p T⟩ ∧ T.WellTyped p

/-- **A row is bounded by `K`**: its twelve handles are, and a jet row names its registered entry (the clue's
value `sf1` is the atom id, entry formula = the hinted body `ftt`). -/
def NodeOK (R : Registry) (K : ℕ) (u : NTree SkelX) : Prop :=
  (∀ x ∈ rowHandleNounsX (rowOfSkelX u.label), Bnd K x) ∧
    ((rowOfSkelX u.label).st = .s11j → ∃ id j, (rowOfSkelX u.label).sf1 = .atom id ∧ R id = some j ∧
      j.c = (rowOfSkelX u.label).ftt)

theorem nodeOK_mono {R : Registry} {K K' : ℕ} (hK : K ≤ K') {u : NTree SkelX} (h : NodeOK R K u) :
    NodeOK R K' u := ⟨fun x hx => bnd_mono hK (h.1 x hx), h.2⟩

theorem jetB_child {p : ℕ} {R : Registry} {t k : NTree SkelX} (h : JetB p R t) (hk : k ∈ t.children) :
    JetB p R k := fun id ⟨u, hu, h1, h2⟩ => h id ⟨u, InTree.sub hk hu, h1, h2⟩

theorem op5_child {p : ℕ} {t k : NTree SkelX} (h : ProgOp5OK p t) (hk : k ∈ t.children) : ProgOp5OK p k :=
  fun u hu => h u (InTree.sub hk hu)

theorem size_mkX (st : StateX) (s f e : Noun) (ks : List (NTree SkelX)) :
    (mkX st s f e ks).size = 1 + (ks.map NTree.size).sum := by
  simp [mkX, NTree.size]

theorem nodes_mkX {R : Registry} {K : ℕ} {st : StateX} {s f e : Noun} {ks : List (NTree SkelX)}
    (hroot : NodeOK R K (mkX st s f e ks)) (hk : ∀ k ∈ ks, ∀ u, InTree k u → NodeOK R K u) :
    ∀ u, InTree (mkX st s f e ks) u → NodeOK R K u := by
  intro u hu
  rcases inTree_mkX hu with rfl | ⟨k, hk', hu'⟩
  · exact hroot
  · exact hk k hk' u hu'

/-- A bounded noun up to a larger bound. -/
macro "bnd_up" : tactic => `(tactic| (apply bnd_mono' <;> first | assumption | omega))

/-- One handle goal. -/
macro "bnd_tac" : tactic => `(tactic| first
  | (simp only [bnd_atom]; omega)
  | bnd_up
  | (apply bnd_hdN; bnd_up)
  | (apply bnd_tlN; bnd_up)
  | (simp only [bnd_cell]; exact ⟨by bnd_up, by bnd_up⟩)
  | exact bnd_wut (by omega) _
  | exact bnd_tis (by omega) _ _
  | (apply bnd_fd1 <;> bnd_up)
  | (apply bnd_fd2 <;> bnd_up)
  | (intro _ hx; simp at hx))

/-- The root row's handles. -/
macro "root_tac" : tactic => `(tactic| (
  simp only [mkX_label, rowOfSkelX, rowHandleNounsX, kidE, kidF, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some, SkelX.row,
    hdN, tlN, List.forall_mem_cons, List.forall_mem_nil, and_true, *] <;>
  (repeat' apply And.intro) <;> bnd_tac))

set_option maxHeartbeats 1600000 in
theorem gen_bnd {p : ℕ} (hp : 2 ≤ p) {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    ∀ M, p ≤ M → JetB p R t → ProgOp5OK p t → Bnd M s → Bnd M f →
      Bnd (M + t.size) r ∧ ∀ u, InTree t u → NodeOK R (M + t.size) u := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨⟨hb, hc⟩, hd'⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hbc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs ⟨hb, hc⟩
    obtain ⟨hr2, hn2⟩ := ih2 hd M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs hd'
    have e1 := (genX_label hbc).2.2.1; have e2 := (genX_label hd).2.2.1
    have hsz := size_mkX .cons s (.cell (.cell b c) d) (.cell l r') [tl, tr]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨⟨bnd_mono' hr1 (by omega), bnd_mono' hr2 (by omega)⟩, nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hsub hf
    simp only [bnd_cell, bnd_atom] at hf
    have hr := bnd_slot _ _ hs hsub
    have hsz := size_mkX .s0 s (.cell (.atom 0) (.atom ax)) r' []
    simp only [List.map_nil, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk; simp at hk
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hsub hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hu⟩ := hf
    have hsz := size_mkX .s1 s (.cell (.atom 1) u) u []
    simp only [List.map_nil, List.sum_nil] at hsz
    refine ⟨bnd_mono' hu (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk; simp at hk
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr3, hn3⟩ := ih3 hm (M + tl.size + tr.size) (by omega) (jetB_child hJ (by simp))
      (op5_child h5 (by simp)) (by bnd_up) (by bnd_up)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hc).2.2.1
    have hsz := size_mkX .s2 s (.cell (.atom 2) (.cell b c)) r2 [tl, tr, t2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr3 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · exact nodeOK_mono (by omega) (hn3 u hu)
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfu⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih hx M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs hfu
    have e1 := (genX_label hx).2.2.1
    have hsz := size_mkX .s3 s (.cell (.atom 3) u) (Noun.wut v) [t2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_wut (by omega) _, nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      exact nodeOK_mono (by omega) (hn1 u hu)
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfu⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih hx M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs hfu
    simp only [bnd_atom] at hr1
    have e1 := (genX_label hx).2.2.1
    have hsz := size_mkX .s4 s (.cell (.atom 4) u) (.atom (v + 1)) [t0]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨by simp only [bnd_atom]; omega, nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      exact nodeOK_mono (by omega) (hn1 u hu)
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hc).2.2.1
    have hax := h5 _ (InTree.here _) rfl
    simp only [mkX_label, rowOfSkelX, kidE, List.map_cons, List.map_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.getD_some, SkelX.row, e1, e2] at hax
    have hsz := size_mkX .s5 s (.cell (.atom 5) (.cell b c)) (Noun.tis l r1) [tl, tr]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_tis (by omega) _ _, nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc, hfd⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hc).2.2.1
    have hsz := size_mkX .s6 s (.cell (.atom 6) (.cell b (.cell c d))) r1 [t2, tC]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · exact nodeOK_mono (by omega) (hn1 u hu)
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc, hfd⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hc).2.2.1
    have hsz := size_mkX .s6 s (.cell (.atom 6) (.cell b (.cell c d))) r1 [t2, tC]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · exact nodeOK_mono (by omega) (hn1 u hu)
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hm (M + t1.size) (by omega) (jetB_child hJ (by simp)) (op5_child h5 (by simp))
      hr1 (by bnd_up)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hm).2.2.1
    have hsz := size_mkX .s7 s (.cell (.atom 7) (.cell b c)) r2 [t2, t1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · exact nodeOK_mono (by omega) (hn1 u hu)
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hb M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hm (M + t1.size) (by omega) (jetB_child hJ (by simp)) (op5_child h5 (by simp))
      ⟨hr1, bnd_mono' hs (by omega)⟩ (by bnd_up)
    have e1 := (genX_label hb).2.2.1; have e2 := (genX_label hm).2.2.1
    have hsz := size_mkX .s8 s (.cell (.atom 8) (.cell b c)) r2 [t2, t1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · exact nodeOK_mono (by omega) (hn1 u hu)
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfa, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have harmB := bnd_slot _ _ harm hr1
    obtain ⟨hr2, hn2⟩ := ih2 hm (M + t1.size) (by omega) (jetB_child hJ (by simp)) (op5_child h5 (by simp))
      hr1 harmB
    have e1 := (genX_label hc).2.2.1; have e2 := (genX_label hm).2.2.1; have e3 := (genX_label hm).2.1
    have hsz := size_mkX .s9 s (.cell (.atom 9) (.cell (.atom ax) c)) r2 [t1, t2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, ⟨hfa, hfc⟩, hfd⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hc M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hd M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have hE : Bnd (M + tl.size + tr.size) e :=
      bnd_edit ax new old he (bnd_mono' hr1 (by omega)) (bnd_mono' hr2 (by omega))
    have hch := chain_bnd (K := M + tl.size + tr.size) (by omega) (bnd_mono' hr2 (by omega)) hE ax ax (by omega)
    have e1 := (genX_label hc).2.2.1; have e2 := (genX_label hd).2.2.1
    have hsz := size_mkX .s10 s (.cell (.atom 10) (.cell (.cell (.atom ax) c) d)) e [tl, tr, genChain old e ax]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hE (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
      · obtain ⟨h1, h2⟩ := hch u hu
        exact ⟨fun x hx => bnd_mono' (h1 x hx) (by omega), fun h => absurd h h2⟩
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    obtain ⟨id, j, rfl, rfl, hRj, hc, hrel⟩ := jetHit_spec hj
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, ⟨hfb, hfcl⟩, hfbody⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hcl M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hcl).2.2.1
    have hid : id ∈ CalledIds
        (mkX .s11j s (.cell (.atom 11) (.cell (.cell (.atom wildTag) clue) body)) r1 [t1]) :=
      ⟨_, InTree.here _, by simp [rowOfSkelX], by simp [rowOfSkelX, kidE, SkelX.row, e1]⟩
    obtain ⟨T, hRT, hT⟩ := hJ id hid
    rw [hRj, Option.some.injEq] at hRT
    subst hRT
    have hrB : Bnd M r1 := bnd_semS (by omega) hM T hT hrel hs
    have hsz := size_mkX .s11j s (.cell (.atom 11) (.cell (.cell (.atom wildTag) clue) body)) r1 [t1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hrB (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · intro _
      refine ⟨id, _, by simp [rowOfSkelX, kidE, SkelX.row, e1], hRj, ?_⟩
      simp only [mkX_label, rowOfSkelX, hdN, tlN]
      exact hc
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      exact nodeOK_mono (by omega) (hn1 u hu)
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, ⟨hfb, hfcl⟩, hfbody⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hcl M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    obtain ⟨hr2, hn2⟩ := ih2 hB M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hcl).2.2.1; have e2 := (genX_label hB).2.2.1
    have hsz := size_mkX .s11d s (.cell (.atom 11) (.cell (.cell b clue) body)) r1 [t1, t2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr2 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact nodeOK_mono (by omega) (hn1 u hu)
      · exact nodeOK_mono (by omega) (hn2 u hu)
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro M hM hJ h5 hs hf
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfbody⟩ := hf
    obtain ⟨hr1, hn1⟩ := ih1 hB M hM (jetB_child hJ (by simp)) (op5_child h5 (by simp)) hs (by assumption)
    have e1 := (genX_label hB).2.2.1
    have hsz := size_mkX .s11s s (.cell (.atom 11) (.cell (.atom b) body)) r1 [t2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsz
    refine ⟨bnd_mono' hr1 (by omega), nodes_mkX ⟨?_, ?_⟩ ?_⟩
    · root_tac
    · simp [rowOfSkelX]
    · intro k hk u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      exact nodeOK_mono (by omega) (hn1 u hu)

end Run

/-! ## 5. The data of a run: rows, roots, J nouns -/

section Data
open Nock.Jet.Autogen (Tpl compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (callsOf rootsOf atomV)

variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Tpl} {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

include hgen in
theorem data_rows : (j8DataOf p Rg Rt hgen).rows = rowsOfT t := rfl

include hgen in
theorem data_bigs : (j8DataOf p Rg Rt hgen).bigs =
    bigsP p (rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ jNounsP p Rt ((callsOf (rowsOfT t)).map Prod.fst).dedup
      (callsOf (rowsOfT t))) (rowsOfT t) := rfl

include hgen in
theorem data_acs : (j8DataOf p Rg Rt hgen).acs = acsP p (j8DataOf p Rg Rt hgen).bigs
    (j8DataOf p Rg Rt hgen).dupP := rfl

theorem mem_rowsOfT {x : RowNX} (hx : x ∈ (rowsOfT t).toList) : ∃ u, InTree t u ∧ x = rowOfSkelX u.label := by
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [t] u).1 hu
  simp only [List.mem_singleton] at hc; subst hc
  exact ⟨u, hcu, rfl⟩

theorem size_rowsOfT : (rowsOfT t).size = t.size := by
  simp only [rowsOfT, List.size_toArray, List.length_map, bfsForest_length, totalSize, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem mem_bigsP {roots : List Noun} {rows : Array RowNX} {a : ℕ} (ha : a ∈ bigsP p roots rows) :
    p ≤ a ∧ ∃ n ∈ roots ++ rows.toList.flatMap rowHandleNounsX, a ∈ leavesOf n := by
  simp only [bigsP, List.mem_mergeSort, List.mem_dedup, List.mem_filter, decide_eq_true_eq,
    List.mem_flatMap] at ha
  obtain ⟨⟨n, hn, ha⟩, hp⟩ := ha
  exact ⟨hp, n, hn, ha⟩

theorem bigs_lt (hS : ∀ v ∈ s.leafList, v < p) (hF : ∀ v ∈ f.leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ProgOp5OK p t) :
    ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, a < p + (j8DataOf p Rg Rt hgen).rows.size := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hJ : JetB p Rg.R t := fun id hid => ⟨Rt id, (hRt id hid).1, (hRt id hid).2.2⟩
  obtain ⟨hr, hn⟩ := gen_bnd hp2 hgen p le_rfl hJ hop5 (bnd_of_leafList hS) (bnd_of_leafList hF)
  set K := p + t.size with hK
  have hKp : p ≤ K := by omega
  have hsB : Bnd K s := bnd_mono (by omega) (bnd_of_leafList hS)
  have hfB : Bnd K f := bnd_mono (by omega) (bnd_of_leafList hF)
  -- every handle noun of every row
  have hrow : ∀ x ∈ (rowsOfT t).toList, ∀ m ∈ rowHandleNounsX x, Bnd K m := by
    intro x hx m hm
    obtain ⟨u, hu, rfl⟩ := mem_rowsOfT hx
    exact (hn u hu).1 m hm
  -- the calls
  have hcall : ∀ cl ∈ callsOf (rowsOfT t), cl.1 ∈ CalledIds t ∧ Bnd K cl.2 ∧
      Bnd K (compile p (Rt cl.1)) := by
    intro cl hcl
    simp only [callsOf, List.mem_filterMap] at hcl
    obtain ⟨x, hx, hxc⟩ := hcl
    split_ifs at hxc with hst
    obtain rfl := Option.some.inj hxc
    obtain ⟨u, hu, rfl⟩ := mem_rowsOfT hx
    obtain ⟨id, j, hid, hRj, hjc⟩ := (hn u hu).2 hst
    have hcal : id ∈ CalledIds t := ⟨u, hu, hst, hid⟩
    rw [hid]
    refine ⟨hcal, (hn u hu).1 _ (by simp [rowHandleNounsX]), ?_⟩
    have h1 := (hRt id hcal).1
    rw [hRj, Option.some.injEq] at h1
    subst h1
    simp only [atomV]
    have hjc' : compile p (Rt id) = (rowOfSkelX u.label).ftt := hjc
    rw [hjc']
    exact (hn u hu).1 _ (by simp [rowHandleNounsX])
  have hroots : ∀ m ∈ rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ jNounsP p Rt ((callsOf (rowsOfT t)).map Prod.fst).dedup
      (callsOf (rowsOfT t)), Bnd K m := by
    intro m hm
    simp only [rootsOf, jNounsP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_map, List.mem_dedup] at hm
    rcases hm with ((rfl | rfl | rfl) | ⟨x, hx, hm⟩) | (⟨i, ⟨cl, hcl, rfl⟩, rfl⟩ | ⟨⟨cl, c⟩, hcl, hm⟩)
    · exact hsB
    · exact hfB
    · exact hr
    · exact hrow x hx m (by
        simp only [handleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hm
        simp only [rowHandleNounsX, List.mem_cons]
        rcases hm with h | h | h | h | h | h <;> simp [h])
    · exact (hcall cl hcl).2.2
    · have hcl' := List.fst_mem_of_mem_zipIdx hcl
      obtain ⟨hid, hsB', -⟩ := hcall cl hcl'
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hsB'
      · simp only [callValsP, List.mem_map] at hm
        obtain ⟨y, hy, rfl⟩ := hm
        exact bnd_honestRows (by omega) hKp (Rt cl.1) (hRt cl.1 hid).2.2 hsB' c y hy
  intro a ha
  rw [data_bigs] at ha
  obtain ⟨-, m, hm, ham⟩ := mem_bigsP ha
  rw [data_rows, size_rowsOfT]
  rw [List.mem_append, List.mem_flatMap] at hm
  rcases hm with hm | ⟨x, hx, hm⟩
  · exact bnd_leavesOf (hroots m hm) a ham
  · exact bnd_leavesOf (hrow x hx m hm) a ham

end Data

/-! ## 6. Goldilocks: two limbs, one `p` row -/

section Single
open Nock.Atoms (B limbs Canonical val)
open Nock.V1J8.Gen (combOf spineOf padN linkOrder lastIdxOf idxOf idxD idxN)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rIAP rootIdxP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (spineL mem_spineL linkOrder_spec spineL_cells
  lastIdxOf_mem idxD_of_nodup idxOf_eq combPP_eq acsP_eq)

/-- **A big atom below `p + 2^31` has exactly two limbs** `[a + 1 − p, B − 1]` (low limb `1 + k`, `k < 2^31`). -/
theorem limbs_two {a : ℕ} (h1 : Nock.Atoms.p ≤ a) (h2 : a < Nock.Atoms.p + 2 ^ 31) :
    limbs a = [a + 1 - Nock.Atoms.p, B - 1] := by
  have hB := Nock.Atoms.B_eq
  have hp : Nock.Atoms.p = 18446744069414584321 := by simp [Nock.Atoms.p, Nock.Field.p]
  have hc : Canonical [a + 1 - Nock.Atoms.p, B - 1] := by
    refine ⟨fun x hx => ?_, fun _ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> omega
    · simp only [List.getLast_cons_cons, List.getLast_singleton]; omega
  have hv : val [a + 1 - Nock.Atoms.p, B - 1] = a := by
    simp only [Nock.Atoms.val_cons, Nock.Atoms.val_nil, mul_zero, add_zero]
    rw [hB]; omega
  rw [← Nock.Atoms.limbs_val hc, hv]

/-- **Every row of the spine list is `[lo (B − 1)]`** when every big atom is in `[p, p + 2^31)`. -/
theorem spineL_shape {bigs : List ℕ} (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    ∀ y ∈ spineL bigs, ∃ lo, y = .cell (.atom lo) (.atom (B - 1)) := by
  intro y hy
  obtain ⟨a, ha, hy⟩ := (mem_spineL bigs y).1 hy
  rw [limbs_two (hb a ha).1 (hb a ha).2] at hy
  simp only [spineOf, combOf, List.mem_singleton] at hy
  exact ⟨_, hy⟩

theorem combPP_cell : combPP Nock.Atoms.p = .cell (.atom 1) (.atom (B - 1)) := by
  rw [combPP_eq]; rfl

theorem up_combPP_not_mem {bigs : List ℕ} (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∉ spineL bigs := by
  intro h
  obtain ⟨lo, hlo⟩ := spineL_shape hb _ h
  rw [combPP_cell] at hlo
  simp at hlo

theorem padN_not_mem {bigs : List ℕ} (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    padN ∉ spineL bigs := by
  intro h
  obtain ⟨lo, hlo⟩ := spineL_shape hb _ h
  simp only [padN, Noun.cell.injEq, Noun.atom.injEq] at hlo
  have := Nock.Atoms.B_eq; omega

/-- **The `p` duplicate is off** and the atom cell list is the link order plus the pad row. -/
theorem acsP_two {bigs : List ℕ} (dupP : Bool) (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    (dupP && decide (Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs)) = false ∧
      acsP Nock.Atoms.p bigs dupP = linkOrder (spineL bigs) ++ [padN] := by
  have hd : (dupP && decide (Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs)) = false := by
    simp [up_combPP_not_mem hb]
  refine ⟨hd, ?_⟩
  rw [acsP_eq, hd]; rfl

theorem acsP_nodup {bigs : List ℕ} (dupP : Bool) (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    (acsP Nock.Atoms.p bigs dupP).Nodup := by
  rw [(acsP_two dupP hb).2]
  have hL := linkOrder_spec (spineL bigs) (spineL_cells bigs)
  refine List.nodup_append.2 ⟨hL.1, List.nodup_singleton _, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy; subst hy
  intro e; subst e
  exact padN_not_mem hb ((hL.2.1 _).1 hx)

theorem lastIdxOf_not_mem (l : List Noun) (n : Noun) (h : n ∉ l) : lastIdxOf l n = 0 := by
  unfold lastIdxOf
  have : ((l.zipIdx 0).reverse.find? fun x => x.1 == n) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_reverse] at hx
    simp only [beq_iff_eq]
    intro e; apply h; rw [← e]; exact List.fst_mem_of_mem_zipIdx hx
  rw [this]; rfl

/-- On a duplicate-free list the last index is the first. -/
theorem lastIdxOf_eq_idxOf {l : List Noun} (hl : l.Nodup) (n : Noun) : lastIdxOf l n = idxOf l n := by
  by_cases h : n ∈ l
  · rw [idxOf_eq _ _ h, idxD_of_nodup l _ n hl (lastIdxOf_mem l n h)]
  · rw [lastIdxOf_not_mem l n h]; simp [idxOf, h]

/-- `idxD` is `List.idxOf` on members. -/
theorem idxD_eq_listIdxOf : ∀ (l : List Noun) (n : Noun), n ∈ l → idxD l n = List.idxOf n l
  | [], n, h => by simp at h
  | c :: l, n, h => by
    simp only [idxD, List.idxOf_cons]
    by_cases hc : c = n
    · simp [hc]
    · have hn : n ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hc
        · exact h
      have hb : (c == n) = false := by simpa using hc
      simp [hc, hb, idxD_eq_listIdxOf l n hn]

/-- Every big atom in `[p, p + 2^31)`: the atom cell list is duplicate-free, `combPP`
occurs at most once, its last index is its first, the atom-walk root map `rIAP` is `idxN`, and the root serial of
every big atom is its comb's first index. -/
theorem single_p {bigs : List ℕ} (dupP : Bool) (hb : ∀ a ∈ bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31) :
    let acs := acsP Nock.Atoms.p bigs dupP
    (dupP && decide (Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs)) = false ∧
      acs.Nodup ∧ List.count (combPP Nock.Atoms.p) acs ≤ 1 ∧
      lastIdxOf acs (combPP Nock.Atoms.p) = idxOf acs (combPP Nock.Atoms.p) ∧
      (combPP Nock.Atoms.p ∈ acs → lastIdxOf acs (combPP Nock.Atoms.p) = List.idxOf (combPP Nock.Atoms.p) acs) ∧
      rIAP Nock.Atoms.p acs = idxN acs ∧
      (∀ n ∈ acs, idxOf acs n = List.idxOf n acs) ∧
      ∀ a, rootIdxP Nock.Atoms.p acs a = idxOf acs (combOf (limbs a)) := by
  intro acs
  have hnd : acs.Nodup := acsP_nodup dupP hb
  have hli : ∀ n, lastIdxOf acs n = idxOf acs n := lastIdxOf_eq_idxOf hnd
  have hmem : ∀ n ∈ acs, idxOf acs n = List.idxOf n acs := fun n hn => by
    rw [idxOf_eq _ _ hn, idxD_eq_listIdxOf _ _ hn]
  refine ⟨(acsP_two dupP hb).1, hnd, List.nodup_iff_count_le_one.1 hnd _, hli _, fun h => by rw [hli, hmem _ h],
    ?_, hmem, ?_⟩
  · funext n
    unfold rIAP
    split_ifs with h
    · subst h; rw [hli, combPP_cell]; rfl
    · rfl
  · intro a
    unfold rootIdxP
    split_ifs with h
    · subst h; rw [hli]; rfl
    · rfl

end Single

/-! ## 7. At the run's data -/

section DataSingle
open Nock.Jet.Autogen (Tpl compile)
open Nock.Atoms (B limbs)
open Nock.V1J8.Gen (combOf lastIdxOf idxOf idxN)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (spineL)

variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Tpl} {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

include hgen in
theorem bigBound_single (hpG : p = Nock.Atoms.p) (hS : ∀ v ∈ s.leafList, v < p) (hF : ∀ v ∈ f.leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ProgOp5OK p t) (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    let D := j8DataOf p Rg Rt hgen
    (∀ a ∈ D.bigs, p ≤ a ∧ a < p + D.rows.size ∧ limbs a = [a + 1 - p, B - 1]) ∧
      (D.dupP && decide (Noun.cell (.atom 0) (combPP p) ∈ spineL D.bigs)) = false ∧
      D.acs.Nodup ∧ List.count (combPP p) D.acs ≤ 1 ∧
      lastIdxOf D.acs (combPP p) = idxOf D.acs (combPP p) ∧
      (combPP p ∈ D.acs → lastIdxOf D.acs (combPP p) = List.idxOf (combPP p) D.acs) ∧
      rIAP p D.acs = idxN D.acs ∧
      (∀ n ∈ D.acs, idxOf D.acs n = List.idxOf n D.acs) ∧
      ∀ a, rootIdxP p D.acs a = idxOf D.acs (combOf (limbs a)) := by
  intro D
  have hlt := bigs_lt hgen hS hF hRt hop5
  have hge : ∀ a ∈ D.bigs, p ≤ a := fun a ha => by
    rw [data_bigs] at ha; exact (mem_bigsP ha).1
  subst hpG
  have hb : ∀ a ∈ D.bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31 :=
    fun a ha => ⟨hge a ha, by have := hlt a ha; omega⟩
  have H := single_p D.dupP hb
  rw [← data_acs hgen] at H
  exact ⟨fun a ha => ⟨hge a ha, hlt a ha, limbs_two (hb a ha).1 (hb a ha).2⟩, H⟩

end DataSingle

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
