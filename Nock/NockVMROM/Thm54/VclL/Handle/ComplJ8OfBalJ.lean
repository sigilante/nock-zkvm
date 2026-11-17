/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalJ.lean

Without it `hJ` fails at an honest run: a zero-argument template called on
    a big-atom subject makes the compute consume `(id, h_c, (2, root), h_E, 3)` while the J chip provides
    `(id, h_c, (0, v mod p), h_E, 3)` (J handles are `ChipJ8Toy.hOf`, the cell table's `hdlP`).
  * the J chip's in-chip balance at an arbitrary honest J table (existence form, `honestJ8_cov`): read
    chains (`chainW_cov`, `chainW_prov`), J-3a node facts (`row_facts`: lookup values, local / read constraints,
    `add`/`mul` operands are field atoms), node rows (`nodeW_prov`, `nodeW_cov`), blocks (`blockW_cov`).
  * the `mv` fix: keys are `mv`-free (`keysOf_setMv`), so the three facts of `termJ_sum_of_mv` hold at the fixed
    rows (`hmv_fix`, `hcov_fix`, `hnd_rows` from the layout statics).
  * the run (`jrows_mv_facts`), the registry pins provided by the registry rows (`pins_prov`).
  * the service pairing: the J call rows' service provides total `Σ_calls dJ(κc)` (`jrows_Fj`), the compute
    `s11j` consumes total `Σ_calls fS(keyK κc)` (`jetT_row`, `sum_jetT`); **`hJ_run`: `hJ` at every coin**, from
    `hpG hax hRt h31 hsubj`; `openJ8_with_balG_J`: `OpenJ8.balG` at the run with `hJ` discharged (`hI hA` carried).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
import Nock.Jet.ChipJ8THonestBal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ

open Nock Nock.Jet.ChipJ8 Nock.Jet.Interp
open Nock.Jet.Autogen (nhd ntl)

noncomputable section

section Chain
variable {p : ℕ} [Fact p.Prime]

/-- An untagged value key `(1, c, n, h)`. -/
def vk (c n : ℕ) (h : ZMod p × ZMod p) : List (ZMod p) :=
  [((1 : ℕ) : ZMod p), (c : ZMod p), (n : ZMod p), h.1, h.2]

/-- The cursor walk of a read chain. -/
def walkB : List Bool → Noun → Noun
  | [], x => x
  | b :: bs, x => walkB bs (if b then ntl x else nhd x)

theorem chainW_cov (hd : Noun → ZMod p × ZMod p) (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun),
    ∀ r ∈ chainWG (p := p) hd c dst src ctr bs x, ∀ κ ∈ consK r,
      κ = vk c src (hd x) ∨ ∃ r' ∈ chainWG (p := p) hd c dst src ctr bs x, κ ∈ provK r'
  | [], src, ctr, x, r, hr, κ, hκ => by
    simp only [chainWG, List.mem_singleton] at hr; subst hr
    left
    have : consK (⟨⟨.cp, 0, c, dst, src, 0⟩, mkW 0 1 0 0 0 (0, 0) (hd x) (0, 0)⟩ : CRow (ZMod p)) =
      [vk c src (hd x)] := rfl
    rw [this] at hκ; simpa using hκ
  | b :: bs, src, ctr, x, r, hr, κ, hκ => by
    simp only [chainWG, List.mem_cons] at hr
    rcases hr with rfl | hr
    · left
      cases b
      · have : consK (⟨⟨.sl, 0, c, ctr, src, 0⟩, mkW 0 1 0 0 0 (hd x) (hd (nhd x)) (hd (ntl x))⟩ :
          CRow (ZMod p)) = [vk c src (hd x)] := rfl
        simp only [Bool.false_eq_true, ↓reduceIte] at hκ
        rw [this] at hκ; simpa using hκ
      · have : consK (⟨⟨.sr, 0, c, ctr, src, 0⟩, mkW 0 1 0 0 0 (hd x) (hd (nhd x)) (hd (ntl x))⟩ :
          CRow (ZMod p)) = [vk c src (hd x)] := rfl
        simp only [↓reduceIte] at hκ
        rw [this] at hκ; simpa using hκ
    · rcases chainW_cov hd c dst bs ctr (ctr + 1) _ r hr κ hκ with h | ⟨r', hr', h⟩
      · right
        refine ⟨_, List.mem_cons_self, ?_⟩
        rw [h]
        cases b
        · show _ ∈ [vk c ctr (hd (nhd x))]; simp
        · show _ ∈ [vk c ctr (hd (ntl x))]; simp
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', h⟩

theorem chainW_prov (hd : Noun → ZMod p × ZMod p) (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun),
    ∃ r' ∈ chainWG (p := p) hd c dst src ctr bs x, vk c dst (hd (walkB bs x)) ∈ provK r'
  | [], src, ctr, x => ⟨_, List.mem_singleton_self _, by
      show _ ∈ [vk c dst (hd x)]; simp [walkB]⟩
  | b :: bs, src, ctr, x => by
    obtain ⟨r', hr', h⟩ := chainW_prov hd c dst bs ctr (ctr + 1) (if b then ntl x else nhd x)
    exact ⟨r', by simp only [chainWG]; exact List.mem_cons_of_mem _ hr', by simpa [walkB] using h⟩

theorem walkB_of_follow : ∀ (bs : List Bool) (x y : Noun), followPath bs x = some y → walkB bs x = y
  | [], x, y, h => by simpa [followPath, walkB] using h
  | b :: bs, .atom _, y, h => by simp [followPath] at h
  | b :: bs, .cell l r, y, h => by
    simp only [followPath] at h
    simp only [walkB]
    cases b <;> simpa [nhd, ntl] using walkB_of_follow bs _ y h

end Chain


section NodeFacts
open Nock.Jet.Autogen (Tpl Ty Ex HasTy ev shapeOK)
variable {p : ℕ} [Fact p.Prime]

/-- The operands of an honest `add` / `mul` row are field atoms. -/
theorem exRows_atoms (hp : 0 < p) {k : ℕ} {ax : Fin k → ℕ} {inTy : Fin k → Ty} {s : Noun}
    {a : Fin k → Noun} (hs : ∀ i, Noun.slot (ax i) s = some (a i))
    (ha : ∀ i, shapeOK p (inTy i) (a i) = true) (c : ℕ) {e : Ex k} {τ : Ty}
    (h : HasTy p inTy e τ) : ∀ b, ∀ r ∈ exRows p ax a c b e, (r.node.op = .add ∨ r.node.op = .mul) →
      isFieldAtom p r.x = true ∧ isFieldAtom p r.y = true := by
  induction h with
  | var i => intro b r hr; simp only [exRows, List.mem_singleton] at hr; subst hr; simp
  | const _ => intro b r hr; simp only [exRows, List.mem_singleton] at hr; subst hr; simp
  | nil _ => intro b r hr; simp only [exRows, List.mem_singleton] at hr; subst hr; simp
  | weakN _ ih => exact ih
  | add h₁ h₂ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · intro _
      exact ⟨by rw [isFieldAtom_eq]; exact (Nock.Jet.Autogen.ev_spec hp hs ha h₁).2,
        by rw [isFieldAtom_eq]; exact (Nock.Jet.Autogen.ev_spec hp hs ha h₂).2⟩
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | mul h₁ h₂ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · intro _
      exact ⟨by rw [isFieldAtom_eq]; exact (Nock.Jet.Autogen.ev_spec hp hs ha h₁).2,
        by rw [isFieldAtom_eq]; exact (Nock.Jet.Autogen.ev_spec hp hs ha h₂).2⟩
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | pair _ _ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · intro h; simp at h
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | nth _ _ ih =>
    intro b r hr
    simp only [exRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · intro h; simp at h
    · exact ih _ r hr

theorem gRows_noarith (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun), ∀ row ∈ gRows c τ b r v,
    row.node.op ≠ .add ∧ row.node.op ≠ .mul := by
  intro τ
  induction τ with
  | F => intro b r v row hrow; simp only [gRows, List.mem_singleton] at hrow; subst hrow; simp
  | N => intro b r v row hrow; simp [gRows] at hrow
  | L n τ ih =>
    intro b r v row hrow
    have hel : ∀ (js : List ℕ) (b : ℕ), ∀ row ∈ gElemsR (gRows c τ) (gSz τ) r v c b js,
        row.node.op ≠ .add ∧ row.node.op ≠ .mul := by
      intro js
      induction js with
      | nil => intro b row hrow; simp [gElemsR] at hrow
      | cons j js ihj =>
        intro b row hrow
        simp only [gElemsR, List.mem_cons, List.mem_append] at hrow
        rcases hrow with rfl | hrow | hrow
        · simp
        · exact ih _ _ _ row hrow
        · exact ihj _ row hrow
    simp only [gRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · simp
    · simp
    · exact hel _ _ row hrow

theorem inRows_noarith (T : Tpl) (a : Fin T.k → Noun) (c : ℕ) : ∀ (is : List (Fin T.k)) (b : ℕ),
    ∀ row ∈ inRows T a c b is, row.node.op ≠ .add ∧ row.node.op ≠ .mul := by
  intro is
  induction is with
  | nil => intro b row hrow; simp [inRows] at hrow
  | cons i is ih =>
    intro b row hrow
    simp only [inRows, List.mem_cons, List.mem_append] at hrow
    rcases hrow with rfl | hrow | hrow
    · simp
    · exact gRows_noarith c _ _ _ _ row hrow
    · exact ih _ row hrow

/-- **The honest node facts of a call**: each honest row's value is the looked-up value of its node, its local
and read constraints hold, its operands are looked-up values of nodes of the template, and `add`/`mul` operands
are field atoms. -/
theorem row_facts (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (hsem : T.sem p s = some r) (c : ℕ) :
    ∀ row ∈ honestRows p T s c,
      honestLook (p := p) T s c row.node.id = row.val ∧ LocalOK p row ∧
      readOK s row.node.op row.val row.x row.y = true ∧
      (0 < row.node.op.arity → honestLook (p := p) T s c row.node.a = row.x ∧
        row.node.a ∈ (nodesOf T).map JNode.id) ∧
      (1 < row.node.op.arity → honestLook (p := p) T s c row.node.b = row.y ∧
        row.node.b ∈ (nodesOf T).map JNode.id) ∧
      ((row.node.op = .add ∨ row.node.op = .mul) → isFieldAtom p row.x = true ∧ isFieldAtom p row.y = true) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨-, hnodes, hloc, -, hread, -⟩ := interp_complete hp T hT s r c hsem
  obtain ⟨a, hs, ha, -⟩ := Nock.Jet.Autogen.sem_eq_some_iff.1 hsem
  have hA := argsD_eq hs
  set R := honestRows p T s c with hRdef
  have hlink : LinkIn R R := by
    intro row hrow
    have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact exRows_link (p := p) T.ax _ c R T.body 0
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inl hx) row hrow'
    · exact inRows_link T _ c R _ _
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inr hx) row hrow'
  have hids := honestRows_ids p T s c
  rw [← hRdef] at hids
  have hlook : ∀ e ∈ R, honestLook (p := p) T s c e.node.id = e.val := by
    intro e he
    unfold honestLook
    rw [← hRdef, getElem?_of_ids hids he]
    rfl
  have hmemid : ∀ e ∈ R, e.node.id ∈ (nodesOf T).map JNode.id := by
    intro e he
    rw [← hnodes, List.map_map]
    exact List.mem_map_of_mem he
  intro row hrow
  obtain ⟨hx, hy⟩ := hlink row hrow
  refine ⟨hlook row hrow, hloc row hrow, hread row hrow, fun h0 => ?_, fun h1 => ?_, fun hop => ?_⟩
  · obtain ⟨e, he, hid, hv⟩ := hx h0
    exact ⟨by rw [← hid, hlook e he, hv], hid ▸ hmemid e he⟩
  · obtain ⟨e, he, hid, hv⟩ := hy h1
    exact ⟨by rw [← hid, hlook e he, hv], hid ▸ hmemid e he⟩
  · have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append, hA] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact exRows_atoms hp hs ha c hT 0 row hrow' hop
    · have := inRows_noarith T a c _ _ row hrow'
      rcases hop with h | h
      · exact absurd h this.1
      · exact absurd h this.2

end NodeFacts

section NodeCov
open Nock.Jet.Autogen (Tpl)
variable {p : ℕ} [Fact p.Prime]

/-- **H1**: the handle map sends a small atom `v` to `(0, v)` (the cell table's `hdlP` does, `hJd_small`). -/
def H1 {p : ℕ} (hd : Noun → ZMod p × ZMod p) : Prop :=
  ∀ v, v < p → hd (.atom v) = (((0 : ℕ) : ZMod p), ((v : ℕ) : ZMod p))

theorem hd_fieldAtom (hd : Noun → ZMod p × ZMod p) (hH : H1 hd) {x : Noun} (h : isFieldAtom p x = true) :
    hd x = (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal x : ℕ) : ZMod p)) := by
  cases x with
  | atom v =>
    have hv : v < p := by simpa [isFieldAtom] using h
    simp only [Nock.Jet.Autogen.atomVal]
    exact hH v hv
  | cell _ _ => simp [isFieldAtom] at h

theorem axPos_var {T : Tpl} (hT : axPosB T = true) {nd : JNode} (hnd : nd ∈ nodesOf T) {i ax : ℕ}
    (hop : nd.op = .var i ax) : 1 ≤ ax := by
  have := List.all_eq_true.mp hT nd hnd
  rw [hop] at this
  simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using this

/-- **A node's rows provide its value key.** -/
theorem nodeW_prov (hd : Noun → ZMod p × ZMod p) (hH : H1 hd) (T : Tpl) (hT : T.WellTyped p) (hax : axPosB T = true) (s r : Noun)
    (hsem : T.sem p s = some r) (c S ctr : ℕ) (row : JRow) (hrow : row ∈ honestRows p T s c) :
    ∃ r' ∈ nodeWG (p := p) hd c S ctr (honestLook (p := p) T s c) s row.node,
      vk c row.node.id (hd (honestLook (p := p) T s c row.node.id)) ∈ provK r' := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hl, hloc, hrd, hx, -, -⟩ := row_facts T hT s r hsem c row hrow
  have hnd : row.node ∈ nodesOf T := by
    rw [← (interp_complete hp T hT s r c hsem).2.1]; exact List.mem_map_of_mem hrow
  set lk := honestLook (p := p) T s c with hlk
  unfold nodeWG
  unfold LocalOK at hloc
  cases hop : row.node.op with
  | var i ax =>
    dsimp only
    rw [hop] at hrd
    obtain ⟨r', hr', h⟩ := chainW_prov (p := p) hd c row.node.id (axPath ax) S ctr s
    refine ⟨r', hr', ?_⟩
    have h1 := axPos_var hax hnd hop
    have hsl : Noun.slot ax s = some row.val := by simpa [readOK] using hrd
    rw [slot_path ax ax s h1 le_rfl] at hsl
    rwa [hl, ← walkB_of_follow _ _ _ hsl]
  | nth j =>
    dsimp only
    rw [hop] at hrd
    have hx' := (hx (by rw [hop]; simp [JOp.arity])).1
    obtain ⟨r', hr', h⟩ := chainW_prov (p := p) hd c row.node.id (List.replicate j true ++ [false]) row.node.a
      ctr (lk row.node.a)
    refine ⟨r', hr', ?_⟩
    have hsl : nthO j row.x = some row.val := by simpa [readOK] using hrd
    rw [nthO_path, ← hx'] at hsl
    rwa [hl, ← walkB_of_follow _ _ _ hsl]
  | tlN n =>
    dsimp only
    rw [hop] at hrd
    have hx' := (hx (by rw [hop]; simp [JOp.arity])).1
    obtain ⟨r', hr', h⟩ := chainW_prov (p := p) hd c row.node.id (List.replicate n true) row.node.a
      ctr (lk row.node.a)
    refine ⟨r', hr', ?_⟩
    have hsl : tailO n row.x = some row.val := by simpa [readOK] using hrd
    rw [tailO_path, ← hx'] at hsl
    rwa [hl, ← walkB_of_follow _ _ _ hsl]
  | const k =>
    dsimp only
    rw [hop] at hloc
    have hv : row.val = .atom k := by simpa [localOK] using hloc
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [hl, hv]
    show _ ∈ [vk c row.node.id (((0 : ℕ) : ZMod p), ((k : ℕ) : ZMod p))]
    have hk : k < p :=
      (ComplJ8Jet.honestRows_small hp T hT s r c hsem row hrow).2.2.2 k hop
    rw [hH k hk]; simp [vk]
  | add =>
    dsimp only
    rw [hop] at hloc
    have hv : row.val = .atom ((Nock.Jet.Autogen.atomVal row.x + Nock.Jet.Autogen.atomVal row.y) % p) := by simpa [localOK] using hloc
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ [vk c row.node.id (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.id) : ℕ) : ZMod p))]
    rw [hl, hv]
    have hlt := Nat.mod_lt (Nock.Jet.Autogen.atomVal row.x + Nock.Jet.Autogen.atomVal row.y) (Fact.out : p.Prime).pos
    rw [hH _ hlt]; simp [vk, Nock.Jet.Autogen.atomVal]
  | mul =>
    dsimp only
    rw [hop] at hloc
    have hv : row.val = .atom ((Nock.Jet.Autogen.atomVal row.x * Nock.Jet.Autogen.atomVal row.y) % p) := by simpa [localOK] using hloc
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ [vk c row.node.id (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.id) : ℕ) : ZMod p))]
    rw [hl, hv]
    have hlt := Nat.mod_lt (Nock.Jet.Autogen.atomVal row.x * Nock.Jet.Autogen.atomVal row.y) (Fact.out : p.Prime).pos
    rw [hH _ hlt]; simp [vk, Nock.Jet.Autogen.atomVal]
  | pair =>
    dsimp only
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ [vk c row.node.id (hd (lk row.node.id))]
    simp
  | isF =>
    dsimp only
    rw [hop] at hloc
    have hv : isFieldAtom p row.x = true ∧ row.val = row.x := by simpa [localOK] using hloc
    have hx' := (hx (by rw [hop]; simp [JOp.arity])).1
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ [vk c row.node.id (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.a) : ℕ) : ZMod p))]
    rw [hl, hv.2, hd_fieldAtom hd hH hv.1, hx']
    simp
  | isNil =>
    dsimp only
    rw [hop] at hloc
    have hv : row.x = .atom 0 ∧ row.val = row.x := by simpa [localOK] using hloc
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ [vk c row.node.id (((0 : ℕ) : ZMod p), ((0 : ℕ) : ZMod p))]
    rw [hl, hv.2, hv.1, hH 0 (Fact.out : p.Prime).pos] <;> simp

/-- The keys a node's rows consume: the subject's, another node's value, or one its own rows provide. -/
def NodeCovOK (hd : Noun → ZMod p × ZMod p) (T : Tpl) (lk : ℕ → Noun) (c S : ℕ) (s : Noun) (rows : List (CRow (ZMod p)))
    (κ : List (ZMod p)) : Prop :=
  κ = vk c S (hd s) ∨ (∃ n ∈ (nodesOf T).map JNode.id, κ = vk c n (hd (lk n))) ∨
    ∃ r' ∈ rows, κ ∈ provK r'

theorem nodeW_cov (hd : Noun → ZMod p × ZMod p) (hH : H1 hd) (T : Tpl) (hT : T.WellTyped p) (s r : Noun)
    (hsem : T.sem p s = some r) (c S ctr : ℕ) (row : JRow) (hrow : row ∈ honestRows p T s c) :
    ∀ x ∈ nodeWG (p := p) hd c S ctr (honestLook (p := p) T s c) s row.node, ∀ κ ∈ consK x,
      NodeCovOK hd T (honestLook (p := p) T s c) c S s
        (nodeWG (p := p) hd c S ctr (honestLook (p := p) T s c) s row.node) κ := by
  obtain ⟨hl, hloc, hrd, hx, hy, hat⟩ := row_facts T hT s r hsem c row hrow
  set lk := honestLook (p := p) T s c with hlk
  intro x hxm κ hκ
  unfold LocalOK at hloc
  have hnodeW := hxm
  unfold nodeWG at hxm
  cases hop : row.node.op with
  | var i ax =>
    rw [hop] at hxm
    rcases chainW_cov hd c row.node.id (axPath ax) S ctr s x hxm κ hκ with h | ⟨r', hr', h⟩
    · exact Or.inl h
    · refine Or.inr (Or.inr ⟨r', ?_, h⟩); unfold nodeWG; rw [hop]; exact hr'
  | nth j =>
    rw [hop] at hxm
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    rcases chainW_cov hd c row.node.id _ row.node.a ctr (lk row.node.a) x hxm κ hκ with h | ⟨r', hr', h⟩
    · exact Or.inr (Or.inl ⟨_, hx'.2, h⟩)
    · refine Or.inr (Or.inr ⟨r', ?_, h⟩); unfold nodeWG; rw [hop]; exact hr'
  | tlN n =>
    rw [hop] at hxm
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    rcases chainW_cov hd c row.node.id _ row.node.a ctr (lk row.node.a) x hxm κ hκ with h | ⟨r', hr', h⟩
    · exact Or.inr (Or.inl ⟨_, hx'.2, h⟩)
    · refine Or.inr (Or.inr ⟨r', ?_, h⟩); unfold nodeWG; rw [hop]; exact hr'
  | const k =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    exact absurd hκ (by simp [consK, keysOf, ents0, ents1])
  | add =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    have hy' := hy (by rw [hop]; simp [JOp.arity])
    obtain ⟨ha1, ha2⟩ := hat (Or.inl hop)
    have e : consK (⟨⟨.add, 0, c, row.node.id, row.node.a, row.node.b⟩, mkW 0 1 (Nock.Jet.Autogen.atomVal (lk row.node.id) : ZMod p)
        (Nock.Jet.Autogen.atomVal (lk row.node.a) : ZMod p) (Nock.Jet.Autogen.atomVal (lk row.node.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩ : CRow (ZMod p)) =
        [vk c row.node.a (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.a) : ℕ) : ZMod p)),
         vk c row.node.b (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.b) : ℕ) : ZMod p))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact Or.inr (Or.inl ⟨_, hx'.2, by rw [hx'.1, hd_fieldAtom hd hH ha1]⟩)
    · exact Or.inr (Or.inl ⟨_, hy'.2, by rw [hy'.1, hd_fieldAtom hd hH ha2]⟩)
  | mul =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    have hy' := hy (by rw [hop]; simp [JOp.arity])
    obtain ⟨ha1, ha2⟩ := hat (Or.inr hop)
    have e : consK (⟨⟨.mul, 0, c, row.node.id, row.node.a, row.node.b⟩, mkW 0 1 (Nock.Jet.Autogen.atomVal (lk row.node.id) : ZMod p)
        (Nock.Jet.Autogen.atomVal (lk row.node.a) : ZMod p) (Nock.Jet.Autogen.atomVal (lk row.node.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩ : CRow (ZMod p)) =
        [vk c row.node.a (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.a) : ℕ) : ZMod p)),
         vk c row.node.b (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.b) : ℕ) : ZMod p))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact Or.inr (Or.inl ⟨_, hx'.2, by rw [hx'.1, hd_fieldAtom hd hH ha1]⟩)
    · exact Or.inr (Or.inl ⟨_, hy'.2, by rw [hy'.1, hd_fieldAtom hd hH ha2]⟩)
  | pair =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    have hy' := hy (by rw [hop]; simp [JOp.arity])
    have e : consK (⟨⟨.rp, 0, c, row.node.id, row.node.a, row.node.b⟩, mkW 0 1 0 0 0
        (hd (lk row.node.id)) (hd (lk row.node.a)) (hd (lk row.node.b))⟩ : CRow (ZMod p)) =
        [vk c row.node.a (hd (lk row.node.a)), vk c row.node.b (hd (lk row.node.b))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact Or.inr (Or.inl ⟨_, hx'.2, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, hy'.2, rfl⟩)
  | isF =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    rw [hop] at hloc
    have hv : isFieldAtom p row.x = true ∧ row.val = row.x := by simpa [localOK] using hloc
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    have e : consK (⟨⟨.isf, 0, c, row.node.id, row.node.a, 0⟩, mkW 0 1 0 (Nock.Jet.Autogen.atomVal (lk row.node.a) : ZMod p) 0
        (0, 0) (0, 0) (0, 0)⟩ : CRow (ZMod p)) =
        [vk c row.node.a (((0 : ℕ) : ZMod p), ((Nock.Jet.Autogen.atomVal (lk row.node.a) : ℕ) : ZMod p))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    subst hκ
    exact Or.inr (Or.inl ⟨_, hx'.2, by rw [hx'.1, hd_fieldAtom hd hH hv.1]⟩)
  | isNil =>
    rw [hop] at hxm; simp only [List.mem_singleton] at hxm; subst hxm
    rw [hop] at hloc
    have hv : row.x = .atom 0 ∧ row.val = row.x := by simpa [localOK] using hloc
    have hx' := hx (by rw [hop]; simp [JOp.arity])
    have e : consK (⟨⟨.nil, 0, c, row.node.id, row.node.a, 0⟩, mkW 0 1 0 0 0
        (0, 0) (0, 0) (0, 0)⟩ : CRow (ZMod p)) =
        [vk c row.node.a (((0 : ℕ) : ZMod p), ((0 : ℕ) : ZMod p))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    subst hκ
    exact Or.inr (Or.inl ⟨_, hx'.2, by rw [hx'.1, hv.1, hH 0 (Fact.out : p.Prime).pos]⟩)

theorem nodesW_mem (hd : Noun → ZMod p × ZMod p) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ∀ (nds : List JNode) (ctr : ℕ), ∀ x ∈ nodesWG (p := p) hd c S lk s ctr nds,
      ∃ nd ∈ nds, ∃ ctr', x ∈ nodeWG (p := p) hd c S ctr' lk s nd ∧
        ∀ y ∈ nodeWG (p := p) hd c S ctr' lk s nd, y ∈ nodesWG (p := p) hd c S lk s ctr nds
  | [], _, x, hx => by simp [nodesWG] at hx
  | nd :: nds, ctr, x, hx => by
    simp only [nodesWG, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨nd, List.mem_cons_self, ctr, hx, fun y hy => by simp only [nodesWG, List.mem_append]; exact Or.inl hy⟩
    · obtain ⟨nd', hnd', c', h1, h2⟩ := nodesW_mem hd c S lk s nds _ x hx
      exact ⟨nd', List.mem_cons_of_mem _ hnd', c', h1, fun y hy => by
        simp only [nodesWG, List.mem_append]; exact Or.inr (h2 y hy)⟩

theorem nodesW_sub (hd : Noun → ZMod p × ZMod p) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ∀ (nds : List JNode) (ctr : ℕ), ∀ nd ∈ nds,
      ∃ ctr', ∀ y ∈ nodeWG (p := p) hd c S ctr' lk s nd, y ∈ nodesWG (p := p) hd c S lk s ctr nds
  | [], _, nd, h => by simp at h
  | x :: xs, ctr, nd, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ctr, fun y hy => by simp only [nodesWG, List.mem_append]; exact Or.inl hy⟩
    · obtain ⟨c', hc'⟩ := nodesW_sub hd c S lk s xs (ctr + nodeVirt x) nd h
      exact ⟨c', fun y hy => by simp only [nodesWG, List.mem_append]; exact Or.inr (hc' y hy)⟩

/-- **The in-block balance**: every key a block row consumes is the registry key of its template, or provided by
a row of the block. -/
theorem blockW_cov (hd : Noun → ZMod p × ZMod p) (hH : H1 hd) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) (hT : (R i).WellTyped p)
    (hax : axPosB (R i) = true) (r : Noun) (hsem : (R i).sem p s = some r) :
    ∀ x ∈ blockWG (p := p) hd R c i s, ∀ κ ∈ consK x,
      κ = [((2 : ℕ) : ZMod p), (i : ZMod p), (hd (Nock.Jet.Autogen.compile p (R i))).1,
        (hd (Nock.Jet.Autogen.compile p (R i))).2] ∨
      ∃ x' ∈ blockWG (p := p) hd R c i s, κ ∈ provK x' := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨-, hnodes, -, -, -, out, hout, hid0, -⟩ := interp_complete hp (R i) hT s r c hsem
  set T := R i with hTdef
  set lk := honestLook (p := p) T s c with hlk
  set N := (nodesOf T).length with hN
  have hbl : blockWG (p := p) hd R c i s = ⟨callPre R c i, mkW 1 1 0 0 0 (hd (Nock.Jet.Autogen.compile p T))
      (hd s) (hd (lk 0))⟩ :: nodesWG (p := p) hd c N lk s (N + 1) (nodesOf T) := rfl
  -- every node value key is provided in the block
  have hprov : ∀ n ∈ (nodesOf T).map JNode.id, ∃ x' ∈ blockWG (p := p) hd R c i s,
      vk c n (hd (lk n)) ∈ provK x' := by
    intro n hn
    obtain ⟨nd, hnd, rfl⟩ := List.mem_map.mp hn
    rw [← hnodes] at hnd
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hnd
    obtain ⟨ctr', hsub⟩ := nodesW_sub (p := p) hd c N lk s (nodesOf T) (N + 1) row.node
      (by rw [← hnodes]; exact List.mem_map_of_mem hrow)
    obtain ⟨x', hx', h⟩ := nodeW_prov hd hH T hT hax s r hsem c N ctr' row hrow
    exact ⟨x', by rw [hbl]; exact List.mem_cons_of_mem _ (hsub x' hx'), h⟩
  have hsubj : vk c N (hd s) ∈ provK (⟨callPre R c i, mkW 1 1 0 0 0 (hd (Nock.Jet.Autogen.compile p T))
      (hd s) (hd (lk 0))⟩ : CRow (ZMod p)) := by
    show _ ∈ [vk c N (hd s)]; simp
  intro x hx κ hκ
  rw [hbl] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · have e : consK (⟨callPre R c i, mkW 1 1 0 0 0 (hd (Nock.Jet.Autogen.compile p T))
        (hd s) (hd (lk 0))⟩ : CRow (ZMod p)) =
        [[((2 : ℕ) : ZMod p), (i : ZMod p), (hd (Nock.Jet.Autogen.compile p T)).1,
          (hd (Nock.Jet.Autogen.compile p T)).2], vk c 0 (hd (lk 0))] := rfl
    rw [e] at hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact Or.inl rfl
    · right
      have h0 : (0 : ℕ) ∈ (nodesOf T).map JNode.id := by
        rw [← hnodes, List.map_map]; exact hid0 ▸ List.mem_map_of_mem hout
      exact hprov 0 h0
  · obtain ⟨nd, hnd, ctr', hxn, hsub⟩ := nodesW_mem (p := p) hd c N lk s (nodesOf T) (N + 1) x hx
    rw [← hnodes] at hnd
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hnd
    rcases nodeW_cov hd hH T hT s r hsem c N ctr' row hrow x hxn κ hκ with h | ⟨n, hn, h⟩ | ⟨x', hx', h⟩
    · exact Or.inr ⟨_, by rw [hbl]; exact List.mem_cons_self, h ▸ hsubj⟩
    · exact Or.inr (h ▸ hprov n hn)
    · exact Or.inr ⟨x', by rw [hbl]; exact List.mem_cons_of_mem _ (hsub x' hx'), h⟩

/-- **The in-chip balance of the honest J rows** (existence form): every consumed key is provided. -/
theorem honestJ8_cov (hd : Noun → ZMod p × ZMod p) (hH : H1 hd) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (hcl : ∀ cl ∈ calls, (R cl.1).WellTyped p ∧ axPosB (R cl.1) = true ∧ (∃ r, (R cl.1).sem p cl.2 = some r) ∧
      cl.1 ∈ regs) :
    ∀ x ∈ honestJ8G (p := p) hd R regs calls, ∀ κ ∈ consK x, ∃ x' ∈ honestJ8G (p := p) hd R regs calls,
      κ ∈ provK x' := by
  intro x hx κ hκ
  have hx' := hx
  unfold honestJ8G at hx'
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hx'
  rcases hx' with ⟨i, -, rfl⟩ | ⟨⟨⟨i, s⟩, c⟩, hmem, hxb⟩
  · exact absurd hκ (by simp [consK, keysOf, ents0, ents1, regPre])
  · obtain ⟨hT, hax, ⟨r, hsem⟩, hreg⟩ := hcl _ (List.fst_mem_of_mem_zipIdx hmem)
    rcases blockW_cov hd hH R c i s hT hax r hsem x hxb κ hκ with h | ⟨x', hx'', h⟩
    · refine ⟨⟨regPre i, mkW 0 1 0 0 0 (hd (Nock.Jet.Autogen.compile p (R i))) (0, 0) (0, 0)⟩, ?_, ?_⟩
      · unfold honestJ8G
        exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hreg, rfl⟩)
      · rw [h]; exact List.mem_singleton_self _
    · refine ⟨x', ?_, h⟩
      unfold honestJ8G
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hmem, hx''⟩)

end NodeCov

section MvFix
open Nock.Jet.RapJetJ8 (consKT provKT consKT_eq provKT_eq tlF tlF_one tlF_two)
open Nock.Jet.Autogen (Tpl)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (mvFixP)
variable {p : ℕ} [Fact p.Prime]

/-- A row with its `mv` replaced. -/
def setMv (r : CRow (ZMod p)) (m : ZMod p) : CRow (ZMod p) := { r with w := { r.w with mv := m } }

theorem colOf_setMv (r : CRow (ZMod p)) (m : ZMod p) (j : ℕ) (hj : j ≠ 19) : colOf (setMv r m) j = colOf r j := by
  unfold colOf setMv
  split_ifs <;> first | rfl | (split <;> simp_all)

theorem keysOf_setMv (es : List (Kd × List KE)) (hes : ∀ e ∈ es, ∀ k ∈ e.2, k ≠ KE.col 19)
    (r : CRow (ZMod p)) (m : ZMod p) : keysOf es (setMv r m) = keysOf es r := by
  show ((es.filter fun e => e.1 == r.pre.kd).map fun e => e.2.map (KE.ev (colOf (setMv r m)))) =
    ((es.filter fun e => e.1 == r.pre.kd).map fun e => e.2.map (KE.ev (colOf r)))
  refine List.map_congr_left fun e he => List.map_congr_left fun k hk => ?_
  have := hes e (List.mem_of_mem_filter he) k hk
  cases k with
  | col j => exact colOf_setMv r m j (fun h => this (h ▸ rfl))
  | k c => rfl

theorem consK_setMv (r : CRow (ZMod p)) (m : ZMod p) : consK (setMv r m) = consK r := by
  unfold consK
  rw [keysOf_setMv _ (by decide) r m, keysOf_setMv _ (by decide) r m]

theorem provK_setMv (r : CRow (ZMod p)) (m : ZMod p) : provK (setMv r m) = provK r :=
  keysOf_setMv _ (by decide) r m

theorem ents3_setMv (r : CRow (ZMod p)) (m : ZMod p) : keysOf ents3 (setMv r m) = keysOf ents3 r :=
  keysOf_setMv _ (by decide) r m

theorem consKT_setMv (r : CRow (ZMod p)) (m : ZMod p) : consKT (setMv r m) = consKT r := by
  rw [consKT_eq, consKT_eq, consK_setMv]

theorem provKT_setMv (r : CRow (ZMod p)) (m : ZMod p) : provKT (setMv r m) = provKT r := by
  rw [provKT_eq, provKT_eq, provK_setMv]

/-- The row's one provided (untagged) key. -/
def pk (r : CRow (ZMod p)) : List (ZMod p) :=
  if r.pre.kd = .reg then [((2 : ℕ) : ZMod p), (r.pre.id : ZMod p), r.w.kN, r.w.vN]
  else [((1 : ℕ) : ZMod p), (r.pre.cid : ZMod p), (r.pre.pn : ZMod p), (provHW r).1, (provHW r).2]

theorem provK_pk (r : CRow (ZMod p)) : provK r = [pk r] := by
  unfold pk
  split_ifs with h
  · exact provK_reg r h
  · exact provK_eq r h

theorem provKT_pk (r : CRow (ZMod p)) : provKT r = [tlF (pk r)] := by
  rw [provKT_eq, provK_pk]; rfl

/-- The multiplicity the fix assigns. -/
def mvOf (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) (r : CRow (ZMod p)) : ZMod p :=
  (((rows.flatMap consKT ++ pins).count (tlF (pk r)) : ℕ) : ZMod p)

theorem mvFixP_eq (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    mvFixP p rows pins = rows.map fun r => setMv r (mvOf rows pins r) := by
  unfold mvFixP
  refine List.map_congr_left fun r _ => ?_
  simp only [provKT_pk]
  rfl

theorem flatMap_consKT_fix (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    (mvFixP p rows pins).flatMap consKT = rows.flatMap consKT := by
  rw [mvFixP_eq, List.flatMap_map]
  exact List.flatMap_congr fun r _ => consKT_setMv r _

theorem flatMap_provKT_fix (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    (mvFixP p rows pins).flatMap provKT = rows.flatMap provKT := by
  rw [mvFixP_eq, List.flatMap_map]
  exact List.flatMap_congr fun r _ => provKT_setMv r _

/-- **`hmv` for the fixed rows.** -/
theorem hmv_fix (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    ∀ x ∈ mvFixP p rows pins, ∀ κ ∈ provKT x,
      x.w.mv = (((((mvFixP p rows pins).flatMap consKT).count κ + pins.count κ : ℕ)) : ZMod p) := by
  intro x hx κ hκ
  rw [mvFixP_eq] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  rw [provKT_setMv, provKT_pk, List.mem_singleton] at hκ
  subst hκ
  rw [flatMap_consKT_fix, ← List.count_append]
  rfl

/-- **`hcov` for the fixed rows**, from the existence-form balance of the rows and the pins' providers. -/
theorem hcov_fix (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p)))
    (hc : ∀ x ∈ rows, ∀ κ ∈ consK x, ∃ x' ∈ rows, κ ∈ provK x')
    (hpin : ∀ κ ∈ pins, ∃ x' ∈ rows, ∃ κ0 ∈ provK x', κ = tlF κ0) :
    ∀ κ ∈ (mvFixP p rows pins).flatMap consKT ++ pins, κ ∈ (mvFixP p rows pins).flatMap provKT := by
  intro κ hκ
  rw [flatMap_consKT_fix] at hκ
  rw [flatMap_provKT_fix]
  rcases List.mem_append.mp hκ with h | h
  · obtain ⟨x, hx, hκx⟩ := List.mem_flatMap.mp h
    rw [consKT_eq] at hκx
    obtain ⟨κ0, hκ0, rfl⟩ := List.mem_map.mp hκx
    obtain ⟨x', hx', h'⟩ := hc x hx κ0 hκ0
    exact List.mem_flatMap.mpr ⟨x', hx', by rw [provKT_eq]; exact List.mem_map_of_mem h'⟩
  · obtain ⟨x', hx', κ0, hκ0, rfl⟩ := hpin κ h
    exact List.mem_flatMap.mpr ⟨x', hx', by rw [provKT_eq]; exact List.mem_map_of_mem hκ0⟩

theorem one_ne_two : ((1 : ℕ) : ZMod p) ≠ ((2 : ℕ) : ZMod p) := by
  intro h
  have : ((2 : ℕ) : ZMod p) - ((1 : ℕ) : ZMod p) = 0 := by rw [h, sub_self]
  norm_num at this

/-- The provided-key projection on the layout. -/
def G (q : PRow) : ZMod p × ZMod p × ZMod p :=
  if q.kd = .reg then (((2 : ℕ) : ZMod p), (q.id : ZMod p), 0) else (((1 : ℕ) : ZMod p), (q.cid : ZMod p), (q.pn : ZMod p))

/-- The same projection read off a tag-last key. -/
def g (κ : List (ZMod p)) : ZMod p × ZMod p × ZMod p :=
  (κ.getD 7 0, κ.getD 0 0, if κ.getD 7 0 = ((2 : ℕ) : ZMod p) then 0 else κ.getD 1 0)

theorem g_pk (r : CRow (ZMod p)) : g (tlF (pk r)) = G r.pre := by
  unfold pk G
  split_ifs with h
  · rw [tlF_two]; simp [g]
  · have h12 : (1 : ZMod p) ≠ 2 := by simpa using one_ne_two (p := p)
    rw [tlF_one]; simp [g, h12]

theorem nonreg_map (l : List PRow) (h : ∀ q ∈ l, q.kd ≠ .reg) :
    l.map (G (p := p)) = (l.filterMap tvKey).map fun k => (((1 : ℕ) : ZMod p), (k.1 : ZMod p), (k.2 : ZMod p)) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have hq := h q List.mem_cons_self
    have ht : tvKey q = some (q.cid, q.pn) := by simp [tvKey, hq]
    simp only [List.map_cons, List.filterMap_cons, ht]
    simp only [G, hq, ↓reduceIte, ih fun q' h' => h q' (List.mem_cons_of_mem _ h')]

theorem flatMap_provKT_pk : ∀ rows : List (CRow (ZMod p)), rows.flatMap provKT = rows.map fun r => tlF (pk r)
  | [] => rfl
  | r :: rows => by rw [List.flatMap_cons, provKT_pk, flatMap_provKT_pk rows]; rfl

/-- **`hnd` for honest rows realizing the layout.** -/
theorem hnd_rows (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p)))
    (hlay : rows.map CRow.pre = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup) (hregs : regs.Nodup) :
    (rows.flatMap provKT).Nodup := by
  rw [flatMap_provKT_pk]
  refine List.Nodup.of_map g ?_
  rw [List.map_map, show (g ∘ fun r => tlF (pk r)) = (G (p := p)) ∘ CRow.pre from funext g_pk, ← List.map_map, hlay]
  unfold layoutJ8 at hsmall huniq ⊢
  rw [List.map_append]
  have hbk : ∀ q ∈ blocks R 0 ids, q.kd ≠ .reg := fun q h => (Nock.Jet.RapJetJ8.blocks_kd R ids 0 q h).1
  have hreg0 : (regs.map regPre).filterMap tvKey = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro q hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    simp [tvKey, regPre]
  rw [List.filterMap_append, hreg0, List.nil_append] at huniq
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · rw [List.map_map]
    refine hregs.map_on fun i hi j hj hij => ?_
    have hi' := (hsmall _ (List.mem_append_left _ (List.mem_map_of_mem hi))).1
    have hj' := (hsmall _ (List.mem_append_left _ (List.mem_map_of_mem hj))).1
    simp only [Function.comp, G, regPre, ↓reduceIte, Prod.mk.injEq] at hij
    exact natCast_inj_lt hi' hj' hij.2.1
  · rw [nonreg_map _ hbk]
    refine huniq.map_on fun k hk k' hk' hkk => ?_
    obtain ⟨q, hq, hqk⟩ := List.mem_filterMap.1 hk
    obtain ⟨q', hq', hqk'⟩ := List.mem_filterMap.1 hk'
    have hs := hsmall q (List.mem_append_right _ hq)
    have hs' := hsmall q' (List.mem_append_right _ hq')
    simp only [tvKey, hbk q hq, hbk q' hq', ↓reduceIte, Option.some.injEq] at hqk hqk'
    subst hqk hqk'
    have hpn : q.pn < p := by unfold PRow.pn; split_ifs <;> omega
    have hpn' : q'.pn < p := by unfold PRow.pn; split_ifs <;> omega
    simp only [Prod.mk.injEq] at hkk
    rw [natCast_inj_lt hs.2.1 hs'.2.1 hkk.2.1, natCast_inj_lt hpn hpn' hkk.2.2]
  · intro a ha b hb hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    simp only [G, regPre, hbk q' hq', ↓reduceIte, Prod.mk.injEq] at hab
    exact one_ne_two hab.1.symm

end MvFix

/-! ## The run: the subject binder and the J chip's in-chip multiset facts -/

section RunJ
open Nock.Jet.RapJetJ8 (consKT provKT consKT_eq provKT_eq tlF)
open Nock.Jet.Autogen (Tpl compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf mvFixP pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Edit Nock.Edit.GenX Nock.Walk
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- Kept separate so it can be merged into `hJsib`. -/
def JSubjOK (D : J8Data p Rg fuel s f r) : Prop := ∀ cl ∈ D.calls, ∀ v, cl.2 = .atom v → v < p

theorem exists_mem_zipIdx {α : Type} {l : List α} {x : α} (h : x ∈ l) : ∃ c, (x, c) ∈ l.zipIdx := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩⟩

variable [Fact (ringChar (ZMod p)).Prime] (Rt : ℕ → Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- The calls of the run are well typed, `axPosB`, in the template's domain, and registered. -/
theorem calls_ok (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ cl ∈ (j8DataOf p Rg Rt hgen).calls, (Rt cl.1).WellTyped p ∧ axPosB (Rt cl.1) = true ∧
      (∃ r, (Rt cl.1).sem p cl.2 = some r) ∧ cl.1 ∈ (j8DataOf p Rg Rt hgen).regs := by
  intro cl hcl
  have hc := ComplJ8Jet.calls_of_hregC hgen Rt hRt cl hcl
  have hid := ComplJ8Of.calls_called hgen cl hcl
  exact ⟨hc.1, (hRt _ hid).2.1, hc.2, List.mem_dedup.mpr (List.mem_map_of_mem hcl)⟩

/-- A registered template's compiled formula is a cell of the table. -/
theorem compile_mem (id : ℕ) (hid : id ∈ (j8DataOf p Rg Rt hgen).regs) :
    compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).cells := by
  obtain ⟨a, c, hac⟩ := ComplJ8Data.compile_isCell p (Rt id)
  have := ComplJ8Data.jn_good p Rg Rt hgen (compile p (Rt id))
    (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩)) a c hac
  exact this

/-- **The registry pins are provided by the registry rows.** -/
theorem pins_prov :
    ∀ κ ∈ pinsOfP p (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).idx,
      ∃ x' ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) Rt
        (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls, ∃ κ0 ∈ provK x', κ = tlF κ0 := by
  set D := j8DataOf p Rg Rt hgen with hD
  intro κ hκ
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hκ
  refine ⟨⟨regPre id, mkW 0 1 0 0 0 (ComplJ8Data.hJd p D.cells D.acs (compile p (Rt id))) (0, 0) (0, 0)⟩, ?_, _,
    List.mem_singleton_self _, ?_⟩
  · unfold honestJ8G
    exact List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩)
  · have hm := compile_mem Rt hgen id hid
    obtain ⟨a, c, hac⟩ := ComplJ8Data.compile_isCell p (Rt id)
    congr 1
    simp only [Nock.Jet.PinJ8.pinKey, mkW]
    rw [hac]
    simp [keyRg, KE.ev, colOf, Col.id, Col.kN, Col.vN, regPre, ComplJ8Data.hJd, ComplJ8Data.hdlP, hD,
      ComplJ8Data.j8DataOf, hac]

/-- **The in-chip balance of the run's J rows** (existence form, before the `mv` fix). -/
theorem honest_cov (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls,
      ∀ κ ∈ consK x, ∃ x' ∈ honestJ8G (p := p) (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) Rt (j8DataOf p Rg Rt hgen).regs
        (j8DataOf p Rg Rt hgen).calls, κ ∈ provK x' :=
  honestJ8_cov _ (fun v hv => by simpa using ComplJ8Data.hJd_small p _ _ v hv) Rt _ _ (calls_ok Rt hgen hRt)

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK) in
/-- **The layout statics of the run** (`hsmall`, `huniq`), from `hax`, `hRt` and the row binder. -/
theorem lay_statics (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : ComplJ8Of.Rows31 (j8DataOf p Rg Rt hgen))
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    (∀ q ∈ layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids,
      q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).filterMap tvKey).Nodup := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hlt := ComplJ8Of.calls_lt hgen hax
  have hmemR : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∃ cl ∈ (j8DataOf p Rg Rt hgen).calls, cl.1 = id := by
    intro id hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
    exact ⟨cl, hcl, e⟩
  have hJlen : (layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).length < p := by
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen, List.length_map]
    exact ComplJ8Of.size_lt_p Rt hgen hp63 h31 (by simp [ComplJ8Of.sizesJ8])
  have hidsl : (j8DataOf p Rg Rt hgen).ids.length < p := by
    have h1 : (j8DataOf p Rg Rt hgen).ids.length ≤ (bfsForest [(j8DataOf p Rg Rt hgen).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 (ComplJ8Of.size_lt_p Rt hgen hp63 h31 List.mem_cons_self)
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls
    hcalls hlt hJlen
  refine ⟨ComplJ8Jet.hsmall_of_blocks Rt _ _ (fun i hi => ?_) hidsl (fun i hi => (hblk i hi).2) hp,
    ComplJ8Jet.huniq_of_blocks Rt _ _ (fun i hi => (hblk i hi).1)⟩
  obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK) in
/-- **The three multiset facts of `termJ_sum_of_mv` at the run's J rows**: unique provides, covered consumes and
pins, and `mv` = consumers + pins. -/
theorem jrows_mv_facts (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : ComplJ8Of.Rows31 (j8DataOf p Rg Rt hgen))
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((j8DataOf p Rg Rt hgen).jrows.flatMap provKT).Nodup ∧
    (∀ κ ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap consKT ++ pinsOfP p (j8DataOf p Rg Rt hgen).regs
        (j8DataOf p Rg Rt hgen).idx, κ ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap provKT) ∧
    (∀ x ∈ (j8DataOf p Rg Rt hgen).jrows, ∀ κ ∈ provKT x,
      x.w.mv = (((((j8DataOf p Rg Rt hgen).jrows.flatMap consKT).count κ +
        (pinsOfP p (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).idx).count κ : ℕ)) : ZMod p)) := by
  rw [ComplJ8Jet.j8DataOf_jrows Rt hgen]
  obtain ⟨hsmall, huniq⟩ := lay_statics Rt hgen hp63 hax h31 hRt
  refine ⟨?_, hcov_fix _ _ (honest_cov Rt hgen hRt) (pins_prov Rt hgen), hmv_fix _ _⟩
  rw [flatMap_provKT_fix]
  exact hnd_rows Rt _ _ _ (ComplJ8Jet.honestJ8_pre _ Rt _ _) hsmall huniq (List.nodup_dedup _)

end RunJ

/-! ## The jet service sub-balance `hJ` at the run -/

section HJ
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf mvFixP pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.RapJetJ8 (keyK dJ consKT provKT tlF)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sT)
open Nock.Jet.Autogen (Tpl compile)
open Module
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem keyX_eq (m : ℕ) (l : List ChipHX.RE) (e : Nock.Reified.Env (ZMod p)) :
    DenXJ8.keyX (K := K) m l e = keyK m (l.map (ChipHX.RE.ev e.trace)) := by
  funext c
  simp only [DenXJ8.keyX, DenXJ8.keyXN, keyK]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[(c : ℕ)]? <;> simp [ChipHX.RE.ev]

/-- A compute jet consume's reciprocal is the service weight `fS` of its key. -/
theorem DX_jet (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ) :
    (TeleCQX.DX δ (Compute.TowerD.gatherEnv b e) e ChipHX.jetRecX)⁻¹ =
      ComplJ8Bal.fS δ b χ (keyK 8 (ChipHX.jetRecX.map (ChipHX.RE.ev e.trace))) := by
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by decide), ← keyX_eq]
  simp only [ComplJ8Bal.fS]
  rw [VerJ8.coinsCV_J8, ← ComplJ8CompPole.γH_eq, ← ComplJ8CompPole.ρH_eq]
  exact congrArg Inv.inv (InhabJ8Good.compress_split _ _ _ _).symm

/-- The template result of a call (the call row's output value). -/
def res (p : ℕ) (cl : ℕ × Noun) : Noun := ((Rt cl.1).sem p cl.2).getD (.atom 0)

/-- **The jet service key of a call** `(id, h(compile T), h(s), h(T s), TAG_jet)`, at the J handle map `hd`. -/
def κc (hd : Noun → ZMod p × ZMod p) (cl : ℕ × Noun) : List (ZMod p) :=
  [(cl.1 : ZMod p), (hd (compile p (Rt cl.1))).1, (hd (compile p (Rt cl.1))).2, (hd cl.2).1,
    (hd cl.2).2, (hd (res Rt p cl)).1, (hd (res Rt p cl)).2, ((3 : ℕ) : ZMod p)]

theorem look0 (T : Tpl) (hT : T.WellTyped p) (s0 r0 : Noun) (hsem : T.sem p s0 = some r0) (c : ℕ) :
    Nock.Jet.ChipJ8.honestLook (p := p) T s0 c 0 = r0 ∧ r0 ∈ (Nock.Jet.Interp.honestRows p T s0 c).map
      Nock.Jet.Interp.JRow.val := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨-, -, -, -, -, out, hout, hid, hv⟩ := Nock.Jet.Interp.interp_complete hp T hT s0 r0 c hsem
  have := (row_facts T hT s0 r0 hsem c out hout).1
  rw [hid, hv] at this
  exact ⟨this, hv ▸ List.mem_map_of_mem hout⟩

theorem ents3_nocall (x : Nock.Jet.ChipJ8.CRow (ZMod p)) (h : x.pre.kd ≠ .call) :
    Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.ents3 x = [] := by
  simp only [Nock.Jet.ChipJ8.keysOf, Nock.Jet.ChipJ8.ents3, List.filter_cons, List.filter_nil]
  have : (Nock.Jet.ChipJ8.Kd.call == x.pre.kd) = false := by simpa using Ne.symm h
  simp [this]

/-- The service term of a J row. -/
abbrev Fj (chals : ℕ → K) (x : Nock.Jet.ChipJ8.CRow (ZMod p)) : 𝕂′ :=
  liftQ δ x.w.m * sT δ chals Nock.Jet.ChipJ8.ents3 x

/-- **A call block's service terms total its call key's weight.** -/
theorem blockW_Fj (chals : ℕ → K) (hd : Noun → ZMod p × ZMod p) (c i : ℕ) (s0 : Noun) (hT : (Rt i).WellTyped p)
    (r0 : Noun) (hsem : (Rt i).sem p s0 = some r0) :
    ((Nock.Jet.ChipJ8.blockWG (p := p) hd Rt c i s0).map (Fj δ chals)).sum = dJ δ chals (κc Rt hd (i, s0)) := by
  obtain ⟨hl0, -⟩ := look0 (Rt i) hT s0 r0 hsem c
  have hres : res Rt p (i, s0) = r0 := by simp [res, hsem]
  have hnodes : ∀ x ∈ Nock.Jet.ChipJ8.nodesWG (p := p) hd c (Nock.Jet.Interp.nodesOf (Rt i)).length
      (Nock.Jet.ChipJ8.honestLook (p := p) (Rt i) s0 c) s0 ((Nock.Jet.Interp.nodesOf (Rt i)).length + 1)
      (Nock.Jet.Interp.nodesOf (Rt i)), Fj δ chals x = 0 := by
    intro x hx
    have hpre : x.pre ∈ Nock.Jet.ChipJ8.nodesPre c (Nock.Jet.Interp.nodesOf (Rt i)).length
        ((Nock.Jet.Interp.nodesOf (Rt i)).length + 1) (Nock.Jet.Interp.nodesOf (Rt i)) := by
      rw [← Nock.Jet.ChipJ8.nodesWG_pre (p := p) hd c _ (Nock.Jet.ChipJ8.honestLook (p := p) (Rt i) s0 c) s0]
      exact List.mem_map_of_mem hx
    have hk := (Nock.Jet.RapJetJ8.nodesPre_kd c _ _ _ x.pre hpre).2
    simp [Fj, sT, ents3_nocall x hk]
  show (((⟨Nock.Jet.ChipJ8.callPre Rt c i, Nock.Jet.ChipJ8.mkW 1 1 0 0 0
      (hd (compile p (Rt i))) (hd s0)
      (hd (Nock.Jet.ChipJ8.honestLook (p := p) (Rt i) s0 c 0))⟩ :
        Nock.Jet.ChipJ8.CRow (ZMod p)) :: _).map (Fj δ chals)).sum = _
  rw [List.map_cons, List.sum_cons, List.sum_eq_zero (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hnodes x hx), add_zero]
  simp only [Fj, sT, hl0]
  have : Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.ents3 (⟨Nock.Jet.ChipJ8.callPre Rt c i, Nock.Jet.ChipJ8.mkW 1 1 0 0 0
      (hd (compile p (Rt i))) (hd s0) (hd r0)⟩ :
        Nock.Jet.ChipJ8.CRow (ZMod p)) = [κc Rt hd (i, s0)] := by
    rw [κc, hres]; rfl
  rw [this]
  simp [Nock.Jet.ChipJ8.mkW, liftQ]

/-- **The J side of the service sub-balance**: the J rows' service terms total the call keys' weights. -/
theorem jrows_Fj (chals : ℕ → K)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((j8DataOf p Rg Rt hgen).jrows.map (Fj δ chals)).sum =
      ((j8DataOf p Rg Rt hgen).calls.map fun cl => dJ δ chals (κc Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) cl)).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hok := calls_ok Rt hgen hRt
  rw [ComplJ8Jet.j8DataOf_jrows Rt hgen, mvFixP_eq, List.map_map]
  have e1 : (Fj δ chals) ∘ (fun r => setMv r (mvOf (Nock.Jet.ChipJ8.honestJ8G (p := p) (ComplJ8Data.hJd p D.cells D.acs) Rt D.regs D.calls)
      (pinsOfP p D.regs D.idx) r)) = Fj δ chals := by
    funext x; simp only [Function.comp, Fj, sT, ents3_setMv]; rfl

  rw [e1]
  unfold Nock.Jet.ChipJ8.honestJ8G
  rw [List.map_append, List.sum_append, List.sum_eq_zero (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    simp [Fj, sT, ents3_nocall, Nock.Jet.ChipJ8.regPre]), zero_add, Nock.Jet.RapJetJ8.sum_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 D.calls, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  obtain ⟨⟨i, s0⟩, c⟩ := q
  obtain ⟨hT, -, ⟨r0, hsem⟩, -⟩ := hok _ (List.fst_mem_of_mem_zipIdx hq)
  exact blockW_Fj δ Rt chals (ComplJ8Data.hJd p D.cells D.acs) c i s0 hT r0 hsem


include hgen in
/-- An `s11j` row of the run: its jet id, its registered formula, its template result. -/
theorem s11j_row (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    {u : NTree SkelX} (hin : InTree t u) (hst : (rowOfSkelX u.label).st = .s11j) :
    ∃ id, (rowOfSkelX u.label).sf1 = .atom id ∧ (rowOfSkelX u.label).ftt = compile p (Rt id) ∧
      (Rt id).sem p (rowOfSkelX u.label).s = some (rowOfSkelX u.label).e := by
  have h := inTree_rowSem hgen hin
  unfold RowNX.SemN at h
  rw [hst] at h
  obtain ⟨-, -, -, -, id, j, -, hft, hRj, hjc, hrel⟩ := h
  have hcalled : id ∈ CalledIds t := ⟨u, hin, hst, hft⟩
  rw [(hRt id hcalled).1] at hRj
  cases Option.some.inj hRj
  exact ⟨id, hft, hjc.symm, hrel⟩

theorem sum_filterMap_ite {α β M : Type} [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (h : α → β)
    (g : β → M) : ∀ l : List α,
    (l.map fun x => if P x then g (h x) else 0).sum = ((l.filterMap fun x => if P x then some (h x) else none).map g).sum
  | [] => rfl
  | x :: l => by
    by_cases hx : P x
    · simp [hx, sum_filterMap_ite P h g l]
    · simp [hx, sum_filterMap_ite P h g l]

/-- The compute row's jet term at its handles. -/
def Fu (hd : Noun → ZMod p × ZMod p) (χ : Coins frameJ8 K) (u : NTree SkelX) : 𝕂′ :=
  if (rowOfSkelX u.label).st = .s11j then
    ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt hd (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).sf1, (rowOfSkelX u.label).s)))
  else 0

set_option maxHeartbeats 1000000 in
/-- **A compute row's jet consume is the service weight of its call's key** (`0` off `s11j`). -/
theorem jetT_row (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p)
    (j : ℕ) (hj : j < (bfsForest [t]).length) :
    ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        pubVal j = Fu δ b Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) χ ((bfsForest [t])[j]'hj) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj, hrr]
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold ComplJ8OfBalG.jetT
  rw [DX_jet δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 16 (by decide)]
  have hmap : ∀ tr : ℕ → ZMod p, ChipHX.jetRecX.map (ChipHX.RE.ev tr) =
      [tr 32, tr 41, tr 42, tr 25, tr 26, tr 29, tr 30, ((3 : ℕ) : ZMod p)] := fun tr => rfl
  rw [hmap]
  simp only [HonestCompX.cxSf1_v, HonestCompX.cxFtt_k, HonestCompX.cxFtt_v, HonestCompX.cxS_k,
    HonestCompX.cxS_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  unfold Fu
  by_cases hst : rr.st = .s11j
  · rw [if_pos hst, ← hrr, if_pos (by rw [hst]; rfl), map_one, one_mul]
    obtain ⟨id, hft, hftt, hsem⟩ := s11j_row Rt hgen hRt hin hst
    rw [← hrr] at hft hftt hsem
    have hcl : (id, rr.s) ∈ D.calls := by
      show _ ∈ Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      refine List.mem_filterMap.mpr ⟨rr, ?_, ?_⟩
      · simp only [List.toList_toArray]; exact List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩
      · simp [hst, hft, Nock.V1J8.Gen.atomV]
    obtain ⟨hT, -, -, hreg⟩ := calls_ok Rt hgen hRt _ hcl
    have hidp : id < p := ComplJ8Of.calls_lt hgen hax _ hcl
    obtain ⟨c, hz⟩ := exists_mem_zipIdx hcl
    have hjn : ∀ y ∈ (Nock.Jet.Interp.honestRows p (Rt id) rr.s c).map Nock.Jet.Interp.JRow.val, y ∈ D.jn := by
      intro y hy
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hz, List.mem_cons_of_mem _ hy⟩)
    have hsjn : rr.s ∈ D.jn := List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hz, List.mem_cons_self⟩)
    obtain ⟨hl0, he⟩ := look0 (Rt id) hT rr.s rr.e hsem c
    have hres : res Rt p (id, rr.s) = rr.e := by simp [res, hsem]
    have hid : HonestCompX.hv D.H (.atom id) = (id : ZMod p) := by
      show (((ComplJ8Data.hdlP p D.cells D.acs (.atom id)).2 : ℕ) : ZMod p) = _
      simp [ComplJ8Data.hdlP, hidp]
    congr 2
    simp only [κc, hres, Nock.V1J8.Gen.atomV, hft, hid, hftt]
    rfl
  · have h16 : RowDecodeVSX.stIdx rr.st ≠ 16 := by
      intro h; apply hst; revert h; cases rr.st <;> simp [RowDecodeVSX.stIdx]
    rw [if_neg h16, ← hrr, if_neg hst]
    simp

theorem sum_jetT (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
        (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((j8DataOf p Rg Rt hgen).calls.map fun cl =>
        ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) cl))).sum := by
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
      (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Fu δ b Rt (ComplJ8Data.hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) χ ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [jetT_row δ b Rt hgen hax hRt χ pubVal j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t]
  show _ = ((Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).map _).sum
  unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
  simp only [List.toList_toArray]
  rw [← sum_filterMap_ite (fun r : RowNX => r.st = .s11j) (fun r => (Nock.V1J8.Gen.atomV r.sf1, r.s)), List.map_map]
  rfl

set_option maxHeartbeats 2000000 in
/-- **`hJ`, the jet service sub-balance of `balG` clause 3, at the run, at every coin**: the compute jet consumes,
the registry pins and the J terminal sum to zero.  Binders: `hpG hax hRt h31` only. -/
theorem hJ_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.jetT δ b (j8DataOf p Rg Rt hgen).H
          (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (ComplJ8OfBalG.pubC δ b Rt hgen χ) j +
        ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map
          fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0 := by
  intro χ _
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  set D := j8DataOf p Rg Rt hgen with hD
  -- the J terminal as `Σ termJ`
  have eJ : Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) =
      ∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k) := by
    show Quad.mk _ (pubsJOf δ D χ 0) (pubsJOf δ D χ 1) = _
    have e0 : pubsJOf δ D χ 0 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 0 := by simp [pubsJOf]
    have e1 : pubsJOf δ D χ 1 = pub2 δ (∑ k, termJ δ (VerJ8.chalsJJ8 χ) (D.jrows.get k)) 1 := by simp [pubsJOf]
    rw [e0, e1, pub2_mk]
  obtain ⟨hnd, hcov, hmv⟩ := jrows_mv_facts Rt hgen hp63 hax h31 hRt
  have hT := Nock.Jet.ChipJ8T.HonestBal.termJ_sum_of_mv_fin δ (VerJ8.chalsJJ8 χ) D.jrows.get
    (pinsOfP p D.regs D.idx) (by rw [List.ofFn_get]; exact hnd) (by rw [List.ofFn_get]; exact hcov)
    (by rw [List.ofFn_get]; exact hmv)
  rw [List.ofFn_get] at hT
  have hF := jrows_Fj δ Rt hgen (VerJ8.chalsJJ8 χ) hRt
  -- the pins
  have eP : ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map
      fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum =
      ((pinsOfP p D.regs D.idx).map (dJ δ (VerJ8.chalsJJ8 χ))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]
    simp only [pinCons, pinsOfP, List.map_map]
    rfl
  -- the compute side
  have eC := sum_jetT δ b Rt hgen hax hRt χ (ComplJ8OfBalG.pubC δ b Rt hgen χ)
  have eCJ : ((D.calls.map fun cl => ComplJ8Bal.fS δ b χ (keyK 8 (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum) =
      ((D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc Rt (ComplJ8Data.hJd p D.cells D.acs) cl))).sum := by
    rw [ComplJ8OfBal.dJ_eq δ b χ]; rfl
  have hF' : (D.jrows.map fun r => liftQ δ r.w.m * sT δ (VerJ8.chalsJJ8 χ) Nock.Jet.ChipJ8.ents3 r).sum =
      (D.calls.map fun cl => dJ δ (VerJ8.chalsJJ8 χ) (κc (p := p) Rt (ComplJ8Data.hJd p D.cells D.acs) cl)).sum := hF
  rw [eC, eP, eJ, hT, eCJ, hF']
  ring


open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgOp5OK) in
/-- **`balG` with its jet sub-balance closed**: `OpenJ8.balG` at the run from the binders and the subject binder
the inc and atom-walk pair sub-balances `hI hA` still carried (exact statements as in `balG_closed`). -/
theorem openJ8_with_balG_J (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (O : OpenJ8 δ b (BRun δ b Rt hgen hpG h31))
    (hI : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.incT δ b (j8DataOf p Rg Rt hgen).H
        (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (ComplJ8OfBalG.pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, ComplJ8OfBalG.awT δ b (j8DataOf p Rg Rt hgen).H
        (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (ComplJ8OfBalG.pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1))) :
    OpenJ8 δ b (BRun δ b Rt hgen hpG h31) :=
  ComplJ8OfBalG.openJ8_with_balG δ b Rt hgen hpG hax hop5 hRt h31 hwalk O hI hA
    (hJ_run δ b Rt hgen hpG hax hRt h31)

end HJ

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ
