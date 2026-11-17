/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Of.lean

* §1 the sizes of the run's six tables, one common orbit height `htJ8`, the orbit from `3·2^htJ8 ∣ P − 1`,
    the nodes `i ↦ ω^i`, the public layout `PbOf`.
  * §2 the honest traces and message of the run at a coin; §3b the concrete atom part `avOf` and its staging.
  * §4 the obligation groups; §7 `obligations_of_run` and **`complJ8`** at Goldilocks, carrying the atom table,
    atom walk and the three balances as the hypothesis `OpenJ8`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompRun
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal
import Nock.Jet.ChipJ8THonestRAP
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8RegLeaf
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)

noncomputable section

/-! ## 1. Sizes, the common orbit, the public layout -/

section Sizes
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The atom walk's row count (one placeholder row when absent). -/
def nVOf (D : J8Data p Rg fuel s f r) : ℕ := if D.preads = [] then 1 else (walkRows D.acs D.preads).length

/-- The atom walk's root count (`0` when absent). -/
def krVOf (D : J8Data p Rg fuel s f r) : ℕ := if D.preads = [] then 0 else krW D.acs D.preads

/-- The six table sizes: compute, cell, J-8 walk, J, atom, atom walk. -/
def sizesJ8 (D : J8Data p Rg fuel s f r) : List ℕ :=
  [(bfsForest [D.t]).length, D.cells.length, (walkRows D.cells D.reads).length, D.jrows.length, D.acs.length,
    nVOf D]

/-- The largest table. -/
def szJ8 (D : J8Data p Rg fuel s f r) : ℕ := (sizesJ8 D).foldr max 0

/-- **The common orbit height**: the least `h ≥ 1` with every table `≤ 2^h`. -/
def htJ8 (D : J8Data p Rg fuel s f r) : ℕ := max 1 (Nat.clog 2 (szJ8 D))

theorem le_szJ8 (D : J8Data p Rg fuel s f r) : ∀ x ∈ sizesJ8 D, x ≤ szJ8 D := by
  unfold szJ8
  generalize sizesJ8 D = L
  intro x hx
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem le_two_pow_ht (D : J8Data p Rg fuel s f r) {x : ℕ} (hx : x ∈ sizesJ8 D) : x ≤ 2 ^ htJ8 D :=
  calc x ≤ szJ8 D := le_szJ8 D x hx
    _ ≤ 2 ^ Nat.clog 2 (szJ8 D) := Nat.le_pow_clog (by norm_num) _
    _ ≤ 2 ^ htJ8 D := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

theorem one_le_ht (D : J8Data p Rg fuel s f r) : 1 ≤ htJ8 D := le_max_left _ _

end Sizes

section Orbit
variable {F : Type} [Field F] [Fintype F]

theorem exists_orderOf_eq_of_dvd' (m : ℕ) (hm : m ∣ Fintype.card F - 1) : ∃ ω : F, orderOf ω = m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdvd : m ∣ orderOf g := by rw [hg]; exact hm
  refine ⟨((g ^ (orderOf g / m) : Fˣ) : F), ?_⟩
  rw [orderOf_units]
  exact orderOf_pow_orderOf_div hne hdvd

/-- **The strict orbit of height `h`** from `3·2^h ∣ |F| − 1`, coset `β = 1`. -/
def orbitOf (h : ℕ) (h1 : 1 ≤ h) (hd : 3 * 2 ^ h ∣ Fintype.card F - 1) : StrictOrbitDomain F 3 h where
  ω := (exists_orderOf_eq_of_dvd' _ hd).choose
  βcoset := 1
  e_pos := by norm_num
  h_pos := h1
  order_ω := (exists_orderOf_eq_of_dvd' _ hd).choose_spec
  βcoset_ne_zero := one_ne_zero

/-- The nodes `i ↦ ω^i`. -/
def powN {h : ℕ} (o : StrictOrbitDomain F 3 h) (n : ℕ) : Fin n → F := fun i => o.ω ^ (i : ℕ)

theorem powN_ok {h n : ℕ} (o : StrictOrbitDomain F 3 h) (hn : n ≤ 2 ^ h) :
    Function.Injective (powN o n) ∧
      ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), powN o n ⟨(i : ℕ) + 1, hi⟩ = powN o n i * o.ω := by
  refine ⟨fun a c hac => Fin.ext ?_, fun i hi => pow_succ _ _⟩
  have hord : orderOf o.ω = 3 * 2 ^ h := o.order_ω
  refine pow_injOn_Iio_orderOf ?_ ?_ hac
  · show (a : ℕ) < orderOf _; rw [hord]; have := a.isLt; omega
  · show (c : ℕ) < orderOf _; rw [hord]; have := c.isLt; omega

end Orbit

/-! ### The public layout of a run -/

section Pb
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem bfs_pos (t : NTree SkelX) : 0 < (bfsForest [t]).length :=
  List.length_pos_of_mem ((mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, InTree.here _⟩)

theorem walk_pos (cells : List Noun) (reads : List (Noun × ℕ)) : 0 < (walkRows cells reads).length :=
  lt_of_lt_of_le (one_le_krW cells reads) (krW_le_rows cells reads)

theorem nV_pos (D : J8Data p Rg fuel s f r) : 0 < nVOf D := by
  unfold nVOf; split_ifs
  · exact one_pos
  · exact walk_pos _ _

/-- The divisibility binder of a run: `3·2^htJ8 ∣ p − 1` (the 40th's `hF` over the common height). -/
def DvdOK (D : J8Data p Rg fuel s f r) : Prop := 3 * 2 ^ htJ8 D ∣ p - 1

/-- The common orbit. -/
def orbJ8 (D : J8Data p Rg fuel s f r) (hF : DvdOK D) : StrictOrbitDomain (ZMod p) 3 (htJ8 D) :=
  orbitOf (htJ8 D) (one_le_ht D) (by rw [ZMod.card]; exact hF)

/-- **The public layout of the run** (`PubJ8`): every table on the common orbit, nodes `ω^i`; the J-8 walk at the
spec rows `walkRows cells reads` with `krW` roots (L2); the J table the run's J rows; the atom walk present iff
some op-5 row compares two big atoms. -/
def PbOf (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length) :
    PubJ8 p where
  h := htJ8 D
  n := (bfsForest [D.t]).length
  hn := bfs_pos D.t
  nodes := powN (orbJ8 D hF) _
  orbit := orbJ8 D hF
  hC := htJ8 D
  nC := D.cells.length
  hnC := hC
  nodesC := powN (orbJ8 D hF) _
  orbitC := orbJ8 D hF
  kroots := krW D.cells D.reads
  hW := htJ8 D
  nW := (walkRows D.cells D.reads).length
  hnW := walk_pos _ _
  nodesW := powN (orbJ8 D hF) _
  orbitW := orbJ8 D hF
  hJ := htJ8 D
  nJ := D.jrows.length
  nodesJ := powN (orbJ8 D hF) _
  orbitJ := orbJ8 D hF
  lay := Nock.Jet.ChipJ8T.HonestRAP.layJ D.jrows.get
  hA := htJ8 D
  nA := D.acs.length
  hnA := hA
  nodesA := powN (orbJ8 D hF) _
  orbitA := orbJ8 D hF
  krootsV := krVOf D
  hV := htJ8 D
  nV := nVOf D
  hnV := nV_pos D
  nodesV := powN (orbJ8 D hF) _
  orbitV := orbJ8 D hF
  Rt := D.Rt
  regs := D.regs
  ids := D.ids
  idx := D.idx
  rk := D.rk

end Pb

/-! ## 2. The honest traces and message at a coin -/

section Honest
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The fingerprint seed `z′ = χ₂ + χ₃√δ` and the memory IO coins `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ`. -/
abbrev zJ (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ WeightsJ8.c2) (χ WeightsJ8.c3)
abbrev γV (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6)
abbrev ρV (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)

/-- A `𝕂′` value as two publics at `2i, 2i+1`. -/
def pub2 (x : 𝕂′) (i : ℕ) : K := if i % 2 = 0 then Quad.re _ x else Quad.im _ x

/-- The big-atom serial map of the cell table's children. -/
abbrev bigOf (D : J8Data p Rg fuel s f r) : Noun → Option ℕ := ComplJ8Data.bigIdOfP p D.acs

/-- The cell multiplicities as functions. -/
abbrev mvF (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j => D.mv.getD j 0
abbrev mxF (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j => D.mx.getD j 0
abbrev mhF (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j => D.mh.getD j 0

end Honest

section HonestE
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The honest memory fingerprint encoder: the verifier's `encJ8 = encZY z y`. -/
abbrev encR (χ : Coins frameJ8 K) : Noun → Nock.ComputeTable.FP 𝕂′ := AcceptsJ8.encJ8 δ χ

theorem encR_congr (χ χ' : Coins frameJ8 K) (h2 : χ WeightsJ8.c2 = χ' WeightsJ8.c2)
    (h3 : χ WeightsJ8.c3 = χ' WeightsJ8.c3) (h4 : χ FrameJ8.cY1 = χ' FrameJ8.cY1)
    (h5 : χ FrameJ8.cY2 = χ' FrameJ8.cY2) : encR δ χ = encR δ χ' := by
  simp only [encR, AcceptsJ8.encJ8]
  rw [show WeightsJ8.c2 = (⟨2, by decide⟩ : Fin frameJ8.n) from rfl,
    show WeightsJ8.c3 = (⟨3, by decide⟩ : Fin frameJ8.n) from rfl] at *
  rw [h2, h3, h4, h5]

/-- On small atoms (no atom-table serial) the verifier's encoder is the inline atom fingerprint. -/
theorem encR_small (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (D : J8Data p Rg fuel s f r) (v : ℕ)
    (hv : ComplJ8Cell.isBig (bigOf D) (.atom v) = false) :
    encR δ χ (.atom v) = Nock.ComputeTable.FP.atomFP (zJ δ χ) (liftQ δ ((v : ℕ) : ZMod p)) := by
  have hlt : v < p := by
    by_contra h
    simp [ComplJ8Cell.isBig, bigOf, ComplJ8Data.bigIdOfP, h, Noun.isCell] at hv
  simp only [encR, AcceptsJ8.encJ8, EncZYJ8.encZY_atom]
  rw [Nock.Atoms.leafVal_small _ (hpG ▸ hlt)]
  simp [liftQ, map_natCast]

theorem encR_cell (χ : Coins frameJ8 K) (a c : Noun) :
    encR δ χ (.cell a c) = Nock.ComputeTable.FP.cons (zJ δ χ) (encR δ χ a) (encR δ χ c) := rfl

/-- The honest cell rows at the coin. -/
abbrev cRows (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → CellVals (ZMod p) 𝕂′ :=
  ComplJ8Enc.cellRowsBE δ (encR δ χ) (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0)

/-- **The cell table's validity and fingerprint-export terminals.** -/
def cvT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range D.cells.length, vTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (cRows δ D χ k))
def cxT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range D.cells.length, xTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (cRows δ D χ k))

/-- The honest cell column function at the coin. -/
abbrev cCol (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → Fin D.cells.length → ZMod p :=
  cellCol δ b (ComplJ8Enc.valsBE δ (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0))

/-- The cell publics before the handle export (`0..3`; the `keyHK` denominators do not read the publics). -/
def pubsC0 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 2 then pub2 δ (cvT δ D χ) i else if i < 4 then pub2 δ (cxT δ D χ) i else 0

/-- **The cell handle-export terminal** `Σ_j mh_j / dNW_j`. -/
def chT (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range D.cells.length, liftQ δ (CellTraceH.mN (fun i : Fin D.cells.length => (mhF D i : ZMod p)) j) *
    (HonestKW.dNW δ b hC (powN o _) o (chalsMJ8 δ χ) (pubsC0 δ D χ) (cCol δ b D χ)
      (fun i : Fin D.cells.length => (mhF D i : ZMod p)) (ComplJ8Cell.kbLB (bigOf D) D.cells)
      (ComplJ8Cell.kbRB (bigOf D) D.cells) j)⁻¹

/-- **The cell table's publics**: `0/1` validity, `2/3` fingerprint export, `4/5` (`pubHQ`) handle export. -/
def pubsCOf (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 4 then pubsC0 δ D χ i else if i < 6 then pub2 δ (chT δ b D hC o χ) i else 0

/-- The honest J-8 walk rows at the coin (the 39th walk coins `chals 0`, `chals 1`). -/
abbrev wR (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → WalkVals (ZMod p) K 𝕂′ :=
  ComplJ8Enc.wRowsBE δ (chalsMJ8 δ χ) (encR δ χ) D.cells D.reads

/-- The J-8 walk's fingerprint-import and path-provide terminals. -/
def wxT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (walkRows D.cells D.reads).length, (walkFillInv δ (γV δ χ) (ρV δ χ) (wR δ D χ k)).xInv
def wpT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (walkRows D.cells D.reads).length, wpTermV δ (walkFillInv δ (γV δ χ) (ρV δ χ) (wR δ D χ k))

/-- The J-8 walk publics before the handle balances (`0..3`). -/
def pubsW0 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 2 then pub2 δ (wxT δ D χ) i else if i < 4 then pub2 δ (wpT δ D χ) i else 0

/-- The honest J-8 walk's 132-column function at the coin. -/
abbrev wCol (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ℕ → Fin (walkRows D.cells D.reads).length → ZMod p :=
  ComplJ8Enc.wColBE δ b (chalsMJ8 δ χ) (encR δ χ) (γV δ χ) (ρV δ χ) D.cells D.reads

/-- The walk row's node. -/
abbrev wNode (D : J8Data p Rg fuel s f r) (i : ℕ) : Noun := (wTrie D.cells D.reads i).label.node

/-- The child handle columns of the walk rows (kind, value of the left / right child of the row's node). -/
def kLW (D : J8Data p Rg fuel s f r) : Fin (walkRows D.cells D.reads).length → ZMod p :=
  fun i => ((D.H (VclL.hdN (wNode D i))).1 : ZMod p)
def vLW (D : J8Data p Rg fuel s f r) : Fin (walkRows D.cells D.reads).length → ZMod p :=
  fun i => ((D.H (VclL.hdN (wNode D i))).2 : ZMod p)
def kRW (D : J8Data p Rg fuel s f r) : Fin (walkRows D.cells D.reads).length → ZMod p :=
  fun i => ((D.H (VclL.tlN (wNode D i))).1 : ZMod p)
def vRW (D : J8Data p Rg fuel s f r) : Fin (walkRows D.cells D.reads).length → ZMod p :=
  fun i => ((D.H (VclL.tlN (wNode D i))).2 : ZMod p)

/-- A walk-twin denominator at the coin (`xKeyH`, `recLH`, `recRH`). -/
abbrev wdN (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K)
    (l : List (CoeffExpr (ZMod p))) (j : ℕ) : 𝕂′ :=
  WalkTraceHQ.dN δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ)
    (pubsW0 δ D χ) (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) l j

/-- The walk's handle-import and handle-provide terminals. -/
def whX (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (walkRows D.cells D.reads).length, (wdN δ b D o χ WalkHC.xKeyH j)⁻¹
def whP (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (walkRows D.cells D.reads).length,
    (liftQ δ (WalkTraceH.cN j (wCol δ b D χ WChip.mL)) * (wdN δ b D o χ WalkHC.recLH j)⁻¹ +
      liftQ δ (WalkTraceH.cN j (wCol δ b D χ WChip.mR)) * (wdN δ b D o χ WalkHC.recRH j)⁻¹)

/-- **The J-8 walk's publics**: `0/1` fingerprint import, `2/3` path provide, `4/5` handle import, `6/7` handle
provide. -/
def pubsWOf (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    ℕ → K := fun i =>
  if i < 4 then pubsW0 δ D χ i else if i < 6 then pub2 δ (whX δ b D o χ) i
  else if i < 8 then pub2 δ (whP δ b D o χ) i else 0

/-- **The J chip's publics**: `0/1` the J terminal `Σ termJ`, `2/3` the J export `Σ sX`. -/
def pubsJOf (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 2 then pub2 δ (∑ k, Nock.Jet.ChipJ8T.HonestRAP.termJ δ (chalsJJ8 χ) (D.jrows.get k)) i
  else if i < 4 then pub2 δ (∑ k, Nock.Jet.ChipJ8T.HonestRAP.sX δ (chalsJJ8 χ) (D.jrows.get k)) i else 0

end HonestE

/-! ## 3. `honestJ8Of` -/

section Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The atom table and atom walk parts. -/
structure AVPart (p : ℕ) [Fact p.Prime] (K : Type) [Field K] where
  trA : Coins frameJ8 K → Fin 349 → (ZMod p)[X]
  trV : Coins frameJ8 K → Fin 166 → (ZMod p)[X]
  pubsA : Coins frameJ8 K → ℕ → K
  pubsV : Coins frameJ8 K → ℕ → K

/-- The free fields of the row parameters (not read by completeness). -/
def extraRows : FrameJ8.RowsJ8 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)
  (AV : AVPart p K)

/-- **The honest traces of the run at a coin.** -/
def trOf (χ : Coins frameJ8 K) : TrJ8 (ZMod p) where
  C := ComplJ8Comp.trCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ (PbOf D hF hC hA).nodes
  M := ComplJ8Enc.cellTrME δ b hC (powN (orbJ8 D hF) _) (orbJ8 D hF) (chalsMJ8 δ)
    (pubsCOf δ b D hC (orbJ8 D hF)) (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0) (mhF D) χ
  W := ComplJ8Enc.walkTrWE δ b (walk_pos D.cells D.reads) (powN (orbJ8 D hF) _) (orbJ8 D hF) (chalsMJ8 δ)
    (pubsWOf δ b D (orbJ8 D hF)) (γV δ) (ρV δ) (encR δ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D) χ
  J := ComplJ8Jet.trJ δ b (powN (orbJ8 D hF) _) (chalsJJ8 χ) D.jrows.get
  A := AV.trA χ
  V := AV.trV χ

/-- **The honest message of the run at a coin.** -/
def msgOf (χ : Coins frameJ8 K) : MsgJ8' p K δ where
  m := ComplJ8Comp.mCOf D.H (cJ s f r)
  ρ := ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  ρS := ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  pubsC := pubsCOf δ b D hC (orbJ8 D hF) χ
  pubsW := pubsWOf δ b D (orbJ8 D hF) χ
  pubsJ := pubsJOf δ D χ
  pubsA := AV.pubsA χ
  pubsV := AV.pubsV χ

/-- **`honestJ8Of`**: the `HonestJ8` record of the run, with the bad list `badList [(χ₁₃, |W|)] fams`. -/
def honestJ8Of (fams : List (List (BadSpec K))) : HonestJ8 p K δ Rg fuel s f r where
  t := D.t
  hgen := D.hgen
  H := D.H
  pd := D.pd
  Pb := PbOf D hF hC hA
  M := msgOf δ b D hF hC AV
  tr := trOf δ b D hF hC hA AV
  rows := ComplJ8Comp.canonRows (PbOf D hF hC hA) extraRows
  g := ComplJ8Comp.canonG (PbOf D hF hC hA)
  bad := badOf (badList [(⟨13, by decide⟩, (bfsForest [D.t]).length)] fams)

end Of

/-! ## 3b. The honest atom table and atom walk of the run (the concrete `AVPart`) -/

section AtomPart
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.V1J8.Gen (idxOf hdN' tlN')
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom table's fingerprint seed: the limb coin `y = (χ_{Y1}, χ_{Y2})` (leaves `2 / 3` of `chalsAJ8Z`). -/
abbrev zA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (ChalsAZJ8.chalsAJ8Z δ χ 2) (ChalsAZJ8.chalsAJ8Z δ χ 3)

/-- The atom cells' validity multiplicity: the number of child references into the atom cell list, a left child at
`idxOf`, a right child at the ONE pointer `ComplJ8Data.ptrP p acs rows` (J-9 B variant 4; = `idxOf` without a
duplicate of `comb p`, `ComplJ8Data.ptrP_eq_idxOf`). -/
def mvA (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j =>
  (D.acs.filter fun y => (hdN' y).isCell && idxOf D.acs (hdN' y) == j).length +
    (D.acs.filter fun y => (tlN' y).isCell && ComplJ8Data.ptrP p D.acs D.rows y == j).length

abbrev mxAF (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j => D.mxA.getD j 0
/-- The atom cell part's handle multiplicity, as the generator's `atomGen` (`mh = mhA + mhx`): the atom-walk rows
plus the inc consumers of the row (`incChain` bumps `mhx` at the old row). -/
abbrev mhAF (D : J8Data p Rg fuel s f r) : ℕ → ℕ := fun j =>
  D.mhA.getD j 0 + (D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx

/-- The atom table's ONE right-child pointer (J-9 B variant 4): `ComplJ8Data.ptrP p acs rows`. -/
abbrev ptA (D : J8Data p Rg fuel s f r) : Noun → ℕ := ComplJ8Data.ptrP p D.acs D.rows

/-- The honest atom cell rows at the coin (no big children; right child at the pointer `ptA`). -/
abbrev aRows (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → CellVals (ZMod p) 𝕂′ :=
  ComplJ8Cell.cellRowsBP δ (zA δ χ) (fun _ => none) D.acs (mvA D) (mxAF D) (fun _ => 0) (ptA D)

/-- The honest atom cell base columns at the coin. -/
abbrev aCol (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → Fin D.acs.length → ZMod p :=
  cellCol δ b (ComplJ8Cell.valsBP δ (γV δ χ) (ρV δ χ) (zA δ χ) (fun _ => none) D.acs (mvA D) (mxAF D) (fun _ => 0)
    (ptA D))

abbrev mhvA (D : J8Data p Rg fuel s f r) : Fin D.acs.length → ZMod p := fun i => (mhAF D i : ZMod p)

def avT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range D.acs.length, vTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (aRows δ D χ k))
def axT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range D.acs.length, xTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (aRows δ D χ k))

/-- The atom publics `0..3` (cell part validity and fingerprint export). -/
def pubsA0 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 2 then pub2 δ (avT δ D χ) i else if i < 4 then pub2 δ (axT δ D χ) i else 0

/-- The atom cell part's handle-export terminal. -/
def ahT (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
    (CellTraceHQ.dN δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsA0 δ D χ) (aCol δ b D χ) (mhvA D) j)⁻¹

/-- The atom publics `0..5`. -/
def pubsA1 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 4 then pubsA0 δ D χ i else if i < 6 then pub2 δ (ahT δ b D hA o χ) i else 0

/-- The 238-column cell part of the atom table at publics `pubs`. -/
abbrev colAH (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (pubs : ℕ → K) : ℕ → Fin D.acs.length → ZMod p :=
  CellTraceHQ.colHQ δ b (aCol δ b D χ) (mhvA D)
    (CellTraceHQ.ivF δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D))
    (CellTraceHQ.avF δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D))

/-- The atom table's added columns `130 .. 204` (the generator's atom rows, L3). -/
abbrev newBA (D : J8Data p Rg fuel s f r) : ℕ → Fin D.acs.length → ZMod p :=
  ComplJ8Atom.newOf (n := D.acs.length) (ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row

/-- An atom-table terminal `Σ_j c_j / d_j` (column `c`, denominator `d`). -/
def aTerm (D : J8Data p Rg fuel s f r) (c : ℕ) (d : Fin D.acs.length → 𝕂′) : 𝕂′ :=
  ∑ j ∈ Finset.range D.acs.length, liftQ δ (HonestA8.cNat j (newBA D c)) * (HonestA8.dNat δ d j)⁻¹

/-- **The atom table's publics**: `0/1` validity, `2/3` export, `4/5` handle export, `6/7` `mb`, `8/9` `mi`,
`10/11` `inc` terminals. -/
def pubsAOf (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  let ch := ChalsAZJ8.chalsAJ8Z δ χ
  let P1 := pubsA1 δ b D hA o χ
  let col := colAH δ b D hA o χ P1
  if i < 6 then P1 i
  else if i < 8 then pub2 δ (aTerm δ D AtomChipHQ.mb (HonestA8.dMB δ b hA (powN o _) o ch P1 col (newBA D))) i
  else if i < 10 then pub2 δ (aTerm δ D AtomChipHQ.mi (HonestA8.dMI δ b hA (powN o _) o ch P1 col (newBA D))) i
  else if i < 12 then pub2 δ (aTerm δ D AtomChipHQ.inc (HonestA8.dC δ b hA (powN o _) o ch P1 col (newBA D))) i
  else 0

/-- **The honest atom-table trace at the coin.** -/
def trAOf (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : Fin 349 → (ZMod p)[X] :=
  HonestA8.atomTraceHQ δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
    (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)

/-! ### The atom walk (present iff `preads ≠ []`) -/

/-- The honest atom-walk rows at the coin. -/
abbrev vR (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → WalkVals (ZMod p) K 𝕂′ :=
  ComplJ8Walk.wRowsB δ (ChalsAZJ8.chalsAJ8Z δ χ) (zA δ χ) D.acs D.preads

def vxT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (nVOf D), (walkFillInv δ (γV δ χ) (ρV δ χ) (vR δ D χ k)).xInv
def vpT (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (nVOf D), wpTermV δ (walkFillInv δ (γV δ χ) (ρV δ χ) (vR δ D χ k))

def pubsV0 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if D.preads = [] then 0 else if i < 2 then pub2 δ (vxT δ D χ) i else if i < 4 then pub2 δ (vpT δ D χ) i else 0

abbrev vCol (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → Fin (nVOf D) → ZMod p :=
  ComplJ8Walk.wColB δ b (ChalsAZJ8.chalsAJ8Z δ χ) (zA δ χ) (γV δ χ) (ρV δ χ) D.acs D.preads

abbrev vNode (D : J8Data p Rg fuel s f r) (i : ℕ) : Noun := (wTrie D.acs D.preads i).label.node

def kLV (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((D.H (VclL.hdN (vNode D i))).1 : ZMod p)
def vLV (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((D.H (VclL.hdN (vNode D i))).2 : ZMod p)
def kRV (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((D.H (VclL.tlN (vNode D i))).1 : ZMod p)
def vRV (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((D.H (VclL.tlN (vNode D i))).2 : ZMod p)

abbrev vdN (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K)
    (l : List (CoeffExpr (ZMod p))) (j : ℕ) : 𝕂′ :=
  WalkTraceHQ.dN δ (krVOf D) b (nV_pos D) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsV0 δ D χ) (vCol δ b D χ)
    (kLV D) (vLV D) (kRV D) (vRV D) l j

def vhX (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (nVOf D), (vdN δ b D o χ WalkHC.xKeyH j)⁻¹
def vhP (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (nVOf D),
    (liftQ δ (WalkTraceH.cN j (vCol δ b D χ WChip.mL)) * (vdN δ b D o χ WalkHC.recLH j)⁻¹ +
      liftQ δ (WalkTraceH.cN j (vCol δ b D χ WChip.mR)) * (vdN δ b D o χ WalkHC.recRH j)⁻¹)

/-- **The atom walk's publics** (all `0` when absent). -/
def pubsVOf (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    ℕ → K := fun i =>
  if D.preads = [] then 0 else
  if i < 4 then pubsV0 δ D χ i else if i < 6 then pub2 δ (vhX δ b D o χ) i
  else if i < 8 then pub2 δ (vhP δ b D o χ) i else 0

/-- **The honest atom-walk trace at the coin.** -/
def trVOf (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    Fin 166 → (ZMod p)[X] := fun j =>
  WalkTraceHQ.walkTraceHQ δ (krVOf D) b (nV_pos D) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsVOf δ b D o χ)
    (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) (Fin.cast (WalkTraceHQ.walkTemplateHQ_width δ (krVOf D)).symm j)

/-- **The concrete atom part of the run.** -/
def avOf (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) : AVPart p K where
  trA := trAOf δ b D hA (orbJ8 D hF)
  trV := trVOf δ b D (orbJ8 D hF)
  pubsA := pubsAOf δ b D hA (orbJ8 D hF)
  pubsV := pubsVOf δ b D (orbJ8 D hF)

theorem zA_round0 (χ χ' : Coins frameJ8 K) (h : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) :
    zA δ χ = zA δ χ' := by
  simp only [zA]
  rw [ChalsAZJ8.chalsAJ8Z_y, ChalsAZJ8.chalsAJ8Z_y, h cY1 frameJ8_y_round0.1, h cY2 frameJ8_y_round0.2.1]

theorem aCol_cong (D : J8Data p Rg fuel s f r) (χ χ' : Coins frameJ8 K) (k : ℕ) (hk : k < 183)
    (hz : 129 ≤ k → zA δ χ = zA δ χ') : aCol δ b D χ k = aCol δ b D χ' k := by
  funext i
  exact cellCol_round1 b _ _ _ _ _ _ k
    (fun i k => by
      simp only [ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, CellVals.base, cellRow0])
    (fun h1 _ _ _ => by rw [hz h1]) i hk

/-- **The honest atom-table trace is staged** (`StJ8`'s `A`). -/
theorem stA_run (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) :
    StagedCols frameJ8 TraceJ8.crA (fun χ => (avOf δ b D hF hA (K := K)).trA χ) :=
  ComplJ8AW.stA_gen δ b hA _ _ (fun χ => ChalsAZJ8.chalsAJ8Z δ χ) (fun χ => pubsAOf δ b D hA (orbJ8 D hF) χ)
    (fun χ => colAH δ b D hA (orbJ8 D hF) χ (pubsAOf δ b D hA (orbJ8 D hF) χ)) (newBA D)
    (fun χ χ' k hk => InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k (by omega)
      (fun h => aCol_cong δ b D χ χ' k (by omega) (fun h' => absurd h' (by omega)))
      (fun h => absurd h (by omega)))
    (fun χ χ' hχ k hk => InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k hk
      (fun h => aCol_cong δ b D χ χ' k (by omega) (fun h' => absurd h' (by omega)))
      (fun h => aCol_cong δ b D χ χ' (k - 1) (by omega) (fun _ => zA_round0 δ χ χ' hχ)))

/-- **The honest atom-walk trace is staged** (`StJ8`'s `V`). -/
theorem stV_run (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) :
    StagedCols frameJ8 TraceJ8.crW (fun χ => (avOf δ b D hF hA (K := K)).trV χ) :=
  ComplJ8AW.stV_gen δ b (krVOf D) (nV_pos D) _ (orbJ8 D hF) (fun χ => ChalsAZJ8.chalsAJ8Z δ χ)
    (fun χ => pubsVOf δ b D (orbJ8 D hF) χ) (fun χ => vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D)
    (fun χ χ' k hk => ComplJ8Walk.wColB_cong δ b _ _ _ _ _ _ _ _ D.acs D.preads k (by omega)
      (fun h => absurd h (by omega)))
    (fun χ χ' hχ k hk => ComplJ8Walk.wColB_cong δ b _ _ _ _ _ _ _ _ D.acs D.preads k hk
      (fun _ => zA_round0 δ χ χ' hχ))

end AtomPart

/-! ## 4b. The cell table's validity pole family -/

section CellPoles
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The validity coins' pole-free parts read only `χ₂ χ₃ χ₄ χ₆`. -/
theorem readsOff_c5 (D : J8Data p Rg fuel s f r) (g : 𝕂′ → 𝕂′ → 𝕂′) :
    ReadsOff WeightsJ8.c5 (fun χ : Coins frameJ8 K => g (γV δ χ) (zJ δ χ)) := by
  intro χ χ' h
  simp only [γV, zJ, h WeightsJ8.c2 (by decide), h WeightsJ8.c3 (by decide), h WeightsJ8.c4 (by decide),
    h WeightsJ8.c6 (by decide)]

/-- The five validity pole-free parts of cell row `j`. -/
def cellVx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (vKeyOf δ (cRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (lKeyOf δ (cRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (rKeyOf δ (cRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (xKeyOf δ (cRows δ D χ j) 0),
   fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (xKeyOf δ (cRows δ D χ j) 1)]

/-- **The cell validity pole family** (and `χ₂ ≠ 0`, so the seed `z′ ≠ 0`). -/
def famCellV (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  ComplJ8Bad.zeroEv WeightsJ8.c2 ::
    (List.range D.cells.length).flatMap fun j => (cellVx δ D j).map (quadPole δ WeightsJ8.c5)

theorem famCellV_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famCellV δ D (K := K), e.OK := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ComplJ8Bad.zeroEv_OK _
  obtain ⟨j, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  simp only [cellVx, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · intro χ χ' h
    simp only [γV, zJ, cRows, encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide))
      (h FrameJ8.cY1 (by decide)) (h FrameJ8.cY2 (by decide)), h WeightsJ8.c2 (by decide), h WeightsJ8.c3 (by decide), h WeightsJ8.c4 (by decide),
      h WeightsJ8.c6 (by decide)]

theorem famCellV_good (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hg : ∀ e ∈ famCellV δ D (K := K), χ ∉ e.ev) :
    zJ δ χ ≠ 0 ∧ ∀ j < D.cells.length,
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (vKeyOf δ (cRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (lKeyOf δ (cRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (rKeyOf δ (cRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (cRows δ D χ j) 0) ≠ 0 ∧
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (cRows δ D χ j) 1) ≠ 0 := by
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 := hg _ List.mem_cons_self
    simp only [ComplJ8Bad.zeroEv, BadSpec.ev, Finset.mem_filter, Finset.mem_univ, true_and] at h0
    intro hz
    exact h0 ((Quad.mk_eq_zero_iff _ _ _).mp hz).1
  · have hx : ∀ x ∈ cellVx δ D j (K := K), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7) + x χ ≠ 0 := by
      intro x hx
      refine ComplJ8Bad.quadPole_ne_mk δ _ x χ _ (hg _ (List.mem_cons_of_mem _ ?_))
      exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
    simp only [cellVx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [InhabJ8Good.compress_split]; exact h1
    · rw [InhabJ8Good.compress_split]; exact h2
    · rw [InhabJ8Good.compress_split]; exact h3
    · rw [InhabJ8Good.compress_split]; exact h4
    · rw [InhabJ8Good.compress_split]; exact h5

variable (b : Basis (Fin 3) (ZMod p) K)

/-- The coin-free environment of cell row `i` (chals and publics `0`; the keys read only its trace). -/
abbrev cEW (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (i : Fin D.cells.length) : Nock.Reified.Env (ZMod p) :=
  HonestKW.EW δ b hC (powN o _) o (fun _ => (0 : K)) (fun _ => (0 : K)) (cCol δ b D χ)
    (fun i : Fin D.cells.length => (mhF D i : ZMod p)) (ComplJ8Cell.kbLB (bigOf D) D.cells)
    (ComplJ8Cell.kbRB (bigOf D) D.cells) (fun _ => 0) (fun _ => 0) i

/-- The pole-free part of cell row `j`'s handle denominator. -/
def cellHx (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (j : ℕ) (χ : Coins frameJ8 K) : 𝕂′ :=
  if hj : j < D.cells.length then
    FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
      (BalanceQ.liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 (TwoProviderQ.keyHK (F := ZMod p)) (cEW δ b D hC o χ ⟨j, hj⟩)))
  else 0

/-- **The cell handle pole family.** -/
def famCellH (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) :
    List (BadSpec K) :=
  (List.range D.cells.length).map fun j => quadPole δ InhabJ8Good.c12 (cellHx δ b D hC o j)

theorem keyHK_env (e e' : Nock.Reified.Env (ZMod p)) (ht : e.trace = e'.trace) (hn : e.traceNext = e'.traceNext) :
    ServeH.keyVec5 (K := K) (TwoProviderQ.keyHK (F := ZMod p)) e = ServeH.keyVec5 (TwoProviderQ.keyHK (F := ZMod p)) e' := by
  funext c
  simp only [ServeH.keyVec5]
  congr 1
  have hm : TwoProviderQ.keyHK.getD c (.const 0) ∈ (TwoProviderQ.keyHK (F := ZMod p)) := by
    fin_cases c <;> simp [TwoProviderQ.keyHK]
  exact colsBelow_eval (HonestKW.keyHK_below134 _ hm) (fun j _ => by rw [ht]) (fun j _ => by rw [hn])

theorem famCellH_OK (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) : ∀ e ∈ famCellH δ b D hC o (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ fun χ χ' hχ => ?_
  have hγ : ComplJ8Bad.γH δ χ = ComplJ8Bad.γH δ χ' := ComplJ8Bad.γH_readsOff δ χ χ' hχ
  have hcol : cCol δ b D χ = cCol δ b D χ' := by
    simp only [cCol, γV, ρV, zJ, encR_congr δ χ χ' (hχ WeightsJ8.c2 (by decide)) (hχ WeightsJ8.c3 (by decide))
      (hχ FrameJ8.cY1 (by decide)) (hχ FrameJ8.cY2 (by decide)), hχ WeightsJ8.c2 (by decide), hχ WeightsJ8.c3 (by decide),
      hχ WeightsJ8.c4 (by decide), hχ WeightsJ8.c5 (by decide), hχ WeightsJ8.c6 (by decide),
      hχ WeightsJ8.c7 (by decide)]
  unfold cellHx cEW
  rw [hγ, hcol]

theorem chals_33 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 33 = χ ⟨11, by decide⟩ := by
  rw [ProbJ8.chalsMJ8_lo δ χ 33 (by norm_num)]
  exact FrameVS.chalsVS_hGam δ _
theorem chals_34 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 34 = χ ⟨12, by decide⟩ := by
  rw [ProbJ8.chalsMJ8_lo δ χ 34 (by norm_num)]
  exact FrameVS.chalsVS_hRho δ _
theorem chals_35 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 35 = χ ⟨15, by decide⟩ := by
  simp [chalsMJ8, FrameVSQ.chalsVSQ, toVSQ, FrameVSQ.cGamHi]
theorem chals_36 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 36 = χ ⟨16, by decide⟩ := by
  simp [chalsMJ8, FrameVSQ.chalsVSQ, toVSQ, FrameVSQ.cRhoHi]

/-- The `𝕂′` handle coins of any env carrying the cell chip's challenges. -/
theorem coinsQ_cell (χ : Coins frameJ8 K) (e : Nock.Reified.Env (ZMod p))
    (hc : e.chal = slotVal b 134 (chalsMJ8 δ χ)) :
    TeleHQ.coinsQ δ (gatherEnv b ((HonestKW.cellTemplateHQKW δ).col0 3) e) =
      (⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) := by
  simp only [TeleHQ.coinsQ, HonestKW.gatherW_chal δ b (chalsMJ8 δ χ) e hc, chals_33, chals_34, chals_35,
    chals_36, ComplJ8Bad.γH, ComplJ8Bad.ρH]

/-- **The cell handle denominator splits** as `ρH + (pole-free part)`, at any publics. -/
theorem dRowW_split (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.cells.length) :
    HonestKW.dRowW δ b hC (powN o _) o (chalsMJ8 δ χ) pubs (cCol δ b D χ)
      (fun i : Fin D.cells.length => (mhF D i : ZMod p)) (ComplJ8Cell.kbLB (bigOf D) D.cells)
      (ComplJ8Cell.kbRB (bigOf D) D.cells) i = ComplJ8Bad.ρH δ χ + cellHx δ b D hC o i χ := by
  unfold HonestKW.dRowW
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl, InhabJ8Good.compress_split, coinsQ_cell δ b χ _ rfl]
  simp only [cellHx, dif_pos i.isLt]
  exact congrArg (fun v => ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
    (BalanceQ.liftRec (K := K) (L := 𝕂′) v)) (keyHK_env _ _ rfl rfl)

theorem chals_0 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 0 = χ ⟨0, by decide⟩ := InhabJ8Good.chalsMJ8_zero δ χ
theorem chals_1 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 1 = χ ⟨1, by decide⟩ := by
  rw [ProbJ8.chalsMJ8_lo δ χ 1 (by norm_num)]
  simp [FrameVS.chalsVS, chalsVCL, FrameVS.toVCL, FrameVSQ.toVS, toVSQ, CellH.hGam, CellH.hRho]

/-- The honest J-8 walk rows with the walk coins read as coordinates `χ₀ χ₁`. -/
abbrev wRow (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → WalkVals (ZMod p) K 𝕂′ :=
  ComplJ8Enc.walkRow0E δ (encR δ χ) D.cells D.reads (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩)

theorem wR_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : wR δ D χ = wRow δ D χ := by
  simp only [wR, ComplJ8Enc.wRowsBE, chals_0, chals_1]

/-- The three walk validity pole-free parts of walk row `j`. -/
def walkVx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (wxKeyV δ (wRow δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecLV δ (wRow δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecRV δ (wRow δ D χ j))]

/-- **The J-8 walk validity pole family.** -/
def famWalkV (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (walkRows D.cells D.reads).length).flatMap fun j => (walkVx δ D j).map (quadPole δ WeightsJ8.c5)

theorem famWalkV_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famWalkV δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  simp only [walkVx, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    simp only [γV, zJ, wRow, encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide))
      (h FrameJ8.cY1 (by decide)) (h FrameJ8.cY2 (by decide)), h WeightsJ8.c2 (by decide), h WeightsJ8.c3 (by decide), h WeightsJ8.c4 (by decide),
      h WeightsJ8.c6 (by decide), h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem famWalkV_good (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hg : ∀ e ∈ famWalkV δ D (K := K), χ ∉ e.ev) : ∀ j < (walkRows D.cells D.reads).length,
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wR δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (wR δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (wR δ D χ j)) ≠ 0 := by
  intro j hj
  have hx : ∀ x ∈ walkVx δ D j (K := K), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7) + x χ ≠ 0 := by
    intro x hx
    refine ComplJ8Bad.quadPole_ne_mk δ _ x χ _ (hg _ ?_)
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  simp only [walkVx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [wR_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [InhabJ8Good.compress_split]; exact h1
  · rw [InhabJ8Good.compress_split]; exact h2
  · rw [InhabJ8Good.compress_split]; exact h3

/-- The honest walk values with coordinate coins. -/
abbrev wValsC (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    Fin (walkRows D.cells D.reads).length → WalkVals (ZMod p) K 𝕂′ :=
  fun i => walkFill δ (γV δ χ) (ρV δ χ) (wRow δ D χ) i

/-- The three walk handle pole-free parts of walk row `j` (`recDen` / `recDenP` at `ρ = 0`). -/
def walkHx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → 𝕂′) :=
  if hj : j < (walkRows D.cells D.reads).length then
    [fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ ⟨j, hj⟩).idx, (kLW D ⟨j, hj⟩, vLW D ⟨j, hj⟩),
        (kRW D ⟨j, hj⟩, vRW D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ ⟨j, hj⟩).ridx, 2 * (wValsC δ D χ ⟨j, hj⟩).pre,
        (kLW D ⟨j, hj⟩, vLW D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ ⟨j, hj⟩).ridx, 2 * (wValsC δ D χ ⟨j, hj⟩).pre + 1,
        (kRW D ⟨j, hj⟩, vRW D ⟨j, hj⟩))]
  else []

/-- **The J-8 walk handle pole family.** -/
def famWalkH (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (walkRows D.cells D.reads).length).flatMap fun j => (walkHx δ D j).map (quadPole δ InhabJ8Good.c12)

theorem famWalkH_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famWalkH δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  have hj' := List.mem_range.mp hj
  simp only [walkHx, dif_pos hj', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    have hγ : ComplJ8Bad.γH δ χ = ComplJ8Bad.γH δ χ' := ComplJ8Bad.γH_readsOff δ χ χ' h
    simp only [hγ, wValsC, γV, ρV, zJ, wRow, encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide))
      (h FrameJ8.cY1 (by decide)) (h FrameJ8.cY2 (by decide)), h WeightsJ8.c2 (by decide), h WeightsJ8.c3 (by decide),
      h WeightsJ8.c4 (by decide), h WeightsJ8.c5 (by decide), h WeightsJ8.c6 (by decide),
      h WeightsJ8.c7 (by decide), h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem recDen_split (ρ γ : 𝕂′) (k : ZMod p × (ZMod p × ZMod p) × (ZMod p × ZMod p)) :
    recDen ρ γ k = ρ + recDen 0 γ k := by unfold recDen; ring
theorem recDenP_split (ρ γ : 𝕂′) (k : ZMod p × ZMod p × (ZMod p × ZMod p)) :
    recDenP ρ γ k = ρ + recDenP 0 γ k := by unfold recDenP; ring

theorem wVals_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ComplJ8Enc.wValsBE (n := (walkRows D.cells D.reads).length) δ (chalsMJ8 δ χ) (encR δ χ) (γV δ χ) (ρV δ χ)
      D.cells D.reads = wValsC δ D χ := by
  unfold ComplJ8Enc.wValsBE ComplJ8Enc.wRowsBE
  rw [chals_0, chals_1]

/-- **The three walk handle denominators split** as `ρH + (pole-free part)` at any publics. -/
theorem walk_dRow_split (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length)) (χ : Coins frameJ8 K) (pubs : ℕ → K)
    (i : Fin (walkRows D.cells D.reads).length) :
    WalkTraceHQ.dRow δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ) pubs
        WalkHC.xKeyH (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) i =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ i).idx, (kLW D i, vLW D i), (kRW D i, vRW D i)) ∧
    WalkTraceHQ.dRow δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ) pubs
        WalkHC.recLH (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ i).ridx, 2 * (wValsC δ D χ i).pre,
        (kLW D i, vLW D i)) ∧
    WalkTraceHQ.dRow δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ) pubs
        WalkHC.recRH (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ D χ i).ridx, 2 * (wValsC δ D χ i).pre + 1,
        (kRW D i, vRW D i)) := by
  obtain ⟨e1, e2, e3⟩ := FrameVSQ.walk_dRowQ_vals δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o
    (chalsMJ8 δ χ) pubs (ComplJ8Enc.wValsBE δ (chalsMJ8 δ χ) (encR δ χ) (γV δ χ) (ρV δ χ) D.cells D.reads)
    (kLW D) (vLW D) (kRW D) (vRW D) hinj i
  have hρ : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 34) (chalsMJ8 δ χ 36) = ComplJ8Bad.ρH δ χ := by
    rw [chals_34, chals_36]; rfl
  have hγ : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 33) (chalsMJ8 δ χ 35) = ComplJ8Bad.γH δ χ := by
    rw [chals_33, chals_35]; rfl
  rw [hρ, hγ, wVals_eq] at e1 e2 e3
  refine ⟨e1.trans (recDen_split δ _ _ _), e2.trans (recDenP_split δ _ _ _), e3.trans (recDenP_split δ _ _ _)⟩

end CellPoles

/-! ## 4. The obligations at the run -/

section Obl
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen

/-- The honest record of the run. -/
abbrev BOf (hF : DvdOK DD) (hC : 0 < (DD).cells.length) (hA : 0 < (DD).acs.length) (AV : AVPart p K)
    (fams : List (List (BadSpec K))) : HonestJ8 p K δ Rg fuel s f r :=
  honestJ8Of δ b DD hF hC hA AV fams

variable (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
  (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

theorem nodes_ok : Function.Injective (BOf δ b Rt hgen hF hC hA AV fams).Pb.nodes ∧
    ∀ (i : Fin (BOf δ b Rt hgen hF hC hA AV fams).Pb.n) (hi : (i : ℕ) + 1 < (BOf δ b Rt hgen hF hC hA AV fams).Pb.n),
      (BOf δ b Rt hgen hF hC hA AV fams).Pb.nodes ⟨(i : ℕ) + 1, hi⟩ =
        (BOf δ b Rt hgen hF hC hA AV fams).Pb.nodes i * (BOf δ b Rt hgen hF hC hA AV fams).Pb.orbit.ω :=
  powN_ok (orbJ8 _ hF) (le_two_pow_ht _ List.mem_cons_self)

theorem htrC_run (χ : Coins frameJ8 K) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    qX δ b B.Pb (B.tr χ) (chalVJ8 b χ) (pubJ δ b B χ) =
    VclL.HonestTraceX.polyX b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ)
      (VclL.HonestTraceX.lnW (αJ b χ)) (VclL.HonestTraceX.cntW B.W (αJ b χ))
      (VclL.HonestTraceX.accW (F := ZMod p) B.H B.W (αJ b χ) (γJ b χ)) B.Pb.nodes
      (computeChipVCLHX B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ) (pubJ δ b B χ) B.Pb.orbit).rap.w := rfl

theorem pubJ_eq (χ : Coins frameJ8 K) :
    pubJ δ b (BOf δ b Rt hgen hF hC hA AV fams) χ = ComplJ8CompRun.pubRun δ b Rt hgen χ := rfl

/-- **The compute group of the obligations** (L1, L3's `hpair`, L5's `goodC`) at the run, given the bad list
contains the compute pole family `compPoles`. -/
theorem compute_group (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hcl : ∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p)
    (hcomp : ComplJ8CompPole.compPoles (K := K) δ (DD).H (DD).pd (bfsForest [(DD).t])
      (bfsForest [(DD).t]).length ∈ fams) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    HonestCompX.HdlOK (ringChar (ZMod p)) B.H ∧
    (∀ u, InTree B.t u → HonestCompX.isPair B.H (rowOfSkelX u.label) →
      HonestCompX.PairOK (F := ZMod p) (B.pd (rowOfSkelX u.label))) ∧
    B.Pb.n = B.W.length ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubIC = αJ b χ) ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubSeed =
      VclL.HonestTraceX.curW (F := ZMod p) B.H B.W (γJ b χ) 1 * αJ b χ) ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubOut = 0) ∧
    (∀ χ, pubJ δ b B χ 0 = HonestCompX.hk B.H s ∧ pubJ δ b B χ 1 = HonestCompX.hv B.H s ∧
      pubJ δ b B χ 2 = HonestCompX.hk B.H f ∧ pubJ δ b B χ 3 = HonestCompX.hv B.H f ∧
      pubJ δ b B χ 4 = HonestCompX.hk B.H r ∧ pubJ δ b B χ 5 = HonestCompX.hv B.H r) ∧
    (∀ χ, ∀ a < 6, ∀ k : Fin 3, pubJ δ b B χ (VclL.HonestTraceX.pubOfA a + k) =
      coord b (VclL.HonestTraceX.accV b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) a B.Pb.n) k) ∧
    (∀ χ, B.Good χ → B.W.length ≤ orderOf (αJ b χ) ∧
      ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
        HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0 ∨
          HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0) := by
  intro B
  have hH := ComplJ8CompRun.hH_run Rt hgen (p := p)
  refine ⟨hH, ?_, rfl, fun χ => ComplJ8Comp.hpIC δ b _ _ _ _ χ, fun χ => ComplJ8CompRun.hpS_run δ b Rt hgen hcl χ,
    fun χ => ComplJ8Comp.hpO δ b _ _ _ _ χ, fun χ => ComplJ8CompRun.hpub_run δ b Rt hgen hcl χ,
    fun χ => ComplJ8CompRun.hρ_run δ b Rt hgen χ, ?_⟩
  · exact ComplJ8Atom.hpair_of_binders hgen hH hp63 _ hax hop5
  · refine ComplJ8Bad.goodC_of_cover δ b B _ rfl (List.mem_append_left _ (List.mem_singleton_self _)) ?_
    refine ComplJ8CompPole.denCovered_of_sub δ b B _ (fun e he => ?_) (bfs_pos _)
    exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hcomp, he⟩)

/-- **The staging obligation** (`StJ8`): compute (L1), cell and J-8 walk (L2; the seed `z′ = (χ₂, χ₃)` is a
round-0 coin), J, the atom table and atom walk (the parts' own staging). -/
theorem staged_run
    (hAst : StagedCols frameJ8 TraceJ8.crA (fun χ => AV.trA χ))
    (hVst : StagedCols frameJ8 TraceJ8.crW (fun χ => AV.trV χ)) :
    StJ8 (BOf δ b Rt hgen hF hC hA AV fams).tr := by
  have hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) →
      encR δ χ = encR δ χ' := fun χ χ' h =>
    encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide)) (h FrameJ8.cY1 (by decide))
      (h FrameJ8.cY2 (by decide))
  exact ⟨ComplJ8Comp.staged_trCOf δ b _ _ _,
    ComplJ8Enc.cellTrME_staged δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
    ComplJ8Enc.walkTrWE_staged δ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
    ComplJ8Jet.stJ δ b _ _ _ (fun χ => rfl), hAst, hVst⟩

/-- **Every table has `≤ 2^31` rows** (the row binder, over the run's six table sizes). -/
def Rows31 (D : J8Data p Rg fuel s f r) : Prop := ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31

theorem rowsLe31_of (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    RowsLe31 (BOf δ b Rt hgen hF hC hA AV fams).Pb := by
  refine ⟨h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_⟩ <;> simp [sizesJ8, BOf, honestJ8Of, PbOf]

theorem size_lt_p (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) {x : ℕ}
    (hx : x ∈ sizesJ8 (j8DataOf p Rg Rt hgen)) : x < p := by
  have := h31 x hx; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  omega

/-- **The node obligations of the cell table, the J-8 walk and the atom table.** -/
theorem nodes_group (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    (Function.Injective B.Pb.nodesC ∧
      (∀ (i : Fin B.Pb.nC) (hi : (i : ℕ) + 1 < B.Pb.nC),
        B.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesC i * B.Pb.orbitC.ω) ∧ B.Pb.nC < ringChar (ZMod p)) ∧
    (Function.Injective B.Pb.nodesW ∧
      (∀ (i : Fin B.Pb.nW) (hi : (i : ℕ) + 1 < B.Pb.nW),
        B.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesW i * B.Pb.orbitW.ω) ∧
      1 ≤ B.Pb.kroots ∧ B.Pb.kroots ≤ B.Pb.nW ∧ B.Pb.kroots + B.Pb.nW < ringChar (ZMod p)) ∧
    (Function.Injective B.Pb.nodesA ∧
      (∀ (i : Fin B.Pb.nA) (hi : (i : ℕ) + 1 < B.Pb.nA),
        B.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesA i * B.Pb.orbitA.ω) ∧ B.Pb.nA < p) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmC : (j8DataOf p Rg Rt hgen).cells.length ∈ sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  have hmW : (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length ∈
      sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  have hmA : (j8DataOf p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  obtain ⟨c1, c2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmC)
  obtain ⟨w1, w2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmW)
  obtain ⟨a1, a2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmA)
  have hWb := h31 _ hmW
  have hk := krW_le_rows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads
  have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  refine ⟨⟨c1, c2, ?_⟩, ⟨w1, w2, one_le_krW _ _, hk, ?_⟩, ⟨a1, a2, size_lt_p Rt hgen hp63 h31 hmA⟩⟩
  · rw [hrc]; exact size_lt_p Rt hgen hp63 h31 hmC
  · rw [hrc]; show krW _ _ + (walkRows _ _).length < p; omega

theorem regs_le (h31 : Rows31 (j8DataOf p Rg Rt hgen)) : (j8DataOf p Rg Rt hgen).regs.length ≤ 2 ^ 31 := by
  have h1 : (j8DataOf p Rg Rt hgen).regs.length ≤ (j8DataOf p Rg Rt hgen).calls.length := by
    show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).dedup.length ≤ _
    exact (List.dedup_sublist _).length_le.trans (by simp; rfl)
  have h2 : (j8DataOf p Rg Rt hgen).calls.length ≤ (bfsForest [(j8DataOf p Rg Rt hgen).t]).length := by
    show (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).length ≤ _
    unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
    exact (List.length_filterMap_le _ _).trans (by simp; rfl)
  exact h1.trans (h2.trans (h31 _ List.mem_cons_self))

/-- **The budget obligation.** -/
theorem budget_run (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    3 + B.Pb.regs.length + 2 * B.Pb.nC < p ∧ B.Pb.nA + B.Pb.nV < p ∧ B.Pb.nA ≤ 2 ^ 62 ∧
    RealIOJ8.BudJ8 B.Pb B.rows (B.g + B.rows.N) ∧
    (B.Pb.regs.length ≤ B.g ∧ B.Pb.nA ≤ B.rows.mb ∧ B.Pb.nA ≤ B.rows.A ∧ B.Pb.nV ≤ B.rows.AW) := by
  intro B
  obtain ⟨l1, l2, l3⟩ := ComplJ8Comp.budget_lengths hp63 B.Pb (rowsLe31_of δ b Rt hgen hF hC hA AV fams h31)
    (regs_le Rt hgen h31)
  obtain ⟨b1, b2, b3, b4, b5⟩ := ComplJ8Comp.budget_canon B.Pb extraRows
  refine ⟨l1, l2, l3, b1, ?_, b3, b4, b5⟩
  show B.Pb.regs.length ≤ ComplJ8Comp.canonG B.Pb
  simp only [ComplJ8Comp.canonG]; omega

theorem formula_cell_of_gen {Rg' : Nock.Jet.VerifiedRegistry} {fuel' : ℕ} {s' f' r' : Noun} {t' : NTree SkelX}
    (hgen' : genX Rg'.R fuel' s' f' = some (t', r')) : ∃ a c, f' = .cell a c := by
  obtain ⟨fu, h⟩ := genX_sound Rg'.faithful hgen'
  change Nock.evalN fu s' f' = some r' at h
  cases hf : f' with
  | atom k => rw [hf] at h; cases fu <;> simp [Nock.evalN] at h
  | cell a c => exact ⟨a, c, rfl⟩

/-- **The claim obligation**, from the claim binders: the claim's atoms are `< p` (`hclA`), the registered
formulas' leaves are `< p` (`hregLeaf`), and `hleaf` (every demand root, in particular the claim nouns and the
registered formulas, has `≤ 2^109` leaves). -/
theorem claim_run (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hregLeaf : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∀ v ∈ (Nock.Jet.Autogen.compile p (Rt id)).leafList, v < p)
    (χ : Coins frameJ8 K) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    (∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true →
      (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ AcceptsJ8P.censusG B.Pb (cJ s f r), x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    FrameVS.isCellN (cJ s f r).formula = true := by
  intro B
  have hroot : ∀ k : Fin 3, FrameVS.claimNoun (cJ s f r) k ∈ (j8DataOf p Rg Rt hgen).roots := by
    intro k
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    fin_cases k <;> simp [FrameVS.claimNoun, cJ]
  have hleafN : ∀ k : Fin 3, (FrameVS.claimNoun (cJ s f r) k).leaves ≤ 2 ^ 110 :=
    fun k => (hleaf _ (hroot k)).trans (by norm_num)
  have hser : ∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p := by
    intro k hk
    have hlt : (j8DataOf p Rg Rt hgen).cells.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
    have hne : (j8DataOf p Rg Rt hgen).cells ≠ [] := List.ne_nil_of_length_pos hC
    show ((j8DataOf p Rg Rt hgen).H (FrameVS.claimNoun (cJ s f r) k)).2 < p
    generalize FrameVS.claimNoun (cJ s f r) k = x at hk
    cases x with
    | atom v => simp [FrameVS.isCellN] at hk
    | cell a c =>
      exact lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hlt.le
  have hreg : ∀ id ∈ B.Pb.regs, (Nock.Jet.Autogen.compile p (B.Pb.Rt id)).leaves ≤ fuelChip ∧
      ∀ v ∈ (Nock.Jet.Autogen.compile p (B.Pb.Rt id)).leafList, v < p := by
    intro id hid
    refine ⟨(hleaf _ ?_).trans (by unfold fuelChip; norm_num), hregLeaf id hid⟩
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hcf : FrameVS.isCellN (cJ s f r).formula = true := by
    obtain ⟨a, c, hfc⟩ := formula_cell_of_gen hgen
    simp [cJ, hfc, FrameVS.isCellN]
  exact ComplJ8Comp.claim_J8_instance hp63 _ _ hclA hleafN hser B.Pb hreg hcf

/-- **The weight and figure obligations** for any family list of pinned events with `≤ 2^66` pins. -/
theorem bad_group (hOK : ∀ L ∈ fams, ∀ e ∈ L, e.OK) (hpin : ∀ L ∈ fams, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (hcnt : RowsLe31 (BOf δ b Rt hgen hF hC hA AV fams).Pb → (fams.map ComplJ8Bad.nPins).sum ≤ 2 ^ 66) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    (∀ e ∈ B.bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2) ∧
    (p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120) := by
  intro B
  refine ⟨ComplJ8Bad.wt_badOf _ (ComplJ8Bad.badList_OK _ fams hOK), ?_⟩
  refine ComplJ8Bad.fig_badList δ B _ fams rfl hpin hcnt (by simp) ?_
  intro hr o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact hr.1

/-- **The J chip's pole family** (L5's `jNoPole` events at the run's J keys). -/
def famJ (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  ComplJ8Bad.ioPoles δ InhabJ8Good.c12 (ComplJ8Bad.γH δ)
      ((ComplJ8Jet.jKeysT D.jrows.get).map fun κ => BalanceQ.liftRec (L := Quad (algebraMap (ZMod p) K δ))
        (Nock.Jet.RapJetJ8.keyK (K := K) 8 κ)) ++
    ComplJ8Bad.ioPoles δ InhabJ8Good.c12 (ComplJ8Bad.γH δ)
      ((ComplJ8Jet.jKeysX D.jrows.get).map fun κ => BalanceQ.liftRec (L := Quad (algebraMap (ZMod p) K δ))
        (Nock.Jet.RapJetJ8.keyK (K := K) 5 κ))

theorem pub2_mk (x : Quad (algebraMap (ZMod p) K δ)) : Quad.mk _ (pub2 δ x 0) (pub2 δ x 1) = x := by
  simp [pub2, Quad.mk_re_im]

/-- **The J chip obligation** at a good coin, given the J pole family is in the bad list. -/
theorem jOK_run (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hJ : famJ δ (j8DataOf p Rg Rt hgen) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (BOf δ b Rt hgen hF hC hA AV fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
      (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ) := by
  intro B
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (j8DataOf p Rg Rt hgen).jrows.length = 0
  · refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
    have hs : ∀ (g : Fin (j8DataOf p Rg Rt hgen).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
      intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
    have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
      (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
    have e : ∀ i, pubsJOf δ (j8DataOf p Rg Rt hgen) χ i = 0 := by
      intro i
      unfold pubsJOf
      rw [hs, hs]
      split_ifs <;> simp [pub2, hz.1, hz.2]
    exact ⟨e 0, e 1, e 2, e 3⟩
  · have hn : 0 < (j8DataOf p Rg Rt hgen).jrows.length := Nat.pos_of_ne_zero h0
    obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (j8DataOf p Rg Rt hgen).jrows.length)
      (le_two_pow_ht _ (by simp [sizesJ8]))
    have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams),
        χ ∉ e.1 := hχ
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (j8DataOf p Rg Rt hgen).jrows.get)
      (ComplJ8Jet.jKeysX (j8DataOf p Rg Rt hgen).jrows.get) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hJ, he⟩)))
    have := ComplJ8Jet.jOK_present_trJ δ b (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsJJ8 χ) (pubsJOf δ _ χ)
      (j8DataOf p Rg Rt hgen).jrows.get hinj hn hadj
      (fun i => ComplJ8Jet.jrows_gate_run Rt hgen hp hRt _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])
    exact this

theorem pub2_mk2 (x : Quad (algebraMap (ZMod p) K δ)) (i : ℕ) (hi : i % 2 = 0) :
    Quad.mk _ (pub2 δ x i) (pub2 δ x (i + 1)) = x := by
  have h1 : (i + 1) % 2 ≠ 0 := by omega
  simp [pub2, hi, h1, Quad.mk_re_im]

theorem dNW_pubs (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (j : ℕ) :
    HonestKW.dNW δ b hC (powN o _) o (chalsMJ8 δ χ) pubs (cCol δ b D χ)
      (fun i : Fin D.cells.length => (mhF D i : ZMod p)) (ComplJ8Cell.kbLB (bigOf D) D.cells)
      (ComplJ8Cell.kbRB (bigOf D) D.cells) j =
    HonestKW.dNW δ b hC (powN o _) o (chalsMJ8 δ χ) pubs' (cCol δ b D χ)
      (fun i : Fin D.cells.length => (mhF D i : ZMod p)) (ComplJ8Cell.kbLB (bigOf D) D.cells)
      (ComplJ8Cell.kbRB (bigOf D) D.cells) j := by
  unfold HonestKW.dNW
  split_ifs with hj
  · rw [dRowW_split, dRowW_split]
  · rfl

/-- **The cell table obligation** at a good coin, given the cell validity and handle pole families are in the
bad list. -/
theorem cellOK_run (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hV : famCellV δ (j8DataOf p Rg Rt hgen) ∈ fams)
    (hH : famCellH δ b (j8DataOf p Rg Rt hgen) hC (orbJ8 _ hF) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (BOf δ b Rt hgen hF hC hA AV fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  obtain ⟨hz, hrows⟩ := famCellV_good δ (j8DataOf p Rg Rt hgen) χ (hin _ hV)
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (j8DataOf p Rg Rt hgen).cells.length)
    (le_two_pow_ht _ (by simp [sizesJ8]))
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC (orbJ8 _ hF) χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hin _ hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 4) (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC (orbJ8 _ hF) χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC (orbJ8 _ hF) χ)]

theorem hdl_kind (cs acs : List Noun) (x : Noun) :
    ((ComplJ8Data.hdlP p cs acs x).1 : ZMod p) = 0 ∨ ((ComplJ8Data.hdlP p cs acs x).1 : ZMod p) = 1 ∨
      ((ComplJ8Data.hdlP p cs acs x).1 : ZMod p) = 2 := by
  cases x with
  | atom v => by_cases hv : v < p <;> simp [ComplJ8Data.hdlP, hv]
  | cell a c => simp [ComplJ8Data.hdlP]

theorem dN_pubs (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length)) (χ : Coins frameJ8 K)
    (pubs pubs' : ℕ → K) (l : List (CoeffExpr (ZMod p))) (hl : l = WalkHC.xKeyH ∨ l = WalkHC.recLH ∨ l = WalkHC.recRH)
    (j : ℕ) :
    WalkTraceHQ.dN δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ) pubs
      (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) l j =
    WalkTraceHQ.dN δ (krW D.cells D.reads) b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ χ) pubs'
      (wCol δ b D χ) (kLW D) (vLW D) (kRW D) (vRW D) l j := by
  unfold WalkTraceHQ.dN
  split_ifs with hj
  · have e := walk_dRow_split δ b D o hinj χ pubs ⟨j, hj⟩
    have e' := walk_dRow_split δ b D o hinj χ pubs' ⟨j, hj⟩
    rcases hl with rfl | rfl | rfl
    · rw [e.1, e'.1]
    · rw [e.2.1, e'.2.1]
    · rw [e.2.2, e'.2.2]
  · rfl

/-- **The J-8 walk obligation** at a good coin, given the walk validity and handle pole families are in the
bad list. -/
theorem walkOK_run (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hV : famWalkV δ (j8DataOf p Rg Rt hgen) ∈ fams) (hH : famWalkH δ (j8DataOf p Rg Rt hgen) ∈ fams)
    (χ : Coins frameJ8 K) (hχ : (BOf δ b Rt hgen hF hC hA AV fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hmW : (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length ∈
      sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmW)
  have hrows := famWalkV_good δ (j8DataOf p Rg Rt hgen) χ (hin _ hV)
  have hcl : (j8DataOf p Rg Rt hgen).cells.length < ringChar (ZMod p) := by
    rw [hrc]; exact size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hkp : krW (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads +
      (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length < ringChar (ZMod p) := by
    have := h31 _ hmW
    have := krW_le_rows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hpoleH : ∀ (i : Fin (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length),
      ∀ x ∈ walkHx δ (j8DataOf p Rg Rt hgen) i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hin _ hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) hinj χ
    (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN (orbJ8 _ hF) _) (orbJ8 _ hF)
    (chalsMJ8 δ χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
    (GeneratedField.primeFieldElems_zmod p) (by rw [hrc]; exact hp63) hcl hwalk hkp rfl hinj hadj
    (ProbJ8.chalsOK_J8 δ χ) (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.1)
    (fun j hj => (hrows j hj).2.2) (pub2_mk2 δ (wxT δ (j8DataOf p Rg Rt hgen) χ) 0 rfl).symm (pub2_mk2 δ (wpT δ (j8DataOf p Rg Rt hgen) χ) 2 rfl).symm
    (fun i => hdl_kind _ _ _) (fun i => hdl_kind _ _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).idx, (kLW _ i, vLW _ i),
        (kRW _ i, vRW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre,
        (kLW _ i, vLW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre + 1,
        (kRW _ i, vRW _ i))) (by
          simp only [walkHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ?_ ?_
  · exact hwalk'
  · show Quad.mk _ (pub2 δ (whX δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) 4) (pub2 δ (whX δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) 6) (pub2 δ (whP δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ hF) χ) _ (Or.inr (Or.inr rfl))]

end Obl


/-! ## 5. The called ids -/

section Called
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.V1J8.Gen (callsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK AxRowX)

/-- **Every call of the run is a called id** (`callsOf` reads exactly the `s11j` rows). -/
theorem calls_called {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) :
    ∀ cl ∈ callsOf (ComplJ8Data.rowsOfT t), cl.1 ∈ CalledIds t := by
  intro cl hcl
  unfold callsOf at hcl
  obtain ⟨row, hrow, hrc⟩ := List.mem_filterMap.1 hcl
  have hrow' : ∃ u ∈ bfsForest [t], rowOfSkelX u.label = row := by
    simpa [ComplJ8Data.rowsOfT] using hrow
  obtain ⟨u, hu, rfl⟩ := hrow'
  obtain ⟨c, hc, huc⟩ := (mem_bfsForest [t] u).1 hu
  have hct : c = t := by simpa using hc
  subst hct
  have hst : u.label.state = .s11j := by
    rw [← ComplJ8Jet.rowOfSkelX_st]
    by_contra hne
    simp [hne] at hrc
  obtain ⟨id, j, r', hRj, hftth, hsem⟩ := ComplJ8Jet.s11j_node hgen huc hst
  have hcl' : cl = (id, u.label.subject) := by
    rw [if_pos (by rw [ComplJ8Jet.rowOfSkelX_st]; exact hst)] at hrc
    rw [← Option.some.inj hrc, hftth, ComplJ8Jet.rowOfSkelX_s]
    rfl
  subst hcl'
  exact ⟨u, huc, by rw [ComplJ8Jet.rowOfSkelX_st]; exact hst, hftth⟩

/-- **Every call's id is an `s11j` row's jet atom** (so `hax` bounds it). -/
theorem calls_lt {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} {p : ℕ}
    (hgen : genX R fuel s f = some (t, r)) (hax : ProgAxOK p t) :
    ∀ cl ∈ callsOf (ComplJ8Data.rowsOfT t), cl.1 < p := by
  intro cl hcl
  obtain ⟨u, hu, hst, hft⟩ := calls_called hgen cl hcl
  have h := hax u hu
  unfold AxRowX at h
  rw [hst] at h
  exact h.2 _ hft

end Called

/-! ## 6. The static obligation -/

section Stat
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds HregC)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
  (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

theorem rk_ne (x : Noun) (hx : ∃ a c, x = .cell a c) : AcceptsJ8P.rkC x ≠ (0, 0) := by
  obtain ⟨a, c, rfl⟩ := hx
  simp only [AcceptsJ8P.rkC, Noun.internal, ne_eq, Prod.mk.injEq, not_and]
  intro h1 h2
  have := Nat.div_add_mod (1 + a.internal + c.internal) (2 ^ 62)
  omega

/-- **The static obligation** (`hlay hsmall huniq hTpl hnd hidx hrk hlt`) from the jet binder `hRt` (the witness
of `HregC`), `hax`, `hleaf` and the row binder. -/
theorem stat_run (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    let B := BOf δ b Rt hgen hF hC hA AV fams
    List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids ∧
    (∀ q ∈ layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ B.Pb.regs, Rg.R i = some ⟨(B.Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (B.Pb.Rt i)⟩ ∧
      axPosB (B.Pb.Rt i) = true ∧ (B.Pb.Rt i).WellTyped p) ∧
    B.Pb.regs.Nodup ∧ (∀ id ∈ B.Pb.regs, B.Pb.idx id < p) ∧ (∀ id ∈ B.Pb.regs, B.Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ B.Pb.regs, (B.Pb.rk id).1 < ringChar (ZMod p) ∧ (B.Pb.rk id).2 < ringChar (ZMod p) ∧
      B.Pb.idx id < ringChar (ZMod p)) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h2 : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hcl := calls_called hgen
  have hlt := calls_lt hgen hax
  have hmemR : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∃ cl ∈ (j8DataOf p Rg Rt hgen).calls, cl.1 = id := by
    intro id hid
    have := List.mem_dedup.mp hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp this
    exact ⟨cl, hcl, e⟩
  have hlay : List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids := by
    show List.ofFn (Nock.Jet.ChipJ8T.HonestRAP.layJ (j8DataOf p Rg Rt hgen).jrows.get) =
      layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen]
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [Nock.Jet.ChipJ8T.HonestRAP.layJ]
  have hJlen : (layoutJ8 Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).ids).length < p := by
    rw [← ComplJ8Jet.jrows_pre_run Rt hgen, List.length_map]
    exact size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hcells : (j8DataOf p Rg Rt hgen).cells.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hidsl : (j8DataOf p Rg Rt hgen).ids.length < p := by
    have h1 : (j8DataOf p Rg Rt hgen).ids.length ≤ (bfsForest [(j8DataOf p Rg Rt hgen).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 (size_lt_p Rt hgen hp63 h31 List.mem_cons_self)
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls
    hcalls hlt hJlen
  have hroot : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs,
      Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).roots := by
    intro id hid
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hne : (j8DataOf p Rg Rt hgen).cells ≠ [] := List.ne_nil_of_length_pos hC
  have hidx : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).idx id < p :=
    fun id _ => lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hcells.le
  have hrk : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, (j8DataOf p Rg Rt hgen).rk id ≠ (0, 0) :=
    fun id _ => rk_ne _ (ComplJ8Data.compile_isCell p (Rt id))
  have hrkl : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ((j8DataOf p Rg Rt hgen).rk id).1 < p ∧
      ((j8DataOf p Rg Rt hgen).rk id).2 < p := by
    intro id hid
    have hl := hleaf _ (hroot id hid)
    have hi := ComplJ8Walk.internal_lt_leaves (Nock.Jet.Autogen.compile p (Rt id))
    have h62 : (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
    have hd : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 ≤ (Nock.Jet.Autogen.compile p (Rt id)).internal :=
      Nat.div_le_self _ _
    have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    refine ⟨?_, ?_⟩
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < p
      have : (Nock.Jet.Autogen.compile p (Rt id)).internal < 2 ^ 109 := lt_of_lt_of_le hi hl
      have h109 : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < 2 ^ 47 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 109 := this
          _ = 2 ^ 47 * 2 ^ 62 := by rw [← pow_add]
      have : (2 : ℕ) ^ 47 < 2 ^ 63 := by norm_num
      omega
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < p
      omega
  refine ComplJ8Jet.stat_of hp Rt _ _ _ _ _ ⟨Rt, hRt⟩ hRt (fun i hi => ?_) hlay (fun i hi => ?_) hidsl
    hblk (List.nodup_dedup _) hidx hrk (fun id hid => ?_)
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hcl cl hcl'
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'
  · rw [hrc]; exact ⟨(hrkl id hid).1, (hrkl id hid).2, hidx id hid⟩

end Stat

/-! ## 7. The assembly: `obligations_of_run` and `complJ8` -/

section Counts
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec nPins)
variable {K : Type}

theorem nPins_le_length : ∀ L : List (BadSpec K), nPins L ≤ L.length
  | [] => le_rfl
  | BadSpec.pin _ _ :: L => by simp only [nPins, List.length_cons]; have := nPins_le_length L; omega
  | BadSpec.ord _ _ :: L => by simp only [nPins, List.length_cons]; have := nPins_le_length L; omega

theorem length_flatMap_le {α β : Type} (l : List α) (g : α → List β) (m : ℕ) (h : ∀ x ∈ l, (g x).length ≤ m) :
    (l.flatMap g).length ≤ l.length * m := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

end Counts

section Final
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimRecsJ8 pinRecsJ8)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The run's pole families**: compute (`compPoles`), cell validity and handle, J-8 walk validity and handle,
J. -/
def famsOf (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length) : List (List (BadSpec K)) :=
  [ComplJ8CompPole.compPoles δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length, famCellV δ D,
    famCellH δ b D hC (orbJ8 D hF), famWalkV δ D, famWalkH δ D, famJ δ D]

/-- **The honest record of the run** (concrete atom part, the run's families). -/
abbrev BR (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) : HonestJ8 p K δ Rg fuel s f r :=
  BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA)
    (famsOf δ b (j8DataOf p Rg Rt hgen) hF hC)

/-- **The obligations still carried as hypotheses** (exact copies of the `ComplJ8Obligations` fields): the atom
table, the atom walk and the three cross-table balances at the run's honest record. -/
structure OpenJ8 (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  atomOK : ∀ χ, B.Good χ →
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA)
  awOK : ∀ χ, B.Good χ → AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
    (qV δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsV)
  balG : ∀ χ, B.Good χ →
    (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3)) =
      Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1)) ∧
    (B.M χ).ρ 4 = Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
    (B.M χ).ρS + ((pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) x))⁻¹).sum +
        Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) =
      Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1))
  balV : ∀ χ, B.Good χ →
    ((claimRecsJ8 δ χ (cJ s f r) (B.M χ).m ++ pinRecsJ8 δ B.Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    ((B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0)
  balF : ∀ χ, B.Good χ →
    ((B.M χ).pubsC 2 = (B.M χ).pubsW 0 ∧ (B.M χ).pubsC 3 = (B.M χ).pubsW 1) ∧
    ((B.M χ).pubsA 2 = (B.M χ).pubsV 0 ∧ (B.M χ).pubsA 3 = (B.M χ).pubsV 1)

/-- Every event of a family is a pin. -/
def AllPin (L : List (BadSpec K)) : Prop := ∀ e ∈ L, ∃ i g, e = BadSpec.pin i g

theorem allPin_map {α : Type} (l : List α) (g : α → BadSpec K) (h : ∀ x, ∃ i c, g x = BadSpec.pin i c) :
    AllPin (l.map g) := by
  intro e he; obtain ⟨x, -, rfl⟩ := List.mem_map.mp he; exact h x

theorem allPin_flatMap {α : Type} (l : List α) (g : α → List (BadSpec K)) (h : ∀ x ∈ l, AllPin (g x)) :
    AllPin (l.flatMap g) := by
  intro e he; obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he; exact h x hx e he

theorem allPin_append (L M : List (BadSpec K)) (hL : AllPin L) (hM : AllPin M) : AllPin (L ++ M) := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact hL e h
  · exact hM e h

theorem quadPole_pin (i : Fin frameJ8.n) (x : Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :
    ∃ j c, ComplJ8Bad.quadPole δ i x = BadSpec.pin j c := ⟨_, _, rfl⟩

theorem slotPoles_len (S : SlotX (ZMod p)) (eT : Nock.Reified.Env (ZMod p)) :
    (ComplJ8CompPole.slotPoles (K := K) δ S eT).length ≤ 3 ∧ AllPin (ComplJ8CompPole.slotPoles (K := K) δ S eT) := by
  unfold ComplJ8CompPole.slotPoles
  cases S.pair with
  | none => exact ⟨by simp, fun e he => by simp at he; subst he; exact ⟨_, _, rfl⟩⟩
  | some q =>
    obtain ⟨fl, a, b', _⟩ := q
    refine ⟨by simp, fun e he => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

theorem walkHx_len (D : J8Data p Rg fuel s f r) (j : ℕ) : (walkHx δ D j (K := K)).length ≤ 3 := by
  unfold walkHx; split_ifs <;> simp

theorem keysOf_len {F : Type} [Field F] (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE))
    (row : Nock.Jet.ChipJ8.CRow F) : (Nock.Jet.ChipJ8.keysOf es row).length ≤ es.length := by
  unfold Nock.Jet.ChipJ8.keysOf; rw [List.length_map]; exact List.length_filter_le _ _

theorem jKeysT_len {n : ℕ} (rows : Fin n → Nock.Jet.ChipJ8.CRow (ZMod p)) : (ComplJ8Jet.jKeysT rows).length ≤ n * 25 := by
  unfold ComplJ8Jet.jKeysT
  refine (length_flatMap_le _ _ 25 fun i _ => ?_).trans (by simp)
  simp only [List.length_append, Nock.Jet.RapJetJ8.consKT, Nock.Jet.RapJetJ8.provKT]
  have h0 := keysOf_len Nock.Jet.ChipJ8.ents0T (rows i)
  have h1 := keysOf_len Nock.Jet.ChipJ8.ents1T (rows i)
  have h2 := keysOf_len Nock.Jet.ChipJ8.ents2T (rows i)
  have h3 := keysOf_len Nock.Jet.ChipJ8.ents3 (rows i)
  have e0 : Nock.Jet.ChipJ8.ents0T.length = 9 := rfl
  have e1 : Nock.Jet.ChipJ8.ents1T.length = 4 := rfl
  have e2 : Nock.Jet.ChipJ8.ents2T.length = 11 := rfl
  have e3 : Nock.Jet.ChipJ8.ents3.length = 1 := rfl
  omega

theorem jKeysX_len {n : ℕ} (rows : Fin n → Nock.Jet.ChipJ8.CRow (ZMod p)) : (ComplJ8Jet.jKeysX rows).length ≤ n * 3 := by
  unfold ComplJ8Jet.jKeysX
  refine (length_flatMap_le _ _ 3 fun i _ => (keysOf_len _ _).trans (le_of_eq rfl)).trans (by simp)

/-- **The families: side conditions, pins only, pin count `≤ 2^40`** (tight enough to add the atom families of
`ComplJ8OfAtom.famsA` under `2^66`, `ComplJ8Closed.famsAll_facts`). -/
theorem famsOf_facts (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) :
    (∀ L ∈ famsOf δ b D hF hC (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsOf δ b D hF hC (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsOf δ b D hF hC (K := K)).map nPins).sum ≤ 2 ^ 40 := by
  have hγ := ComplJ8Bad.γH_readsOff (K := K) δ
  have hJOK : ∀ e ∈ famJ δ D (K := K), e.OK := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact ComplJ8Bad.ioPoles_OK δ _ _ _ hγ e h
    · exact ComplJ8Bad.ioPoles_OK δ _ _ _ hγ e h
  have pC : AllPin (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length) :=
    allPin_flatMap _ _ fun j _ => allPin_flatMap _ _ fun S _ => (slotPoles_len δ S _).2
  have pCV : AllPin (famCellV δ D (K := K)) := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, rfl⟩
    · exact allPin_flatMap _ _ (fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _) e he
  have pCH : AllPin (famCellH δ b D hC (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => quadPole_pin δ _ _
  have pWV : AllPin (famWalkV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _
  have pWH : AllPin (famWalkH δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _
  have pJ : AllPin (famJ δ D (K := K)) :=
    allPin_append _ _ (allPin_map _ _ fun x => quadPole_pin δ _ _) (allPin_map _ _ fun x => quadPole_pin δ _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    simp only [famsOf, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ComplJ8CompPole.compPoles_OK δ _ _ _ _
    · exact famCellV_OK δ D
    · exact famCellH_OK δ b D hC _
    · exact famWalkV_OK δ D
    · exact famWalkH_OK δ D
    · exact hJOK
  · intro L hL e he i N hN
    simp only [famsOf, List.mem_cons, List.not_mem_nil, or_false] at hL
    have hp : AllPin L := by rcases hL with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨j, g, rfl⟩ := hp e he
    cases hN
  · have hn := h31 _ (show (bfsForest [D.t]).length ∈ sizesJ8 D by simp [sizesJ8])
    have hnC := h31 _ (show D.cells.length ∈ sizesJ8 D by simp [sizesJ8])
    have hnW := h31 _ (show (walkRows D.cells D.reads).length ∈ sizesJ8 D by simp [sizesJ8])
    have hnJ := h31 _ (show D.jrows.length ∈ sizesJ8 D by simp [sizesJ8])
    have l1 : (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length).length ≤
        (bfsForest [D.t]).length * 12 := by
      unfold ComplJ8CompPole.compPoles
      refine (length_flatMap_le _ _ 12 fun j _ => ?_).trans (by simp)
      exact (length_flatMap_le _ _ 3 fun S _ => (slotPoles_len δ S _).1).trans (by simp [ComplJ8CompPole.SLOTS]; rfl)
    have l2 : (famCellV δ D (K := K)).length ≤ 1 + D.cells.length * 5 := by
      unfold famCellV
      rw [List.length_cons]
      have := length_flatMap_le (List.range D.cells.length)
        (fun j => (cellVx δ D j (K := K)).map (ComplJ8Bad.quadPole δ WeightsJ8.c5)) 5 (fun j _ => by simp [cellVx])
      simp only [List.length_range] at this; omega
    have l3 : (famCellH δ b D hC (orbJ8 D hF) (K := K)).length ≤ D.cells.length := by simp [famCellH]
    have l4 : (famWalkV δ D (K := K)).length ≤ (walkRows D.cells D.reads).length * 3 := by
      unfold famWalkV
      exact (length_flatMap_le _ _ 3 fun j _ => by simp [walkVx]).trans (by simp)
    have l5 : (famWalkH δ D (K := K)).length ≤ (walkRows D.cells D.reads).length * 3 := by
      unfold famWalkH
      exact (length_flatMap_le _ _ 3 fun j _ => by rw [List.length_map]; exact walkHx_len δ D j).trans (by simp)
    have l6 : (famJ δ D (K := K)).length ≤ D.jrows.length * 28 := by
      unfold famJ ComplJ8Bad.ioPoles
      simp only [List.length_append, List.length_map]
      have h1 := jKeysT_len D.jrows.get
      have h2 := jKeysX_len D.jrows.get
      omega
    have e : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have e66 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    simp only [famsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := nPins_le_length (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length)
    have := nPins_le_length (famCellV δ D (K := K))
    have := nPins_le_length (famCellH δ b D hC (orbJ8 D hF) (K := K))
    have := nPins_le_length (famWalkV δ D (K := K))
    have := nPins_le_length (famWalkH δ D (K := K))
    have := nPins_le_length (famJ δ D (K := K))
    rw [e66]; rw [e] at hn hnC hnW hnJ
    omega

theorem regs_called :
    ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, id ∈ CalledIds t := by
  intro id hid
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
  exact calls_called hgen cl hcl

/-- **`obligations_of_run`**: every field of `ComplJ8Obligations` at the run's honest record, from the run
binders, with the fields of `OpenJ8` (atom table, atom walk, balances) as the one carried hypothesis. -/
theorem obligations_of_run (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length)
    (O : OpenJ8 δ b (BR δ b Rt hgen hF hC hA)) :
    ComplJ8Obligations δ b (BR δ b Rt hgen hF hC hA) := by
  have hcl : ∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p := fun k v hv =>
    hclA k v (by rw [hv]; simp [Noun.leafList])
  have hreg := regs_called (p := p) Rt hgen
  have hregLeaf : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∀ v ∈ (Nock.Jet.Autogen.compile p (Rt id)).leafList, v < p :=
    ComplJ8RegLeaf.compile_leaves_lt_reg (by omega) Rt _ (fun id hid => (hRt id (hreg id hid)).2.2)
      (fun id hid => hregAx id (hreg id hid))
  obtain ⟨hOK, hpin, hcnt⟩ := famsOf_facts δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC h31
  have m0 : ComplJ8CompPole.compPoles (K := K) δ (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
      (bfsForest [(j8DataOf p Rg Rt hgen).t]) (bfsForest [(j8DataOf p Rg Rt hgen).t]).length ∈
      famsOf δ b (j8DataOf p Rg Rt hgen) hF hC := List.mem_cons_self
  have m1 : famCellV δ (j8DataOf p Rg Rt hgen) ∈ famsOf δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : famCellH δ b (j8DataOf p Rg Rt hgen) hC (orbJ8 _ hF) ∈ famsOf δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : famWalkV δ (j8DataOf p Rg Rt hgen) ∈ famsOf δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m4 : famWalkH δ (j8DataOf p Rg Rt hgen) ∈ famsOf δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  have m5 : famJ δ (j8DataOf p Rg Rt hgen) ∈ famsOf δ b (K := K) (j8DataOf p Rg Rt hgen) hF hC :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := compute_group δ b Rt hgen hF hC hA
    (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) (famsOf δ b (j8DataOf p Rg Rt hgen) hF hC) hp63 hax hop5 hcl m0
  obtain ⟨n1, n2⟩ := nodes_ok δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA)
    (famsOf δ b (j8DataOf p Rg Rt hgen) hF hC)
  obtain ⟨g1, g2, g3⟩ := nodes_group δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA)
    (famsOf δ b (j8DataOf p Rg Rt hgen) hF hC) hp63 h31
  obtain ⟨w1, w2⟩ := bad_group δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA)
    (famsOf δ b (j8DataOf p Rg Rt hgen) hF hC) hOK hpin (fun _ => hcnt.trans (by norm_num))
  exact
    { hH := c1, hpair := c2, hN := c3, hinjX := n1, hadjX := n2,
      htrC := fun χ => htrC_run δ b Rt hgen hF hC hA _ _ χ,
      hpIC := c4, hpS := c5, hpO := c6, hpub := c7, hρ := c8, goodC := c9,
      cellOK := fun χ hχ => cellOK_run δ b Rt hgen hF hC hA _ _ hpG hp63 hleaf m1 m2 χ hχ,
      cellNodes := g1,
      walkOK := fun χ hχ => walkOK_run δ b Rt hgen hF hC hA _ _ hp63 h31 hwalk m3 m4 χ hχ,
      walkNodes := g2,
      jOK := fun χ hχ => jOK_run δ b Rt hgen hF hC hA _ _ hp63 h31 hRt m5 χ hχ,
      atomOK := O.atomOK, atomNodes := g3, awOK := O.awOK, balG := O.balG, balV := O.balV, balF := O.balF,
      stat := stat_run δ b Rt hgen hF hC hA _ _ hp63 hax h31 hleaf hRt,
      claim := fun χ => claim_run δ b Rt hgen hF hC hA _ _ hp63 h31 hclA hleaf hregLeaf χ,
      budget := budget_run δ b Rt hgen hF hC hA _ _ hp63 h31,
      wt := w1,
      staged := staged_run δ b Rt hgen hF hC hA _ _ (stA_run δ b _ hF hA) (stV_run δ b _ hF hA),
      fig := w2 }

/-! ### The derived run facts: the common orbit at Goldilocks, a cell, an atom row -/

theorem szJ8_le (D : J8Data p Rg fuel s f r) (h31 : Rows31 D) : szJ8 D ≤ 2 ^ 31 := by
  unfold szJ8
  have : ∀ L : List ℕ, (∀ x ∈ L, x ≤ 2 ^ 31) → L.foldr max 0 ≤ 2 ^ 31 := by
    intro L hL
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.foldr_cons]
      exact max_le (hL a List.mem_cons_self) (ih fun x hx => hL x (List.mem_cons_of_mem _ hx))
  exact this _ h31

theorem ht_le (D : J8Data p Rg fuel s f r) (h31 : Rows31 D) : htJ8 D ≤ 31 :=
  max_le (by norm_num) (Nat.clog_le_of_le_pow (szJ8_le D h31))

theorem goldilocks_dvd : 3 * 2 ^ 32 ∣ Nock.Atoms.p - 1 :=
  ⟨1431655765, by simp [Nock.Atoms.p, Nock.Field.p]⟩

/-- **`DvdOK` at Goldilocks** from the row binder (the common height is `≤ 31`). -/
theorem dvdOK_of_rows (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (h31 : Rows31 D) : DvdOK D := by
  unfold DvdOK
  have h := goldilocks_dvd
  rw [← hpG] at h
  exact (mul_dvd_mul_left 3 (pow_dvd_pow 2 ((ht_le D h31).trans (by norm_num)))).trans h

theorem mem_addCells_self (a c : Noun) (acc : List Noun) : Noun.cell a c ∈ Nock.V1J8.Gen.addCells (.cell a c) acc := by
  unfold Nock.V1J8.Gen.addCells
  split_ifs with h
  · exact h
  · exact ComplJ8Data.subset_addCells _ _ _ (ComplJ8Data.subset_addCells _ _ _
      (List.mem_append_right _ List.mem_cons_self))

theorem mem_foldl_addCells : ∀ (roots acc : List Noun) (x : Noun), x ∈ acc →
    x ∈ roots.foldl (fun acc n => Nock.V1J8.Gen.addCells n acc) acc
  | [], _, _, h => h
  | n :: roots, acc, x, h => mem_foldl_addCells roots _ x (ComplJ8Data.subset_addCells n acc x h)

theorem mem_cellsOfRoots_of_root : ∀ (roots acc : List Noun) (a c : Noun), Noun.cell a c ∈ roots →
    Noun.cell a c ∈ roots.foldl (fun acc n => Nock.V1J8.Gen.addCells n acc) acc
  | [], _, _, _, h => absurd h (List.not_mem_nil)
  | n :: roots, acc, a, c, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_addCells roots _ _ (mem_addCells_self a c acc)
    · exact mem_cellsOfRoots_of_root roots _ a c h

/-- **The cell list is non-empty** (the formula is a cell and a demand root). -/
theorem cells_pos : 0 < (j8DataOf p Rg Rt hgen).cells.length := by
  obtain ⟨a, c, hf⟩ := formula_cell_of_gen hgen
  have hroot : Noun.cell a c ∈ (j8DataOf p Rg Rt hgen).roots := by
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    simp [hf]
  exact List.length_pos_of_mem (mem_cellsOfRoots_of_root _ [] a c hroot)

/-- **The atom cell list is non-empty.** -/
theorem acs_pos : 0 < (j8DataOf p Rg Rt hgen).acs.length :=
  List.length_pos_of_ne_nil (ComplJ8Data.acsP_ne _ _ _)

/-- **The honest record of the run, from the row binder** (`hF hC hA` derived). -/
abbrev BRun (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) : HonestJ8 p K δ Rg fuel s f r :=
  BR δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen)

open Classical in
/-- **`complJ8`: J-8 general completeness at Goldilocks**, for every generated run `hgen` of every program over
every registry `Rg` whose called jets are registered in compiled form (`hRt`, `hregAx`: `HregC`'s witness `Rt`
with its template axes `< p`), under the run binders `hax hop5`, the claim binder `hclA`, the leaf binder
`hleaf`, the walk-depth binder `hwalk`, every table `≤ 2^31` rows (`h31`), and the carried obligations `hopen`
(atom table, atom walk, three balances; `OpenJ8`).  Conclusion as `complJ8_of_obligations`: honest acceptance at
every good coin, `Pr[¬Good] ≤ ε_c`, staging, the claim holds, and at `|K| = cK` the figure `ε_c < 2^-120` with a
good coin. -/
theorem complJ8 (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hopen : OpenJ8 δ b (BRun δ b Rt hgen hpG h31)) :
    let B := BRun δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  intro B
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have O := obligations_of_run δ b Rt hgen hpG hp63 hax hop5 hclA hleaf hwalk hRt hregAx h31
    (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) hopen
  refine ⟨fun χ hχ => honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ,
    probJ8_notGood_le δ b B O, O.staged, genX_sound Rg.faithful B.hgen, fun hcK => ?_⟩
  have hrows : RowsLe31 B.Pb := rowsLe31_of δ b Rt hgen _ _ _ _ _ h31
  have hfig := O.fig hpG hcK hrows
  obtain ⟨χ, hχ⟩ := exists_good δ b B O (lt_trans hfig (by norm_num))
  exact ⟨hfig, χ, honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ⟩

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
