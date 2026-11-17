/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean

  * **`HonestJ8`**: the honest data of one run (phase B1 builds it from `genX`): the generated tree and its
    `genX` equation, the handle map `H`, the op-5 limb data `pd`, the public layout `Pb`, the message and trace
    maps `M χ`, `tr χ`, the budgets, and the honest bad events `bad` as `(event, weight)` pairs (phase B3).
    `Good χ` = outside every event; `epsC` = the sum of the weights.
  * `smallX_of_binders`: together they give `SmallX` at every row (the compute chip's `hsm`).
  * **`ComplJ8Obligations`**: the remaining lemmas, one field per lemma, each stated exactly.  The compute chip's
    fields are the HYPOTHESES of `HonestTraceX.computeChipVCLHX_honest_sat` (the composition is proved here); the
    other chips' fields are their `AcceptsJ8V` conjuncts at good coins (phase B discharges each through the per-chip
    honest theorem named in its docstring).
  * **`honest_accepted_J8_of_obligations`**: `Good χ → AcceptsJ8V …` (PROVED from the obligations).
  * **`probJ8_notGood_le`**: `Pr[¬ Good] ≤ epsC` (PROVED: union bound over the list).
  * **`complJ8_of_obligations`**: acceptance at good coins, the probability bound, staging, the claim `HoldsN`,
    and at Goldilocks with rows `≤ 2^31`: `epsC < 2^-120` and an accepting coin EXISTS (non-vacuity), all PROVED
    from the obligations.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX
import Nock.Jet.VerifiedRegistry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK isPair PairOK hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

noncomputable section

/-! ## 1. The two new run binders -/

section Binders

/-- **Formula-atom bound at one row** (the formula-position atoms the compute base gates read as field elements):
the op-0 axis, the op-9 axis, the op-10 edit axis, the chain level `a + 1`, the jet id. -/
def AxRowX (p : ℕ) (r : RowNX) : Prop :=
  match r.st with
  | .s0 => ∀ ax, r.ft = .atom ax → ax < p
  | .s9 => ∀ ax, r.fth = .atom ax → ax < p
  | .s10 => ∀ a, r.ftth = .atom a → a < p
  | .s10L => ∀ a, r.f = .atom a → a + 1 < p
  | .s11j => (∀ id, r.ftth = .atom id → id < p) ∧ (∀ id, r.sf1 = .atom id → id < p)
  | _ => True

/-- **The op-5 depth condition at one row**: on an op-5 row, the axis of the first difference of the two compared
nouns is `< p` (a DATA quantity: it depends on the compared nouns, not on the formula). -/
def Op5RowX (p : ℕ) (r : RowNX) : Prop :=
  r.st = .s5 → axisOfPath (fdN r.sf1 r.sf2).1 < p

/-- **Binder 1 (`hax`)**: every row of the generated tree satisfies `AxRowX p`. -/
def ProgAxOK (p : ℕ) (t : NTree SkelX) : Prop := ∀ u, InTree t u → AxRowX p (rowOfSkelX u.label)

/-- **Binder 2 (`hop5`)**: every row of the generated tree satisfies `Op5RowX p`. -/
def ProgOp5OK (p : ℕ) (t : NTree SkelX) : Prop := ∀ u, InTree t u → Op5RowX p (rowOfSkelX u.label)

/-- The two binders give `SmallX` at a row. -/
theorem smallX_of_rows {p : ℕ} {r : RowNX} (h1 : AxRowX p r) (h2 : Op5RowX p r) : SmallX p r := by
  unfold SmallX
  unfold AxRowX at h1
  unfold Op5RowX at h2
  cases hst : r.st <;> simp only [hst] at h1 h2 ⊢ <;> first | exact h1 | exact h2 trivial

/-- **The two binders give the compute chip's `hsm`.** -/
theorem smallX_of_binders {p : ℕ} {t : NTree SkelX} (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t) :
    ∀ u, InTree t u → SmallX p (rowOfSkelX u.label) :=
  fun u hu => smallX_of_rows (hax u hu) (hop5 u hu)

/-- Phase B1 either consumes it or proves it
from `hrun` and drops it. -/
def ProgLeafOK (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → ∀ k < 12, (HonestCompX.hN (rowOfSkelX u.label) k).leaves ≤ 2 ^ 109

end Binders

/-! ## 2. The honest data of a run and its bad events -/

/-- The claim of a run. -/
def cJ (s f r : Noun) : P8PublicClaim := ⟨s, f, r⟩

/-- **The honest J-8 data of one run** (phase B1 builds it from `genX`; phase B3 supplies `bad`). -/
structure HonestJ8 (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    (Rg : Nock.Jet.VerifiedRegistry) (fuel : ℕ) (s f r : Noun) where
  /-- the generated tree of the run -/
  t : NTree SkelX
  hgen : genX Rg.R fuel s f = some (t, r)
  /-- the handle map and the op-5 α-pair limb data -/
  H : Noun → ℕ × ℕ
  pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)
  /-- the public layout, the honest messages and traces at each coin, the budgets -/
  Pb : PubJ8 p
  M : Coins frameJ8 K → MsgJ8' p K δ
  tr : Coins frameJ8 K → TrJ8 (ZMod p)
  rows : RowsJ8
  g : ℕ
  /-- the honest bad events with their weights -/
  bad : List (Finset (Coins frameJ8 K) × ℚ)

namespace HonestJ8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {δ : ZMod p}
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- A coin is good when it lies outside every honest bad event. -/
def Good (B : HonestJ8 p K δ Rg fuel s f r) (χ : Coins frameJ8 K) : Prop := ∀ e ∈ B.bad, χ ∉ e.1

/-- The completeness error: the sum of the weights. -/
def epsC (B : HonestJ8 p K δ Rg fuel s f r) : ℚ := (B.bad.map Prod.snd).sum

/-- The BFS rows of the run. -/
abbrev W (B : HonestJ8 p K δ Rg fuel s f r) : List (NTree SkelX) := bfsForest [B.t]

end HonestJ8

def RowsLe31 {p : ℕ} [Fact p.Prime] (Pb : PubJ8 p) : Prop :=
  Pb.n ≤ 2 ^ 31 ∧ Pb.nC ≤ 2 ^ 31 ∧ Pb.nW ≤ 2 ^ 31 ∧ Pb.nJ ≤ 2 ^ 31 ∧ Pb.nA ≤ 2 ^ 31 ∧ Pb.nV ≤ 2 ^ 31

/-! ## 3. The obligations -/

section Obl
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The compute publics of the honest message at `χ`. -/
abbrev pubJ (B : HonestJ8 p K δ Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  pubVJ8 δ b (cJ s f r) (B.M χ).m (B.M χ).ρ (B.M χ).ρS χ

/-- The compute walk coins `α`, `γ` (read from the challenge vector). -/
abbrev αJ (χ : Coins frameJ8 K) : K := limbVal b (chalVJ8 b χ) chalAlphaW
abbrev γJ (χ : Coins frameJ8 K) : K := limbVal b (chalVJ8 b χ) chalGammaW

/-- **The remaining lemmas of J-8 completeness**, one field per lemma. -/
structure ComplJ8Obligations (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  -- ### compute: the hypotheses of `HonestTraceX.computeChipVCLHX_honest_sat`
  /-- [B1] the handle map is honest (`hdl` / `hdlB` of the generator). -/
  hH : HdlOK (ringChar (ZMod p)) B.H
  /-- [B1] the op-5 α-pair limb data satisfies `PairOK` on every pair row (from the atom table's comb spines). -/
  hpair : ∀ u, InTree B.t u → isPair B.H (rowOfSkelX u.label) → PairOK (F := ZMod p) (B.pd (rowOfSkelX u.label))
  /-- [B1] the compute chip has one row per BFS row. -/
  hN : B.Pb.n = B.W.length
  /-- [B1] the compute row nodes (`AcceptsJ8V.hinjX` / `hadjX`). -/
  hinjX : Function.Injective B.Pb.nodes
  hadjX : ∀ (i : Fin B.Pb.n) (hi : (i : ℕ) + 1 < B.Pb.n),
    B.Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodes i * B.Pb.orbit.ω
  /-- [B1] the compute trace is `polyX` at the walk coins of `χ`. -/
  htrC : ∀ χ, qX δ b B.Pb (B.tr χ) (chalVJ8 b χ) (pubJ δ b B χ) =
    VclL.HonestTraceX.polyX b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ)
      (VclL.HonestTraceX.lnW (αJ b χ)) (VclL.HonestTraceX.cntW B.W (αJ b χ))
      (VclL.HonestTraceX.accW (F := ZMod p) B.H B.W (αJ b χ) (γJ b χ)) B.Pb.nodes
      (computeChipVCLHX B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ) (pubJ δ b B χ) B.Pb.orbit).rap.w
  /-- [B1] the walk publics: initial count, seed, output. -/
  hpIC : ∀ χ, limbVal b (pubJ δ b B χ) pubIC = αJ b χ
  hpS : ∀ χ, limbVal b (pubJ δ b B χ) pubSeed =
    VclL.HonestTraceX.curW (F := ZMod p) B.H B.W (γJ b χ) 1 * αJ b χ
  hpO : ∀ χ, limbVal b (pubJ δ b B χ) pubOut = 0
  /-- [B1] the claim publics `0..5` are the handles of `(s, f, r)`. -/
  hpub : ∀ χ, pubJ δ b B χ 0 = hk B.H s ∧ pubJ δ b B χ 1 = hv B.H s ∧ pubJ δ b B χ 2 = hk B.H f ∧
    pubJ δ b B χ 3 = hv B.H f ∧ pubJ δ b B χ 4 = hk B.H r ∧ pubJ δ b B χ 5 = hv B.H r
  /-- [B2] the six accumulator terminals are the honest totals. -/
  hρ : ∀ χ, ∀ a < 6, ∀ k : Fin 3, pubJ δ b B χ (VclL.HonestTraceX.pubOfA a + k) =
    coord b (VclL.HonestTraceX.accV b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) a B.Pb.n) k
  /-- [B3] at a good coin: the walk coin order and the slot pole condition. -/
  goodC : ∀ χ, B.Good χ → B.W.length ≤ orderOf (αJ b χ) ∧
    ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0 ∨
        HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0
  -- ### the cell table (`HonestKW.cellChipHQKW_accepts_honest`)
  cellOK : ∀ χ, B.Good χ →
    (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC)
  /-- [B1] cell nodes. -/
  cellNodes : Function.Injective B.Pb.nodesC ∧
    (∀ (i : Fin B.Pb.nC) (hi : (i : ℕ) + 1 < B.Pb.nC),
      B.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesC i * B.Pb.orbitC.ω) ∧ B.Pb.nC < ringChar (ZMod p)
  -- ### the J-8 walk (`HonestK8.walkChipJ8_accepts_honest`)
  /-- [B1] walk: satisfied and bound at every good coin. -/
  walkOK : ∀ χ, B.Good χ →
    (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW)
  /-- [B1] walk nodes and roots. -/
  walkNodes : Function.Injective B.Pb.nodesW ∧
    (∀ (i : Fin B.Pb.nW) (hi : (i : ℕ) + 1 < B.Pb.nW),
      B.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesW i * B.Pb.orbitW.ω) ∧
    1 ≤ B.Pb.kroots ∧ B.Pb.kroots ≤ B.Pb.nW ∧ B.Pb.kroots + B.Pb.nW < ringChar (ZMod p)
  -- ### the J chip (`ChipJ8THonestRAP.jetChipJ8_honest_sat`, or absent at `nJ = 0`)
  /-- [B1] J present (calls) or absent (no call). -/
  jOK : ∀ χ, B.Good χ → JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
    (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ)
  -- ### the atom table (`HonestA8.atomChipHQ_accepts_honest`, `AtomChipHQL.atomChipHQL_accepts_honest`, `AtomGenJ8` pad row)
  /-- [B1] atom table: both chip views satisfied and bound at every good coin. -/
  atomOK : ∀ χ, B.Good χ →
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA)
  /-- [B1] atom nodes. -/
  atomNodes : Function.Injective B.Pb.nodesA ∧
    (∀ (i : Fin B.Pb.nA) (hi : (i : ℕ) + 1 < B.Pb.nA),
      B.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesA i * B.Pb.orbitA.ω) ∧ B.Pb.nA < p
  -- ### the atom walk (`walkChipHQK` honest, present iff some op-5 row compares two big atoms)
  /-- [B1] atom walk present or absent. -/
  awOK : ∀ χ, B.Good χ → AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
    (qV δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsV)
  -- ### cross-table balances
  /-- [B2] the export / path / service balances (`hGx hGp hGS`; `ChipJ8THonestBal.termJ_sum_of_mv` for the J
  terminal). -/
  balG : ∀ χ, B.Good χ →
    (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3)) =
      Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1)) ∧
    (B.M χ).ρ 4 = Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
    (B.M χ).ρS + ((pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) =
      Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1))
  /-- [B2] the cell validity, the atom export, the atom validity terminal (`hsumC' hbalA' hvalA0`). -/
  balV : ∀ χ, B.Good χ →
    ((claimRecsJ8 δ χ (cJ s f r) (B.M χ).m ++ pinRecsJ8 δ B.Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    ((B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0)
  /-- [B2] the fingerprint-export links (`hfxC hfxA`). -/
  balF : ∀ χ, B.Good χ →
    ((B.M χ).pubsC 2 = (B.M χ).pubsW 0 ∧ (B.M χ).pubsC 3 = (B.M χ).pubsW 1) ∧
    ((B.M χ).pubsA 2 = (B.M χ).pubsV 0 ∧ (B.M χ).pubsA 3 = (B.M χ).pubsV 1)
  -- ### the static, registry, claim, census and budget conjuncts
  /-- [B1] the J layout and the registry pins (`hlay hsmall huniq hTpl hnd hidx hrk hlt`) at `Rg.R`. -/
  stat : List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids ∧
    (∀ q ∈ layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ B.Pb.regs, Rg.R i = some ⟨(B.Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (B.Pb.Rt i)⟩ ∧
      axPosB (B.Pb.Rt i) = true ∧ (B.Pb.Rt i).WellTyped p) ∧
    B.Pb.regs.Nodup ∧ (∀ id ∈ B.Pb.regs, B.Pb.idx id < p) ∧ (∀ id ∈ B.Pb.regs, B.Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ B.Pb.regs, (B.Pb.rk id).1 < ringChar (ZMod p) ∧ (B.Pb.rk id).2 < ringChar (ZMod p) ∧
      B.Pb.idx id < ringChar (ZMod p))
  /-- [B1] the claim checks and the census (`hclA hclI hclR hcen hcellF`), from the claim binders. -/
  claim : ∀ χ, (∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → (claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ censusG B.Pb (cJ s f r), x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    isCellN (cJ s f r).formula = true
  /-- [B1] public lengths and budgets (`hlenC hlenA hnA62 hbud hbudV`). -/
  budget : 3 + B.Pb.regs.length + 2 * B.Pb.nC < p ∧ B.Pb.nA + B.Pb.nV < p ∧ B.Pb.nA ≤ 2 ^ 62 ∧
    RealIOJ8.BudJ8 B.Pb B.rows (B.g + B.rows.N) ∧
    (B.Pb.regs.length ≤ B.g ∧ B.Pb.nA ≤ B.rows.mb ∧ B.Pb.nA ≤ B.rows.A ∧ B.Pb.nV ≤ B.rows.AW)
  -- ### bad events, staging, figure
  /-- [B3] each bad event's probability is at most its weight. -/
  wt : ∀ e ∈ B.bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2
  /-- [B3] the honest traces are staged. -/
  staged : StJ8 B.tr
  /-- [B3] the Goldilocks figure. -/
  fig : p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120

end Obl

/-! ## 4. The probability bound (union bound over the list) -/

section Prob
variable {K : Type} [Fintype K] [DecidableEq K]

open Classical in
theorem prob_exists_le (L : List (Finset (Coins frameJ8 K) × ℚ))
    (hw : ∀ e ∈ L, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e ∈ L, χ ∈ e.1).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have hN : (0 : ℚ) ≤ Fintype.card (Coins frameJ8 K) := by positivity
    have hsub : (Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ e :: L, χ ∈ e'.1) ⊆
        e.1 ∪ Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ L, χ ∈ e'.1 := by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hχ
      obtain ⟨e', he', hχ'⟩ := hχ
      rcases he' with rfl | he'
      · exact Finset.mem_union_left _ hχ'
      · exact Finset.mem_union_right _ (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨e', he', hχ'⟩)
    have hc : ((Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ e :: L, χ ∈ e'.1).card : ℚ) ≤
        (e.1.card : ℚ) + ((Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ L, χ ∈ e'.1).card : ℚ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h1 := hw e (by simp)
    have h2 := ih (fun e' he' => hw e' (by simp [he']))
    calc _ ≤ ((e.1.card : ℚ) + ((Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ L, χ ∈ e'.1).card : ℚ)) /
          Fintype.card (Coins frameJ8 K) := div_le_div_of_nonneg_right hc hN
      _ = (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) +
          ((Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e' ∈ L, χ ∈ e'.1).card : ℚ) /
            Fintype.card (Coins frameJ8 K) := add_div _ _ _
      _ ≤ e.2 + (L.map Prod.snd).sum := add_le_add h1 h2
      _ = ((e :: L).map Prod.snd).sum := by simp

end Prob

/-! ## 5. The main theorems -/

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **Honest acceptance at every good coin, from the obligations.** -/
theorem honest_accepted_J8_of_obligations (B : HonestJ8 p K δ Rg fuel s f r)
    (O : ComplJ8Obligations δ b B) (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p B.t) (hop5 : ProgOp5OK p B.t)
    (χ : Coins frameJ8 K) (hχ : B.Good χ) :
    AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp16 : 16 ≤ ringChar (ZMod p) := by rw [hrc]; omega
  have hsm : ∀ u, InTree B.t u → SmallX (ringChar (ZMod p)) (rowOfSkelX u.label) := by
    rw [hrc]; exact smallX_of_binders hax hop5
  obtain ⟨hord, hnb⟩ := O.goodC χ hχ
  have hX := VclL.HonestTraceX.computeChipVCLHX_honest_sat δ B.hgen B.H B.pd O.hH hp16 hsm O.hpair
    (αJ b χ) (γJ b χ) hord B.Pb.hn O.hN B.Pb.nodes O.hinjX b (chalVJ8 b χ) (pubJ δ b B χ) B.Pb.orbit
    (fun i hi => (O.hadjX i hi).trans (mul_comm _ _)) rfl rfl (O.hpIC χ) (O.hpS χ) (O.hpO χ) (O.hpub χ)
    (O.hρ χ) hnb
  obtain ⟨hsatC, hbindC⟩ := O.cellOK χ hχ
  obtain ⟨hinjC, hadjC, hnpC⟩ := O.cellNodes
  obtain ⟨hsatW, hbindW⟩ := O.walkOK χ hχ
  obtain ⟨hinjW, hadjW, hkW, hknW, hkpW⟩ := O.walkNodes
  obtain ⟨hsatA, hbindA, hsatL, hbindL⟩ := O.atomOK χ hχ
  obtain ⟨hinjA, hadjA, hnpA⟩ := O.atomNodes
  obtain ⟨hGx, hGp, hGS⟩ := O.balG χ hχ
  obtain ⟨hsumC', hbalA', hvalA0⟩ := O.balV χ hχ
  obtain ⟨hfxC, hfxA⟩ := O.balF χ hχ
  obtain ⟨hlay, hsmall, huniq, hTpl, hnd, hidx, hrk, hlt⟩ := O.stat
  obtain ⟨hclA, hclI, hclR, hcen, hcellF⟩ := O.claim χ
  obtain ⟨hlenC, hlenA, hnA62, hbud, hbudV⟩ := O.budget
  have hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ)
      (pubVJ8 δ b (cJ s f r) (B.M χ).m (B.M χ).ρ (B.M χ).ρS χ) B.Pb.orbit)
      (qX δ b B.Pb (B.tr χ) (chalVJ8 b χ) (pubVJ8 δ b (cJ s f r) (B.M χ).m (B.M χ).ρ (B.M χ).ρS χ)) := by
    rw [O.htrC χ]
    exact hX
  exact
  { hsatX := hsatX
    hinjX := O.hinjX
    hadjX := O.hadjX
    hsatC := hsatC
    hbindC := hbindC
    hinjC := hinjC
    hadjC := hadjC
    hnpC := hnpC
    hsatW := hsatW
    hbindW := hbindW
    hinjW := hinjW
    hadjW := hadjW
    hkW := hkW
    hknW := hknW
    hkpW := hkpW
    hJk := O.jOK χ hχ
    hsatA := hsatA
    hbindA := hbindA
    hinjA := hinjA
    hadjA := hadjA
    hnpA := hnpA
    hVk := O.awOK χ hχ
    hGx := hGx
    hGp := hGp
    hGS := hGS
    hlay := hlay
    hsmall := hsmall
    huniq := huniq
    hTpl := hTpl
    hnd := hnd
    hidx := hidx
    hrk := hrk
    hlt := hlt
    hsumC' := hsumC'
    hbalA' := hbalA'
    hvalA0 := hvalA0
    hfxC := hfxC
    hfxA := hfxA
    hclA := hclA
    hclI := hclI
    hclR := hclR
    hcen := hcen
    hlenC := hlenC
    hlenA := hlenA
    hcellF := hcellF
    hnA62 := hnA62
    hbud := hbud
    hbudV := hbudV
    hsatL := hsatL
    hbindL := hbindL }

open Classical in
/-- **`Pr_χ[some honest bad event] ≤ ε_c`.** -/
theorem probJ8_notGood_le (B : HonestJ8 p K δ Rg fuel s f r) (O : ComplJ8Obligations δ b B) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC := by
  have he : (Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ) =
      Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e ∈ B.bad, χ ∈ e.1 := by
    ext χ
    simp [HonestJ8.Good]
  rw [he]
  exact prob_exists_le B.bad O.wt

open Classical in
/-- **Non-vacuity**: when `ε_c < 1` some coin is good. -/
theorem exists_good (B : HonestJ8 p K δ Rg fuel s f r) (O : ComplJ8Obligations δ b B) (h1 : B.epsC < 1) :
    ∃ χ : Coins frameJ8 K, B.Good χ := by
  by_contra hn0
  have hn : ∀ χ : Coins frameJ8 K, ¬ B.Good χ := not_exists.mp hn0
  have hall : (Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ) = Finset.univ := by
    ext χ; simp [hn χ]
  have hp := probJ8_notGood_le δ b B O
  rw [hall, Finset.card_univ] at hp
  have hpos : (0 : ℚ) < Fintype.card (Coins frameJ8 K) := by exact_mod_cast Fintype.card_pos
  rw [div_self hpos.ne'] at hp
  linarith

open Classical in
/-- **J-8 general completeness from the obligations.**  For the run `genX Rg.R fuel s f = some (t, r)` at a
verified registry, under the run binders `hp63`, `hax`, `hop5`:
1. every good coin ACCEPTS the honest message and traces (`AcceptsJ8V`, the claim `(s, f, r)`, the registry `Rg.R`);
2. `Pr_χ[¬ Good] ≤ ε_c`;
3. the honest traces are staged (`StJ8`);
4. the claim holds (`HoldsN (s, f, r)`, from `genX_sound` at the verified registry);
5. at Goldilocks (`p = Nock.Atoms.p`, `|K| = cK`) with every table `≤ 2^31` rows: `ε_c < 2^-120`, and some coin
   accepts (non-vacuity). -/
theorem complJ8_of_obligations (B : HonestJ8 p K δ Rg fuel s f r) (O : ComplJ8Obligations δ b B)
    (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p B.t) (hop5 : ProgOp5OK p B.t) (hleaf : ProgLeafOK B.t) :
    (∀ χ, B.Good χ → AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  refine ⟨fun χ hχ => honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ,
    probJ8_notGood_le δ b B O, O.staged, genX_sound Rg.faithful B.hgen, fun hpG hcK hrows => ?_⟩
  have hfig := O.fig hpG hcK hrows
  have h1 : B.epsC < 1 := lt_trans hfig (by norm_num)
  obtain ⟨χ, hχ⟩ := exists_good δ b B O h1
  exact ⟨hfig, χ, honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ⟩

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
