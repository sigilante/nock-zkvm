/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean

  **Layout** (MEASURED `widthHX = 123` by `rfl`):

  | cols | group |
  |---|---|
  | `0..16`   | `StateX` one-hot: `OP_0..OP_9`, `cons` (10), `s10` 11, `s10L` 12, `s10T` 13, `s11s` 14, `s11d` 15, `s11j` 16 |
  | `17, 18`  | `isFirst`, `isLast` (verifier preprocessing) |
  | `25..48`  | 12 handles `(k, v)`: `s f e sf1 sf2 f_h f_t f_th f_tt f_tth f_ttt m` (`k` = WIRE kind `0/1/2`) |
  | `49..60`  | `kb` per handle (`k = kc + 2·kb`, `kc := k − 2·kb`) |
  | `61, 62`  | `fast`, `inv4` (op 4) |
  | `63..68`  | α second pair: `ax2`, `pr2`, `l₁ = (65, 66)`, `l₂ = (67, 68)` |
  | `69..92`  | 4 slot inverses over `𝕂′` (Re / Im, 3 limbs each): `inv0 69/72`, `inv1 75/78`, `inv2 81/84`, `inv3 87/90` |
  | `93..110` | 3 accumulators over `𝕂′`: export `93/96`, path `99/102`, SERVICE `105/108` |
  | `111..122`| compute walk `ln, count, acc, walk_inv` (`𝕂`) |

  **Deviation from SPEC §3.5 (124):** the α pair needs no `w2`: the pair's `≠` is the EXISTING
  `neGate` on the atom-only copies `v := l₁.v` (when `l₁.k = 0`) and `v2 := l₂.v` (when `l₂.k = 0`),
  which are free exactly when the pair is active (both leaves big ⇒ their own `v` copies are off).
  Hence `124 − 1 = 123`.

  **Kinds.** The handle `k` column is the wire kind of the records (unchanged keys); `kb` is new and
  `kc := k − 2·kb` is an expression.  Gates `kb² = kb`, `kc² = kc`, `kc·kb = 0` (12 × 3, degree 2).
  The "small atom" selector `notC kc · notC kb` is written in its linear form `1 − k + kb` (equal
  under `kc·kb = 0`), which keeps every copy gate at degree `≤ 4`.  Handle equality over
  `(kc, kb, v)` is `heq` over `(k, v)` (`k ∈ {0,1,2}` determines `(kc, kb)`).

  **ONE service accumulator** consumes the three record kinds.

  Record shapes match the LANDED providers: `incRec = (sf1.k, sf1.v, e.k, e.v, 4)` (A-2
  `AtomChipHQ.incKey`, `TAG_inc = 4` LAST), `jetRec = (3, id, h_c, h_S, h_E)` (J-3b
  `ChipJ8.keyJet`, `TAG_jet = 3` LAST since C-2 step 0), `walkRecA = (rootIdx, ax2, k_b, v_b)` (AW).
  The tag now sits in
  position 7 on both sides, and `serviceKeys_disjoint` proves the inc, `walkRecA` and jet keys are
  pairwise distinct polynomials in `γ` for ALL handle values.

  NOT here: `LocalVSX` / soundness (C-2), the frame
  wiring of the service terminal (J-8a), honest fill (J-8b).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
import Nock.Jet.Wild

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipHX

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.Framework

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Layout -/

/-- `StateX` selector columns (`E-0` numbering). -/
def sS10 : ℕ := 11
def sS10L : ℕ := 12
def sS10T : ℕ := 13
def sS11s : ℕ := 14
def sS11d : ℕ := 15
def sS11j : ℕ := 16
def nStates : ℕ := 17

def firstX : ℕ := 17
def lastX : ℕ := 18
def z1X : ℕ := 19
def vX : ℕ := 20
def betaX : ℕ := 21
def v2X : ℕ := 22
def wX : ℕ := 23
def prX : ℕ := 24

def hdX (j : ℕ) : Hd := ⟨25 + 2 * j, 26 + 2 * j⟩

def xS : Hd := hdX 0
def xF : Hd := hdX 1
def xE : Hd := hdX 2
def xSf1 : Hd := hdX 3
def xSf2 : Hd := hdX 4
def xFh : Hd := hdX 5
def xFt : Hd := hdX 6
def xFth : Hd := hdX 7
def xFtt : Hd := hdX 8
def xFtth : Hd := hdX 9
def xFttt : Hd := hdX 10
def xM : Hd := hdX 11

def allHandlesX : List Hd := (List.range 12).map hdX

/-- The `kb` column of a handle `hdX j` is `49 + j`. -/
def kbX (h : Hd) : ℕ := 49 + (h.k - 25) / 2

def fastX : ℕ := 61
def inv4X : ℕ := 62
def ax2X : ℕ := 63
def pr2X : ℕ := 64
def xL1 : Hd := ⟨65, 66⟩
def xL2 : Hd := ⟨67, 68⟩

/-- Round-0 width (B0): everything above. -/
def round0WX : ℕ := 69

def inv0X : ℕ := 69
def inv0Xi : ℕ := 72
def inv1X : ℕ := 75
def inv1Xi : ℕ := 78
def inv2X : ℕ := 81
def inv2Xi : ℕ := 84
def inv3X : ℕ := 87
def inv3Xi : ℕ := 90
def accXX : ℕ := 93
def accXXi : ℕ := 96
def accPX : ℕ := 99
def accPXi : ℕ := 102
def accSX : ℕ := 105
def accSXi : ℕ := 108
def wLnX : ℕ := 111
def wCntX : ℕ := 114
def wAccX : ℕ := 117
def wInvX : ℕ := 120

/-- **The J-8 compute chip's width.** -/
def widthHX : ℕ := 123

theorem widthHX_eq : widthHX = widthHQ + 6 + 12 + 2 + 6 + 6 + 6 := rfl

theorem widthHX_val : widthHX = 123 := rfl

/-- The layout tiles `0.. 123`. -/
theorem layoutX_tiles :
    hdX 0 = ⟨25, 26⟩ ∧ hdX 11 = ⟨47, 48⟩ ∧ (allHandlesX.map kbX) = (List.range 12).map (49 + ·) ∧
    49 + 12 = fastX ∧ fastX + 1 = inv4X ∧ inv4X + 1 = ax2X ∧ ax2X + 1 = pr2X ∧ pr2X + 1 = xL1.k ∧
    xL1.v + 1 = xL2.k ∧ xL2.v + 1 = round0WX ∧ round0WX = inv0X ∧
    inv0X + 3 = inv0Xi ∧ inv0Xi + 3 = inv1X ∧ inv1X + 3 = inv1Xi ∧ inv1Xi + 3 = inv2X ∧
    inv2X + 3 = inv2Xi ∧ inv2Xi + 3 = inv3X ∧ inv3X + 3 = inv3Xi ∧ inv3Xi + 3 = accXX ∧
    accXX + 3 = accXXi ∧ accXXi + 3 = accPX ∧ accPX + 3 = accPXi ∧ accPXi + 3 = accSX ∧
    accSX + 3 = accSXi ∧ accSXi + 3 = wLnX ∧ wLnX + 3 = wCntX ∧ wCntX + 3 = wAccX ∧
    wAccX + 3 = wInvX ∧ wInvX + 3 = widthHX ∧
    (allHandlesX.map Hd.k ++ allHandlesX.map Hd.v ++ allHandlesX.map kbX).Nodup := by
  decide

/-- Publics: `0..5` claim handles, `6/9/12` walk, export `15/21`, path `18/24`, service `27/30`
(Re / Im). -/
def pubRhoSX : ℕ := 27
def pubRhoSXi : ℕ := 30

/-- **The serial-capable columns**: every handle value column, plus the α pair's record values
(`v_b` is a suffix row index when `k_b = 1`). -/
def serialColsX : List ℕ := allHandlesX.map Hd.v ++ [xL1.v, xL2.v]

/-! ## 2. Base-field building blocks -/

section Base
variable {F : Type} [Field F]

def kbE (h : Hd) : CoeffExpr F := cc (kbX h)
/-- `kc := k − 2·kb`. -/
def kcE (h : Hd) : CoeffExpr F := .sub (cc h.k) (.mul (.const 2) (kbE h))
/-- The "small atom" selector `(1 − kc)(1 − kb)` in its linear form `1 − k + kb`. -/
def smallE (h : Hd) : CoeffExpr F := .add (.sub (.const 1) (cc h.k)) (kbE h)
def boolG (x : CoeffExpr F) : CoeffExpr F := .mul x (.sub x (.const 1))
def oneMinus (x : CoeffExpr F) : CoeffExpr F := .sub (.const 1) x

end Base

/-! ## 3. Base gates by arm (serial-free arithmetic) -/

section Gates
variable {F : Type} [Field F]

/-- One-hot over `0..16`, `z1`, `β`, `fast`, `l₁.k`, `l₂.k` booleanity. -/
def oneHotG : List (CoeffExpr F) :=
  ((List.range nStates).map fun j => boolG (cc j)) ++
  [.sub (selS (List.range nStates)) (.const 1), boolG (cc z1X), boolG (cc betaX), boolG (cc fastX),
   boolG (cc xL1.k), boolG (cc xL2.k)]

/-- **The `kb` split** (SPEC §3.2): `kb`, `kc` boolean and `kc·kb = 0`, per handle. -/
def kindG : List (CoeffExpr F) :=
  allHandlesX.flatMap fun h => [boolG (kbE h), boolG (kcE h), .mul (kcE h) (kbE h)]

def l2X : List ℕ := [2, 5, 6, 7, 8, 9, 11, 14, 15, 16]
/-- `f_th` is decoded on `s10, s11d, s11j` (the shared `slot2` entry). -/
def l3X : List ℕ := [11, 15, 16]

/-- SV and the decode-parent kinds. -/
def svG : List (CoeffExpr F) :=
  [.sub (cc consCol) (kcE xFh),
   .add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T),
   kbE xFh,
   .mul (selS l2X) (oneMinus (kcE xFt)),
   .mul (cc 6) (oneMinus (kcE xFtt)),
   .mul (selS l3X) (oneMinus (kcE xFth))]

def op0G : List (CoeffExpr F) :=
  [.mul (cc 0) (cc xFt.k),
   prodL [cc 0, notC z1X, oneMinus (kcE xS)],
   prodL [cc 0, cc z1X, .sub (cc vX) (.const 1)]]

def op3G : List (CoeffExpr F) :=
  [.mul (cc 3) (cc xE.k),
   .mul (cc 3) (.add (.sub (cc betaX) (.const 1)) (kcE xSf1))]

/-- **op 4** (SPEC §3.3): fast `s4·fast·(v2·inv4 − 1)`, `fast ⇒ sf1.kb = e.kb = 0`, `v2 = v + 1`;
slow `s4·(1−fast)·(1−sf1.kb)·v2 = 0` (small & slow ⇒ `v = p − 1`), `s4·(1−fast)·(1−e.kb) = 0`. -/
def op4G : List (CoeffExpr F) :=
  [.mul (cc 4) (kcE xSf1),
   .mul (cc 4) (kcE xE),
   .mul (cc 4) (.sub (.sub (cc v2X) (cc vX)) (.const 1)),
   prodL [cc 4, cc fastX, .sub (.mul (cc v2X) (cc inv4X)) (.const 1)],
   prodL [cc 4, cc fastX, kbE xSf1],
   prodL [cc 4, cc fastX, kbE xE],
   prodL [cc 4, notC fastX, oneMinus (kbE xSf1), cc v2X],
   prodL [cc 4, notC fastX, oneMinus (kbE xE)]]

/-- `neGate` over `(kc, kb, v)`: `s5·β·((Δkc)² + (Δkb)² + (v − v2)·w − 1)`. -/
def neGateX : CoeffExpr F :=
  .mul (prodL [cc 5, cc betaX])
    (.sub (.add (.add (.pow (.sub (kcE xFtth) (kcE xFttt)) 2) (.pow (.sub (kbE xFtth) (kbE xFttt)) 2))
      (.mul (.sub (cc vX) (cc v2X)) (cc wX))) (.const 1))

/-- `pr − s5·β·(1 − z1) − s10L`. -/
def prGateX : CoeffExpr F := .sub (.sub (cc prX) (prodL [cc 5, cc betaX, notC z1X])) (cc sS10L)

/-- `pr2 − s5·β·kb(f_tth)·kb(f_ttt)`. -/
def pr2GateX : CoeffExpr F := .sub (cc pr2X) (prodL [cc 5, cc betaX, kbE xFtth, kbE xFttt])

def op5G : List (CoeffExpr F) :=
  [.mul (cc 5) (cc xE.k),
   prodL [cc 5, cc betaX, kcE xFtth, kcE xFttt],
   neGateX, prGateX,
   .mul (cc prX) (cc xM.k),
   .mul (cc prX) (oneMinus (kcE xSf1)),
   .mul (cc prX) (oneMinus (kcE xSf2)),
   pr2GateX,
   prodL [cc pr2X, cc xL1.k, cc xL2.k]]

def op6G : List (CoeffExpr F) :=
  [.mul (cc 6) (cc xSf2.k), prodL [cc 6, cc vX, .sub (cc vX) (.const 1)]]

def op8G : List (CoeffExpr F) := [.mul (cc 8) (oneMinus (kcE xM))]

def op9G : List (CoeffExpr F) :=
  [.mul (cc 9) (cc xFth.k),
   prodL [cc 9, notC z1X, oneMinus (kcE xSf1)],
   prodL [cc 9, cc z1X, .sub (cc vX) (.const 1)]]

def consG : List (CoeffExpr F) := [.mul (cc consCol) (oneMinus (kcE xE))]

/-- **op 10, `s10`**: the axis atom is small; `z1` (axis 1) case; the read of `e` needs a cell. -/
def s10G : List (CoeffExpr F) :=
  [.mul (cc sS10) (cc xFtth.k),
   prodL [cc sS10, cc z1X, .sub (cc vX) (.const 1)],
   prodL [cc sS10, notC z1X, oneMinus (kcE xE)]]

/-- **op 10, `s10L`** (on the atom-only copy `v2 := a_k`, `ax2 :=` the sibling axis):
`a_k = 2v + β`, `a_k ≠ 1`, `ax2 = a_k + 1 − 2β`. -/
def s10LG : List (CoeffExpr F) :=
  [.mul (cc sS10L) (.sub (.sub (cc v2X) (.mul (.const 2) (cc vX))) (cc betaX)),
   .mul (cc sS10L) (.sub (.mul (.sub (cc v2X) (.const 1)) (cc wX)) (.const 1)),
   .mul (cc sS10L) (.add (.sub (.sub (cc ax2X) (cc v2X)) (.const 1)) (.mul (.const 2) (cc betaX)))]

/-- **op 11**: `s11s` static (atom tag); `s11j`: the tag `f_tth` is a small atom (its VALUE is
pinned to `%wild` in `svEq`), and the jet key, the clue's value `sf1`, is a small atom.
(`s11d`/`s11j` decode-parent kinds sit in `svG`.) -/
def s11G : List (CoeffExpr F) :=
  [.mul (cc sS11s) (kcE xFth),
   .mul (cc sS11j) (cc xFtth.k),
   .mul (cc sS11j) (cc xSf1.k)]

def kidFormsX : List (ℕ × Hd) :=
  [(2, xFth), (2, xFtt), (2, xSf2), (3, xFt), (4, xFt), (5, xFth), (5, xFtt), (6, xM), (6, xFth),
   (7, xFtt), (7, xFth), (8, xFtt), (8, xFth), (9, xFtt), (9, xM), (consCol, xFh), (consCol, xFt),
   (sS10, xFttt), (sS10, xFtt), (sS11s, xFtt), (sS11d, xFttt), (sS11d, xFtt), (sS11j, xFttt)]

/-- **The kid-kind gates** `st · (1 − kc(h)) = 0` on every real-child formula handle (degree 2, no
column, no coin).  A chain pseudo-row has an ATOM formula, so it can no longer serve a real child. -/
def kidKindG : List (CoeffExpr F) := kidFormsX.map fun jh => .mul (cc jh.1) (oneMinus (kcE jh.2))

/-- **Serial-free arithmetic gates.** -/
def arithGatesX : List (CoeffExpr F) :=
  oneHotG ++ kindG ++ svG ++ op0G ++ op3G ++ op4G ++ op5G ++ op6G ++ op8G ++ op9G ++ consG ++
    s10G ++ s10LG ++ s11G ++ kidKindG

/-! ### Equality tests (the only base gates that read a handle value) -/

def svEq : List (EqG F) :=
  ((List.range 10).map fun j => ⟨cc j, xFh.v, .cst (j : F)⟩) ++
  [⟨cc sS10, xFh.v, .cst 10⟩, ⟨cc sS11s, xFh.v, .cst 11⟩, ⟨cc sS11d, xFh.v, .cst 11⟩,
   ⟨cc sS11j, xFh.v, .cst 11⟩, ⟨cc sS11j, xFtth.v, .cst (Nock.Jet.wildTag : F)⟩]

def op0Eq : List (EqG F) := [⟨cc 0, vX, .col xFt.v⟩] ++ heq (.mul (cc 0) (cc z1X)) xE xS
def op1Eq : List (EqG F) := heq (cc 1) xE xFt
def op3Eq : List (EqG F) := [⟨cc 3, xE.v, .col betaX⟩]
def op4Eq : List (EqG F) :=
  [⟨.mul (cc 4) (oneMinus (kbE xSf1)), vX, .col xSf1.v⟩, ⟨.mul (cc 4) (cc fastX), xE.v, .col v2X⟩]
def op5Eq : List (EqG F) :=
  [⟨cc 5, xE.v, .col betaX⟩] ++ heq (prodL [cc 5, notC betaX]) xSf1 xSf2 ++
  heq (prodL [cc 5, cc betaX, cc z1X]) xFtth xSf1 ++ heq (prodL [cc 5, cc betaX, cc z1X]) xFttt xSf2 ++
  [⟨prodL [cc 5, cc betaX, smallE xFtth], vX, .col xFtth.v⟩,
   ⟨prodL [cc 5, cc betaX, smallE xFttt], v2X, .col xFttt.v⟩,
   ⟨.mul (cc pr2X) (notC xL1.k), vX, .col xL1.v⟩,
   ⟨.mul (cc pr2X) (notC xL2.k), v2X, .col xL2.v⟩]
def op6Eq : List (EqG F) :=
  [⟨cc 6, vX, .col xSf2.v⟩] ++ heq (.mul (cc 6) (notC vX)) xM xFtth ++ heq (.mul (cc 6) (cc vX)) xM xFttt ++
  heq (cc 6) xE xSf1
def op78Eq : List (EqG F) := heq (cc 7) xE xSf1 ++ heq (cc 8) xE xSf1
def op9Eq : List (EqG F) :=
  [⟨cc 9, vX, .col xFth.v⟩] ++ heq (.mul (cc 9) (cc z1X)) xM xSf1 ++ heq (cc 9) xE xSf2
def s10Eq : List (EqG F) := [⟨cc sS10, vX, .col xFtth.v⟩] ++ heq (.mul (cc sS10) (cc z1X)) xE xSf1
def s10LEq : List (EqG F) :=
  [⟨cc sS10L, v2X, .col xF.v⟩, ⟨cc sS10L, xM.v, .col ax2X⟩] ++
  heq (cc sS10L) xSf1 xS ++ heq (cc sS10L) xSf2 xE ++ heq (cc sS10L) xFtth xFttt
def s10TEq : List (EqG F) := [⟨cc sS10T, xF.v, .cst 1⟩]
def claimEq : List (EqG F) :=
  hpub (cc firstX) xS 0 1 ++ hpub (cc firstX) xF 2 3 ++ hpub (cc firstX) xE 4 5

def eqGatesX : List (EqG F) :=
  svEq ++ op0Eq ++ op1Eq ++ op3Eq ++ op4Eq ++ op5Eq ++ op6Eq ++ op78Eq ++ op9Eq ++ s10Eq ++
    s10LEq ++ s10TEq ++ claimEq

end Gates

/-! ## 4. Records, slots, balances -/

/-- A record entry: a column or a constant (a tag). -/
inductive RE where
  | col (i : ℕ)
  | k (c : ℕ)
deriving DecidableEq, Repr

/-- The three balances under the handle coins: cell export, walk path, SERVICE. -/
inductive Bal where
  | x | p | s
deriving DecidableEq, Repr

def recOf (l : List ℕ) : List RE := l.map RE.col

def cellRecX (p l r : Hd) : List RE := recOf (cellRec p l r)
def walkRecX (root : Hd) (axis : ℕ) (ch : Hd) : List RE := recOf (walkRec root axis ch)
/-- A-2 `incKey`: `(old.k, old.v, new.k, new.v, TAG_inc = 4)`. -/
def incRecX : List RE := [.col xSf1.k, .col xSf1.v, .col xE.k, .col xE.v, .k 4]
/-- J-3b `keyJet` (C-2 step 0 order): `(id, h_c, h_S, h_E, TAG_jet = 3)`, the tag LAST.  The `id`
is the VALUE of the clue, `sf1.v` (a small atom by `s11G`), not the hint's tag. -/
def jetRecX : List RE :=
  [.col xSf1.v, .col xFtt.k, .col xFtt.v, .col xS.k, .col xS.v, .col xE.k, .col xE.v, .k 3]
/-- AW `walkRecA` at the first-difference leaves: `(rootIdx, ax2, k_b, v_b)`. -/
def walkRecAX (root : Hd) (l : Hd) : List RE := [.col root.v, .col ax2X, .col l.k, .col l.v]

section Slots
variable {F : Type} [Field F]

structure EntX (F : Type) where
  states : List ℕ
  extra : CoeffExpr F
  rcd : List RE
  bal : Bal

def EntX.act (x : EntX F) : CoeffExpr F := .mul (selS x.states) x.extra

/-- A slot: one `𝕂′` inverse (Re `inv`, Im `invIm`); optionally a batched PAIR under a flag column. -/
structure SlotX (F : Type) where
  inv : ℕ
  invIm : ℕ
  ents : List (EntX F)
  pair : Option (ℕ × List RE × List RE × Bal)
  pairStates : List ℕ

/-- The non-chain states (`f` is a cell). -/
def opStatesX : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16]

def slot0X : SlotX F := ⟨inv0X, inv0Xi, [⟨opStatesX, .const 1, cellRecX xF xFh xFt, .x⟩], none, []⟩

def slot1X : SlotX F :=
  ⟨inv1X, inv1Xi,
    [⟨l2X, .const 1, cellRecX xFt xFth xFtt, .x⟩,
     ⟨[0], notC z1X, walkRecX xS xFt.v xE, .p⟩,
     ⟨[4], notC fastX, incRecX, .s⟩], none, []⟩

def slot2X : SlotX F :=
  ⟨inv2X, inv2Xi,
    [⟨[6], .const 1, cellRecX xFtt xFtth xFttt, .x⟩,
     ⟨[9], notC z1X, walkRecX xSf1 xFth.v xM, .p⟩,
     ⟨[consCol], .const 1, cellRecX xE xSf1 xSf2, .x⟩,
     ⟨[8], .const 1, cellRecX xM xSf2 xS, .x⟩,
     ⟨[3], kcE xSf1, cellRecX xSf1 xFtth xFttt, .x⟩,
     ⟨l3X, .const 1, cellRecX xFth xFtth xFttt, .x⟩],
    some (prX, walkRecX xSf1 xM.v xFtth, walkRecX xSf2 xM.v xFttt, .p), [5, 12]⟩

/-- **`inv3`**, the fourth slot: `s10` read `slot a e = new`, the `s11j` jet consume, the α pair. -/
def slot3X : SlotX F :=
  ⟨inv3X, inv3Xi,
    [⟨[sS10], notC z1X, walkRecX xE vX xSf1, .p⟩,
     ⟨[sS11j], .const 1, jetRecX, .s⟩],
    some (pr2X, walkRecAX xFtth xL1, walkRecAX xFttt xL2, .s), [5]⟩

def slotsX : List (SlotX F) := [slot0X, slot1X, slot2X, slot3X]

/-- The activity of a slot into balance `b`. -/
def SlotX.actB (S : SlotX F) (b : Bal) : CoeffExpr F :=
  .add (CoeffExpr.sumList (S.ents.filter fun x => decide (x.bal = b)) EntX.act)
    (match S.pair with
     | some (fl, _, _, b') => if b' = b then cc fl else .const 0
     | none => .const 0)

end Slots

/-! ## 5. The accumulators (at `isFirst = 17`, `isLast = 18`) -/

section Acc
variable {F : Type} [Field F]

def accInitX (accBase k : ℕ) : CoeffExpr F := .mul (cc firstX) (cc (accBase + k))

def accStepX (slots : List (Slot F)) (accBase k : ℕ) : CoeffExpr F :=
  .mul (notC lastX) (.sub (.sub (.var .traceNext (accBase + k)) (cc (accBase + k))) (termCoord slots k))

def accTermX (slots : List (Slot F)) (accBase pubBase k : ℕ) : CoeffExpr F :=
  .mul (cc lastX) (.sub (.add (cc (accBase + k)) (termCoord slots k)) (.var .publicVal (pubBase + k)))

/-- `LogUp.accGates 3` with the preprocessing masks at `17 / 18`. -/
def accGatesX (slots : List (Slot F)) (accBase pubBase : ℕ) : List (CoeffExpr F) :=
  (List.range 3).map (accInitX accBase) ++ (List.range 3).map (accStepX slots accBase) ++
    (List.range 3).map (accTermX slots accBase pubBase)

def accOf (b : Bal) (im : Bool) (accBase pubBase : ℕ) : List (CoeffExpr F) :=
  accGatesX (slotsX.map fun S => ⟨S.actB b, if im then S.invIm else S.inv⟩) accBase pubBase

/-- **The three `𝕂′` accumulators** (export, path, SERVICE), Re and Im. -/
def accGatesHX : List (CoeffExpr F) :=
  accOf .x false accXX pubRhoX ++ accOf .x true accXXi pubRhoXIm ++
  accOf .p false accPX pubRhoP ++ accOf .p true accPXi pubRhoPIm ++
  accOf .s false accSX pubRhoSX ++ accOf .s true accSXi pubRhoSXi

/-- **Base gates** (generic builder). -/
def baseGatesHX : List (CoeffExpr F) := arithGatesX ++ accGatesHX ++ eqGatesX.map EqG.gate

end Acc

/-! ## 6. The `𝕂′` slot gates -/

section Q
variable (F : Type) [Field F]

def RE.q : RE → Q F
  | .col i => qlift F (cc i)
  | .k c => qconst F (c : ℤ)

def rlcKeyQX (δ : F) : ℕ → List RE → Q F
  | _, [] => qconst F 0
  | n, x :: r => qadd F (qmul F δ (qpow F δ (qγH F) n) (x.q F)) (rlcKeyQX δ (n + 1) r)

def denQX (δ : F) (r : List RE) : Q F := qadd F (qρH F) (rlcKeyQX F δ 0 r)

/-- **The slot gate over `𝕂′`** (as `ChipHQ.slotGateQ`, with an explicit Im column and tagged
records). -/
def slotGateQX (δ : F) (S : SlotX F) : Q F :=
  qsub F (qmul F δ (qvar F .traceCur S.inv (some S.invIm))
      (qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd)))
        (match S.pair with
         | some (fl, a, b, _) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQX F δ a) (denQX F δ b))
         | none => qconst F 0)))
    (qadd F (qlift F (CoeffExpr.sumList S.ents EntX.act))
      (match S.pair with
       | some (fl, a, b, _) => qmul F δ (qlift F (cc fl)) (qadd F (denQX F δ a) (denQX F δ b))
       | none => qconst F 0))

def slotPairsX (δ : F) : List (Q F) := (slotsX (F := F)).map (slotGateQX F δ)

end Q

/-! ## 7. The compute walk over handle labels, 17 states -/

section Walk
variable {F : Type} [Field F]

/-- A label entry: a column, or `none` for a constant-zero coordinate (an atom formula's kind). -/
def rlcKeyL (kind : VarKind) (γ : ℕ) : ℕ → List (Option ℕ) → MixedExpr F
  | _, [] => .Const 0
  | n, none :: r => rlcKeyL kind γ (n + 1) r
  | n, some i :: r =>
      .Add (.Mul (.Pow (.Var .challenge γ) n) (.Lift (.var kind i))) (rlcKeyL kind γ (n + 1) r)

def labX (s f e : Hd) : List (Option ℕ) := [some s.k, some s.v, some f.k, some f.v, some e.k, some e.v]
/-- A child with the ATOM formula `(0, fv)` (the chain level `a_k / 2`). -/
def labAtom (s : Hd) (fv : ℕ) (e : Hd) : List (Option ℕ) :=
  [some s.k, some s.v, none, some fv, some e.k, some e.v]

def labelColsX : List (Option ℕ) := labX xS xF xE

def childrenX : ℕ → List (List (Option ℕ))
  | 2 => [labX xS xFth xSf1, labX xS xFtt xSf2, labX xSf1 xSf2 xE]
  | 3 => [labX xS xFt xSf1]
  | 4 => [labX xS xFt xSf1]
  | 5 => [labX xS xFth xSf1, labX xS xFtt xSf2]
  | 6 => [labX xS xM xSf1, labX xS xFth xSf2]
  | 7 => [labX xSf2 xFtt xSf1, labX xS xFth xSf2]
  | 8 => [labX xM xFtt xSf1, labX xS xFth xSf2]
  | 9 => [labX xS xFtt xSf1, labX xSf1 xM xSf2]
  | 10 => [labX xS xFh xSf1, labX xS xFt xSf2]
  | 11 => [labX xS xFttt xSf1, labX xS xFtt xSf2, labX xSf2 xFtth xE]
  | 12 => [labAtom xS vX xE]
  | 14 => [labX xS xFtt xE]
  | 15 => [labX xS xFttt xSf1, labX xS xFtt xE]
  | 16 => [labX xS xFttt xSf1]
  | _ => []

def allStatesX : List ℕ := List.range nStates

def curLX (kind : VarKind) : MixedExpr F := rlcKeyL kind chalGammaW 0 labelColsX

def childSumX (kind : VarKind) (st : ℕ) : MixedExpr F :=
  sumM (((childrenX st).zipIdx).map fun p =>
    .Mul (.Pow (.Var .challenge chalAlphaW) (p.2 + 1)) (rlcKeyL kind chalGammaW 0 p.1))

def ccLX (kind : VarKind) : MixedExpr F :=
  sumM (allStatesX.map fun st => .Scale (kv kind st) (childSumX kind st))

def cmLX (kind : VarKind) : MixedExpr F :=
  sumM (allStatesX.map fun st => .Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (childrenX st).length))

/-- **The walk gates** (as `ChipH.walkGates`, at the shifted columns and the 17 states). -/
def walkGatesX : List (MixedExpr F) :=
  let αW : MixedExpr F := .Var .challenge chalAlphaW
  let lnC := wv .traceCur wLnX; let lnN := wv .traceNext wLnX
  let cnC := wv .traceCur wCntX; let cnN := wv .traceNext wCntX
  let acC := wv .traceCur wAccX; let acN := wv .traceNext wAccX
  [.Scale (notC lastX) (.Sub lnN (.Mul αW lnC)),
   .Scale (notC lastX) (.Sub cnN (.Mul cnC (cmLX .traceNext))),
   .Scale (notC lastX) (.Sub (.Sub (.Add (.Mul lnN (curLX .traceNext)) acN) acC) (.Mul cnC (ccLX .traceNext))),
   .Scale (cc firstX) (.Sub lnC αW),
   .Scale (cc firstX) (.Sub cnC (.Mul (.Var .publicVal pubIC) (cmLX .traceCur))),
   .Scale (cc firstX) (.Sub (.Add (.Mul lnC (curLX .traceCur)) acC)
      (.Add (.Mul (.Var .publicVal pubIC) (ccLX .traceCur)) (.Var .publicVal pubSeed))),
   .Scale (notC lastX) (.Sub (.Mul (wv .traceCur wInvX) (.Sub cnC lnC)) (.Const 1)),
   .Scale (cc lastX) (.Sub cnC lnC),
   .Scale (cc lastX) (.Sub acC (.Var .publicVal pubOut))]

/-- The fanouts of the new states (SPEC §3.1 table). -/
theorem fanoutX_new :
    ((childrenX 11).length, (childrenX 12).length, (childrenX 13).length, (childrenX 14).length,
      (childrenX 15).length, (childrenX 16).length) = (3, 1, 0, 1, 2, 1) := rfl

end Walk

/-! ## 8. The gate list -/

section Assemble
variable {F K : Type} [Field F] [Field K] [Algebra F K]

def baseGatesFX : List (CoeffExpr F) := (baseGatesHX (F := ℚ)).map (mapC (fun q : ℚ => (q : F)))

def walkGatesFX : List (MixedExpr F) := (walkGatesX (F := ℚ)).map (mapM (fun q : ℚ => (q : F)))

/-- **The gates of `computeChipVCLHX`**: base, the four `𝕂′` slot pairs (`6` coordinate gates
each), the compiled walk gates. -/
def gatesHX (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  baseGatesFX ++ (slotPairsX F δ).flatMap (qGates b) ++
    (walkGatesFX (F := F)).flatMap fun g => List.ofFn (mixedCompile b col0Id g)

end Assemble

/-! ## 9. Degree -/

section Degree
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem baseTemplateX_degree :
    ((baseGatesHX (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem walkTemplateX_degree :
    ((walkGatesX (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem baseGatesFX_degree : ∀ g ∈ (baseGatesFX : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapC]
  simpa using List.all_eq_true.mp baseTemplateX_degree t ht

theorem walkGatesFX_degree : ∀ g ∈ (walkGatesFX : List (MixedExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapM]
  simpa using List.all_eq_true.mp walkTemplateX_degree t ht

theorem qdeg_REq (x : RE) : qdeg F (x.q F) ≤ 1 := by
  cases x with
  | col i => exact (qdeg_qlift_le F (cc i)).trans (by simp [cc, CoeffExpr.degree])
  | k c => rw [RE.q, qdeg_qconst0]; omega

theorem qdeg_rlcKeyQX (δ : F) : ∀ (r : List RE) (n : ℕ), qdeg F (rlcKeyQX F δ n r) ≤ 1
  | [], n => by rw [rlcKeyQX, qdeg_qconst0]; omega
  | x :: r, n => by
      rw [rlcKeyQX]
      refine (qdeg_qadd F _ _).trans (max_le ?_ (qdeg_rlcKeyQX δ r (n + 1)))
      refine (qdeg_qmul F δ _ _).trans ?_
      have h1 := (qdeg_qpow F δ (qγH F) n).trans (by rw [qdeg_qγH]; omega : n * qdeg F (qγH F) ≤ 0)
      have h2 := qdeg_REq (F := F) x
      omega

theorem qdeg_denQX (δ : F) (r : List RE) : qdeg F (denQX F δ r) ≤ 1 :=
  (qdeg_qadd F _ _).trans (max_le (by rw [qdeg_qρH]; omega) (qdeg_rlcKeyQX δ r 0))

/-- A slot pair has degree `≤ 4` when its activities have degree `≤ 2`. -/
theorem slotGateQX_deg (δ : F) (S : SlotX F) (hact : ∀ x ∈ S.ents, x.act.degree ≤ 2) :
    qdeg F (slotGateQX F δ S) ≤ 4 := by
  have hinv : qdeg F (qvar F .traceCur S.inv (some S.invIm)) ≤ 1 := by
    rw [qdeg_qvar]; simp [MixedExpr.degree]
  have hs : qdeg F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))) ≤ 3 := by
    refine qdeg_sumQ _ 3 fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    have := (qdeg_qlift_le F x.act).trans (hact x hx)
    have := qdeg_denQX δ x.rcd
    exact (qdeg_qmul F δ _ _).trans (by omega)
  have hsum : qdeg F (qlift F (CoeffExpr.sumList S.ents EntX.act)) ≤ 2 :=
    (qdeg_qlift_le F _).trans (CoeffExpr.degree_sumList_le _ _ _ hact)
  have hfl : ∀ fl : ℕ, qdeg F (qlift F (cc fl)) ≤ 1 := fun fl =>
    (qdeg_qlift_le F (cc fl)).trans (by simp [cc, CoeffExpr.degree])
  have hp1 : qdeg F (match S.pair with
      | some (fl, a, b, _) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQX F δ a) (denQX F δ b))
      | none => qconst F 0) ≤ 3 := by
    rcases hp : S.pair with _ | ⟨fl, a, b, bb⟩
    · simp [qdeg_qconst0]
    · have hf := hfl fl
      have ha := qdeg_denQX δ a; have hb := qdeg_denQX δ b
      refine (qdeg_qmul F δ _ _).trans ?_
      have := qdeg_qmul F δ (denQX F δ a) (denQX F δ b)
      omega
  unfold slotGateQX
  refine (qdeg_qsub F _ _).trans (max_le ?_ ?_)
  · refine (qdeg_qmul F δ _ _).trans ?_
    have := (qdeg_qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))) _).trans
      (max_le hs hp1)
    omega
  · refine (qdeg_qadd F _ _).trans (max_le (hsum.trans (by omega)) ?_)
    rcases hp : S.pair with _ | ⟨fl, a, b, bb⟩
    · simp [qdeg_qconst0]
    · have hf := hfl fl
      have ha := qdeg_denQX δ a; have hb := qdeg_denQX δ b
      refine (qdeg_qmul F δ _ _).trans ?_
      have := qdeg_qadd F (denQX F δ a) (denQX F δ b)
      omega

theorem slotsX_act_deg : ∀ S ∈ (slotsX : List (SlotX F)), ∀ x ∈ S.ents, x.act.degree ≤ 2 := by
  intro S hS x hx
  simp only [slotsX, slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [EntX.act, selS, CoeffExpr.degree, notC, cc, CoeffExpr.degree_sumList_le, kcE, kbE,
      opStatesX, l2X, l3X]

theorem slotPairsX_degree (δ : F) : ∀ q ∈ slotPairsX F δ, qdeg F q ≤ 4 := by
  intro q hq
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
  exact slotGateQX_deg δ S (slotsX_act_deg S hS)

/-- **Degree `≤ 4` for every gate of the chip.** -/
theorem gatesHX_degree (b : Basis (Fin 3) F K) (δ : F) : ∀ g ∈ gatesHX b δ, g.degree ≤ 4 := by
  intro g hg
  simp only [gatesHX, List.mem_append, List.mem_flatMap, List.mem_ofFn] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, k, rfl⟩
  · exact baseGatesFX_degree g hg
  · have hd := slotPairsX_degree δ q hq
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact (mixedCompile_degree_le b _ q.1 k).trans (le_trans (le_max_left _ _) hd)
    · exact (mixedCompile_degree_le b _ q.2 k).trans (le_trans (le_max_right _ _) hd)
  · exact (mixedCompile_degree_le b _ m k).trans (walkGatesFX_degree m hm)

end Degree

/-! ## 10. -/

section Instrument
variable {F : Type} [Field F]

/-- **No serial-capable column is read** (at the J-8 layout). -/
def serialFreeX (g : CoeffExpr F) : Bool := (colsOf g).all fun i => !serialColsX.contains i

/-- `𝕂` discipline (`ChipH.keyOK` at the J-8 serial set). -/
def keyOKX : MixedExpr F → Bool
  | .Mul (.Pow (.Var .challenge _) _) (.Lift (.var _ _)) => true
  | .Var _ _ => true
  | .Lift g => serialFreeX g
  | .Scale g u => serialFreeX g && keyOKX u
  | .Const _ => true
  | .Add x y => keyOKX x && keyOKX y
  | .Sub x y => keyOKX x && keyOKX y
  | .Mul x y => keyOKX x && keyOKX y
  | .Neg x => keyOKX x
  | .Pow x _ => keyOKX x

/-- `𝕂′` discipline (`ChipHQ.keyOKQe` at the J-8 serial set). -/
def keyOKQXe : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => coinOnly x
  | .Var _ _ => true
  | .Lift g => serialFreeX g
  | .Scale g u => serialFreeX g && keyOKQXe u
  | .Const _ => true
  | .Add x y => keyOKQXe x && keyOKQXe y
  | .Sub x y => keyOKQXe x && keyOKQXe y
  | .Mul x y => keyOKQXe x && keyOKQXe y
  | .Neg x => keyOKQXe x
  | .Pow x _ => keyOKQXe x

def keyOKQX (q : Q F) : Bool := keyOKQXe q.1 && keyOKQXe q.2

/-- An equality test is well-formed: serial-free selector (the difference is the only serial read). -/
def EqG.okX (g : EqG F) : Bool := serialFreeX g.σ

theorem slotPairsX_keyOK : (slotPairsX ℚ 7).all keyOKQX = true := by decide +kernel

theorem walkGatesX_keyOK : (walkGatesX (F := ℚ)).all keyOKX = true := by decide +kernel

/-- Every arithmetic gate is serial-free (the `kb` split, op 4 fast/slow, the pair, `s10L`'s
parity on the atom-only copies). -/
theorem arithGatesX_serialFree : (arithGatesX (F := ℚ)).all serialFreeX = true := by decide +kernel

theorem accGatesHX_serialFree : (accGatesHX (F := ℚ)).all serialFreeX = true := by decide +kernel

theorem eqGatesX_ok : (eqGatesX (F := ℚ)).all EqG.okX = true := by decide +kernel

/-- **Positive control 1**: the instrument flags a pair multiplying a denominator by a serial. -/
theorem keyOKQX_flags : keyOKQX (qmul ℚ 7 (denQX ℚ 7 [.col xS.v]) (qlift ℚ (cc xS.v))) = false := by
  decide +kernel

/-- **Positive control 2**: the NAIVE α-pair `≠` (reading `l₁.v − l₂.v`) is flagged — why the pair
goes through the atom-only copies. -/
theorem serialFreeX_flags_naive_pair :
    serialFreeX (F := ℚ) (.mul (cc pr2X)
      (.sub (.add (.pow (.sub (cc xL1.k) (cc xL2.k)) 2) (.mul (.sub (cc xL1.v) (cc xL2.v)) (cc wX)))
        (.const 1))) = false := by decide +kernel

/-- **Positive control 3**: the NAIVE `s10L` parity on `f.v` is flagged. -/
theorem serialFreeX_flags_naive_s10L :
    serialFreeX (F := ℚ) (.mul (cc sS10L) (.sub (.sub (cc xF.v) (.mul (.const 2) (cc vX))) (cc betaX)))
      = false := by decide +kernel

/-- **Positive control 4**: the `𝕂` instrument flags a walk gate scaled by a serial. -/
theorem keyOKX_flags : keyOKX (F := ℚ) (.Scale (cc xE.v) (.Var .challenge 0)) = false := by
  decide +kernel

end Instrument

/-! ## 11. The read-set receipt -/

section ReadSet

/-- The records a row in state `st` consumes, with their balance (entries whose states contain
`st`, plus the slot's pair on its pair states). -/
def consumesX (st : ℕ) : List (List RE × Bal) :=
  (slotsX (F := ℚ)).flatMap fun S =>
    ((S.ents.filter fun x => decide (st ∈ x.states)).map fun x => (x.rcd, x.bal)) ++
      (if st ∈ S.pairStates then
        match S.pair with
        | some (_, a, b, bal) => [(a, bal), (b, bal)]
        | none => []
       else [])

/-- In every slot, the entries' and the pair's states are pairwise disjoint (so one inverse per
row serves at most one entry, or one pair). -/
theorem slotsX_disjoint :
    ((slotsX (F := ℚ)).all fun S => ((S.ents.flatMap EntX.states) ++ S.pairStates).Nodup) = true := by
  decide +kernel

theorem consumesX_op4 :
    consumesX 4 = [(cellRecX xF xFh xFt, .x), (incRecX, .s)] := by decide +kernel

theorem consumesX_op5 :
    consumesX 5 = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x),
      (walkRecX xSf1 xM.v xFtth, .p), (walkRecX xSf2 xM.v xFttt, .p),
      (walkRecAX xFtth xL1, .s), (walkRecAX xFttt xL2, .s)] := by decide +kernel

theorem consumesX_s10 :
    consumesX 11 = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x),
      (cellRecX xFth xFtth xFttt, .x), (walkRecX xE vX xSf1, .p)] := by decide +kernel

theorem consumesX_s10L :
    consumesX 12 = [(walkRecX xSf1 xM.v xFtth, .p), (walkRecX xSf2 xM.v xFttt, .p)] := by
  decide +kernel

theorem consumesX_s10T : consumesX 13 = [] := by decide +kernel

theorem consumesX_s11s :
    consumesX 14 = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x)] := by decide +kernel

theorem consumesX_s11d :
    consumesX 15 = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x),
      (cellRecX xFth xFtth xFttt, .x)] := by decide +kernel

theorem consumesX_s11j :
    consumesX 16 = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x),
      (cellRecX xFth xFtth xFttt, .x), (jetRecX, .s)] := by decide +kernel

/-- The SERVICE balance consumes exactly three record kinds: `TAG_inc` (op 4 slow), `TAG_jet`
(`s11j`), and the two `walkRecA` records of the α pair (op 5). -/
theorem service_consumers :
    ((List.range nStates).flatMap fun st =>
      ((consumesX st).filter fun r => decide (r.2 = .s)).map Prod.fst) =
      [incRecX, walkRecAX xFtth xL1, walkRecAX xFttt xL2, jetRecX] := by decide +kernel

/-- The `TAG_inc` record has its nonzero tag beyond the 4th entry (5 entries, tag `4` last), so it
is not a 4-entry `walkRecA` key as a polynomial in `γ`; its first entry is the old wire kind
(`0` or `2` at the atom table), never the jet tag `3`. -/
theorem incKey_tag_beyond_fourth :
    incRecX.length = 5 ∧ incRecX.getLast? = some (.k 4) ∧ jetRecX.getLast? = some (.k 3) ∧
      (walkRecAX xFtth xL1).length = 4 := by decide

/-- The polynomial `Σ γ^i · x_i` of a key. -/
def keyPoly {F : Type} [Field F] (γ : F) : List F → F
  | [] => 0
  | x :: r => x + γ * keyPoly γ r

/-- C-1's finding: with
`TAG_jet` FIRST, `(3, id, h_c, h_S, h_E)` at `h_S = h_E = (0, 0)` was a 4-entry `walkRecA` key as a
polynomial in `γ`.  This is a statement about the literal OLD key layout only; the landed
`keyJet` / `jetRecX` put the tag LAST and `serviceKeys_disjoint` below negates the collision. -/
theorem jetKey_collides_walkRecA {F : Type} [Field F] (γ id hk hv : F) :
    keyPoly γ [3, id, hk, hv, 0, 0, 0, 0] = keyPoly γ [3, id, hk, hv] := by
  simp [keyPoly]

/-- A record entry's value on a row `f`. -/
def RE.ev {F : Type} [Field F] (f : ℕ → F) : RE → F
  | .col i => f i
  | .k c => (c : F)

/-- The key as a POLYNOMIAL in `γ`: `Σ C x_i · X^i`. -/
def keyP {F : Type} [Field F] : List F → Polynomial F
  | [] => 0
  | x :: r => Polynomial.C x + Polynomial.X * keyP r

theorem keyP_coeff {F : Type} [Field F] : ∀ (l : List F) (n : ℕ), (keyP l).coeff n = l.getD n 0
  | [], n => by simp [keyP]
  | x :: r, 0 => by simp [keyP]
  | x :: r, n + 1 => by simp [keyP, keyP_coeff r n]

/-- The RLC value is the polynomial's evaluation at `γ`. -/
theorem keyPoly_eq_eval {F : Type} [Field F] (γ : F) : ∀ l : List F, keyPoly γ l = (keyP l).eval γ
  | [] => by simp [keyPoly, keyP]
  | x :: r => by simp [keyPoly, keyP, keyPoly_eq_eval γ r]

/-- **Service-key disjointness (C-2 step 0).**  For ALL rows `f, g` (all handle values, all
`rootIdx / ax2` values) and all handles named in the `walkRecA` record, the three service record
kinds are pairwise DISTINCT polynomials in `γ`: the inc key has coefficient `TAG_inc = 4` at `γ⁴`,
the jet key has coefficient `TAG_jet = 3` at `γ⁷`, and a `walkRecA` key has no coefficient beyond
`γ³`.  Needs only `2 ≠ 0` and `3 ≠ 0` in `F` (Goldilocks: yes). -/
theorem serviceKeys_disjoint {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (f g : ℕ → F) (root l : Hd) :
    keyP (incRecX.map (RE.ev f)) ≠ keyP ((walkRecAX root l).map (RE.ev g)) ∧
    keyP (jetRecX.map (RE.ev f)) ≠ keyP ((walkRecAX root l).map (RE.ev g)) ∧
    keyP (incRecX.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
    keyP (jetRecX.map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  refine ⟨fun h => h4 ?_, fun h => h3 ?_, fun h => h3 ?_, fun h => h3 ?_⟩
  · have := congrArg (fun q => Polynomial.coeff q 4) h
    simpa [keyP_coeff, incRecX, walkRecAX, RE.ev] using this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simpa [keyP_coeff, jetRecX, walkRecAX, RE.ev] using this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simpa [keyP_coeff, jetRecX, incRecX, RE.ev] using this.symm
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simpa [keyP_coeff, jetRecX, incRecX, RE.ev] using this

/-- The tags themselves differ (`TAG_jet = 3 ≠ 4 = TAG_inc`), and they sit in different positions
(`7` vs `4`). -/
theorem serviceTags_distinct :
    jetRecX.getLast? = some (.k 3) ∧ incRecX.getLast? = some (.k 4) ∧ (3 : ℕ) ≠ 4 ∧
      jetRecX.length = 8 ∧ incRecX.length = 5 := by decide

end ReadSet

/-! ## 12. Row-level semantic lemmas (one per new arm; `RowSemX`-ready) -/

section RowSem
variable {F : Type} [Field F]

/-- Evaluation of a `ℚ`-template gate in `F` (constants cast). -/
def evalQX : CoeffExpr ℚ → Env F → F
  | .const c, _ => (c : F)
  | .var .traceCur i, env => env.trace i
  | .var .traceNext i, env => env.traceNext i
  | .var .challenge i, env => env.chal i
  | .var .publicVal i, env => env.pub i
  | .add a b, env => evalQX a env + evalQX b env
  | .sub a b, env => evalQX a env - evalQX b env
  | .mul a b, env => evalQX a env * evalQX b env
  | .neg a, env => - evalQX a env
  | .pow a n, env => (evalQX a env) ^ n

/-- The template's base gates vanish at a row. -/
def BaseHoldsX (env : Env F) : Prop := ∀ g ∈ (baseGatesHX (F := ℚ)), evalQX g env = 0

theorem arith_of_base {env : Env F} (h : BaseHoldsX env) {g : CoeffExpr ℚ} (hg : g ∈ arithGatesX) :
    evalQX g env = 0 := h g (by simp only [baseGatesHX, List.mem_append]; exact Or.inl (Or.inl hg))

theorem eq_of_base {env : Env F} (h : BaseHoldsX env) {g : EqG ℚ} (hg : g ∈ eqGatesX) :
    evalQX g.gate env = 0 :=
  h _ (by simp only [baseGatesHX, List.mem_append]; exact Or.inr (List.mem_map_of_mem hg))

/-- Row values. -/
abbrev tr (env : Env F) (i : ℕ) : F := env.trace i
def kcV (env : Env F) (h : Hd) : F := env.trace h.k - 2 * env.trace (kbX h)
def kbV (env : Env F) (h : Hd) : F := env.trace (kbX h)

/-- **The `kb` split** (SPEC §3.2): every handle is a small atom, a cell, or a big atom, and the
wire kind is `kc + 2·kb`. -/
theorem kind_split {env : Env F} (hB : BaseHoldsX env) (h : Hd) (hh : h ∈ allHandlesX) :
    (kcV env h = 0 ∧ kbV env h = 0) ∨ (kcV env h = 1 ∧ kbV env h = 0) ∨
      (kcV env h = 0 ∧ kbV env h = 1) := by
  have mem : ∀ g ∈ [boolG (kbE h), boolG (kcE h), .mul (kcE h) (kbE h)], g ∈ (arithGatesX (F := ℚ)) := by
    intro g hg
    have hk : g ∈ (kindG (F := ℚ)) := List.mem_flatMap.mpr ⟨h, hh, hg⟩
    simp only [arithGatesX, List.mem_append]
    simp [hk]
  have h1 := arith_of_base hB (mem (boolG (kbE h)) (by simp))
  have h2 := arith_of_base hB (mem (boolG (kcE h)) (by simp))
  have h3 := arith_of_base hB (mem (.mul (kcE h) (kbE h)) (by simp))
  simp only [boolG, kbE, kcE, cc, evalQX, Rat.cast_one, Rat.cast_ofNat] at h1 h2 h3
  simp only [kcV, kbV]
  rcases mul_eq_zero.mp h1 with hb | hb <;> rcases mul_eq_zero.mp h2 with hc | hc
  · left; exact ⟨hc, hb⟩
  · right; left; exact ⟨by linear_combination hc, hb⟩
  · right; right; exact ⟨hc, by linear_combination hb⟩
  · exfalso
    have : env.trace (kbX h) = 1 := by linear_combination hb
    have hc' : env.trace h.k - 2 * env.trace (kbX h) = 1 := by linear_combination hc
    rw [hc', this] at h3; simp at h3

/-- Fetch an arithmetic gate of a named arm. -/
theorem arm_mem {l : List (CoeffExpr ℚ)} {g : CoeffExpr ℚ} (hl : ∀ x ∈ l, x ∈ arithGatesX)
    (hg : g ∈ l) : g ∈ (arithGatesX (F := ℚ)) := hl g hg

theorem op4G_sub : ∀ x ∈ (op4G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem op5G_sub : ∀ x ∈ (op5G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem s10G_sub : ∀ x ∈ (s10G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem s10LG_sub : ∀ x ∈ (s10LG : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem s11G_sub : ∀ x ∈ (s11G : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]
theorem svG_sub : ∀ x ∈ (svG : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]

theorem eqArm_sub {l : List (EqG ℚ)} (hl : ∀ x ∈ l, x ∈ (eqGatesX (F := ℚ))) {g : EqG ℚ} (hg : g ∈ l) :
    g ∈ (eqGatesX (F := ℚ)) := hl g hg

theorem op4Eq_sub : ∀ x ∈ (op4Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem op5Eq_sub : ∀ x ∈ (op5Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem svEq_sub : ∀ x ∈ (svEq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem s10Eq_sub : ∀ x ∈ (s10Eq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem s10LEq_sub : ∀ x ∈ (s10LEq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem s10TEq_sub : ∀ x ∈ (s10TEq : List (EqG ℚ)), x ∈ (eqGatesX (F := ℚ)) := by
  intro x hx; simp only [eqGatesX, List.mem_append]; simp [hx]
theorem kidKindG_sub : ∀ x ∈ (kidKindG : List (CoeffExpr ℚ)), x ∈ (arithGatesX (F := ℚ)) := by
  intro x hx; simp only [arithGatesX, List.mem_append]; simp [hx]

theorem kidFormsX_handles : ∀ jh ∈ kidFormsX, jh.2 ∈ allHandlesX := by decide

/-- **The kid-kind gate, row level** (C-2 part 2): on a row in state `j`, a real child's formula
handle (`(j, h) ∈ kidFormsX`) has `kc = 1`, hence `kb = 0` (`kind_split`), hence wire kind `1`. -/
theorem kid_cell {env : Env F} (hB : BaseHoldsX env) {j : ℕ} {h : Hd} (hj : tr env j = 1)
    (hm : (j, h) ∈ kidFormsX) : env.trace h.k = 1 := by
  have g := arith_of_base hB (kidKindG_sub _ (List.mem_map_of_mem (f := fun jh : ℕ × Hd =>
    (CoeffExpr.mul (cc jh.1) (oneMinus (kcE jh.2)) : CoeffExpr ℚ)) hm))
  simp only [oneMinus, kcE, kbE, cc, evalQX, Rat.cast_one, Rat.cast_ofNat] at g
  rw [show env.trace j = 1 from hj, one_mul] at g
  rcases kind_split hB h (kidFormsX_handles _ hm) with ⟨hc, -⟩ | ⟨-, hb⟩ | ⟨hc, -⟩
  · simp only [kcV] at hc; rw [hc] at g; exact absurd g (by simp)
  · simp only [kbV] at hb; rw [hb] at g; linear_combination -g
  · simp only [kcV] at hc; rw [hc] at g; exact absurd g (by simp)

/-- **Chip-level negative control for the part-1 FINDING** (the swapped state): an OP4 row whose
child formula handle `f_t` is a small atom — e.g. `[4 1]`, whose child `(s, 1, sf1)` an `s10T`
pseudo-row could serve — fails the kid-kind gate `s4 · (1 − kc(f_t))`: no such row satisfies the
base gates. -/
theorem swapped_s10T_child_rejected {env : Env F} (h4 : tr env 4 = 1) (hk : env.trace xFt.k = 0) :
    ¬ BaseHoldsX env := by
  intro hB
  have := kid_cell hB h4 (by decide : ((4 : ℕ), xFt) ∈ kidFormsX)
  rw [hk] at this; exact zero_ne_one this

/-- **op 4, fast** (SPEC §3.3): on an `s4` row with `fast = 1`, input and output are small atoms,
`e.v = sf1.v + 1` and `sf1.v + 1 ≠ 0` (no wrap). -/
theorem op4_fast_row {env : Env F} (hB : BaseHoldsX env) (h4 : tr env 4 = 1) (hf : tr env fastX = 1) :
    kcV env xSf1 = 0 ∧ kcV env xE = 0 ∧ kbV env xSf1 = 0 ∧ kbV env xE = 0 ∧
      tr env xE.v = tr env xSf1.v + 1 ∧ tr env xSf1.v + 1 ≠ 0 := by
  have g := fun x hx => arith_of_base (F := F) hB (op4G_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (op4Eq_sub x hx)
  have a1 := g _ (by simp [op4G] : (.mul (cc 4) (kcE xSf1)) ∈ (op4G (F := ℚ)))
  have a2 := g _ (by simp [op4G] : (.mul (cc 4) (kcE xE)) ∈ (op4G (F := ℚ)))
  have a3 := g _ (by simp [op4G] : (.mul (cc 4) (.sub (.sub (cc v2X) (cc vX)) (.const 1))) ∈ (op4G (F := ℚ)))
  have a4 := g _ (by simp [op4G] :
    (prodL [cc 4, cc fastX, .sub (.mul (cc v2X) (cc inv4X)) (.const 1)]) ∈ (op4G (F := ℚ)))
  have a5 := g _ (by simp [op4G] : (prodL [cc 4, cc fastX, kbE xSf1]) ∈ (op4G (F := ℚ)))
  have a6 := g _ (by simp [op4G] : (prodL [cc 4, cc fastX, kbE xE]) ∈ (op4G (F := ℚ)))
  have e1 := e _ (by simp [op4Eq] : (⟨.mul (cc 4) (oneMinus (kbE xSf1)), vX, .col xSf1.v⟩ : EqG ℚ) ∈ (op4Eq (F := ℚ)))
  have e2 := e _ (by simp [op4Eq] : (⟨.mul (cc 4) (cc fastX), xE.v, .col v2X⟩ : EqG ℚ) ∈ (op4Eq (F := ℚ)))
  simp only [tr] at h4 hf
  simp only [prodL, List.foldr, cc, kcE, kbE, oneMinus, EqG.gate, Opnd.expr, evalQX, Rat.cast_one,
    Rat.cast_ofNat, h4, hf, one_mul, mul_one] at a1 a2 a3 a4 a5 a6 e1 e2
  simp only [kcV, kbV, tr]
  refine ⟨a1, a2, a5, a6, ?_, ?_⟩
  · simp only [a5, sub_zero, one_mul] at e1
    linear_combination e2 + a3 + e1
  · intro hz
    simp only [a5, sub_zero, one_mul] at e1
    have hv2 : env.trace v2X = 0 := by linear_combination a3 + e1 + hz
    rw [hv2] at a4; simp at a4

/-- **op 4, slow**: on an `s4` row with `fast = 0`, the output is a BIG atom (`e.kb = 1`), and a
small input is `p − 1` (the row's `TAG_inc` consume in `slot1` carries the rest, `consumesX_op4`). -/
theorem op4_slow_row {env : Env F} (hB : BaseHoldsX env) (h4 : tr env 4 = 1) (hf : tr env fastX = 0) :
    kcV env xSf1 = 0 ∧ kcV env xE = 0 ∧ kbV env xE = 1 ∧
      (kbV env xSf1 = 0 → tr env xSf1.v = -1) := by
  have g := fun x hx => arith_of_base (F := F) hB (op4G_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (op4Eq_sub x hx)
  have a1 := g _ (by simp [op4G] : (.mul (cc 4) (kcE xSf1)) ∈ (op4G (F := ℚ)))
  have a2 := g _ (by simp [op4G] : (.mul (cc 4) (kcE xE)) ∈ (op4G (F := ℚ)))
  have a3 := g _ (by simp [op4G] : (.mul (cc 4) (.sub (.sub (cc v2X) (cc vX)) (.const 1))) ∈ (op4G (F := ℚ)))
  have a7 := g _ (by simp [op4G] : (prodL [cc 4, notC fastX, oneMinus (kbE xSf1), cc v2X]) ∈ (op4G (F := ℚ)))
  have a8 := g _ (by simp [op4G] : (prodL [cc 4, notC fastX, oneMinus (kbE xE)]) ∈ (op4G (F := ℚ)))
  have e1 := e _ (by simp [op4Eq] : (⟨.mul (cc 4) (oneMinus (kbE xSf1)), vX, .col xSf1.v⟩ : EqG ℚ) ∈ (op4Eq (F := ℚ)))
  simp only [tr] at h4 hf
  simp only [prodL, List.foldr, cc, notC, kcE, kbE, oneMinus, EqG.gate, Opnd.expr, evalQX,
    Rat.cast_one, Rat.cast_ofNat, h4, hf, one_mul, mul_one, sub_zero] at a1 a2 a3 a7 a8 e1
  simp only [kcV, kbV, tr]
  refine ⟨a1, a2, by linear_combination -a8, fun hs => ?_⟩
  simp only [hs, sub_zero, one_mul] at a7 e1
  linear_combination a7 - a3 - e1

/-- **op 5, the α second pair** (SPEC §3.3): on an `s5` "≠" row whose two first-difference leaves
are both BIG, `pr2 = 1`, at most one pair record is a suffix row, and two inline limbs differ. -/
theorem op5_pair_row {env : Env F} (hB : BaseHoldsX env) (h5 : tr env 5 = 1) (hb : tr env betaX = 1)
    (h1 : kbV env xFtth = 1) (h2 : kbV env xFttt = 1) :
    tr env pr2X = 1 ∧ tr env xL1.k * tr env xL2.k = 0 ∧
      (tr env xL1.k = 0 → tr env xL2.k = 0 → tr env xL1.v ≠ tr env xL2.v) := by
  have g := fun x hx => arith_of_base (F := F) hB (op5G_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (op5Eq_sub x hx)
  have k1 := kind_split hB xFtth (by decide)
  have k2 := kind_split hB xFttt (by decide)
  have hc1 : kcV env xFtth = 0 := by rcases k1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> simp_all
  have hc2 : kcV env xFttt = 0 := by rcases k2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> simp_all
  have aP := g _ (by simp [op5G] : pr2GateX ∈ (op5G (F := ℚ)))
  have aK := g _ (by simp [op5G] : (prodL [cc pr2X, cc xL1.k, cc xL2.k]) ∈ (op5G (F := ℚ)))
  have aN := g _ (by simp [op5G] : neGateX ∈ (op5G (F := ℚ)))
  have e1 := e _ (by simp [op5Eq] : (⟨.mul (cc pr2X) (notC xL1.k), vX, .col xL1.v⟩ : EqG ℚ) ∈ (op5Eq (F := ℚ)))
  have e2 := e _ (by simp [op5Eq] : (⟨.mul (cc pr2X) (notC xL2.k), v2X, .col xL2.v⟩ : EqG ℚ) ∈ (op5Eq (F := ℚ)))
  simp only [kcV, kbV, tr] at h5 hb h1 h2 hc1 hc2 ⊢
  simp only [pr2GateX, neGateX, prodL, List.foldr, cc, notC, kcE, kbE, EqG.gate, Opnd.expr, evalQX,
    Rat.cast_one, Rat.cast_ofNat, h5, hb, h1, h2, one_mul, mul_one] at aP aK aN e1 e2
  have hp : env.trace pr2X = 1 := by linear_combination aP
  refine ⟨hp, by rw [hp] at aK; simpa using aK, fun hk1 hk2 hv => ?_⟩
  rw [hp, hk1] at e1; rw [hp, hk2] at e2
  simp at e1 e2
  have ht1 : env.trace xFtth.k = 2 := by linear_combination hc1 + 2 * h1
  have ht2 : env.trace xFttt.k = 2 := by linear_combination hc2 + 2 * h2
  have : env.trace vX - env.trace v2X = 0 := by linear_combination e1 - e2 + hv
  rw [ht1, ht2, this] at aN; norm_num at aN

/-- **op 10, `s10`** (SPEC §3.3): head `10`, a small axis atom copied to `v`; axis `1` makes
`e = new`; otherwise `e` is a cell (the read `slot a e = new` is `inv3`'s path entry). -/
theorem s10_row {env : Env F} (hB : BaseHoldsX env) (h : tr env sS10 = 1) :
    tr env xFh.v = 10 ∧ tr env xFtth.k = 0 ∧ tr env vX = tr env xFtth.v ∧
      (tr env z1X = 1 → tr env vX = 1 ∧ tr env xE.k = tr env xSf1.k ∧ tr env xE.v = tr env xSf1.v) ∧
      (tr env z1X = 0 → kcV env xE = 1) := by
  have g := fun x hx => arith_of_base (F := F) hB (s10G_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (s10Eq_sub x hx)
  have es := fun x hx => eq_of_base (F := F) hB (svEq_sub x hx)
  have a1 := g _ (by simp [s10G] : (.mul (cc sS10) (cc xFtth.k)) ∈ (s10G (F := ℚ)))
  have a2 := g _ (by simp [s10G] : (prodL [cc sS10, cc z1X, .sub (cc vX) (.const 1)]) ∈ (s10G (F := ℚ)))
  have a3 := g _ (by simp [s10G] : (prodL [cc sS10, notC z1X, oneMinus (kcE xE)]) ∈ (s10G (F := ℚ)))
  have e0 := es _ (by simp [svEq] : (⟨cc sS10, xFh.v, .cst 10⟩ : EqG ℚ) ∈ (svEq (F := ℚ)))
  have e1 := e _ (by simp [s10Eq] : (⟨cc sS10, vX, .col xFtth.v⟩ : EqG ℚ) ∈ (s10Eq (F := ℚ)))
  have e2 := e _ (by simp [s10Eq, heq] : (⟨.mul (cc sS10) (cc z1X), xE.k, .col xSf1.k⟩ : EqG ℚ) ∈ (s10Eq (F := ℚ)))
  have e3 := e _ (by simp [s10Eq, heq] : (⟨.mul (cc sS10) (cc z1X), xE.v, .col xSf1.v⟩ : EqG ℚ) ∈ (s10Eq (F := ℚ)))
  simp only [tr] at h ⊢
  simp only [kcV]
  simp only [prodL, List.foldr, cc, notC, kcE, kbE, oneMinus, EqG.gate, Opnd.expr, evalQX,
    Rat.cast_one, Rat.cast_ofNat, h, one_mul, mul_one] at a1 a2 a3 e0 e1 e2 e3
  refine ⟨by linear_combination e0, a1, by linear_combination e1, fun hz => ?_, fun hz => ?_⟩
  · rw [hz] at a2 e2 e3; simp at a2 e2 e3
    exact ⟨by linear_combination a2, by linear_combination e2, by linear_combination e3⟩
  · rw [hz] at a3; simp at a3; linear_combination -a3

/-- **op 10, `s10L`** (SPEC §3.3): an atom formula `a_k ≠ 1` with `a_k = 2v + β`; the pair reads
the sibling axis `m.v = a_k + 1 − 2β` (= `a_k xor 1`) in `sf1 = s` (old) and `sf2 = e`, and the two
leaves agree (`f_tth = f_ttt`). -/
theorem s10L_row {env : Env F} (hB : BaseHoldsX env) (h : tr env sS10L = 1) (h5 : tr env 5 = 0)
    (h13 : tr env sS10T = 0) :
    tr env xF.k = 0 ∧ tr env xF.v = 2 * tr env vX + tr env betaX ∧ tr env xF.v ≠ 1 ∧
      tr env xM.v = tr env xF.v + 1 - 2 * tr env betaX ∧ tr env prX = 1 ∧ tr env xM.k = 0 ∧
      tr env xSf1.v = tr env xS.v ∧ tr env xSf1.k = tr env xS.k ∧
      tr env xSf2.v = tr env xE.v ∧ tr env xSf2.k = tr env xE.k ∧
      tr env xFtth.v = tr env xFttt.v ∧ tr env xFtth.k = tr env xFttt.k := by
  have g := fun x hx => arith_of_base (F := F) hB (s10LG_sub x hx)
  have gs := fun x hx => arith_of_base (F := F) hB (svG_sub x hx)
  have g5 := fun x hx => arith_of_base (F := F) hB (op5G_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (s10LEq_sub x hx)
  have a1 := g _ (by simp [s10LG] :
    (.mul (cc sS10L) (.sub (.sub (cc v2X) (.mul (.const 2) (cc vX))) (cc betaX))) ∈ (s10LG (F := ℚ)))
  have a2 := g _ (by simp [s10LG] :
    (.mul (cc sS10L) (.sub (.mul (.sub (cc v2X) (.const 1)) (cc wX)) (.const 1))) ∈ (s10LG (F := ℚ)))
  have a3 := g _ (by simp [s10LG] :
    (.mul (cc sS10L) (.add (.sub (.sub (cc ax2X) (cc v2X)) (.const 1)) (.mul (.const 2) (cc betaX))))
      ∈ (s10LG (F := ℚ)))
  have aF := gs _ (by simp [svG] :
    (.add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T)) ∈ (svG (F := ℚ)))
  have aP := g5 _ (by simp [op5G] : prGateX ∈ (op5G (F := ℚ)))
  have aM := g5 _ (by simp [op5G] : (.mul (cc prX) (cc xM.k)) ∈ (op5G (F := ℚ)))
  have e1 := e _ (by simp [s10LEq] : (⟨cc sS10L, v2X, .col xF.v⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e2 := e _ (by simp [s10LEq] : (⟨cc sS10L, xM.v, .col ax2X⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e3 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xSf1.k, .col xS.k⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e4 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xSf1.v, .col xS.v⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e5 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xSf2.k, .col xE.k⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e6 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xSf2.v, .col xE.v⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e7 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xFtth.k, .col xFttt.k⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  have e8 := e _ (by simp [s10LEq, heq] : (⟨cc sS10L, xFtth.v, .col xFttt.v⟩ : EqG ℚ) ∈ (s10LEq (F := ℚ)))
  simp only [tr] at h h5 h13 ⊢
  simp only [prGateX, prodL, List.foldr, cc, notC, EqG.gate, Opnd.expr, evalQX, Rat.cast_one,
    Rat.cast_ofNat, h, h5, h13, one_mul, mul_one, zero_mul, sub_zero, add_zero] at a1 a2 a3 aF aP aM e1 e2 e3 e4 e5 e6 e7 e8
  have hp : env.trace prX = 1 := by linear_combination aP
  rw [hp] at aM; simp at aM
  refine ⟨by linear_combination aF, by linear_combination a1 - e1, fun h1 => ?_,
    by linear_combination e2 + a3 + e1, hp, aM, by linear_combination e4, by linear_combination e3,
    by linear_combination e6, by linear_combination e5, by linear_combination e8,
    by linear_combination e7⟩
  have : env.trace v2X - 1 = 0 := by linear_combination e1 + h1
  rw [this] at a2; simp at a2

/-- **op 10, `s10T`**: the chain terminal's formula is the small atom `1`. -/
theorem s10T_row {env : Env F} (hB : BaseHoldsX env) (h : tr env sS10T = 1) (h12 : tr env sS10L = 0) :
    tr env xF.k = 0 ∧ tr env xF.v = 1 := by
  have gs := fun x hx => arith_of_base (F := F) hB (svG_sub x hx)
  have e := fun x hx => eq_of_base (F := F) hB (s10TEq_sub x hx)
  have aF := gs _ (by simp [svG] :
    (.add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T)) ∈ (svG (F := ℚ)))
  have e1 := e _ (by simp [s10TEq] : (⟨cc sS10T, xF.v, .cst 1⟩ : EqG ℚ) ∈ (s10TEq (F := ℚ)))
  simp only [tr] at h h12 ⊢
  simp only [cc, EqG.gate, Opnd.expr, evalQX, Rat.cast_one, h, h12, one_mul, add_zero] at aF e1
  exact ⟨by linear_combination aF, by linear_combination e1⟩

/-- The row's `StateX` one-hot is at `j`. -/
def OneHotAt (env : Env F) (j : ℕ) : Prop := ∀ i, i < nStates → env.trace i = if i = j then 1 else 0

theorem selS_onehot {env : Env F} {j : ℕ} (hOH : OneHotAt env j) :
    ∀ (l : List ℕ), (∀ i ∈ l, i < nStates) → l.Nodup →
      evalQX (selS (F := ℚ) l) env = if j ∈ l then 1 else 0
  | [], _, _ => by simp [selS, CoeffExpr.sumList, evalQX]
  | a :: l, hl, hnd => by
      have ih := selS_onehot hOH l (fun i hi => hl i (by simp [hi])) (List.nodup_cons.mp hnd).2
      have ha := hOH a (hl a (by simp))
      have hsel : evalQX (selS (F := ℚ) (a :: l)) env = env.trace a + evalQX (selS (F := ℚ) l) env := by
        simp [selS, CoeffExpr.sumList, evalQX, cc]
      rw [hsel, ih, ha]
      by_cases hj : a = j
      · subst hj
        have : a ∉ l := (List.nodup_cons.mp hnd).1
        simp [this]
      · by_cases hjl : j ∈ l
        · simp [hj, hjl]
        · simp [hj, hjl, Ne.symm hj]

/-- **op 11** (SPEC §3.3): head `11`; `s11s`'s tag is an atom; `s11d`/`s11j` decode
`f_th = [b clue]` (a cell); `s11j`'s id `b = f_tth` is a SMALL atom (its `TAG_jet` consume is
`inv3`'s service entry, `consumesX_s11j`). -/
theorem s11_row {env : Env F} (hB : BaseHoldsX env) {j : ℕ} (hOH : OneHotAt env j)
    (hj : j = sS11s ∨ j = sS11d ∨ j = sS11j) :
    tr env xFh.v = 11 ∧ kcV env xFt = 1 ∧
      (j = sS11s → kcV env xFth = 0) ∧ (j ≠ sS11s → kcV env xFth = 1) ∧
      (j = sS11j → tr env xFtth.k = 0) := by
  have g := fun x hx => arith_of_base (F := F) hB (s11G_sub x hx)
  have gs := fun x hx => arith_of_base (F := F) hB (svG_sub x hx)
  have es := fun x hx => eq_of_base (F := F) hB (svEq_sub x hx)
  have a1 := g _ (by simp [s11G] : (.mul (cc sS11s) (kcE xFth)) ∈ (s11G (F := ℚ)))
  have a2 := g _ (by simp [s11G] : (.mul (cc sS11j) (cc xFtth.k)) ∈ (s11G (F := ℚ)))
  have aT := gs _ (by simp [svG] : (.mul (selS l2X) (oneMinus (kcE xFt))) ∈ (svG (F := ℚ)))
  have aH := gs _ (by simp [svG] : (.mul (selS l3X) (oneMinus (kcE xFth))) ∈ (svG (F := ℚ)))
  have e14 := es _ (by simp [svEq] : (⟨cc sS11s, xFh.v, .cst 11⟩ : EqG ℚ) ∈ (svEq (F := ℚ)))
  have e15 := es _ (by simp [svEq] : (⟨cc sS11d, xFh.v, .cst 11⟩ : EqG ℚ) ∈ (svEq (F := ℚ)))
  have e16 := es _ (by simp [svEq] : (⟨cc sS11j, xFh.v, .cst 11⟩ : EqG ℚ) ∈ (svEq (F := ℚ)))
  have hl2 : (∀ i ∈ l2X, i < nStates) ∧ l2X.Nodup := by decide
  have hl3 : (∀ i ∈ l3X, i < nStates) ∧ l3X.Nodup := by decide
  have hT : evalQX (selS (F := ℚ) l2X) env = 1 := by
    rw [selS_onehot hOH l2X hl2.1 hl2.2]; rcases hj with rfl | rfl | rfl <;> simp [l2X, sS11s, sS11d, sS11j]
  have hH : evalQX (selS (F := ℚ) l3X) env = if j = sS11s then 0 else 1 := by
    rw [selS_onehot hOH l3X hl3.1 hl3.2]; rcases hj with rfl | rfl | rfl <;> simp [l3X, sS11s, sS11d, sS11j]
  have hs : ∀ i, i < nStates → (env.trace i = if i = j then 1 else 0) := hOH
  have h14 := hs sS11s (by decide)
  have h15 := hs sS11d (by decide)
  have h16 := hs sS11j (by decide)
  simp only [EqG.gate, Opnd.expr, cc, evalQX, Rat.cast_ofNat] at e14 e15 e16
  simp only [cc, kcE, kbE, evalQX, Rat.cast_ofNat] at a1 a2
  rw [show evalQX (.mul (selS l2X) (oneMinus (kcE xFt))) env =
      evalQX (selS (F := ℚ) l2X) env * evalQX (oneMinus (kcE (F := ℚ) xFt)) env from rfl, hT] at aT
  rw [show evalQX (.mul (selS l3X) (oneMinus (kcE xFth))) env =
      evalQX (selS (F := ℚ) l3X) env * evalQX (oneMinus (kcE (F := ℚ) xFth)) env from rfl, hH] at aH
  simp only [oneMinus, kcE, kbE, cc, evalQX, Rat.cast_one, Rat.cast_ofNat, one_mul] at aT aH
  simp only [kcV, tr]
  rcases hj with rfl | rfl | rfl
  · simp only [sS11s, sS11d, sS11j] at h14 h15 h16 a1 e14
    simp at h14 h15 h16
    rw [h14] at a1 e14
    refine ⟨by linear_combination e14, by linear_combination -aT, fun _ => by linear_combination a1,
      fun h => absurd rfl h, fun h => absurd h (by decide)⟩
  · simp only [sS11s, sS11d, sS11j] at h14 h15 h16 e15 aH
    simp at h14 h15 h16 aH
    rw [h15] at e15
    refine ⟨by linear_combination e15, by linear_combination -aT, fun h => absurd h (by decide),
      fun _ => by linear_combination -aH, fun h => absurd h (by decide)⟩
  · simp only [sS11s, sS11d, sS11j] at h14 h15 h16 e16 aH a2
    simp at h14 h15 h16 aH
    rw [h16] at e16 a2
    refine ⟨by linear_combination e16, by linear_combination -aT, fun h => absurd h (by decide),
      fun _ => by linear_combination -aH, fun _ => by linear_combination a2⟩

/-- **A jet row is a `%wild` hint keyed by its clue's value**: on `s11j` the tag `f_tth` has value
`%wild` (with `s11_row`'s kind `0`, the atom `%wild` when `wildTag < p`), and the clue's value `sf1`
is a small atom, the jet key that `jetRecX` consumes. -/
theorem s11j_wild {env : Env F} (hB : BaseHoldsX env) (hOH : OneHotAt env sS11j) :
    tr env xFtth.v = (Nock.Jet.wildTag : F) ∧ tr env xSf1.k = 0 := by
  have g := fun x hx => arith_of_base (F := F) hB (s11G_sub x hx)
  have es := fun x hx => eq_of_base (F := F) hB (svEq_sub x hx)
  have a3 := g _ (by simp [s11G] : (.mul (cc sS11j) (cc xSf1.k)) ∈ (s11G (F := ℚ)))
  have eW := es _ (by simp [svEq] :
    (⟨cc sS11j, xFtth.v, .cst (Nock.Jet.wildTag : ℚ)⟩ : EqG ℚ) ∈ (svEq (F := ℚ)))
  have h16 := hOH sS11j (by decide)
  simp only [EqG.gate, Opnd.expr, cc, evalQX, Rat.cast_natCast] at eW
  simp only [cc, evalQX] at a3
  simp only [if_true] at h16
  rw [h16] at eW a3
  simp only [tr]
  exact ⟨by linear_combination eW, by linear_combination a3⟩

end RowSem

/-! ## 13. The chip -/

section Chip
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The J-8 handle compute RAP** (`wRAP = ![69, 54]`: B0 columns, then the coin-dependent block). -/
def vclRAPHX [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![round0WX, 54]
    w := widthHX
    w_eq := by simp [Fin.sum_univ_two, round0WX, widthHX]
    h := h
    d := 4
    s := (gatesHX b δ).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((gatesHX b δ).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (gatesHX_degree b δ _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLHX`**: the J-8 compute chip (preprocessing `isFirst` / `isLast` at `17` / `18`). -/
def computeChipVCLHX [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPHX b δ chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := Nat.two_pos
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨17 + (j : ℕ), by
          have := j.isLt
          change 17 + (j : ℕ) < round0WX
          simp only [round0WX]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLHX_width [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w = 123 := rfl

end Chip

end

end ChipHX
end VclL.Handle
end Nock.NockVMROM.Thm54
