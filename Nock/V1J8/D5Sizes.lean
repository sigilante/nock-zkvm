/-
  Nock/V1J8/D5Sizes.lean

  * `matS N` — the gate subject `[0 [[A B] 0]]` (`AutogenMatmul.toyS`'s shape) of two `N × N` matrices of small field
    atoms, `A i j = (3 i + j + 1) mod 11`, `B i j = (i + 2 j + 2) mod 7`; `matRef N` — the product mod `p` by plain
    `ℕ` arithmetic (the independent reference).
  * `matPure N` — the PURE Nock formula: `compile p (matmulT N)` (the jet's own body, no hint, run against the empty
    registry); `matJetF N` — `[11 [%wild [1 7]] c_T]` (`wildCall 7 c_T`, as `Demo.matProg` at `N = 2`).
  * `Sz` — the row counts of a generated input (compute / cell / walk / J / atom / atom walk), the committed field
    elements `rows × width` per table (widths 123 / 242 / 166 / 71 / 349 / 166, the J-8 chips), their total.
  * `genPure` / `genJet` — `genJ8` (no registry) / `genJ8J` (registry `[7 ↦ matmulT N]`, fuel `2`) at the pseudo-random coins.
  * Kernel receipt (`Nock/RedTeam/Batch4790Thm54D5Sizes.lean`): the pure and the jetted `N = 2` programs evaluate to
    the same noun.
-/
import Nock.V1J8.GenJet
import Nock.Jet.AutogenMatmul
import Nock.Edit.GenXDemo

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.D5

open Nock Nock.Field Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Jet.Autogen (matmulT compile mat)
open Nock.Jet.ChipJ8 (layoutJ8)

/-- Matrix entries (small field atoms). -/
def entA (i j : ℕ) : ℕ := (3 * i + j + 1) % 11
def entB (i j : ℕ) : ℕ := (i + 2 * j + 2) % 7

def listMat (f : ℕ → ℕ → ℕ) (N : ℕ) : List (List ℕ) :=
  (List.range N).map fun i => (List.range N).map fun j => f i j

/-- The gate subject `[battery [[A B] context]]`. -/
def matS (N : ℕ) : Noun :=
  .cell (.atom 0) (.cell (.cell (mat (listMat entA N)) (mat (listMat entB N))) (.atom 0))

/-- The reference product mod `p` (plain arithmetic). -/
def matRef (N : ℕ) : Noun :=
  mat ((List.range N).map fun i => (List.range N).map fun j =>
    ((List.range N).foldl (fun acc l => acc + entA i l * entB l j) 0) % P)

/-- The PURE formula: the compiled matmul body, no jet hint. -/
def matPure (N : ℕ) : Noun := compile P (matmulT N)

/-- The JETTED program `[11 [7 [1 0]] c_T]`. -/
def matJetF (N : ℕ) : Noun := Nock.Jet.wildCall 7 (compile P (matmulT N))

/-- Cell count of a noun. -/
def cellsOf : Noun → ℕ
  | .atom _ => 0
  | .cell a b => 1 + cellsOf a + cellsOf b

/-- The J-8 chip widths: compute, cell, walk, J, atom table, atom walk. -/
def widths : List ℕ := [123, 242, 166, 71, 349, 166]
def tableNames : List String := ["compute", "cell", "walk", "J", "atom", "atom walk"]

/-- Row counts of a generated input, in `tableNames` order. -/
def rowsOf (I : InJ8) : List ℕ := [I.X.n, I.C.n, I.W.n, I.J.n, I.A.n, I.V.n]

def committed (rs : List ℕ) : List ℕ := (rs.zip widths).map fun x => x.1 * x.2

def total (rs : List ℕ) : ℕ := (committed rs).foldl (· + ·) 0

/-- The pure run: Nock steps (= compute rows), the result noun. -/
def runPure (N : ℕ) : Option (ℕ × Noun) :=
  (runX (fun _ => none) 1000000 (matS N) (matPure N)).map fun r => (r.rows.size, r.res)

def runJet (N : ℕ) : Option (ℕ × Noun) :=
  (runX (regOf (fun _ => matmulT N) [7]) 1000000 (matS N) (matJetF N)).map fun r => (r.rows.size, r.res)

def genPure (N : ℕ) (χ : CoinsE) : Option InJ8 := genJ8 (fun _ => none) 1000000 (matS N) (matPure N) χ

def genJet (N : ℕ) (χ : CoinsE) : Option InJ8 :=
  genJ8J (fun _ => matmulT N) [7] 1000000 (matS N) (matJetF N) χ

/-- **The table sizes without the column fill** (the stage of `genJ8` that fixes the row counts): compute = the run's
rows, cell = `|cellsOfRoots …|`, walk = `|walkGen …|`, J = `|layoutJ8 …|`, atom / atom walk = the pad rows (`genJ8` /
`genJ8J` carry no big atom).  Equal to `rowsOf` of the full generator (`nockvm-j8check report --check`). -/
def fastRows (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ) (s f : Noun) :
    Option (List ℕ × ℕ) :=
  match runX R 1000000 s f with
  | none => none
  | some Rn =>
    let calls := callsOf Rn.rows
    let jn := jNouns Rt regs calls
    if !(smallAtoms Rn.rows && smallNouns jn) then none else
    let c : Nock.NockVMROM.Thm54.P8PublicClaim := ⟨s, f, Rn.res⟩
    let cs := cellsOfRoots (rootsOf c Rn.rows ++ jn)
    let ws := (walkGen (cs.headD (.atom 0)) (pathReads Rn.rows)).1
    let nJ := if regs.isEmpty then 0 else (layoutJ8 Rt regs (calls.map Prod.fst)).length
    some ([Rn.rows.size, cs.length, ws.length, nJ, 1, 1], Rn.rows.size)

def fastPure (N : ℕ) := fastRows (fun _ => none) (fun _ => matmulT N) [] (matS N) (matPure N)
def fastJet (N : ℕ) := fastRows (regOf (fun _ => matmulT N) [7]) (fun _ => matmulT N) [7] (matS N) (matJetF N)

end Nock.V1J8.D5
