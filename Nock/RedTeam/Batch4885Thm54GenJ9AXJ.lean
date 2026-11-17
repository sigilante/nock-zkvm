/-
  Nock/RedTeam/Batch4885Thm54GenJ9AXJ.lean

  The input of `genJ9AXJ` on the jetted matmul `n = 2` (`[11 [%wild [1 7]] c_T]` on `toyS`, registry
  `[7 ↦ matmulT 2]` = `regOf matRt [7]`), at the pseudo-random coins `Gen.prngCoins 1`.
  The definition is not evaluated in this module (an interpreted `#eval` of this pipeline is too slow).
  Observed with the compiled diagnostic: `run.isSome = true`, `checkJ9AX I = true`, and adding `1` to J column 28
  (the call row's output handle) at row `regs.length` gives `checkJ9AX = false`.  This is executable evidence, not a kernel-checked theorem.

  **Coins.** `Example.χ0e` is degenerate past one compute row: its walk coin `α` (coin 13) is `1`, so at every
  non-last row `cnt = ln` and the walk-inverse gate `notLast · (inv · (cnt − ln) − 1)` cannot hold.
  The two-row jetted run therefore needs non-degenerate coins.
-/
import Nock.V1J9A.GenJ9AXJ
import Nock.V1J8.GenJetMat

set_option autoImplicit false

namespace Nock.RedTeam.Batch4885

open Nock Nock.V1J8 Nock.V1J8.Gen Nock.V1J8.GenJ Nock.V1J9A Nock.V1J9A.GenJ9AXJ
open Nock.Edit.GenX
open Nock.Jet.Autogen (toyS)

/-- The input for `genJ9AXJ` described in the module docstring (not evaluated here). -/
def run : Option Nock.V1J9A.CheckJ9A.InJ9A :=
  genJ9AXJ (regOf matRt [7]) matRt 2 toyS Demo.matProg (prngCoins 1)

end Nock.RedTeam.Batch4885
