/-
  Nock/NockVMROM/Thm54/VclL/Handle/WildTagX.lean

  **A jet row's tag is the atom `%wild`.**  The soundness chain (`RowSemChipX.sem_s11j`,
  `LocalVSX.RowSemX0`, `GenuineNX.RowOutputNX`) takes the jet id from the clue's value and does not
  mention the hint's tag: `evalN` ignores the tag, so soundness has no use for it.  This file states
  separately what the chip does enforce about the tag.  `s11_row` makes the tag's handle kind `0`
  and `s11j_wild` makes its value `wildTag` in the field; when `wildTag < p` (as at Goldilocks) the
  two give the handle `(0, wildTag)`, the atom `%wild`.  At a field with `p ≤ wildTag`, `%wild` is a
  big atom and no honest jet row exists.

  Nothing in the soundness chain uses this theorem.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WildTagX

open Nock.Reified Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (hdV_k0 val_nat)

variable {p : ℕ} [Fact p.Prime] {env : Env (ZMod p)}

/-- **The tag of an accepted jet row is the atom `%wild`** (given `wildTag < p`). -/
theorem s11j_tag (hB : BaseHoldsX env) (hOH : OneHotAt env sS11j) (hw : Nock.Jet.wildTag < p) :
    hdV env xFtth = (0, Nock.Jet.wildTag) := by
  obtain ⟨-, -, -, -, hk⟩ := s11_row hB hOH (Or.inr (Or.inr rfl))
  have hv : env.trace xFtth.v = (Nock.Jet.wildTag : ZMod p) := (s11j_wild hB hOH).1
  rw [hdV_k0 (hk rfl), hv, val_nat hw]

/-- At Goldilocks, `wildTag < p`. -/
theorem wildTag_lt_goldilocks : Nock.Jet.wildTag < Nock.Field.p := by
  unfold Nock.Jet.wildTag Nock.Field.p; norm_num

end Nock.NockVMROM.Thm54.VclL.Handle.WildTagX

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.WildTagX.s11j_tag
