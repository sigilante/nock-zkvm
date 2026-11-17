/-
  Nock/Jet/Wild.lean

  **The reserved hint tag of a jet call.**  A jet is ONE KIND of opcode-11 dynamic hint: its tag is
  the cord `%wild`, and the jet key is the value of its clue.  Every other tag is a hint the
  machine does not act on.  This file has no imports, so the generator, the row semantics and the
  compute chip can all name the same constant.
-/

namespace Nock.Jet

/-- The cord `%wild` as an atom (bytes `w i l d`, least significant first). -/
def wildTag : Nat := 0x646c6977

theorem wildTag_eq : wildTag = 1684826487 := rfl

end Nock.Jet
