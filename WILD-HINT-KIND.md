# Jets as a hint kind: `%wild`

A proposal against REL-5.4 (`7a51d916`), as a branch. Status: **layer
1 of 3 is done and builds; layers 2 and 3 are not started, and the
headline theorems do not build on this branch.** The purpose of the
branch is to show the change and its price, not to be merged as is.

## The change

In REL-5.4 a jet call is the dynamic hint `[11 [id clue] body]`. The
hint's tag is the jet's id; the clue is evaluated and discarded.

In Nock as it is used elsewhere, the tag of an opcode 11 names the
*kind* of hint (`%fast`, `%slog`, `%spot`, `%memo`) and the clue
carries the payload. Under tag-as-id the machine has no notion of a
hint kind: every tag is a candidate jet id, and no emission can be a
jet both here and in a runtime that follows the convention.

This branch makes a jet one hint kind:

```
REL-5.4:      [11 [id    clue    ] body]
this branch:  [11 [%wild [1 id]  ] body]
```

- The tag must be the atom `%wild` (`0x646c6977`, `wildTag`).
- The jet key is the **value of the clue**, which must be an atom.
  `[1 id]` is the cheap spelling (one `s1` row); any clue formula
  with that value dispatches the same way.
- Everything else is as before: the registered formula must equal
  the body exactly, the template must answer on the subject, and a
  miss is an ordinary dynamic hint.

## What does not change

The registry type, `Faithful`, `Complete`, `VerifiedRegistry`, the
template language and `evalN` are untouched. Soundness of a jet row
rests on the registered formula equalling the body and the entry
being faithful; where the key is read from does not enter. In the
generator's soundness and completeness lemmas (`genX_sound`,
`genX_complete`) the change is one extra `rfl` in each jet case.

## Layer 1: generator and row semantics (done)

| file | change |
|---|---|
| `Nock/Edit/GenX.lean` | `wildTag`, `wildCall`; `jetHit R b v c s` takes the clue value `v`; `jetHit_spec` concludes `b = atom wildTag ∧ v = atom id`; `genX_jet_row` takes the clue run as a hypothesis |
| `Nock/Edit/GenXRows.lean` | `RowNX.SemN` at `s11j`: `ftth = atom wildTag ∧ sf1 = atom id` in place of `ftth = atom id`. The row already carries the clue's value in `sf1`; no column is added |
| `Nock/Edit/GenXDemo.lean` | the matmul demo uses the new form; new theorem `mat_tagged_not_jet`: the old form is now an `s11d` row with the same value |
| `Nock/RedTeam/Batch2653Thm54GenX.lean` | negative controls restated in the new form |

Checked: `lake build Nock.Edit.GenXDemo
Nock.RedTeam.Batch2653Thm54GenX` succeeds. The printed axioms of
`genX_sound`, `genX_complete`, `genX_jet_row`, `mat_gen` and
`mat_rows` are `[propext, Quot.sound]`, as before. Not reviewed by
anyone but the author of the patch.

Row counts in the demo are unchanged: 2 rows jetted, 2999 unjetted.

## Layer 2: prover data and the compute chip (not started)

Building the `scripts/delivery-axioms.lean` import set on layer 1
fails first at `Handle/ComplJ8Jet.lean`, and everything behind it is
not attempted. That file is the boundary because from there on the
jet id is read from the **tag column** `ftth`:

- `CalledIds` (`Handle/ComplJ8Jet.lean:39`) and `callsOf`
  (`Nock/V1J8/GenJet.lean:49`) collect `atomV r.ftth`.
- The chip's jet lookup record `jetRecX`
  (`Handle/ChipHX.lean:350`) is keyed on `xFtth.v`, and the gate
  `s11G` pins `xFtth.k = 0`.
- The row-bound predicates (`HonestRowX`, `ComplJ8`,
  `ComplJ9ABinders`) bound the id as `ftth = atom id → id < p`.
- The handle-level row semantics (`Handle/LocalVSX.lean:148`) reads
  `ftth = (0, id)`.

The intended change is uniform:

1. Key the record on the clue-value column: `xFtth.v` becomes
   `xSf1.v` in `jetRecX`.
2. Two gates on `s11j` rows: `xFtth.v = wildTag`, and `xSf1.k = 0`
   (the clue value is a small atom). The existing `xFtth.k = 0`
   stays.
3. Read `sf1` wherever a call's id is collected or bounded.

There is one chip definition for all revisions (`ChipHX`, extended
by `ChipHX9`), so the chip edit is made once. 116 files mention one
of the names involved (`jetRecX`, `s11G`, `CalledIds`, `callsOf`,
`s11j_node`, `genX_s11j`, or the tag column as an id); that is an
upper bound on the files touched, not a count of proofs that break.
By directory: 57 in `Handle/`, 12 in `Handle/J9AL/`, 11 in
`Handle/J9A/`, 8 in `Handle/TU/`, 17 in `RedTeam/`, 6 in `V1J*/`,
5 in `nockvm-e2e/`.

Until layer 2 lands, the chip on this branch still accepts the old
form and the generator emits the new one, so soundness statements
still hold (they do not mention tags) and completeness does not.

## Layer 3: the end-to-end package (not started)

The chip appears in `nockvm-e2e/` as kernel-checked literals. Two
more gates change the constraint list, so the literals, the
verification keys and the shipped fixtures (`add`, `jp`) would be
regenerated, and any numeric lemma that depends on the constraint
count re-checked. Not examined beyond that.

## An open choice

The registry is keyed by a natural number. A richer clue, such as
`[label ver digest]`, would need either a noun-keyed registry or a
rule for which atom inside the clue is the key. This branch takes
the whole clue value as the key and requires it to be an atom.
