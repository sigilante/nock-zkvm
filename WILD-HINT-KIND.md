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
template language and `evalN` are untouched.

That a jet row's *result* is right rests on the registered formula
equalling the body and the entry being faithful. Neither the tag
nor the key appears in that argument, and `evalN` ignores both. So
no key a prover can choose changes a result; it only decides
whether a hint is jetted or traced. The statements of `genX_sound`
and `genX_complete` are unchanged, and their proofs change by one
`rfl` in each jet case. `jetHit_spec` and `genX_jet_row` are
restated and re-proved.

The source of the key does enter the *row-level* proofs: how the
key is bound to the program (below), and two new gates.

## What does change in the trust argument

- **How the key is bound.** In REL-5.4 the key is part of the
  formula, bound by the cell-export records. Here it is the value
  of the clue, bound by the compute walk: on an `s11j` row the
  child label is `(s, fttt, sf1)`, so `sf1` must be the value of
  the clue formula on the same subject. REL-5.4's chip already
  enforces this (`Handle/ChipHX.lean:510`, kid-kind gate at `:280`).
- **Clue values become public.** The list of called ids is part of
  the public layout. With keys in the formula it holds constants;
  with keys from the clue it holds run-time values, which may
  depend on the subject (a clue `[0 2]`, say). The machine is not
  zero-knowledge, so no claimed property is lost, but a caller who
  wants constant keys should write constant clues.
- **`wildTag < p` becomes a hypothesis.** See layer 2.

## Layer 1: generator and row semantics (done)

| file | change |
|---|---|
| `Nock/Edit/GenX.lean` | `wildTag`, `wildCall`; `jetHit R b v c s` takes the clue value `v`; `jetHit_spec` concludes `b = atom wildTag ∧ v = atom id`; `genX_jet_row` takes the clue run as a hypothesis and concludes `t.children = [tD]` for that run |
| `Nock/Edit/GenXRows.lean` | `RowNX.SemN` at `s11j`: `ftth = atom wildTag ∧ sf1 = atom id` in place of `ftth = atom id`. The row already carries the clue's value in `sf1`; no column is added |
| `Nock/Edit/GenXDemo.lean` | the matmul demo uses the new form; `mat_tagged_not_jet`: the earlier form is now an `s11d` row with the same value; `mat_wrong_tag_not_jet`: a registered key and formula under a tag other than `%wild` is not a jet |
| `Nock/RedTeam/Batch2653Thm54GenX.lean` | negative controls restated in the new form |
| `Nock/Jet/Semantics.lean` | comments only: `jetCall` and the standalone §E row specs are marked as the earlier tag-as-id form |

Checked: `lake build Nock.Edit.GenXDemo
Nock.RedTeam.Batch2653Thm54GenX` succeeds. The printed axioms of
`genX_sound`, `genX_complete`, `genX_jet_row`, `mat_gen` and
`mat_rows` are `[propext, Quot.sound]`, as before.

Row counts in the demo are unchanged: 2 rows jetted, 2999 unjetted.

## Layer 2: prover data and the compute chip (not started)

The `scripts/delivery-axioms.lean` import set was built once
against the generator change. Two modules failed:
`Nock/Edit/GenXDemo.lean`, since fixed and part of layer 1, and
`Handle/ComplJ8Jet.lean`. Nothing that imports the latter was
attempted, and the set has not been rebuilt since. `ComplJ8Jet` is
the boundary because from there on the jet id is read from the
**tag column** `ftth`:

- `CalledIds` (`Handle/ComplJ8Jet.lean:39`) and `callsOf`
  (`Nock/V1J8/GenJet.lean:49`) collect `atomV r.ftth`.
- The chip's jet lookup record `jetRecX`
  (`Handle/ChipHX.lean:350`) is keyed on `xFtth.v`, and the gate
  `s11G` pins `xFtth.k = 0`.
- The row-bound predicates (`HonestRowX`, `ComplJ8`,
  `ComplJ9ABinders`) bound the id as `ftth = atom id → id < p`.
- The handle-level row semantics (`Handle/LocalVSX.lean:148`) reads
  `ftth = (0, id)`, and `RowOutputNX` at `s11j`
  (`Nock/Edit/GenuineNX.lean:64`) reads the id from the formula.

The intended change is uniform:

1. Key the record on the clue-value column: `xFtth.v` becomes
   `xSf1.v` in `jetRecX`.
2. Two gates on `s11j` rows: `xFtth.v = wildTag`, and `xSf1.k = 0`
   (the clue value is a small atom). The existing `xFtth.k = 0`
   stays. These gates are not needed for a right result; they are
   needed to state the row semantics (`ftth = (0, wildTag)`,
   `sf1 = (0, id)`).
3. Read `sf1` wherever a call's id is collected or bounded. The
   bound `id < p` moves with it: a key at or above `p` is a big
   atom and cannot be jetted, as in REL-5.4.
4. Carry `wildTag < p` as a hypothesis. The tag gate is an equation
   in the field, and the chip lemmas are generic in `p`. At
   Goldilocks it holds. At a toy field such as `p = 101`, `%wild`
   is a big atom and the small atom `wildTag mod p` would pass the
   gate in its place.

There is one chip definition for all revisions (`ChipHX`, reused
by `ChipHX9`), so the chip edit is made once. 109 files name one of
`jetRecX`, `s11G`, `CalledIds`, `callsOf`, `s11j_node` or
`genX_s11j`:

```
grep -rlE "jetRecX|s11G|CalledIds|callsOf|s11j_node|genX_s11j" \
  --include='*.lean' Nock nockvm-e2e TraceDemo | wc -l
```

That is a measure of reach, not a count of proofs that break. Files
that use the tag column as an id without naming one of those are
not in it.

Until layer 2 lands, the generator emits the new form and the chip
still accepts the earlier one. The J-8 soundness bound
(`Handle/LinkJ8A.lean`) does not import the generator, so it is
untouched and still holds, for the earlier-form chip. The
non-vacuity theorems and everything in the delivery set import the
generator and do not build, so on this branch they are not checked.
Statements about the chip no longer connect to the generator's
output; that costs completeness and consistency, not soundness.

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
