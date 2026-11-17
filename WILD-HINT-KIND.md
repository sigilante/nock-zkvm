# Jets as a hint kind: `%wild`

A proposal against REL-5.4 (`7a51d916`), as a branch. Status: see
the end of layer 2. Layer 3, the end-to-end package, is not
started. The purpose of the branch is to show the change and its
price, not to be merged as is.

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
- **The key is not a formula atom.** Completeness bounds that
  covered the key as a leaf of the formula need a separate
  hypothesis (`JetKeyX`, layer 2).

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

## Layer 2: the compute chip and the library proofs

### The chip

`Handle/ChipHX.lean` is the one chip definition for every revision
(`ChipHX9` reuses it). On `s11j` rows:

| | REL-5.4 | this branch |
|---|---|---|
| jet record `jetRecX`, first field | `xFtth.v` (the tag) | `xSf1.v` (the clue's value) |
| tag | `xFtth.k = 0` (a small atom) | `xFtth.k = 0` and `xFtth.v = wildTag` |
| clue value | unconstrained beyond the child label | `xSf1.k = 0` (a small atom) |

That is two arithmetic gates and one equality gate, and no new
column: `sf1` already held the clue's value, bound to the clue
formula by the child label `(s, fttt, sf1)`. `ChipHX.s11j_wild`
exports the two new facts. `wildTag` lives in `Nock/Jet/Wild.lean`,
which imports nothing, so the generator and the chip name the same
constant.

### Soundness side

The row predicates that soundness goes through
(`GenuineNX.RowOutputNX`, `LocalVSX.RowSemX0`,
`RowSemChipX.sem_s11j`) take the jet id from the clue child's value
and **do not mention the tag**. `evalN` ignores the tag, so
soundness has no use for it. One consequence: no `wildTag < p`
hypothesis enters the soundness chain. At a toy field where `%wild`
is a big atom, the tag gate admits `wildTag mod p` in its place,
and that costs nothing, because no soundness statement reads the
tag. (The reviewers of layer 1 had expected this hypothesis to be
needed; keeping the tag out of these predicates avoids it.)

These modules are in the import closure of the J-8 soundness bound
(`Handle/LinkJ8A.lean`), so on this branch the bound is re-proved
against the new chip, not inherited.

### Completeness side

The per-row bounds (`HonestRowX.SmallX`, `ComplJ8.AxRowX`,
`ComplJ9ABinders.AxRowX9A`, `HonestCompX.RowOKX`) bound both the
tag and the clue value on jet rows. Call lists (`callsOf`,
`CalledIds`, the J-9 AL call tables) read `sf1`.

**One new hypothesis.** The honest-satisfaction theorems bound
every axis and id through `FormLeafX`: every atom of every formula
is small. A key that is the clue's *value* is not an atom of the
formula, so `FormLeafX` no longer covers it. `HonestPairX.JetKeyX q t`
states it directly: on every jet row, the clue's value, when an
atom, is below `q`. It is a hypothesis of
`computeChipVCLHX_honest_sat_tree` and `smallX_of_tree`; the
concrete inhabitant discharges it (`InhabJ8Comp.jetKey0`). A
constant clue `[1 id]` with `FormLeafX` implies it. Requiring the
clue to be syntactically `[1 id]` would remove the hypothesis at
the cost of one more cell decode per jet row.

### Test programs and literals

Hand-written jet programs in the headline set are restated in the
new form: the J-9 AL toy facts and the `mul`/`lt`/`div` demos, the
template-jet twin of `jp` (`Batch4939`, whose two calls now carry
their own clues `[1 7]` and `[1 8]`), the T0 demo, and the ALU
attack negative controls. The executables that generate demo runs
(`J8Dump`, `D5RedMain`, `J9ALEmit`) and `V1J8/D5Sizes` emit the new
form.

`Batch4771` is a literal trace printed by `nockvm-j8dump jet`; it is
regenerated with that tool, not edited.

### Status

Checked on this branch (Lean 4.35, two threads):

- **Headline set.** Every module imported by
  `scripts/delivery-axioms.lean` builds (10,527 jobs). The script's
  123 printed axiom footprints are identical, theorem by theorem, to
  REL-5.4's: 63 + 59 at `[propext, Classical.choice, Quot.sound]`,
  `pub_before_first_squeeze` at `[propext, Quot.sound]`, no
  `sorryAx`.
- **Outside the headline set.** The 22 library modules that name a
  changed definition and are not in the headline closure build, as
  do `nockvm-j8dump`, `nockvm-d5red` and `nockvm-j9alemit` (8,596
  jobs). Not built: the rest of the library (about 1,400 modules
  outside both sets, including the 48 GB module), which names none
  of the changed definitions.
- **Native checker.** `nockvm-j8dump jet` generates the tiny jetted
  program in the new form and its native `checkJ8` accepts it. The
  checker takes its gates from `ChipHX`, so it checks the new gates.

**Measured cost.** The clue `[1 id]` is a new cell; the earlier
`[1 0]` was hash-consed with an identical cell inside the compiled
template and cost nothing. So the cell table grows by one row per
distinct jet id in a program: 122 → 123 for the one-call program
(`Batch4771`), 157 → 159 for `jp`'s twin with two ids (`Batch4939`).
Columns, decoding and public-input shape are unchanged. Proof size
and verifier time are not measured; they need layer 3.

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
