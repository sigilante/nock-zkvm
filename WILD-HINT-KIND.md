# Jets as a hint kind: `%wild`

A proposal against REL-5.4 (`7a51d916`), as a branch. All three
layers are ported: the generator, the compute chip with the library's
proofs, and the end-to-end package with its fixtures. Status and
measured cost are at the end of layers 2 and 3. The purpose of the
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
  enforces this (child labels at `Handle/ChipHX.lean:514`, kid-kind gate
  `(sS11j, xFttt)` at `:283`, on this branch).
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

That is one new arithmetic gate (`sS11j · xSf1.k`) and one new
equality gate (the tag value); the tag's kind gate was already there.
No column is added: `sf1` already held the clue's value, bound to the clue
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

Soundness in fact needs less than the predicates state: the proof
that a jet row's result is right (`GenuineNX.genuineNX_sem`) uses
`R id = some j`, `j.c = body`, the template relation and the clue's
termination, and never which `id` it was. Binding the id to the
clue's value is what makes dispatch deterministic, not what makes
it correct.

The remark about `wildTag < p` is a statement about soundness only. At a toy field where
`%wild` is a big atom, an honest `%wild` call fails the tag's kind
gate, so jets cannot be used there at all; no toy instance in the
release has jet rows. And the soundness predicates no longer say
that a jet row's tag is `%wild`. The chip enforces it at Goldilocks
(`s11_row` gives kind 0, `s11j_wild` gives the value, and
`wildTag < p`); `Handle/WildTagX.lean` states it as a separate
corollary, `s11j_tag`, which nothing in the soundness chain uses.

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
`computeChipVCLHX_honest_sat_tree` and `smallX_of_tree`. It is
necessary: the honest fill fails the `sf1.k = 0` gate when `id ≥ p`.
**Its only discharge is vacuous**: the concrete inhabitant
(`InhabJ8Comp.jetKey0`) has no jet rows, and no theorem exhibits
`computeChipVCLHX_honest_sat_tree` on a tree with one. (The
`ProgAxOK` completeness paths, which carry the same bound on the
clue value, are exercised non-vacuously by the J-9 AL toy facts,
the `mul`/`lt`/`div` demos, `jp`'s twin and the matmul gen-link.)
For a constant clue `[1 id]` the key is a formula leaf, so
`FormLeafX` should imply `JetKeyX`; that lemma is not proved. Requiring the
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

- **Final build.** One build of the headline set, every module that
  transitively imports a changed file (777, all but the 48 GB
  module), `Handle/WildTagX.lean` and the three executables succeeds
  (14,976 jobs) with no `sorryAx` printed.
- **Headline set.** Every module imported by
  `scripts/delivery-axioms.lean` builds. The script's
  123 printed axiom footprints are identical, theorem by theorem, to
  REL-5.4's: 63 + 59 at `[propext, Classical.choice, Quot.sound]`,
  `pub_before_first_squeeze` at `[propext, Quot.sound]`, no
  `sorryAx`.
- **Not built:** `Nock.RedTeam.Batch1420Thm54PartAL3Honest12` (the
  48 GB module, the one dependent excluded) and modules that import
  no changed file, whose oleans are unaffected.
- **Reviews.** Wizard: sound (soundness chain to `HoldsN` intact and
  no weaker; completeness hypotheses stronger by a necessary bound;
  `JetKeyX` discharged only vacuously, as noted above). Chevalier:
  sealed (no false result through a jet row; dropping the tag from
  the soundness predicates is safe).
- **Native checker.** `nockvm-j8dump jet` generates the tiny jetted
  program in the new form and its native `checkJ8` accepts it. The
  checker takes its gates from `ChipHX`, so it checks the new gates.

**Measured cost.** The clue `[1 id]` is a new cell unless that cell
already occurs in the table; the earlier `[1 0]` was hash-consed with
an identical cell inside the compiled template and cost nothing. In
both measured programs the cell table grows by one row per distinct
jet id: 122 → 123 for the one-call program
(`Batch4771`), 157 → 159 for `jp`'s twin with two ids (`Batch4939`).
Columns, decoding and public-input shape are unchanged. End-to-end
proof sizes are in layer 3.

## Layer 3: the end-to-end package

`nockvm-e2e/` is ported: its chip documents, chip literals, fixtures,
instance literals and the proofs that depend on them are regenerated
for the new chip, with the release's own tools.

**Chip documents** (`chipdocs/`). `j8_computeChipVCLHX.json` and
`j9a_computeChipVCLHX9.json` are re-emitted with the emitter in
`Exec/J9AEmitMain.lean` (`docJson`). The emitter was first checked by
re-emitting four unchanged documents (`j9a_axisChipJ9`,
`j9a_splitChipJ9`, `j8_cellChipHQKW`, `j8_atomChipHQL`): all four are
byte-identical to the shipped files. The two compute documents differ
from REL-5.4's by exactly two constraints each (227 → 229 and
276 → 278, both `base_transition`), with the same columns and the
same document header.

**Chip literals** (`Exec/J8Chips.lean` `chipCompute`,
`Exec/J9AChips.lean` `chipCompute9`). Regenerated with the in-repo
generator `J9AChipsGen.genChip`, which was first checked to reproduce
the shipped `chipAtom` and `chipCell` literals exactly. The kernel
ties `tie_compute`, `tie_compute9` (`tieB spec lit`, by `decide
+kernel`) hold for the new literals.

**Fixtures** (`fixtures/j9al-add`, `fixtures/j9alj-jp`). Regenerated
with `nockvm-e2e-j9alemit2` and `nockvm-e2e-j9al-prove` (`jp` with
`--reg-catj`), `jp.pub.json` with `verify-fam index`, and
`SHA256SUMS` rewritten over the same file lists. The README's
procedure accepts both, with `nockvm-e2e-verify-fam verify --vk` and
with the certified `nockvm-e2e-verify-cert`. Negative checks: the
REL-5.4 `add` fixture is rejected by the new verifier (`chipsOkF`: a
loaded chip is not a literal of the family), and `--wrong-claim` is
rejected by the prover's in-process verifier (`public relation
fails`). The README's jet example also runs and verifies in the new
form.

**Instance literals** (`Exec/AddALR.lean`, `Exec/JpALR.lean`). The
release does not include their generator. They were patched from the
new instances as `FlatFam.loadInstF famJ9AL` loads them, each old
value first asserted equal to the old literal. The changes are: the
claim formula's tokens (`[%wild [1 7]]`), the cell table's `hN`
(116 → 117, 157 → 159), two preprocessed columns (170, 171), the
compute chip's K-tag array lengths (all `false`, +3 shared, +2
constraints), and `jp`'s primitive cell index (122 → 124).

**Proofs.** Hard-coded sizes follow (`LinkJ9ALAdd`, `LinkJ9ALToy`,
`GenJp`, `LinkJ9ALJjp`: 116 → 117, 232 → 234, 157 → 159, 314 → 318,
122 → 124), `jp`'s two calls get their own clue trees (`GenJp`), and
the clue values in `JpClaim`'s truth proof are the keys.

**Checked.** The whole package builds (17,750 jobs). The ten
end-to-end headlines (`nock_e2e_J9AL_succinct`{,`_B`,`_S`},
`nock_e2e_J9ALJ_succinct`{,`_B`,`_S`}, `nock_e2e_J9AL_numbers`,
`nock_e2e_J9A_succinct`, `verifyBytesL_sound`, `verifyBytesLJ_sound`)
depend on `[propext, Classical.choice, Quot.sound]`. The build's
8,094 axiom printouts name nothing else and no `sorryAx`.

**Measured cost, end to end**, REL-5.4 fixture against the new one:

| | `add` (1 call) | `jp` (2 calls) |
|---|---|---|
| cell-table rows | 116 → 117 | 157 → 159 |
| padded table height, columns | unchanged | unchanged |
| opened trace values `vT` | 6,927 = 6,927 | 7,389 = 7,389 |
| quotient values, roots, FRI final | unchanged | unchanged |
| statement `z` (field elements) | 560 → 562 | 3,038 → 3,042 |
| Merkle paths `trees` | 425,385 → 438,409 | 474,344 → 465,003 |
| proof JSON bytes | +2.9% | −2.0% |

The statement grows by two elements per jet call: atom `0` encodes as
zero limbs and the key as one limb plus a length; the tag `%wild` and
the old tag `7` are both one limb. The Merkle-path count moves with
how many of the 170 Fiat–Shamir query positions coincide (166 → 169
distinct for `add`, 170 → 168 for `jp`), which is why the two
programs move in opposite directions; that is sampling, one sample
each, not a cost of the change. Verifier time was not measured
against REL-5.4.

**Known issue, not introduced here.** On macOS
`nockvm-e2e-j9al-prove` exits 1 after writing all its outputs, because
its peak-memory report reads `/proc/self/status`; `scripts/run-free.sh`
stops at that step.

## An open choice

The registry is keyed by a natural number. A richer clue, such as
`[label ver digest]`, would need either a noun-keyed registry or a
rule for which atom inside the clue is the key. This branch takes
the whole clue value as the key and requires it to be an atom.
