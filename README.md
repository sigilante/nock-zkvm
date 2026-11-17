# NockVM J-8, J-9 B, J-9 A and J-9 AL

> **Status: alpha research release.** This is not production software. It has not been independently audited and must
> not be used in production. See [Review and audit](#review-and-audit).

A Lean 4 formalization of J-8, J-9 B, J-9 A and J-9 AL, four revisions of one arithmetization of full Nock (opcodes 0–11 over unbounded
natural-number atoms, with jets) over the Goldilocks field, with kernel-checked soundness and completeness theorems.
J-9 B is J-8 with claim atoms of any size; J-9 A is J-9 B with op-0 / op-10 axes beyond `p` (up to 62 limbs of 2^32), adding
an axis chip, a split chip and a twin compute chip (`docs/SPEC.md` §5). J-9 AL is J-9 A plus big-atom arithmetic
primitives (add, sub, lt, mul, div, mod on big atoms) as jets checked by an ALU chip (`docs/SPEC.md` §6).
Jet templates may also take and return opaque nouns (type `N`), so a jet can pass a big atom or a cell through unchanged.

The source is public at https://github.com/nockchain/nock-zkvm, tag `rel5.4`.

## Overview

**Where things are.** `docs/README.md` lists every document. The specification is `docs/SPEC.md`; the trusted base and
the gaps are `docs/LIMITS.md`; how to build and re-run everything is `docs/REPRODUCE.md`; every named theorem with its
location and `#print axioms` line is `docs/THEOREMS.md` (generated); `docs/GLOSSARY.md` maps the release labels to names.

**Soundness.** For a faithful jet registry, row budgets within the corner of `docs/SPEC.md` §4.1.1 (tables of at most
`2^31` rows) and `|K| = p^3`: for any claim `*[subject formula] = result` and any staged prover strategy,
Pr over the verifier's coins [ the verifier accepts (`AcceptsJ8V`, `AcceptsJ9V`, `AcceptsJ9A` or `AcceptsJ9AL`) ∧ the claim is false under `evalN` ] < 2^-155, where `evalN`
(`Nock/Reference.lean`) is the reference Nock interpreter over natural-number atoms (not a field-reduced semantics).
The statement is about a staged prover map over polynomial traces: in this library no commitment scheme or low-degree test is
modelled, and Fiat–Shamir is executable code, not a theorem (`docs/SPEC.md` §11.1). The package `nockvm-e2e/` (below) adds
both: a FRI-based succinct verifier with a kernel-checked soundness theorem in the random-oracle model.

The specification (machine, chips, constraints, transcript, theorems and hypotheses, error figures, scope) is `docs/SPEC.md`.

**Trace uniqueness (P1 fragment).** For claims whose formulas use only ops `0, 7, 10` and cons, with every op-0 / op-10
axis in `[1, 2^61)` and every leaf of the subject, formula and result `< p`, the J-8 verifier with canonical-form pins accepts only the honest generator's transcript, except with probability `< 2^-119`
(`trace_unique_prob_119`; split `2^-154 + 2^-120`). The size premise `P1SizeOK` is a hypothesis: it does not follow from the
fragment, since nested op-7 formulas can make the run's nouns grow exponentially.

## In this release

The certified verifier, the front end for arbitrary programs and the `ACCEPT-UNCOVERED` verdicts are described in
`nockvm-e2e/README.md`; `rapFriEps_le_Q` (the main-proof numbers term for every Fiat–Shamir query budget) is in
`docs/SPEC.md` §9.4.

- *A template-jet J-9 AL run* (`Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean`): with no hypothesis, a J-9 AL run that calls
  a compiled template jet (id `7`) and a big-atom primitive (`add`, id `8`) is generated and accepted by the executable
  checker (`genLinkTpl`); the closed completeness instance holds there with a non-vacuous template clause
  (`complJ9AL_tpl`); every chip has at most `nRowsTpl = 159` rows, and the generator's record is accepted at every common
  orbit that fits it (`honestTplUnif`). This is the program the end-to-end template-jet headline below is instantiated at.
- *End-to-end, template jets* (`nockvm-e2e/`): the headline `nock_e2e_J9ALJ_succinct_B` covers programs that call template
  jets from a fixed catalogue `catJ` as well as the big-atom ALU jets.
- *Fiat–Shamir statement binding* (`nockvm-e2e/`): the executed `j9al` and `j9alj` verifiers bind the full public input into the Fiat–Shamir
  transcript (the gate `zBind`), so a proof verifies only for the public input it was produced for; the jet-free `j9a` path does not bind
  (`docs/SPEC.md` §9.3). The release headlines
  are the `_B` forms, which take the binding verdicts as hypotheses. The kernel-checked theorem is non-adaptive
  (public input fixed before the oracle).
- *ALU last-row mask*: the ALU chip's next-row gates are multiplied by `1 − isLT` (the verifier-fixed last-row mask;
  `docs/SPEC.md` §6.2), so they are not imposed from the last row onto the wrapped first row. An honest ALU table is
  therefore accepted on any orbit that fits it (`genJ9ALXJ_honest_at'`). Soundness (`probJ9AL_final_clean`) is proved for
  this predicate with the `< 2^-155` figure.

## End-to-end package (`nockvm-e2e/`)
`nockvm-e2e/` is a separate Lake package (Apache-2.0) over this library and ArkLib: a FRI-based STARK prover and verifier
for full Nock with big-atom ALU jets and catalogue template jets, with kernel-checked soundness of the succinct verifier.
The executable accepts only instances whose chips match its literal list (`docs/LIMITS.md`, end-to-end row 7).
Headlines `nock_e2e_J9AL_succinct_B` and `nock_e2e_J9ALJ_succinct_B`: if the verifier executable accepts a claim `c`, every
adversary within the stated query budgets has `Pr[accept ∧ c false] ≤ 2^-82 + (bfriErr + mcROM + coll)`, for a claim and
public input fixed before the oracle, for query budgets `Q_FS, Q_H ≤ 2^64` and `V ≤ 2^32`; `nock_e2e_J9AL_numbers` bounds the
bracket by `2^-83 + 2^-120` under its binders (`T ≤ 2^40`). Limits: not zero-knowledge; random-oracle model with Tip5;
non-adaptive; verification key recomputed by `verify --vk` (trusted only in `verify-online`, which no theorem covers); the executable's verdict is compiled code, and some gates are executed checks, not
kernel facts. See `nockvm-e2e/README.md` and `docs/LIMITS.md`.

## Headline theorems

Grouped by label in `docs/THEOREMS.md` (generated, with locations and axioms lines); the table below lists the library's
main rows.
| theorem | file | statement |
|---|---|---|
| `probJ8V_final_clean` | `Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8.lean` | soundness: `Pr_χ[(∃ M, AcceptsJ8V …) ∧ ¬ HoldsN c] < 2^-155` |
| `probJ8V_verified` | `…/Handle/CleanJ8V.lean` | the same at a `VerifiedRegistry` (a jet registry carrying its own faithfulness proof) |
| `probJ9B_final_clean` | `…/Handle/LinkJ9G.lean` | the same bound for `AcceptsJ9V`, where the claim may contain atoms `≥ p` |
| `complJ8_closed`, `complJ9B_closed` | `…/Handle/ComplJ8Closed.lean`, `…/Handle/ComplJ9BClosed.lean` | completeness: under the run binders of `docs/SPEC.md` §4.3, an honest run is accepted at every good coin, `Pr[¬ good] ≤ ε_c`, and at `|K| = p^3` `ε_c < 2^-120` |
| `probJ9A_final_clean` | `…/Handle/J9A/ProbJ9A.lean` | J-9 A soundness: for `Rg.Faithful` and the numeric binders (budgets `hr`, `hAX`, `hSP`, `hk`, `hmax`, `hg`, `hLC`…`hLV`, `hnM`, `hreg9`), `Pr_χ[(∃ M, AcceptsJ9A δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155` for every staged `Q` (`StJ9A Q`) |
| `complJ9A_closed` | `…/Handle/J9A/ComplJ9AClosed.lean` | J-9 A completeness: binders `hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx h31A`; at `B := BRun9A δ b Rt hgen hpG h31A`, `∀ χ, B.Good χ → AcceptsJ9A …`, `Pr[¬ Good] ≤ B.epsC`, `StJ9A B.tr`, `HoldsN`, and at `|K| = p^3` `B.epsC < 2^-120` with an accepting coin |
| `genJ9AX_honest_at` | `…/Handle/GenPortJ9AHonest.lean` | executable link, jet-free runs: if `genJ9AX Rg.R fuel s f χe = some I` and `χe` is a good coin (`hχ`), then for every admissible orbit choice `o` (`OrbAdm I o`), `AcceptsJ9A` holds of the generated trace data `withOrb I o`; binders as `complJ9A_closed`, plus `hcid` in the lemmas below |
| `checkJ9AX_genJ9AX` | `…/Handle/GenPortJ9AHonest.lean` | under the same hypotheses, `checkJ9AX I = true` (the executable checker accepts the generated input) |
| `epsC_lt`, `exists_good_coinE` | `…/Handle/GenPortJ9AHGoodCoin.lean` | jet-free runs (binder `hcid : CalledIds t = ∅`): `(BRun9A …).epsC < 1 / 2 ^ 120`, and `∃ χe : CoinsE, (BRun9A …).Good (toχ χe)` (a good coin exists in executable form) |
| `genJ9AXJ_honest_at`, `checkJ9AX_genJ9AXJ` | `…/Handle/GenPortJ9AHonestJ.lean` | the same two statements for the jet-calling generator `genJ9AXJ Rg.R Rt fuel s f χe`, with the extra hypothesis `hC : CheckedRegistry.CompiledBy p Rg Rt` (a registry checked once: every entry is compiled from `Rt`, with `axPosB`, `WellTyped` and axes `< p`) |
| `exists_good_coinEJ` | `…/Handle/GenPortJ9AHGoodCoinJ.lean` | jet-calling runs: `∃ χe : CoinsE, (BRun9A … Rt …).Good (toχ χe)` under `hC` |
| `complJ9A_closed_of` | `…/Handle/ComplClosedChecked.lean` | `complJ9A_closed` with `hRt`, `hregAx` replaced by the single hypothesis `hC : CheckedRegistry.CompiledBy p Rg Rt` (likewise `complJ8_closed_of`, `complJ9B_closed_of`) |
| `probJ9AL_final_clean` | `…/Handle/J9AL/ProbJ9AL.lean` | J-9 AL soundness: for `Rg.Faithful`, every staged `Q` (`StJ9AL Q`) and the numeric binders of `probJ9A_final_clean` plus the ALU row bound `hAL : r.AL ≤ 2^31` (and `hreg9P` counting the primitive table), `Pr_χ[(∃ M, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155` |
| `complJ9AL_closed`, `complJ9AL_closed_of` | `…/Handle/J9AL/ComplJ9ALClosed.lean` | J-9 AL completeness at runs calling template jets and ALU primitives: the J-9 A binders at the template table `rtP Rt prims`, distinct primitive ids registered with their specs (`hnd`, `hprim`), ALU length `aluLen < 2^31` (`h31L`; the table has `aluLen + 1 ≤ 2^31` rows), primitive operands within 62 limbs (`hlimb`), no `dec` primitive (`hnoDec`); conclusions as `complJ9A_closed` with `AcceptsJ9AL`, `StJ9AL`; `_of` takes a checked registry instead of `hRt`, `hregAx` |
| `checkJ9ALX_iff` | `Nock/V1J9AL/CheckJ9ALIff.lean` | the executable J-9 AL checker: `checkJ9ALX I = true ↔ ∃ hv : ValidJ9AL I, AcceptsJ9AL … (mkPbAL I hv) Rg …`, for a registry consistent with the input (`RegOK`) that registers every primitive the input uses with its spec |
| `genJ9ALXJ_honest_at`, `checkJ9ALX_genJ9ALXJ` | `…/Handle/GenPortJ9ALHonestJ.lean` | executable link: the J-9 AL generator's output is accepted by `AcceptsJ9AL`, and by `checkJ9ALX`, at a good coin, under the binders of `complJ9AL_closed` |
| `runStaged_eq`, `checkJ9ALX_staged` | `…/Handle/GenPortJ9ALHStaged.lean` | the generator in three stages (before the first coin round, after it, after the second): fed the two coin slices of any coin vector, it returns exactly what the one-shot generator returns; its output is accepted by `checkJ9ALX` |
| `epsilonOf_listJ9AL`, `soundJ9AL_pointwise`, `oneRound_listJ9AL` | `…/Handle/J9AL/E2EJ9ALIface.lean` | the J-9 AL soundness split into its parts: a list `listJ9AL` of bad-event summands whose total probability is `< 2^-155`, acceptance outside every summand implies `HoldsN c`, and each summand is a one-round event; binders as `probJ9AL_final_clean` |
| `genJ9ALXJ_honest_at'` | `…/Handle/GenPortJ9ALHOrbFree.lean` | executable link at a free ALU orbit: every `genJ9ALXJ` output at a good coin is valid and accepted by `AcceptsJ9AL` at every orbit choice `o` with `OrbAdmL' I o` (each chip's orbit valid and its rows fit), the ALU orbit not pinned to the generator's own; binders as `complJ9AL_closed_of`. `genJ9ALXJ_honest_at_of'` recovers the pinned form |
| `pregOK_of_tableCheck`, `pregOK_of_tableCheck_interp`, `pregTableOK_iff` | `…/Handle/J9AL/PregTableCheck.lean` (namespace `GenPortJ9ALHAluE`) | a computable check `pregTableOK` on a table of the ALU's `preg` columns (`sP`, `pId`, `pOp`) implies the pre-column spec `PregOK` consumed by `ALChipOK`, for polynomials that evaluate to the table at the row nodes and for the table's Lagrange interpolant; the check is equivalent to the length bound and the pointwise equations |
| `trace_unique_prob_119` | `…/Handle/TU/TraceUniqueP1Closed.lean` | trace uniqueness on the P1 fragment: for a claim `c` with `P1FragC c` (formula ops among `0, 7, 10` and cons, every op-0 / op-10 axis in `[1, 2^61)` (`axesB`), leaves of subject, formula and result `< p`, a run exists) and the size premise `P1SizeOK p c` (the canonical run fits `2^31` rows and its roots' leaf bound), at `|K| = p^3` and for every staged prover strategy `Q`, `Pr_χ[AcceptsCanonP1 … (Q χ) ∧ Q χ ≠ canonOfP1 … χ] < 2^-119`: an accepted transcript is the honest generator's transcript `canonOfP1 χ`. `AcceptsCanonP1` is the J-8 verifier at the canonical layout `canonPb` (rows `rowsP1`, budget `0`, empty registry) with the canonical-form pins of `…/Handle/TU/StatementP1.lean` (`AcceptsCanon`), `…/Handle/TU/UniqueP1.lean` and `…/Handle/TU/TraceUniqueP1.lean` |
| `trace_unique_prob_split` | `…/Handle/TU/TraceUniqueP1Closed.lean` | the same probability `≤ 2·ε + Pr[¬ Good]` with, at `|K| = p^3`, `2·ε < 2^-154` (soundness events) and `Pr[¬ Good] < 2^-120` (J-8 completeness) as separate conjuncts |
| `canon_eq_closed`, `trace_unique_good_final`, `canon_complete'` | `…/Handle/TU/TraceUniqueP1Closed.lean`, `…/Handle/TU/TraceUniqueP1.lean`, `…/Handle/TU/CanonSideP1.lean` | the pointwise forms: `canon_eq_closed`, at a good coin outside the soundness events (at the tuple's trace and at the canonical one) a tuple accepted by `AcceptsCanonP1` is the canonical tuple; `trace_unique_good_final`, two accepted tuples at one such coin are equal, given that the second tuple's compute requests cover the honest reads (`hcov'`); `canon_complete'`, the canonical transcript is accepted at every good coin and `Pr[¬ Good] ≤ ε_c` |
| `genLinkMat` | `Nock/RedTeam/Batch4937Thm54J9AMatmulGenLink.lean` | with no hypothesis: on a jetted `2 × 2` matrix product (compiled `matmul` template as jet `7`), some coin vector makes `genJ9AXJ` produce an input `I` with `checkJ9AX I = true` |
| `genLinkTpl`, `complJ9AL_tpl`, `honestTplUnif` | `Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean` | with no hypothesis: on a J-9 AL run that calls a compiled template jet (id `7`) and a big-atom primitive (`add`, id `8`), some coin vector makes `genJ9ALXJ` produce an input `I` with `checkJ9ALX I = true`; the `complJ9AL_closed` instance there (template clause not vacuous); every chip has at most `nRowsTpl = 159` rows (`rowsTpl_le`, any coin; `nRowsTpl_le_768`), and the generator's record is valid and accepted at every common orbit `⟨h, ω⟩` with `orderOf ω = 3 * 2^h` and `nRowsTpl <= 3 * 2^h` |
| `compile_faithful`, `compile_complete`, `interp_sound`, `interp_complete` | `Nock/Jet/Autogen.lean`, `Nock/Jet/Interp.lean` | the jet template compiler and interpreter, including templates with opaque-noun (`N`) arguments and results |
| `complJ9A_closed_of_N` | `Nock/RedTeam/Batch4892Thm54T0Demo.lean` | J-9 A completeness at a run whose jet takes a big atom as an opaque noun |
| `HoldsN` | `Nock/Jet/Semantics.lean` | the target: `∃ fuel, evalN fuel c.subject c.formula = some c.result` |

Non-vacuity witnesses (honest instances inside the exact hypotheses): `nvJet_final_const`, `nvJet_hyps_final_clean`,
`eq5_final_const`, `probJ9B_nonvacuous_demo`, `complJ8_closed_toy(_figure)`, `complJ9B_toy(_figure)`; for J-9 AL
`complJ9AL_toy` (`Batch4921`), the mul/lt/div figures `complJ9AL_toy_figure` (`Batch4932`–`Batch4934`), `acceptsJ9AL_withPrims`
(`Batch4930`), `acceptsJ9AL_noAlu` (`Batch4935`), `genLink_toy` (`Batch4936`), `genLinkTpl` and `honestTplUnif` (`Batch4939`, a template-jet run); for trace uniqueness `toy_trace_unique_119` (`Batch4938`, at `*[[1 2] [0 2]] = 1`, no claim-side hypothesis) and `toy_trace_unique_119_cons` (an autocons claim); false claims at which the soundness bound is read (`false_claim_rejected_AL`,
`wrap_claim_rejected_AL` (`Batch4922`), `nc16_cell_operand_rejected_AL` (`Batch4923`): acceptance probability `< 2^-155`), and one
structural rejection (`opConfusion_rejected`, `Batch4923`); `N`-typed jets:
`complJ9A_N_figure`, `good_coin_N`, `numerics_N` (`Batch4892`, `Batch4893`).

Namespaces `Nock.RedTeam.BatchNNNN` live in modules `Nock.RedTeam.BatchNNNN<Suffix>`; the number is only a sequence index,
and several headline theorems live there. The namespace `Nock.NockVMROM.Thm54.VclL.Handle` is an opaque prefix (see
`docs/SPEC.md` §0).

## Build
Toolchain: the version in `lean-toolchain` (`leanprover/lean4:v4.35.0`); Mathlib `v4.35.0`.
```
lake exe cache get                         # Mathlib build cache
lake build                                 # library `Nock`
lake build nockvm-j8check nockvm-j9dump nockvm-j9aemit nockvm-j9alemit   # the native checker, the J-9 B demo, the J-9 A and J-9 AL trace dumps
```

`lakefile.toml` also defines the library `NockPure` and the executables `trace-demo`, `nockvm-j8dump` and `nockvm-d5red`.
`scripts/delivery-axioms.lean` prints the axioms of the checked declarations.

`nockvm-j9aemit [OUTDIR] [prog]` (`prog` = `toy` | `absent` | `corner-t1` | `corner-t5`; `TraceDemo/J9AEmit.lean`) generates a
J-9 A instance with `genJ9AX` (empty registry, coins from a pseudo-random generator, not Fiat–Shamir), checks it with
`checkJ9AX`, and writes the chip traces (`<id>.trace.json`), `coins.json` and `pubeq.json` under `OUTDIR/traces/trace-<prog>/`.
It exits with status 1 and writes nothing if the check is not `true`. Its output is executable evidence only.
`nockvm-j9alemit [OUTDIR] [prog] [add|mul]` (`TraceDemo/J9ALEmit.lean`) does the same for J-9 AL with `genJ9ALXJ` and
`checkJ9ALX`; with a third argument it runs a program that calls the `add` or `mul` primitive (ALU chip on). Executable evidence only.

**Memory.** The full `lake build` needs about 48 GB of RAM because of one module,
`Nock.RedTeam.Batch1420Thm54PartAL3Honest12`, on which no headline theorem depends. To check the headline theorems
without it, build exactly the modules that `scripts/delivery-axioms.lean` imports:
```
lake build $(sed -n 's/^import //p' scripts/delivery-axioms.lean)
```
That subset is about 1480 modules (the full library has 2972); it does not import the 48 GB module. Measured once:
a from-scratch build of that subset together with the executables and the library modules `nockvm-e2e` imports (Mathlib
built from source, 2 threads) peaked at 16.7 GB of RAM and took 79 minutes.

## Check
```
lake env lean scripts/delivery-axioms.lean
```

prints `#print axioms` for the checked declarations (123 in total: the 17 of J-8 and J-9 B first, then the J-9 A
declarations of `docs/SPEC.md` §5, then J-9 AL (§6), the `N`-typed jets and the J-9 AL end-to-end interface, then the
free-orbit link and the `preg` table check, trace uniqueness (§7) and the template-jet run (`Batch4939`), in the same format). Long rows wrap in `lean`'s output; compare after joining lines.
Expected output:

```
'Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8.probJ8V_final_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8V.probJ8V_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.VerifiedRegistry.ofCompiled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G.probJ9B_final_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed.complJ9B_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4776.nvJet_hyps_final_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4777.nvJet_final_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4779.eq5_final_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4812.probJ9B_nonvacuous_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4842.complJ8_closed_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4842.complJ8_closed_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4856.complJ9B_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4856.complJ9B_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J8.Check.checkFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J8.Check.checkJ8_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.DriverJ8.TranscriptJ8.pub_before_first_squeeze' depends on axioms: [propext, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9A.probJ9A_final_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent.complJ9A_closed_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed.complJ9A_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4881.probJ9A_nonvacuous_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4882.complJ9A_absent_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4882.complJ9A_absent_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4883.complJ9A_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4883.complJ9A_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.ptrE_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.infoOfE_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.sxE_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.mvE_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.genJ9A_pointer_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.epsilonOf_listJ9A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.soundJ9A_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.oneRound_listJ9A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ProviderG.acceptsGenericG_j8_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9A.acceptsGeneric_j9a_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9A.FillX9.colX9E_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9A.FillX9.nodeLab9E_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9A.CompX9.gatesHX9_src' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9A.CompX9.checkCompX9_gates_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.genJ9AX_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.axGenE_cols' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.pubsXE_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.spGenE_cols' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.pubsSE_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rhoS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9A.CheckJ9AIffComp.checkJ9AX_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.checkJ9AX_genJ9AX' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.badE_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.epsC_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.exists_good_coinE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ8_closed_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ9A_closed_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ9B_closed_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.checkJ9AX_genJ9AXJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.badE_leJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.epsC_ltJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.exists_good_coinEJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed.complJ9AL_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed.complJ9AL_closed_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.honest_rec_atJL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9ALX_staged' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9AX_stagedA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStagedA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9AL.probJ9AL_final_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4921.complJ9AL_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4922.false_claim_rejected_AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4922.wrap_claim_rejected_AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4923.nc16_cell_operand_rejected_AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4923.opConfusion_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4930.acceptsJ9AL_withPrims' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4932.complJ9AL_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4933.complJ9AL_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4934.complJ9AL_toy_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4935.acceptsJ9AL_noAlu' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4936.genLink_toy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4937.genLinkMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.V1J9AL.CheckJ9ALIff.checkJ9ALX_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.Autogen.compile_faithful' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.Autogen.compile_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.Autogen.compile_jetSpec_faithful' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.Interp.interp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.Jet.Interp.interp_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4892.complJ9A_closed_of_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4892.complJ9A_N_figure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4893.good_coin_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4893.numerics_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.listJ9AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.epsilonOf_listJ9AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.soundJ9AL_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.oneRound_listJ9AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.preL_eval_pregCol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.lastRow_S_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.honest_rec_atJL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.genJ9ALXJ_honest_at'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.genJ9ALXJ_honest_at_of'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregTableOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregOK_of_tableCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregOK_of_tableCheck_interp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trace_unique_good_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.canon_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_119' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.hcovC_P1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canon_complete'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4938.toy_trace_unique_119' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.genLinkTpl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.complJ9AL_tpl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.honestTpl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.rowsTpl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.nRowsTpl_le_768' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nock.RedTeam.Batch4939.honestTplUnif' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the standard axioms occur (122 lines with `propext, Classical.choice, Quot.sound`, one with `propext, Quot.sound`): no
`sorry`, no `native_decide`.

**The jetted matmul.** `genLinkMat` (above) is the kernel-checked statement that the generator and the executable checker
agree on the jetted 2×2 matrix product. That a perturbed J-chip cell makes `checkJ9AX` return `false` on it
(`Nock.RedTeam.Batch4885`) is executable evidence only, not a kernel-checked theorem.

## Demo (J-8 and J-9 B checker)

`scripts/demo-candidate.sh` is the library demo. For J-9 AL and the end-to-end package see
`nockvm-e2e/README.md`.
```
LAKE=lake scripts/demo-candidate.sh
```

Steps: (a) honest run accepted; (b) a tampered trace rejected; (c) a false claim rejected; (d) a jetted 2×2 matrix
product accepted; (e) big atoms (op 5 on `p+1 = p+1`, and on `p` vs `p+1`) accepted; (f) a J-9 B claim with a big atom
accepted and its false variant rejected; (g) six programs through the J-8 pipeline (`toy1 add dec mul fib ack`). The script reads
the `lake` command from `LAKE` and builds missing executables. Demo verdicts come from native executable runs and are
not kernel-checked.

## Review and audit

This is a large and complex development. Its theorems are machine-checked, but a machine-checked proof is only as strong as
its statements and its trusted base (the Lean kernel and compiler, the C toolchain and file I/O, and for `nockvm-e2e-verify-fam`
also the input parser; see `docs/LIMITS.md`). Because of its size and complexity, we welcome review, issues and pull requests from the community, and
we are commissioning an independent audit. This release is for research and review; we will complete that audit before any
production deployment.

License: Apache-2.0 (`LICENSE`).
