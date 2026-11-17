# NockVM specification: J-8, J-9 B, J-9 A, J-9 AL and the end-to-end package (REL-5.4)

A `<sub>Sources (generated)</sub>` line closes most subsections; it is produced by `docs/gen/cite_sections.py`
and checked by `docs/gen/check_citations.py`.

This document specifies what release REL-5.4 proves and what it runs. Every normative statement names a Lean declaration
and its `file:line` in this tree; the line numbers are those of the release commit and the generated index
`docs/THEOREMS.md` re-derives them.

**Status: alpha research release**, not independently audited; it must not be used in production. Review, issues and the
independent audit: `README.md`, section Review and audit.

## 0. Conventions

**Labels.** Each claim carries one label.

| label | meaning |
|---|---|
| [kernel] | a Lean theorem checked by the Lean 4 kernel. Where a `#print axioms` line is recorded for it (every headline in `docs/THEOREMS.md` but one definition; the cited declarations not listed in `docs/theorems-unrecorded.tsv`), that line is a subset of `propext`, `Classical.choice`, `Quot.sound`; for the others no axioms line is claimed (§11.2) |
| [executed] | the result of running a compiled executable of this tree; it is evidence, not a kernel fact |
| [trusted] | assumed: not checked by the kernel or at run time (e.g. the Lean compiler, the C toolchain, the random-oracle model) |
| [inferred] | this document's reading of a statement; check against the cited source |

**Citations.** Paths are relative to the repository root. `nockvm-e2e/…` is the end-to-end package; everything else is the
library. The library namespace `Nock.NockVMROM.Thm54.VclL.Handle` is an opaque prefix and is abbreviated `Handle`;
module names `Nock.RedTeam.BatchNNNN…` carry a sequence number only. The release labels (J-8, J-9 B, J-9 A, J-9 AL,
`j9alj`) are mapped to descriptive names in `docs/GLOSSARY.md`.

**The target predicate.** "The claim `c` holds" is `Nock.Jet.HoldsN c` (`Nock/Jet/Semantics.lean:41`):
`∃ fuel, evalN fuel c.subject c.formula = some c.result`, with `evalN` the reference interpreter over natural-number
atoms (`Nock/Reference.lean:75`). A second declaration with the short name `HoldsN` exists at `Nock/Atoms/HoldsN.lean:33`;
the headlines of §4–§6 and §9 use `Nock.Jet.HoldsN` [inferred from the statements].

**Release labels.** J-8, J-9 B, J-9 A and J-9 AL are four revisions of one arithmetization of full Nock; they carry no other
meaning. J-9 B is J-8 with claim atoms of any size; J-9 A adds op-0 / op-10 axes of up to 62 limbs (§5); J-9 AL adds
primitive jets checked by an ALU chip (§6). `j9alj` in `nockvm-e2e/` is J-9 AL with template jets from the fixed catalogue
`catJ`, not a fifth revision; the executables' `--family` flag selects one of `j8`, `j9a`, `j9al`, `j9alj`. In identifiers a
bare `J9` means J-9 B in `V1J9`, `checkJ9`, `AcceptsJ9V`, `nockvm-j9dump`, and J-9 A or J-9 AL in `axisChipJ9`, `aluChipJ9`,
`PrimJ9.lean`. In prose this document writes J-9 AL; `j9al` appears only in code font.

**Reading order.** §1–§4 specify J-8 with J-9 B folded in (§3.6, §4.1.3, §4.3.2); §5 (J-9 A) and §6 (J-9 AL) are deltas;
§7 is a J-8 result (trace uniqueness); §8–§10 are the end-to-end package.

**Names and paths.** `Handle.` abbreviates `Nock.NockVMROM.Thm54.VclL.Handle.` and `Jet.` abbreviates `Nock.Jet.`. The
prefixes `Nock.NockVMROM.Thm54`, `VclL` (the memory design: a table of validated cells keyed by content and round-0 serial,
linked to the other tables by LogUp) and `Handle` (the compute chip refers to memory cells by handle, the cell's round-0
serial) are opaque names. Chip suffixes such as `HQ`, `HQK`, `HQKW`, `HX`, `VCLHX` are revision labels;
the chips in force are those §3.3 names. Namespaces `Nock.RedTeam.BatchNNNN` live in modules
`Nock.RedTeam.BatchNNNN<Suffix>`; the number is only a sequence index, and several headline theorems live there.
`File.lean::decl` cites a declaration in a file; `BatchNNNN::decl` cites one in a namespace.

**Notation.** `p` is the Goldilocks prime; `K` (written `𝕂` in column descriptions) is the cubic extension and
`𝕂′ = K(√δ)`. A `𝕂` value takes 3 base-field columns and a `𝕂′` value 6, so a chip's width is its base columns plus
3·(number of `𝕂` roles). Probabilities are written `2^-155`. Chip letters: in traces `C` is compute, `M` cell table, `W`
cell walk, `J` J chip, `A` atom table, `V` atom walk, `X` axis, `S` split, `L` ALU; `rowsTpl_le` (§6.11) uses another
lettering, spelled out there. A statement marked **(informal)** is an explanation, not something a theorem states. Where a
column or gate description and the Lean definition differ, the definition holds.

## 1. The machine

### 1.1 Nouns and the reference interpreter
A noun is an atom (`ℕ`) or a cell of two nouns (`Nock.Noun`). The semantics is `Nock.evalN : ℕ → Noun → Noun → Option
Noun` (`Nock/Reference.lean`): `evalN fuel subject formula`, fuel-indexed, `none` = crash or out of fuel.

`a` is the subject.

| formula | result |
|---|---|
| `[[b c] d]` (autocons) | `[*[a [b c]] *[a d]]` |
| `[0 ax]` | `/[ax a]` (`Noun.slot`; axis 0 crashes) |
| `[1 b]` | `b` |
| `[2 b c]` | `*[*[a b] *[a c]]` |
| `[3 b]` | `0` if `*[a b]` is a cell, `1` if an atom |
| `[4 b]` | `*[a b] + 1` (unbounded; crash on a cell) |
| `[5 b c]` | `0` if `*[a b] = *[a c]`, else `1` |
| `[6 b c d]` | `*[a c]` if `*[a b] = 0`, `*[a d]` if `= 1`, else crash |
| `[7 b c]` | `*[*[a b] c]` |
| `[8 b c]` | `*[[*[a b] a] c]` |
| `[9 ax c]` | with `core = *[a c]`: `*[core /[ax core]]` |
| `[10 [ax c] d]` | `#[ax *[a c] *[a d]]` (`Noun.edit`) |
| `[11 [b clue] body]` | evaluate `clue` (crash if it crashes), then `*[a body]` |
| `[11 b body]`, `b` an atom | `*[a body]` |
| the formula is an atom | crash |
| head atom outside 0–11 | crash |

This is Nock 4K: op 10 is edit and op 11 is hint. Atoms are natural numbers: op 4 never wraps.

<sub>Sources (generated): `Noun` Nock/Tree.lean:20; `evalN` Nock/Reference.lean:75; `slot` Nock/Reference.lean:42; `edit` Nock/Reference.lean:57</sub>

### 1.2 Claims and the target predicate
A claim is `P8PublicClaim = ⟨subject, formula, result⟩` (`Nock.NockVMROM.Thm54.P8PublicClaim`; the `P8` prefix is opaque). The target is

`Jet.HoldsN c := ∃ fuel, evalN fuel c.subject c.formula = some c.result`.

Every soundness theorem in §4.1 bounds the probability that the verifier accepts while `HoldsN c` fails.

<sub>Sources (generated): `P8PublicClaim` Nock/NockVMROM/Thm54/JointSoundness.lean:48; `HoldsN` Nock/Jet/Semantics.lean:41</sub>

### 1.3 Jets
- `Jet.Template = (k, ax, sem)`: arity, argument axes in the subject, a semantic function
  `(Fin k → Noun) → Option Noun`. `Template.rel T s r` iff the axes exist in `s` and `sem` of the arguments is `r`.
- `Jet.JetSpec = (T, c)`: a template and the Nock formula it stands for. `Jet.Registry := ℕ → Option JetSpec`.
- `Jet.Faithful T c := ∀ s r, T.rel s r → ∃ fuel, evalN fuel s c = some r`;
  `Jet.Complete T c := ∀ s fuel r, evalN fuel s c = some r → T.rel s r`;
  `JetSpec.Faithful j := Faithful j.T j.c ∧ Complete j.T j.c`;
  `Registry.Faithful R := ∀ n j, R n = some j → j.Faithful`.
- A jet call is the hint `[11 [n clue] c]` with `n` an atom id (`Jet.jetCall`). By `Jet.evalN_hint_jet` its value is
  the value of `c` once the clue evaluates; `Jet.rowJ_holdsN` turns a registered entry's relation into `HoldsN`.
- `Jet.VerifiedRegistry = (R, faithful : R.Faithful)`. Constructors: `VerifiedRegistry.empty`;
  `VerifiedRegistry.ofCompiled p hp Rt regs hwt` (id `n ∈ regs` ↦ `((Rt n).toTemplate p, compile p (Rt n))`, proof
  from `compile_jetSpec_faithful`); `VerifiedRegistry.add V n j hj` (requires `hj : j.Faithful`).

<sub>Sources (generated): `Template` Nock/Jet/Semantics.lean:48; `rel` Nock/Jet/Semantics.lean:63; `JetSpec` Nock/Jet/Semantics.lean:96; `Registry` Nock/Jet/Semantics.lean:101; `Faithful` Nock/Jet/Semantics.lean:106; `Complete` Nock/Jet/Semantics.lean:110; `jetCall` Nock/Jet/Semantics.lean:134; `evalN_hint_jet` Nock/Jet/Semantics.lean:137; `rowJ_holdsN` Nock/Jet/Semantics.lean:219; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `VerifiedRegistry` Nock/Jet/VerifiedRegistry.lean:22; `empty` Nock/Jet/VerifiedRegistry.lean:29; `ofCompiled` Nock/Jet/VerifiedRegistry.lean:35; `compile_jetSpec_faithful` Nock/Jet/Autogen.lean:870; `add` Nock/Jet/VerifiedRegistry.lean:48</sub>

### 1.4 The template language (`Nock/Jet/Autogen.lean`)
- Types `Ty`: `F` (a field atom `< p`), `L n τ` (a null-terminated list of exactly `n` elements of type `τ`) or `N` (an opaque
  noun: any noun; see §1.4.1).
- Expressions `Ex k`: `var i`, `const c`, `add`, `mul`, `nth j`, `pair`; loop-free and first-order.
- `ev p a e`: evaluation; `add`/`mul` reduce mod `p`.
- `Tpl = (k, ax, inTy, outTy, body)`; `Tpl.WellTyped p T := HasTy p T.inTy T.body T.outTy`.
- `Tpl.toTemplate p T`: same arity and axes; `sem a = some (ev p a T.body)` when every argument passes `shapeOK p`,
  else `none`.
- `compile p T = [8 [1 LIB] [6 GUARD BODY [0 0]]]`: the Nock formula of `T` (a pure function of `p` and `T`).
- `compile_jetSpec_faithful hp T hT : (⟨T.toTemplate p, compile p T⟩ : JetSpec).Faithful` for `0 < p` and well-typed
  `T`; `compile_rel_iff_holdsN`: `(T.toTemplate p).rel s r ↔ HoldsN ⟨s, compile p T, r⟩`.
- `Jet.ChipJ8.axPosB T`: every `var` axis of `T` is `≥ 1` (a public check on the registry).

<sub>Sources (generated): `Tpl` Nock/Jet/Autogen.lean:107; `WellTyped` Nock/Jet/Autogen.lean:115; `toTemplate` Nock/Jet/Autogen.lean:118; `sem` Nock/Jet/Autogen.lean:124; `shapeOK` Nock/Jet/Autogen.lean:75; `compile` Nock/Jet/Autogen.lean:202; `compile_jetSpec_faithful` Nock/Jet/Autogen.lean:870; `compile_rel_iff_holdsN` Nock/Jet/Autogen.lean:876; `axPosB` Nock/Jet/ChipJ8.lean:414</sub>

#### 1.4.1 The opaque-noun type `N`
`Autogen.lean::Ty.N` types an argument or a result that the template only passes through. Facts, each by definition or theorem
in this tree:
- `shapeOK p .N v = true` for every noun `v` (`Autogen.lean::shapeOK`; namespace `Batch4890`, `shapeOK_N`): an `N` slot may hold an atom
  `≥ p` or a cell of any shape, while an `F` slot requires an atom `< p`.
- Typing: `HasTy.weakN` turns a typing of an expression at any type into one at `N`. No other rule consumes an `N`: `add` and
  `mul` need `F`, `nth` needs `L n τ`. An `N` value is read by `var`, built into lists by `pair`, and returned.
- Compilation: the guard at `N` is `gTy p .N f = [6 [3 f] [1 0] [1 0]]` (`Batch4890::gTy_N`). It evaluates the slot, so the
  compiled formula crashes when the slot is missing (needed by `compile_complete`), and it always returns `0` when the slot
  exists. The guards at `F` and `L` and the compiled `matmul` template are unchanged (`Batch4890::gTy_F_unchanged`,
  `gTy_L_unchanged`, `matmul2_compile_unchanged`).
- `Autogen.lean::compile_faithful`, `compile_complete`, `compile_jetSpec_faithful` and `compile_crash_exact` hold for every
  well-typed `Tpl`, including templates with `N` in `inTy` or `outTy`. `Interp.lean::interp_sound` and `interp_complete` do
  likewise; the interpreter emits no guard rows for an `N` argument (`Interp.lean::gNodes`, `gRows`: `.N ↦ []`).
- The driver serialises types with `DriverJ8.lean::encTy`: `F ↦ [0]`, `L n τ ↦ 1 :: n :: encTy τ`, `N ↦ [2]`.
- Effect on the theorems: the binders of `complJ8_closed`, `complJ9B_closed`, `complJ9A_closed` and `complJ9A_closed_of` (§4.3, §5.4)
  and of the soundness theorems (§4.1, §5.3) do not mention `N`; what widens is the set of programs they apply to: a run may call a
  jet whose template passes nouns of any size or shape through an `N` slot. Smallness lemmas that were stated for every argument
  (`ComplJ8OfBalG.lean::shape_small`, `look_small`: a value of a shape-checked type has only atoms `< p`) are false at `N`;
  they are restated for templates with no `N` in an input type (`ComplJ8OfBalG.lean::NFree`), and the new
  `ComplJ8OfBalG.lean::ev_small` shows that a well-typed expression over arguments with atoms `< p` has value with atoms `< p`
  (`Batch4891` prints the axioms of these).
- For the same reason three published lemmas of `Batch4872` gain a hypothesis that no input type of the template (resp. of every called template) contains `N`
  (`hN`, via `NFree`): `blockWG_agree`, `jrowsH_eq_of_sib`, `jrowsH_eq_old`.
- Non-vacuity: `Batch4892::complJ9A_closed_of_N` is `complJ9A_closed_of` at the template `TN` (`x : F` at axis 2, `d : N` at axis
  3, body `[x·x d]`, output `L 2 N`), registered as jet id `7`, run on the subject `[3 (p+5)]` (so `d = p+5 ≥ p`); every
  binder is discharged, and `Batch4892::complJ9A_N_figure` gives `ε_c < 2^-120` and an accepting coin.
  `Batch4893::good_coin_N` gives a good coin, and `Batch4893::numerics_N` gives an accepting coin together with every numeric
  binder of `probJ9A_final_clean` at that run. The negative control is the same template with `d : F`: `Batch4892::TF_sem_none`
  and `TF_crashes` (the compiled formula crashes at every fuel on that subject).

<sub>Sources (generated): `N` Nock/NockVMROM/Thm54/P8Core/OptimizedFailureEventEv.lean:81; `shapeOK` Nock/Jet/Autogen.lean:75; `shapeOK_N` Nock/RedTeam/Batch4890Thm54T0Lang.lean:37; `gTy` Nock/Jet/Autogen.lean:189; `compile_complete` Nock/Jet/Autogen.lean:835; `gTy_L_unchanged` Nock/RedTeam/Batch4890Thm54T0Lang.lean:30; `matmul2_compile_unchanged` Nock/RedTeam/Batch4890Thm54T0Lang.lean:35; `compile_faithful` Nock/Jet/Autogen.lean:825; `compile_jetSpec_faithful` Nock/Jet/Autogen.lean:870; `compile_crash_exact` Nock/Jet/Autogen.lean:856; `Tpl` Nock/Jet/Autogen.lean:107; `interp_sound` Nock/Jet/Interp.lean:429; `interp_complete` Nock/Jet/Interp.lean:777; `gNodes` Nock/Jet/Interp.lean:159; `gRows` Nock/Jet/Interp.lean:475; `encTy` Nock/DriverJ8/DriverJ8.lean:44; `complJ8_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean:202; `complJ9B_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean:141; `complJ9A_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AClosed.lean:166; `complJ9A_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean:53; `shape_small` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean:565; `look_small` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean:678; `NFree` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean:560; `ev_small` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean:575; `blockWG_agree` Nock/RedTeam/Batch4872Thm54JSibRetire.lean:108; `jrowsH_eq_of_sib` Nock/RedTeam/Batch4872Thm54JSibRetire.lean:146; `jrowsH_eq_old` Nock/RedTeam/Batch4872Thm54JSibRetire.lean:176; `probJ9A_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProbJ9A.lean:548; `TF_crashes` Nock/RedTeam/Batch4892Thm54T0Demo.lean:359</sub>

### 1.5 Execution trees (`Nock/Edit/GenX.lean`, `Nock/Edit/SemanticsX.lean`)
The honest prover runs the generator `genX R fuel s f : Option (NTree SkelX × Noun)`. One node per evaluation step
in one of the 17 states of `StateX`: `s0 … s9`, `cons`, `s10` (edit), `s10L` (edit chain level), `s10T` (edit chain
terminal), `s11s` (static hint), `s11d` (dynamic hint), `s11j` (jet hint). A jet hint is a dynamic hint
`[11 [%wild clue] body]` whose tag is the atom `%wild` (`wildTag`, `Nock/Jet/Wild.lean`) and whose clue evaluates to an atom
`id`, the jet key. When `id` is registered with formula `c = body` and the template relation holds, the hint is an `s11j`
node with one child (the clue); the body is not expanded. Any other tag is an ordinary hint. The canonical spelling is
`wildCall id body = [11 [%wild [1 id]] body]`.
- `genX_sound (hR : R.Faithful)`: `genX R n s f = some (t, r) → HoldsN ⟨s, f, r⟩`.
- `genX_complete (hR : R.Faithful)`: `evalN n s f = some r → ∃ t, genX R n s f = some (t, r)`.
- `edit_of_slots`: if `old` and `e` agree on every off-path sibling along axis `a` (`ChainOK a old e`) and
  `slot a e = some new`, then `edit a new old = some e`. The edit chain rows `s10L`/`s10T` certify exactly this.

<sub>Sources (generated): `genX` Nock/Edit/GenX.lean:188; `StateX` Nock/Edit/SemanticsX.lean:41; `genX_sound` Nock/Edit/GenX.lean:221; `genX_complete` Nock/Edit/GenX.lean:314; `evalN` Nock/Reference.lean:75; `edit_of_slots` Nock/Edit/SemanticsX.lean:269; `ChainOK` Nock/Edit/SemanticsX.lean:193</sub>

## 2. Field, atoms, encodings

### 2.1 Fields
- `Nock.Field.p = 2^64 − 2^32 + 1`; `Nock.Field.goldilocks_prime : Nat.Prime p`. `Nock.Atoms.p` is the same number.
- Statements are parametric in a field `K ⊇ ZMod p` with a basis `b : Basis (Fin 3) (ZMod p) K` (so `[K : 𝔽_p] = 3`),
  a non-square `δ ∈ 𝔽_p` that stays a non-square in `K`, and `𝕂′ := Quad (algebraMap (ZMod p) K δ)`, i.e.
  `K(√δ)`, `|𝕂′| = |K|²`. The soundness theorems take `hpG : p = Nock.Atoms.p` and
  `hcK : Fintype.card K = cK` with `Nock.NockVMROM.Thm54.VclL.Events.cK = Fintype.card Nock.Field.K`,
  `cK_eq : cK = p^3` (`Nock.Field.K = GaloisField p 3`).
- Executable instance (`Nock/TraceGenExe`): `KC = 𝔽_p[X]/(X^3 − 7)` (`cubicPoly`, `cubic_irreducible`),
  `deltaF = 7`, `KQ = KC(√7)`, `powerBasis3 : Basis (Fin 3) (ZMod p) KC`; `KC_card` and `cK_eq` give `|KC| = cK`.
- A `𝕂` value in a trace occupies 3 base-field columns (coordinates in `b`); a `𝕂′` value occupies 6 (Re, Im).

<sub>Sources (generated): `p` Nock/Field.lean:33; `goldilocks_prime` Nock/Field.lean:38; `cK` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHJRun.lean:48; `cK_eq` Nock/NockVMROM/Thm54/VclL/Events/Bound.lean:134; `K` Nock/Field.lean:53; `cubicPoly` Nock/TraceGenExe/K3.lean:102, nockvm-e2e/NockvmE2E/Exec/Field.lean:405 (several); `cubic_irreducible` Nock/TraceGenExe/K3.lean:104, nockvm-e2e/NockvmE2E/Exec/Field.lean:407 (several); `deltaF` Nock/TraceGenExe/K6.lean:21; `powerBasis3` Nock/TraceGenExe/PowerBasis.lean:18; `KC_card` Nock/TraceGenExe/K3.lean:130, nockvm-e2e/NockvmE2E/Exec/Field.lean:433 (several)</sub>

### 2.2 Small and big atoms (`Nock/Atoms/Limbs.lean`)
An atom `n` is small iff `n < p`, big iff `n ≥ p`. A big atom is represented by its canonical little-endian limb
list in base `B = 2^32` (`limbs n = Nat.digits B n`; every limb `< B`, top limb `≠ 0`).
`limbs_p : limbs p = [1, B − 1]`; `big_iff`: for canonical `l`, `p ≤ val l ↔ len ≥ 3 ∨ (len = 2 ∧ l₁ = B − 1 ∧ l₀ ≥ 1)`.
`lenL n` is `1` for small `n` and `(limbs n).length` for big `n`.

<sub>Sources (generated): `limbs` Nock/Atoms/Limbs.lean:48; `limbs_p` Nock/Atoms/Limbs.lean:83; `big_iff` Nock/Atoms/Limbs.lean:127; `lenL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:683, Nock/Atoms/Fingerprint.lean:105 (several)</sub>

### 2.3 Noun fingerprints
A fingerprint is `FP K = (size, dyck, leaf)` (`Nock.ComputeTable.FP`):
`atomFP z v = ⟨z, 0, v⟩`; `cons z a b = ⟨a.size·b.size, z·a.dyck + a.size²·z⁻¹ + a.size²·b.dyck, a.leaf + a.size·b.leaf⟩`.
The J-8 encoder is `Handle.EncZYJ8.encZY z y`: `atom n ↦ atomFP z (leafVal y n)`, `cell a b ↦ cons z (E a) (E b)`,
where `leafVal y n` is `n` for small `n` and the limb polynomial `Σ lᵢ yⁱ` of `limbs n` for big `n`. The structure
coin `z` and the limb coin `y` are independent coins of `𝕂′` (`Handle.encJ8`). With one coin for both, there are
distinct nouns that collide at every coin (`Nock.Atoms.sameCoin_collision`).

<sub>Sources (generated): `FP` Nock/ComputeTable.lean:52; `atomFP` Nock/ComputeTable.lean:72; `encZY` Nock/NockVMROM/Thm54/VclL/Handle/EncZYJ8.lean:46; `leafVal` Nock/Atoms/Fingerprint.lean:196; `encJ8` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8.lean:413; `sameCoin_collision` Nock/Atoms/Fingerprint.lean:322</sub>

### 2.4 Handles and kinds
A noun occurrence is referenced by a handle `(k, v)`: kind `k = 0` a small atom with value `v`; `k = 1` a cell at
cell-table row `v`; `k = 2` a big atom at atom-table row `v`. On the wire the kind of a cell-table child is
`w + kb ∈ {0, 1, 2}` (§3.3.2).

## 3. The J-8 arithmetization

This section specifies J-8; J-9 B differs only in its predicate (§3.6). J-9 A and J-9 AL are deltas (§5, §6).

### 3.1 Constraint-system model

- `Nock.Framework.RAP F`: columns `w`, rounds `k` with per-round widths, row domain `H`, generator `ω`, constraint
  polynomials `C_i` of degree `≤ d` over shifted symbolic variables `Y_{i,j} ↦ P_i(ω^j X)`.
  `RAP.Satisfies R P := ∀ i, ∀ x ∈ R.H, (R.compose P i).eval x = 0`.
- `FixedPreprocessingRAP`: a RAP plus verifier-fixed columns; `BindsPreprocessing P` = those columns of `P` equal the
  fixed polynomials; `RAP.SatisfiesWithPreprocessing R P = R.rap.Satisfies P ∧ R.BindsPreprocessing P`.
- Every chip is `MonolithicRAP.expandChip` of a `ChipTemplate`: base-field gates, mixed gates over `𝕂`/`𝕂′` coins,
  each gate of total degree `≤ 4`; a `𝕂′` equation becomes 2 `𝕂` equations, each 3 base-field equations.
- Rows sit on `nodes : Fin n → ZMod p` with `nodes (i+1) = nodes i · ω` for a `StrictOrbitDomain (ZMod p) 3 h`;
  `isFirst`/`isLast` are verifier-fixed masks.
- A trace is `Handle.TraceJ8.TrJ8 F`: six groups of column polynomials, `C : Fin 123`, `M : Fin 242`,
  `W : Fin 166`, `J : Fin 71`, `A : Fin 349`, `V : Fin 166`.
- Rounds: round 0 columns are committed before any coin; round-1 columns may depend on coins sampled after round 0;
  round-2 columns on coins sampled after round 1 (`crC crM crW crJ crA`). `StJ8 Q` states that the prover's map
  `Q : Coins frameJ8 K → TrJ8` (`frameJ8` is defined in §3.2) is staged: every column depends only on coins sampled before its round
  (`StagedCols`).
- LogUp (multiset) arguments: a record `r = (r₀, …, r_{m−1})` is compressed to `ρ + Σ γ^j r_j ∈ 𝕂′`
  (`FiniteIO.compress`). A provider row holds an inverse column with gate `inv·den − 1 = 0` and adds `m·inv` to an
  accumulator (`m` its multiplicity); a consumer adds `inv` (or `w·inv`, `w` a weight). Accumulator gates: initial
  value on `isFirst`, step between adjacent rows, terminal equal to a public on `isLast`. A balance holds when the
  verifier's equation between terminals (§3.5) holds.

<sub>Sources (generated): `RAP` Nock/Framework/Core.lean:100; `Satisfies` Nock/NockVMROM/Thm54/StagedTableRAP.lean:579, Nock/Framework/Core.lean:150 (several); `FixedPreprocessingRAP` Nock/Framework/FixedPreprocessingRAP.lean:46; `BindsPreprocessing` Nock/Framework/FixedPreprocessingRAP.lean:78; `SatisfiesWithPreprocessing` Nock/Framework/FixedPreprocessingRAP.lean:87; `expandChip` Nock/NockVMROM/Thm54/CoordinateRAPCore.lean:420; `ChipTemplate` Nock/NockVMROM/Thm54/CoordinateRAPCore.lean:210; `StrictOrbitDomain` Nock/NockVMROM/Thm54/ExtensionField.lean:79; `isFirst` Nock/Jet/ChipJ8.lean:55; `isLast` Nock/Jet/ChipJ8.lean:56; `TrJ8` Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean:51; `crC` Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean:60; `StJ8` Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean:71; `frameJ8` Nock/NockVMROM/Thm54/VclL/Handle/FrameJ8.lean:29; `StagedCols` Nock/NockVMROM/Thm54/P8Core/SVFrame/MemSoundnessFamily.lean:77, nockvm-e2e/NockvmE2E/Rap/Frame.lean:31 (several); `compress` Nock/NockVMROM/Thm54/FiniteFieldIO.lean:65</sub>

### 3.2 Coins `frameJ8`

`Handle.FrameJ8.frameJ8`: 19 coins of `K`.

| index | name | sampled after round | use |
|---|---|---|---|
| 0, 1 | `αC`, `γ` | 1 | memory-walk coins (informal) |
| 2, 3 | `z = χ₂ + χ₃√δ` | 0 | structure fingerprint coin |
| 4–7 | `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ` | 1 | validity class balances |
| 8, 9, 10 | `a, b, c` | 0 | base-frame coins |
| 11, 12, 15, 16 | `γH′ = χ₁₁ + χ₁₅√δ`, `ρH′ = χ₁₂ + χ₁₆√δ` | 0 | handle class balances (export, path, service, J in-chip) |
| 13, 14 | `αW`, `γW` | 0 | compute-walk coins (informal) |
| 17, 18 | `y = χ₁₇ + χ₁₈√δ` | 0 | limb coin |

Challenge vectors per chip: `chalVJ8` (compute), `chalsMJ8` (cell table and J-8 walk), `chalsAJ8Z` (atom table and
atom walk: `y` in place of `z` at leaves 2, 3, and `z` at leaves 37, 38), `chalsJJ8` (J chip: handle coins only).

<sub>Sources (generated): `frameJ8` Nock/NockVMROM/Thm54/VclL/Handle/FrameJ8.lean:29; `chalVJ8` Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean:55; `chalsMJ8` Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean:58; `chalsAJ8Z` Nock/NockVMROM/Thm54/VclL/Handle/ChalsAZJ8.lean:32; `chalsJJ8` Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean:62</sub>

### 3.3 Chips

Widths are kernel facts (`rfl`). Width = base columns + 3·(`𝕂` roles).

| chip | Lean | width | theorem |
|---|---|---:|---|
| compute | `Handle.ChipHX.computeChipVCLHX` | 123 | `widthHX_val`, `computeChipVCLHX_width` |
| cell table | `Handle.CellTwinKW.cellChipHQKW` | 242 | `cellChipHQKW_width` |
| cell walk | `Handle.WalkJ8.walkChipJ8` | 166 | `walkChipJ8_width` |
| J chip | `Jet.ChipJ8.jetChipJ8` (template `jetTemplateJ8T`) | 71 | `jetChipJ8_width`, `jetTemplateJ8T_width` |
| atom table | `Handle.AtomChipHQ.atomChipHQ`, and `Handle.AtomChipHQL.atomChipHQL` on the same trace | 349 | `atomChipHQ_width`, `atomChipHQL_width` |
| atom walk | `Handle.CellTwinK.walkChipHQK` over the atom table | 166 | `walkChipHQK_width` |

<sub>Sources (generated): `computeChipVCLHX` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:1271; `widthHX_val` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:136; `computeChipVCLHX_width` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:1291; `cellChipHQKW` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean:79; `cellChipHQKW_width` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean:100; `walkChipJ8` Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean:147; `walkChipJ8_width` Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean:167; `jetChipJ8` Nock/Jet/ChipJ8T.lean:132; `jetTemplateJ8T` Nock/Jet/ChipJ8T.lean:84; `jetChipJ8_width` Nock/Jet/ChipJ8T.lean:147; `jetTemplateJ8T_width` Nock/Jet/ChipJ8T.lean:103; `atomChipHQ` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:247; `atomChipHQL` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:109; `atomChipHQ_width` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:269; `atomChipHQL_width` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:131; `walkChipHQK` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:386; `walkChipHQK_width` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:406</sub>

#### 3.3.1 Compute chip `computeChipVCLHX`
123 columns = 69 round-0 + 54 coin-dependent. One row per execution-tree node.

| cols | content |
|---|---|
| 0–16 | one-hot `StateX` selector: `s0…s9`, `cons` (10), `s10` 11, `s10L` 12, `s10T` 13, `s11s` 14, `s11d` 15, `s11j` 16 |
| 17, 18 | `isFirst`, `isLast` (fixed) |
| 19–24 | `z1`, `v`, `β`, `v2`, `w`, `pr` (scalar witnesses) |
| 25–48 | 12 handles `(k, v)`: `s f e sf1 sf2 f_h f_t f_th f_tt f_tth f_ttt m` (`k` is the wire kind) |
| 49–60 | `kb` per handle; `kc := k − 2·kb` |
| 61, 62 | `fast`, `inv4` (op 4) |
| 63–68 | second-pair witnesses `ax2`, `pr2`, `l₁ = (k, v)`, `l₂ = (k, v)` (op 5 on two big atoms) |
| 69–92 | four slot inverses over `𝕂′`: `inv0 inv1 inv2 inv3` |
| 93–110 | three accumulators over `𝕂′`: export, path, service |
| 111–122 | in-chip forest walk over the execution tree: `ln, count, acc, walk_inv` (`𝕂`) |

Gates (all degree `≤ 4`: `gatesHX_degree`):
- Kind split per handle: `kb² = kb`, `kc² = kc`, `kc·kb = 0`. A value read as small uses the selector `1 − k + kb`.
- Structural gates per state (the head opcode, the shape of the formula handles); kid-kind gates
  `st·(1 − kc(h)) = 0` on every real-child formula handle (`kidKindG`; `kid_cell`).
- op 4: `s4·kc(sf1) = 0`, `s4·kc(e) = 0`, `s4·(v2 − v − 1) = 0`; fast path `s4·fast·(v2·inv4 − 1) = 0` with
  `sf1.kb = e.kb = 0` (`op4_fast_row`: small in, small out, `e = sf1 + 1`); slow path `s4·(1−fast)·(1−sf1.kb)·v2 = 0`,
  `s4·(1−fast)·(1 − e.kb) = 0` (`op4_slow_row`: the output is big, a small input is `p − 1`) and the row consumes an
  increment record `(sf1.k, sf1.v, e.k, e.v, 4)` from the service balance.
- op 5: `=` is handle equality over `(k, v)`; `≠` is `neGateX`: `s5·β·((Δkc)² + (Δkb)² + (v − v2)·w − 1) = 0` on the
  first-difference leaves; `prGateX` selects the path-read pair; when both first-difference leaves are big,
  `pr2 = s5·β·kb(f_tth)·kb(f_ttt)` selects a second pair read from the atom walk, with `pr2·l₁.k·l₂.k = 0`
  (`op5_pair_row`).
- op 10: `s10` reads axis `a < p` (small), handles axis 1 by `z1`, and reads `slot a e = new` through the path
  balance; `s10L` rows (atom formula `a_k ≠ 1`, `a_k = 2v + β`, sibling axis `ax2 = a_k + 1 − 2β`) check sibling
  agreement between `old` and `e`; `s10T` is the terminal (formula `1`).
- op 11: `s11s` (static, atom tag), `s11d` (dynamic: clue and body children), `s11j` (jet: tag value `%wild`, one child,
  the clue, whose value `sf1` is a small atom, the id); an `s11j` row consumes the jet record `(id, h_c, h_S, h_E, 3)` with
  `id = sf1.v` from the service balance (`ChipHX.s11j_wild`; the tag is the atom `%wild` when `wildTag < p`,
  `WildTagX.s11j_tag`).
- Slots (state-disjoint entries, `slotsX_disjoint`): `slot0` decodes `f` (export record of the formula handle);
  `slot1` decodes `f_t` on states `s2`, `s5`–`s9`, `s10`, `s11s`, `s11d`, `s11j`, the op-0 read, and the op-4 slow increment consume;
  `slot2` holds five decode/read entries of the base layout, the `f_th` decode on states `s10`, `s11d`, `s11j`, and the
  path-read pair under `pr` on states `s5`, `s10L`; `inv3` holds the `s10` read, the
  `s11j` jet consume and the op-5 second pair under `pr2`.
- Service keys are pairwise distinct polynomials in `γ` for all handle values (`serviceKeys_disjoint`): every service
  key has 8 entries with its tag last (`3` jet, `4` increment, `0` for atom-walk records, padded).
- Publics: claim handles `0–5`, export terminal `15/21`, path terminal `18/24`, service terminal `27/30` (Re/Im).

<sub>Sources (generated): `computeChipVCLHX` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:1271; `StateX` Nock/Edit/SemanticsX.lean:41; `isFirst` Nock/Jet/ChipJ8.lean:55; `isLast` Nock/Jet/ChipJ8.lean:56; `inv0` Nock/NockVMROM/Thm54/VclL/Handle/ChipH.lean:84, Nock/Jet/ChipJ8.lean:76, nockvm-e2e/NockvmE2E/Exec/PubExe.lean:40 (several); `gatesHX_degree` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:664; `kidKindG` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:284; `kid_cell` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:976; `op4_fast_row` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:999; `op4_slow_row` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:1027; `neGateX` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:225; `prGateX` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:231; `op5_pair_row` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:1048; `slotsX_disjoint` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:768; `slot0` Nock/NockVMROM/Thm54/VclL/Handle/ChipH.lean:286, Nock/NockVMROM/Thm54/P8Core/Batch1171Thm54C2InductionPositional.lean:240, Nock/RedTeam/Batch1141Thm54C2InductionCertAxes0.lean:232, Nock/RedTeam/Batch1110Thm54C2CombinedInduction.lean:234 (several); `slot1` Nock/NockVMROM/Thm54/VclL/Handle/ChipH.lean:289; `slot2` Nock/NockVMROM/Thm54/VclL/Handle/ChipH.lean:296, Nock/RedTeam/Batch1060Thm54RepairIIMemoryReadSet.lean:117 (several); `inv3` Nock/NockVMROM/Thm54/VclL/Handle/SplitChipJ9.lean:67, Nock/Jet/ChipJ8.lean:79 (several); `serviceKeys_disjoint` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:853</sub>

#### 3.3.2 Cell table `cellChipHQKW`
242 columns = 134 base + 3·36 (`𝕂` roles). One row per distinct cell (hash-consed). Base columns (`ChipRAP.Cell`): `isF isL idx idL idR wL wR aL aR lo hi
loL hiL loR hiR carry mv mx` and 110 rank bits; `mx1` (128); `mh` (129); `kbL kbR invL invR` (130–133).
`𝕂′` roles: fingerprints `p, l, r` of the row and its children, validity / export / handle-export inverses and
accumulators.
- Serial: `isFirst·idx = 0`, `(1 − isLast)(idx′ − idx − 1) = 0`.
- Rank (`lo + 2^62·hi` limbs, bit-certified): `lo + 2^62·carry = loL + loR + 1`, `hi = hiL + hiR + carry`; a weight-0
  (inline atom) child has rank `(0, 0)`. Every accepted row has rank `≥ 1` (`cellRow_rank_pos`).
- Fingerprint: `p = cons z l r`; an inline child (`w = 0`) has `l = atomFP z a`.
- Big-atom routing per side (`sideGates`): `kb(1−kb)`, `kb·lo`, `kb·hi`, `w(1−kb)((lo+hi)·inv − 1)`, `kb(1−w)`;
  so `kb = 1 ⇔ (w = 1 ∧ lo = hi = 0)` (`sideGates_kind`): a big-atom child is a weighted child of rank `(0, 0)`.
- Records. Provides `vKeyP = (fp p, lo + hi√δ, idx)` (validity, `γ′ρ′`, multiplicity `mv`); consumes
  `vKeyL`, `vKeyR` (weighted by `wL`, `wR`); provides the export records `xKeyS = (fp p, fp l, fp r, idx, s)` for
  `s ∈ {0, 1}` (multiplicities `mx`, `mx1`) to the cell walk; provides the handle export record
  `keyHK = (idx, kL, vL, kR, vR)` with kinds `w + kb` (multiplicity `mh`, `γH′ρH′`).
- No cell row provides a rank-`(0,0)` key (`no_cell_provides_rank0`), so a big-atom child is served by the atom
  table (§3.3.5). `exportHKW_genuine`: a provided export key is the record of a decoded row, at all three kinds.

<sub>Sources (generated): `cellChipHQKW` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean:79, Nock/NockVMROM/Thm54/VclL/Handle/HonestKW.lean:72 (several); `Cell` Nock/MemoryTable.lean:74; `isF` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:147, Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:264, Nock/NockVMROM/Thm54/VclL/Chips/WalkChip.lean:49 (several); `mx1` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:168, Nock/V1J8/Example.lean:77 (several); `kbL` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:121; `cellRow_rank_pos` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:36; `sideGates` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:126; `sideGates_kind` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:248; `vKeyP` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:198; `vKeyL` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:200; `vKeyR` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:201; `xKeyS` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:209; `keyHK` Nock/NockVMROM/Thm54/VclL/Handle/TwoProviderQ.lean:346; `no_cell_provides_rank0` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:48; `exportHKW_genuine` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean:327</sub>

#### 3.3.3 Cell walk `walkChipJ8`
166 columns. A forest walk over the cell table (`Nock/NockVMROM/Thm54/VclL/Chips/WalkChip.lean` columns `isF isL rM idx pre ridx len cL cR e mL mR q qinv
u bit0…`). Each row consumes one export record `(p, l, r, idx, 0)` and provides two path records
`(root, l, 2·prefix, rootIdx)`, `(root, r, 2·prefix + 1, rootIdx)` with multiplicities `mL`, `mR`; in-gate walk with
coins `αW, γW`; BFS queue counter; root gate on the first `kroots` rows. Kinds are ternary: `k(k−1)(k−2) = 0`
(`ternE`). Depth certificate `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60 = 0` on every row, so `len ≤ 60`
(`depthCert60_range`, `walkJ8_len_le_60`); outside the walk event every provided record axis lies in
`[2, 2^62)` (`walkHQK_axis_lt`). These are the fingerprint-layer records; the export side is linked
to the cell table by `hfxC`. On the handle layer (`γH′ρH′`) each row consumes the handle export record of its node
and provides handle path records `(root.v, axis, ch.k, ch.v)` for its children, which the compute chip consumes
through the path balance (informal summary of `walkTemplateHQ`).

<sub>Sources (generated): `walkChipJ8` Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean:147; `isF` Nock/NockVMROM/Thm54/VclL/Chips/WalkChip.lean:49; `kroots` nockvm-e2e/NockvmE2E/Emit/Chips.lean:31; `ternE` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:332; `len` Nock/NockVMROM/Thm54/VclL/Chips/WalkChip.lean:55; `depthCert60_range` Nock/NockVMROM/Thm54/VclL/Handle/HalvingJ8.lean:81; `walkJ8_len_le_60` Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean:608; `walkHQK_axis_lt` Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean:647; `walkTemplateHQ` Nock/NockVMROM/Thm54/VclL/Handle/MemHQ.lean:184</sub>

#### 3.3.4 J chip `jetChipJ8`
71 columns = 29 base + 3·14 (`𝕂` roles). A straight-line interpreter over `Tpl.ev`: one block of rows per unique call `(id, h_S, h_E)`.
- Row kinds (`Jet.ChipJ8.Kd`): `reg`, `call`, `cst`, `add`, `mul`, `rp`, `sl`, `sr`, `cp`, `isf`, `nil`.
- Columns: selectors 0–10, masks 11–12, `id cid nid n1 n2` 13–17 (verifier-fixed, interpolated from the public layout
  `lay : Fin n → PRow`, `jetPre`), `m mv val v1 v2` 18–22, handles `kN vN kL vL kR vR` 23–28; `𝕂′` roles: four tagged
  slot inverses, the export-read inverse, one tagged accumulator, one export accumulator.
- Gates: `val = n1` (`cst`), `val = v1 + v2` (`add`), `val = v1·v2` (`mul`) on field values; `rp` binds
  `h_N = [h_L h_R]` by one export read; `sl`/`sr` move a read cursor to the left/right child; `cp` ends a read chain;
  `isf`/`nil` are shape guards.
- In-chip keys (8 entries, tag last, `tagLast`): node value `(cid, nid, k, v, 0, 0, 0, 1)`, registry
  `(id, k, v, 0, 0, 0, 0, 2)`. Service provide (to compute): `keyJet = (id, h_c.k, h_c.v, h_S.k, h_S.v, h_E.k, h_E.v, 3)`.
  Export reads consume `(h_N.v, h_L.k, h_L.v, h_R.k, h_R.v)` from the cell export balance.
- `jetChip_sound` / `jetChip_holds`: an accepted block with genuine export records and a bound registry entry gives
  `HoldsN ⟨s, compile p T, e⟩` for the call's subject and output handles.
- The chip may be absent: `JGenJ8.JChipOK` is "satisfied, bound, injective nodes, `0 < nJ`, adjacent nodes" or
  "`nJ = 0` and `pubsJ 0..3 = 0`".

<sub>Sources (generated): `jetChipJ8` Nock/Jet/ChipJ8T.lean:132; `ev` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Bad.lean:57, Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:829, Nock/NockVMROM/Thm54/VclL/Chips/QEval.lean:30, Nock/NockVMROM/Thm54/VclL/Chips/QEval.lean:34 … (several); `Kd` Nock/Jet/ChipJ8.lean:45; `jetPre` Nock/Jet/ChipJ8T.lean:126; `tagLast` Nock/Jet/ChipJ8T.lean:48; `keyJet` Nock/Jet/ChipJ8.lean:148; `jetChip_sound` Nock/Jet/ChipJ8.lean:838; `jetChip_holds` Nock/Jet/ChipJ8.lean:903; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `JChipOK` Nock/NockVMROM/Thm54/VclL/Handle/JGenJ8.lean:53</sub>

#### 3.3.5 Atom table `atomChipHQ`
349 columns = 205 base + 3·48 (`𝕂` roles). A restriction twin of the cell table at the limb coin `y`: every cell-table gate holds verbatim (at challenge vector
`chalsAJ8Z`), so the cell table's lemmas apply to its restriction (`atomChipHQ_restrict_sat`,
`atomChipHQ_restrict_cell_sat`). One row per right-comb node of a big atom's limb list: `aL` is this node's limb
(left child inline, `wL = 0`); the right child is the next node (`wR = 1`, `idR`) or the top limb (`wR = 0`, `aR`).
Added columns: limb bits `130–193`, `invT` 194, `invB` 195, `mb` 196, `inc` 197, `conv` 198, `cout` 199,
old-node copy `idxO lO kRO vRO` 200–203, `mi` 204; `𝕂′` roles `mbInv mbAcc cInv miInv miAcc cAcc`.
Gates (`atomGates`, `atomQ`):
- g1: `aL = Σ 2^i bᵢ`, `aR = Σ 2^i b_{32+i}`, 64 booleanities (limbs `< B`). g2: `wL = 0`. g3: `(1−wR)(aR·invT − 1) = 0`
  (top limb `≠ 0`).
- Boundary (`bnd`, for `mb` and for `mi`): an exported two-limb row has `aR = B − 1` and `aL ≠ 0` (value `≥ p`).
- g7.0: booleanity of `inc conv cout kRO`; `(1−inc)·cout = 0`; `inc·conv = 0`; `mi·(1 − inc − conv) = 0`.
- g7.1: `inc·(aL − lO − 1 + B·cout) = 0`. g7.2 (no carry): new tail = old tail. g7.3′ (carry into a suffix row):
  `idR = idx + 1`, next row's `idxO = vRO`, `wR = 1`, next row is an increment row. g7.4 (carry out of the top limb):
  `aR = t + 1`, or `t = B − 1` and the adjacent row is the two-limb row `(0, 1)`. g8 (conversion): the row is
  `p = [1, B − 1]`.
- `atomChipHQL` adds `isL·cout = 0` (`gL`): the last row carries no carry-out (`cout_last`);
  `atomChipHQL_sat_iff` relates the two chips on one trace.
- Records. g5 provides `mbKey = (⟨z, 0, leaf_y⟩, 0 + 0√δ, idx)` into the CELL validity balance (multiplicity `mb`):
  this serves a cell's big-atom child and a big claim atom. It consumes the old node's export record
  `(idxO, 0, lO, kRO, vRO)` (atom export balance, accumulator `cAcc`, terminal `pubC = 10/11`). It provides the
  increment record `incKey = (2·(1−conv), (1−conv)·idxO − conv, 2, idx, 4)` (old handle `(2, idxO)`, or `(0, p − 1)` on a
  conversion row; new handle `(2, idx)`) into the service balance (multiplicity `mi`, terminal `pubMI = 8/9`). It
  provides its own export records (`keyH`) to the atom walk and to its increment rows.
- `inc_chain_sound`: an increment row whose old node is genuine denotes the `+1` of the old limb list
  (`Nock.Atoms.carry_val`: `val new = val old + 1`).
- The conversion row's constants are those of `p = Nock.Atoms.p`; this is one reason the theorems take `hpG`
  (informal).

<sub>Sources (generated): `atomChipHQ` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:247; `chalsAJ8Z` Nock/NockVMROM/Thm54/VclL/Handle/ChalsAZJ8.lean:32; `atomChipHQ_restrict_sat` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:303; `atomChipHQ_restrict_cell_sat` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:319; `idR` Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean:151; `invT` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:102, Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:50 (several); `invB` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:51; `idxO` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:56; `mbInv` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:63; `atomGates` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:146; `atomQ` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:166; `atomChipHQL` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:109; `cout_last` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:273, Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Atom.lean:824 (several); `atomChipHQL_sat_iff` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:180; `mbKey` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:149; `cAcc` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:69, nockvm-e2e/NockvmE2E/J8/TieJ8.lean:1107 (several); `pubC` Nock/NockVMROM/Thm54/StandaloneVerifierData.lean:162, Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:75, Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean:2374, nockvm-e2e/NockvmE2E/Exec/PubExe.lean:162 (several); `incKey` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:159; `pubMI` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:72, nockvm-e2e/NockvmE2E/Exec/PubExe.lean:160 (several); `keyH` Nock/NockVMROM/Thm54/VclL/Handle/ProvideH.lean:273, Nock/NockVMROM/Thm54/VclL/Handle/TU/CellOrderP1.lean:1134 (several); `inc_chain_sound` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:494; `carry_val` Nock/Atoms/Carry.lean:35</sub>

#### 3.3.6 Atom walk `walkChipHQK`
166 columns, over the atom table. The walk template at the atom table's balances and labels at `y`; it provides `walkRecA = (rootIdx, 2·prefix + b,
k_b, v_b)` records (`k_b = 0` an inline limb, `1` a suffix row) to the service balance for op 5 on two big atoms, and
consumes the atom table's export records. It may be absent (`AcceptsJ8V.AWChipOK`): present = the seven conjuncts
(satisfied, bound, injective nodes, adjacent nodes, `1 ≤ krootsV ≤ nV`, `krootsV + nV < p`); absent = `krootsV = 0` and
the six atom-walk publics it would contribute are `0`.

<sub>Sources (generated): `walkChipHQK` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean:386; `walkRecA` Nock/NockVMROM/Thm54/VclL/Handle/AtomWalkAW.lean:107; `AWChipOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:101</sub>

### 3.4 Public data and messages

`Handle.AcceptsJ8.PubJ8 p` (fixed before any coin): for each chip the orbit height, row count (`n nC nW nJ nA nV`,
all positive except `nJ`), nodes and orbit; `kroots`, `krootsV`; the J layout `lay`; the template table
`Rt : ℕ → Tpl`; the registered ids `regs`, the call ids `ids`, and per registered id the cell-table row `idx id` and rank
`rk id` of its compiled formula.

`Handle.AcceptsJ8P.MsgJ8' p K δ` (the prover's public messages): the claim message `m` (cell-table rows of the claim's
cell nouns), compute terminals `ρ : Fin 5 → 𝕂′` and `ρS : 𝕂′`, and the publics `pubsC pubsW pubsJ pubsA pubsV`. It holds
no lists: every request list is computed by the verifier or read from committed traces.

Verifier-computed lists:
- `claimRecsJ8 χ c m`: per cell claim noun `x`, `claimVec (encJ8 χ x) (m k) rk(x)` (rank limbs `rkC`).
- `pinRecsJ8 Pb χ`: per registered id, the same record for `compile p (Rt id)` at row `idx id`, rank `rk id`.
- `pinCons regs idx` (`Jet.PinJ8`): per registered id one consume of the J chip's registry key.
- `censusG Pb c`: the registered formulas and the claim's cell nouns.

<sub>Sources (generated): `PubJ8` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8.lean:94; `kroots` nockvm-e2e/NockvmE2E/Emit/Chips.lean:31; `MsgJ8'` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:246; `pubsC` Nock/NockVMROM/Thm54/VclL/Chips/MemFamilyVCL.lean:414; `claimRecsJ8` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:262; `claimVec` Nock/NockVMROM/Thm54/VclL/Handle/ClaimVS.lean:46, nockvm-e2e/NockvmE2E/Exec/PubExe.lean:90 (several); `rkC` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:257; `pinRecsJ8` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:266; `compile` Nock/Jet/Autogen.lean:202; `pinCons` Nock/Jet/PinJ8.lean:68; `censusG` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:271</sub>

### 3.5 The verifier predicate `AcceptsJ8V`

`Handle.AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g`.

A structure; every field is a check. Grouped:

**Chips.** `hsatX` (compute satisfied with preprocessing, at `chalVJ8 χ` and compute publics `pubVJ8 c M.m M.ρ M.ρS χ`);
`hsatC hbindC` (cell); `hsatW hbindW`, `hkW : 1 ≤ kroots`, `hknW : kroots ≤ nW`, `hkpW : kroots + nW < p` (cell walk);
`hJk : JChipOK …` (J chip present or absent); `hsatA hbindA` and `hsatL hbindL` (atom table under both `atomChipHQ`
and `atomChipHQL`); `hVk : AWChipOK …` (atom walk present or absent); for every chip, injective nodes and
`nodes (i+1) = nodes i · ω` (`hinj*`, `hadj*`); `hnpC : nC < p`, `hnpA : nA < p`.

**Balance equations** (`𝕂′`):
- `hGx` (handle export): `ρ 3 + T_W^export + T_J^export = T_C^handle-export`.
- `hGp` (path): `ρ 4 = T_W^path`.
- `hGS` (service): `ρS + Σ_{pinCons} 1/compress(r) + T_J = T_A^inc + T_V^path`.
- `hsumC'` (cell validity): `Σ_{claimRecsJ8 ++ pinRecsJ8} 1/compress_{γ′ρ′}(r) = T_C^validity + T_A^g5`.
- `hbalA'` (atom export): `T_A^export = T_A^old-consume + T_V^export`.
- `hvalA0`: the atom table's internal validity terminal is `0`.
- `hfxC`, `hfxA`: fingerprint-export links cell ↔ cell walk and atom table ↔ atom walk.

**Registry and J layout.** `hlay : List.ofFn lay = layoutJ8 Rt regs ids`; `hsmall` (layout numbers `< p`);
`huniq` (node-value keys distinct); `hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, compile p (Rt i)⟩ ∧
axPosB (Rt i) ∧ (Rt i).WellTyped p`; `hnd : regs.Nodup`; `hidx`, `hrk : rk id ≠ (0, 0)`, `hlt` (range checks).

**Claim.** `hclA`: every claim atom is `< p`; `hclI`: claim cell rows `< p`; `hclR`: claim cell ranks
`internal / 2^62 < p`; `hcellF : isCellN c.formula`; `hcen : ∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ every leaf < p`.

**Lengths and budgets.** `hlenC : 3 + |regs| + 2·nC < p`; `hlenA : nA + nV < p`; `hnA62 : nA ≤ 2^62`;
`hbud : RealIOJ8.BudJ8 Pb r (g + r.N)` and `hbudV` (record counts of each balance bounded by the row budgets `r`, `g`).

<sub>Sources (generated): `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143; `chalVJ8` Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean:55; `pubVJ8` Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean:111; `hkW` nockvm-e2e/NockvmE2E/Exec/E2EJ8ToyD.lean:55; `atomChipHQ` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:247; `atomChipHQL` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:109; `internal` Nock/Tree.lean:45</sub>

### 3.6 The J-9 B predicate `AcceptsJ9V`

`Handle.AcceptsJ9V.AcceptsJ9V`.
`AcceptsJ8V` with: the compute publics at `ClaimJ9.pubVJ9` (a big claim atom `n ≥ p` has handle `(2, idx)`);
`hsumC'` over `claimRecsJ9` (adds one record per big claim atom); `hclA` removed; `hclI` extended to big-atom
positions; `hcen'` over `censusGJ9` with `lenL v ≤ nA + 2` in place of `v < p`. Claims may contain atoms `≥ p`.

<sub>Sources (generated): `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143; `pubVJ9` Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean:197; `claimRecsJ9` Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean:286; `censusGJ9` Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean:297; `lenL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:683, Nock/Atoms/Fingerprint.lean:105 (several)</sub>

### 3.7 Transcript and executable checker

#### 3.7.1 Fiat–Shamir (`Nock.DriverJ8.TranscriptJ8`)
Sponge: Tip5 (`Nock.Driver.Tip5`). State `s` (5 limbs). `absorb label data`:
`s ↦ hashVarlen([tAbs] ++ s ++ bytes7 label ++ [|data|] ++ data)`; `squeeze idx`: read coins `idx` from `s`
(`coinsOf`, three limbs per coin), then `s ↦ hashVarlen([tSqz] ++ s ++ [|idx|] ++ idx)`. Initial state
`hashVarlen [tIni]`. Schedule `sched pub claim c0 c1 c2 mm`:

1. absorb the domain tag `"nockvm/j8/fs/v1"`, every field of the public record, every claim field;
2. absorb `commit/r0`, squeeze `idxS0 = [2, 3, 8, …, 18]` (the coins sampled after round 0);
3. absorb `commit/r1`, squeeze `idxS1 = [0, 1, 4, 5, 6, 7]`;
4. absorb `commit/r2`, absorb `msg`.

`pub_before_first_squeeze`: everything before the first squeeze is an absorb, and it contains the header, every
public field and every claim field. The random-oracle behaviour of `Tip5.hashVarlen` is an assumption; no theorem
states it.

<sub>Sources (generated): `coinsOf` Nock/NockVMROM/Thm54/VclL/Handle/TeleC.lean:427, Nock/Driver/Transcript.lean:124, nockvm-e2e/NockvmE2E/Exec/SoundPub.lean:648 (several); `hashVarlen` Nock/Driver/Tip5.lean:164, nockvm-e2e/NockvmE2E/Exec/Tip5Core.lean:153, nockvm-e2e/NockvmE2E/Exec/Tip5.lean:156 (several); `idxS0` Nock/DriverJ8/TranscriptJ8.lean:34; `idxS1` Nock/DriverJ8/TranscriptJ8.lean:36; `pub_before_first_squeeze` Nock/DriverJ8/TranscriptJ8.lean:85</sub>

#### 3.7.2 Checker (`Nock.V1J8`)
`checkJ8 : InJ8 → Bool` = `validB ∧ checkStaticJ8 ∧ checkPubJ8E ∧ chipsB` (the seven chip checks), computable (field
arithmetic in an executable model of `KC`, read back by `toχ`). `InJ8` holds the claim, the message, the coins, the budgets `r g`, the registry data and per chip the orbit
height, row count, generator and rows. `checkFast` is the evaluation-optimized form; `checkFast_eq : checkFast I = checkJ8 I`.

`checkJ8_iff (hreg : RegOK I Rg)` (stated under the section instances `[Algebra Nock.Atoms.Fp KQ]`,
`[Fact (ringChar (ZMod p)).Prime]` and `[Algebra (ZMod (ringChar (ZMod p))) KC]`; all are satisfied at `KC`/`KQ`):
`checkJ8 I = true ↔ ∃ hv : ValidJ8 I, AcceptsJ8V deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g`,
where `mkTr I` interpolates the rows and `RegOK I Rg` says every registered id maps to its compiled, well-typed
template. The J-9 B checker is `Nock.V1J9.Check9.checkJ9` with `checkJ9_iff`.

<sub>Sources (generated): `checkJ8` Nock/V1J8/CheckJ8.lean:391; `validB` Nock/V1J8/CheckJ8.lean:290; `InJ8` Nock/V1J8/CheckJ8.lean:241; `checkFast` Nock/V1J8/FastCheck.lean:56; `checkFast_eq` Nock/V1J8/FastCheck.lean:66; `checkJ8_iff` Nock/V1J8/CheckJ8.lean:490; `mkTr` Nock/V1J8/CheckJ8.lean:362; `RegOK` Nock/V1J8/CheckJ8.lean:403; `checkJ9` Nock/V1J9/CheckJ9.lean:87; `checkJ9_iff` Nock/V1J9/CheckJ9.lean:177</sub>

### 3.8 Worked example: the `add` fixture

The fixture `nockvm-e2e/fixtures/j9al-add/` is one J-9 AL run carried through every layer; its files are listed with hashes
in `SHA256SUMS` there.

- **Claim.** Subject `[(p+5) (p+7)]`, formula `[11 [%wild [1 7]] (primC add)]` (a jet hint with id `7` whose body is the formula of
  the primitive `add`, §6.1), result `2p + 12`, fuel 2 (`nockvm-e2e/NockvmE2E/Exec/J9ALConv.lean:58`). Both operands are big
  atoms (`≥ p`), so the run uses the atom table and the ALU. The same run is the library's non-vacuity witness
  `complJ9AL_toy` (`Batch4921`) and executable link `genLink_toy` (`Batch4936`) (§6.9) [kernel].
- **Registry.** The primitive table is `[(7, add)]`: id `7` registered at `primSpec add` (§6.5); no template jets.
- **Tables.** The instance `add.inst.json` names five chip documents, in order: the J-9 A twin compute chip
  (`computeChipVCLHX9`), the cell table (`cellChipHQKW`), the cell walk (`walkChipJ8`), the atom table (`atomChipHQL`) and the
  ALU (`aluChipJ9`). The axis, split, J and atom-walk chips are absent (§5.1, §6.4, §3.3.6). Each chip document is checked
  against the verifier's Lean literal for that table (`chipsOkF`, `docs/LIMITS.md` row 7) [executed].
- **Public input.** The claim's cell nouns (`claimCells`) and the primitive table; `zBind` requires the Fiat–Shamir statement
  of the proof to start with their encoding (§9.3).
- **Proof parameters** (fields of `add.inst.json`, kernel facts in §9.5): `l = 170` queries, `k = 6`, evaluation domain `2^nD`
  with `nD = 13`, `1219` columns in total.
- **Channels (informal).** The jet call is checked by the ALU, not the J chip (§6.1): the compute row of the `s11j` node consumes the jet
  key from the service balance, the ALU's `hdr` row provides it and consumes the registry key `pinRgP` and operation record
  `pinOpP` that the verifier pins (§6.3); the ALU reads the two operands and writes the result through the cell-validity and
  export balances, as limb lists in the atom table (§3.3.5); the identity `a + b = c` is checked at the limb coin `y` (§6.2).
- **Run.** `../nockvm-e2e/README.md`, section Running the fixtures: `vk-setup`, `fix-prove`, then `verify --family j9al --vk`
  prints `ACCEPT claim …`, a covered accept (§10.1) [executed]. The certified verifier gives the same verdict on the same
  files.

## 4. J-8 and J-9 B theorems

### 4.1 Soundness

#### 4.1.1 `Handle.CleanJ8.probJ8V_final_clean`
For every `Pb : PubJ8 p`, registry `Rg` with `hRg : Rg.Faithful`, claim `c`, staged prover map
`Q : Coins frameJ8 K → TrJ8 (ZMod p)` with `hQ : StJ8 Q`, budgets `r : RowsJ8`, `g : ℕ`:

  `|{χ : (∃ M, AcceptsJ8V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ HoldsN c}| / |Coins frameJ8 K| < 2^-155`.

Hypotheses (besides the field/algebra instances of §2.1, `[CharP K p] [CharP 𝕂′ p]` and an instance
`[Algebra Nock.Atoms.Fp 𝕂′]`; `hqM` is written with `ringChar (ZMod p)`, which is `p`):

| binder | meaning |
|---|---|
| `hRg : Rg.Faithful` | every registered jet is faithful and complete against `evalN` |
| `hQ : StJ8 Q` | the prover's columns are staged by round |
| `hpG : p = Nock.Atoms.p` | Goldilocks |
| `hcK : Fintype.card K = cK` | `|K| = p^3` |
| `hr : RowsLe r EncInjJ8.cornerC` | budgets at most the corner (below) and `r.Λ = fuelChip` |
| `hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen` | every atom `< p` has limb length at most `r.maxlen` |
| `hk : 2·fuelChip ≤ r.leaves` | the leaf budget is at least `2·fuelChip` |
| `hmax : Pb.nA + 2 ≤ r.maxlen` | the limb-length budget covers the atom table plus 2 |
| `hg : g ≤ 2^31` | registered ids budget |
| `hLC hLM hLW hLA hLV` | `n ≤ r.N`, `nC ≤ r.D`, `nW ≤ r.W`, `nA ≤ r.A`, `nV ≤ r.AW` |
| `hnM : Pb.nC ≤ 2^31` | the cell table has at most `2^31` rows |
| `hreg : (censusG Pb c).length ≤ 2^31` | the census (registered formulas and the claim's cell nouns) has at most `2^31` entries |

`fuelChip = 2^110`. `cornerC = { corner31 with leaves := 2·fuelChip }`, where `corner31` has `N D W A AW J mb inc
calls heads blocks rd maxlen = 2^31` and `Λ = leaves = fuelChip` (`Handle.WeightsJ8.corner31`). The claim `c`, `Pb`,
`Rg`, `r`, `g` are fixed before the coins; the message `M` may depend on all coins.

The theorem covers both atom-walk layouts: `LinkJ8A.probJ8V_final` is the case split of `AcceptsJ8V.probJ8V_present`
(`1 ≤ krootsV`) and `LinkJ8A.probJ8V_absent` (`krootsV = 0`); `probJ8V_final_clean` removes the derived instances
`[Fact (ringChar (ZMod p)).Prime]` and `[Algebra (ZMod (ringChar (ZMod p))) K]`.

<sub>Sources (generated): `probJ8V_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8.lean:49; `evalN` Nock/Reference.lean:75; `fuelChip` Nock/NockVMROM/Thm54/P8Core/VclL/Table.lean:150; `cornerC` Nock/NockVMROM/Thm54/VclL/Handle/EncInjJ8.lean:452; `corner31` Nock/NockVMROM/Thm54/VclL/Handle/WeightsJ8.lean:701; `probJ8V_final` Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8A.lean:866; `probJ8V_present` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:447; `probJ8V_absent` Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8A.lean:839</sub>

#### 4.1.2 `Handle.CleanJ8V.probJ8V_verified`
The same statement at `Rg := V.R` for `V : Jet.VerifiedRegistry`; no `hRg` binder.

<sub>Sources (generated): `probJ8V_verified` Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8V.lean:54</sub>

#### 4.1.3 `Handle.LinkJ9G.probJ9B_final_clean` (big atoms in the claim)
The same statement with `AcceptsJ9V` in place of `AcceptsJ8V`, the same binders, and `hreg9 : (censusG Pb c).length
+ 6 ≤ 2^31` in place of `hreg`.

<sub>Sources (generated): `probJ9B_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/LinkJ9G.lean:848; `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143</sub>

#### 4.1.4 Structure of the proof (informal)
`ProbJ8.prob_le_of_outside`: if acceptance at a coin outside every bad event of a summand list implies `HoldsN c`,
then the bad fraction is at most `epsilonOf` of the list. The implication is `LinkJ8A.hsoundJ8XUA`: outside the events,
every balance is a multiset equality of genuine records; the cell and atom tables decode to nouns
(`exportHKW_genuine`, `inc_chain_sound`); the walks give genuine path reads; the J chip gives `HoldsN` of each jet call
(`jetChip_holds`); each compute row is a correct step (`LocalVSX.local_stepX`, `edit_of_slots`); and the execution
tree's root is the claim.

<sub>Sources (generated): `prob_le_of_outside` Nock/NockVMROM/Thm54/VclL/Handle/ProbJ8.lean:41; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `epsilonOf` Nock/NockVMROM/Thm54/P8Core/SVFrame/MemSoundnessFamily.lean:437, nockvm-e2e/NockvmE2E/Rap/Frame.lean:60 (several); `hsoundJ8XUA` Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8A.lean:584; `exportHKW_genuine` Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean:327; `inc_chain_sound` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean:494; `jetChip_holds` Nock/Jet/ChipJ8.lean:903; `local_stepX` Nock/NockVMROM/Thm54/VclL/Handle/LocalVSX.lean:287; `edit_of_slots` Nock/Edit/SemanticsX.lean:269</sub>

### 4.2 Error figures

#### 4.2.1 The soundness bound
The summand list is `AtomFpxJ8.allJ8X`; its `ε` is `boundJ8X |K| |𝕂′| r P g` (`epsilon_allJ8X`), and (below, `c` stands for `|K|`; `P` is the census parameter of the record `DataJ8X`, at most `2^66` in the figure [inferred])
`boundJ8X c (c²) r P g = numJ8X c r P g / c⁴` (`boundJ8X_eq`) with

```
numJ8X c r P g = numJ8Pin c r P g + IO(11, AW, 2A)
numJ8Pin c r P g =
    numHQ c N D W Λ
  + IO(5, 3 + 2D + g, D + mb)          -- cell validity, two providers (cell rows, atom g5)
  + IO(5, 3 + 2A, A)                   -- atom-table internal validity
  + IO(5, A + inc + AW, A)             -- atom-table export
  + IO(5, 3N + W + rd, D)              -- cell export, three consumers (compute, cell walk, J reads)
  + IO(8, N + 2J + g, calls + heads + blocks + J)   -- service balance with the J in-chip balances
  + c²·(A·(2·fuelChip − 1) + pairCount(A + 3)·(2Λ − 1) + 1)   -- atom-table census and Dyck events at y
  + c³·(15·AW)                         -- atom-walk event
  + P·(c²·(leaves − 1) + c²·(maxlen − 1))   -- bivariate census in (z, y)
numHQ c N D W Λ = c³·(8N + 2 + 15W) + c²·(D·(2·fuelChip − 1) + 1 + pairCount(D + 3)·(2Λ − 1))
  + IO(5, 3N + W, D) + IO(5, 2N, 2W) + IO(5, 3 + 2D, D) + IO(11, W, 2D)
IO(m, k₁, k₂) = ioFailureUnionBound m k₁ k₂ (c²) = (k₁ + k₂)²·(m − 1)·c² + c²·2·(k₁ + k₂)
```
(`m` is the record length; `k₁`, `k₂` the consumer and provider budgets.) In the final theorem the list is
instantiated at `g′ = g + r.N`, which prices the service summand at `2N + 2J + g` consumers
(`RepriceJ8.service_budget_reprice`).

| figure | theorem | value |
|---|---|---|
| `boundJ8X cK (cK²) r P g < 2^-155` for `RowsLe r cornerC`, `P ≤ 2^66`, `g′ ≤ 2^32` where `g′ = g + r.N` (§4.2.1) | `RepriceJ8.figJ8X_155_census32` (kernel `decide` in `numJ8X_census32`) | 155 bits |
| not `≤ 2^-156` at the corner | `RepriceJ8.figJ8X_not_156_32` | tight |
| `Pr[accept ∧ ¬ HoldsN] < 2^-155` | `RepriceJ8.probJ8X_lt_155_census32`, used by `probJ8V_final_clean`, `probJ8V_verified`, `probJ9B_final_clean` | 155 bits |

<sub>Sources (generated): `allJ8X` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:94; `boundJ8X` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:100; `epsilon_allJ8X` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:109; `DataJ8X` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:59; `boundJ8X_eq` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:119; `numJ8X` Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean:116</sub>

#### 4.2.2 Completeness figure
`ε_c < 2^-120` at `|K| = cK`, stated inside `complJ8_closed` and `complJ9B_closed` (§4.3).

<sub>Sources (generated): `complJ8_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean:202; `complJ9B_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean:141</sub>

### 4.3 Completeness

#### 4.3.1 `Handle.ComplJ8Closed.complJ8_closed`
For a verified registry `Rg`, a template table `Rt`, and a generated run `hgen : genX Rg.R fuel s f = some (t, r)`,
let `B := BRunA δ b Rt hgen hpG h31` (the honest record: public data `B.Pb`, messages `B.M χ`, traces `B.tr χ`, budgets
`B.rows`, `B.g`, the good-coin predicate `B.Good`, and `B.epsC`). Then

1. `∀ χ, B.Good χ → AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g`;
2. `|{χ : ¬ B.Good χ}| / |Coins frameJ8 K| ≤ B.epsC`;
3. `StJ8 B.tr`;
4. `HoldsN (cJ s f r)`;
5. `Fintype.card K = cK → B.epsC < 2^-120 ∧ ∃ χ, AcceptsJ8V … χ (B.M χ) (B.tr χ) B.rows B.g`.

Both completeness theorems additionally take the derived instances `[Fact (ringChar (ZMod p)).Prime]` and
`[Algebra (ZMod (ringChar (ZMod p))) K]` (satisfied at any `K` by `ringChar (ZMod p) = p`); no "clean" variant is provided.

Hypotheses:

| binder | meaning |
|---|---|
| `hpG : p = Nock.Atoms.p` | Goldilocks |
| `hax : ProgAxOK p t` | on every row: op-0 and op-9 axes, op-10 edit axes, jet tags and jet ids (clue values) are `< p`; an `s10L` level `a` has `a + 1 < p` |
| `hop5 : ProgOp5OK p t` | on every op-5 row, the axis of the first difference of the compared nouns is `< p` |
| `hclA` | every leaf atom of the claim's subject, formula and result is `< p` |
| `hleaf : RootsLeafOK roots` | every walked root has `≤ 2^109` leaves |
| `hwalk`, `hwalkA : WalkDepthOK …` | every path read (cell reads, atom reads) has depth `≤ 61` |
| `hRt` | every called jet id is registered as `⟨(Rt id).toTemplate p, compile p (Rt id)⟩`, with `axPosB` and `WellTyped` |
| `hregAx` | every axis of a called template is `< p` |
| `h31 : Rows31 …` | every table has `≤ 2^31` rows |

<sub>Sources (generated): `complJ8_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean:202; `M` Nock/NockVMROM/Thm54/P8Core/OptimizedFailureEventEv.lean:84, Nock/RedTeam/Batch1382Thm54MemoryMaskCensus.lean:12 (several); `tr` Nock/NockVMROM/Thm54/VclL/Handle/ChipHX.lean:909; `rows` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAxisRows.lean:495, Nock/NockVMROM/Thm54/P8Core/OptimizedComputeHostileAccumulator.lean:55, Nock/NockVMROM/Thm54/P8Core/OptimizedMemoryHostileAccumulator.lean:64 (several); `g` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalJ.lean:665; `Good` Nock/NockVMROM/Thm54/Unhosted309Canonical.lean:1330, Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean:166, Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean:128, Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AObl.lean:120 … (several); `epsC` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean:169, Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean:131, Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AObl.lean:123 (several); `StJ8` Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean:71; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `axPosB` Nock/Jet/ChipJ8.lean:414; `WellTyped` Nock/Jet/Autogen.lean:115</sub>

#### 4.3.2 `Handle.ComplJ9BClosed.complJ9B_closed`
The same conclusion with `AcceptsJ9V` and the honest record `BRun9`; hypotheses: those of `complJ8_closed` without
`hclA` (claim atoms may be big).

<sub>Sources (generated): `complJ9B_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean:141; `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `BRun9` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BOf.lean:183; `complJ8_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean:202</sub>

### 4.4 Non-vacuity

Each witness is a kernel-checked instance at `K = KC`, `δ = deltaF`, `b = powerBasis3`, Goldilocks.

| theorem | instance | content |
|---|---|---|
| `Nock.RedTeam.Batch4777.nvJet_final_const` | `Ijet`: registry `[7 ↦ tinyT]` (`tinyT x y = x + y` on field atoms), subject `[0 [[5 7] 0]]`, program `[11 [%wild [1 7]] compile tinyT]` | `AcceptsJ8V` holds at the instance's coins at `r = cornerC`, and `probJ8V_final_clean`'s conclusion holds at the constant trace map |
| `Nock.RedTeam.Batch4776.nvJet_hyps_final_clean` | `Ijet` | the same for any staged `Q` (instances `CharP` taken as arguments) |
| `Nock.RedTeam.Batch4779.eq5_final_const` | `Ine`: `*[p−1 [5 [4 [0 1]] [4 [4 [0 1]]]]]` (op 5 on big atoms `p`, `p+1`) | `AcceptsJ8V` with `0 < krootsV` (atom walk present), and the conclusion of `probJ8V_final_clean` |
| `Nock.RedTeam.Batch4812.probJ9B_nonvacuous_demo` | `c9 = *[[(p+5) 0] [0 2]] = p+5` | `AcceptsJ9V` at `cornerC`, `HoldsN c9`, `claimBigs p c9 = [2]`, every numeric binder of `probJ9B_final_clean` |
| `Nock.RedTeam.Batch4842.complJ8_closed_toy`, `complJ8_closed_toy_figure` | `*[[0 0] [0 1]] = [0 0]`, empty registry | `complJ8_closed` with every binder discharged; `ε_c < 2^-120` and an accepting coin |
| `Nock.RedTeam.Batch4856.complJ9B_toy`, `complJ9B_toy_figure` | `*[(p+5) [0 1]] = p+5`, empty registry | `complJ9B_closed` with every binder discharged (`hclA` fails here: `hclA_fails`); `ε_c < 2^-120` and an accepting coin |

Also: `Handle.CleanJ8.probJ8V_nonvacuous_clean` (an accepting instance of `AcceptsJ8V` with a true claim, J chip and
atom walk absent); `Nock.RedTeam.Batch4775.acceptsJ8V_mono_rows` (a larger budget keeps `AcceptsJ8V`).

<sub>Sources (generated): `nvJet_final_const` Nock/RedTeam/Batch4777Thm54NVJetConst.lean:39; `Ijet` Nock/RedTeam/Batch4771Thm54NVJetData.lean:68; `tinyT` Nock/RedTeam/Batch4771Thm54NVJetData.lean:21, TraceDemo/D5RedMain.lean:450, TraceDemo/J8Dump.lean:53 (several); `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143; `probJ8V_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8.lean:49; `nvJet_hyps_final_clean` Nock/RedTeam/Batch4776Thm54NVJetClean.lean:55; `eq5_final_const` Nock/RedTeam/Batch4779Thm54NVEq5Regime.lean:78; `Ine` Nock/RedTeam/Batch4778Thm54NVEq5.lean:57; `probJ9B_nonvacuous_demo` Nock/RedTeam/Batch4812Thm54J9bNVFinal.lean:150; `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `cornerC` Nock/NockVMROM/Thm54/VclL/Handle/EncInjJ8.lean:452; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `claimBigs` Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean:145; `probJ9B_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/LinkJ9G.lean:848; `complJ8_closed_toy` Nock/RedTeam/Batch4842Thm54J8ComplClose.lean:134; `complJ8_closed_toy_figure` Nock/RedTeam/Batch4842Thm54J8ComplClose.lean:151; `complJ8_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean:202; `complJ9B_toy` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:178; `complJ9B_toy_figure` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:192; `complJ9B_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean:141; `hclA_fails` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:165; `probJ8V_nonvacuous_clean` Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8.lean:64; `acceptsJ8V_mono_rows` Nock/RedTeam/Batch4775Thm54NVJetRegime.lean:43</sub>

## 5. J-9 A

J-9 A is J-9 B plus op-0 / op-10 axes beyond `p`: an axis of up to 62 limbs of `2^32` (`ComplJ9ABinders.lean::AxCap`) is read
or edited through two new chips and a changed compute chip. Everything not named below is J-8 / J-9 B verbatim.

<sub>Sources (generated): `AxCap` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABinders.lean:31</sub>

### 5.1 Machine and chip deltas against J-8

| chip | what changes | width / source |
|---|---|---|
| compute twin `X9` | J-8's compute chip with 14 appended columns (`123..136`: three new one-hot states for a big/field axis in op 0, a big axis in op 10, and a segment pseudo-row; their id, routed child label, limb and segment columns); the one-hot sum runs over 20 states; some J-8 gates are changed on the new states, every other J-8 base gate is kept | `widthHX9 = 137` columns in the twin RAP order: round 0 = `0..82`, round 1 = `83..136` (`RealIOJ9A.lean::crC9`); `ChipHX9.lean` (layout table), `CompX9.lean::gatesHX9_src`, `CompX9.lean::checkCompX9_gates_iff` |
| axis chip `AX` | reads the limbs of an axis and routes its path records: provides the tagged axis key, consumes limb and path records | 52 columns (22 base in round 0 + 3·10 `𝕂` roles); `AxisChipJ9.lean::axisChipJ9`, `RealIOJ9A.lean::crAX` |
| split chip `SP` | splits a big atom into `(hi, lo)` limbs of `2^32` (64 bit columns); provides the records `(id, 2, 0, lo)`, `(id, 3, 0, hi)`; the parameter `nA` (the verifier's atom-table length) is a template parameter, not a prover column | 90 columns (72 base + 3·6 `𝕂` roles); `SplitChipJ9.lean::splitChipJ9`, `RealIOJ9A.lean::crSP` |

The other six chips (cell, J-8 walk, J, atom table at the variant chip `atomChipHQL`, atom walk, and the J-8 compute columns inside the
twin) are those of J-9 B. A trace is `RealIOJ9A.lean::TrJ9A` (eight chips: `C` 137, `M` 242, `W` 166, `J` 71, `A` 349, `V` 166,
`X` 52, `S` 90 columns); `TrJ9A.toJ8` reads the J-8 projection of the compute columns through `permX9`. `StJ9A Q` says every
column of every chip is staged at its round. Public data is `PubJ9A` (the J-8 data, the two orbit layouts and the presence flags
`axOn`, `spOn`); messages are `MsgJ9A'` (`MsgJ8'` plus `pubsX`, `pubsS`).

Presence: the axis and split chips may be absent. `AcceptsJ9A.lean::AXChipOK` is, for `axOn = true`, the five conjuncts
(RAP satisfied, preprocessing bound, injective nodes, orbit adjacency, `nX < p`); for `axOn = false`, the four axis publics are `0`.
`AcceptsJ9A.lean::SPChipOK` is the same for the split chip (absent: `pubsS pubSPs = 0 ∧ pubsS (pubSPs + 1) = 0`).

<sub>Sources (generated): `widthHX9` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ChipHX9.lean:98; `crC9` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:65; `gatesHX9_src` Nock/V1J9A/CompX9.lean:34; `checkCompX9_gates_iff` Nock/V1J9A/CompX9.lean:73; `axisChipJ9` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:365; `crAX` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:67; `splitChipJ9` Nock/NockVMROM/Thm54/VclL/Handle/SplitChipJ9.lean:193; `crSP` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:69; `atomChipHQL` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:109; `TrJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:72; `toJ8` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:86; `permX9` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ChipHX9RAP.lean:48; `StJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:95; `PubJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:44; `MsgJ9A'` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:59; `MsgJ8'` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean:246; `AXChipOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:104; `SPChipOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:118</sub>

### 5.2 The predicate `AcceptsJ9A`

`AcceptsJ9A.AcceptsJ9A δ b Pb Rg c χ M tr r g`.

`AcceptsJ9A.lean::AcceptsJ9A` is a structure of propositions over `(Pb : PubJ9A p) (Rg : Registry) (c : P8PublicClaim)
(χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (r : RowsJ9A) (g : ℕ)`. Against `AcceptsJ9V` (§3.6):
- changed: `hsatX` (the twin RAP `computeChipVCLHX9` satisfied, with preprocessing); `hGp` (the path balance gains the axis chip's path
  consume `pubsX pubAXp`); `hGS` (the service balance gains the axis chip's service terminal `pubsX pubAXs` on the left and the split
  chip's `pubsS pubSPs` on the right); `hnAS : Pb.nA + Pb.nS < 2^57` in place of `hnA62`; `hbud : BudJ9A Pb r (g + r.N)` and
  `hbudV` (which adds `Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP`); the atom table is the variant chip `atomChipHQL` (`hsatL`, `hbindL`);
- added: `hAXk : AXChipOK …`, `hSPk : SPChipOK …`, `hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p`;
- every other field is the J-9 B field at the projections `Pb.toPubJ8`, `M.toMsgJ8'`, `tr.toJ8`, `r.toRowsJ8`
  (`AcceptsJ9A.lean::AcceptsJ9A.of_V` builds an `AcceptsJ9A` from an `AcceptsJ9V` and only the changed and added pieces).

`RealIOJ9A.lean::BudJ9A` is `BudJ8` with three inequalities changed: the axis rows are charged to `N` (`Pb.n + Pb.nX ≤ r.N`), to
the service consumers (`s1`, `+ Pb.nX`) and, with the two split provides per row, to the providers (`s2`, `+ Pb.nX + 2·Pb.nS`).

<sub>Sources (generated): `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `computeChipVCLHX9` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ChipHX9RAP.lean:260; `nX` Nock/RedTeam/Batch1672Thm54VclLRelink.lean:99; `atomChipHQL` Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean:109; `toJ8` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:86; `of_V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:233; `BudJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:141; `BudJ8` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ8.lean:297</sub>

### 5.3 Soundness

`Handle.ProbJ9A.probJ9A_final_clean` (`J9A/ProbJ9A.lean`): for `Rg.Faithful`, a staged `Q` (`hQ : StJ9A Q`), `hpG : p = Nock.Atoms.p`,
`hcK : Fintype.card K = VclL.Events.cK`, and the budget binders
`hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC`, `hAX : r.AX ≤ 2^31`, `hSP : r.SP ≤ 2^31`, `hqM`, `hk : 2 * fuelChip ≤ r.leaves`,
`hmax : Pb.nA + 2 ≤ r.maxlen`, `hg : g ≤ 2^31`, `hLC`, `hLM`, `hLW`, `hLA`, `hLV`, `hnM : Pb.nC ≤ 2^31`,
`hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2^31`,

`Pr_χ[(∃ M, AcceptsJ9A δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`.

Non-vacuity: `Nock.RedTeam.Batch4881.probJ9A_nonvacuous_demo` (`Batch4881Thm54J9APredNC.lean`) exhibits public data, a coin and a message
with every numeric binder of `probJ9A_final_clean` met.

<sub>Sources (generated): `probJ9A_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProbJ9A.lean:548; `Faithful` Nock/Jet/Semantics.lean:106, Nock/Jet/Semantics.lean:114, Nock/Jet/Semantics.lean:117 (several); `probJ9A_nonvacuous_demo` Nock/RedTeam/Batch4881Thm54J9APredNC.lean:178</sub>

### 5.4 Completeness

`Handle.ComplJ9AClosed.complJ9A_closed` (`J9A/ComplJ9AClosed.lean`). For a verified registry `Rg`, a template table `Rt`, a generated
run `hgen` and `B := BRun9A δ b Rt hgen hpG h31A`:
1. `∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g`;
2. `|{χ : ¬ B.Good χ}| / |Coins frameJ8 K| ≤ B.epsC`;
3. `StJ9A B.tr`;
4. `HoldsN (cJ s f r)`;
5. `Fintype.card K = cK → B.epsC < 2^-120 ∧ ∃ χ, AcceptsJ9A … χ (B.M χ) (B.tr χ) B.rows B.g`.

`BRun9A` is one record for both the present and the absent regime of the two chips (they are switched by the program).
Binders: those of `complJ9B_closed` (§4.3) with `hax`, `hwalk`, `h31` replaced by

| binder | meaning |
|---|---|
| `hax9 : ProgAxOK9A p t` | on every row (`ComplJ9ABinders.lean::AxRowX9A`): op-0 axes, op-10 edit axes and `s10L` levels `+1` are `< p` or within the cap `AxCap` (at most 62 limbs of `2^32`); op-9 axes, jet tags and jet ids (clue values) `< p`. Implied by J-9 B's `hax` (`ComplJ9ABinders.lean::progAxOK9A_of_progAxOK`) |
| `hwalk9 : WalkDepthOK9A (rowsOfT t)` | every path read of the J-9 A cell walk has depth `≤ 61` (implied by J-9 B's) |
| `h31A : Rows31A DA` | every table, including the axis and split tables, has `≤ 2^31` rows (`ComplJ9ARun.lean::Rows31A`) |

and the binders `hpG hop5 hleaf hwalkA hRt hregAx` as in §4.3. There is no corner binder.
Hypothesis-free instances: `Nock.RedTeam.Batch4883.complJ9A_toy`, `complJ9A_toy_figure` (both chips on, `ε_c < 2^-120`, an accepting
coin); the absent-chip regime `ComplJ9AAbsent.lean::complJ9A_closed_absent` and `Nock.RedTeam.Batch4882.complJ9A_absent_toy(_figure)`.

<sub>Sources (generated): `complJ9A_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AClosed.lean:166; `StJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:95; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `BRun9A` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ARun.lean:405; `complJ9B_closed` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean:141; `hax9` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:139; `AxRowX9A` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABinders.lean:35; `AxCap` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABinders.lean:31; `progAxOK9A_of_progAxOK` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABinders.lean:58; `hwalk9` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:75; `h31A` Nock/RedTeam/Batch4883Thm54J9AComplToy.lean:382, nockvm-e2e/NockvmE2E/J9A/LinkJ9AF1.lean:127 (several); `Rows31A` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ARun.lean:125; `complJ9A_toy` Nock/RedTeam/Batch4883Thm54J9AComplToy.lean:410; `complJ9A_toy_figure` Nock/RedTeam/Batch4883Thm54J9AComplToy.lean:425; `complJ9A_closed_absent` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAbsent.lean:168; `complJ9A_absent_toy` Nock/RedTeam/Batch4882Thm54J9AComplAbsent.lean:30</sub>

### 5.5 Registry condition

`Handle.CheckedRegistry.CompiledBy p Rg Rt` (`CheckedRegistry.lean::CompiledBy`): for every id with `Rg.R id = some j`,
`j = ⟨(Rt id).toTemplate p, compile p (Rt id)⟩`, `ChipJ8.axPosB (Rt id) = true`, `(Rt id).WellTyped p` and `∀ i, (Rt id).ax i < p`.
It is a property of the registry, checked once, in place of the per-call hypotheses `hRt` and `hregAx`:
`CheckedRegistry.lean::hRt_hregAx_of` derives both for every id a generated run calls, and
`ComplClosedChecked.lean::complJ9A_closed_of` is `complJ9A_closed` with `hC : CompiledBy p Rg Rt` in place of `hRt`, `hregAx`
(`complJ8_closed_of` and `complJ9B_closed_of` likewise).

<sub>Sources (generated): `CompiledBy` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistry.lean:13; `R` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:79; `axPosB` Nock/Jet/ChipJ8.lean:414; `hRt_hregAx_of` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistry.lean:30; `complJ9A_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean:53; `complJ9A_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AClosed.lean:166; `complJ8_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean:143; `complJ9B_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean:187</sub>

### 5.6 Executable generator and checker

- `V1J9A/GenJ9AX.lean::genJ9AX R fuel s f χe : Option InJ9A` generates the instance of a jet-free run (`R` registry, `χe : CoinsE` the coins):
  the twin compute table (`GenCompX9.lean`), the axis chip (`GenAxE.lean`), the split chip (`GenSpE.lean`) and the J-9 B tables with the
  cell-handle multiplicity at the twin's handle consumes (`mhCountsX9E`). Orbits are chosen per chip by `chipOf`.
- `V1J9A/GenJ9AXJ.lean::genJ9AXJ R Rt fuel s f χe : Option InJ9A` is the same with jets: the J-8 call list, the J nouns in the roots, the
  honest J rows and the J chip, mirroring `ComplJ8Data.j8DataOf` / `ComplJ9ADataRec.j9aDataOf`.
- `V1J9A/GenJ9AX.lean::checkJ9AX I : Bool` is the executable checker (`checkJ9A` with the twin compute check `CompX9.checkCompX9`).
  `V1J9A/CheckJ9AIffComp.lean::checkJ9AX_iff` relates it to `AcceptsJ9A` at a valid input (`ValidJ9A`, `CheckJ9AIff.lean`).
- The `nockvm-j9aemit` executable (`TraceDemo/J9AEmit.lean`, `lakefile.toml`) writes a generated instance as per-chip trace files.
  Its output and verdicts are executable evidence, not kernel-checked.

<sub>Sources (generated): `genJ9AX` Nock/V1J9A/GenJ9AX.lean:58; `mhCountsX9E` Nock/V1J9A/GenJ9AX.lean:48; `chipOf` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AGen.lean:110, Nock/NockVMROM/Thm54/P8Core/SVCompute/ChipData.lean:183, Nock/V1J8/GenJ8.lean:41, TraceDemo/J8CheckMain.lean:118 (several); `genJ9AXJ` Nock/V1J9A/GenJ9AXJ.lean:36; `j8DataOf` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Data.lean:409; `j9aDataOf` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ADataRec.lean:91; `checkJ9AX` Nock/V1J9A/GenJ9AX.lean:131; `checkJ9A` Nock/V1J9A/CheckJ9A.lean:163; `checkCompX9` Nock/V1J9A/CompX9.lean:68; `checkJ9AX_iff` Nock/V1J9A/CheckJ9AIffComp.lean:118; `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `ValidJ9A` Nock/V1J9A/CheckJ9AIff.lean:90</sub>

### 5.7 Completeness of the executable link

At every theorem below, `p = Nock.Atoms.p` (`hpG`), `hgen` is the generated run, the binders `hax9 hop5 hleaf hwalk9 hwalkA h31A` are those of
§5.4, and `hχ` says the coin is good: `(BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)`.

**Jet-free runs** (registry `Rg` with `Rt = Example.RtG`), `GenPortJ9AHonest.lean`:
- `genJ9AX_honest_at`: if `genJ9AX Rg.R fuel s f χe = some I` and `hχ`, then for every orbit assignment `o` with `OrbAdm I o`
  (every chip's orbit valid and its rows fit in `3·2^h`), there is `hv : ValidJ9A (withOrb I o)` with
  `AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb I o) hv) Rg.R (withOrb I o).c (toχ (withOrb I o).χ) (withOrb I o).toMsg (withOrb I o).toTr (withOrb I o).toRows (withOrb I o).g`;
- `checkJ9AX_genJ9AX`: under the same hypotheses `checkJ9AX I = true`.

`GenPortJ9AHGoodCoin.lean` adds the binder `hcid : ComplJ8Jet.CalledIds t = ∅` (no jet is called):
- `epsC_lt`: `(BRun9A …).epsC < 2^-120`;
- `exists_good_coinE`: `∃ χe : CoinsE, (BRun9A …).Good (toχ χe)`.

**Jet-calling runs**, `GenPortJ9AHonestJ.lean`, with the template table `Rt`, the generator `genJ9AXJ Rg.R Rt fuel s f χe`, and the extra
hypothesis `hC : CheckedRegistry.CompiledBy p Rg Rt`:
- `genJ9AXJ_honest_at`, `checkJ9AX_genJ9AXJ`: the two statements above for `genJ9AXJ`;
- `GenPortJ9AHGoodCoinJ.lean::exists_good_coinEJ`: `∃ χe : CoinsE, (BRun9A … Rt …).Good (toχ χe)` under `hC` (and `epsC_ltJ`, `badE_leJ`,
  the jet-calling twins of `epsC_lt`, `badE_le`).

`ComplClosedChecked.lean::complJ9A_closed_of` is the closed completeness theorem of §5.4 at `hC`.

Executable evidence only (no theorem): `Nock.RedTeam.Batch4885.run` (`Batch4885Thm54GenJ9AXJ.lean`), the input of `genJ9AXJ` on a jetted
2×2 matrix product at pseudo-random coins, was observed with a compiled build to give `run.isSome = true` and `checkJ9AX I = true`, and a
perturbation of one J-column cell makes `checkJ9AX = false`. It is not evaluated in the kernel.

<sub>Sources (generated): `hax9` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:139; `genJ9AX_honest_at` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonest.lean:195; `genJ9AX` Nock/V1J9A/GenJ9AX.lean:58; `OrbAdm` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbA.lean:55; `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `checkJ9AX_genJ9AX` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonest.lean:232; `checkJ9AX` Nock/V1J9A/GenJ9AX.lean:131; `epsC_lt` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean:112; `exists_good_coinE` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean:123; `genJ9AXJ` Nock/V1J9A/GenJ9AXJ.lean:36; `genJ9AXJ_honest_at` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonestJ.lean:193; `checkJ9AX_genJ9AXJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonestJ.lean:232; `exists_good_coinEJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean:94; `epsC_ltJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean:83; `badE_leJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean:71; `badE_le` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean:100; `complJ9A_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean:53; `run` Nock/RedTeam/Batch4885Thm54GenJ9AXJ.lean:26</sub>

### 5.8 Scope of J-9 A

- The statement is about `AcceptsJ9A` at polynomial traces, as in §11.1: no commitment scheme, no low-degree test; the coins of `genJ9AX` /
  `nockvm-j9aemit` are a pseudo-random generator, not Fiat–Shamir.
- Completeness of the executable link is proved at good coins (`hχ`); `exists_good_coinE` / `exists_good_coinEJ` give the existence of one. The
  fraction of bad coins is at most `epsC`, and `epsC < 2^-120` at `|K| = p^3` (`epsC_lt`, `epsC_ltJ`).
- An op-0 / op-10 axis longer than 62 limbs of `2^32` is outside completeness (`hax9`); soundness is unaffected.

<sub>Sources (generated): `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `genJ9AX` Nock/V1J9A/GenJ9AX.lean:58; `exists_good_coinE` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean:123; `exists_good_coinEJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean:94; `epsC` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean:169, Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean:131, Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AObl.lean:123 (several); `epsC_lt` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean:112; `epsC_ltJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean:83; `hax9` Nock/RedTeam/Batch4856Thm54J9BComplToy.lean:139</sub>

## 6. J-9 AL

J-9 AL is J-9 A plus primitive jets over big atoms: `add`, `sub`, `lt`, `mul`, `div`, `mod` on atoms of up to 62 limbs of `2^32`
are checked by one new chip, the ALU, through a Schwartz–Zippel identity at a limb coin. Everything not named below is J-9 A
verbatim. `Nock/Jet/PrimJ9.lean` has namespace `Jet.Prim.`.

### 6.1 Primitive jets (`Nock/Jet/PrimJ9.lean`)

- `PrimOp` has seven constructors `add sub lt dec mul div mod`. `primSem : PrimOp → ℕ → ℕ → Option ℕ` is their semantics on
  natural numbers: `sub a b = none` iff `a < b`; `div` and `mod` are `none` iff `b = 0`; `dec a = none` iff `a = 0` (and ignores its
  second argument); `lt a b = some 0` iff `a < b` and `some 1` otherwise (Nock loobean: `0` is yes).
- `primTemplate op : Template`: arity `2` and axes `![2, 3]` for the binary operations, arity `1` and axis `![1]` for `dec`;
  `sem` is `none` when an argument is a cell.
- `primC op : Noun` is a Nock formula for the operation (counting loops over single-arm cores); `primSpec op := ⟨primTemplate op, primC op⟩`.
- `primSpec_faithful (op : PrimOp) : (primSpec op).Faithful` and `primSpec_complete`, for all seven operations, no side hypothesis.
- `VerifiedRegistry.addPrim V n op := V.add n (primSpec op) (primSpec_faithful op)`.

A call of a primitive is an ordinary jet hint `[11 [%wild [1 id]] primC op]` (§1.3). In J-9 AL it is not a J-chip row: the ALU chip
checks it, and the J chip sees only the template-registered ids (§6.5).

<sub>Sources (generated): `PrimOp` Nock/Jet/PrimJ9.lean:29; `primSem` Nock/Jet/PrimJ9.lean:33; `primTemplate` Nock/Jet/PrimJ9.lean:58; `primC` Nock/Jet/PrimJ9.lean:117; `primSpec` Nock/Jet/PrimJ9.lean:126; `primSpec_faithful` Nock/Jet/PrimJ9.lean:560; `primSpec_complete` Nock/Jet/PrimJ9.lean:628; `addPrim` Nock/Jet/PrimJ9.lean:632</sub>

### 6.2 Chips, trace and public data

| object | what | source |
|---|---|---|
| ALU `AL` | one new chip over the eight chips of J-9 A: 196 columns = 94 base (round 0) + 3·34 (`𝕂` roles) (`H … RO` in round 1: 54 columns, `invV … accX` in round 2: 48 columns); five verifier-fixed columns: the first-row and last-row masks and the `preg` layout `sP`, `pId`, `pOp`; 180 base gates and 39 `𝕂′` equations (78 mixed gates), every gate of degree `≤ 4` | `AluSZChipJ9.lean::aluSZChipJ9`, `aluSZ_width_eq` (`RealIOJ9AL.lean::wAL = 196`, `crAL`), `baseGates_length`, `aluQ_length`, `aluMixed_length`, `aluSZGates_degree` |
| trace `TrJ9AL` | `TrJ9A` (eight chips, §5.1) plus `L : Fin 196 → F[X]`; `StJ9AL Q` says every column of every chip, ALU included, is staged at its round | `RealIOJ9AL.lean::TrJ9AL`, `StJ9AL` |
| public data `PubJ9AL` | `PubJ9A` plus the ALU's orbit and row layout (`hL nL hnL nodesL orbitL`), the presence flag `aluOn`, the primitive table `prims : List (ℕ × PrimOp)` (id, operation), the cell-table index `idxP id` and rank `rkP id` of each `primC op`, and the verifier-fixed `preg` layout `preL` | `RealIOJ9AL.lean::PubJ9AL` |
| message `MsgJ9AL'` | `MsgJ9A'` plus `pubsL` (the ALU's publics: `pubALv`, `pubALs`, `pubALx` at `0`, `2`, `4`, each with an imaginary part at `+ 1`) | `RealIOJ9AL.lean::MsgJ9AL'`, `AluSZChipJ9.lean::pubALv` |
| rows `RowsJ9AL` | `RowsJ9A` plus `AL`; the census corner is `cornerC9L` (`AL = 2^31`); the budget `BudJ9AL` charges each ALU row one export read and up to two service consumes and provides | `RealIOJ9AL.lean::RowsJ9AL`, `cornerC9L`, `BudJ9AL` |

Rows of the ALU table are `preg` (one per primitive, preprocessed: `sP = 1`, `pId`, `pOp`), `hdr` (one per call), and `lane` rows
(32 bits each); a call is a `hdr` followed by its operand and witness slots, each slot a run of lane rows. Slot roles (`ra rb rc`
operands and result, `rd rx ry rs` witnesses) and the role sequence of each operation are fixed by gates; a slot's mode is one of read-only,
split, view, witness, packed carry (32 carries per row) and 25-bit carry. The identity per operation is a sum of per-slot
contributions evaluated at the limb coin `y`, with `y^t` supplied by the verifier (`AluSZChipJ9.lean::chalsALJ8`, leaves `40 + 2t, 41 + 2t`).

Gate groups (`AluSZChipJ9.lean`):

| group | what it enforces |
|---|---|
| `gKind`, `gSlot`, `gSeq`, `gCompat` | row-kind, operation, role and mode one-hot structure; slot boundaries; the role sequence of each operation (no dropped or repeated operand); mode and role compatibility |
| `gFlag`, `gCoef`, `gHdr`, `gConst`, `gBind` | slot flags; the identity coefficients per (role, operation); the `lt` result, and the operation code `opc = Σ k·op_k` on `hdr` (on `preg`: `opc = pOp`, `id = pId`); block constancy; each slot's handle is its role's block handle |
| `gBits`, `gSplit`, `gCap` | the 32 lane bits are boolean, and the high bits of a 25-bit carry slot are zero; the split of a small atom into two limbs with the `< p` check; a 6-bit counter bounding every Horner value slot to at most 62 limbs |
| `identQ` (`𝕂′`, round 1) | the identity at `y`: Horner evaluation of value slots and packed carries, the link of each slot's value to its handle, the latch and contribution of the product slot, and the running sums `S1`, `S2` that must vanish at the end of each block |
| `logupQ` (`𝕂′`, round 2) | the validity consume `[z, 0, L, 0, sv]` on read and view slots; the service balance (`hdr` consumes the registry key and the operation record, `preg` provides them, `hdr` provides the jet key); the export consume of the call's subject cell |

**Last-row mask.** The next-row gates of the ALU (the block-constancy gates on the operation, handle and value columns
`opCols, lb, kA, kB, kE, vA, vB, vE`, the `sH`-to-`sL` transition, and the `𝕂′` latches and running sums `RL, RO, S1, S2`) carry
the factor `1 − isLT` (`isLT`, column 1, the verifier-fixed last-row mask), so they do not constrain the step from the last row
to the wrapped first row. The mask changes neither the gate count nor the degree bound `≤ 4` (`aluSZGates_degree`). With it, an honest ALU table on an
orbit with spare rows is accepted (`GenPortJ9ALHOrbFree.lean::genJ9ALXJ_honest_at'`, `lastRow_S_zero`); soundness (§6.6) is
proved for this predicate.

The operation codes are `RealIOJ9AL.lean::primCode`: `add 1, sub 2, lt 3, mul 4, div 5, mod 6`, and `dec 0`. The ALU has no row
kind for `dec`: no `hdr` can carry code `0`.

<sub>Sources (generated): `invV` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:184; `pId` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:113; `pOp` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:114; `aluSZChipJ9` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:631; `aluSZ_width_eq` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:649; `wAL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:48; `crAL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:74; `baseGates_length` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:574; `aluQ_length` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:578; `aluMixed_length` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:581; `aluSZGates_degree` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:613; `TrJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:77; `TrJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:72; `StJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:81; `PubJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:53; `PubJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:44; `rkP` nockvm-e2e/NockvmE2E/Exec/E2EInstGen.lean:435; `primC` Nock/Jet/PrimJ9.lean:117; `MsgJ9AL'` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:68; `MsgJ9A'` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:59; `pubsL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtom.lean:101; `pubALv` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:194; `pubALs` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:195; `pubALx` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:196; `RowsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:85; `RowsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:102; `cornerC9L` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:89; `BudJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:114; `chalsALJ8` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:680; `gKind` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:269; `gSlot` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:283; `gSeq` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:297; `gCompat` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:308; `gFlag` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:319; `gCoef` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:332; `gHdr` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:349; `gConst` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:355; `gBind` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:363; `opc` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:160; `gBits` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:369; `gSplit` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:380; `gCap` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:383; `identQ` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:448; `logupQ` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:490; `isLT` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:111; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `genJ9ALXJ_honest_at'` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbFree.lean:911; `lastRow_S_zero` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbFree.lean:337; `primCode` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:44</sub>

### 6.3 The predicate `AcceptsJ9AL`

`AcceptsJ9AL.AcceptsJ9AL δ b Pb Rg c χ M tr r g`.

`AcceptsJ9AL.lean::AcceptsJ9AL` is a structure of propositions over `(Pb : PubJ9AL p) (Rg : Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
(M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) (r : RowsJ9AL) (g : ℕ)`. Against `AcceptsJ9A` (§5.2), every field is the J-9 A field at the
projections `Pb.toPubJ9A`, `M.toMsgJ9A'`, `tr.toTrJ9A`, `r.toRowsJ9A` except:
- changed: `hGx` (the handle-export balance gains the ALU's export terminal `pubALx` on the left, with the J chip's); `hGS` (the service
  balance gains the primitive pins `pinRgP`, `pinOpP` and the ALU service terminal `pubALs` on the left); `hsumC'` (the cell-validity
  balance gains the ALU validity terminal `pubALv` on the left and the primitive claim records `pinRecsP` among the consumers); `hcen'`
  (the census covers `censusGJ9 ++ censusP`, where `censusP Pb = Pb.prims.map (primC ·.2)`); `hbud : BudJ9AL Pb r (g + r.N)`;
- added: `hALk : ALChipOK …` (§6.4), `hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (primSpec q.2)`, `hdisjP : ∀ q ∈ Pb.prims, q.1 ∉ Pb.regs`,
  `hlenL : Pb.nL + Pb.n < p ∧ Pb.nL ≤ r.AL ∧ ∀ q ∈ Pb.prims, q.1 < p ∧ Pb.idxP q.1 < p`, `hndP : (Pb.prims.map Prod.fst).Nodup`,
  `hrkP : ∀ q ∈ Pb.prims, Pb.rkP q.1 ≠ (0, 0)`, `hltP` (primitive ranks and indices are field elements), `hlenCP`
  (`3 + |Pb.regs| + |Pb.prims| + Pb.nL + 2·Pb.nC < p`).

Per primitive the verifier computes two service pins, the registry key `pinRgP` (`(id, 1, idxP id, 0, 0, 0, 0, 7)`) and the operation record
`pinOpP` (`(id, primCode op, 0, 0, 0, 0, 0, 6)`), and one claim record `pinRecsP` (`encJ8 (primC op)` at `idxP id` with rank `rkP id`).
The two service keys carry the same weight in the ALU's balance, so both are pinned once. The claim record, `hrkP` and the census at
`primC op` bind the cell at `idxP id` to the noun `primC op` (`AcceptsJ9AL.lean::hReg_of_pinP`). The ALU's registry key has tag `7`, the J chip's tag `2`
(`AcceptsJ9AL.lean::pinRgVec_ne_pinCons`).

<sub>Sources (generated): `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `pubALx` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:196, nockvm-e2e/NockvmE2E/Exec/PubExe9L.lean:21 (several); `pinRgP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:143; `pinOpP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:149; `pubALs` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:195, nockvm-e2e/NockvmE2E/Exec/PubExe9L.lean:20 (several); `pubALv` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:194, nockvm-e2e/NockvmE2E/Exec/PubExe9L.lean:19 (several); `pinRecsP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:181; `censusGJ9` Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean:297; `censusP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:187; `encJ8` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8.lean:413; `rkP` nockvm-e2e/NockvmE2E/Exec/E2EInstGen.lean:435; `primC` Nock/Jet/PrimJ9.lean:117; `hReg_of_pinP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:454; `pinRgVec_ne_pinCons` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:166</sub>

### 6.4 Presence of the ALU

`AcceptsJ9AL.lean::ALChipOK` is a disjunction. Present: `aluOn = true`, the ALU RAP satisfied with preprocessing bound, injective nodes,
orbit adjacency, `nL < p`, and `PregOK` (`preg` row `i < |prims|` has `sP = 1`, `pId` the id, `pOp` the operation code; every other row is `0`).
Absent: `aluOn = false`, `prims = []`, and the six ALU publics `pubsL pubALv`, `pubsL (pubALv + 1)`, `pubsL pubALs`, `pubsL (pubALs + 1)`,
`pubsL pubALx`, `pubsL (pubALx + 1)` are `0`. With the ALU absent, `pinRgP`, `pinOpP`, `pinRecsP` and `censusP` are empty
(`pinRecsP_nil`, `censusP_nil`), and `AcceptsJ9AL.lean::AcceptsJ9AL.of_A` turns an `AcceptsJ9A` plus `hlenL` and `hlenCP` into an `AcceptsJ9AL`.
`Nock.RedTeam.Batch4935.acceptsJ9AL_noAlu` exhibits an accepting instance with the ALU off.

<sub>Sources (generated): `ALChipOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:125; `PregOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:116; `pId` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:113; `pOp` Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean:114; `pubsL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtom.lean:101; `pinRgP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:143; `pinOpP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:149; `pinRecsP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:181; `censusP` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:187; `pinRecsP_nil` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:189; `censusP_nil` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:192; `of_A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:338; `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `acceptsJ9AL_noAlu` Nock/RedTeam/Batch4935Thm54J9ALNoAluInhabitant.lean:43</sub>

### 6.5 Registering primitives

The registry condition of J-9 AL has two parts: primitive ids and template ids are disjoint, and each primitive id maps to its spec.
- `CheckedRegistryP.lean::addPrims V prims` registers every `(id, op)` of `prims` at `primSpec op` (`addPrim`, folded right);
  `CheckedRegP` is a `CheckedReg` plus a primitive list `prims` with distinct ids (`ndP`), and `toVR := toCR.toVR.addPrims prims`.
- `CheckedRegistryP.lean::CompiledByP p Rg Rt prims`: every registered id outside `prims.map Prod.fst` is the compiled template
  `⟨(Rt id).toTemplate p, compile p (Rt id)⟩` with `axPosB (Rt id) = true`, `(Rt id).WellTyped p` and all axes `< p`; and every `q ∈ prims`
  has `Rg.R q.1 = some (primSpec q.2)`. `CheckedRegP.compiledByP` holds for every `CheckedRegP`; `compiledByP_nil` embeds `CompiledBy`.
- `CheckedRegistryP.lean::hRt_hregAx_ofP` derives, from `CompiledByP` and a generated run, the template conditions for every called
  non-primitive id and the primitive condition `hprim`.
- The J chip and the compiled-template machinery of J-9 A run over `ComplJ9ALData.lean::rtP Rt prims`, which sends every primitive id to
  the trivial template `trivTpl` (arity `0`, body `const 0`). Calls are split by id: primitive calls go to the ALU, the others to the J chip.

<sub>Sources (generated): `addPrims` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:27; `primSpec` Nock/Jet/PrimJ9.lean:126; `addPrim` Nock/Jet/PrimJ9.lean:632; `CheckedRegP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:66; `CheckedReg` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistry.lean:43; `toVR` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:71; `CompiledByP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:54; `map` Nock/Verb.lean:163, Nock/NockVMROM/Thm54/GigaRAPIOSlots.lean:182, Nock/NockVMROM/Thm54/GigaRAPThirdMessage.lean:207 (several); `axPosB` Nock/Jet/ChipJ8.lean:414; `R` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:79; `compiledByP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:73; `compiledByP_nil` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:61; `CompiledBy` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistry.lean:13; `hRt_hregAx_ofP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:81; `rtP` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALData.lean:67; `trivTpl` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALData.lean:59</sub>

### 6.6 Soundness

`Handle.ProbJ9AL.probJ9AL_final_clean` (`J9AL/ProbJ9AL.lean`): for `Rg.Faithful`, a public claim `c`, a staged `Q` (`hQ : StJ9AL Q`),
`hpG : p = Nock.Atoms.p`, `hcK : Fintype.card K = VclL.Events.cK` and the budget binders listed below,

`Pr_χ[(∃ M, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`.

Binders against `probJ9A_final_clean` (§5.3): `Pb : PubJ9AL p`, `Q : Coins frameJ8 K → TrJ9AL (ZMod p)`, `r : RowsJ9AL`; the added
`hAL : r.AL ≤ 2^31`; and `hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2^31` in place of `hreg9`. The others
(`hr hAX hSP hqM hk hmax hg hLC hLM hLW hLA hLV hnM`) are unchanged. No binder mentions the primitive table: that `Rg` registers
each primitive at its spec is the field `hPrim` of the predicate, and soundness needs only `Rg.Faithful`.

Error figure. The summand list is J-9 A's list at the J-9 AL rows plus one event, the ALU's identity at the limb coin
(`RR49AL.lean::boundJ9AL`):

`boundJ9AL c c′ r P g = boundJ8X c c′ (rowsBL r) P (gL r g) + wSZ r / c²`,

with `rowsBL r` the J-9 A rows with `blocks + 2·AL` and `rd + AL`, `gL r g = g + N + AX + 3·AL`, and `wSZ r = AluSZEvent.weightC r.AL r.A r.AL`
(`AL·(2A + 32·AL + 2)`). `numJ9AL_le_P4`: at the census corner (`cornerC9L`, `P = 2^66`, `g = 2^31`) the numerator
`numJ9AL c cornerC9L (2^66) (2^31)` is at most `xP4 c`, by kernel `decide`; `xP4_lt` (from `RepriceJ9AL.lean::numJ8X_optL_census32`) gives
`xP4 cK · 2^155 < cK⁴`. `figJ9AL_155`: `boundJ9AL cK (cK²) r P g < 2^-155` below the corner (`AX, SP, AL ≤ 2^31`, `P ≤ 2^66`, `g ≤ 2^31`);
`probJ9AL_lt_155` is the probability statement for any soundness core, and `probJ9AL_final_clean` instantiates it for the cases
`1 ≤ krootsV` and `krootsV = 0` (`soundAL_present`, `soundAL_absent`).

<sub>Sources (generated): `probJ9AL_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:550; `Faithful` Nock/Jet/Semantics.lean:106, Nock/Jet/Semantics.lean:114, Nock/Jet/Semantics.lean:117 (several); `probJ9A_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProbJ9A.lean:548; `boundJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:83; `rowsBL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:69; `blocks` Nock/Jet/ChipJ8.lean:398; `wSZ` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:77; `numJ9AL_le_P4` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:105; `cornerC9L` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:89; `numJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:80; `xP4` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:94; `xP4_lt` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:100; `numJ8X_optL_census32` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RepriceJ9AL.lean:23; `figJ9AL_155` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:141; `probJ9AL_lt_155` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean:545; `soundAL_present` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:340; `soundAL_absent` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:278</sub>

### 6.7 Completeness

`Handle.ComplJ9ALClosed.complJ9AL_closed` (`J9AL/ComplJ9ALClosed.lean`). For a verified registry `Rg`, a template table `Rt`, a primitive table
`prims`, a generated run `hgen : genX Rg.R fuel s f = some (t, r)` and `B := BRun9AL δ b (rtP Rt prims) hgen prims hpG h31A`, the conclusion
is the five items of §5.4 with `AcceptsJ9AL` and `StJ9AL` in place of `AcceptsJ9A` and `StJ9A`; item 5 gives `B.epsC < 2^-120` and an accepting coin.
Binders: those of `complJ9A_closed` (§5.4) at the template table `rtP Rt prims`, namely `hpG hax9 hop5 hleaf hwalk9 hwalkA h31A`, and

| binder | meaning |
|---|---|
| `hRt`, `hregAx` | every called id that is not a primitive id is registered as its compiled template, with `axPosB` and `WellTyped`, and its axes are `< p` |
| `hnd : (prims.map Prod.fst).Nodup` | primitive ids are distinct |
| `hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)` | every primitive id is registered at its spec |
| `h31L : ComplJ9ALRun.aluLen … < 2^31` | the honest ALU length is below `2^31`; the table has `aluLen + 1` rows, so at most `2^31` |
| `hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t` | at every primitive call of the run both operands have at most 62 limbs of `2^32` |
| `hnoDec : ∀ q ∈ prims, q.2 ≠ .dec` | no primitive is `dec` |

`complJ9AL_closed_of` is the same with `hC : CheckedRegistryP.CompiledByP p Rg Rt prims` in place of `hRt`, `hregAx`, `hprim`.
Completeness limits, in addition to those of §5.8: primitive operands within 62 limbs (results need no bound); no `dec` primitive, so `dec` is
specified and proved faithful (§6.1) but is not covered by the honest prover; the ALU table has at most `2^31` rows (`aluLen < 2^31`). Runs outside
these limits are outside completeness; soundness is unaffected.

<sub>Sources (generated): `complJ9AL_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean:1031; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `StJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:81; `AcceptsJ9A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean:129; `StJ9A` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean:95; `epsC` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean:169, Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean:131, Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AObl.lean:123 (several); `complJ9A_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AClosed.lean:166; `rtP` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALData.lean:67; `axPosB` Nock/Jet/ChipJ8.lean:414; `WellTyped` Nock/Jet/Autogen.lean:115; `aluLen` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALRun.lean:162; `complJ9AL_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean:1083</sub>

### 6.8 Executable generator and checker

- `V1J9AL/CheckJ9AL.lean::InJ9AL` is `InJ9A` plus the ALU table, `pubsL`, `aluOn`, `prims`, `idxP`, `rkP` and `rAL`. `checkJ9ALX I : Bool` is the nine-chip
  checker: `checkJ9AL` with the twin compute check `CompX9.checkCompX9` wired in. `checkJ9AL` is `validB ∧ validAXSPB ∧ validALB ∧ checkStaticJ9AL ∧ checkPubJ9ALE ∧ chipsBJ9AL`;
  `alOK` is `ALChipOK` decided, with the five fixed columns `prepAL` built from `prims` (`pregCol`) and the executable challenge vector `chalsALJ8E`.
- `V1J9AL/CheckJ9ALIff.lean::checkJ9ALX_iff (I : InJ9AL) (Rg : Registry) (hreg : RegOK I.toInJ8 Rg) (hprim : ∀ q ∈ I.prims, Rg q.1 = some (primSpec q.2))`:
  `checkJ9ALX I = true ↔ ∃ hv : ValidJ9AL I, AcceptsJ9AL deltaF powerBasis3 (mkPbAL I hv) Rg I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g`. `hprim` is the
  predicate's field `hPrim`: it is an equation on the registry function and is not decided by the checker.
- `V1J9AL/GenJ9ALXJ.lean::genJ9ALXJ R Rt prims fuel s f χe : Option InJ9AL` generates the input of a run with jets and primitives. Only the
  primitives that are called enter the ALU; when none is called the ALU is absent (`aluOn = false`, `prims = []`, one zero row).
- `GenPortJ9ALHonestJ.lean`: under the hypotheses of `complJ9AL_closed_of`, if `genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I` and the coin is
  good (`hχ : (BRun9AL …).Good (toχ χe)`), then `genJ9ALXJ_honest_at` gives, for every admissible orbit `o` (`OrbAdmL I o`), `ValidJ9AL (withOrbL I o)` and `AcceptsJ9AL` at it;
  `genJ9ALXJ_honest` gives the same at the orbit the generator chose; `checkJ9ALX_genJ9ALXJ` gives `checkJ9ALX I = true`.
- Staged generator, `GenPortJ9ALHStaged.lean` over `V1J9AL/GenJ9ALXJStaged.lean`. The nineteen coins of `frameJ8` (§3.2) are sampled in two groups
  (§3.7.1): `Coins0 := Fin 13 → K3` at `idxS0 = [2, 3, 8, …, 18]` (after round 0) and `Coins1 := Fin 6 → K3` at `idxS1 = [0, 1, 4, 5, 6, 7]` (after round 1).
  `gen0` runs the program and returns the round-0 columns of the nine chips and takes no coin; `gen1 st coins0` returns the round-1 columns from the
  `Coins0` coins; `gen2 st coins1` returns the round-2 columns and the rest of the record from the `Coins1` coins; `runStaged` composes them.
  `runStaged_eq`: for every `χe`, `runStaged R Rt prims fuel s f (c0 χe) (c1 χe) = genJ9ALXJ R Rt prims fuel s f χe`, for every registry,
  template table, primitive list, fuel, subject and formula. `checkJ9ALX_staged`: under the binders of `checkJ9ALX_genJ9ALXJ`, if
  `runStaged … a b = some I` and `assemble a b` is a good coin then `checkJ9ALX I = true`.
- `Nock.RedTeam.Batch4937.genLinkMat` (J-9 A, no ALU): hypothesis-free; for the program calling the compiled `matmul` template of size `2` as jet id `7`
  there is a coin `χe` with `genJ9AXJ … = some I` and `checkJ9AX I = true`.
- The `nockvm-j9alemit` executable (`TraceDemo/J9ALEmit.lean`, `lakefile.toml`; programs `toy`, `absent`, `corner-t1`, `corner-t5`) generates an instance
  with `genJ9ALXJ` over the empty registry and an empty primitive table, checks it with `checkJ9ALX`, and writes per-chip trace files only if the
  verdict is `true`. Its coins are a pseudo-random generator, not Fiat–Shamir. Its output is executable evidence, not kernel-checked.
  With a third argument `add` or `mul` it instead runs a program calling that primitive over `addPrims empty [(7, op)]` (ALU chip on), and each
  `prims` entry of `pubeq.json` carries the op code `RealIOJ9AL.primCode`.
- The end-to-end interface `J9AL/E2EJ9ALIface.lean` (the twin of `J9A/E2EJ9AIface.lean`): `listJ9AL` (the bad-event summands of
  `probJ9AL_absent` / `probJ9AL_present`, by `krootsV`), `epsilonOf_listJ9AL` (their total `< 2^-155` at `|K| = cK`),
  `soundJ9AL_pointwise` (`AcceptsJ9AL` at a trace and coin outside every summand implies `HoldsN c`), `oneRound_listJ9AL` (each
  summand is a one-round event, `OneRoundCD frameJ8`); binders those of `probJ9AL_final_clean`. `J9AL/PregLagrange.lean::preL_eval_pregCol`:
  the Lagrange interpolant of the honest table's preg columns, at node `i`, is the verifier's `CheckJ9AL.pregCol ps k i`, for
  injective nodes (`hinj`), no `dec` primitive (`hnoDec`) and a table no longer than the number of nodes (`hlen`).

<sub>Sources (generated): `InJ9AL` Nock/V1J9AL/CheckJ9AL.lean:52; `InJ9A` Nock/V1J9A/CheckJ9A.lean:48; `pubsL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtom.lean:101; `rkP` nockvm-e2e/NockvmE2E/Exec/E2EInstGen.lean:435; `checkJ9ALX` Nock/V1J9AL/CheckJ9AL.lean:213; `checkJ9AL` Nock/V1J9AL/CheckJ9AL.lean:202; `checkCompX9` Nock/V1J9A/CompX9.lean:68; `validB` Nock/V1J8/CheckJ8.lean:290; `alOK` Nock/V1J9AL/CheckJ9AL.lean:185; `ALChipOK` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:125; `prepAL` Nock/V1J9AL/CheckJ9AL.lean:70; `pregCol` Nock/V1J9AL/CheckJ9AL.lean:64; `chalsALJ8E` Nock/V1J9AL/CheckJ9AL.lean:76; `checkJ9ALX_iff` Nock/V1J9AL/CheckJ9ALIff.lean:644; `genJ9ALXJ` Nock/V1J9AL/GenJ9ALXJ.lean:48; `complJ9AL_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean:1083; `genJ9ALXJ_honest_at` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:927; `OrbAdmL` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrb.lean:38; `ValidJ9AL` Nock/V1J9AL/CheckJ9ALIff.lean:79; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `genJ9ALXJ_honest` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:956; `checkJ9ALX_genJ9ALXJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:995; `frameJ8` Nock/NockVMROM/Thm54/VclL/Handle/FrameJ8.lean:29; `Coins0` Nock/V1J9AL/GenJ9ALXJStaged.lean:37; `idxS0` Nock/DriverJ8/TranscriptJ8.lean:34; `Coins1` Nock/V1J9AL/GenJ9ALXJStaged.lean:38; `idxS1` Nock/DriverJ8/TranscriptJ8.lean:36; `gen0` Nock/V1J9AL/GenJ9ALXJStaged.lean:127; `gen1` Nock/V1J9AL/GenJ9ALXJStaged.lean:134; `gen2` Nock/V1J9AL/GenJ9ALXJStaged.lean:138; `runStaged` Nock/V1J9AL/GenJ9ALXJStaged.lean:143; `runStaged_eq` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHStaged.lean:860; `checkJ9ALX_staged` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHStaged.lean:872; `assemble` Nock/V1J9AL/GenJ9ALXJStaged.lean:48; `genLinkMat` Nock/RedTeam/Batch4937Thm54J9AMatmulGenLink.lean:269; `genJ9AXJ` Nock/V1J9A/GenJ9AXJ.lean:36; `checkJ9AX` Nock/V1J9A/GenJ9AX.lean:131; `addPrims` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:27; `primCode` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:44; `listJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/E2EJ9ALIface.lean:64; `probJ9AL_absent` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:491; `probJ9AL_present` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:462; `epsilonOf_listJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/E2EJ9ALIface.lean:81; `soundJ9AL_pointwise` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/E2EJ9ALIface.lean:96; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `oneRound_listJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/E2EJ9ALIface.lean:169; `OneRoundCD` Nock/NockVMROM/Thm54/VclL/Handle/E2EJ8Iface.lean:131; `probJ9AL_final_clean` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean:550; `preL_eval_pregCol` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/PregLagrange.lean:34</sub>

### 6.9 Non-vacuity and attacks

Each is a kernel-checked instance at `K = KC`, `δ = deltaF`, `b = powerBasis3`, Goldilocks; axioms in §11.2.

| theorem | content |
|---|---|
| `Nock.RedTeam.Batch4921.complJ9AL_toy`, `complJ9AL_toy_figure` | `*[[(p+5) (p+7)] [11 [%wild [1 id_add]] (primC add)]] = 2p+12` over `addPrims empty [(id_add, add)]`: one `add` call on two big atoms, ALU on; `complJ9AL_closed` with every binder discharged; `ε_c < 2^-120` and an accepting coin |
| `Nock.RedTeam.Batch4922.false_claim_rejected_AL` and companions | the soundness bound read at a false claim, with the in-regime binders gathered in `RegimeAL`; the label-equal false claim (`labelJ9_cTrue_cFalse`, `cFalse_rejected_AL`); the atom wrap `v` vs `v + p` (`labelJ9_wrap_ne`, `wrap_claim_rejected_AL`); padding by `p` copies (`pinRecsP_length`, `censusP_length`, `prims_len_le`, `bus_len_lt_p`); post-coin record lists are coin-free along `StJ9AL` (`postcoin_lists_AL`, `aluFp_staged`); and structural rejections of out-of-regime data (`nAS_out_rejected`, `rows_out_rejected`, `nL_out_rejected`, `axOff_forged_rejected`, `spOff_forged_rejected`, `aluOff_forged_rejected`, `aluOff_prims_rejected`, `aluOn_forces_chip`, `primUnreg_rejected`, `primId_in_regs_rejected`, `primId_dup_rejected`, `primId_out_rejected`, `lenCP_out_rejected`) |
| `Nock.RedTeam.Batch4923.opConfusion_rejected` and the `nc*` claims | 23 concrete false claims (primitive calls, a cell operand, and two Nock increments on big atoms), each with `¬ HoldsN` (`nc3a_wrap_add_false`, `nc4_product_split_wrap_false`, `nc5a_dropped_top_carry_false`, `nc8a_sub_underflow_wrap_false`, `nc9a_div_by_zero_false`, `nc9c_remainder_ge_divisor_false`, `nc10a_forged_lt_false`, `nc11_column_overflow_false`, `nc12a_missing_pair_false`, and others), positive controls for the true calls (`ctl_add`, `ctl_lt_big`, `ctl_mul_big`, …) and `*_rejected_AL`: `Pr < 2^-155` at every in-regime datum. `opConfusion_rejected`: a primitive table entry whose id is registered at a different operation's spec has no accepting instance. These are the soundness bound read at each claim; they do not locate the gate that fires |
| `Nock.RedTeam.Batch4930.acceptsJ9AL_withPrims` | an accepting instance of `AcceptsJ9AL` with the ALU on and `prims = [(id_add, add)]`, and the claim holds |
| `Nock.RedTeam.Batch4932.complJ9AL_toy`, `complJ9AL_toy_figure` | `mul` on `2^70 + 3` and `2^65 + 11`: `complJ9AL_closed` with every binder discharged |
| `Nock.RedTeam.Batch4933.complJ9AL_toy`, `complJ9AL_toy_figure` | `lt` on `2^70 + 3` and `2^80 + 5`: the same |
| `Nock.RedTeam.Batch4934.complJ9AL_toy`, `complJ9AL_toy_figure` | `div` of `2^95 + 7` (big) by `2^20 + 3` (small, through the split handle): the same |
| `Nock.RedTeam.Batch4935.acceptsJ9AL_noAlu` | an accepting instance with `aluOn = false` and `prims = []`, from the J-9 A toy run by `AcceptsJ9AL.of_A` |
| `Nock.RedTeam.Batch4936.genLink_toy` | the run of `Batch4921`: there is a coin `χe` with `genJ9ALXJ … = some I` and `checkJ9ALX I = true`; every binder of `checkJ9ALX_genJ9ALXJ` is discharged |

<sub>Sources (generated): `complJ9AL_toy` Nock/RedTeam/Batch4921Thm54J9ALComplToy.lean:155; `complJ9AL_toy_figure` Nock/RedTeam/Batch4933Thm54J9ALLtDemo.lean:614, Nock/RedTeam/Batch4921Thm54J9ALComplToy.lean:170, Nock/RedTeam/Batch4932Thm54J9ALMulDemo.lean:616, Nock/RedTeam/Batch4934Thm54J9ALDivDemo.lean:617 (several); `addPrims` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:27; `complJ9AL_closed` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean:1031; `false_claim_rejected_AL` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:92; `RegimeAL` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:65; `labelJ9_cTrue_cFalse` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:112, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:244 (several); `cFalse_rejected_AL` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:116; `labelJ9_wrap_ne` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:134; `wrap_claim_rejected_AL` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:149; `pinRecsP_length` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:178; `censusP_length` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:182; `prims_len_le` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:192; `bus_len_lt_p` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:202, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:282 (several); `StJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:81; `postcoin_lists_AL` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:220; `aluFp_staged` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:242; `nAS_out_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:271, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:310 (several); `rows_out_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:276, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:315 (several); `nL_out_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:282; `axOff_forged_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:300, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:323 (several); `spOff_forged_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:310, Nock/RedTeam/Batch4881Thm54J9APredNC.lean:333 (several); `aluOff_forged_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:320; `aluOff_prims_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:331; `aluOn_forces_chip` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:341; `primUnreg_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:353; `primId_in_regs_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:359; `primId_dup_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:364; `primId_out_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:288; `lenCP_out_rejected` Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean:294; `opConfusion_rejected` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:468; `nc3a_wrap_add_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:185; `nc4_product_split_wrap_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:191; `nc5a_dropped_top_carry_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:194; `nc8a_sub_underflow_wrap_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:206; `nc9a_div_by_zero_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:212; `nc9c_remainder_ge_divisor_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:218; `nc10a_forged_lt_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:224; `nc11_column_overflow_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:233; `nc12a_missing_pair_false` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:236; `ctl_add` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:275; `ctl_lt_big` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:284; `ctl_mul_big` Nock/RedTeam/Batch4923Thm54J9ALAttackNC.lean:290; `acceptsJ9AL_withPrims` Nock/RedTeam/Batch4930Thm54J9ALPrimNonvac.lean:35; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `acceptsJ9AL_noAlu` Nock/RedTeam/Batch4935Thm54J9ALNoAluInhabitant.lean:43; `of_A` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:338; `genLink_toy` Nock/RedTeam/Batch4936Thm54J9ALGenLinkToy.lean:52; `genJ9ALXJ` Nock/V1J9AL/GenJ9ALXJ.lean:48; `checkJ9ALX` Nock/V1J9AL/CheckJ9AL.lean:213; `checkJ9ALX_genJ9ALXJ` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean:995</sub>

### 6.10 Scope of J-9 AL

- The statements are about `AcceptsJ9AL` at polynomial traces, as in §11.1 and §5.8.
- The ALU covers `add sub lt mul div mod`. `dec` is a specified, faithful primitive (§6.1) but the ALU has no operation code for it and the
  completeness theorem excludes it (`hnoDec`).
- Primitive operands of more than 62 limbs are outside completeness (`hlimb`); the honest ALU table must have at most `2^31` rows (`h31L : aluLen < 2^31`, `aluLen + 1` rows).
- `Rg.R` must register each primitive id at its spec (`hPrim`); ids must be distinct from each other and from the J-chip registry ids (`hndP`, `hdisjP`).
- The ALU's next-row gates are masked at the last row (§6.2), so an honest ALU table is accepted on any orbit that fits it; the soundness figure of §6.6 is proved for this predicate.
- The `Ty.N` extension (§1.4.1) is independent of the ALU; it applies to J-8, J-9 B and J-9 A statements and to J-9 AL through the same theorems.

<sub>Sources (generated): `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `aluLen` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALRun.lean:162; `R` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:79; `N` Nock/NockVMROM/Thm54/P8Core/OptimizedFailureEventEv.lean:81</sub>

### 6.11 Example: a template-jet J-9 AL run

Module `Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean`.

The run is hypothesis-free, at `K = KC`, `δ = deltaF`, `b = powerBasis3`. It is the program `jp` (namespace `Nock.RedTeam.Batch4939`):
- subject `sJ = [3 (p+5)]`;
- formula `fJP = [[11 [%wild [1 7]] (compile p TN)] [11 [%wild [1 8]] (primC add)]]`;
- fuel `4`;
- the checked registry `catJ` (`CheckedRegP`): the compiled template `TN` at id `7`, and the primitive `add` at id `8` (`catJ.prims = [(8, add)]`);
- templates `rtP catJ.toCR.Rt catJ.prims`.

It makes one template jet call and one big-atom primitive call, so the J-8 tables carry jet rows and the ALU chip is on. `TN` and `catJ`
are the catalogue the end-to-end package's template-jet headline is stated over.
- `genLinkTpl : ∃ χe I, genJ9ALXJ catJ.toVR.R (rtP catJ.toCR.Rt catJ.prims) catJ.prims 4 sJ fJP χe = some I ∧ checkJ9ALX I = true`.
- `complJ9AL_tpl`: the `complJ9AL_closed_of` instance at this run, with every binder discharged (`hRt`/`hregAx` from
  `catJ.compiledByP`, so the template clause is not vacuous). On every good coin `AcceptsJ9AL … catJ.toVR.R (cJ sJ fJP rT) χ (BL.M χ) (BL.tr χ) BL.rows BL.g`
  holds; `Pr[¬ Good] ≤ BL.epsC`; `StJ9AL BL.tr`; `HoldsN (cJ sJ fJP rT)`; and at `|K| = cK`, `BL.epsC < 2^-120` with an accepting coin.
- `honestTpl`: the generated record is valid and accepted by `AcceptsJ9AL` at every orbit choice `o` with `OrbAdmL' I o` (`GenPortJ9ALHOrbFree.lean::OrbAdmL'`).
- `rowsTpl_le`: every chip (in `rowsTpl_le`'s lettering: `X` compute, `C` cell table, `W` cell walk, `J`, `A` atom table, `V` atom walk, `AX` axis, `SP` split, `AL` ALU; traces use `C` for compute and `X` for the axis chip, §5.1) of every generated record has at most `nRowsTpl` rows, for every coin.
  `nRowsTpl = 157` (the cell table, the largest chip); `nRowsTpl_le_768 : nRowsTpl ≤ 3 · 2^8`.
- `honestTplUnif`: there is a coin `χe` and record `I` with `genJ9ALXJ … = some I` such that, for every `h ≥ 1` and
  every `ω : Gold` with `orderOf ω = 3 · 2^h` and `nRowsTpl ≤ 3 · 2^h`, the record on the uniform orbit `orbU h ω`
  (all nine chips on `⟨h, ω⟩`) is valid and accepted by `AcceptsJ9AL`. This is the form `nockvm-e2e` consumes.

The run and its J-8 / J-9 A facts are kernel `decide` on the explicit five-node execution tree. The ALU length is a bound (`aluLen ≤ 48`).

<sub>Sources (generated): `fJP` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:74; `catJ` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:65; `CheckedRegP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:66; `rtP` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALData.lean:67; `genLinkTpl` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:654; `complJ9AL_tpl` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:631; `complJ9AL_closed_of` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean:1083; `compiledByP` Nock/NockVMROM/Thm54/VclL/Handle/CheckedRegistryP.lean:73; `AcceptsJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean:196; `StJ9AL` Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9AL.lean:81; `HoldsN` Nock/Atoms/HoldsN.lean:33, Nock/Jet/Semantics.lean:41 (several); `epsC` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8.lean:169, Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean:131, Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AObl.lean:123 (several); `honestTpl` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:667; `OrbAdmL'` Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbFree.lean:617; `rowsTpl_le` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:741; `nRowsTpl` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:684; `nRowsTpl_le_768` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:686; `honestTplUnif` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:757; `genJ9ALXJ` Nock/V1J9AL/GenJ9ALXJ.lean:48; `orderOf` nockvm-e2e/NockvmE2E/Exec/VChip.lean:29; `orbU` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:752; `aluLen` Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALRun.lean:162</sub>

## 7. Trace uniqueness on the P1 fragment (J-8)

Namespace `Handle.TU`.

**Statement.** On a fragment of claims, an accepted J-8 prover tuple (its transcript) is the honest generator's tuple, except with small
probability over the coins. A soundness theorem (§4.1) bounds the probability that a false claim is accepted; this statement is about the
transcript itself.

**The fragment** (`TU/StatementP1.lean::P1FragC c`):
- every formula op is among `0, 7, 10` and cons (`OpsP1`);
- every op-0 / op-10 axis is in `[1, 2^61)` (`axesB`);
- every atom of the claim's subject, formula and result is `< p`;
- a run exists (`genX … c.subject c.formula = some (t, c.result)` for some fuel).

**The size premise** (`TU/ClaimSizesP1.lean::P1SizeOK p c`): the canonical run `runP1 c` exists, fits `2^31` rows (`Rows31`),
and its roots meet the leaf bound (`RootsLeafOK`). It is a hypothesis. It does not follow from the fragment: nested op-7 formulas
can make the run's nouns grow exponentially.

**The verifier.** `TU/TraceUniqueP1.lean::AcceptsCanonP1 hpG sz Pb Rg c χ M tr ax r g` is the J-8 verifier `AcceptsJ8V` (§3.5) plus
the canonical-form pins (`AcceptsCanon` in `TU/StatementP1.lean`, `AcceptsCanon2` in `TU/UniqueP1.lean`, and one zero pin on the walk chip when the claim has no path reads).
The theorems instantiate it at:
- the canonical public layout `canonPb hpG (szOfClaim p) c`, with rows `rowsP1 (canonPb …)`;
- budget `0`;
- the empty registry (`VerifiedRegistry.empty.R`).

A prover tuple is `TripP1 p K δ` (trace, auxiliary columns, message). `canonOfP1 … χ` is the honest generator's tuple at coin `χ`.

**Headline** (`TU/TraceUniqueP1Closed.lean`). For `hpG : p = Nock.Atoms.p`, `hc : P1FragC c`, `hok : P1SizeOK p c`,
`h : runP1 c = some (t, c.result)`, `hcK : |K| = cK`, and every staged prover strategy `Q` (`StJ8 (fun χ => (Q χ).1)`):
- `trace_unique_prob_119`: `Pr_χ[AcceptsCanonP1 … (Q χ) ∧ Q χ ≠ canonOfP1 … χ] < 2^-119`.
- `trace_unique_prob_split`: the same probability is `≤ 2·ε + Pr_χ[¬ Good χ]`. At `|K| = cK`, `2·ε < 2^-154` (the J-8 soundness
  events, at `Q`'s trace and at the canonical one) and `Pr[¬ Good] < 2^-120` (J-8 completeness), as separate conjuncts.

**Pointwise forms:**
- `canon_eq_closed`: at a good coin outside the soundness events, a tuple accepted by `AcceptsCanonP1` is the canonical tuple.
- `trace_unique_good_final` (`TU/TraceUniqueP1.lean`): two accepted tuples at one such coin are equal, given that the second tuple's
  compute requests cover the honest reads (`hcov'`).
- `canon_complete'` (`TU/CanonSideP1.lean`): the canonical tuple is accepted at every good coin, and `Pr[¬ Good] ≤ ε_c`.

**Non-vacuity** (`Nock/RedTeam/Batch4938Thm54TUP1Toy.lean`):
- `toy_trace_unique_119`: the headline at the claim `*[[1 2] [0 2]] = 1`, with `P1FragC` and `P1SizeOK` discharged, so no
  claim-side hypothesis is left;
- `toy_trace_unique_119_cons`: the same at an autocons claim.

**Scope.**
- Ops outside `0, 7, 10` and cons, axes outside `[1, 2^61)`, atoms `≥ p`, jets, J-9 B / J-9 A / J-9 AL predicates: not covered.
- The statement is about polynomial traces chosen by a staged prover map, as in §11.1.

<sub>Sources (generated): `P1FragC` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:73; `OpsP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:61; `axesB` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:64; `genX` Nock/Edit/GenX.lean:188; `P1SizeOK` Nock/NockVMROM/Thm54/VclL/Handle/TU/ClaimSizesP1.lean:301; `runP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/ClaimSizesP1.lean:147; `Rows31` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Of.lean:970; `RootsLeafOK` Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Walk.lean:462; `AcceptsCanonP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1.lean:78; `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143; `AcceptsCanon` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:558; `AcceptsCanon2` Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueP1.lean:62; `canonPb` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:205; `rowsP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1Closed.lean:64; `R` Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean:79; `TripP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean:638; `canonOfP1` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1.lean:649; `StJ8` Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean:71; `trace_unique_prob_119` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1Closed.lean:627; `trace_unique_prob_split` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1Closed.lean:643; `canon_eq_closed` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1Closed.lean:597; `trace_unique_good_final` Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1.lean:570; `canon_complete'` Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonSideP1.lean:314; `toy_trace_unique_119` Nock/RedTeam/Batch4938Thm54TUP1Toy.lean:151; `toy_trace_unique_119_cons` Nock/RedTeam/Batch4938Thm54TUP1Toy.lean:255</sub>

## 8. The succinct layer

Paths in this section are under `nockvm-e2e/NockvmE2E/`. The layer turns the library's algebraic soundness (§4–§6: a staged
prover, ideal coins, polynomial traces) into soundness of a hash-based argument in the random-oracle model. Each step below is
a [kernel] theorem; the chain is the order in which the end-to-end theorems (§9) use them [inferred from the imports and proofs].

| step | what it adds | theorem |
|---|---|---|
| 1. RAP frame | the library's pointwise soundness (acceptance outside every bad-event summand implies `HoldsN c`) as the premise `SoundG` of a staged-RAP frame; for J-9 AL the summands are `listJ9AL` and the premise `soundJ9AL_pointwise` (§6.8), which `J9AL/GenJ9AL.lean:54` applies | `soundJ9AL_pointwise` (`Nock/NockVMROM/Thm54/VclL/Handle/J9AL/E2EJ9ALIface.lean`) |
| 2. DEEP | two appended rounds: sample `α`, commit the quotient chunks; sample `ζ`; two new summands with `epsilonOf (old ++ [s_α, s_ζ]) = ε_old + ε_α + ε_ζ` | `epsilon_deep` (`Rap/DeepSound.lean:115`), `soundG_deep` (`Rap/DeepSound.lean:160`), `certificate_deep` (`Rap/DeepCert.lean:61`) |
| 3. Round-by-round knowledge | `SoundG` plus column-locality of every summand gives a round-by-round knowledge certificate for the staged-RAP protocol, in ArkLib's fixed-round state-restoration format, hence single-salt Fiat–Shamir knowledge soundness | `rap_rbr_knowledge` (`Rap/Bridge.lean:369`), `rap_singleSalt_knowledge_soundness` (`Rap/Bridge.lean:384`) |
| 4. Commitments as a parameter | every column replaced by its commitment under a commitment scheme `CS`; with honest oracle access (`ε_CS = 0`) and the DEEP opening plan | `rap_succinct_sound` (`Succ/Statement.lean:277`), `rap_succinct_sound_deep` (`Succ/Deep.lean:142`) |
| 5. Batched FRI | the openings checked by batched FRI in one single-salt Fiat–Shamir game; committed data are words on FRI's domain read by unique decoding; ArkLib's batched-FRI soundness lifted to single-salt Fiat–Shamir | `rap_fri_sound` (`Succ/Fri.lean:259`), `rap_fri_sound_deep` (`Succ/FriDeep.lean:203`), `deep_of_inputRelation` (`Deep/UDFri.lean:43`), `batchedFri_singleSalt_soundness` (`FriPort/BatchedSoundness.lean:80`) |
| 6. Merkle (BCS) | Merkle trees on the column blocks and the FRI folds; the verifier is query-only | `merkle_singleSalt_soundness` (`Merkle/Soundness.lean:26`), `rapFri_queryOnly` (`Merkle/RapFriQueryOnly.lean:408`), `rap_fri_merkle_sound_deep` (`Merkle/E2E.lean:132`) |
| 7. Numbers | at `l = 170` queries, `θ = δ = 31/64`, rate `1/64` (`64·2^(Σs)·d ≤ 2^n`), `n ≤ 32`, `\|F\| ≥ p^3`, digests `\|Dg\| ≥ p^4`, `Q_FS, Q_H ≤ 2^64`, `V ≤ 2^32`: the bound is `≤ 2^-82` | `rap_fri_merkle_sound_deep_numbers` (`Merkle/E2E.lean:211`), `rapFriEps_le` (`Merkle/E2ENumbers.lean:120`); for every `Q`, `rapFriEps_le_Q` (§9.4) |

**Fixed columns.** The verifier-fixed columns are committed once by the indexer (`vk-setup`) and opened through a second,
side argument with its own oracle and budgets (`Q_FSf`, `Q_Hf`, `Vf`, `Pf`, `T` in §9.2); its error terms are `bfriErr`,
`mcROM` and `coll` of the headline.

**Statement binding.** Executed, not proved adaptive: `zBind` (§9.3).

**ArkLib boundary.** Used, not re-proved: Reed–Solomon codes, FRI and batched-FRI soundness, round-by-round and
state-restoration security (ArkLib at `c488a3a4`), and the single-salt Fiat–Shamir framework (the ten modules vendored in
`nockvm-e2e/vendor/arklib-fs/`). This package's: steps 1–7 above and the end-to-end theorems.

**Uniqueness (not used by the headlines).** `rap_succinct_unique` (`Ung/Positive.lean:559`) [kernel]: for a RAP with a
deterministic AIR (`AirDet`) and a unique-commitment instance, two accepted proofs of the same statement have different
projections (round-0 message and commitments) only with the stated small probability; one bound in its statement
(`Q₂ ≤ Q + (nb + 2)`) is a hypothesis, not proved.

**A code comment that disagrees.** The header of `Rap/Frame.lean` says the library "cannot be imported here" and that its
definitions are transcribed. The package does import the library (e.g. `J9AL/GenJ9AL.lean` imports
`…/Handle/J9AL/E2EJ9ALIface.lean`), and the J-9 AL headline discharges the frame premise from the library theorem (step 1)
[inferred]. Where the comment and this section differ, this section holds.

## 9. End-to-end theorems

### 9.1 Forms

All in `nockvm-e2e/NockvmE2E/`. For each family the theorems come in up to four forms with one conclusion; they differ
only in the hypothesis that names the verifier's verdict.

| family | base form: hypothesis on the base verdict | `_B`: on the binding verdict | `_S`: on the executed verdict | gate form |
|---|---|---|---|---|
| `j9al` (ALU jets) | `nock_e2e_J9AL_succinct`, `J9AL/E2ESuccinctJ9AL.lean:167`; `verdict9LV … = .ok c` | `nock_e2e_J9AL_succinct_B`, `J9AL/E2ESuccinctJ9ALB.lean:167`; `verdict9LVB … = .ok c` | `nock_e2e_J9AL_succinct_S`, `J9AL/E2ESuccinctJ9ALS.lean:168`; `verdict9LVS … = .ok c` | `exec_e2e_J9ALV`, `J9AL/E2EJ9ALV.lean:186` |
| `j9alj` (ALU + catalogue template jets) | `nock_e2e_J9ALJ_succinct`, `Z38/E2ESuccinctJ9ALJ.lean:170` | `nock_e2e_J9ALJ_succinct_B`, `Z38/E2ESuccinctJ9ALJB.lean:168` | `nock_e2e_J9ALJ_succinct_S`, `Z38/E2ESuccinctJ9ALJS.lean:168` | — |
| `j9a` (no jets) | `nock_e2e_J9A_succinct`, `J9A/E2ESuccinct.lean:174`; `verdict9V … = .ok c`; with the cost clause: `nock_e2e_J9A_succinct_SC`, `J9A/E2ESuccinctCost.lean:67` | — | — | — |

**The release headlines are the `_B` forms** [kernel]. `_B` is a corollary of the base form: `verdict9LVB` is
`verdict9LV` behind the gate `zBind XI0.pubIn z` (`J9AL/RunGate9LB.lean:17`), and `verdict9LVB_sound`
(`J9AL/RunGate9LB.lean:21`) returns both. `_S` is the form the executable meets: `verdict9LVS` (`J9AL/RunGate9LS.lean:17`)
recomputes the verification key from the loaded instance, rejects unless the vk file's root equals it, then runs
`verdict9LVB`; `verdict9LVS_sound` (`J9AL/RunGate9LS.lean:27`) turns its accept into the `_B` hypothesis. The `j9alj`
twins are `verdict9LJVB` (`Z38/RunGate9LJB.lean:17`, sound at `:21`) and `verdict9LJVS` / `verdict9LJVS_sound`
(`Z38/RunGate9LJS.lean:17`, `:27`).

The gate form `exec_e2e_J9ALV` takes the table restriction `R` as a binder pinned by its hypotheses; the headlines
construct it at the loaded instance's tables (`RJ9AL`, `J9AL/InstJ9ALW.lean:27`) [kernel].

### 9.2 The statement (j9al; j9alj is the same with `verdict9LJVB` and the catalogue)

`nock_e2e_J9AL_succinct_B` (`J9AL/E2ESuccinctJ9ALB.lean:167`) [kernel]. Given `verdict9LVB XI0 root H Hf FS FSf z0 π0 πF0 = .ok c`:

1. the loaded instance passes the shape gates and the chip gate (`shapeOkF`, `shapeXOkF`, `chipsOkF famJ9AL (XI170 XI0) = true`),
   and there is a datum `d` (`DatumOK9AL d`) linked to it (`Link9L`) with `d.c = c`: the claim the verifier prints is the
   datum's claim;
2. for every adversary `Aon` (an oracle computation against the two random oracles, main and side), every query budget
   with `Q_FS ≤ 2^64`, `Q_H ≤ 2^64`, `V ≤ 2^32` on the main proof and `Q_FSf, Q_Hf, Vf, Pf, T` on the side proof, and the
   named hypotheses `hnum : SideNums …` (side numerics, including `1 ≤ k`) and `hTb` (`T` bounds the side-VK size),

   `Pr[ verifyOnline' accepts the adversary's output ∧ ¬ Nock.Jet.HoldsN c ] ≤ 2^-82 + (bfriErr + mcROM + coll)`,

   where `bfriErr` is the side proof's batched-FRI error at budget `Q_FSf`, `mcROM` the Merkle multi-checkpoint term and
   `coll` the collision term `(Q_Hf + Vf + T)² / (2·|Dg|)` (the conclusion is at `:226–:231`; `HoldsN` is `Nock.Jet.HoldsN`, `:226`).

Scope stated in the docstring and in the binders: non-adaptive (the claim and public input are fixed before the oracle);
random-oracle model; preprocessing verifier with the honest verification key; not zero-knowledge; template jets excluded
in `j9al`.

### 9.3 Statement binding (`zBind`)

`zBind p z := z.take (zHdr p).length == zHdr p` (`Exec/ZBind.lean:193`), with `zHdr p = tagZ :: encPub p`
(`:190`; `tagZ` is the domain tag `"ZB"`, `encPub` an injective prefix-free encoding of the public input). So a proof's
Fiat–Shamir statement `z` must start with the encoding of the public input it is checked against, and `zBind_inj`
(`Exec/ZBind.lean:254`) [kernel] shows that one `z` binds at most one public input. The theorems remain non-adaptive:
binding is executed, and no theorem bounds an adversary that chooses the public input after querying the oracle.

The jet-free `j9a` path has no binding gate: `verify --family j9a --vk` runs `verdict9VS` (`J9A/RunGate9VS.lean:17`),
which does not call `zBind` [inferred from the source].

### 9.4 The numbers

- `nock_e2e_J9AL_numbers` (`J9AL/E2ESuccinctNumJ9AL.lean:24`) [kernel]: at `Q_FSf, Q_Hf ≤ 2^64`, `Vf ≤ 2^32`, `T ≤ 2^40`
  (and `m + 1 ≤ 2^12`), the headline's right-hand side is at most `2^-82 + (2^-83 + 2^-120)`, i.e. about `2^-81.4`.
- `rapFriEps_le_Q` (`Merkle/E2ENumbersQ.lean:45`) [kernel]: the main-proof numbers term `rapFriEps` as a function of the
  Fiat–Shamir query budget `Q`, with the hypothesis `Q ≤ 2^64` of `rapFriEps_le` (`Merkle/E2ENumbers.lean:120`) dropped:
  for every `Q`, `rapFriEps … Q ≤ Q·2^-147 + (2^-144 + 2^-146)`. At `Q = 2^64` this is below `2^-82`, the constant term of
  the headline. It is a stand-alone corollary: no headline uses it, and the headlines keep their `Q ≤ 2^64` budget
  [inferred: only the package root `NockvmE2E.lean:23` imports `E2ENumbersQ`]. Two declarations are named `rapFriEps`
  (`Merkle/E2ENumbers.lean:104`, `Merkle/RapFriQueryOnly.lean:516`); this one is the first.

### 9.5 Non-vacuity

At the executed `add` instance (`addALR`, the fixture of §3.8) every binder of the `j9al` headline is inhabited:
`binders_add_indep` (`J9AL/E2ESuccinctNonVacL.lean:321`) and `binders_add_dep` (`J9AL/E2ESuccinctNonVacL.lean:354`), with the
side numerics `sideNums_add` (`J9AL/E2ESuccinctNonVacL.lean:102`), the main-tree budgets `main_budgets_add`
(`J9AL/E2ESuccinctNonVacL.lean:280`) and the side-VK bound `vk_total_add` (`J9AL/E2ESuccinctNonVacL.lean:98`) [kernel]. The `j9alj`
headline has the same package at the program `jp`: `binders_jp_indep` (`Z38/E2ESuccinctNonVacLJ.lean:323`), `binders_jp_dep`
(`Z38/E2ESuccinctNonVacLJ.lean:356`) [kernel]. The instance sizes are kernel facts too: `add_nD`, `add_nc`, `add_k`
(`J9AL/E2ESuccinctNonVacL.lean:68`–`71`: `nD = 13`, `1219` columns, `k = 6`) and `jp_nD`, `jp_nc`, `jp_k`
(`Z38/E2ESuccinctNonVacLJ.lean:70`–`73`: `14`, `1302`, `7`).
## 10. Executables

All built from `nockvm-e2e/lakefile.toml`; run from `nockvm-e2e/`.

### 10.1 Covered and uncovered accepts

An accept is **covered** when an end-to-end theorem has the executed verdict as its hypothesis.

| command | verdict run | prints | covered by |
|---|---|---|---|
| `nockvm-e2e-verify-cert verify --family j9al --vk V I P F` | `verifyBytesL` (`Exec/CertBytes.lean:86`) | `ACCEPT claim …` | `verifyBytesL_sound` (`Exec/CertSound.lean:166`) [kernel] |
| `nockvm-e2e-verify-cert verify --family j9alj --vk V I P F` | `verifyBytesLJ` (`Exec/CertBytes.lean:91`) | `ACCEPT claim …` | `verifyBytesLJ_sound` (`Exec/CertSound.lean:242`) [kernel] |
| `nockvm-e2e-verify-fam verify --family j9al --vk V I P F` | `verdict9LVS` (arm at `Exec/VerifyFamMain.lean:324`) | `ACCEPT claim …` | `nock_e2e_J9AL_succinct_S` [kernel] + compiled code [trusted] |
| `nockvm-e2e-verify-fam verify --family j9alj --vk V I P F` | `verdict9LJVS` (`:368`) | `ACCEPT claim …` | `nock_e2e_J9ALJ_succinct_S` [kernel] + compiled code [trusted] |
| `nockvm-e2e-verify-fam verify --family j9a --vk V I P F` | `verdict9VS` (`:281`) | `ACCEPT claim …` | `nock_e2e_J9A_succinct` via `verdict9VS_sound` (`J9A/RunGate9VS.lean:25`) [kernel]; no `zBind` (§9.3) |
| `nockvm-e2e-verify-fam verify --family j8\|j9a\|j9al\|j9alj I P` (no `--vk`) | `verifyFlatE`, `verdict9`, `verdict9L`, `verdict9LJ` (`:169`) | `ACCEPT-UNCOVERED claim …`; for `j8` `ACCEPT-UNCOVERED (famGates j8 …)` (`:203`) | none |
| `nockvm-e2e-verify-fam verify-online --family j9a\|j9alj VK PUB P F` | online verdicts (`:257`, `:405`) | `ACCEPT-UNCOVERED claim …` | none; the VK file is trusted |
| `nockvm-e2e-verify-fam gates --family F I` | the family's shape gates only (`:163`) | `famGates F: all … gates pass` | none (no claim is verified) |

Every `ACCEPT-UNCOVERED` line ends with "no end-to-end theorem covers this command; use verify --vk or
nockvm-e2e-verify-cert" (`Exec/VerifyFamMain.lean:185`, `:191`, `:197`, `:203`, `:279`, `:427`) [executed source].
No mode prints `GATES-OK`.

### 10.2 The certified verifier

`nockvm-e2e-verify-cert`'s `main` (`Exec/VerifyCertMain.lean:12`) reads the vk, instance, proof and fix files and the chip
documents the instance names (via the pure `chipPaths`, `Exec/CertBytes.lean:67`), passes the bytes to the pure
`verifyReport` (`:129`), prints its line and exits with its code. Kernel facts:

- `verifyReport_ok` (`Exec/CertReport.lean:10`): exit code 0 implies `verifyBytesL … = .ok c` (family `j9al`) or
  `verifyBytesLJ … = .ok c` (family `j9alj`);
- `verifyBytesL_sound` (`Exec/CertSound.lean:166`) / `verifyBytesLJ_sound` (`Exec/CertSound.lean:242`): `.ok c` implies the bytes parse
  (`parseInputs`, `Exec/CertBytes.lean:72`) to some `XI0, root, z, π, πF`, the executed verdict `verdict9LVS` /
  `verdict9LJVS` is `.ok c` on them at the executable's Tip5 oracles, and the conclusion of the `_S` headline holds at
  `XI0`.

No parser correctness is needed: the theorem holds for whatever `parseInputs` returns, so a misparse can make the
executable prove a different statement, never a false one; the instance the bytes parse to is the statement
[kernel + inferred]. Trusted base of this executable: `main`'s file I/O, the Lean compiler and runtime, the C toolchain
[trusted]; reproducible build: `nockvm-e2e/scripts/build-certified.sh`.

Two code comments disagree with this section, which holds: the header of `Exec/VerifyCertMain.lean` cites `CertSoundL.lean` and `CertSoundLJ.lean`, where both theorems are in
`Exec/CertSound.lean`; and the error text of `nockvm-e2e-verify-fam` for an unknown family lists `(j8 | j9a)`, while the
executable also accepts `j9al` and `j9alj` (see `famOf?` at `Exec/VerifyFamMain.lean:60`).

### 10.3 Proving and setup

`nockvm-e2e-verify-fam vk-setup` writes the verification key (fixed columns and a Tip5 Merkle root; deterministic, no
secret); `fix-prove` writes the fixed-column proof; `index` writes the stripped public instance for `verify-online`;
`nockvm-e2e-j9al-prove` produces proofs; `nockvm-e2e-j9alemit2` emits traces, chip documents and instances. All untrusted:
nothing they output is trusted by a covered accept [inferred from §10.1–10.2].

### 10.4 Scripts

- `nockvm-e2e/scripts/run-free.sh LABEL --subject S --formula F [--prims id:op,…] [--fuel N]`: the whole chain (emit, prove,
  vk-setup, fix-prove, `verify --vk`) on a user's Nock program, family `j9al`. Exit 0 = ACCEPT; 3 = a side condition or a
  missing chip literal reported before proving.
- `scripts/bench.sh <runs> <outdir> …`: wall time and peak RSS of prove, vk-setup, fix-prove and verify for `add` (`j9al`)
  and `jp` (`j9alj`), and proof/VK sizes; writes `header.txt`, `results.csv`, `sizes.csv` [executed when run].
- `scripts/demo-candidate.sh`: the library demo (honest, tampered and false runs; jetted matmul; big atoms; six
  end-to-end programs) [executed when run].
- `nockvm-e2e/scripts/build-certified.sh <outdir>`: reproducible build and hashes of the certified verifier.

## 11. Trusted base, scope and axioms

### 11.1 Scope and assumptions of the library (J-8, J-9 B)

Covered:
- Every Nock claim over unbounded atoms, ops 0–11, any formula that is a cell; jets through a faithful registry.
  Big atoms (`≥ p`) occur in the computation (op 4 carries, op 5 comparisons, cells holding big atoms); under
  `AcceptsJ8V` the claim's own atoms are `< p` (`hclA`), under `AcceptsJ9V` they may be big.
- The statement is about `evalN`, not about a field-reduced semantics.

Not covered:
- **Commitments.** The theorems are stated over polynomial traces chosen by a staged prover map `Q`; no polynomial
  commitment scheme, low-degree test or query phase is modelled.
- **Fiat–Shamir.** The transcript is executable code with the order receipt of §3.7.1; its security rests on the named
  random-oracle assumption on `Tip5.hashVarlen`, which no theorem states.
- **Demo verdicts.** The command-line checker runs compiled code; `checkJ8_iff` relates the Lean function `checkJ8` to
  `AcceptsJ8V`, and the native executable's agreement with that function is not kernel-checked.
- **Field.** Soundness is proved at Goldilocks (`hpG`) with `|K| = p^3` (`hcK`).
- **Size.** Soundness holds for budgets `RowsLe r cornerC` (tables `≤ 2^31` rows, `≤ 2·fuelChip` claim leaves),
  `≤ 2^31` registered ids, census `≤ 2^31` nouns. Completeness additionally needs the binders of §4.3 (formula axes
  `< p`, path depth `≤ 61`, `≤ 2^109` leaves per walked root, jet ids and called-template axes `< p`).
  In practice: every op-0 / op-9 read axis in the run must be `< 2^62` (path depth `≤ 61`), and op-10 edit axes `< p`;
  an op-5 whose compared nouns first differ at tree depth `≥ 64` is outside completeness (soundness is unaffected).
  **(informal)** Programs produced by ordinary compilers use small axes; deep structural comparisons are the case to watch.
- **Jets.** Soundness assumes `Rg.Faithful` (discharged for `VerifiedRegistry`); the J chip interprets only compiled
  `Tpl` templates (`hTpl`).

The package `nockvm-e2e/` models commitments and Fiat–Shamir for its own J-9 A, J-9 AL and `j9alj` verifiers (§8–§10).
Nothing in §1–§7 depends on it.

<sub>Sources (generated): `AcceptsJ8V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean:143; `AcceptsJ9V` Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9V.lean:98; `evalN` Nock/Reference.lean:75; `hashVarlen` Nock/Driver/Tip5.lean:164, nockvm-e2e/NockvmE2E/Exec/Tip5.lean:156 (several); `checkJ8_iff` Nock/V1J8/CheckJ8.lean:490; `checkJ8` Nock/V1J8/CheckJ8.lean:391; `RowsLe` Nock/NockVMROM/Thm54/VclL/Handle/WeightsJ8.lean:660; `Faithful` Nock/Jet/Semantics.lean:106, Nock/Jet/Semantics.lean:114, Nock/Jet/Semantics.lean:117 (several); `VerifiedRegistry` Nock/Jet/VerifiedRegistry.lean:22; `Tpl` Nock/Jet/Autogen.lean:107</sub>

### 11.2 Axioms

The `#print axioms` lines of the headline declarations (`docs/gen/headlines.txt`) are in `docs/THEOREMS.md`, which labels each line with its source: two builds of the end-to-end package from these Lean sources (E, L), and the output of `scripts/delivery-axioms.lean` recorded in `README.md` for these library sources (R; not re-run by the release gate, since the package build does not print the library headlines). Every headline has a recorded line except `Nock.Jet.HoldsN`, a definition (the target predicate). The other declarations this document cites are supporting lemmas and definitions. Most of them have no recorded line: they are listed, with their kind, in `docs/theorems-unrecorded.tsv`, and the counts are in the header of `docs/THEOREMS.md` (both generated). These sources record no `#print axioms` line for them, and this documentation claims none. In every recorded line only `propext`, `Classical.choice` and `Quot.sound` occur (`pub_before_first_squeeze` uses only `propext` and `Quot.sound`); no recorded line mentions `sorryAx` or `Lean.ofReduceBool`.

<sub>Sources (generated): `pub_before_first_squeeze` Nock/DriverJ8/TranscriptJ8.lean:85</sub>

### 11.3 Trusted base and gaps of the end-to-end package

The trusted base of an ACCEPT (rows marked kernel-checked, checked at run time, or trusted) and the stated gaps are
`docs/LIMITS.md`. In short: the Lean kernel; the Lean compiler and runtime and the C toolchain (for `nockvm-e2e-verify-cert`
only those and `main`'s file I/O, §10.2); the random-oracle model with the package's own Tip5; the query budgets and the
named hypotheses `hnum`, `hTb`; the non-adaptive scope. Gaps: template jets outside `catJ`, zero-knowledge, adaptive
adversaries, a cost clause for J-9 AL, end-to-end completeness, Tip5 equivalence with a deployed hash, and the query
positions (each within statistical distance `2^-64` of uniform; no theorem bounds the effect).

<sub>Sources (generated): `catJ` Nock/RedTeam/Batch4939Thm54J9ALTplJetToy.lean:65, nockvm-e2e/NockvmE2E/Z38/CatJ.lean:48 (several)</sub>

## 12. The preprint and the essay

This document follows the Lean source at the release commit. Where the preprint or the essay states a number, a name, a
hypothesis or a scope differently, the source holds.
