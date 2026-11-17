# nockvm-e2e

Kernel-checked soundness of a succinct (FRI-based STARK) verifier for full Nock with primitive jets (big-atom arithmetic on
the ALU chip). The specification of everything below is `../docs/SPEC.md` §8–§10.
**Not zero-knowledge.** Lean 4.35 kernel checks only; no other proof checker has been run on this package.

This is a Lake package on Lean v4.35.0 and Mathlib. It requires the NockVM library (the parent directory, Lake package `nock`) and ArkLib (FRI and Fiat–Shamir state-restoration results). Its namespace is `NockvmE2E`.
License: Apache-2.0 (see `LICENSE`).

## What is proved

| Theorem | File:line |
|---|---|
| `nock_e2e_J9AL_succinct_B` (release headline, primitive jets) | `NockvmE2E/J9AL/E2ESuccinctJ9ALB.lean:167` |
| `nock_e2e_J9ALJ_succinct_B` (release headline, primitive jets plus template jets from the checked registry `catJ`) | `NockvmE2E/Z38/E2ESuccinctJ9ALJB.lean:168` |
| `nock_e2e_J9AL_succinct` (base form; the `_B` headline is its corollary) | `NockvmE2E/J9AL/E2ESuccinctJ9AL.lean:167` |
| `nock_e2e_J9ALJ_succinct` (template-jet twin of the above) | `NockvmE2E/Z38/E2ESuccinctJ9ALJ.lean:170` |
| `nock_e2e_J9AL_numbers` (numeric corollary) | `NockvmE2E/J9AL/E2ESuccinctNumJ9AL.lean:24` |
| `nock_e2e_J9A_succinct` (jet-free twin; with a cost clause: `nock_e2e_J9A_succinct_SC`, `NockvmE2E/J9A/E2ESuccinctCost.lean:67`) | `NockvmE2E/J9A/E2ESuccinct.lean:174` |

**Statement of the headline.** For a claim `c` about a Nock program with ALU big-atom jets (and, for `j9alj`, template jets
over the fixed catalogue `catJ`) and a public input fixed before the oracle, every adversary within the stated query budgets has
Pr[the verifier accepts `c` and `c` is false] ≤ 2^-82 + (bfriErr + mcROM + coll),
where the verifier is the Lean verifier (`nockvm-e2e-verify-fam verify --family j9al --vk ...`, or `--family j9alj` for programs
that call template jets).
The proof goes through ArkLib's FRI and Fiat–Shamir state-restoration results. The ALU jets covered are the big-atom
add, sub, lt, mul, div and mod.

**The release headlines are the `_B` forms.** The executable's verify arms call the binding verdicts, not the base verdicts:
`verdict9LVB` (`--family j9al`) and `verdict9LJVB` (`--family j9alj`); `verify-online --family j9alj` runs `verdict9LJVOB`, which no end-to-end
theorem covers (it prints `ACCEPT-UNCOVERED`, see below). Each is the base verdict (`verdict9LV`, `verdict9LJV`, `verdict9LJVO`) behind the gate `zBind pubIn z`, which checks that the Fiat–Shamir
statement `z` starts with `zHdr pubIn`. `nock_e2e_J9AL_succinct_B` and `nock_e2e_J9ALJ_succinct_B` take `verdict9LVB ... = .ok c` and
`verdict9LJVB ... = .ok c` as their hypotheses; they are corollaries of the base headlines. The `verify` arms run them behind one more
check: `verdict9LVS` / `verdict9LJVS` recompute the verification key from the loaded instance and reject unless the vk file's root equals
it; `verdict9LVS_sound` / `verdict9LJVS_sound` turn an accept into the `_B` hypothesis, and `nock_e2e_J9AL_succinct_S` /
`nock_e2e_J9ALJ_succinct_S` state the headlines at these executed verdicts directly (same conclusion).

**Non-vacuity.** At an executed `add` program every binder of the headline is inhabited; the binders of the template-jet headline
are likewise inhabited at the program `jp` (one template-jet call plus one big-atom `add`). Proofs for the `add`, `mul` and `jp`
programs are produced and accepted; tampered proofs and tampered keys are rejected.

## Assumptions and limits

- Not zero-knowledge: the prover is Reed–Solomon plus FRI with no masking.
- Random-oracle model, with Tip5 as the oracle.
- Non-adaptive theorem; statement-binding verifier. The executed verifier binds the full public input into the Fiat–Shamir
  transcript: a proof verifies only for the public input it was produced for. The kernel-checked soundness theorem is still
  stated for a public input fixed before the oracle. The adaptive version, where the prover may choose the public input after
  oracle access, is not yet proved.
- The jet-free path `verify --family j9a --vk` is covered (`nock_e2e_J9A_succinct`) but runs no `zBind`: it does not bind the
  public input.
- Verification key: `verify --vk` recomputes it from the instance and rejects unless the vk file matches; `verify-online` trusts the vk
  file (reproducible and transparent: re-run `index` / `vk-setup` and compare). The verifier is a preprocessing verifier.
- Chip files: untrusted input; the verifier accepts only chips equal to kernel-tied Lean literals (no generic emitter theorem: a
  table size with no literal is rejected).
- Certified verifier `nockvm-e2e-verify-cert`: its `main` only reads files and prints a pure function of their bytes
  (`Exec/CertBytes.lean`); `verifyBytesL_sound` / `verifyBytesLJ_sound` (`Exec/CertSound.lean`) turn its ACCEPT into the headline
  conclusion for the instance those bytes parse to. The trusted base for that executable is: main's file I/O, the Lean compiler and runtime,
  and the C toolchain (`CERTIFIED.md`, `scripts/build-certified.sh`). The parser and loader are not trusted.
  For the other executables the verdict is trusted from the Lean compiler and runtime (compiled code, not a kernel fact).
- The shape gate and `setupGates` are executed checks, not kernel facts.
- The named hypotheses `hnum` (side numerics, including `1 ≤ k`) and `hTb` (the side-VK size bound).

**Not covered:** template jets outside the fixed catalogue `catJ`; a cost clause for the J-9 AL headline; zero-knowledge; adaptive adversaries; completeness as an
end-to-end headline; the trusted base of the underlying NockVM library.

Details are in `../docs/LIMITS.md`.

## Source layout

Under `NockvmE2E/`: `FriPort` (ArkLib's FRI lifted to single-salt Fiat–Shamir, batched), `Lift` and `Spike` (embedding legacy
protocols into the fixed-round state-restoration format), `Deep`, `Rap`, `Merkle`, `Succ` (the succinct layer), `J8`, `J9A`,
`J9AL` (per-family end-to-end theorems), `Z38` (the `j9alj` template-jet twins of the `J9AL` files; the name is a sequence label),
`Ung` (ungrindability: `rap_succinct_unique` and its premises), `Emit` (chip emitter specs), `Exec` (the executables, the
generated instances and the chip literals).

## ArkLib and attribution

This package builds on [ArkLib](https://github.com/Verified-zkEVM/ArkLib) (Apache-2.0) at upstream main c488a3a4, fetched
from GitHub. Ten ArkLib modules of upstream pull requests #1280 (head 3444c2f7) and #1282 (head 89433a85) by Quang Dao, which
this package imports and which are not on upstream main (both pull requests were closed on GitHub without being merged), are
vendored in `vendor/arklib-fs/` (a small Lake package) with their own Apache-2.0 headers and ArkLib's `LICENSE`. Their content
is unchanged except that the module names are moved from `ArkLib.*` to `ArkLibFs.*` (Lake would otherwise look for them in
the ArkLib package); declaration names and proofs are as upstream, and each file carries a modification notice.
There is no other ArkLib-side change.

- ArkLib's work (used, not re-proved): Reed–Solomon codes, FRI and batched-FRI soundness, round-by-round and
  state-restoration security; the single-salt Fiat–Shamir framework (from #1280/#1282).
- Ours: `NockvmE2E/FriPort` lifts ArkLib's FRI soundness to single-salt Fiat–Shamir soundness of our batched FRI
  (`batchedFri_singleSalt_soundness`); `NockvmE2E/Lift`, `Deep`, `Rap`, `Merkle`, `Succ` and the end-to-end theorems.

Full text in `NOTICE`.

## Build

```
lake build NockvmE2E            # the library: every theorem above
lake build nockvm-e2e-verify-cert nockvm-e2e-verify-fam nockvm-e2e-prove nockvm-e2e-verify nockvm-e2e-j9al-prove nockvm-e2e-j9alemit2 \
           nockvm-e2e-genal nockvm-e2e-vkspec nockvm-e2e-vkregress nockvm-e2e-j9aemit \
           nockvm-e2e-t5bench nockvm-e2e-t5bench-base   # the executables
```

A full build compiles several hundred modules. Measured: the from-source build of the library and executables peaked at 20.0 GB
(systemd scope `memory.peak`, which includes page cache; 2 Lean threads), and single headline modules take about 9 to 10 GB.

## Running the fixtures

The chip documents in `chipdocs/` carry the prefix of the label that introduced the chip (`j8_`, `j9a_`); the `j9al` and `j9alj`
families use all of them. The fixtures `fixtures/j9al-add/` and `fixtures/j9alj-jp/` hold the instance, the chip documents, the coins, a proof and its
fixed-column proof for an `add` program (family `j9al`) and for `jp`, one template-jet call plus one big-atom `add` (family `j9alj`).
`SHA256SUMS` in each lists the files. Each instance names its chip files as `out3/<prog>/<file>`, relative to the working directory.
From `nockvm-e2e/`, the `add` program:

```
V=.lake/build/bin/nockvm-e2e-verify-fam
F=fixtures/j9al-add
mkdir -p out3 && ln -sfn ../$F out3/add   # the instance names its chip files as out3/add/<file>
$V vk-setup  --family j9al $F/add.inst.json add.vk.json
$V fix-prove --family j9al $F/add.inst.json $F/add.proof.json add.fix.json
$V verify    --family j9al --vk add.vk.json $F/add.inst.json $F/add.proof.json add.fix.json
```

and the `jp` program:

```
V=.lake/build/bin/nockvm-e2e-verify-fam
F=fixtures/j9alj-jp
mkdir -p out3 && ln -sfn ../$F out3/jp    # the instance names its chip files as out3/jp/<file>
$V vk-setup  --family j9alj $F/jp.inst.json jp.vk.json
$V verify    --family j9alj --vk jp.vk.json $F/jp.inst.json $F/jp.proof.json $F/jp.fix.json
```

`vk-setup` runs the setup gates and writes the verification key; `fix-prove` produces the fixed-column proof; `verify`
recomputes the verification key from the instance (rejecting `vk root differs from setup` if the vk file does not match) and runs the
binding verdict (`verdict9LVB` for `j9al`, `verdict9LJVB` for `j9alj`), the verdict that the `_B` headline's hypothesis refers to,
and prints `ACCEPT claim ...` or `REJECT: ...`. The proofs in the fixtures bind the public input (`z` starts with
`zHdr pubIn`); a proof whose statement does not is rejected with `z does not bind pubIn (zBind)`.
`nockvm-e2e-j9al-prove` produces new proofs (slow; run with ample memory).

The certified verifier takes the same arguments (`verify --family j9al|j9alj --vk <vk> <inst> <proof> <fix>`) and prints the same
`ACCEPT claim ...` / `REJECT: ...` (no timing): `F=fixtures/j9al-add; .lake/build/bin/nockvm-e2e-verify-cert verify --family j9al --vk add.vk.json $F/add.inst.json $F/add.proof.json add.fix.json`.
Build it reproducibly with `bash scripts/build-certified.sh <outdir>`.

**Covered and uncovered verdicts.** Only `verify --family j9a|j9al|j9alj --vk ...` and `nockvm-e2e-verify-cert` print `ACCEPT`: an end-to-end
theorem covers them (`nock_e2e_J9A_succinct`, `nock_e2e_J9AL_succinct_S`, `nock_e2e_J9ALJ_succinct_S`; for verify-cert also `verifyBytesL_sound` /
`verifyBytesLJ_sound`). The other accepting arms of `nockvm-e2e-verify-fam` (`verify` without `--vk`, `verify-online`, and the J-8 arm) print
`ACCEPT-UNCOVERED`: they are useful checks, but no end-to-end theorem covers their accept.

## Running an arbitrary program
One command runs the whole chain (emit, prove, vk-setup, fix-prove, verify) on a Nock program of your own, family `j9al`:

```
lake build nockvm-e2e-verify-fam nockvm-e2e-j9alemit2 nockvm-e2e-j9al-prove
scripts/run-free.sh LABEL --subject S --formula F [--prims id:op,...] [--fuel N]
```

Worked example (executed; verify ACCEPT in 91 s total, peak RSS 187 MB):

```
scripts/run-free.sh ex1 --subject "[41 7]" --formula "[[4 [0 2]] [4 [4 [0 3]]]]"
# ACCEPT claim [[41 7] [[4 [0 2]] [4 [4 [0 3]]]] [42 9]] (online, VK; famGates j9al; ...)
```

Rejected input: `--subject "[41 7"` gives `ERROR: --subject: cannot parse '[41 7': unclosed '[': missing ']' at the end of the input (after 5 characters)`.
A crashing program (`--subject "[5 5]" --formula "[2 [0 1] [1 [4 [0 1]]]]"`) gives `ERROR: LABEL: the Nock run did not finish (crash, or more than fuel 1000 steps; try --fuel N with a larger N)`.

Jet example (executed; `--print-primc add` gives the primitive's formula; a jet call is `[11 [%wild [1 id]] body]`, and
`%wild` is the atom `1684826487`; verify ACCEPT; on an Apple-silicon Mac the five steps were run by hand, 107 s in
total, because of the macOS note below):

```
scripts/run-free.sh ex2 --subject "[4294967301 4294967303]" --prims 7:add --fuel 2 \
  --formula "[11 [1684826487 [1 7]] $(nockvm-e2e-j9alemit2 --print-primc add)]"
# ACCEPT claim [[4294967301 4294967303] [11 [[1684826487 [1 7]] [6 ...]]] 8589934604] (online, VK; famGates j9al; ...)
```

On macOS `nockvm-e2e-j9al-prove` writes every output and then exits 1, because its peak-memory report reads
`/proc/self/status`; `run-free.sh` stops there. The exit code then says nothing about the proof: the prover's own
verdict line is not printed either. Check that the outputs were written and run the remaining steps (vk-setup,
fix-prove, verify) by hand.

Chip-literal error (executed): `kroots` = number of distinct subjects read at axis ≥ 2; `--subject "[4 5]" --formula "[7 [[0 3] [0 2]] [0 2]]"`
reads in two subjects, so `kroots` 2, which has no literal:
`ERROR: kr2: CHIP-LITERAL MISSING: table W (walk, kroots) (walkChipJ8) needs numeral 2 but the verifier's literal list has only [1, 9, 25, 42, 48, 174, 3]; the verifier will REJECT ...`.
The check mirrors `BndJ9AL.numOkB` (numeral in `lits`, and for walk tables numeral ≤ rows; split table `A.n` when present).
`--allow-unverifiable` (emit and prove) downgrades the chip-literal errors to WARNINGs so that the verifier's REJECT can be observed.
Executed on that program: `scripts/run-free.sh kr2f --subject "[4 5]" --formula "[7 [[0 3] [0 2]] [0 2]]" --allow-unverifiable` prints both WARNINGs, then the
prover's in-process verifier says `verifyFlatE (in-process): REJECT (DeepCheck fails)` and the script exits 1 (no ACCEPT; the standalone verify-fam step is not reached).

- `S` and `F` are noun text: decimal atoms, cells `[a b]`, `[a b c]` = `[a [b c]]`. Malformed input is rejected with a message
  giving the character position (`unclosed '['`, `a cell needs at least two elements`, `trailing input after the noun`, ...).
- `--prims 7:add,8:mul` registers primitive jets (ops `add sub lt mul div mod`; `dec` is refused) at the given ids; `--fuel` (default 1000)
  bounds the Nock run. `nockvm-e2e-j9alemit2 --print-primc add` prints the formula of a primitive, for building
  `[11 [1684826487 [1 7]] <primC add>]` (`%wild`, key 7) as in the built-in `add` program.
- `LABEL` names the output files (`$WORK/LABEL/...`). The built-in names `add mul toy absent jp` work without `--subject`.
- The same flags work directly on `nockvm-e2e-j9alemit2 OUT ... LABEL` and `nockvm-e2e-j9al-prove [flags] DOCS LABEL OUT`
  (`DOCS` = `chipdocs/` plus the `j9al_aluChipJ9.json` the emitter writes; `run-free.sh` assembles it).

Errors reported before anything is proved (exit 3, nothing written): prim `dec`; duplicate prim ids; the Nock run crashes or exceeds fuel;
generator returns none; a table with ≥ 2^31 rows (`h31A`/`h31L`); a primitive operand of more than 62 limbs of 2^32 or not an atom
(`PrimLimbs62`); and **missing chip literals (`../docs/LIMITS.md`, end-to-end row 7)**: the walk chip of table W needs `kroots` in `{1,3,9,25,42,48,174}` and
table V `krootsV` in `{1,2}` (`famJ9AL.lits`). If the program's run needs another numeral the front end prints
`CHIP-LITERAL MISSING: table ... needs numeral k ... the verifier will REJECT` and stops (also when `kroots` exceeds the W rows). Emitting the Lean literal and its `tie_*`
theorem for a new numeral is not automated (`Exec/J9ALChipsK_*` shows the shape); the shipped literal list is fixed.

## Axiom check

1,763 declarations of the package have a `#print axioms` line (not every theorem does), so a build prints one
`depends on axioms` line for each. Each printed line must be a subset of `[propext, Classical.choice, Quot.sound]`; none may mention `sorryAx`. The package
declares no axioms of its own and uses no `native_decide`.
To check one headline: add `#print axioms nock_e2e_J9AL_succinct` to a scratch file that imports
`NockvmE2E.J9AL.E2ESuccinctJ9AL`.
