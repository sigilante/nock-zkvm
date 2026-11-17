import Lean.Data.Json
import Nock.V1J9AL.GenJ9ALXJ
import Nock.V1J9A.GenJ9AX
import Nock.V1J9.GenJ9
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

/-!
  TraceDemo/J9ALEmit.lean

  `nockvm-j9alemit [OUTDIR] [prog]` (`prog` = `toy` | `absent` | `corner-t1` | `corner-t5`) generates the J-9 AL instance
  (`genJ9ALXJ`, registry `fun _ => none`, EMPTY primitive table, fuel 1000, coins `Gen.prngCoins 1` — a PRNG, NOT
  Fiat–Shamir), checks it with `checkJ9ALX` (stderr: verdict; exit 1 and NOTHING written if not `true`) and writes, as
  `J9AEmit` does, `OUTDIR/traces/trace-<prog>/<id>.trace.json` for the J-9 A chips plus `aluChipJ9.trace.json` when
  `I.aluOn` (`main` = base columns 0..93, `aux_r1` = 9 `K6` = 18 extension columns, `aux_r2` = 8 `K6` = 16, three limbs
  each; width 196 = `aluSZ_width_eq`; `public_flat` = `pubsL` = `pubALv/pubALs/pubALx`, six `K3`), `coins.json`, and
  `pubeq.json` with the J-9 A fields plus `pubsL`, `prims` and `check_pub_ok` = `checkPubJ9ALE`.
  The primitive table is empty by default (so `aluOn = false`, no `aluChipJ9` trace).  Each `prims` entry of
  `pubeq.json` carries `code` = `RealIOJ9AL.primCode` of the op (add 1, sub 2, lt 3, dec 0, mul 4, div 5, mod 6).
  Optional prims mode (third CLI argument `add` | `mul`; default unchanged): the program is the J-9 AL toy
  `*[[a b] [11 [%wild [1 7]] (primC op]]` over `addPrims empty [(7, op)]` (`add`: a = p+5, b = p+7, as `Batch4936`'s toy;
  `mul`: a = 2^70+3, b = 2^65+11, three limbs, as `Batch4932`'s demo), written to `trace-<prog>` with `prog` =
  `prim-add` / `prim-mul`, so the ALU chip is on and `aluChipJ9.trace.json` is emitted.
  Executable evidence only; this file is unverified glue, not kernel-checked.
-/

-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml

open Lean Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX Nock.V1J8.Exe System
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.GenJ9ALXJ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.V1J8.MemX (checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAWOK checkAtomHQL)

def rspP : ℕ → Noun
  | 0 => .atom 0
  | n+1 => .cell (.atom 0) (rspP n)

/-- `toy` = Batch4883 `*[sA [[0 AB] [0 AF]]]` (restated literally). -/
def toyS : Noun := rspP 63
def toyF : Noun := .cell (.cell (.atom 0) (.atom (2 ^ 64 - 1))) (.cell (.atom 0) (.atom (2 ^ 63 - 1)))
/-- `absent` = `*[[(p+5) 0] [0 2]]` (chips axis/split off). -/
def absS : Noun := .cell (.atom (Nock.Field.p + 5)) (.atom 0)
def absF : Noun := .cell (.atom 0) (.atom 2)

/-! Corner programs (FC-B G2), `uv wv f3 fCorner fForced` copied verbatim from
  the J-9 B corner corpus (`Bn := Nock.Atoms.B`, `P := Nock.Field.p`). -/
def Bn : ℕ := Nock.Atoms.B
abbrev Pc : ℕ := Nock.Field.p   -- = `Nock.V1J8.Gen.P` (abbrev of `Nock.Field.p`)
def uv : ℕ := (Bn - 1) + 1 * Bn + (Bn - 1) * Bn * Bn          -- [B-1, 1, B-1]
def wv : ℕ := (Bn - 1) + 0 * Bn + (Bn - 1) * Bn * Bn          -- [B-1, 0, B-1]: w+1 = [0, 1, B-1], carries INTO comb p
def f3 : Noun := .cell (.atom 4) (.cell (.atom 4) (.cell (.atom 1) (.atom (Pc - 1))))   -- p-1 -> p -> p+1
def fCorner : Noun := .cell f3 (.cell (.atom 4) (.cell (.atom 0) (.atom 3)))
def fForced : Noun := .cell f3 (.cell (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) (.cell (.atom 4) (.cell (.atom 0) (.atom 3))))
/-- `corner-t1` = `*[[P*B uv] fCorner]`; `corner-t5` = `*[[wv P*B] fForced]`. -/
def ct1S : Noun := .cell (.atom (Pc * Bn)) (.atom uv)
def ct5S : Noun := .cell (.atom wv) (.atom (Pc * Bn))

def coinNamesL : List String :=
  ["alphaC", "gamma", "z1", "z2", "gammaP_re", "rhoP_re", "gammaP_im", "rhoP_im", "a", "b", "c",
   "gammaH_re", "rhoH_re", "alphaW", "gammaW", "gammaH_im", "rhoH_im", "y1", "y2"]

def k3L (k : K3) : List Nat := [k.c0.val.toNat, k.c1.val.toNat, k.c2.val.toNat]
def k6L (k : K6) : List Nat := k3L k.re ++ k3L k.im
def jn (n : ℕ) : Json := (n : Json)
def nounTok : Noun → List Json
  | .atom n => [(toString n : Json)]
  | .cell a b => ("c" : Json) :: (nounTok a ++ nounTok b)
def k3j (k : K3) : Json := Json.arr ((k3L k).map jn).toArray
def k6j (k : K6) : Json := Json.arr ((k6L k).map jn).toArray
def pubsOfL (f : ℕ → K3) (limbs : ℕ) : List ℕ := (List.range (limbs / 3)).flatMap fun i => k3L (f i)

/-- One `<id>.trace.json`, the J-8 shape: `main` = base columns, `aux_r1`/`aux_r2` = 3 limbs per round-1/round-2 extension column,
`public_flat` = public limbs. -/
def chipTrace (q : ChipIn) (nb n1 n2 : ℕ) (pubs : List ℕ) : Json :=
  let rows := List.range q.n
  let val (c i : ℕ) : ℕ := if h : i < q.n then (q.cols c ⟨i, h⟩).val else 0
  let main := rows.map fun i => Json.arr ((List.range nb).map fun c => jn (val c i)).toArray
  let aux := fun (e0 cnt : ℕ) =>
    let es := (List.range cnt).map (e0 + ·)
    (es, rows.map fun i => Json.arr (es.map fun e =>
      Json.arr ((List.range 3).map fun k => jn (val (nb + 3 * e + k) i)).toArray).toArray)
  let a1 := aux 0 n1
  let a2 := aux n1 n2
  Json.mkObj [("n_rows", jn q.n), ("width", jn (nb + 3 * (n1 + n2))), ("base_cols", jn nb),
    ("main", Json.arr main.toArray),
    ("aux_r1_ext_index", Json.arr (a1.1.map jn).toArray), ("aux_r1", Json.arr a1.2.toArray),
    ("aux_r2_ext_index", Json.arr (a2.1.map jn).toArray), ("aux_r2", Json.arr a2.2.toArray),
    ("public_flat", Json.arr (pubs.map jn).toArray)]

def partsOf (I : InJ9AL) : String :=
  if hv : validB I.toInJ8 = true then
    let Pb := mkPb I.toInJ8 ((validB_iff I.toInJ8).mp hv)
    s!"valid {validB I.toInJ8} validAL {validALB I} static {checkStaticJ9AL Pb I.c I.M.m I.r I.g I.AX.n I.SP.n I.rAX I.rSP I.AL.n I.rAL I.prims I.idxP I.rkP} pub {checkPubJ9ALE Pb I.prims I.idxP I.rkP I.c I.χ I.M I.pubsX I.pubsS I.pubsL}"
  else s!"validB false"

/-- The J-9 AL `pubeq.json`: J-9 A's fields plus `pubsL` / `prims`; records `check_pub_ok` = `checkPubJ9ALE`. -/
def pubeqJson (I : InJ9AL) (hv : ValidJ8 I.toInJ8) : Json :=
  let Pb := mkPb I.toInJ8 hv
  let ok := checkPubJ9ALE Pb I.prims I.idxP I.rkP I.c I.χ I.M I.pubsX I.pubsS I.pubsL
  let claimJ := (claimCells I.c).map fun k =>
    Json.mkObj [("k", jn k.val), ("noun", Json.arr (nounTok (claimNoun I.c k)).toArray),
      ("idx", jn (I.M.m k).1), ("hi", jn (rkC (claimNoun I.c k)).1), ("lo", jn (rkC (claimNoun I.c k)).2),
      ("msg_hi", jn (I.M.m k).2.1), ("msg_lo", jn (I.M.m k).2.2)]
  -- FC-G4: key-2 big-atom records (claim position k with compute public label kind `labelJ9[2k] = 2`): one-atom noun, idx = hi = lo = 0.
  let bigJ := ((List.finRange 3).filter fun k => ((Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9.labelJ9 p I.c I.M.m).getD (2 * k.val) 0).val == 2).map fun k =>
    Json.mkObj [("k", jn k.val), ("noun", Json.arr (nounTok (claimNoun I.c k)).toArray),
      ("idx", jn 0), ("hi", jn 0), ("lo", jn 0),
      ("msg_hi", jn (I.M.m k).2.1), ("msg_lo", jn (I.M.m k).2.2)]
  -- J-9 A has no jets: `regs = []`, so no pins (the J-8 `pins` entries carry a compiled noun; not emitted).
  let pinJ := I.regs.map fun (id : ℕ) =>
    Json.mkObj [("id", jn id), ("idx", jn (I.idx id)), ("hi", jn (I.rk id).1), ("lo", jn (I.rk id).2)]
  let recsC := (Nock.V1J9.Exe9.claimRecsJ9E I.χ I.c I.M.m).map fun r => Json.arr ((List.finRange 5).map fun c => k6j (r c)).toArray
  let recsP := (pinRecsJ8E Pb I.χ).map fun r => Json.arr ((List.finRange 5).map fun c => k6j (r c)).toArray
  let pc := (pinConsE I.regs I.idx).map fun r => Json.arr ((List.finRange 8).map fun c => k6j (r c)).toArray
  let M := I.M
  let pubs := fun (f : ℕ → K3) => Json.arr ((List.range 64).map fun i => k3j (f i)).toArray
  Json.mkObj [("check_pub_ok", ok), ("regs", Json.arr (I.regs.map jn).toArray),
    ("claim", Json.arr (claimJ ++ bigJ).toArray), ("pins", Json.arr pinJ.toArray),
    ("claim_recs_E", Json.arr recsC.toArray), ("pin_recs_E", Json.arr recsP.toArray), ("pin_cons_E", Json.arr pc.toArray),
    ("rho", Json.arr ((List.finRange 5).map fun i => k6j (M.ρ i)).toArray), ("rhoS", k6j M.ρS),
    ("pubsC", pubs M.pubsC), ("pubsW", pubs M.pubsW), ("pubsJ", pubs M.pubsJ), ("pubsA", pubs M.pubsA), ("pubsV", pubs M.pubsV),
    ("pubsX", pubs I.pubsX), ("pubsS", pubs I.pubsS), ("pubsL", pubs I.pubsL), ("aluOn", I.aluOn),
    ("prims", Json.arr (I.prims.map fun q => Json.mkObj [("id", jn q.1), ("idx", jn (I.idxP q.1)), ("hi", jn (I.rkP q.1).1), ("lo", jn (I.rkP q.1).2),
      ("code", jn (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL.primCode q.2))]).toArray),
    ("axOn", I.axOn), ("spOn", I.spOn)]

/-- The primitive table of the default run (empty: the registry is `fun _ => none`). -/
def primsL : List (ℕ × Nock.Jet.Prim.PrimOp) := []

/-- Prims mode: `*[[a b] [11 [%wild [1 7]] (primC op)]]` with the primitive `op` registered at id 7. -/
def primProg (op : Nock.Jet.Prim.PrimOp) (a b : ℕ) : Noun × Noun :=
  (.cell (.atom a) (.atom b),
   Nock.Jet.wildCall 7 (Nock.Jet.Prim.primC op))

def primsMode : String → Option (Nock.Jet.Prim.PrimOp × ℕ × ℕ)
  | "add" => some (.add, Nock.Field.p + 5, Nock.Field.p + 7)
  | "mul" => some (.mul, 2 ^ 70 + 3, 2 ^ 65 + 11)
  | _ => none

def main (args : List String) : IO UInt32 := do
  let out := FilePath.mk (args.headD ".")
  let prog0 := args.getD 1 "toy"
  let pm := args.getD 2 ""
  let pmode := primsMode pm
  if pm != "" && pmode.isNone then
    IO.eprintln s!"unknown prims mode {pm} (add | mul)"; return 2
  let prog := if pmode.isSome then s!"prim-{pm}" else prog0
  let (s, f) ← match prog0 with
    | "toy" => pure (toyS, toyF)
    | "absent" => pure (absS, absF)
    | "corner-t1" => pure (ct1S, fCorner)
    | "corner-t5" => pure (ct5S, fForced)
    | _ => do IO.eprintln s!"unknown program {prog0} (toy | absent | corner-t1 | corner-t5)"; return 2
  let (s, f, primsR, reg) : Noun × Noun × List (ℕ × Nock.Jet.Prim.PrimOp) × Nock.Jet.Registry :=
    match pmode with
    | none => (s, f, primsL, fun _ => none)
    | some (op, a, b) =>
      let (s', f') := primProg op a b
      (s', f', [(7, op)],
        (Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.addPrims Nock.Jet.VerifiedRegistry.empty [(7, op)]).R)
  let χ := Nock.V1J8.Gen.prngCoins 1
  match genJ9ALXJ reg (fun _ => Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData.trivTpl) primsR 1000 s f χ with
  | none => IO.eprintln s!"{prog}: genJ9ALXJ none"; return 2
  | some I =>
    let ok := checkJ9ALX I
    IO.eprintln s!"checkJ9ALX: {ok}"
    IO.eprintln s!"parts: {partsOf I}"
    IO.eprintln s!"rows X {I.X.n} C {I.C.n} W {I.W.n} J {I.J.n} A {I.A.n} V {I.V.n} AX {I.AX.n} SP {I.SP.n} AL {I.AL.n}; axOn {I.axOn} spOn {I.spOn}; kroots {I.kroots} krootsV {I.krootsV}"
    if !ok then return 1
    let dir := out / "traces" / s!"trace-{prog}"
    IO.FS.createDirAll dir
    -- coins.json
    let coinsJ := (List.range frameJ8.n).map fun (i : ℕ) =>
      if h : i < frameJ8.n then
        Json.mkObj [("index", jn i), ("name", coinNamesL.getD i ""), ("limbs", k3j (I.χ ⟨i, h⟩))]
      else Json.null
    let g := gV I.χ
    let derived := (List.range 22).map fun (j : ℕ) =>
      Json.mkObj [("slot", jn (19 + j)), ("power", jn (j / 2)), ("part", if j % 2 = 0 then "re" else "im"),
        ("limbs", k3j (let q := powE g (j / 2); if j % 2 = 0 then q.re else q.im))]
    IO.FS.writeFile (dir / "coins.json") ((Json.mkObj [("prog", prog), ("family", "j9al"),
      ("driver", "none: PRNG placeholder coins Gen.prngCoins 1 (not Fiat-Shamir); instance from genJ9ALXJ"),
      ("verdict", "checkJ9ALX true"), ("kroots", jn I.kroots), ("krootsV", jn I.krootsV),
      ("coins", Json.arr coinsJ.toArray), ("gamma_prime", Json.mkObj [("re_coin", jn 4), ("im_coin", jn 6)]),
      ("derived", Json.arr derived.toArray)]).compress ++ "\n")
    -- traces: (id, chip, base cols, round-1 exts, round-2 exts, public limbs)
    let pubsXc := (List.range 33).map fun j => (Nock.V1J9.Check9.pubVJ9E I.c I.M.m I.M.ρ I.M.ρS I.χ j).val
    let items : List (String × ChipIn × ℕ × ℕ × ℕ × List ℕ) :=
      [("computeChipVCLHX9", I.X, 83, 18, 0, pubsXc),
       ("cellChipHQKW", I.C, 134, 18, 18, pubsOfL I.M.pubsC 18),
       ("walkChipJ8", I.W, 25, 24, 23, pubsOfL I.M.pubsW 24),
       ("jetChipJ8", I.J, 29, 14, 0, pubsOfL I.M.pubsJ 12),
       ("atomChipHQL", I.A, 205, 18, 30, pubsOfL I.M.pubsA 36),
       ("walkChipHQK", I.V, 25, 24, 23, pubsOfL I.M.pubsV 24)]
      ++ (if I.axOn then [("axisChipJ9", I.AX, 22, 0, 10, pubsOfL I.pubsX 12)] else [])
      ++ (if I.spOn then [("splitChipJ9", I.SP, 72, 0, 6, pubsOfL I.pubsS 6)] else [])
      ++ (if I.aluOn then [("aluChipJ9", I.AL, 94, 18, 16, pubsOfL I.pubsL 18)] else [])
    for (nm, q, nb, n1, n2, pb) in items do
      IO.FS.writeFile (dir / s!"{nm}.trace.json") ((chipTrace q nb n1 n2 pb).compress ++ "\n")
    if hv : validB I.toInJ8 = true then
      IO.FS.writeFile (dir / "pubeq.json") ((pubeqJson I ((validB_iff I.toInJ8).mp hv)).compress ++ "\n")
    else IO.eprintln s!"{prog}: validB false, no pubeq.json"
    IO.println s!"{prog}: wrote {items.length} traces + coins.json + pubeq.json to {dir}"
    return 0
