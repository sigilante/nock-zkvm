/-
  NockvmE2E/Exec/J9ALEmit2Main.lean

  `nockvm-e2e-j9alemit2 OUT [--reg-catj] [prog ...]`, `prog ∈ add | mul | toy | absent | jp` (`jp`, with `--reg-catj`: registry `catJ` (template id 7 + prim add id 8), also writes `calls` into pubeq.json) (default: all four).  For each program it runs `genJ9ALXJ`
  (registry `addPrims empty prims`, template table `rtP (fun _ => trivTpl) prims`, PRNG coins `Gen.prngCoins seed`, the first seed in
  `1..8` with `checkJ9ALX = true`; NOT Fiat–Shamir) and writes `OUT/trace-<prog>/`: the J-9 A dump files (`<id>.trace.json` of the six J-8 chips,
  `axisChipJ9` / `splitChipJ9` when on), `aluChipJ9.trace.json` when `aluOn`, `coins.json`, `pubeq.json` (J-9 A fields + `pubsL`,
  `prims[] = {id, code, idx, hi, lo}` with `code = RealIOJ9AL.primCode`, and the key-2 big-atom records of `claim`).  Also writes the ALU chip document
  `OUT/j9al_aluChipJ9.json` (`aluSpec`, with the y-power derived slots 41..106 as coins (17, 18)).
  Programs: `add` = Batch4921/4936 (`*[[(p+5) (p+7)] [11 [%wild [1 7]] (primC add)]]`, fuel 2), `mul` = Batch4932 (`2^70+3`, `2^65+11`, fuel 2),
  `toy` = J-9 A toy (walk dispatch, prims [], aluOn false), `absent` = `*[[(p+5) 0] [0 2]]` (prims [], chips off).
  Untrusted tooling; no theorem.  The dump code follows nockvm `TraceDemo/J9ALEmit.lean` (cross-check target), the doc code `J9AEmitMain.lean`.
-/
import NockvmE2E.Emit.ChipsJ9AL
import NockvmE2E.Exec.J9ALConv
import NockvmE2E.Exec.FreeProg
import Nock.V1J9AL.GenJ9ALXJ
import Nock.V1J9AL.CheckJ9AL
import Nock.V1J9A.GenJ9AX
import Nock.V1J9.GenJ9
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP
import Lean.Data.Json

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.ALDoc
open Lean Nock.Emit Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP

def kindStr : VarKind → String
  | .traceCur => "trace_cur" | .traceNext => "trace_next"
  | .challenge => "challenge" | .publicVal => "public_val"

def toJ : JExpr → Json
  | .var k i => Json.mkObj [("var", Json.mkObj [("kind", kindStr k), ("index", i)])]
  | .constF n => Json.mkObj [("const_f", toString n)]
  | .constZ z => Json.mkObj [("const_z", Lean.toJson z)]
  | .add a b => Json.mkObj [("add", Json.arr #[toJ a, toJ b])]
  | .sub a b => Json.mkObj [("sub", Json.arr #[toJ a, toJ b])]
  | .mul a b => Json.mkObj [("mul", Json.arr #[toJ a, toJ b])]
  | .neg a => Json.mkObj [("neg", toJ a)]
  | .pow a n => Json.mkObj [("pow", Json.arr #[toJ a, (n : Json)])]
  | .extVar i k => Json.mkObj [("ext_var", Json.mkObj [("ext_index", i), ("kind", kindStr k)])]
  | .extChal i => Json.mkObj [("ext_chal", Json.mkObj [("index", i)])]
  | .extLift a => Json.mkObj [("ext_lift", toJ a)]
  | .extAdd a b => Json.mkObj [("ext_add", Json.arr #[toJ a, toJ b])]
  | .extSub a b => Json.mkObj [("ext_sub", Json.arr #[toJ a, toJ b])]
  | .extMul a b => Json.mkObj [("ext_mul", Json.arr #[toJ a, toJ b])]
  | .extNeg a => Json.mkObj [("ext_neg", toJ a)]
  | .ref i => Json.mkObj [("ref", (i : Json))]

def sampledAfterJ8 : List ℕ := [1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def coinAfter (i : ℕ) : ℕ := sampledAfterJ8.getD i 0

/-- Derived slots `19..40` are `γ′ = (χ4, χ6)` powers (round 1); `41..106` are `y = (χ17, χ18)` powers (round 0). -/
def slotRound (i : ℕ) : ℕ :=
  if i < 19 then coinAfter i else if i < 41 then max (coinAfter 4) (coinAfter 6) else max (coinAfter 17) (coinAfter 18)

structure Summ where
  deg : ℕ := 0
  rnd : ℕ := 0
  next : Bool := false
  chals : List ℕ := []
  pub : ℕ := 0

def Summ.join (a b : Summ) (d : ℕ) : Summ :=
  { deg := d, rnd := max a.rnd b.rnd, next := a.next || b.next,
    chals := b.chals.foldl (fun l c => if l.contains c then l else c :: l) a.chals, pub := max a.pub b.pub }

def baseRounds (s : TSpec) : List ℕ :=
  (s.baseCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r
def extRounds (s : TSpec) : List ℕ :=
  (s.extCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r

def summ (br er : List ℕ) (tab : Array Summ) : JExpr → Summ
  | .ref i => tab.getD i {}
  | .var .traceCur i => { deg := 1, rnd := br.getD i 0 }
  | .var .traceNext i => { deg := 1, rnd := br.getD i 0, next := true }
  | .var .challenge i | .extChal i | .extVar i .challenge => { chals := [i], rnd := slotRound i }
  | .var .publicVal i => { pub := i / 3 + 1 }
  | .extVar i .publicVal => { pub := i + 1 }
  | .constF _ | .constZ _ => {}
  | .extVar i .traceCur => { deg := 1, rnd := er.getD i 0 }
  | .extVar i .traceNext => { deg := 1, rnd := er.getD i 0, next := true }
  | .neg a | .extNeg a | .extLift a => summ br er tab a
  | .pow a n => let x := summ br er tab a; { x with deg := if x.deg = 0 then 0 else x.deg * n }
  | .add a b | .sub a b | .extAdd a b | .extSub a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (max x.deg y.deg)
  | .mul a b | .extMul a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (x.deg + y.deg)

def columnsJson (s : TSpec) : Json :=
  let br := baseRounds s
  let er := extRounds s
  let nb := br.length
  let bs := br.zipIdx.map fun ((r, i) : ℕ × ℕ) =>
    Json.mkObj [("name", s!"b{i}"), ("index", i), ("round", r), ("field", Json.mkObj [("base", true)]),
      ("var_kind", "trace_cur")]
  let es := er.zipIdx.flatMap fun ((r, e) : ℕ × ℕ) => (List.range 3).map fun (c : ℕ) =>
    Json.mkObj [("name", s!"k{e}_{c}"), ("index", nb + 3 * e + c), ("round", r),
      ("field", Json.mkObj [("ext", Json.mkObj [("ext_index", e), ("coord", c)])]), ("var_kind", "trace_cur")]
  Json.arr (bs ++ es).toArray

def chipJson (id : String) (s : TSpec) : Json × List ℕ × ℕ × ℕ :=
  let d := emitDag s
  let br := baseRounds s
  let er := extRounds s
  let tab := d.defs.foldl (fun (t : Array Summ) j => t.push (summ br er t j)) #[]
  let arr (l : List JExpr) := Json.arr (l.map toJ).toArray
  let cs := [("base_transition", d.base), ("ext_transition", d.ext), ("mixed_transition", d.mixed),
    ("ext_deg1", d.ext1), ("ext_deg3", d.ext3), ("equality_checks", d.eqc)]
  let cons := cs.flatMap fun (nm, l) => l.zipIdx.map fun ((j, i) : JExpr × ℕ) =>
    let m := summ br er tab j
    Json.mkObj [("kind", if m.next then "transition" else "row"), ("round", m.rnd), ("degree", m.deg),
      ("source", s!"{id}.{nm}[{i}]"), ("expr", toJ j)]
  let allS := (cs.flatMap fun (_, l) => l.map (summ br er tab)) ++ tab.toList
  let ch := allS.foldl (fun l m => m.chals.foldl (fun l c => if l.contains c then l else c :: l) l) []
  let mp := (allS.map (·.pub)).foldl max 0
  (Json.mkObj [("id", id), ("rounds", s.rounds), ("columns", columnsJson s),
    ("shared", arr d.defs),
    ("gate_lists", Json.mkObj (cs.map fun (nm, l) => (nm, arr l))),
    ("constraints", Json.arr cons.toArray), ("bus_ids", Json.arr #[])], ch, mp, d.defs.length)

def coinNames : List String :=
  ["alphaC", "gamma", "z1", "z2", "gammaP_re", "rhoP_re", "gammaP_im", "rhoP_im", "a", "b", "c",
   "gammaH_re", "rhoH_re", "alphaW", "gammaW", "gammaH_im", "rhoH_im", "y1", "y2"]

/-- The ALU document: as `J9AEmitMain.docJson`, but slots `41..106` are `y = (χ17, χ18)` powers `(slot − 41)/2`
(slots `19..40` stay `γ′ = (χ4, χ6)` powers `(slot − 19)/2`). -/
def docJsonAL (p : ℕ) (δv : ℕ) (id : String) (s : TSpec) : Json :=
  let c := chipJson id s
  let slots := c.2.1
  let derived := ((slots.filter (· ≥ 19)).mergeSort).map fun (sl : ℕ) =>
    if sl < 41 then
      Json.mkObj [("slot", sl), ("re_coin", 4), ("im_coin", 6), ("power", (((sl - 19) / 2 : ℕ) : Json)),
        ("part", if (sl - 19) % 2 = 0 then "re" else "im")]
    else
      Json.mkObj [("slot", sl), ("re_coin", 17), ("im_coin", 18), ("power", (((sl - 41) / 2 : ℕ) : Json)),
        ("part", if (sl - 41) % 2 = 0 then "re" else "im")]
  let npub := max c.2.2.1 1
  let coins := (List.range 19).map fun (i : ℕ) =>
    Json.mkObj [("index", i), ("name", coinNames.getD i s!"chi_{i}"), ("sampled_after", coinAfter i),
      ("field", "ext_k"), ("components", 3)]
  Json.mkObj [("schema_version", 1), ("field", "goldilocks"),
    ("extension", Json.mkObj [("k_degree", 3), ("k_prime_degree", 6), ("k_prime_delta", toString δv),
      ("modulus", Json.arr #[toString (p - 7), "0", "0"])]),
    ("frame", Json.mkObj [("coins", Json.arr coins.toArray),
      ("staging_rule", "constraint.round = max(max column.round read, max coin.sampled_after read)")]),
    ("derived_challenges", Json.arr derived.toArray),
    ("public_values", Json.arr ((List.range npub).map fun (i : ℕ) =>
      Json.mkObj [("index", i), ("name", s!"pub_{i}"), ("round", 0)]).toArray),
    ("buses", Json.arr #[]),
    ("chips", Json.arr #[c.1])]

end NockvmE2E.ALDoc



open Lean Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX Nock.V1J8.Exe System
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.GenJ9ALXJ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl)

def coinNamesL : List String := NockvmE2E.ALDoc.coinNames

/-- Run one program; `true` iff generated, checked (`checkJ9ALX`) and written. -/
def runProg (out : FilePath) (prog : String) (fo : NockvmE2E.Exec.FreeProg.FreeOpts) (catj : Bool := false) : IO Bool := do
  let (s, f, primsR, fuel) ← match NockvmE2E.Exec.FreeProg.resolveProg prog fo with
    | .ok p => pure p
    | .error e => IO.eprintln s!"ERROR: {e}"; return false
  let pe := NockvmE2E.Exec.FreeProg.progErrors primsR
  unless pe.isEmpty do
    for e in pe do IO.eprintln s!"ERROR: {e}"
    return false
  let (reg, rtT) := regOf catj primsR
  if (Nock.V1J8.Gen.runX reg fuel s f).isNone then
    IO.eprintln s!"ERROR: {prog}: the Nock run did not finish (crash, or more than fuel {fuel} steps; try --fuel N with a larger N)"
    return false
  let mut found : Option (InJ9AL × ℕ) := none
  for seed in [1, 2, 3, 4, 5, 6, 7, 8] do
    if found.isNone then
      match genJ9ALXJ reg rtT primsR fuel s f (Nock.V1J8.Gen.prngCoins seed) with
      | none => IO.eprintln s!"{prog}: seed {seed}: genJ9ALXJ none (the run is fine but the tracegen refuses it, e.g. a prim call whose operands are not atoms)"
      | some I =>
        let ok := checkJ9ALX I
        IO.eprintln s!"{prog}: seed {seed}: checkJ9ALX {ok}"
        if ok then found := some (I, seed)
  let some (I, seed) := found
    | IO.eprintln s!"ERROR: {prog}: no seed gives checkJ9ALX = true"; return false
  let se := NockvmE2E.Exec.FreeProg.sideErrors reg primsR fuel s f I
  unless se.isEmpty do
    if fo.force then
      for e in se do IO.eprintln s!"WARNING (--allow-unverifiable): {prog}: {e}"
    else
      for e in se do IO.eprintln s!"ERROR: {prog}: {e}"
      return false
  IO.println s!"== {prog} (PRNG seed {seed}, fuel {fuel}) =="
  IO.println s!"checkJ9ALX {checkJ9ALX I}"
  IO.println s!"rows X {I.X.n} C {I.C.n} W {I.W.n} J {I.J.n} A {I.A.n} V {I.V.n} AX {I.AX.n} SP {I.SP.n} AL {I.AL.n}"
  IO.println s!"kroots {I.kroots} krootsV {I.krootsV} nA {I.A.n} axOn {I.axOn} spOn {I.spOn} aluOn {I.aluOn}"
  if catj then IO.println s!"registry catJ: regs {I.regs} ids (J calls) {I.ids} hNof jet (J rows) {I.J.n} prims {I.prims.map Prod.fst}"
  IO.println s!"hN (h per table X C W J A V AX SP AL) {[I.X.h, I.C.h, I.W.h, I.J.h, I.A.h, I.V.h, I.AX.h, I.SP.h, I.AL.h]} prims {I.prims.length}"
  let dir := out / s!"trace-{prog}"
  IO.FS.createDirAll dir
  let coinsJ := (List.range frameJ8.n).map fun (i : ℕ) =>
    if h : i < frameJ8.n then
      Json.mkObj [("index", jn i), ("name", coinNamesL.getD i ""), ("limbs", k3j (I.χ ⟨i, h⟩))]
    else Json.null
  let g := gV I.χ
  let derived := (List.range 22).map fun (j : ℕ) =>
    Json.mkObj [("slot", jn (19 + j)), ("power", jn (j / 2)), ("part", if j % 2 = 0 then "re" else "im"),
      ("limbs", k3j (let q := powE g (j / 2); if j % 2 = 0 then q.re else q.im))]
  let y := yE I.χ
  let derivedY := (List.range 66).map fun (j : ℕ) =>
    Json.mkObj [("slot", jn (41 + j)), ("power", jn (j / 2)), ("part", if j % 2 = 0 then "re" else "im"),
      ("limbs", k3j (let q := powE y (j / 2); if j % 2 = 0 then q.re else q.im))]
  IO.FS.writeFile (dir / "coins.json") ((Json.mkObj [("prog", prog), ("family", "j9al"),
    ("driver", s!"none: PRNG placeholder coins Gen.prngCoins {seed} (not Fiat-Shamir); instance from genJ9ALXJ"),
    ("verdict", "checkJ9ALX true"), ("kroots", jn I.kroots), ("krootsV", jn I.krootsV),
    ("coins", Json.arr coinsJ.toArray), ("gamma_prime", Json.mkObj [("re_coin", jn 4), ("im_coin", jn 6)]),
    ("derived", Json.arr derived.toArray),
    ("y_coin", Json.mkObj [("re_coin", jn 17), ("im_coin", jn 18)]), ("derived_y", Json.arr derivedY.toArray)]).compress ++ "\n")
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
    let pe := pubeqJson I ((validB_iff I.toInJ8).mp hv)
    -- registry mode adds the call sequence (the J call ids); the default path is byte-identical
    let pe := if catj then pe.setObjVal! "calls" (Json.arr (I.ids.map jn).toArray) else pe
    IO.FS.writeFile (dir / "pubeq.json") (pe.compress ++ "\n")
  else IO.eprintln s!"{prog}: validB false, no pubeq.json"
  IO.println s!"{prog}: wrote {items.length} traces + coins.json + pubeq.json to {dir}"
  return true

def main (args0 : List String) : IO UInt32 := do
  let (fo, args) ← match NockvmE2E.Exec.FreeProg.extractFree {} args0 with
    | .ok r => pure r
    | .error e => IO.eprintln s!"ERROR: {e}"; return 2
  -- `--print-primc OP`: print the formula text of the primitive `OP` (a core, the jet's naive Nock body) and exit
  match args with
  | ["--print-primc", op] =>
    match NockvmE2E.Exec.NounText.primNames.lookup op with
    | some o => IO.println (NockvmE2E.Exec.NounText.showNoun (Nock.Jet.Prim.primC o)); return 0
    | none => IO.eprintln s!"ERROR: unknown primitive '{op}'"; return 2
  | _ => pure ()
  let out := FilePath.mk (args.headD ".")
  let rest := args.drop 1
  let catj := rest.contains "--reg-catj"
  let rest := rest.filter (· != "--reg-catj")
  let progs := match rest with
    | [] => if fo.any then ["custom"] else ["add", "mul", "toy", "absent"]
    | l => l
  if fo.any && progs.length != 1 then
    IO.eprintln "ERROR: with --subject/--formula give exactly one program label (it names the output directory trace-<label>)"
    return 2
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "j9al_aluChipJ9.json")
    ((NockvmE2E.ALDoc.docJsonAL Nock.Field.p Nock.Emit.δ.val "aluChipJ9" Nock.Emit.aluSpec).compress ++ "\n")
  IO.println s!"wrote {out}/j9al_aluChipJ9.json"
  let mut rc : UInt32 := 0
  for pr in progs do
    let ok ← runProg out pr fo catj
    if !ok then rc := 1
  return rc
