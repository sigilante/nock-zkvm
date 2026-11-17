/-
  NockvmE2E/Exec/J9ALConv.lean

  The conversion bits shared by `J9ALEmit2Main` (the dump) and `DriveJ9AL` (the FS driver): programs, noun tokens, K3 limbs,
  `chipTrace`, `pubeqJson`.  Moved verbatim out of the emitter (its output is unchanged: diffed [executed]); `pubsOfRec` is new.
  Untrusted tooling; no theorem.
-/
import Nock.V1J9AL.GenJ9ALXJ
import Nock.V1J9AL.CheckJ9AL
import Nock.V1J9A.GenJ9AX
import Nock.V1J9.GenJ9
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP
import Lean.Data.Json
import NockvmE2E.Z38.CatJ

set_option autoImplicit false
set_option maxRecDepth 100000

open Lean Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX Nock.V1J8.Exe System
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.GenJ9ALXJ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP trivTpl)

def rspP : ℕ → Noun
  | 0 => .atom 0
  | n+1 => .cell (.atom 0) (rspP n)

def toyS : Noun := rspP 63
def toyF : Noun := .cell (.cell (.atom 0) (.atom (2 ^ 64 - 1))) (.cell (.atom 0) (.atom (2 ^ 63 - 1)))
def absS : Noun := .cell (.atom (Nock.Field.p + 5)) (.atom 0)
def absF : Noun := .cell (.atom 0) (.atom 2)

/-- `*[[a b] [11 [%wild [1 7]] (primC op)]]` with the primitive `op` registered at id 7. -/
def primProg (op : Nock.Jet.Prim.PrimOp) (a b : ℕ) : Noun × Noun :=
  (.cell (.atom a) (.atom b),
   .cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) (.cell (.atom 1) (.atom 7))) (Nock.Jet.Prim.primC op)))

/-- program `jp`: subject `[3 (p+5)]`, formula `[fJ fP]` = one template call (id 7, `TN`, as Batch4892 `fJ`) and one big-atom `add`
(id 8).  Only meaningful in the catalogue-registry mode (`--reg-catj`, registry `catJ`). -/
def jpProg : Noun × Noun :=
  (.cell (.atom 3) (.atom (Nock.Field.p + 5)),
   .cell (.cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) (.cell (.atom 1) (.atom 7)))
            (Nock.Jet.Autogen.compile Nock.Field.p NockvmE2E.Z38.CatJ.TN)))
         (.cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) (.cell (.atom 1) (.atom 8))) (Nock.Jet.Prim.primC .add))))

/-- registry mode: the registry `R` and template table `Rt` handed to `genJ9ALXJ`.  Default (`catj = false`): `addPrims empty prims`,
`rtP (fun _ => trivTpl) prims` (unchanged); `catj = true`: `catJ.toVR.R`, `rtP catJ.toCR.Rt prims`. -/
def regOf (catj : Bool) (primsR : List (ℕ × Nock.Jet.Prim.PrimOp)) : Nock.Jet.Registry × (ℕ → Nock.Jet.Autogen.Tpl) :=
  if catj then (NockvmE2E.Z38.CatJ.catJ.toVR.R, rtP NockvmE2E.Z38.CatJ.catJ.toCR.Rt primsR)
  else ((Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.addPrims Nock.Jet.VerifiedRegistry.empty primsR).R,
        rtP (fun _ => trivTpl) primsR)

/-- program name ↦ (s, f, prims, fuel) -/
def progOf : String → Option (Noun × Noun × List (ℕ × Nock.Jet.Prim.PrimOp) × ℕ)
  | "add" => let (s, f) := primProg .add (Nock.Field.p + 5) (Nock.Field.p + 7); some (s, f, [(7, .add)], 2)
  | "mul" => let (s, f) := primProg .mul (2 ^ 70 + 3) (2 ^ 65 + 11); some (s, f, [(7, .mul)], 2)
  | "toy" => some (toyS, toyF, [], 1000)
  | "absent" => some (absS, absF, [], 1000)
  | "jp" => some (jpProg.1, jpProg.2, [(8, .add)], 4)
  | _ => none

def k3L (k : K3) : List Nat := [k.c0.val.toNat, k.c1.val.toNat, k.c2.val.toNat]
def k6L (k : K6) : List Nat := k3L k.re ++ k3L k.im
def jn (n : ℕ) : Json := (n : Json)
def nounTok : Noun → List Json
  | .atom n => [(toString n : Json)]
  | .cell a b => ("c" : Json) :: (nounTok a ++ nounTok b)
def k3j (k : K3) : Json := Json.arr ((k3L k).map jn).toArray
def k6j (k : K6) : Json := Json.arr ((k6L k).map jn).toArray
def pubsOfL (f : ℕ → K3) (limbs : ℕ) : List ℕ := (List.range (limbs / 3)).flatMap fun i => k3L (f i)

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

def pubeqJson (I : InJ9AL) (hv : ValidJ8 I.toInJ8) : Json :=
  let Pb := mkPb I.toInJ8 hv
  let ok := checkPubJ9ALE Pb I.prims I.idxP I.rkP I.c I.χ I.M I.pubsX I.pubsS I.pubsL
  let claimJ := (claimCells I.c).map fun k =>
    Json.mkObj [("k", jn k.val), ("noun", Json.arr (nounTok (claimNoun I.c k)).toArray),
      ("idx", jn (I.M.m k).1), ("hi", jn (rkC (claimNoun I.c k)).1), ("lo", jn (rkC (claimNoun I.c k)).2),
      ("msg_hi", jn (I.M.m k).2.1), ("msg_lo", jn (I.M.m k).2.2)]
  -- key-2 big-atom records (claim position k with compute public label kind `labelJ9[2k] = 2`): one-atom noun, idx = hi = lo = 0.
  let bigJ := ((List.finRange 3).filter fun k => ((Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9.labelJ9 p I.c I.M.m).getD (2 * k.val) 0).val == 2).map fun k =>
    Json.mkObj [("k", jn k.val), ("noun", Json.arr (nounTok (claimNoun I.c k)).toArray),
      ("idx", jn 0), ("hi", jn 0), ("lo", jn 0),
      ("msg_hi", jn (I.M.m k).2.1), ("msg_lo", jn (I.M.m k).2.2)]
  let pinJ := I.regs.map fun (id : ℕ) =>
    Json.mkObj [("id", jn id), ("idx", jn (I.idx id)), ("hi", jn (I.rk id).1), ("lo", jn (I.rk id).2),
      -- the pin's noun = the registry template `compile p (Rt id)` (`InpLink9.hpin`); `regs = []` at the default programs, so unchanged there
      ("noun", Json.arr (nounTok (Nock.Jet.Autogen.compile Nock.Field.p (I.Rt id))).toArray)]
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
    ("prims", Json.arr (I.prims.map fun q => Json.mkObj [("id", jn q.1), ("code", jn (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL.primCode q.2)),
      ("idx", jn (I.idxP q.1)), ("hi", jn (I.rkP q.1).1), ("lo", jn (I.rkP q.1).2)]).toArray),
    ("axOn", I.axOn), ("spOn", I.spOn)]

/-- the public values (flat limbs) of table `id` in the record `I`, as the emitter writes them into `<id>.trace.json` -/
def pubsOfRec (I : InJ9AL) (id : String) : List ℕ :=
  if id == "computeChipVCLHX9" then (List.range 33).map fun j => (Nock.V1J9.Check9.pubVJ9E I.c I.M.m I.M.ρ I.M.ρS I.χ j).val
  else if id == "cellChipHQKW" then pubsOfL I.M.pubsC 18
  else if id == "walkChipJ8" then pubsOfL I.M.pubsW 24
  else if id == "jetChipJ8" then pubsOfL I.M.pubsJ 12
  else if id == "atomChipHQL" then pubsOfL I.M.pubsA 36
  else if id == "walkChipHQK" then pubsOfL I.M.pubsV 24
  else if id == "axisChipJ9" then pubsOfL I.pubsX 12
  else if id == "splitChipJ9" then pubsOfL I.pubsS 6
  else if id == "aluChipJ9" then pubsOfL I.pubsL 18
  else []
