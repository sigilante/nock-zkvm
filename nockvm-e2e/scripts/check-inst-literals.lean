/-
  scripts/check-inst-literals.lean -- the instance-literal check

  The Lean literals `AddALR.addALR` and `JpALR.jpX` are used by kernel-checked non-vacuity theorems as the
  executed `add` and `jp` instances.  This script checks that each literal equals the instance that
  `FlatFam.loadInstF famJ9AL` loads from the shipped fixture, field by field:

    nD dShift dGen hN hGen hShift r k d l nc nq colKind blockOf pre pubOf ppt nCoins derived pubLay slotOf pubMode,
    pubIn (claim cells, pins, atoms, prims, calls), and for every table hN col0 nc npub pubBase, its chip by
    `chipEqB` (id, shared, constraints, colRound, baseCols, width) and its K tags (sharedK, consK).

  `pubTest` (a function) is not compared.  The false-claim twins `addALRF` / `jpXF` differ from the literals only in
  `pubIn` and are not checked here.

  Run from `nockvm-e2e/` (the instances name their chip files as `out3/<prog>/<file>`):

    mkdir -p out3 && ln -sfn ../fixtures/j9al-add out3/add && ln -sfn ../fixtures/j9alj-jp out3/jp
    lake env lean scripts/check-inst-literals.lean

  Prints one line per instance, `OK` or the list of fields that differ.  Untrusted tooling; no theorem.
-/
import NockvmE2E.Exec.AddALR
import NockvmE2E.Exec.JpALR
import NockvmE2E.Exec.FlatFam

open NockvmE2E.Exec NockvmE2E.Exec.V

namespace CheckInst

def tokS : PE.Tok → String
  | PE.Tok.cell => "c"
  | PE.Tok.atom n => toString n

def recS (r : PE.NounRec) : String :=
  s!"{r.key}:[{",".intercalate (r.noun.map tokS)}]:{r.idx}:{r.hi}:{r.lo}"

def primS (r : PE.PrimRec) : String := s!"{r.id}:{r.code}:{r.idx}:{r.hi}:{r.lo}"

def pubInS (p : PE.PubIn) : String :=
  s!"cells {p.claimCells.map recS} pins {p.pins.map recS} atoms {p.atoms} prims {p.prims.map primS} calls {p.calls}"

def k3S (x : VF.K3) : String := s!"({x.c0},{x.c1},{x.c2})"

def tabEq (a b : TabInst) : List String :=
  (if a.hN == b.hN then [] else ["hN"]) ++ (if a.col0 == b.col0 then [] else ["col0"]) ++
  (if a.nc == b.nc then [] else ["nc"]) ++ (if a.npub == b.npub then [] else ["npub"]) ++
  (if a.pubBase == b.pubBase then [] else ["pubBase"]) ++
  (if J8Chips.chipEqB a.chip b.chip then [] else ["chip"]) ++
  (if a.chip.sharedK == b.chip.sharedK then [] else ["sharedK"]) ++
  (if a.chip.consK == b.chip.consK then [] else ["consK"])

/-- the fields on which the literal `a` and the loaded instance `b` differ -/
def diffs (a b : ExecInst) : List String :=
  let f (nm : String) (ok : Bool) : List String := if ok then [] else [nm]
  f "nD" (a.nD == b.nD) ++ f "dShift" (a.dShift == b.dShift) ++ f "dGen" (a.dGen == b.dGen) ++
  f "hN" (a.hN == b.hN) ++ f "hGen" (a.hGen == b.hGen) ++ f "hShift" (a.hShift == b.hShift) ++
  f "r" (a.r == b.r) ++ f "k" (a.k == b.k) ++ f "d" (a.d == b.d) ++ f "l" (a.l == b.l) ++
  f "nc" (a.nc == b.nc) ++ f "nq" (a.nq == b.nq) ++ f "colKind" (a.colKind == b.colKind) ++
  f "blockOf" (a.blockOf == b.blockOf) ++ f "pre" (a.pre == b.pre) ++ f "pubOf" (a.pubOf == b.pubOf) ++
  f "ppt" (k3S a.ppt == k3S b.ppt) ++ f "nCoins" (a.nCoins == b.nCoins) ++ f "derived" (a.derived == b.derived) ++
  f "pubIn" (pubInS a.pubIn == pubInS b.pubIn) ++
  f "pubLay" (a.pubLay.bases == b.pubLay.bases && a.pubLay.lens == b.pubLay.lens && a.pubLay.present == b.pubLay.present) ++
  f "slotOf" (a.slotOf == b.slotOf) ++ f "pubMode" (a.pubMode == b.pubMode) ++
  f "tabs.size" (a.tabs.size == b.tabs.size) ++
  ((a.tabs.toList.zip b.tabs.toList).zipIdx.flatMap fun ((x, y), i) => (tabEq x y).map (s!"tab{i}." ++ ·))

def check (name path : String) (lit : ExecInst) : IO Bool := do
  let xi ← FlatFam.loadInstF J9ALChips.famJ9AL path
  match diffs lit xi with
  | [] => IO.println s!"{name}: OK (literal = loadInstF famJ9AL {path})"; pure true
  | ds => IO.println s!"{name}: DIFF {ds}"; pure false

end CheckInst

#eval do
  let a ← CheckInst.check "addALR" "out3/add/add.inst.json" AddALR.addALR
  let b ← CheckInst.check "jpX" "out3/jp/jp.inst.json" JpALR.jpX
  unless a && b do throw (IO.userError "instance literal check FAILED")
