/-
  Nock/RedTeam/Batch4873Thm54JSibNonVac.lean

The run (Goldilocks `p`, `K = KC`, `δ = deltaF`, `b = powerBasis3`):
  * template `T1`: one argument at axis `3` (type `F`), body `var 0` (the jet returns the subject's tail);
  * registry `RgB := ofCompiled p _ (fun _ => T1) [7]` (the jet `7 ↦ compile p T1`);
  * claim `*[3 [8 [4 [1 (p−1)]] [11 [%wild [1 7]] (compile p T1)]]] = 3`.

  The `8` pushes the increment `(p − 1) + 1 = p` (a BIG atom that ARISES MID-RUN: every claim leaf is `< p`, so
  `hclA` holds) onto the subject; the jet is then called on the subject `[p 3]`.  Its argument axis `3` walks the
  tail, whose off-path sibling (the head) is the big atom `p`: `ChainSibsOK p [true] [p 3]` fails, so `JSibOK` fails
  (`not_jsib`).  Every binder of the new `complJ8_closed` (`hpG hax hop5 hclA hleaf hwalk hwalkA hRt hregAx h31`) is a
  closed lemma below, and `complJ8_closed_bigSib` / `complJ8_closed_bigSib_figure` carry no hypothesis.

  Labels: everything below is kernel-checked (`#print axioms` at the end; std3).
-/
import Nock.RedTeam.Batch4842Thm54J8ComplClose

set_option autoImplicit false

namespace Nock.RedTeam.Batch4873

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.Jet.Autogen (Tpl HasTy compile)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (factRC charPKC algRC card_KC)

noncomputable section

/-! ## 1. The template, the registry and the run -/

/-- The template: one field argument at axis `3`, returned as is. -/
def T1 : Tpl where
  k := 1
  ax := ![3]
  inTy := fun _ => .F
  outTy := .F
  body := .var 0

theorem T1_wt : T1.WellTyped Nock.Field.p := HasTy.var _

/-- The template table. -/
abbrev RtB : ℕ → Tpl := fun _ => T1

/-- The registry: jet `7 ↦ compile p T1`. -/
def RgB : Nock.Jet.VerifiedRegistry :=
  Nock.Jet.VerifiedRegistry.ofCompiled Nock.Field.p (by decide) RtB [7] (fun _ _ => T1_wt)

/-- The claim subject. -/
def sB : Noun := .atom 3
/-- The jet's subject `[p 3]`: the big head `p` is the off-path sibling of the argument axis `3`. -/
def sJ : Noun := .cell (.atom Nock.Field.p) sB
/-- `[1 (p − 1)]`. -/
def fQ : Noun := .cell (.atom 1) (.atom (Nock.Field.p - 1))
/-- `[4 [1 (p − 1)]]`: the increment to the big atom `p`. -/
def fI : Noun := .cell (.atom 4) fQ
/-- The clue `[1 7]`: its value is the jet key `7`. -/
def fC : Noun := .cell (.atom 1) (.atom 7)
/-- `[11 [%wild [1 7]] (compile p T1)]`: the jet call. -/
def fJ : Noun := .cell (.atom 11) (.cell (.cell (.atom Nock.Jet.wildTag) fC) (compile Nock.Field.p T1))
/-- The claim formula `[8 [4 [1 (p−1)]] fJ]`. -/
def fB : Noun := .cell (.atom 8) (.cell fI fJ)

def tQ : NTree SkelX := mkX .s1 sB fQ (.atom (Nock.Field.p - 1)) []
def tI : NTree SkelX := mkX .s4 sB fI (.atom Nock.Field.p) [tQ]
def tC : NTree SkelX := mkX .s1 sJ fC (.atom 7) []
def tJ : NTree SkelX := mkX .s11j sJ fJ sB [tC]
/-- The generated tree. -/
def tB : NTree SkelX := mkX .s8 sB fB sB [tJ, tI]

theorem jetB : jetHit RgB.R (.atom Nock.Jet.wildTag) (.atom 7) (compile Nock.Field.p T1) sJ = some sB := by
  decide +kernel

theorem gC : genX RgB.R 1 sJ fC = some (tC, .atom 7) := rfl

theorem gI : genX RgB.R 2 sB fI = some (tI, .atom Nock.Field.p) := rfl

theorem gJ : genX RgB.R 2 sJ fJ = some (tJ, sB) := by
  have h := gC
  simp only [genX] at h
  simp only [genX, fJ, genComputeSkeletonX, h, jetB]
  rfl

theorem genB : genX RgB.R 3 sB fB = some (tB, sB) := by
  have h1 := gI
  have h2 := gJ
  simp only [genX] at h1 h2
  simp only [genX, fB, genComputeSkeletonX, h1]
  rw [show Noun.cell (.atom Nock.Field.p) sB = sJ from rfl, h2]
  rfl


/-! ## 2. The rows and the honest data -/

theorem bfsB : bfsForest [tB] = [tB, tJ, tI, tC, tQ] := by
  simp [bfsForest, tB, tJ, tI, tC, tQ, mkX]

theorem rowsB : ComplJ8Data.rowsOfT tB =
    #[rowOfSkelX tB.label, rowOfSkelX tJ.label, rowOfSkelX tI.label, rowOfSkelX tC.label,
      rowOfSkelX tQ.label] := by
  simp only [ComplJ8Data.rowsOfT, bfsB]; rfl

/-- The run's honest J-8 data. -/
abbrev DB := j8DataOf Nock.Field.p RgB RtB genB

theorem callsB : DB.calls = [(7, sJ)] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tB) = _
  rw [rowsB]; decide +kernel

theorem readsB : DB.reads = [] := by
  show Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tB) = []
  rw [rowsB]; decide +kernel

theorem preadsB : DB.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tB) = []
  rw [rowsB]; decide +kernel

theorem rootsB : DB.roots = Nock.V1J8.Gen.rootsOf ⟨sB, fB, sB⟩ (ComplJ8Data.rowsOfT tB) ++
    ComplJ8Data.jNounsP Nock.Field.p RtB [7] [(7, sJ)] := by
  show Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT tB) ++
    ComplJ8Data.jNounsP Nock.Field.p RtB (List.map Prod.fst DB.calls).dedup DB.calls = _
  rw [callsB]; rfl

theorem hleafB : ComplJ8Walk.RootsLeafOK DB.roots := by
  rw [rootsB, rowsB]
  show ∀ x ∈ _, Noun.leaves x ≤ 2 ^ 109
  decide +kernel

theorem hwalkB : ComplJ8Walk.WalkDepthOK DB.reads := by
  rw [readsB]; intro r hr; simp [VclL.pathReads] at hr

theorem hwalkAB : ComplJ8Walk.WalkDepthOK DB.preads := by
  rw [preadsB]; intro r hr; simp [VclL.pathReads] at hr

theorem cellsB_len : DB.cells.length ≤ 2 ^ 31 := by
  show (Nock.V1J8.Gen.cellsOfRoots DB.roots).length ≤ 2 ^ 31
  rw [rootsB, rowsB]
  decide +kernel

theorem jrowsB_len : DB.jrows.length ≤ 2 ^ 31 := by
  rw [ComplJ8Jet.j8DataOf_jrows]
  simp only [ComplJ8Data.mvFixP, List.length_map]
  show (Nock.Jet.ChipJ8.honestJ8G _ RtB (List.map Prod.fst DB.calls).dedup DB.calls).length ≤ 2 ^ 31
  rw [callsB]
  decide +kernel

theorem bigsB : DB.bigs = [Nock.Field.p] := by
  show ComplJ8Data.bigsP _ DB.roots (ComplJ8Data.rowsOfT tB) = _
  rw [rootsB, rowsB]
  unfold ComplJ8Data.bigsP
  rw [show (List.filter _ _).dedup = [Nock.Field.p] by decide +kernel]
  simp

theorem limbsB : Nock.Atoms.limbs Nock.Field.p = [1, Nock.Atoms.B - 1] := by
  have h := ComplJ8BigBound.limbs_two (a := Nock.Field.p) (by simp [Nock.Atoms.p]) (by simp [Nock.Atoms.p])
  rw [h]; simp [Nock.Atoms.p]

theorem acsB_len : DB.acs.length ≤ 3 := by
  show (ComplJ8Data.acsP _ DB.bigs _).length ≤ 3
  rw [bigsB]
  unfold ComplJ8Data.acsP
  simp only [List.foldl_cons, List.foldl_nil, limbsB]
  have hsp : Nock.V1J8.Gen.spineOf [1, Nock.Atoms.B - 1] = [Nock.V1J8.Gen.combOf [1, Nock.Atoms.B - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [1, Nock.Atoms.B - 1]] =
      [Nock.V1J8.Gen.combOf [1, Nock.Atoms.B - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [1, Nock.Atoms.B - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem h31B : Rows31 DB := by
  intro x hx
  simp only [sizesJ8, nVOf, preadsB, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hW : (VclL.GenWalk.walkRows DB.cells DB.reads).length ≤ 2 ^ 31 := by
    rw [readsB]
    have := VclL.GenWalk.walkRows_length_le DB.cells []
    simp [VclL.pathReads] at this
    omega
  have hB : (bfsForest [DB.t]).length = 5 := by
    show (bfsForest [tB]).length = 5
    rw [bfsB]; rfl
  have hC := cellsB_len
  have hA := acsB_len
  have hJ := jrowsB_len
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## 3. The binders -/

theorem inT_Q (u : NTree SkelX) (h : InTree tQ u) : u = tQ := by
  cases h with
  | here => rfl
  | sub hs _ => simp [tQ, mkX] at hs

theorem inT_C (u : NTree SkelX) (h : InTree tC u) : u = tC := by
  cases h with
  | here => rfl
  | sub hs _ => simp [tC, mkX] at hs

theorem inT_I (u : NTree SkelX) (h : InTree tI u) : u = tI ∨ u = tQ := by
  cases h with
  | here => exact Or.inl rfl
  | sub hs h' =>
    rename_i s'
    have e : s' = tQ := by simpa [tI, mkX] using hs
    subst e; exact Or.inr (inT_Q _ h')

theorem inT_J (u : NTree SkelX) (h : InTree tJ u) : u = tJ ∨ u = tC := by
  cases h with
  | here => exact Or.inl rfl
  | sub hs h' =>
    rename_i s'
    have e : s' = tC := by simpa [tJ, mkX] using hs
    subst e; exact Or.inr (inT_C _ h')

theorem inT_B (u : NTree SkelX) (h : InTree tB u) :
    u = tB ∨ u = tJ ∨ u = tC ∨ u = tI ∨ u = tQ := by
  cases h with
  | here => exact Or.inl rfl
  | sub hs h' =>
    rename_i s'
    have e : s' = tJ ∨ s' = tI := by simpa [tB, mkX] using hs
    rcases e with e | e <;> subst e
    · rcases inT_J _ h' with h | h <;> simp [h]
    · rcases inT_I _ h' with h | h <;> simp [h]

theorem haxB : ComplJ8.ProgAxOK Nock.Field.p tB := by
  intro u hu
  rcases inT_B u hu with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold ComplJ8.AxRowX
    simp [rowOfSkelX, tB, tJ, tI, tC, tQ, mkX, fJ, fB, fI, fC, fQ, VclL.hdN, VclL.tlN, kidE, SkelX.row]
  all_goals decide

theorem hop5B : ComplJ8.ProgOp5OK Nock.Field.p tB := by
  intro u hu
  rcases inT_B u hu with rfl | rfl | rfl | rfl | rfl
  all_goals
    intro h
    simp [rowOfSkelX, tB, tJ, tI, tC, tQ, mkX] at h

theorem calledB (id : ℕ) (h : id ∈ ComplJ8Jet.CalledIds tB) : id = 7 := by
  obtain ⟨u, hu, hst, hid⟩ := h
  rcases inT_B u hu with rfl | rfl | rfl | rfl | rfl
  all_goals simp [rowOfSkelX, tB, tJ, tI, tC, tQ, mkX, fJ, VclL.hdN, VclL.tlN, kidE, SkelX.row] at hst hid
  all_goals omega

theorem hRtB : ∀ id ∈ ComplJ8Jet.CalledIds tB,
    RgB.R id = some ⟨(RtB id).toTemplate Nock.Field.p, compile Nock.Field.p (RtB id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (RtB id) = true ∧ (RtB id).WellTyped Nock.Field.p := by
  intro id hid
  obtain rfl := calledB id hid
  exact ⟨by simp [RgB, Nock.Jet.VerifiedRegistry.ofCompiled], by decide, T1_wt⟩

theorem hregAxB : ∀ id ∈ ComplJ8Jet.CalledIds tB, ∀ i, (RtB id).ax i < Nock.Field.p := by
  intro id _ i
  fin_cases i
  show 3 < Nock.Field.p
  decide

theorem hclAB : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ sB fB sB) k).leafList, v < Nock.Field.p := by
  decide +kernel


/-! ## 4. The run is outside the retired binder `JSibOK` -/

/-- **The old binder `hsib` FAILS at this run**: the call `(7, [p 3])` reads axis `3`, whose off-path sibling (the
head) is the big atom `p`. -/
theorem not_jsib : ¬ ComplJ8OfBalG.JSibOK (p := Nock.Field.p) RtB DB := by
  intro h
  have h1 := h (7, sJ) (by rw [callsB]; exact List.mem_singleton_self _) ⟨0, by decide⟩
  have hax : Nock.Jet.ChipJ8.axPath ((RtB 7).ax ⟨0, by decide⟩) = [true] := by decide
  rw [hax] at h1
  exact absurd (h1.1 Nock.Field.p rfl) (lt_irrefl _)

/-- The atom-subject binder `hsubj` holds here (the subject is a cell); the run is outside the old domain through
`JSibOK` alone. -/
theorem jsubj_holds : ComplJ8OfBalJ.JSubjOK (p := Nock.Field.p) DB := by
  intro cl hcl v hv
  rw [callsB, List.mem_singleton] at hcl
  subst hcl; cases hv

/-- **Negative control at the run**: the OLD honest J rows (`honestJ8 cs`, handle `hOf`) and the NEW ones
(`honestJ8G (hJd …)`, the cell table's handle) differ in the left-child kind column: the `sl` read row of the
chain carries kind `0` (old, `hOf` reduces `p` to `(0, p mod p)`) against kind `2` (new, an atom-table root). -/
theorem kinds_old_ne_new :
    (Nock.Jet.ChipJ8.honestJ8 (p := Nock.Field.p) DB.cells RtB DB.regs DB.calls).map (fun r => r.w.kL) ≠
      (Nock.Jet.ChipJ8.honestJ8G (p := Nock.Field.p) (ComplJ8Data.hJd Nock.Field.p DB.cells DB.acs) RtB DB.regs
        DB.calls).map (fun r => r.w.kL) := by
  show (Nock.Jet.ChipJ8.honestJ8 (p := Nock.Field.p) DB.cells RtB (List.map Prod.fst DB.calls).dedup
      DB.calls).map (fun r => r.w.kL) ≠
    (Nock.Jet.ChipJ8.honestJ8G (p := Nock.Field.p) (ComplJ8Data.hJd Nock.Field.p DB.cells DB.acs) RtB
      (List.map Prod.fst DB.calls).dedup DB.calls).map (fun r => r.w.kL)
  rw [callsB]
  decide +kernel

/-! ## 5. `complJ8_closed` at the run, nothing carried -/

/-- The run's honest record (every family). -/
abbrev BB := ComplJ8Closed.BRunA deltaF powerBasis3 RtB genB rfl h31B

open Classical in
/-- **`complJ8_closed` (no `hsib`, no `hsubj`) at the jet-bearing big-sibling run**
`*[3 [8 [4 [1 (p−1)]] [11 [%wild [1 7]] (compile p T1)]]] = 3`, every binder discharged. -/
theorem complJ8_closed_bigSib :
    (∀ χ, BB.Good χ → AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BB.Pb RgB.R
      (ComplJ8.cJ sB fB sB) χ (BB.M χ) (BB.tr χ) BB.rows BB.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BB.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BB.epsC) ∧
    StJ8 BB.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sB fB sB) ∧
    (Fintype.card KC = VclL.Events.cK →
      BB.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BB.Pb RgB.R
        (ComplJ8.cJ sB fB sB) χ (BB.M χ) (BB.tr χ) BB.rows BB.g) :=
  ComplJ8Closed.complJ8_closed deltaF powerBasis3 RtB genB rfl haxB hop5B hclAB hleafB hwalkB hwalkAB
    hRtB hregAxB h31B

/-- **The figure at the run, hypothesis-free**: `ε_c < 2^-120` and an accepting coin. -/
theorem complJ8_closed_bigSib_figure :
    BB.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BB.Pb RgB.R
        (ComplJ8.cJ sB fB sB) χ (BB.M χ) (BB.tr χ) BB.rows BB.g :=
  complJ8_closed_bigSib.2.2.2.2 card_KC

/-- **F3 in one statement**: the new `complJ8_closed` gives an accepting coin at a run where the retired binder
`JSibOK` fails. -/
theorem bigSib_nonvacuous :
    ¬ ComplJ8OfBalG.JSibOK (p := Nock.Field.p) RtB DB ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BB.Pb RgB.R
        (ComplJ8.cJ sB fB sB) χ (BB.M χ) (BB.tr χ) BB.rows BB.g :=
  ⟨not_jsib, complJ8_closed_bigSib_figure.2⟩

end

end Nock.RedTeam.Batch4873

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed
#print axioms Nock.RedTeam.Batch4873.genB
#print axioms Nock.RedTeam.Batch4873.h31B
#print axioms Nock.RedTeam.Batch4873.not_jsib
#print axioms Nock.RedTeam.Batch4873.jsubj_holds
#print axioms Nock.RedTeam.Batch4873.kinds_old_ne_new
#print axioms Nock.RedTeam.Batch4873.complJ8_closed_bigSib
#print axioms Nock.RedTeam.Batch4873.complJ8_closed_bigSib_figure
#print axioms Nock.RedTeam.Batch4873.bigSib_nonvacuous
