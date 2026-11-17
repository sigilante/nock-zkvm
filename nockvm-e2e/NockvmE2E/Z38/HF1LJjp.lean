import NockvmE2E.Z38.LinkJ9ALJjp
import Nock.RedTeam.Batch4939Thm54J9ALTplJetToy

/-!
# `HF1LJ` at the `jp` run (`XJ`), from the honest template-jet generator

`HF1LJ XJ` (Z38/HF1LJ.lean, frozen) is discharged from the nock library's `honestTplUnif` (Batch4939). That lemma
says: at the generator's good coin, for every common orbit `⟨h, ω⟩` with `orderOf ω = 3 * 2^h` and
`nRowsTpl ≤ 3 * 2^h`, the record is valid and `AcceptsJ9AL`. We take `h = XJ.k + 1` and `ω = ofU64 XJ.hGen`, so the
orbit is exactly `orbSh XJ`. The order comes from the executed shape gate (`hord_jp`), and the row bound from
`nRowsTpl = 159 ≤ 768`. Batch4939's `catJ`, `sJ` and `fJP` are literal copies of ours (Z38/CatJ.lean, Z38/HF1LJ.lean),
and the bridge checks they agree by `rfl`. Not zero-knowledge.
-/

namespace NockvmE2E.Z38.HF1LJjp
open NockvmE2E.Z38.LinkJ9ALJjp (hord_jp)
open NockvmE2E.Z38.E2EJ9ALJToy (XJ)
open NockvmE2E.J9AL.LinkJ9ALBridge (orbSh)
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9ALChips

theorem catJ_eq : Nock.RedTeam.Batch4939.catJ = NockvmE2E.Z38.CatJ.catJ := rfl
theorem sJ_eq : Nock.RedTeam.Batch4939.sJ = NockvmE2E.Z38.HF1LJ.sJ := rfl
theorem fJ_eq : Nock.RedTeam.Batch4939.fJP = NockvmE2E.Z38.HF1LJ.fJ := rfl

theorem orbSh_eq : orbSh XJ = Nock.RedTeam.Batch4939.orbU (XJ.k + 1) (Nock.TraceGenExe.Gold.ofU64 XJ.hGen) := rfl

theorem hn_jp : Nock.RedTeam.Batch4939.nRowsTpl ≤ 3 * 2 ^ (XJ.k + 1) := by
  have h8 : XJ.k + 1 = 8 := by decide +kernel
  rw [h8]; exact Nock.RedTeam.Batch4939.nRowsTpl_le_768

/-- **`HF1LJ` at `XJ`**, given only the executed shape gate. -/
theorem hf1lj_jp (hsh : shapeOkF famJ9AL XJ = true) : NockvmE2E.Z38.HF1LJ.HF1LJ XJ := by
  obtain ⟨χe, I, hI, hall⟩ := Nock.RedTeam.Batch4939.honestTplUnif
  rw [catJ_eq, sJ_eq, fJ_eq] at hI
  obtain ⟨hv, hacc⟩ := hall (XJ.k + 1) (Nock.TraceGenExe.Gold.ofU64 XJ.hGen) (by omega) (hord_jp hsh) hn_jp
  rw [catJ_eq] at hacc
  -- `orbSh XJ` and `orbU (XJ.k+1) (ofU64 XJ.hGen)` agree by `rfl` (`orbSh_eq`), so `hv`/`hacc` fit as they are
  exact ⟨χe, I, hI, hv, hacc⟩

/-- **`jp_air_closed`**: the AIR half of non-vacuity at `jp` with `HF1LJ` discharged. Only the executed gate `hsh`
remains, as at J-9 A/AL. -/
theorem jp_air_closed (hsh : shapeOkF famJ9AL XJ = true) :
    ∃ χ M tr,
      NockvmE2E.J9AL.InstJ9AL.AccJ9AL (NockvmE2E.Z38.IfaceJ.DX9LJ XJ hsh NockvmE2E.Z38.LinkJ9ALJjp.hlen_jp
        (NockvmE2E.J9A.RunGate9L.kOfL XJ) (NockvmE2E.J9A.RunGate9L.kVOfL XJ) NockvmE2E.Z38.JpClaim.cJ) χ M tr ∧
      NockvmE2E.J9AL.InstJ9AL.PubP9AL (NockvmE2E.Z38.IfaceJ.DX9LJ XJ hsh NockvmE2E.Z38.LinkJ9ALJjp.hlen_jp
        (NockvmE2E.J9A.RunGate9L.kOfL XJ) (NockvmE2E.J9A.RunGate9L.kVOfL XJ) NockvmE2E.Z38.JpClaim.cJ) χ
        (M, fun j => Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9.pubVJ9 Nock.TraceGenExe.deltaF Nock.TraceGenExe.powerBasis3
          NockvmE2E.Z38.JpClaim.cJ M.m M.ρ M.ρS χ j) :=
  NockvmE2E.Z38.LinkJ9ALJjp.jp_air hsh (hf1lj_jp hsh)

end NockvmE2E.Z38.HF1LJjp

#print axioms NockvmE2E.Z38.HF1LJjp.hf1lj_jp
#print axioms NockvmE2E.Z38.HF1LJjp.jp_air_closed
