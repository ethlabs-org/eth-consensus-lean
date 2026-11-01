module
public import AvailableChainPCSAProofs.Proofs.Clean.SnapshotContents
public import AvailableChainPCSAProofs.Proofs.Clean.CarriedPCs
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps

public section

/-! C6 ViewOrigins: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A vote tick cannot also be a freeze tick. -/
theorem pcsa_vote_ne_freeze (p : Params) (s r : Slot) :
    SA.voteTime p.toParams s ≠ SA.freezeTime p.toParams r := by
  intro he
  change 4 * p.Δ * (s : Int) + p.Δ = 4 * p.Δ * (r : Int) + 3 * p.Δ at he
  have hp := p.deltaPos
  rcases le_or_gt s r with h | h
  · have hh : (s : Int) ≤ (r : Int) := Int.ofNat_le.mpr h
    nlinarith
  · have hh : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast h
    nlinarith
/-- Vote ticks leave the frozen PC source lists unchanged. -/
theorem pcsa_vote_snapshot (p : Params) (st : State p.n) (s : Slot) :
    (clock p st (SA.voteTime p.toParams s)).pcSnapshot = st.pcSnapshot := by
  have he : (clock p st (SA.voteTime p.toParams s)).pcSnapshot =
      (clockPre p st (SA.voteTime p.toParams s)).pcSnapshot := by
    delta clock
    dsimp only
    split
    · exact gateStep_snapshot _ _ _
    · rfl
  rw [he, clockPre_snapshot]
  dsimp only
  split
  · rename_i hf
    exact (pcsa_vote_ne_freeze p s _
      (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hf).2)).elim
  · rfl
/-- Clock updates preserve valid carried-PC metadata. -/
theorem pcsa_clock_carriedPCs (p : Params) (st : State p.n) (t : Time) (s : Slot) :
    carriedPCs (clock p st t) s = carriedPCs st s := by
  delta carriedPCs
  rw [pcsa_clock_proposals]
  congr 1
  funext C
  delta pcValid activeCompatible
  rw [pcsa_clock_blocks, pcsa_body_clock_fg]
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Every selected vote PC has an honest ack on its target strictly before the vote. -/
theorem pcsa_voterPC_honest_ack_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (hx : x ∈ rho.honest) (s : Slot)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) (C : PC p.n)
    (hC : voterPC p (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.voteTime p.toParams s)) s = some C) :
    ∃ y, HonestAckAt p c E rho y C.slot C.target ∧
      SA.earlyTime p.toParams C.slot < SA.voteTime p.toParams s := by
  have hm := (List.mem_filter.mp (bestPC_mem _ C hC)).1
  rcases List.mem_append.mp hm with hfrozen | hcarried
  · have he : pcSnapshotAt (clock p (V2.D.Run.stateBefore E rho k x).st
        (SA.voteTime p.toParams s)) (s - 1) =
        pcSnapshotAt (V2.D.Run.stateBefore E rho k x).st (s - 1) := by
      delta pcSnapshotAt
      rw [pcsa_vote_snapshot]
    rw [he] at hfrozen
    obtain ⟨a, ha, _, hpc⟩ := pcsa_snapshot_pc_origin E rho k x (s - 1) C hfrozen
    exact (pcsa_pc_honest_ack_before E rho h hFault a x hx _
      ((Nat.le_of_lt ha).trans hk) C hpc).2
  · rw [pcsa_clock_carriedPCs] at hcarried
    exact pcsa_carriedPC_honest_ack_before E rho h hFault k x hx s _ hk C hcarried
end AvailableChain.PCSA.Run

end
