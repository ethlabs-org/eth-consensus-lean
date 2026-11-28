module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal and recipient frames

Frame uniqueness, relay and view agreement for the post-reset duty suppliers. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF a : Time}

/-- An honest designated actual proposal is the unique block of its positive slot
in every honest frame, without reset or readiness premises. -/
theorem proposal_frame_unique
    {ini} (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hcall : tr.projAC.CallAt y j ell) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hac.localRun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPprop, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hpH hdesignated hactual hPs
  rw [← hdesignated] at hPprop hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (AC.accept_new sp hr hpH ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hQf : AC.HonestFrameBlock tr.projAC H Q := ⟨y, hy, j, ell, hcall, hQ⟩
  have hroot : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hy j)
    obtain rfl := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hcall).2 hQ)
      ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block P Q ⟨p, hpH, ja, ellp, hcp, hPm⟩ hQf (hPprop ▸ hpH)
    (by rw [hPprop, hac.honest.proposer Q hQf hroot, hQu, hdesignated])
    (by rw [hPs, hQu])).symm

end Consensus.Goldilocks.Healing

end
