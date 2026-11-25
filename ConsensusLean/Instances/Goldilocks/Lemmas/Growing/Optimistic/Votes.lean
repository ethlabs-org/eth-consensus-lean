module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Held

public section

/-! # Optimistic inclusion: the honest committee votes for the proposal

For the proposal `P` of slot `s` by a proposer honest at `t_s + Δ`, every member of the slot-`s`
committee honest, awake and joined at `t_s + Δ` casts a slot-`s` vote by then
(`vote_of_awake_joined_at`, the committee gate `CommitteeFacts.hGate`), and every honest slot-`s`
vote names `P` (`honest_votes_eq_proposal_at_update_at`).

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **B1: the honest committee votes for the proposal.** A member of the slot-`s` committee
honest, awake and joined at `t_s + Δ` casts, while honest and by `t_s + Δ`, a slot-`s` vote whose
head is the proposal `P` of a proposer honest at `t_s + Δ`. -/
theorem committee_votes_proposal_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b) {x : Fin sp.n} (hx : x ∈ H (sp.ts s + sp.Δ))
    (hxK : x ∈ K.committee s) (hw : tr.awake x (sp.ts s + sp.Δ))
    (hj : tr.JoinedAt x (sp.ts s + sp.Δ)) :
    ∃ j e, HVoteAt tr H x j e ∧ e.msg.slot = s ∧ e.msg.head = P.root ∧
      tr.time j ≤ sp.ts s + sp.Δ := by
  have hd := ts_add_delta_nonneg (sp := sp) s
  obtain ⟨j, e, hv, hes, hjt⟩ := vote_of_awake_joined_at hrun hnc hx
    (fun i hi => (hKB.hGate _ hd x hx i hi s).2 hxK) hw hj
  exact ⟨j, e, hv, hes, honest_votes_eq_proposal_at_update_at hrun hnc hsync hB hinv hp hP hPs
    hsb hKB hBK x j e hv hes, hjt⟩

end Consensus.Goldilocks.Compose.Growing
