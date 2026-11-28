module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window

public section

/-! # The viable witness of a shadow window (the relocated `hJ`)

The stock report-renewal and regular-report suppliers (`FollowWrite`, `FollowLaterBoundary`,
`FollowHeads`, `RegularLater`) carry a witness `Q ⪰ X` of the floor (`floor ≤ σ(Q).h`) and a
separate `kindJ → J ⪯ X` for the followed block `X`. Over the shadow frame `X ∈ viableTree` needs
only `F ⪯ X ⪯ Q` with `Q` a P-U viable head, so the `J` clause moves from `X` to the witness `Q`
(manager's decision; Lane R found the same on V-B8). The stock `kindJ → J ⪯ X` with `kindJ := isTop`
fails on a paper trace in a top-contest window (an optimistic lock on a contest-branch head); it is
not a V-B fact and no conclusion here depends on it.

A viable head of a node's shadow frame inside a `Generic.FrameWindow … M isTop J` carries exactly:

* `M − 1 ≤ σ(Q).h`;
* `isTop → σ(Q).h = M − 1 → J ⪯ Q`.

`viable'_witness` is the store form; `early_witness_viable'` reads it at an AC call of a node honest
at it, with `J ⪯ Q` inside the blocks held while honest. Carrying the witness to later cuts of the
window is `viableHead_persists'` (V-B4, Lane W), which the consumers use separately. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- **The P-U witness clauses of a viable block**, for the store's own `h_max = M`, top status and
justified block. -/
theorem viable_witness {M : Nat} {isTop : Prop} {J : NodeBlock P ACP} (hM : st.hmax = M)
    (htop : st.hmax = st.hj + 1 ↔ isTop) (hJ : isTop → st.J = J) {Q : NodeBlock P ACP}
    (hQ : st.IsViable Q) :
    M - 1 ≤ (st.σ Q.root).h ∧ (isTop → (st.σ Q.root).h = M - 1 → st.Anc J Q) := by
  rw [isViable_iff] at hQ
  refine ⟨by rcases hQ with h | ⟨h, -⟩ <;> omega, fun ht he => ?_⟩
  have hjm := htop.2 ht
  rcases hQ with h | ⟨-, hgap | hanc⟩
  · omega
  · omega
  · exact hJ ht ▸ hanc

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **The early viable witness** at an AC call of a node honest at it, inside a shadow window:
a viable head `Q` of the call's frame (the shadow frame) is at least `M − 1` high, and in a top
window a witness at `M − 1` extends `J` among the blocks held while honest. -/
theorem early_witness_viable
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {lo hi : Time} {M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H lo hi M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a)) (hlo : lo ≤ tr.time a)
    (hhi : tr.time a ≤ hi) {ellw : ACLabel (goldilocksNode sp)}
    (hcw : tr.projAC.CallAt w a ellw) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ellw.frame.viableHeads) :
    M - 1 ≤ ((tr.state w a).fg.σ Q.root).h ∧
      (isTop → ((tr.state w a).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q) := by
  rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_viableHeads] at hQ
  obtain ⟨hQt, -, hv⟩ := hQ
  obtain ⟨h1, h2⟩ := (tr.state w a).fg.viable_witness (hwin.M_eq w a hw hlo hhi)
    (hwin.top_iff w a hw hlo hhi) (hwin.root_eq w a hw hlo hhi) hv
  refine ⟨h1, fun ht he => (h2 ht he).mono fun X hX => ?_⟩
  exact ⟨w, a, tr.time a, hrun.time_nonneg a, fun k hk => hrun.time_mono hk.le, hw, hX⟩

end Consensus.Goldilocks.Shadow.PU.Growing

end
