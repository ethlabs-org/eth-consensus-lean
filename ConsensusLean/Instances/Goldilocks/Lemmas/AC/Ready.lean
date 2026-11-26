module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.VoteBranch

public section

/-! # Goldilocks AC: what an honest vote's call shows

The read point of an honest vote has the block stamps of the state its call leaves
(`readPoint_blockStamp_eqU`), and a vote cast before `t_s + Δ` is ready at its read point
(`cast_readyU`, the `vote_ready` branch of `try_vote`). -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro}

/-- The read point of an honest vote has the block stamps of the state its call leaves. With the
unlock given. -/
theorem readPoint_blockStamp_eqU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    e.readPoint.blockStamp = (tr.post i).blockStamp := by
  rw [post_of_castAtU hr hy hc, AC.optimistic_blockStamp,
    AC.admitVote_blockStamp]

/-- A block already held in an earlier frame has an early read-point stamp. The
stamp cases include restart replay; unique acceptance forbids a later overwrite. From starts up
to the vote permission. -/
theorem readPoint_blockStamp_lt_of_earlier_frame {ini}
    (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n} (hy : y ∈ H)
    {a i : Nat} {ell₀ ell : ACLabel (goldilocksAC sp FGP ro)}
    (ha : tr.CallAt y a ell₀) {e : Em sp FGP} (hc : CastAt tr y i ell e)
    {Q : Blk sp.n FGP} (hQa : Q ∈ ell₀.frame.tree) (hQi : Q ∈ ell.frame.tree)
    (hat : tr.time a < freeze sp e.msg.slot)
    (hrs : ∀ r ≤ i, tr.RestartAt y r → tr.time r < freeze sp e.msg.slot) :
    e.readPoint.blockStamp Q.root < ETime.of (freeze sp e.msg.slot) := by
  rw [readPoint_blockStamp_eqU hr.toU hy hc]
  rcases stamp_casesU sp (wm := WriteMode.parent sp) hr.toU hini hy i ell hc.1 Q hQi with
    h | ⟨k, -, hk, h⟩ | ⟨r, hri, hrst, h⟩
  · rw [h]; exact WithBot.bot_lt_coe _
  · have hka : k ≤ a := by
      by_contra hn
      exact (accept_new sp hr hy hk).2 a (by omega) ell₀ ha hQa
    rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ((hr.time_mono hka).trans_lt hat))
  · rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hrs r hri hrst))

/-- **An early vote is ready**: an honest vote cast before `t_s + Δ` is ready at its read point: its
frame holds a block of its slot, and every declaration of a slot-`s` proposal of its frame is
counted in the pools of the read point (`vote_ready`). With the unlock given. -/
theorem cast_readyU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (ht : tr.time i < sp.ts e.msg.slot + sp.Δ) :
    voteReady sp e.readPoint ℓ.frame e.msg.slot := by
  have hb := voteBranchAt_iff.1 (voteBranchAt_of_castAtU hr hy hc)
  rw [(castAt_specU hr hy hc).2.1] at ht ⊢
  by_contra hn
  exact hb.2.2.2.2.2.1 ⟨ht, Or.inr hn⟩

end Consensus.Goldilocks.AC

end
