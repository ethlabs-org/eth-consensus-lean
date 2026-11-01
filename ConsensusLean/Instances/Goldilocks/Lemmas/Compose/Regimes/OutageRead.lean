module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Conditional post-stop read certificates -/

namespace Consensus.Goldilocks.Compose

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An admitted, resolved honest batch extending a held prefix gives a strict majority
in the read's selected latest view. Delivery and head-stamp production remain explicit. -/
theorem read_majority_of_honest_batch (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {w : Fin sp.n} (hw : w ∈ H) {i : Nat} {t : Time}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 = s)
    (hall : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hBt : B ∈ (Node.frame (tr.state w i)).tree)
    (hdeliv : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      e.msg ∈ (tr.state w i).ac.pool s ∧
      ∃ Hd ∈ (Node.frame (tr.state w i)).tree, Hd.root = e.msg.head ∧
        (tr.state w i).ac.blockStamp Hd.root < ⊤)
    (hfb : tr.FaultBound H (sp.ts s + sp.Δ)) :
    (SA.voters (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state w i))
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 B).ncard := by
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hst := projAC_state hrun.toLocalRun hw i
  let SX := {x | x ∈ H ∧ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = s}
  let V := SA.voters (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1.votes
  let S := SA.supporters (Node.frame (tr.state w i))
    (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1
    (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 B
  have hsupport : V ∩ H ⊆ S := by
    intro x hx
    apply latest_honest_supporter_of_target_votes hrun hnc hw hBt hs.symm _ _ x hx.1 hx.2
    · intro x hx k _ e hv he
      exact hall x hx k e hv he
    · intro x hx k e hv he Hd hHd hHdr _
      obtain ⟨-, Hd', hHd', hHdr', hstamp⟩ := hdeliv x hx k e hv he
      have heq : Hd = Hd' := hr.localRun.coherent.1 hHd ⟨w, hw, i, hHd'.1⟩
        (hHdr.trans hHdr'.symm)
      subst Hd'
      exact ⟨hHd', by rw [hst]; exact hstamp⟩
  have hSX : SX ⊆ V ∩ H := by
    rintro x ⟨hx, k, e, hv, he⟩
    obtain ⟨ell, hc, hem⟩ := hv
    have hval := (SA.castAt_spec hr.localRun hx ⟨hc, hem⟩).1
    have hp := (hdeliv x hx k e ⟨ell, hc, hem⟩ he).1
    rw [← hst] at hp
    exact ⟨⟨e.msg, mem_latest_votes hrun hnc hw hs.symm hp, hval⟩, hx⟩
  have hcount : Hᶜ.ncard < SX.ncard := by
    refine hfb.trans_le (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, haw, hj⟩
    obtain ⟨k, e, hv, he, -⟩ := vote_of_awake_joined hrun hnc hx haw hj
    exact ⟨hx, k, e, hv, he⟩
  have h₁ := Set.ncard_le_ncard (hSX.trans hsupport) (Set.toFinite _)
  have h₂ := Set.ncard_le_ncard hsupport (Set.toFinite _)
  have h₃ : V.ncard ≤ (V ∩ H).ncard + Hᶜ.ncard := by
    refine (Set.ncard_le_ncard (fun x hx => ?_) (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    by_cases hxH : x ∈ H
    · exact Or.inl ⟨hx, hxH⟩
    · exact Or.inr hxH
  change V.ncard < 2 * S.ncard
  omega

end Consensus.Goldilocks.Compose
