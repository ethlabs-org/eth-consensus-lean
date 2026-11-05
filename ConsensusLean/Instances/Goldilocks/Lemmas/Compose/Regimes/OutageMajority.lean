module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare

public section

/-! # Outage: the extending majority at a label (O4, S5-V)

The count form of S5-V, in which O4 consumes S5.

* `ExtendingCasters tr H B q`: the honest slot-`q` casters whose vote extends `B`;
* `Opponents tr H B q`: the faulty validators and the honest slot-`q` casters whose vote does not
  extend `B`;
* `ExtendingMajority tr H B q`: the extending casters outnumber the opponents;
* `ExtendingMajority.anti`: the majority for `B` is a majority for every block below `B`;
* `extendingMajority_of_all` (L4): when every honest slot-`q` vote extends `B`, the fault bound at
  `t_q + Δ` gives the majority (the honest validators awake and joined at `t_q + Δ` vote in slot
  `q`, `vote_of_awake_joined`).

These read no vote head: they need neither the vote walk nor the voter's vote domain. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The honest slot-`q` casters whose vote extends `B`. -/
def ExtendingCasters (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) : Set (Fin sp.n) :=
  {x | x ∈ H ∧ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q ∧
    SA.VoteExtends (tr.HonestBlocks H) e.msg B}

/-- The faulty validators and the honest slot-`q` casters whose vote does not extend `B`. -/
def Opponents (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) : Set (Fin sp.n) :=
  Hᶜ ∪ {x | x ∈ H ∧ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q ∧
    ¬ SA.VoteExtends (tr.HonestBlocks H) e.msg B}

/-- S5-V: the extending casters of label `q` outnumber its opponents. -/
def ExtendingMajority (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) : Prop :=
  (Opponents tr H B q).ncard < (ExtendingCasters tr H B q).ncard

theorem extendingCasters_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {x : Fin sp.n} :
    x ∈ ExtendingCasters tr H B q ↔ x ∈ H ∧ ∃ k e, SA.VoteAt tr.projAC x k e ∧
      e.msg.slot = q ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg B :=
  Iff.rfl

theorem opponents_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {x : Fin sp.n} :
    x ∈ Opponents tr H B q ↔ x ∈ Hᶜ ∨ (x ∈ H ∧ ∃ k e, SA.VoteAt tr.projAC x k e ∧
      e.msg.slot = q ∧ ¬ SA.VoteExtends (tr.HonestBlocks H) e.msg B) :=
  Iff.rfl

theorem extendingMajority_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} :
    ExtendingMajority tr H B q ↔
      (Opponents tr H B q).ncard < (ExtendingCasters tr H B q).ncard :=
  Iff.rfl

/-- A vote extending `B` extends every block below `B`. -/
private theorem voteExtends_anti {B B' : SA.Blk sp.n (List (FG.Att sp.n))} {v : SA.Vote sp.n}
    (hBB' : Anc (tr.HonestBlocks H) B' B) (h : SA.VoteExtends (tr.HonestBlocks H) v B) :
    SA.VoteExtends (tr.HonestBlocks H) v B' := by
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := h
  exact ⟨Hd, hHd, hHdr, hBB'.trans hBHd⟩

/-- **Downward monotonicity**: from the protected origin to any block below it. -/
theorem ExtendingMajority.anti {B B' : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat}
    (hBB' : Anc (tr.HonestBlocks H) B' B) (h : ExtendingMajority tr H B q) :
    ExtendingMajority tr H B' q := by
  rw [extendingMajority_iff] at h ⊢
  have hO : Opponents tr H B' q ⊆ Opponents tr H B q := by
    intro x hx
    rcases opponents_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact opponents_iff.2 (Or.inl hx)
    · exact opponents_iff.2 (Or.inr ⟨hx, k, e, hv, hs, fun h => hne (voteExtends_anti hBB' h)⟩)
  have hE : ExtendingCasters tr H B q ⊆ ExtendingCasters tr H B' q := by
    intro x hx
    obtain ⟨hx, k, e, hv, hs, hext⟩ := extendingCasters_iff.1 hx
    exact extendingCasters_iff.2 ⟨hx, k, e, hv, hs, voteExtends_anti hBB' hext⟩
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (h.trans_le (Set.ncard_le_ncard hE (Set.toFinite _)))

/-- **L4**: when every honest slot-`q` vote extends `B`, the opponents are the faulty validators
and the extending casters hold every honest validator awake and joined at `t_q + Δ`, so the fault
bound there gives the majority. -/
theorem extendingMajority_of_all (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat}
    (hall : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hfb : tr.FaultBound H (sp.ts q + sp.Δ)) : ExtendingMajority tr H B q := by
  rw [extendingMajority_iff]
  have hO : Opponents tr H B q ⊆ Hᶜ := by
    intro x hx
    rcases opponents_iff.1 hx with hx | ⟨hx, k, e, hv, hs, hne⟩
    · exact hx
    · exact absurd (hall x hx k e hv hs) hne
  have hE : {y | y ∈ H ∧ tr.awake y (sp.ts q + sp.Δ) ∧ tr.JoinedAt y (sp.ts q + sp.Δ)} ⊆
      ExtendingCasters tr H B q := by
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined hrun hnc hx hw hj
    exact extendingCasters_iff.2 ⟨hx, k, e, hv, hs, hall x hx k e hv hs⟩
  exact (Set.ncard_le_ncard hO (Set.toFinite _)).trans_lt
    (lt_of_lt_of_le hfb (Set.ncard_le_ncard hE (Set.toFinite _)))

end Consensus.Goldilocks.Compose

end
