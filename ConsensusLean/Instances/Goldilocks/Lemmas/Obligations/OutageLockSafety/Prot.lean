module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyRetention
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepHonest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage lock safety: retention of the protection `Prot`, one cut

* `unlockKeeps_of_voteCompat`: `unlock` at an honest AC call keeps a frame block `B`
  when every honest vote of the view's slot by a validator outside `W` has a head compatible with
  `B`, and `2·|Hᶜ ∪ W| < n`. It covers every call, so both unlock views.
* `OutageVoteInv.prot_step`: the protection `Prot x k j m` (`j ≥ j₀ − 1`) carries to
  `k + 1` through the lock's life (`slot(t_k) ≤ m ≤ expiry`), with (VA) (`OutageLockInv.viable`) at
  `k` and the caches at `k + 1`.
* `OutageVoteInv.vote_extends_of_prot`: an honest cast under the protection extends `P`. -/

namespace Consensus.Goldilocks.Compose

set_option backward.isDefEq.respectTransparency false

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- A held honest vote across an AC cut was cast by its validator. -/
private theorem held_vote_cast (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.CallAt y j (.ac ℓ)) {v : Vote sp.n}
    (hv : v ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hvH : v.val ∈ H) :
    ∃ k e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hcA : tr.projAC.CallAt y j ℓ := projAC_callAt.2 hc
  have hfr : ℓ.frame = Node.frame (tr.state y j) := (hrun.cutLaw y hy j _ hc).1
  rcases SA.mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
  · rw [← projAC_state hrun.toLocalRun hy] at hv
    obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy j τ v hv hvH
    exact ⟨k, e, he, hm⟩
  · rw [← projAC_state hrun.toLocalRun hy] at hv
    obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy (j + 1) τ v hv hvH
    exact ⟨k, e, he, hm⟩
  · rw [← hfr] at hC
    have hvB : v ∈ SA.blockVotes C :=
      hv.elim id fun h => (SA.frame_validPayload sp hr hy hcA C hC).2 v h
    obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.carried_vote y hy j ℓ hcA C hC v hvB hvH
    exact ⟨k, e, he, hm⟩

/-- **`unlock` keeps `B` against the honest non-late-waker votes**: at an AC cut `j`
of an honest `y`, with `B` in the frame's tree and `2·|Hᶜ ∪ W| < n`, if every honest vote of
slot `slot(t_j) − 1` cast before `j` by a validator outside `W` has a head compatible with `B`,
the unlock target of `B` at the call's view is `B`. -/
theorem unlockKeeps_of_voteCompat (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {W : Set (Fin sp.n)} (hf : 2 * (Hᶜ ∪ W).ncard < sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.toFrame.tree)
    (hcompat : ∀ x ∈ H, x ∉ W → ∀ k < j, ∀ e, SA.VoteAt tr.projAC x k e →
      (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1 →
      VoteCompat (tr.HonestBlocks H) e.msg B) :
    UnlockKeeps tr y j B := by
  intro ℓ hcall
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hfr, hst, -, -⟩ := hrun.cutLaw y hy j _ hcall
  rw [hfr] at hst
  have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
      (Node.frame (tr.state y j)) (tr.time j) ℓ.call).1 = (tr.state y (j + 1)).ac := by
    rw [tr.state_succ_of_call hcall, hst]
  have hpool : ∀ m τ, ∀ v ∈ (tr.state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
    rw [← projAC_state hrun.toLocalRun hy] at hv
    exact SA.state_pool_slot sp hr hy m τ v hv
  have hpay : ∀ C ∈ (Node.frame (tr.state y j)).tree, SA.validPayload C := by
    rw [← hfr]
    exact SA.frame_validPayload sp hr hy (projAC_callAt.2 hcall)
  have hΦ := frameOK_state hrun.toLocalRun hy j
  have hΦU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, j, hX.1⟩
  have hHn : (H \ W)ᶜ = Hᶜ ∪ W := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, not_and, not_not]; tauto
  refine SA.unlockTarget_unlockView_held_of_honest_slot (Hn := H \ W) y ℓ.call hA' hΦ _ hB
    (hpool j) (hpool (j + 1)) hpay
    (fun x hx x' hx' hxH hval hs => heldVotes_honest_unique hrun hnc hy hcall hx hx' hxH.1 hval hs)
    (fun x hx hxH hs Hd hHd hHdr => ?_) (by rw [hHn]; exact hf)
  obtain ⟨k, e, hve, rfl⟩ := held_vote_cast hrun hnc hy hcall hx hxH.1
  obtain ⟨ℓ', hc', he'⟩ := hve
  have hkj : k < j := cast_lt_of_slot hrun hnc hxH.1 ⟨hc', he'⟩ hs
  obtain ⟨Hd', hHd', hHd'r, hcomp⟩ :=
    voteCompat_iff.1 (hcompat _ hxH.1 hxH.2 k hkj e ⟨ℓ', hc', he'⟩ hs)
  obtain rfl : Hd = Hd' := hU.1 (hΦU hHd) hHd' (hHdr.trans hHd'r.symm)
  rcases hcomp with h | h
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hHd h hB)
  · exact Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hB h hHd)

namespace OutageVoteInv

/-- `unlock` at an honest AC cut `k` keeps `P` (in the frame) when the view's slot is at least
`j₀`: the classification OL-W at the cuts before `k`. -/
theorem unlockKeeps {k : Nat} (hvi : OutageVoteInv D k) {y : Fin sp.n} (hy : y ∈ H)
    (hP : D.P ∈ (tr.state y k).fg.toFrame.tree)
    (hs : (D.j₀ : Int) + 1 ≤ sp.slot (tr.time k)) : UnlockKeeps tr y k D.P :=
  unlockKeeps_of_voteCompat D.hrun D.hnc D.two_mul_lt hy hP
    fun x hx hxW k' hk' e hv hes => hvi.voteCompat_of_not_lateWaker hx hxW hk' hv (by omega)

/-- **One step of the protection**: `Prot x k j m` with `j₀ − 1 ≤ j`, within the lock's
life (`slot(t_k) ≤ m`), (VA) at `k` and the caches at `k + 1` give `Prot x (k + 1) j m`. -/
theorem prot_step {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n} (hx : x ∈ H) {j m : Nat}
    (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (k + 1)).fg.F D.P)
    (hp : Prot D x k j m) : Prot D x (k + 1) j m := by
  have hr := FamilySafety.retentionFacts_goldilocks D.hrun D.hnc
    (fun _ hf _ hx _ _ hB hv => unlockKeeps_of_voteCompat D.hrun D.hnc hf hx hB hv)
  have hp' : FamilySafety.Prot D.family x k j m := by
    simpa only [FamilySafety.prot_iff, prot_iff, OutageLockPremises.family_P,
      FamilySafety.floorAt_goldilocks D.hrun hx] using hp
  have h := FamilySafety.OutageVoteInv.prot_step hr
    (FamilySafety.voteTiming_goldilocks D.hrun D.hnc) (projFG_localRun D.hrun D.hnc)
    (OutageVoteInv.family_iff.mpr hvi) hx
    (by simpa only [OutageLockPremises.family_j₀] using hj) hk
    (by simpa only [OutageLockPremises.family_P] using hva)
    (by simpa only [OutageLockPremises.family_P] using hF) hp'
  simpa only [FamilySafety.prot_iff, prot_iff, OutageLockPremises.family_P,
    FamilySafety.floorAt_goldilocks D.hrun hx] using h

/-- **An honest cast under the protection extends `P`**: at an honest cast at cut `k`,
within the life of `Prot x k j m` (`j₀ − 1 ≤ j`, `slot(t_k) ≤ m`), with (VA) at `k`, the vote
extends `P`. -/
theorem vote_extends_of_prot {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n} (hx : x ∈ H)
    {j m : Nat} (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hp : Prot D x k j m) {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hr := FamilySafety.retentionFacts_goldilocks D.hrun D.hnc
    (fun _ hf _ hx _ _ hB hv => unlockKeeps_of_voteCompat D.hrun D.hnc hf hx hB hv)
  have hp' : FamilySafety.Prot D.family x k j m := by
    simpa only [FamilySafety.prot_iff, prot_iff, OutageLockPremises.family_P,
      FamilySafety.floorAt_goldilocks D.hrun hx] using hp
  simpa only [OutageLockPremises.family_P] using
    FamilySafety.OutageVoteInv.vote_extends_of_prot hr
      (FamilySafety.voteDominance_goldilocks D.hrun D.hnc)
      (FamilySafety.voteTiming_goldilocks D.hrun D.hnc)
      (OutageVoteInv.family_iff.mpr hvi) hx
      (by simpa only [OutageLockPremises.family_j₀] using hj) hk
      (by simpa only [OutageLockPremises.family_P] using hva) hp' hv

end OutageVoteInv

end Consensus.Goldilocks.Compose

end
