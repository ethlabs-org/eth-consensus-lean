module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
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
  `B`, and `2·|K σ ∩ (Hᶜ ∪ W)| < committeeSize` at the previous slot `σ`, with P and the frame
  votes in the committees `K`. It covers every call, so both unlock views.
* `OutageVoteInv.prot_step`: the protection `Prot x k j m` (`j ≥ j₀ − 1`) carries to
  `k + 1` through the lock's life (`slot(t_k) ≤ m ≤ expiry`), with (VA) (`OutageLockInv.viable`) at
  `k` and the caches at `k + 1`.
* `OutageVoteInv.vote_extends_of_prot`: an honest cast under the protection extends `P`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- A held honest vote across an AC cut was cast by its validator. -/
private theorem held_vote_cast {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.CallAt y j (.ac ℓ)) {v : Vote sp.n}
    (hv : v ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hvH : v.val ∈ H) :
    ∃ k e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v := by
  have hrun' := goldilocks_ac_projection_from hrun hnc
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
of an honest `y`, with `B` in the frame's tree, P and the frame's block votes in the committees
`K`, and `2·|K σ ∩ (Hᶜ ∪ W)| < committeeSize` at `σ = slot(t_j) − 1`, if every honest vote of
slot `σ` cast before `j` by a validator outside `W` has a head compatible with `B`, the unlock
target of `B` at the call's view is `B`. The opposing set is `(H ∖ W) ∪ {i ∉ K σ}`: a
non-member holds no slot-`σ` vote. -/
theorem unlockKeeps_of_voteCompat {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hP : SA.CommitteeP K tr.projAC H)
    {W : Set (Fin sp.n)} {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    (hf : 2 * (K.committee (sp.slot (tr.time j) - 1) ∩ (Hᶜ ∪ W)).ncard < sp.committeeSize)
    (hFr : ∀ C ∈ (Node.frame (tr.state y j)).tree, ∀ v ∈ SA.blockVotes C,
      v.val ∈ K.committee v.slot)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.toFrame.tree)
    (hcompat : ∀ x ∈ H, x ∉ W → ∀ k < j, ∀ e, SA.VoteAt tr.projAC x k e →
      (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1 →
      VoteCompat (tr.HonestBlocks H) e.msg B) :
    UnlockKeeps tr y j B := by
  intro ℓ hcall
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hfr, hst, -, -⟩ := hrun.cutLaw y hy j _ hcall
  rw [hfr] at hst
  have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
      (Node.frame (tr.state y j)) (tr.time j) ℓ.call).1 = (tr.state y (j + 1)).ac := by
    rw [tr.state_succ_of_call hcall, hst]
  have hpool : ∀ m τ, ∀ v ∈ (tr.state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
    rw [← projAC_state hrun.toLocalRun hy] at hv
    exact SA.state_pool_slot_from sp hr hrun.vstart hy m τ v hv
  have hpay : ∀ C ∈ (Node.frame (tr.state y j)).tree, SA.validPayload C := by
    rw [← hfr]
    exact SA.frame_validPayload sp hr hy (projAC_callAt.2 hcall)
  have hΦ := frameOK_state hrun.toLocalRun hy j
  have hΦU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, j, hX.1⟩
  have hmem : ∀ x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)), x.val ∈ K.committee x.slot := fun x hx => by
    rcases SA.mem_heldVotes.1 hx with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
    · rw [hpool j τ x hv]
      rw [← projAC_state hrun.toLocalRun hy] at hv
      exact hP.1 y hy j τ x hv
    · rw [hpool (j + 1) τ x hv]
      rw [← projAC_state hrun.toLocalRun hy] at hv
      exact hP.1 y hy (j + 1) τ x hv
    · exact hFr C hC x (hv.elim id fun h => (hpay C hC).2 x h)
  have hHnH : ∀ x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)),
      x.val ∈ H \ W ∪ {i | i ∉ K.committee (sp.slot (tr.time j) - 1)} →
      (x.slot : Int) = (sp.slot (tr.time j) : Int) - 1 → x.val ∈ H \ W :=
    fun x hx hxH hs => hxH.resolve_right fun hn =>
      hn (by rw [← show x.slot = sp.slot (tr.time j) - 1 by omega]; exact hmem x hx)
  have hHn : (H \ W ∪ {i | i ∉ K.committee (sp.slot (tr.time j) - 1)})ᶜ =
      K.committee (sp.slot (tr.time j) - 1) ∩ (Hᶜ ∪ W) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_inter_iff, not_or, not_and, not_not]
    tauto
  refine SA.unlockTarget_unlockView_held_of_honest_slot
    (Hn := H \ W ∪ {i | i ∉ K.committee (sp.slot (tr.time j) - 1)}) y ℓ.call hA' hΦ _ hB
    (hpool j) (hpool (j + 1)) hpay
    (fun x hx x' hx' hxH hval hs hσ =>
      heldVotes_honest_unique hrun hnc hy hcall hx hx' (hHnH x hx hxH hσ).1 hval hs)
    (fun x hx hxH hs Hd hHd hHdr => ?_)
    (by rw [hHn]; exact hf)
  have hxH := hHnH x hx hxH hs
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
`j₀`: the classification OL-W at the cuts before `k`, at the full committee. -/
theorem unlockKeeps {k : Nat} (hvi : OutageVoteInv D k) {y : Fin sp.n} (hy : y ∈ H)
    (hP : D.P ∈ (tr.state y k).fg.toFrame.tree)
    (hs : (D.j₀ : Int) + 1 ≤ sp.slot (tr.time k)) : UnlockKeeps tr y k D.P :=
  unlockKeeps_of_voteCompat D.hrun D.hnc SA.CommitteeP.full hy
    (SA.cs2_full D.stock D.two_mul_lt)
    (fun _ _ v _ => SA.mem_full v.slot _) hP
    fun x hx hxW k' hk' e hv hes => hvi.voteCompat_of_not_lateWaker hx hxW hk' hv (by omega)

/-- **One step of the protection**: `Prot x k j m` with `j₀ − 1 ≤ j`, within the lock's
life (`slot(t_k) ≤ m`), (VA) at `k` and the caches at `k + 1` give `Prot x (k + 1) j m`. -/
theorem prot_step {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n} (hx : x ∈ H) {j m : Nat}
    (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (k + 1)).fg.F D.P)
    (hp : Prot D x k j m) : Prot D x (k + 1) j m := by
  have hU := D.coherent
  have hFm := Healing.run_F_mono D.hrun.toLocalRun hx (Nat.le_succ k)
  rcases prot_iff.1 hp with hfl | hroot
  swap
  · exact prot_iff.2 (Or.inr (hroot.trans hFm))
  by_cases hroot' : Anc (tr.HonestBlocks H) D.P (tr.state x (k + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot')
  have hFP : Anc (tr.HonestBlocks H) (tr.state x (k + 1)).fg.F D.P := hF.resolve_right hroot'
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP : D.P ∈ (tr.state x k).fg.toFrame.tree := SA.mem_of_anc hPB hB
  have hP' : D.P ∈ (tr.state x (k + 1)).fg.toFrame.tree := by
    have hPt := tree_mono D.hrun.toLocalRun hx (Nat.le_succ k) hP.1
    exact frame_mem_of_tree D.hrun hx le_rfl hPt (honest_held_anc D.hrun D.hnc hx hFP hPt)
  have hva0 : (tr.state x k).fg.toFrame.viableAncestor D.P = D.P :=
    SA.viableAncestor_self (frameOK_state D.hrun.toLocalRun hx k) hP (hva hP).symm
  refine prot_iff.2 (Or.inl (floor_run_view D.hrun hx k ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ hk hP hP'
    hva0 fun ℓ hc => ?_))
  by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
  · exact Or.inl hs
  · exact Or.inr (hvi.unlockKeeps hx hP (by omega) ℓ hc)

/-- **An honest cast under the protection extends `P`**: at an honest cast at cut `k`,
within the life of `Prot x k j m` (`j₀ − 1 ≤ j`, `slot(t_k) ≤ m`), with (VA) at `k`, the vote
extends `P`. -/
theorem vote_extends_of_prot {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n} (hx : x ∈ H)
    {j m : Nat} (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hp : Prot D x k j m) {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  have hcast : SA.CastAt tr.projAC x k ℓ e := ⟨hc, he⟩
  have hfr : ℓ.frame = Node.frame (tr.state x k) := (D.hrun.cutLaw x hx k _ (projAC_callAt.1 hc)).1
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hx hc
  rcases prot_iff.1 hp with hfl | hroot
  swap
  · obtain ⟨Hd, hHd, hHdr, -⟩ := SA.honest_head_frame hr hx hcast
    have hFHd : ℓ.frame.Anc ℓ.frame.F Hd := hΦ.rooted.2 Hd hHd
    rw [hfr] at hFHd
    exact ⟨Hd, hΦU hHd, hHdr, hroot.trans (hFHd.mono fun X hX => ⟨x, hx, k, hX.1⟩)⟩
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP : D.P ∈ (tr.state x k).fg.toFrame.tree := SA.mem_of_anc hPB hB
  have hva0 : (tr.state x k).fg.toFrame.viableAncestor D.P = D.P :=
    SA.viableAncestor_self (frameOK_state D.hrun.toLocalRun hx k) hP (hva hP).symm
  rw [← Node.frame, ← hfr] at hP hva0 hB hPB
  have hl' : l ∈ (tr.projAC.state x k).locks := by
    rw [projAC_state D.hrun.toLocalRun hx k]; exact hl
  obtain ⟨C, hC, hPC⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hx hcast hP hva0 hk
    (by
      by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
      · exact Or.inl hs
      · refine Or.inr ?_
        have := hvi.unlockKeeps hx (by rw [← Node.frame, ← hfr]; exact hP) (by omega) ℓ
          (projAC_callAt.1 hc)
        rw [projAC_state D.hrun.toLocalRun hx k, hfr]
        exact this)
    ⟨l, hl', hlj, hle, B, hB, hBr, hPB⟩
  obtain ⟨Hd, hHd, hHdr, hPHd⟩ := SA.castAt_head_anc hr hx hcast (Or.inl hC)
    (SA.castAt_compatible_of_live hr (fun _ => SA.voteStart_initial _) hx hcast (Or.inl hC)) hPC
  exact ⟨Hd, hΦU hHd, hHdr, hPHd.mono hΦU⟩

end OutageVoteInv

end Consensus.Goldilocks.Compose

end
