module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepHonest
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety under growing faults: retention of the protection, one cut

Every fact here is local to one node at one cut `k` at which it is honest, so each static fact
is lifted to the prefix through `d = t_k` (`Growing.GoldilocksRun.upTo`), where the node's states
at `k` and `k + 1` are the run's.

* `unlockKeeps_of_voteCompat_at`: `unlock` at an AC call of a node honest at its cut `j` keeps a
  frame block `B` when the slot votes cast before `j` by a set `G` of validators honest at `j` have
  heads compatible with `B`, and `2·|Gᶜ| < n`;
* `OutageVoteInv.unlockKeeps_at`: with `G = H z ∖ W` at a cut `t_k ≤ z` (the opponents lie in
  `(H z)ᶜ ∪ W`, `two_mul_lt`);
* `OutageVoteInv.prot_step_at`, `OutageVoteInv.vote_extends_of_prot_at`: the protection of a node
  honest at `k` carries to `k + 1` through the lock's life (`m ≤ j₀ + k`), and a cast under it
  extends `P`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {d : Time}

/-- A vote compatibility of a vote cast in the prefix by a node honest at `d`, with a block of the
prefix's honest blocks, comes down into the prefix. -/
private theorem voteCompat_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d) {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (tr.upTo d).projAC x k e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.upTo d).HonestBlocks (H d))
    (h : VoteCompat (tr.HonestBlocksAt H) e.msg B) :
    VoteCompat ((tr.upTo d).HonestBlocks (H d)) e.msg B := by
  obtain ⟨Hd, hHd, hHdr, hcomp⟩ := voteCompat_iff.1 h
  obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := SA.honest_head
    (goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer (hrun.upTo hd) (hnc.upTo d))
    hx hv
  obtain rfl : Hd = Hd₂ := (honestBlocksAt_coherent hrun hnc).1 hHd (upTo_subset hrun hd hHd₂)
    (hHdr.trans hHd₂r.symm)
  exact voteCompat_iff.2 ⟨Hd, hHd₂, hHdr, compatible_upTo hrun hnc hd hHd₂ hB hcomp⟩

/-- **`unlock` keeps `B` against the votes of a set `G` honest at the cut**: at an AC cut `j` of a
node honest then, with `B` in the frame's tree, `G ⊆ H (t_j)` and `2·|Gᶜ| < n`, if every vote of
slot `slot(t_j) − 1` cast before `j` by a member of `G` has a head compatible with `B`, the unlock
target of `B` at the call's view is `B`. -/
theorem unlockKeeps_of_voteCompat_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {G : Set (Fin sp.n)} {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    (hG : G ⊆ H (tr.time j)) (hf : 2 * Gᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.toFrame.tree)
    (hcompat : ∀ x ∈ G, ∀ k < j, ∀ e, HVoteAt tr H x k e →
      (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1 →
      VoteCompat (tr.HonestBlocksAt H) e.msg B) :
    UnlockKeeps tr y j B := by
  have hd := hrun.time_nonneg j
  have hst : (tr.upTo (tr.time j)).state y j = tr.state y j :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  have hf' : 2 * ((H (tr.time j))ᶜ ∪ Gᶜ).ncard < sp.n := by
    rwa [Set.union_eq_right.mpr (Set.compl_subset_compl.mpr hG)]
  have h := Compose.unlockKeeps_of_voteCompat (hrun.upTo hd) (hnc.upTo _) hf' hy
    (by rw [hst]; exact hB) fun x hx hxG k hk e hv hs => by
      have hv' := hv
      rw [RunTrace.upTo_projAC] at hv'
      obtain ⟨hkd, hv'⟩ := sa_voteAt_upTo.mp hv'
      exact voteCompat_upTo hrun hnc hd hx hv ⟨y, hy, j, by rw [hst]; exact hB.1⟩
        (hcompat x (not_not.1 hxG) k hk e (hVoteAt_iff.2 ⟨hrun.antitone hkd hx, hv'⟩) hs)
  intro ℓ hc
  have := h ℓ ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  rwa [hst] at this

variable {D : OutageLockPremises tr H proposer dg}

namespace OutageVoteInv

/-- `unlock` at an AC cut `k` of a node honest then, at a time `≤ z`, keeps `P` (in the frame)
when the view's slot is at least `j₀`: OL-W at the cuts before `k`, the opponents in
`(H z)ᶜ ∪ W`. -/
theorem unlockKeeps_at {k : Nat} (hvi : OutageVoteInv D k) {y : Fin sp.n}
    (hy : y ∈ H (tr.time k)) (hP : D.P ∈ (tr.state y k).fg.toFrame.tree)
    (hs : (D.j₀ : Int) + 1 ≤ sp.slot (tr.time k)) (hkz : tr.time k ≤ D.z) :
    UnlockKeeps tr y k D.P := by
  have hG : H D.z \ D.W ⊆ H (tr.time k) := fun x hx => D.hrun.antitone hkz hx.1
  have hc : (H D.z \ D.W)ᶜ = (H D.z)ᶜ ∪ D.W := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, not_and, not_not]; tauto
  refine unlockKeeps_of_voteCompat_at D.hrun D.hnc hy hG (by rw [hc]; exact D.two_mul_lt) hP
    fun x hx k' hk' e hv hes => hvi.voteCompat_of_not_lateWaker_at hk' hv (by omega)
      fun _ => ⟨hx.1, hx.2⟩

/-- A cut of a node at a slot at most `j₀ + k`, with an honest call there, is at a time `≤ z`. -/
private theorem time_le_z (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} {k : Nat}
    (hx : x ∈ H (tr.time k)) (hc : tr.IsCall x k) (hs : sp.slot (tr.time k) ≤ D.j₀ + sp.k) :
    tr.time k ≤ D.z := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hlt : tr.time k < sp.ts (D.j₀ + sp.k + 1 : Nat) := by
    by_contra h
    have := (SA.ts_le_iff_le_slot sp (D.hrun.time_nonneg k) ((D.j₀ + sp.k + 1 : Nat) : Int)).1
      (not_lt.1 h)
    omega
  have hts : sp.ts (D.j₀ + sp.k + 1 : Nat) = sp.ts (D.j₀ + sp.k : Nat) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  exact D.hzc _ (by linarith) ⟨x, k, hx, hc, le_rfl⟩

/-- **One step of the protection**: at a cut `k` of a node honest then, `Prot x k j m` with
`j₀ − 1 ≤ j`, within the lock's life (`slot(t_k) ≤ m ≤ j₀ + k`), (VA) at `k` and the caches at
`k + 1` give `Prot x (k + 1) j m`. -/
theorem prot_step_at {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n}
    (hx : x ∈ H (tr.time k)) {j m : Nat} (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m)
    (hmK : m ≤ D.j₀ + sp.k)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hF : Compatible (tr.HonestBlocksAt H) (tr.state x (k + 1)).fg.F D.P)
    (hp : Prot D x k j m) : Prot D x (k + 1) j m := by
  have hrun := D.hrun
  have hd := hrun.time_nonneg k
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun hd
  have hst : (tr.upTo (tr.time k)).state x k = tr.state x k :=
    RunTrace.upTo_state_of_le hm le_rfl
  have hst1 : (tr.upTo (tr.time k)).state x (k + 1) = tr.state x (k + 1) :=
    Trace.upTo_state tr x fun _ hk' => hm (Nat.lt_succ_iff.1 hk')
  have hr := hrun.upTo hd
  have hFm := Healing.run_F_mono hr.toLocalRun hx (Nat.le_succ k)
  rw [hst, hst1] at hFm
  rcases prot_iff.1 hp with hfl | hroot
  swap
  · exact prot_iff.2 (Or.inr (hroot.trans (hFm.mono hsub)))
  by_cases hroot' : Anc (tr.HonestBlocksAt H) D.P (tr.state x (k + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot')
  have hFP : Anc (tr.HonestBlocksAt H) (tr.state x (k + 1)).fg.F D.P := hF.resolve_right hroot'
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP : D.P ∈ (tr.state x k).fg.toFrame.tree := SA.mem_of_anc hPB hB
  have hPt : D.P ∈ (tr.state x (k + 1)).fg.tree := by
    have h := tree_mono hr.toLocalRun hx (Nat.le_succ k) (by rw [hst]; exact hP.1)
    rwa [hst1] at h
  have hPU : D.P ∈ (tr.upTo (tr.time k)).HonestBlocks (H (tr.time k)) :=
    ⟨x, hx, k + 1, by rw [hst1]; exact hPt⟩
  have hanc : (tr.state x (k + 1)).fg.Anc (tr.state x (k + 1)).fg.F D.P := by
    have h := honest_held_anc hr (D.hnc.upTo _) hx (i := k + 1)
      (RunTrace.anc_upTo_of_right hrun.toLocalRun D.hnc hd hPU hFP) (by rw [hst1]; exact hPt)
    rwa [hst1] at h
  have hP' : D.P ∈ (tr.state x (k + 1)).fg.toFrame.tree := ⟨hPt, hanc⟩
  have hva0 : (tr.state x k).fg.toFrame.viableAncestor D.P = D.P :=
    SA.viableAncestor_self (by have h := frameOK_state hr.toLocalRun hx k; rw [hst] at h; exact h)
      hP (hva hP).symm
  have h := floor_run_view hr hx k (B₀ := D.P) (j := j) (m := m)
    (by simp only [FloorAt, hst]; exact ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩) hk
    (by rw [hst]; exact hP)
    (by rw [hst1]; exact hP') (by rw [hst]; exact hva0) fun ℓ hc => by
      rw [hst]
      have hc' := (Trace.upTo_callAt_of_le _ le_rfl).mp hc
      by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
      · exact Or.inl hs
      · exact Or.inr (hvi.unlockKeeps_at hx hP (by omega)
          (time_le_z D hx ⟨_, hc'⟩ (hk.trans hmK)) ℓ hc')
  simp only [FloorAt, hst1] at h
  exact prot_iff.2 (Or.inl h)

/-- **A cast under the protection extends `P`**: at a cast at cut `k` of a node honest then,
within the life of `Prot x k j m` (`j₀ − 1 ≤ j`, `slot(t_k) ≤ m ≤ j₀ + k`), with (VA) at `k`, the
vote extends `P`. -/
theorem vote_extends_of_prot_at {k : Nat} (hvi : OutageVoteInv D k) {x : Fin sp.n}
    {j m : Nat} (hj : D.j₀ ≤ j + 1) (hk : sp.slot (tr.time k) ≤ m) (hmK : m ≤ D.j₀ + sp.k)
    (hva : D.P ∈ (Node.frame (tr.state x k)).tree →
      (Node.frame (tr.state x k)).AncestorCandidate D.P)
    (hp : Prot D x k j m) {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  have hrun := D.hrun
  have hd := hrun.time_nonneg k
  obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
  have hr := (acRun_upTo hrun D.hnc hd).localRun
  have hcast : SA.CastAt (tr.projAC.upTo (tr.time k)) x k ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc, he⟩
  have hfr : ℓ.frame = Node.frame (tr.state x k) := frame_of_projAC_at hrun hx hc
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun D.hnc hx hc
  rcases prot_iff.1 hp with hfl | hroot
  swap
  · obtain ⟨Hd, hHd, hHdr, -⟩ := SA.honest_head_frame hr hx hcast
    have hFHd : ℓ.frame.Anc ℓ.frame.F Hd := hΦ.rooted.2 Hd hHd
    rw [hfr] at hFHd
    exact ⟨Hd, hΦU hHd, hHdr,
      hroot.trans (hFHd.mono fun X hX => mem_honestBlocksAt hrun hx hX.1)⟩
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hfl
  have hP : D.P ∈ (tr.state x k).fg.toFrame.tree := SA.mem_of_anc hPB hB
  have hva0 : (tr.state x k).fg.toFrame.viableAncestor D.P = D.P :=
    SA.viableAncestor_self
      (by
        have h := frameOK_state (hrun.upTo hd).toLocalRun hx k
        rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
        exact h) hP (hva hP).symm
  rw [← Node.frame, ← hfr] at hP hva0 hB hPB
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state x k).locks := by
    rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hx]; exact hl
  obtain ⟨C, hC, hPC⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hx hcast hP hva0 hk
    (by
      by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ j
      · exact Or.inl hs
      · refine Or.inr ?_
        have := hvi.unlockKeeps_at hx (by rw [← Node.frame, ← hfr]; exact hP) (by omega)
          (time_le_z D hx ⟨_, projAC_callAt.1 hc⟩ (hk.trans hmK)) ℓ (projAC_callAt.1 hc)
        rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hx, hfr]
        exact this)
    ⟨l, hl', hlj, hle, B, hB, hBr, hPB⟩
  obtain ⟨Hd, hHd, hHdr, hPHd⟩ := SA.castAt_head_anc hr hx hcast (Or.inl hC)
    (SA.castAt_compatible_of_live hr hx hcast (Or.inl hC)) hPC
  exact ⟨Hd, hΦU hHd, hHdr, hPHd.mono hΦU⟩

end OutageVoteInv

end Consensus.Goldilocks.Compose.Growing

end
