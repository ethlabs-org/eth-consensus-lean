module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the restored votes

Inside lock safety's cut induction, at a vote of slot `q + 1 > r` at cut `k`, by a node honest
then, from `OutageLockInv D i` (`k ≤ i`) and receiver service from `b₁`:

* `viable_at_vote_of_lo_at` (G4): under Lo, `P` is viable at the vote: the witness head is
  frozen (`honest_head_accepted_after_at`), and below the floor the `h_max` carrier's floor entry
  is above `P` with a source extended by a slot-`≤ q` vote (`rows_supported_at`), whose head is
  frozen and viable;
* `outage_s5_inner_at` (INV): root cover, Hi (`vote_extends_of_hi_at`), or Lo with the batch walk.
  For `q > r` the batch is every slot-`q` vote (each extends `P` by induction on the cut), counted
  at the voter's cut (`vote_extends_of_batch_at`, `faults_lt_voters`). For `q = r` the batch is the
  cohort `A₀`: the voters honest at the vote's time `t_k ≤ t_r + 5Δ ≤ z` are classified at their
  cast (`cohort_classify`), the others are compromised by `z`, and `hcohort` counts the rest;
* `outage_s5_step_at` (lock safety's `hS5`) and `restored_votes_extend_at`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **A block accepted before the freeze is in the voter block tree** (`accepted_voter_tree` on
the prefix through the vote's time). -/
private theorem accepted_voter_tree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hXU : X ∈ tr.HonestBlocksAt H)
    (hacc : SA.AcceptedBefore tr.projAC y X (sp.ts s + 3 * sp.Δ))
    (hFX : Anc (tr.HonestBlocksAt H) ℓ.frame.F X) :
    X ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1) := by
  have hd := hrun.time_nonneg i
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hy hc.1
  obtain ⟨-, hti⟩ := honest_vote_restarts_at hrun hnc hy hc hs
  have hcT : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hXt : X ∈ ℓ.frame.tree := by
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ :=
        SA.genesis_mem_of_call sp (acRun_upTo hrun hnc hd).localRun hy i ℓ hcT.1
      obtain rfl : X = G := hU.1 hXU (upTo_subset hrun hd hGU) (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFX
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k ≤ i := by
        by_contra h
        have := hrun.time_mono (le_of_not_ge h)
        change tr.time k < _ at hkt
        linarith only [this, hkt, hti, hΔ]
      exact mem_tree_of_acceptAt_at hrun hnc hy hk hki hc.1 hFX
  have hXU' := frame_upTo_at hrun hnc hy hc.1 hXt
  have hFX' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hXU' hFX
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e := by
    rw [RunTrace.upTo_projAC]; exact hcT
  have hacc' : SA.AcceptedBefore (tr.upTo (tr.time i)).projAC y X (sp.ts s + 3 * sp.Δ) := by
    rw [RunTrace.upTo_projAC]
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · exact Or.inl hg
    · refine Or.inr ⟨k, (ac_acceptAt_upTo _).mpr ⟨?_, hk⟩, hkt⟩
      change tr.time k < _ at hkt
      change tr.time k ≤ tr.time i
      linarith only [hkt, hti, hΔ]
  exact accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy hc' hs hXU' hacc' hFX'

/-- **C1.1 (i) at a vote** (`vote_viable`, the vote's node honest at its cut): a block compatible
with both caches and below a frozen viable block (or `fc_root`) is in the vote's viable tree or
below `fc_root`. -/
private theorem vote_viable_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time k))
    (hc : SA.CastAt tr.projAC y k ℓ e) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcache : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  have hd := hrun.time_nonneg k
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hcT : SA.CastAt (tr.projAC.upTo (tr.time k)) y k ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  have hfr := frame_of_projAC_at hrun hy hc.1
  have hcomp : Compatible (tr.HonestBlocksAt H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y k).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hcache.2
    · exact hcache.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      refine Or.inl ⟨SA.voterBlockTree_anc_from hr hrun.vstart hy hcT D hD B
          hΦBD, hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- A block held below a source's entry height is below the entry, in a static run. (As
`Compose/Sleepy/Frame.lean`'s private `below_entry`.) -/
private theorem below_entry {H₀ : Set (Fin sp.n)} {tr₀ : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H₀ tr₀ ini) (hnc : NoCollRun dg tr₀)
    {y : Fin sp.n} (hy : y ∈ H₀) {i : Nat} {B Ds E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr₀.state y i).fg.tree) (hE : E ∈ (tr₀.state y i).fg.tree)
    (hD : IsHonestSource tr₀ H₀ Ds E.root) (hDB : Compatible (tr₀.HonestBlocks H₀) Ds B)
    (hlt : ((tr₀.state y i).fg.σ B.root).h < ((tr₀.state y i).fg.σ E.root).h) :
    (tr₀.state y i).fg.Anc B E := by
  have hU := (projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr₀.HonestBlocks H₀) E Ds := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr₀.HonestBlocks H₀) E B := fun h => by
    have := (honest_held_height hrun hnc hy (honest_held_anc hrun hnc hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hU h hEDU with h' | h'
    · exact honest_held_anc hrun hnc hy h' hE
    · exact absurd h' no

/-- **The counted batch under growing faults**, at a slot-`(s+1)` vote of a node honest at its
cut `i`: a batch `SX` of validators honest at `t_i`, each with a slot-`s` vote, all such votes
extending `B` and carried, outnumbering half of a cover `W` of the merged voters (`W` holds every
slot-`s` caster honest at `t_i` and every validator compromised by `t_i`), with every live lock
compatible with `B`, makes the vote extend `B`. The static counted batch on the prefix through
`t_i`. -/
private theorem vote_extends_of_counted_batch_run
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H (tr.time i))
    (hSXv : ∀ x ∈ SX, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', HVoteAt tr H x j e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hW : ∀ x j e', HVoteAt tr H x j e' → x ∈ H (tr.time i) → e'.msg.slot = s → x ∈ W)
    (hWc : (H (tr.time i))ᶜ ⊆ W) (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s
      {v | ∃ x ∈ SX, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hr := acRun_upTo hrun hnc hd
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hts1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    change s + 1 = sp.slot (tr.time i) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by exact_mod_cast h.le)
  have hT : sp.ts s + 3 * sp.Δ ≤ tr.time i := by linarith
  -- a vote of the prefix by a validator honest at `t_i` is one of the run by a node honest at it
  have hvote : ∀ x j e', x ∈ H (tr.time i) → SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      HVoteAt tr H x j e' := fun x j e' hx hv => by
    obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
    exact hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩
  have hΦ := (frameIn_at hrun hnc hy hc.1).1
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  have hBU := frame_upTo_at hrun hnc hy hc.1 hBt
  have h := Compose.vote_extends_of_counted_batch hr hy hc' hs hviab (SX := SX) (W := W) hSXH
    (fun x hx => by
      obtain ⟨j, e', hv, hes⟩ := hSXv x hx
      exact ⟨j, e', sa_voteAt_upTo.mpr ⟨(vote_cut_lt hrun hnc hv hes hti).1.le.trans hti,
        (hVoteAt_iff.1 hv).2⟩, hes⟩)
    (fun x hx j e' hv hes => voteExtends_upTo hrun hnc hd (hSXH hx)
      (by rw [RunTrace.upTo_projAC]; exact hv) (hall x hx j e' (hvote x j e' (hSXH hx) hv) hes))
    (by
      rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H (tr.time i)
      · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hr hy hc' hv hw
        exact hW _ j e' (hvote _ j e' hw hv') hw
          (by
            rw [he']
            exact SA.merged_vote_slot hr.localRun hr.vstart hy hc' v hv)
      · exact hWc hw)
    hcount
    ⟨⟨hcarry.awake, le_rfl⟩, hcarry.joined, fun v ⟨x, hx, j, e', hv, hev, hvs⟩ => by
      have hv' := hvote x j e' (hSXH hx) hv
      obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨x, hx, j, e', hv', hev, hvs⟩
      obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := SA.honest_head hr (hSXH hx) hv
      obtain rfl : Hv = Hd₂ := hU.1 hHv (hsub hHd₂) (hHvr.trans (hev ▸ hHd₂r.symm))
      refine ⟨Hv, hHd₂, hHvr, fun X hX => ?_⟩
      exact (hacc X (hX.mono hsub)).imp_right fun ⟨k, hk, hkT⟩ =>
        ⟨k, (ac_acceptAt_upTo _).mpr ⟨hkT.le.trans hT, hk⟩, hkT⟩,
      fun v ⟨x, hx, j, e', hv, hev, hvs⟩ =>
        hcarry.holds v ⟨x, hx, j, e', hvote x j e' (hSXH hx) hv, hev, hvs⟩⟩
    (fun L hL => compatible_upTo hrun hnc hd (frame_upTo_at hrun hnc hy hc.1 hL.1) hBU
      (hlocks L hL))
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := h
  exact ⟨Hd, hsub hHd, hHdr, hBHd.mono hsub⟩

variable (D : OutageLockPremises tr H proposer dg ini)

/-- **G4**: at a Lo vote of slot `q + 1 ≥ r + 1` above `Σ.F`, by a node honest at its cut `i`,
with receiver service from `b₁`, a protected block `P` that a slot-`q` vote (of a node honest at
its cast) extends is viable at the vote. The witness head is frozen; below the floor
(`h_max − 1`, no contest under Lo, counted at `t_i`), the `h_max` carrier's floor entry is above
`P` and the head of a vote extending its source (`rows_supported_at`) is frozen and viable. The
store of `y` is read on the prefix through `t_i`. -/
theorem viable_at_vote_of_lo_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n}
    (hy : y ∈ H (tr.time i)) (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC)
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) {q : Nat} (hs : e.msg.slot = q + 1) (hrq : D.r ≤ q)
    (hLo : ¬ HiAt tr H D.P y i)
    (hFP : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F D.P)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = q ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg D.P) :
    SA.ViableAtVote ℓ e (q + 1) D.P := by
  have hrun := D.hrun
  have hU := D.coherent
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have ht : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hm hk.le
  have hf := D.two_faults_lt_at hy ⟨_, projAC_callAt.1 hc.1⟩
  have hfr : ℓ.frame = Node.frame (tr.state y i) := frame_of_projAC_at hrun hy hc.1
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun D.hnc hy hc.1
  have hFℓ : ℓ.frame.F = (tr.state y i).fg.F := by rw [hfr]; rfl
  have hg : D.b₁ ≤ sp.ts q + sp.Δ := by
    have := ts_le_ts (sp := sp) hrq
    linarith only [this, D.hr.1]
  -- the head of a vote of a slot `≤ q` above `Σ.F` is frozen at `y`
  have frozen : ∀ x k e', HVoteAt tr H x k e' → e'.msg.slot ≤ q →
      ∀ Z, SA.VoteExtends (tr.HonestBlocksAt H) e'.msg Z →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Z →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (q + 1),
        Anc (tr.HonestBlocksAt H) Z W := by
    intro x k e' hv hs' Z ⟨Hd, hHd, hHdr, hZHd⟩ hFZ
    have hFHd : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd := hFℓ ▸ hFZ.trans hZHd
    exact ⟨Hd, accepted_voter_tree_at hrun D.hnc hy hc hs hHd
      (honest_head_accepted_after_at hrun D.hnc hS hg hy hc hs hv hs' hHd hHdr hFHd) hFHd, hZHd⟩
  have hvt : ∀ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (q + 1),
      W ∈ (tr.state y i).fg.tree := by
    intro W hW
    have := hW.1
    rw [hfr] at this
    exact this.1
  -- the store of `y` on the prefix through `t_i`
  have hr := hrun.upTo hd
  have hnc' := D.hnc.upTo (tr.time i)
  have hsub := upTo_subset hrun hd
  have hst := Trace.upTo_state tr y ht
  have toU : ∀ {A W : SA.Blk sp.n (List (FG.Att sp.n))}, W ∈ (tr.state y i).fg.tree →
      Anc (tr.HonestBlocksAt H) A W →
      Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) A W := fun hW h =>
    RunTrace.anc_upTo_of_right hrun.toLocalRun D.hnc hd ⟨y, hy, i, by rw [hst]; exact hW⟩ h
  -- (K2): a frozen viable block above `P`
  have hK2 : ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) D.P W ∧ (tr.state y i).fg.IsViable W := by
    rw [hs]
    have hR := reachable_at hrun hd hy ht
    have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [not_contest_of_lo_at D hinv le_rfl hd ht hy hf hLo, ↓reduceIte]
    obtain ⟨x, k, e', hv, hs', hext⟩ := hw
    obtain ⟨Hx, hHx, hPHx⟩ := frozen x k e' hv hs'.le D.P hext hFP
    have hHxt := hvt Hx hHx
    by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ Hx.root).h
    · exact ⟨Hx, hHx, hPHx, hle⟩
    -- below the floor: the floor entry of an `h_max` carrier is above `P`
    obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
    have hHx1 : 1 ≤ ((tr.state y i).fg.σ Hx.root).h := by
      have h := (honest_held_chain hr hy (i := i) (by rw [hst]; exact hHxt)).1
      rwa [hst] at h
    have hPHx' := held_anc_at hrun D.hnc hd hy ht hPHx hHxt
    have hPt : D.P ∈ (tr.state y i).fg.tree := by
      by_cases he : D.P = Hx
      · exact he ▸ hHxt
      · exact (Anc.mem hPHx' he).1
    have hPh : ((tr.state y i).fg.σ D.P.root).h ≤ ((tr.state y i).fg.σ Hx.root).h := by
      have h := (honest_held_height hr hnc' hy (i := i) (by rw [hst]; exact hPHx')).1
      rwa [hst] at h
    have hsrc := ((rows_supported_at D hinv hy hc hs).by_ hrun).upTo_held ht
    obtain ⟨E, hEt, -, hEh, -, Ds, ⟨⟨hDsP, x', k', e'', hv', hs'', hext'⟩, hDsU⟩, hDs⟩ :=
      frame_crossing_source_before hr hnc' hf hy (i := i) hsrc (by rw [hst]; exact hX)
        (j := (tr.state y i).fg.hmax - 1) (by omega) (by rw [hst]; omega)
    have hPU : D.P ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
      ⟨y, hy, i, by rw [hst]; exact hPt⟩
    have hEh' := hEh
    rw [hst] at hEh'
    have hPE := below_entry hr hnc' hy (by rw [hst]; exact hPt) hEt hDs
      (compatible_upTo hrun D.hnc hd hDsU hPU hDsP) (by rw [hst]; omega)
    obtain ⟨z, hz, kz, -, -, hEDs, -, -⟩ := honest_source_entry hr hnc' hDs
      (fg_tree_subset_honest hy i hEt) rfl
    have hEDsU : Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) E Ds :=
      Anc.mono (fg_tree_subset_honest hz kz) hEDs
    have hPDs : Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D.P Ds :=
      (Anc.mono (fg_tree_subset_honest hy i) hPE).trans hEDsU
    obtain ⟨W, hW, hDsW⟩ := frozen x' k' e'' hv' hs'' Ds hext' (hFP.trans (Anc.mono hsub hPDs))
    have hWt := hvt W hW
    have hEW := honest_held_anc hr hnc' hy (hEDsU.trans (toU hWt hDsW))
      (by rw [hst]; exact hWt)
    have hWh := (honest_held_height hr hnc' hy hEW).1
    rw [hst] at hWh
    refine ⟨W, hW, (Anc.mono hsub hPDs).trans hDsW, ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    omega
  rcases vote_viable_at hrun D.hnc hy hc (B := D.P) (hinv.caches_at_cut le_rfl hy)
      (Or.inl hK2) with h | h
  · rw [hs] at h
    exact Or.inl h
  · right
    have hFP' : Anc (tr.HonestBlocksAt H) ℓ.frame.F D.P := hFℓ ▸ hFP
    have hPt := SA.frame_mem_of_between sp hU hΦ hΦU hΦ.fcRoot_mem h hFP'
    exact SA.anc_tree_of_anc_U hU hΦ hΦU hPt h hΦ.fcRoot_mem

/-- The invariant at the cuts before `i` holds at the cuts before every `k ≤ i`. -/
theorem OutageLockInv.mono {i k : Nat} (h : OutageLockInv D i) (hk : k ≤ i) :
    OutageLockInv D k where
  toOutageVoteInv := h.toOutageVoteInv.mono hk
  results y k' hk' := h.results y k' (by omega)
  locks y k' t hk' := h.locks y k' t (by omega)
  sources y k' hk' := h.sources y k' (by omega)
  caches y k' t hk' := h.caches y k' t (by omega)
  viable y k' t hk' := h.viable y k' t (by omega)
  protPrev x hx c ℓ hu hb k' hck hk' := h.protPrev x hx c ℓ hu hb k' hck (by omega)
  protCover x hx c ℓ hu hb k' hck hk' := h.protCover x hx c ℓ hu hb k' hck (by omega)

/-- **INV, the inner cut induction**: from the invariant at the cuts before `i` and receiver
service from `b₁`, every vote at a cut `≤ i` of a slot after `r`, by a node honest at its cut,
extends `P`. Root cover, Hi (H1) or Lo (G4 and the batch walk). For `q > r` the slot-`q` votes all
extend `P` by induction and are counted at the voter's cut; for `q = r` the cohort `A₀` is counted
against `(H z)ᶜ ∪ W` at `z ≥ t_k`. -/
theorem outage_s5_inner_at
    (hS : ∀ y, ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC)
    (i : Nat) (hinv : OutageLockInv D i) :
    ∀ k ≤ i, ∀ y e, HVoteAt tr H y k e → D.r < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  have hrun := D.hrun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hki y e hv hrs
  obtain ⟨q, hs⟩ : ∃ q, e.msg.slot = q + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hrq : D.r ≤ q := by omega
  have hinvk := hinv.mono D hki
  obtain ⟨hy, ℓ, hc⟩ := hVoteAt_iff.1 hv
  have hcast : SA.CastAt tr.projAC y k ℓ e := hc
  have hd := hrun.time_nonneg k
  have hcallk : tr.IsCall y k := ⟨_, projAC_callAt.1 hcast.1⟩
  have hsl := (castAt_spec_at hrun D.hnc hy hcast).2.1
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun D.hnc hy hcast.1
  have hfr : ℓ.frame = Node.frame (tr.state y k) := frame_of_projAC_at hrun hy hcast.1
  have hFℓ : ℓ.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
  have hL := readPoint_liveLockBlocks_compatible_at D hinvk hy hcast
    (show 0 < sp.slot (tr.time k) by rw [← hsl]; omega) .refl
  obtain ⟨htk, htk'⟩ := hv.ts_le_cast hrun D.hnc
  rw [hs] at htk htk'
  have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have htk1 : sp.ts ((q + 1 : Nat) : Int) ≤ tr.time k := htk
  have hg : D.b₁ ≤ sp.ts q + sp.Δ := by
    have := ts_le_ts (sp := sp) hrq
    linarith only [this, D.hr.1]
  -- root cover
  by_cases hPF : Anc (tr.HonestBlocksAt H) D.P (tr.state y k).fg.F
  · obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := cast_head_fcRoot_at hrun D.hnc hy hcast
    exact ⟨Hd, hΦU hHd, hHdr, hPF.trans (hFℓ ▸ Anc.mono hΦU (hΦ.rooted.2 Hd hHd))⟩
  have hFP : Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P :=
    ((hinvk.caches_at_cut le_rfl hy).1).resolve_right hPF
  -- Hi
  by_cases hHi : HiAt tr H D.P y k
  · exact vote_extends_of_hi_at D hinvk hy hcast hHi hL
  -- Lo: a carried batch extending `P`
  have hcarry : ∀ SX : Set (Fin sp.n), (∀ x ∈ SX, ∀ j e', HVoteAt tr H x j e' →
      e'.msg.slot = q → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg D.P) →
      SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e q
        {v | ∃ x ∈ SX, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg = v ∧ v.slot = q} := by
    intro SX hall
    refine carryAt_after_at hrun D.hnc (hS y) hg hy hcast hs fun v hv' => ?_
    obtain ⟨x, hx, j, e', hve, rfl, hvs⟩ := hv'
    obtain ⟨Hd, hHd, hHdr, hPHd⟩ := hall x hx j e' hve hvs
    exact ⟨x, j, e', hve, rfl, hvs, Hd, hHd, hHdr, hFℓ ▸ hFP.trans hPHd⟩
  have hviab : (∃ x j e', HVoteAt tr H x j e' ∧ e'.msg.slot = q ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg D.P) → SA.ViableAtVote ℓ e (q + 1) D.P :=
    viable_at_vote_of_lo_at D hinvk hy (hS y) hcast hs hrq hHi hFP
  rcases hrq.lt_or_eq with hrq' | rfl
  · -- `q > r`: every earlier slot-`q` vote extends `P` (induction), counted at the voter's cut
    have hall : ∀ x j e', j < k → HVoteAt tr H x j e' → e'.msg.slot = q →
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg D.P := fun x j e' hjk hve hvs =>
      ih j hjk (by omega) x e' hve (by omega)
    have hBK := D.hBK (tr.time k) ⟨y, k, hy, hcallk, le_rfl⟩
    have hcount := faults_lt_voters hrun D.hnc D.facts hBK (s := q) (d := tr.time k)
      (Nat.zero_le _) (by linarith only [htk1, hts, hΔ]) le_rfl
      (by linarith only [htk', hs, hts, hΔ])
    obtain ⟨x, hx⟩ : (VotersAt tr H q (tr.time k)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      rw [h, Set.ncard_empty] at hcount
      omega
    obtain ⟨-, j, e', hve, hvs⟩ := votersAt_iff.1 hx
    have hjk := (vote_cut_lt hrun D.hnc hve hvs htk1).2
    exact vote_extends_of_batch_at hrun D.hnc D.facts hBK (Nat.zero_le _) hy hcast hs le_rfl
      (hviab ⟨x, j, e', hve, hvs, hall x j e' hjk hve hvs⟩) hall
      (by
        have h := hcarry Set.univ fun x _ j e' hve hvs =>
          hall x j e' (vote_cut_lt hrun D.hnc hve hvs htk1).2 hve hvs
        simpa only [Set.mem_univ, true_and] using h)
      hL
  · -- `q = r`: the cohort `A₀` casts and extends `P`; the other casters honest at `t_k` are
    -- late wakers or compromised by `z ≥ t_k`
    have hσ := D.hσ
    have hrk := D.hrk
    have hrK := ts_le_ts (sp := sp) hrk.2
    have hkz : tr.time k ≤ D.z := D.hzc _
      (by have := htk'; linarith only [this, hs, hts, hrK, hΔ]) ⟨y, k, hy, hcallk, le_rfl⟩
    have hA₀k : D.A₀ ⊆ H (tr.time k) := fun x hx => hrun.antitone hkz (D.hA₀ hx)
    have hall : ∀ x ∈ D.A₀, ∀ j e', HVoteAt tr H x j e' → e'.msg.slot = D.r →
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg D.P := fun x hx j e' hve hvs =>
      hinvk.votes x j (vote_cut_lt hrun D.hnc hve hvs htk1).2 e' hve (by omega) (by omega)
        (Or.inr hx)
    have hcallr : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧
        sp.ts D.r + sp.Δ ≤ tr.time i :=
      ⟨y, k, hy, hcallk, by linarith only [htk1, hts, hΔ]⟩
    have hSXv : ∀ x ∈ D.A₀, ∃ j e', HVoteAt tr H x j e' ∧ e'.msg.slot = D.r := by
      intro x hx
      obtain ⟨haw, hjn⟩ := OutageVoteInv.cohort_ready_at D hx hrk.1 hrk.2 hcallr
      have hxr : x ∈ H (sp.ts D.r + sp.Δ) := hrun.antitone
        (D.hzc _ (by linarith only [hrK, hΔ]) hcallr) (D.hA₀ hx)
      obtain ⟨j, e', hve, hvs, -⟩ := vote_of_awake_joined_at hrun D.hnc hxr
        -- TEMP(C2): C3c replaces
        (mayVote_at hrun D.hnc (ts_add_delta_nonneg _) hxr (D.hmv _ _)) haw hjn
      exact ⟨j, e', hve, hvs⟩
    have hW : ∀ x j e', HVoteAt tr H x j e' → x ∈ H (tr.time k) → e'.msg.slot = D.r →
        x ∈ D.A₀ ∪ ((H D.z)ᶜ ∪ D.W) := by
      intro x j e' hve _ hvs
      obtain ⟨hts', -⟩ := hve.ts_le_cast hrun D.hnc
      rw [hvs] at hts'
      have hjr := ts_le_ts (sp := sp) (show D.j₀ + 1 ≤ D.r by omega)
      have hj₁ : sp.ts (D.j₀ + 1 : Nat) = sp.ts D.j₀ + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      have hjk := (vote_cut_lt hrun D.hnc hve hvs htk1).2
      rcases D.cohort_classify hve (by linarith only [D.ha, hts', hjr, hj₁, hΔ])
          ((hrun.time_mono hjk.le).trans hkz) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hWc : (H (tr.time k))ᶜ ⊆ D.A₀ ∪ ((H D.z)ᶜ ∪ D.W) := fun x hx =>
      Or.inr (Or.inl fun hxz => hx (hrun.antitone hkz hxz))
    have hcount : (D.A₀ ∪ ((H D.z)ᶜ ∪ D.W)).ncard < 2 * D.A₀.ncard := by
      have := Set.ncard_union_le D.A₀ ((H D.z)ᶜ ∪ D.W)
      have := D.hcohort
      omega
    obtain ⟨x, hx⟩ : D.A₀.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      have := D.hcohort
      rw [h, Set.ncard_empty] at this
      omega
    obtain ⟨j, e', hve, hvs⟩ := hSXv x hx
    exact vote_extends_of_counted_batch_run hrun D.hnc hy hcast hs
      (hviab ⟨x, j, e', hve, hvs, hall x hx j e' hve hvs⟩) hA₀k hSXv hall hW hWc hcount
      (hcarry D.A₀ hall) hL

/-- **Lock safety's `hS5`**: compatibility past the lock lifetime, from the inner induction at
the cast cut. -/
theorem outage_s5_step_at
    (hS : ∀ y, ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC) :
    OutageS5StepAt D := by
  rw [outageS5StepAt_iff]
  intro i hinv y e hv hs
  have hrk := D.hrk
  exact (outage_s5_inner_at D hS i hinv i le_rfl y e hv (by omega)).voteCompat

/-- **INV at all cuts**: every vote of a slot after `r`, by a node honest at its cut, extends
`P`. -/
theorem restored_votes_extend_at
    (hS : ∀ y, ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) :
    ∀ y k e, HVoteAt tr H y k e → D.r < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P :=
  fun y k e hv hs => outage_s5_inner_at D hS k (hinv k) k le_rfl y e hv hs

end Consensus.Goldilocks.Compose.Growing

end
