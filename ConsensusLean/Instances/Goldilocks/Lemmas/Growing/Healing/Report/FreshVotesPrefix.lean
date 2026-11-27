module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesPath
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ProposalLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CarryPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Prior honest votes force a cast's prefix on its read horizon -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- Proposal-start provenance lifts from the handler-specific supplier on each retained prefix. -/
theorem actual_proposal_start_live_origin_at
    {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (_hnc : Compose.NoCollRun dg tr)
    (hstart : ∀ {t : Time}, 0 ≤ t →
      AC.CommitteeP K (tr.upTo t).projAC (H t) →
      ∀ {s₀ p i : Nat}, 1 ≤ p →
      2 * (K.committee p ∩ (H t)ᶜ).ncard < sp.committeeSize → s₀ + sp.k ≤ p →
      ∀ {ell : ACLabel (goldilocksNode sp ro)}, proposer p ∈ H t →
      (tr.upTo t).projAC.CallAt (proposer p) i ell → ell.call = .proposal →
      (tr.upTo t).time i = sp.ts p →
      ∀ {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n},
      (AC.acProposal sp ((tr.upTo t).projAC.state (proposer p) i) ell.frame
        ((tr.upTo t).time i)).2 = some (d, pay) →
      d.start = ell.frame.fcRoot ∨
        ∃ l ∈ AC.liveLocks sp ((tr.upTo t).projAC.state (proposer p) i).locks
            ell.frame ((tr.upTo t).time i),
          s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
            B.root = l.block ∧ ell.frame.Anc d.start B)
    {g b : Time} {s₀ p i : Nat}
    (hgp : gbar g ≤ sp.ts p) (hib : tr.time i ≤ b)
    (hp : 1 ≤ p) (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H (tr.time i))
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (AC.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ AC.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  have hs := Trace.upTo_state tr.projAC (proposer p) (d := tr.time i) (i := i)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt (proposer p) i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hpay' : (AC.acProposal sp ((tr.upTo (tr.time i)).projAC.state (proposer p) i)
      ell.frame (tr.time i)).2 = some (d, pay) := by
    simpa only [RunTrace.upTo_projAC, hs] using hpay
  have h := hstart (hrun.time_nonneg i)
    (by
      rw [RunTrace.upTo_projAC]
      exact AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _)
    hp (hK.cs2 p hgp (hti ▸ hib) (tr.time i) (hrun.time_nonneg i) hib)
    hmargin hz hc' hcall hti hpay'
  simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using h

end Core

/-- Proposal-start provenance is local to the proposer's own honest call, at the slot committees
`K` of a run from `K`'s committee start. -/
theorem actual_proposal_start_live_origin_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time} {s₀ p i : Nat}
    (hgp : gbar g ≤ sp.ts p) (hib : tr.time i ≤ b)
    (hp : 1 ≤ p) (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H (tr.time i))
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (AC.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ AC.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  exact Core.actual_proposal_start_live_origin_at hrun.toCore hnc
    (fun ht => Healing.actual_proposal_start_live_origin (hrun.upTo ht) (hnc.upTo _))
    hgp hib hp hmargin hz hc hcall hti hpay hK

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

private theorem anc_upTo_of_right
    {K : AC.CommitteeDict sp.n}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {t : Time} (ht : 0 ≤ t)
    {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : C ∈ (tr.upTo t).HonestBlocks (H t))
    (h : Anc (tr.HonestBlocksAt H) B C) :
    Anc ((tr.upTo t).HonestBlocks (H t)) B C := by
  obtain ⟨y, hy, i, hC⟩ := hC
  have hp := rc.upTo ht
  have hsub : ((tr.upTo t).state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => rc.upTo_subset ht ⟨y, hy, i, hX⟩
  suffices Anc ((tr.upTo t).state y i).fg.tree B C from
    this.mono (fun _ hX => ⟨y, hy, i, hX⟩)
  induction h with
  | refl => exact .refl
  | @tail X Y _ hXY ih =>
    have hroot := (Store.accepted_tree_with hp.finalitySpec (hp.reachable y hy i)).2.2.2 Y hC
    rcases hroot.cases_tail with heq | ⟨Z, _, hZ⟩
    · rw [heq] at hXY
      cases hXY.2.2
    · obtain rfl : Z = X := (rc.coherent hnc).1 (hsub hZ.1) hXY.1
        (Option.some.inj (hZ.2.2.symm.trans hXY.2.2))
      exact (ih hZ.1).tail hZ

/-- Prior-slot heads from validators honest at their own casts force the receiving walk.
Only the healthy AC base on the receiver's read prefix is used. -/
theorem honest_prefix_of_finality_before_at
    {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hheads : ∀ x j ev, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j ev →
      ev.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg B)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ell.frame.Anc B (AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hd := hrun.time_nonneg i
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hac := hrun.acRun hnc
  have hri := (hrun.acRun_upTo hnc hd).localRun
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hslot := (AC.castAt_specU hri.toU hy hcast).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have ht := AC.vote_time_leU hri.toU hy ⟨ell, hcast⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
  rw [hslot] at ht
  have hstart : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp hd _).2 (by rw [hslot])
  have hstep : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
  have hS := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch hd (ht.trans hmb)
  have hPhi := AC.frameIn_of_callAt hS.run.localRun hy hci
  have hheads' : ∀ x ∈ H (tr.time i), ∀ j ev,
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j ev → ev.msg.slot = s →
      AC.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ev.msg B := by
    intro x hx j ev hv hs
    obtain ⟨ellx, hcx, hex⟩ := hv
    obtain ⟨hjd, hcx'⟩ := (Trace.upTo_callAt _).mp hcx
    obtain ⟨R, hR, hRr, _⟩ := AC.honest_headU hS.run.toU hx ⟨ellx, hcx, hex⟩
    obtain ⟨R', hR', hR'r, hBR⟩ := hheads x j ev (hrun.antitone hjd hx) ⟨ellx, hcx', hex⟩ hs
    have he : R' = R := hac.localRun.coherent.1 hR'
      (hrun.upTo_subset hd hR) (hR'r.trans hRr.symm)
    exact ⟨R, hR, hRr, anc_upTo_of_right hrun hnc hd hR (he ▸ hBR)⟩
  have hnr' : Healing.NoRestartAfter (tr.upTo (tr.time i)) (H (tr.time i)) (gbar g) := by
    intro x hx q hq
    obtain ⟨hqd, hq⟩ := (RunTrace.upTo_restartAt _).mp hq
    exact hnr x q (hrun.antitone hqd hx) hq
  have hrestarts : ∀ x ∈ H (tr.time i), ∀ q,
      ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) x q → tr.time q ≤ gbar g := by
    intro x hx q hq
    rw [← RunTrace.upTo_projAC] at hq
    exact hnr' x hx q (Compose.projAC_restartAt.mp hq)
  have hcarry := AC.honest_batch_carry_before hS hy hcast hes hm
    (by change sp.ts s + 2 * sp.Δ ≤ tr.time i
        rw [hstep] at hstart; linarith [sp.toParams.hΔ]) le_rfl
    (fun k hk t ht => by
      rw [← RunTrace.upTo_projAC]
      apply Compose.ac_deadline_le_of_restarts (a := sp.ts s)
      intro r _ hrs
      have := hnr' y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ gbar g at this
      change tr.time r ≤ _
      linarith [sp.toParams.hΔ])
    (fun k hk hrs => by
      have := hrestarts y hy k hrs
      change tr.time k < _
      linarith [sp.toParams.hΔ])
    (fun x hx j ev hv hs R hR hRr => by
      obtain ⟨R', hR', hR'r, hBR⟩ := hheads' x hx j ev hv hs
      have he : R' = R := hS.run.localRun.coherent.1 hR' hR (hR'r.trans hRr.symm)
      exact (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hB.2.1)).trans (he ▸ hBR))
  have hex := AC.honest_votes_in_slot_before hS hm
    (by rw [hstep] at hstart; linarith [sp.toParams.hΔ])
    (fun x hx r ht hrs => by
      have := hrestarts x hx r hrs
      rw [AC.ts_sub_one]
      change tr.time r ≤ _
      linarith)
  rw [← AC.viableTree_voteDomain_eq_of_viable ⟨B, hB⟩]
  exact AC.honest_prefix_of_carry sp hS.run K hS.hT hS.hsize
    (hS.cs2 s (by linarith [sp.toParams.hΔ]) (by linarith [sp.toParams.hΔ])) hy hcast hes hheads'
    (fun x hx hxK => by obtain ⟨j, ev, hv, hs, _⟩ := hex x hx hxK; exact ⟨j, ev, hv, hs⟩)
    hcarry (AC.viableTree_voterBlockTree_subset_voteDomain hB) haB

end Core

/-- Prior-slot heads from validators honest at their own casts force the receiving walk. -/
theorem honest_prefix_of_finality_before_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hheads : ∀ x j ev, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j ev →
      ev.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg B)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ell.frame.Anc B (AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  exact Core.honest_prefix_of_finality_before_at hrun.toCore hnc hsvc hawake hf hcatch hnr
    hm hmb hheads hy hc hes hB haB hK

end Consensus.Goldilocks.Healing.Growing

end
