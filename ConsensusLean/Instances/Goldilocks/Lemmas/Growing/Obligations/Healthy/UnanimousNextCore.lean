module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.UnanimousStep
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy

public section

/-! # The slot after a unanimous slot, under growing faults: the cores

The cores of the growing unanimous next-slot helpers of `Healing/OperationalReports`. Each reads
the run, `ResetService`, `Catch(2Δ)` and `ḡ ≤ t_u`, with its remaining inputs explicit; none
reads a reset:

* `unanimous_carry_votes_core_at`: the slot-`u` votes of nodes honest at their casts are carried
  to a slot-`(u+1)` cast;
* `unanimous_next_vote_viable_core_at`: the unanimous proposal `P` is in the frozen viable tree of
  a slot-`(u+1)` cast, given the caster's own slot-`u` vote by `t_u + Δ`, its finalized tip
  below `P`, and viability of `P`;
* `unanimous_next_votes_extend_core_at`: every slot-`(u+1)` vote extends `P`, by strong induction
  on the vote's cut, with the batch counted at the voter's cut (every validator honest at
  `t_{u+1}` voted in slot `u` by `t_u + Δ`, and the fault bound at the cut).

The `ResetPremisesUpTo` forms are in `UnanimousNext`. Each node is honest at its own cut. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-! ### Prefix tools -/

/-- The static AC run of the prefix through `tr.time i`, for the validators honest then. -/
theorem acRun_upTo_time {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (i : Nat) :
    AC.ACRun proposer (tr.upTo (tr.time i)).projAC (H (tr.time i))
      ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ini :=
  Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _)

/-- A cast at a cut at or before `d` is one of the prefix through `d`. -/
theorem castAt_upTo_of_le {d : Time} {y : Fin sp.n} {j : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))} (hjd : tr.time j ≤ d)
    (hc : AC.CastAt tr.projAC y j ell e) : AC.CastAt (tr.upTo d).projAC y j ell e := by
  rw [RunTrace.upTo_projAC]
  exact ⟨(Trace.upTo_callAt_of_le tr.projAC hjd).mpr hc.1, hc.2⟩

/-- A block accepted before the freeze and above the voter’s finality is in the frozen tree. -/
theorem accepted_voter_tree_of_accept_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k j s : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hs : e.msg.slot = s + 1) (hkj : k ≤ j)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt y k P)
    (ht : tr.time k < sp.ts s + 3 * sp.Δ) (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    P ∈ AC.voterBlockTree sp e.readPoint ell.frame (s + 1) := by
  have hd := hrun.time_nonneg j
  have hr := (acRun_upTo_time hrun hnc j).localRun
  have ha' : (tr.upTo (tr.time j)).projAC.AcceptAt y k P := by
    rw [RunTrace.upTo_projAC]
    exact (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hrun.time_mono hkj, ha⟩
  have hP : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    obtain ⟨ella, hca, _⟩ := id ha'
    exact (AC.frameIn_of_callAt hr hy hca).2 ((AC.accept_new sp hr hy ha').1 ella hca)
  exact Compose.accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy
    (castAt_upTo_of_le le_rfl hc) hs hP (Or.inr ⟨k, ha', ht⟩)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hP hFP)

/-! ### Service and catch-up at the voter, with each sender honest at its own cut -/

/-- A vote cast at or after `g` by a node honest at its cast is served to every node honest at
a later call whose deadline for it has passed. -/
theorem served_of_resetService
    (hsvc : ResetService tr H g ΔF b hold) {z : Fin sp.n} {q : Nat}
    {ell' : ACLabel (goldilocksNode sp)} {e' : AC.Em sp (List (FG.Att sp.n))}
    (hz : z ∈ H (tr.time q)) (hcz : AC.CastAt tr.projAC z q ell' e') (hgq : g ≤ tr.time q)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time q) ≤ tr.time i) :
    AC.MessageServedBefore tr.projAC y i (tr.time q) e'.msg := by
  have he : max (tr.time q) g = tr.time q := max_eq_left hgq
  obtain ⟨k, hkj, htk, hp, hlt⟩ := hsvc.message z q e'.msg hz
    ⟨ell', Compose.projAC_callAt.mp hcz.1, Or.inl ⟨e', hcz.2, rfl⟩⟩ y i hy
    ⟨_, Compose.projAC_callAt.mp hci⟩ (by rw [he, ← Compose.projAC_deadline]; exact hdl)
  refine (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k, hkj, htk, ?_, ?_⟩)
  · rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩,
      ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr hm'⟩]
  · rw [Compose.projAC_deadline]
    change tr.time k < _
    simpa only [he] using hlt

/-- An AC acceptance at or after `g` of a node honest at it is relayed to every node honest at
a later call whose deadline for it has passed, once the block is above that node's `Σ.F`. -/
theorem relayed_of_resetService
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hsvc : ResetService tr H g ΔF b hold) {z : Fin sp.n} {k : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hgk : g ≤ tr.time k)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time k) ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < tr.projAC.deadline y k' (tr.time k) := by
  apply hrun.toLocalRun.acRelayAt (σ := tr.time k) hz hacc hy hci hanc
  intro q hq hz' haq hj hF
  have hgq : g ≤ tr.time q := hq ▸ hgk
  have he : max (tr.time q) g = tr.time k := (max_eq_left hgq).trans hq
  simpa only [he] using hsvc.relay z q B hz' haq hgq y i hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- An AC acceptance before `ḡ` of a node honest at it is caught up before `ḡ + 2Δ` by every node
honest at a call from `ḡ + 2Δ` on, once the block is above that node's `Σ.F`. -/
theorem caught_of_catchRun {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hc : CatchRun tr H g (2 * sp.Δ)) {z : Fin sp.n} {k : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hkg : tr.time k < AC.gbar g)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hti : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < AC.gbar g + 2 * sp.Δ := by
  exact hrun.toLocalRun.acCatchAt hc hz hacc hkg hy hci hti hanc

/-! ### The carried slot-`u` votes -/

/-- **The slot-`u` votes of nodes honest at their casts are carried to a slot-`(u+1)` cast** of a
node honest at it, when every such vote names the honest block `P`, `P` is above the cast's `Σ.F`,
and `ḡ ≤ t_u`: each vote is served (`ResetService`), and `P` is relayed (accepted from `g` on)
or caught up (`Catch(2Δ)`, accepted before `ḡ`). -/
theorem unanimous_carry_votes_core_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : AC.gbar g ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) := by
  exact UnanimousStep.carry_votes_of_unanimous hrun hnc hsvc hc hP hun hg hy hcast hs hib hFP

/-! ### The frozen viable tree of the next slot -/

/-- **A later caller accepts the unanimous proposal before `t_u + 3Δ`**: a node honest at a call
from `t_u + 2Δ` on, with `P` above the call's `Σ.F`, accepted `P` before `t_u + 3Δ`, given a
slot-`u` vote by `t_u + Δ` of some node honest at it. The voter's acceptance of `P` reaches the
caller by relay from `g` on and by catch-up before `ḡ`. Only the caller's own restarts before the
call are bounded. -/
theorem unanimous_head_accepted_core_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : AC.gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    (hcall : tr.projAC.CallAt y j ell) (hti : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ AC.gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    ∃ k' ≤ j, tr.projAC.AcceptAt y k' P ∧ tr.time k' < sp.ts u + 3 * sp.Δ := by
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  -- the voter's slot-`u` vote names `P`, which it accepted by its vote
  obtain ⟨w, q, e', hwq, ⟨ellv, hv⟩, hvs, hq⟩ := hvote
  have hqj : tr.time q ≤ tr.time j := by linarith
  have hrq := acRun_upTo_time hrun hnc q
  have hvq := castAt_upTo_of_le le_rfl hv
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hrq.localRun hrq.vstart hwq hvq
  have hHdq := (AC.frameIn_of_callAt hrq.localRun hwq hvq.1).2 hHd
  obtain rfl : Hd = P := hU.1 (RunTrace.honestBlocks_upTo_subset (H := H) hm
    (hrun.time_nonneg q) hHdq) hP (he.trans (hun w q e' hwq ⟨ellv, hv⟩ (hqj.trans hjb) hvs))
  obtain hz | ⟨k, hk, ha⟩ := AC.frame_genesis_or_acceptedU sp hrq.localRun.toU hwq hvq.1 Hd hHd
  · omega
  rw [RunTrace.upTo_projAC] at ha
  obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
  change tr.time k ≤ tr.time q at hkq
  have hwk := hrun.antitone hkq hwq
  have hdl : ∀ c ≤ j, tr.projAC.deadline y c (tr.time k) ≤ max (tr.time k) (AC.gbar g) + sp.Δ :=
    fun c hcj => Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
      (fun r hrc hrs => hnr r (hrc.trans hcj) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
  by_cases hkg : AC.gbar g ≤ tr.time k
  · obtain ⟨k', hk'j, ha', hlt⟩ := relayed_of_resetService hrun hsvc hwk ha
      ((AC.le_gbar g).trans hkg) hy hcall
      ((hdl j le_rfl).trans (by rw [max_eq_left hkg]; linarith)) hanc
    have := hdl k' hk'j
    rw [max_eq_left hkg] at this
    exact ⟨k', hk'j, ha', by linarith⟩
  · obtain ⟨k', hk'j, ha', hlt⟩ := caught_of_catchRun hrun hc hwk ha (not_le.mp hkg) hy
      hcall (by linarith) hanc
    exact ⟨k', hk'j, ha', by linarith⟩

/-- **The unanimous proposal is in the frozen viable tree of a slot-`(u+1)` cast** of a node
honest at it, given a slot-`u` vote by `t_u + Δ` of some node honest at it, the caster's
fork-choice root below `P`, and viability of `P` once `P` is held. The
caster accepts `P` before the freeze `t_u + 3Δ` (`unanimous_head_accepted_core_at`). Only the
caster's own restarts before the cast are bounded. -/
theorem unanimous_next_vote_viable_core_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : AC.gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b)
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ AC.gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hroot : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P)
    (hviable : P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.IsViable P) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := Compose.Growing.frameIn_at hrun hnc hy hcast.1
  have hfr := Outcome.frame_of_call hrun hy hcast.1
  have hrootFrame : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P := hfr.symm ▸ hroot
  -- the cast is at `t_{u+1}` or later
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    have h := (Compose.Growing.castAt_spec_at hrun hnc hy hcast).2.1
    change e.msg.slot = sp.slot (tr.time j) at h
    exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega)
  have hanc : Anc (tr.HonestBlocksAt H) ell.frame.F P :=
    (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootFrame
  -- the caster accepts `P` before the freeze
  obtain ⟨k', hk'j, ha', hk't⟩ := unanimous_head_accepted_core_at hrun hnc hsvc hc hP hslot hu
    hun hg hy hcast.1 (by linarith [AC.ts_succ (sp := sp) u]) hjb hnr hvote hanc
  have hPt := accepted_voter_tree_of_accept_at hrun hnc hy hcast hs hk'j ha' hk't hanc
  have hroot' := AC.anc_tree_of_anc_U (Compose.Growing.honest_blocks_coherent hrun hnc)
    hPhi hPhiU hPhi.fcRoot_mem hrootFrame hPt.1
  refine ⟨hanc, hPt, hroot', P, hPt, ?_, .refl⟩
  have hmem := hPt.1
  rw [hfr] at hmem ⊢
  exact ⟨hmem.1, hmem.2, hviable hmem.1⟩


/-! ### Every slot-`(u+1)` vote extends `P` -/

/-- Extend an already established prefix through the next slot, using viability at each cast. -/
theorem extend_next_votes_core_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {m : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hg : AC.gbar g ≤ sp.ts m) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hvotes : ∀ x, x ∈ H (sp.ts (m + 1 : Nat)) → x ∈ K.committee m → ∃ q e,
      AC.VoteAt tr.projAC x q e ∧ e.msg.slot = m ∧ tr.time q ≤ sp.ts m + sp.Δ)
    (hfault : ∀ i, sp.ts (m + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK K m tr.projAC (H (tr.time i)) (tr.time i))
    (hcs2 : ∀ i, sp.ts (m + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * (K.committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hcast : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = m + 1 → tr.time j ≤ b →
      (∀ x q e', q < j → x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e' →
        e'.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg P) →
      Anc (tr.HonestBlocksAt H) ell.frame.F P ∧ AC.ViableAtVote ell e (m + 1) P) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  apply UnanimousStep.next_votes_extend_of_viable hrun hnc
  · intro y j ell e hy hc' hs hjb ih
    exact Or.inr (hcast y j ell e hy hc' hs hjb fun x q e' hq hx hv hvs => ih x q hq hx e' hv hvs)
  · intro y j ell e hy hc' hs hjb hFP hvi ih
    have htime := (Compose.Growing.cast_time_at hrun hnc hy hc').1
    rw [hs] at htime
    exact UnanimousStep.next_vote_of_batch hrun hnc hsvc hc hext hg hPK hTK hsize hy hc' hs hjb
      (fun x hx => hvotes x (hrun.antitone htime hx.2) hx.1)
      (hfault j htime hjb) (hcs2 j htime hjb) hFP hvi ih


/-- **Every slot-`(u+1)` vote of a node honest at it extends the unanimous proposal `P`**, by
strong induction on the vote's cut. The batch is counted at the voter's cut among the slot-`u`
committee: its members honest at `t_{u+1}` voted in slot `u` by `t_u + Δ` (`hvotes`), and CS at the
cut (`hfault`) leaves more than half of the committee honest then; CS2 bounds the slot-`(u+1)`
committee (`hcs2`). One slot-`u` vote by `t_u + Δ` (`hwit`) puts `P` in every caster's frame. The
finalized tip and proposal viability of each cast (`hroot`, `hviable`) are inputs. -/
theorem unanimous_next_votes_extend_core_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : AC.gbar g ≤ sp.ts u) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hnr : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b →
      tr.time k ≤ AC.gbar g)
    (hwit : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hvotes : ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → x ∈ K.committee u → ∃ q e,
      AC.VoteAt tr.projAC x q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ)
    (hfault : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK K u tr.projAC (H (tr.time i)) (tr.time i))
    (hcs2 : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * (K.committee (u + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hroot : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P)
    (hviable : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.IsViable P) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  apply extend_next_votes_core_at hrun hnc hsvc hc (P := P)
    (fun x q e hx hv hqb hs => ⟨P, hP, (hun x q e hx hv hqb hs).symm, .refl⟩)
    hg hPK hTK hsize hvotes hfault hcs2
  intro y j ell e hy hcast hs hjb _
  obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable_core_at hrun hnc hsvc hc hP hslot hu
    hun hg hy hcast hs hjb
    (fun r hrj hrs => hnr y r (hrun.antitone (hrun.time_mono hrj) hy) hrs
      ((hrun.time_mono hrj).trans hjb)) hwit (hroot y j ell e hy hcast hs hjb)
    (hviable y j ell e hy hcast hs hjb)
  exact ⟨hFP, Or.inl hvi⟩

end Consensus.Goldilocks.Healing.Growing

end
