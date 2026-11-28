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
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy

public section

/-! # The slot after a unanimous slot, under growing faults: the cores

The cores of the growing unanimous next-slot helpers of `Healing/OperationalReports`. Each reads
the run, `ResetService`, `Catch(2Δ)` and `ḡ ≤ t_u`, with its remaining inputs explicit; none
reads a reset:

* `unanimous_carry_votes_core_at`: the slot-`u` votes of nodes honest at their casts are carried
  to a slot-`(u+1)` cast;
* `unanimous_next_vote_viable_core_at`: the unanimous proposal `P` is in the frozen viable tree of
  a slot-`(u+1)` cast, given the caster's own slot-`u` vote by `t_u + Δ`, its fork-choice root
  below `P`, and its head-height floor at or below `P`;
* `unanimous_next_votes_extend_core_at`: every slot-`(u+1)` vote extends `P`, by strong induction
  on the vote's cut, with the batch counted at the voter's cut (every validator honest at
  `t_{u+1}` voted in slot `u` by `t_u + Δ`, and the fault bound at the cut);
* `unanimous_next_optimistic_compatible_core_at`: a slot-`(u+1)` optimistic selection is
  compatible with `P`, through a supporting vote of a node honest at its cast.

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
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg i
  have hΔ := sp.toParams.hΔ
  have hgg := AC.le_gbar g
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hr := (acRun_upTo_time hrun hnc i).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time i := by
    have h := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hcarry := Compose.carryAt_of_served hr
    (acRun_upTo_time hrun hnc i).vstart (Compose.frame_anc_acceptedU hr.toU hy) hy hc' hs
    (CV := Compose.Growing.honestVotes tr H u) fun v hv => by
    obtain ⟨z, q, e', hz, ⟨ell', hcz⟩, rfl, hsl⟩ := hv
    have hdq := hrun.time_nonneg q
    have hrq := (acRun_upTo_time hrun hnc q).localRun
    have hcz' := castAt_upTo_of_le le_rfl hcz
    have hslq := (AC.castAt_specU hrq.toU hz hcz').2.1
    change e'.msg.slot = sp.slot (tr.time q) at hslq
    have hqts : sp.ts u ≤ tr.time q := (AC.ts_le_iff_le_slot sp hdq _).2 (by omega)
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq (acRun_upTo_time hrun
      hnc q).vstart hz hcz'
    rw [hsl] at hqt
    change tr.time q ≤ _ at hqt
    have hqi : tr.time q ≤ tr.time i := by linarith
    have hHdp := (AC.frameIn_of_callAt hrq hz hcz'.1).2 hHd
    have hsubq := RunTrace.honestBlocks_upTo_subset (H := H) hm hdq
    obtain rfl : Hd = P := hU.1 (hsubq hHdp) hP
      (hHdr.trans (hun z q e' hz ⟨ell', hcz⟩ (hqi.trans hib) hsl))
    refine ⟨hsl, ⟨tr.time q, hqts, by linarith, fun hdl => ?_⟩, Hd, hHdr, ?_⟩
    · rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      exact (AC.upTo_messageServedBefore hmA le_rfl).mpr
        (served_of_resetService hsvc hz hcz (hgg.trans (hg.trans hqts)) hy hcast.1 hdl)
    rcases Compose.frame_anc_acceptedU hrq.toU hz q ell' hcz'.1 Hd hHd Hd .refl
        with h0 | ⟨k, hk, ha⟩
    · exact Or.inr (Or.inl h0)
    rw [RunTrace.upTo_projAC] at ha
    obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
    change tr.time k ≤ tr.time q at hkq
    have hzk := hrun.antitone hkq hz
    by_cases hkg : AC.gbar g ≤ tr.time k
    · refine Or.inl ⟨tr.time k, by linarith, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      obtain ⟨ky, hky, hacc, hkyt⟩ := relayed_of_resetService hrun hsvc hzk ha (hgg.trans hkg) hy
        hcast.1 hdl hFP
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hkyd, hacc⟩,
        by rw [ACTrace.upTo_deadline hmA hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc, hkyt⟩ := caught_of_catchRun hrun hc hzk ha (not_le.mp hkg) hy
        hcast.1 (by linarith) hFP
      exact Or.inr (Or.inr ⟨ky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr
        ⟨hm hky, hacc⟩, by change tr.time ky < _; linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp hk).2, hkt⟩

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
fork-choice root below `P`, and its head-height floor at or below `P` once `P` is held. The
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
    (hroot : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.fcRoot P)
    (hfloor : P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg j
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hr := (acRun_upTo_time hrun hnc j).localRun
  have hc' := castAt_upTo_of_le le_rfl hcast
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc'.1
  have hj : ∀ k < j, tr.time k ≤ tr.time j := fun _ h => hm h.le
  have hreach := fg_reachable_at hrun hd hj hy
  have hcache := Store.cache_invariants _ _ _ _ hreach
  have hFroot : (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.fcRoot := by
    unfold Store.fcRoot
    split_ifs
    · exact hcache.2.2.1
    · exact .refl
  have hFrootU := hFroot.mono fun X hX =>
    (⟨y, j, tr.time j, hd, hj, hy, hX⟩ : X ∈ tr.HonestBlocksAt H)
  have hFPu := hFrootU.trans hroot
  have hrootFrame : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P := by
    rw [Outcome.frame_of_call hrun hy hcast.1]
    exact hFPu
  -- the cast is at `t_{u+1}` or later
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    have h := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time j) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hanc : Anc (tr.HonestBlocksAt H) ell.frame.F P :=
    (((hPhi.F_anc_fcRoot.mono hPhiU).mono hsub).trans hrootFrame)
  -- the caster accepts `P` before the freeze
  obtain ⟨k', hk'j, ha', hk't⟩ := unanimous_head_accepted_core_at hrun hnc hsvc hc hP hslot hu
    hun hg hy hcast.1 (by linarith) hjb hnr hvote hanc
  have ha'' : (tr.upTo (tr.time j)).projAC.AcceptAt y k' P := by
    rw [RunTrace.upTo_projAC]
    exact (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hm hk'j, ha'⟩
  have hHdp : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    obtain ⟨ella, hca, hba⟩ := ha''
    exact (AC.frameIn_of_callAt hr hy hca).2
      ((AC.accept_new sp hr hy ⟨ella, hca, hba⟩).1 ella hca)
  have hrootp := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdp hrootFrame
  have hFP := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootp
  have hacc : AC.AcceptedBefore (tr.upTo (tr.time j)).projAC y P (sp.ts u + 3 * sp.Δ) :=
    Or.inr ⟨k', ha'', hk't⟩
  have hPt := Compose.accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy hc' hs hHdp hacc hFP
  have hfr := Compose.frame_of_projAC (hrun.upTo hd) hy hc'.1
  have hst := RunTrace.upTo_state_of_le (y := y) hm (le_refl (tr.time j))
  have hstore : P ∈ (tr.state y j).fg.tree := by
    have hmem := hPt.1
    rw [hfr, hst] at hmem
    exact hmem.1
  have hfl := hfloor hstore
  have hroot' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hrootp hPt.1
  refine ⟨Anc.mono hsub hFP, hPt, hroot', P, hPt, ?_, .refl⟩
  have hmem := hPt.1
  rw [hfr, hst] at hmem hroot' ⊢
  refine ⟨hmem.1, hmem.2, ?_⟩
  have hrootStore := Store.anc_of_anc_universe hreach hU
    (fun X hX => ⟨y, j, tr.time j, hd, hj, hy, hX⟩) hroot hstore
  by_cases hh : (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ P.root).h
  · exact Or.inl hh
  have hpred : ((tr.state y j).fg.σ P.root).h + 1 = (tr.state y j).fg.hmax := by
    have hb : (tr.state y j).fg.hmax - 1 ≤ (tr.state y j).fg.headHeightFloor := by
      unfold Store.headHeightFloor
      split_ifs <;> omega
    omega
  refine Or.inr ⟨hpred, ?_⟩
  by_cases hgap : (tr.state y j).fg.hj + 1 < (tr.state y j).fg.hmax
  · exact Or.inl hgap
  right
  have htop : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 := by
    obtain ⟨C, hC, -, hCh⟩ := hcache.2.2.2.1
    have := Store.hj_lt_h hreach hC
    have := hcache.2.2.2.2.1 C hC
    omega
  have hnc : ¬ (tr.state y j).fg.Contest := by
    intro hc
    have hf : (tr.state y j).fg.headHeightFloor = (tr.state y j).fg.hmax := by
      simp only [Store.headHeightFloor, ite_eq_left hc]
    omega
  simpa only [Store.fcRoot, ite_eq_left (show
    (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest from
      ⟨htop, hnc⟩)] using hrootStore


/-! ### Every slot-`(u+1)` vote extends `P` -/

/-- **Every slot-`(u+1)` vote of a node honest at it extends the unanimous proposal `P`**, by
strong induction on the vote's cut. The batch is counted at the voter's cut among the slot-`u`
committee: its members honest at `t_{u+1}` voted in slot `u` by `t_u + Δ` (`hvotes`), and CS at the
cut (`hfault`) leaves more than half of the committee honest then; CS2 bounds the slot-`(u+1)`
committee (`hcs2`). One slot-`u` vote by `t_u + Δ` (`hwit`) puts `P` in every caster's frame. The
fork-choice root and the head-height floor of each cast (`hroot`, `hfloor`) are inputs. -/
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
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.fcRoot P)
    (hfloor : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hacr := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have all : ∀ j, tr.time j ≤ b → ∀ y e, y ∈ H (tr.time j) →
      AC.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y e hy ⟨ell, hcast⟩ hs
      have htime : sp.ts (u + 1 : Nat) ≤ tr.time j := by
        have := (Compose.Growing.cast_time_at hrun hnc hy hcast).1
        rwa [hs] at this
      obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable_core_at hrun hnc hsvc hc hP hslot hu hun
        hg hy hcast hs hjb
        (fun r hrj hrs => hnr y r (hrun.antitone (hrun.time_mono hrj) hy) hrs
          ((hrun.time_mono hrj).trans hjb)) hwit (hroot y j ell e hy hcast hs hjb)
        (hfloor y j ell e hy hcast hs hjb)
      have hcarry := unanimous_carry_votes_core_at hrun hnc hsvc hc hP hun hg hy hcast hs hjb hFP
      have hf := hfault j htime hjb
      have hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
          AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u}.ncard := by
        have hsub : K.committee u ∩ H (tr.time j) ⊆ {x | x ∈ H (tr.time j) ∧ ∃ q e',
            x ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u} := by
          rintro x ⟨hxK, hx⟩
          obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x (hrun.antitone htime hx) hxK
          exact ⟨hx, q, e', hrun.antitone (by linarith) hx, hv, hvs⟩
        have h₁ := Set.ncard_le_ncard hsub
        have h₂ := Set.ncard_le_ncard (s := K.committee u ∩ {y | y ∈ H (tr.time j) ∧
            tr.projAC.awake y (tr.time j) ∧ AC.JoinedAt tr.projAC y (tr.time j)})
          (t := K.committee u ∩ H (tr.time j)) (fun x hx => ⟨hx.1, hx.2.1⟩)
        have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u) (H (tr.time j))
          (Set.toFinite _)
        rw [hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time j))ᶜ] at hsplit
        unfold AC.FaultBoundK at hf
        omega
      refine AC.Growing.next_transfer_from hacr K hPK hTK hsize hy hcast hs ?_ hhalf hcarry hf
        (hcs2 j htime hjb) (Or.inl hvi) ?_
      · intro x q e' hx hv hvs
        have hq := (Compose.Growing.cast_time_at hrun hnc hx hv.choose_spec).2
        rw [hvs] at hq
        exact ⟨P, hP, (hun x q e' hx hv (by linarith) hvs).symm, .refl⟩
      · intro x q hq hx e' hv hvs
        exact ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
  exact fun y j e hy hv hjb hs => all j hjb y e hy hv hs

/-! ### A slot-`(u+1)` optimistic selection -/

/-- An optimistic selection of a node honest at it, with fewer than half of the slot committee
faulty at its cut, has a supporting vote of a node honest at its cast, no later than the
selection, that extends the selected block: the optimistic voters are three quarters of the
committee (P). -/
private theorem optimistic_supporter_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) {y : Fin sp.n} {j s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hy : y ∈ H (tr.time j))
    (hopt : AC.OptimisticLockAt tr.projAC y j s D CV)
    (hf : 2 * (K.committee s ∩ (H (tr.time j))ᶜ).ncard < sp.committeeSize) :
    ∃ z q e, q ≤ j ∧ z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg j
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hacr := acRun_upTo_time hrun hnc j
  rw [RunTrace.upTo_projAC] at hacr
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ :=
    ((AC.upTo_optimisticLockAt (d := tr.time j) hmA).mpr ⟨le_rfl, hopt⟩)
  have hU := (AC.frameIn_of_callAt hacr.localRun hy hpt.1).2
  have hsl' : sp.slot ((tr.projAC.upTo (tr.time j)).time j) = s := hsl
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (AC.deepest_mem hsel).1.2.1
  rw [hsl'] at h34 hsel
  have hOK : AC.optimisticVoters sp A ell.frame s D ⊆ K.committee s := by
    rintro w ⟨v, hv, rfl, -⟩
    exact (AC.CommitteePAt.upTo hm hrun.antitone hPK (tr.time j)).2 y hy j ell A hpt s v hv
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ (H (tr.time j))ᶜ)
      (t := AC.optimisticVoters sp A ell.frame s D) (by omega)
  have hzH : v.val ∈ H (tr.time j) := by
    by_contra h
    exact hz ⟨hOK ⟨v, hv, rfl, R, hR, hRr, hBR⟩, h⟩
  obtain ⟨hvs, q, hqj, e, he, rfl⟩ := AC.optimisticPoint_pool_voteU hacr.toU hy hpt hv hzH
  obtain ⟨hqd, he⟩ := AC.upTo_voteAt.mp he
  exact ⟨_, q, e, hqj, hrun.antitone hqd hzH, he, hvs, R,
    hsub (hU hR), hRr, (hBR.mono hU).mono hsub⟩

/-- **A slot-`(u+1)` optimistic selection of a node honest at it is compatible with the unanimous
proposal `P`**: its supporting vote, of a node honest at its cast, extends both (counted
at the slot committees, as for `unanimous_next_votes_extend_core_at`). -/
theorem unanimous_next_optimistic_compatible_core_at
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
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.fcRoot P)
    (hfloor : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hopt : AC.OptimisticLockAt tr.projAC y j (u + 1) D CV)
    (hjb : tr.time j ≤ b) :
    Compatible (tr.HonestBlocksAt H) D P := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have htime : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    obtain ⟨_, _, _, hsl, _, _⟩ := hopt
    exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by
      change sp.slot (tr.time j) = u + 1 at hsl
      omega)
  obtain ⟨z, q, e, hqj, hz, hv, hs, Hd, hHd, he, hDH⟩ :=
    optimistic_supporter_at hrun hnc hPK hy hopt (hcs2 j htime hjb)
  obtain ⟨Hd', hHd', he', hPH⟩ := unanimous_next_votes_extend_core_at hrun hnc hsvc hc hP hslot
    hu hun hg hPK hTK hsize hnr hwit hvotes hfault hcs2 hroot hfloor z q e hz hv ((hrun.time_mono
      hqj).trans hjb) hs
  obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
  exact AC.anc_total hU hDH hPH

end Consensus.Goldilocks.Healing.Growing

end
