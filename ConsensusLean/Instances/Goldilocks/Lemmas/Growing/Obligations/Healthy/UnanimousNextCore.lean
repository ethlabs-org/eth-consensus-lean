module
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
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer

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

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-! ### Prefix tools -/

/-- The static AC run of the prefix through `tr.time i`, for the validators honest then. -/
private theorem acRun_prefix (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (i : Nat) :
    SA.ACRun proposer (tr.upTo (tr.time i)).projAC (H (tr.time i))
      ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) :=
  Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i)) proposer
    (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _)

/-- A cast at a cut at or before `d` is one of the prefix through `d`. -/
private theorem castAt_prefix {d : Time} {y : Fin sp.n} {j : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))} (hjd : tr.time j ≤ d)
    (hc : SA.CastAt tr.projAC y j ell e) : SA.CastAt (tr.upTo d).projAC y j ell e := by
  rw [RunTrace.upTo_projAC]
  exact ⟨(Trace.upTo_callAt_of_le tr.projAC hjd).mpr hc.1, hc.2⟩

/-! ### Service and catch-up at the voter, with each sender honest at its own cut -/

/-- A vote cast at or after `g` by a node honest at its cast is served to every node honest at
a later call whose deadline for it has passed. -/
private theorem served_of_service
    (hsvc : ResetService tr H g ΔF b) {z : Fin sp.n} {q : Nat}
    {ell' : ACLabel (goldilocksNode sp ro)} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hz : z ∈ H (tr.time q)) (hcz : SA.CastAt tr.projAC z q ell' e') (hgq : g ≤ tr.time q)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time q) ≤ tr.time i) :
    SA.MessageServedBefore tr.projAC y i (tr.time q) e'.msg := by
  have he : max (tr.time q) g = tr.time q := max_eq_left hgq
  obtain ⟨k, hkj, htk, hp, hlt⟩ := hsvc.message z q e'.msg hz
    ⟨ell', Compose.projAC_callAt.mp hcz.1, Or.inl ⟨e', hcz.2, rfl⟩⟩ y i hy
    ⟨_, Compose.projAC_callAt.mp hci⟩ (by rw [he, ← Compose.projAC_deadline]; exact hdl)
  refine (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k, hkj, htk, ?_, ?_⟩)
  · rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩,
      ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr hm'⟩]
  · rw [Compose.projAC_deadline]
    change tr.time k < _
    simpa only [he] using hlt

/-- An AC acceptance at or after `g` of a node honest at it is relayed to every node honest at
a later call whose deadline for it has passed, once the block is above that node's `Σ.F`. -/
private theorem relayed_of_service
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hsvc : ResetService tr H g ΔF b) {z : Fin sp.n} {k : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hgk : g ≤ tr.time k)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time k) ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < tr.projAC.deadline y k' (tr.time k) := by
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  have hc := Compose.projAC_callAt.mp hci
  obtain ⟨k₀, rfl, hk₀, htk⟩ := Obligations.Growing.acBlock_prev_at hrun hz
    (Compose.projAC_callAt.mp hc₀) hb
  have hfr : ell.frame.F = (tr.state y i).fg.F := by
    rw [(hrun.cutLaw y i _ hc hy).1]
    rfl
  have he : max (tr.time k₀) g = tr.time k₀ := max_eq_left (htk ▸ hgk)
  obtain ⟨k', hk'i, hk', hlt⟩ := hsvc.relay z k₀ B (htk ▸ hz) hk₀ (htk ▸ hgk) y i hy ⟨_, hc⟩
    (by rw [he, htk, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
  obtain ⟨ℓ', hc', hb', htk'⟩ := Obligations.Growing.accept_next_at hrun
    (hrun.antitone (hrun.time_mono hk'i) hy) hk'
  have hk'i' : k' + 1 ≤ i := by
    rcases Nat.lt_or_eq_of_le hk'i with hlt' | rfl
    · omega
    · cases Option.some.inj (hk'.2.symm.trans hc.2)
  have hnr : ¬ tr.RestartAt y (k' + 1) := fun ⟨ℓr, hcr, hrestart⟩ => by
    cases Option.some.inj (hc'.2.symm.trans hcr.2)
    rw [hb'] at hrestart
    cases hrestart
  refine ⟨k' + 1, hk'i', ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
  rw [Compose.projAC_deadline, htk', ← htk]
  simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
  simpa only [he] using hlt

/-- An AC acceptance before `ḡ` of a node honest at it is caught up before `ḡ + 2Δ` by every node
honest at a call from `ḡ + 2Δ` on, once the block is above that node's `Σ.F`. -/
private theorem caught_of_catch (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hc : CatchRun tr H g (2 * sp.Δ)) {z : Fin sp.n} {k : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hkg : tr.time k < SA.gbar g)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hti : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < SA.gbar g + 2 * sp.Δ := by
  classical
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  obtain ⟨k₀, rfl, hk₀, htk⟩ := Obligations.Growing.acBlock_prev_at hrun hz
    (Compose.projAC_callAt.mp hc₀) hb
  have hex : ∃ j, SA.gbar g + 2 * sp.Δ ≤ tr.time j := ⟨i, hti⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (SA.gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀i : Nat.find hex ≤ i := Nat.find_min' hex hti
  have hfr : ell.frame.F = (tr.state y i).fg.F := by
    rw [(hrun.cutLaw y i _ (Compose.projAC_callAt.mp hci) hy).1]
    rfl
  have hanc₀ := (Obligations.Growing.run_F_mono_at hrun hy hj₀i).trans (hfr ▸ hanc)
  obtain ⟨k', hk', hak⟩ := hc z k₀ B (htk ▸ hz) hk₀ (htk ▸ hkg) y _
    (hrun.antitone hti hy) hj₀ hanc₀
  obtain ⟨ℓ', hc', hb', htk'⟩ := Obligations.Growing.accept_next_at hrun
    (hrun.antitone (hrun.time_mono (by omega : k' ≤ i)) hy) hak
  exact ⟨k' + 1, by omega, ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩,
    by rw [htk']; exact hj₀.2 k' hk'⟩

/-! ### The carried slot-`u` votes -/

/-- **The slot-`u` votes of nodes honest at their casts are carried to a slot-`(u+1)` cast** of a
node honest at it, when every such vote names the honest block `P`, `P` is above the cast's `Σ.F`,
and `ḡ ≤ t_u`: each vote is served (`ResetService`), and `P` is relayed (accepted from `g` on)
or caught up (`Catch(2Δ)`, accepted before `ḡ`). -/
theorem unanimous_carry_votes_core_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : SA.gbar g ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg i
  have hΔ := sp.toParams.hΔ
  have hgg := SA.le_gbar g
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hr := (acRun_prefix hrun hnc i).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := SA.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time i := by
    have h := (SA.castAt_spec hr hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hcarry := Compose.carryAt_of_served hr
    (fun _ => SA.voteStart_initial _) (Compose.frame_anc_accepted hr hy) hy hc' hs
    (CV := Compose.Growing.honestVotes tr H u) fun v hv => by
    obtain ⟨z, q, e', hz, ⟨ell', hcz⟩, rfl, hsl⟩ := hv
    have hdq := hrun.time_nonneg q
    have hrq := (acRun_prefix hrun hnc q).localRun
    have hcz' := castAt_prefix le_rfl hcz
    have hslq := (SA.castAt_spec hrq hz hcz').2.1
    change e'.msg.slot = sp.slot (tr.time q) at hslq
    have hqts : sp.ts u ≤ tr.time q := (SA.ts_le_iff_le_slot sp hdq _).2 (by omega)
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq hz hcz'
    rw [hsl] at hqt
    change tr.time q ≤ _ at hqt
    have hqi : tr.time q ≤ tr.time i := by linarith
    have hHdp := (SA.frameIn_of_callAt hrq hz hcz'.1).2 hHd
    have hsubq := RunTrace.honestBlocks_upTo_subset (H := H) hm hdq
    obtain rfl : Hd = P := hU.1 (hsubq hHdp) hP
      (hHdr.trans (hun z q e' hz ⟨ell', hcz⟩ (hqi.trans hib) hsl))
    refine ⟨hsl, ⟨tr.time q, hqts, by linarith, fun hdl => ?_⟩, Hd, hHdr, ?_⟩
    · rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      exact (SA.upTo_messageServedBefore hmA le_rfl).mpr
        (served_of_service hsvc hz hcz (hgg.trans (hg.trans hqts)) hy hcast.1 hdl)
    rcases Compose.frame_anc_accepted hrq hz q ell' hcz'.1 Hd hHd Hd .refl with h0 | ⟨k, hk, ha⟩
    · exact Or.inr (Or.inl h0)
    rw [RunTrace.upTo_projAC] at ha
    obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := SA.goldilocksSA sp _ ro)).mp ha
    change tr.time k ≤ tr.time q at hkq
    have hzk := hrun.antitone hkq hz
    by_cases hkg : SA.gbar g ≤ tr.time k
    · refine Or.inl ⟨tr.time k, by linarith, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      obtain ⟨ky, hky, hacc, hkyt⟩ := relayed_of_service hrun hsvc hzk ha (hgg.trans hkg) hy
        hcast.1 hdl hFP
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt (A := SA.goldilocksSA sp _ ro)).mpr ⟨hkyd, hacc⟩,
        by rw [ACTrace.upTo_deadline hmA hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc, hkyt⟩ := caught_of_catch hrun hc hzk ha (not_le.mp hkg) hy
        hcast.1 (by linarith) hFP
      exact Or.inr (Or.inr ⟨ky, (ACTrace.upTo_acceptAt (A := SA.goldilocksSA sp _ ro)).mpr
        ⟨hm hky, hacc⟩, by change tr.time ky < _; linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ACTrace.upTo_acceptAt (A := SA.goldilocksSA sp _ ro)).mp hk).2, hkt⟩

/-! ### The frozen viable tree of the next slot -/

/-- **The unanimous proposal is in the frozen viable tree of a slot-`(u+1)` cast** of a node
honest at it, given its own slot-`u` vote by `t_u + Δ`, its fork-choice root below `P`, and its
head-height floor at or below `P` once `P` is held. -/
theorem unanimous_next_vote_viable_core_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcast : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b)
    (hvote : ∃ q e', SA.VoteAt tr.projAC y q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hroot : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P)
    (hfloor : P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg j
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hr := (acRun_prefix hrun hnc j).localRun
  have hc' := castAt_prefix le_rfl hcast
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc'.1
  -- the cast is at `t_{u+1}` or later
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    have h := (SA.castAt_spec hr hy hc').2.1
    change e.msg.slot = sp.slot (tr.time j) at h
    exact (SA.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- `y`'s own slot-`u` vote names `P`, which is then in `y`'s frame
  obtain ⟨q, e', ⟨ellv, hv⟩, hvs, hq⟩ := hvote
  have hqj : tr.time q ≤ tr.time j := by linarith
  have hyq : y ∈ H (tr.time q) := hrun.antitone hqj hy
  have hv' := castAt_prefix hqj hv
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hy hv'
  have hHdp := (SA.frameIn_of_callAt hr hy hv'.1).2 hHd
  obtain rfl : Hd = P := hU.1 (hsub hHdp) hP
    (he.trans (hun y q e' hyq ⟨ellv, hv⟩ (hqj.trans hjb) hvs))
  have hrootp := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdp hroot
  have hFP := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootp
  have hacc : SA.AcceptedBefore (tr.upTo (tr.time j)).projAC y Hd (sp.ts u + 3 * sp.Δ) := by
    rcases SA.frame_genesis_or_accepted sp hr hy hv'.1 Hd hHd with hz | ⟨k, hk, ha⟩
    · omega
    · refine Or.inr ⟨k, ha, ?_⟩
      have := hm hk
      change tr.time k < _
      linarith
  have hPt := Compose.accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy hc' hs hHdp hacc hFP
  have hfr := Compose.frame_of_projAC (hrun.upTo hd) hy hc'.1
  have hst := RunTrace.upTo_state_of_le (y := y) hm (le_refl (tr.time j))
  have hstore : Hd ∈ (tr.state y j).fg.tree := by
    have hmem := hPt.1
    rw [hfr, hst] at hmem
    exact hmem.1
  have hfl := hfloor hstore
  have hroot' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hrootp hPt.1
  refine ⟨Anc.mono hsub hFP, hPt, hroot', Hd, hPt, ?_, .refl⟩
  have hmem := hPt.1
  rw [hfr, hst] at hmem hroot' ⊢
  exact ⟨hmem.1, hmem.2, hroot'.mono (fun X hX => hX.1), hfl⟩


/-! ### Every slot-`(u+1)` vote extends `P` -/

/-- A cast of a node honest at it is no earlier than the start of its slot and at most `Δ` after
it. -/
private theorem cast_time (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y j ell e) :
    sp.ts e.msg.slot ≤ tr.time j ∧ tr.time j ≤ sp.ts e.msg.slot + sp.Δ := by
  have hr := (acRun_prefix hrun hnc j).localRun
  have hc' := castAt_prefix le_rfl hcast
  have h := (SA.castAt_spec hr hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at h
  refine ⟨(SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega), ?_⟩
  exact (Compose.cast_head_fcRoot hr hy hc').2

/-- **Every slot-`(u+1)` vote of a node honest at it extends the unanimous proposal `P`**, by
strong induction on the vote's cut. The batch is counted at the voter's cut: every validator
honest at `t_{u+1}` voted in slot `u` by `t_u + Δ` (`hvotes`), and the fault bound at the cut
(`hfault`) leaves more than half of the validators honest then. The fork-choice root and the
head-height floor of each cast (`hroot`, `hfloor`) are inputs. The transfer counts the batch at
the full committee, which reads the stock committee (`hstock`, §S.2 scope-(ii) item). -/
theorem unanimous_next_votes_extend_core_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : SA.gbar g ≤ sp.ts u)
    (hvotes : ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → ∃ q e, SA.VoteAt tr.projAC x q e ∧
      e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ)
    (hfault : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      SA.FaultBoundAt tr.projAC H (tr.time i) (tr.time i))
    (hroot : ∀ y j ell e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P)
    (hfloor : ∀ y j ell e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h)
    (hstock : sp.committeeSize = sp.n) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hacr := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have all : ∀ j, tr.time j ≤ b → ∀ y e, y ∈ H (tr.time j) →
      SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y e hy ⟨ell, hcast⟩ hs
      have htime : sp.ts (u + 1 : Nat) ≤ tr.time j := by
        have := (cast_time hrun hnc hy hcast).1
        rwa [hs] at this
      obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable_core_at hrun hnc hP hslot hu hun hy hcast
        hs hjb (hvotes y (hrun.antitone htime hy)) (hroot y j ell e hy hcast hs hjb)
        (hfloor y j ell e hy hcast hs hjb)
      have hcarry := unanimous_carry_votes_core_at hrun hnc hsvc hc hP hun hg hy hcast hs hjb hFP
      have hf := hfault j htime hjb
      have hhalf : sp.n ≤ 2 * {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
          SA.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u}.ncard := by
        have hsub : H (tr.time j) ⊆ {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
            SA.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u} := by
          intro x hx
          obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x (hrun.antitone htime hx)
          exact ⟨hx, q, e', hrun.antitone (by linarith) hx, hv, hvs⟩
        have h₁ := Set.ncard_le_ncard hsub
        have h₂ : {x | x ∈ H (tr.time j) ∧ tr.projAC.awake x (tr.time j) ∧
            SA.JoinedAt tr.projAC x (tr.time j)}.ncard ≤ (H (tr.time j)).ncard :=
          Set.ncard_le_ncard fun x hx => hx.1
        have hn : (H (tr.time j)).ncard + (H (tr.time j))ᶜ.ncard = sp.n := by
          rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
        unfold SA.FaultBoundAt at hf
        omega
      refine SA.Growing.next_transfer sp _ ro H _ tr.projAC proposer hacr
        (SA.CommitteeDict.full sp.n)
        ⟨fun _ _ _ _ _ s _ _ => SA.mem_full s _, fun _ _ _ _ _ _ s _ _ => SA.mem_full s _⟩
        (fun _ _ _ _ _ _ _ v _ => SA.mem_full v.slot _) (SA.size_binding_full hstock)
        u y j P ell e hy hcast hs ?_ (by rw [hstock]; exact hhalf) hcarry
        ((SA.ncard_inter_full_lt_iff _ _ _).2 hf) (SA.Growing.cs2_full_of_faultBoundAt hstock hf)
        (Or.inl hvi) ?_
      · intro x q e' hx hv hvs
        have hq := (cast_time hrun hnc hx hv.choose_spec).2
        rw [hvs] at hq
        exact ⟨P, hP, (hun x q e' hx hv (by linarith) hvs).symm, .refl⟩
      · intro x q hq hx e' hv hvs
        exact ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
  exact fun y j e hy hv hjb hs => all j hjb y e hy hv hs

/-! ### A slot-`(u+1)` optimistic selection -/

/-- An optimistic selection of a node honest at it, under a fault bound at its cut, has a
supporting vote of a node honest at its cast, no later than the selection, that extends the
selected block. -/
private theorem optimistic_supporter_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hy : y ∈ H (tr.time j))
    (hopt : SA.OptimisticLockAt tr.projAC y j s D CV)
    (hf : SA.FaultBoundAt tr.projAC H (tr.time j) (tr.time j)) :
    ∃ z q e, q ≤ j ∧ z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg j
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hacr := acRun_prefix hrun hnc j
  rw [RunTrace.upTo_projAC] at hacr
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ :=
    ((SA.upTo_optimisticLockAt (d := tr.time j) hmA).mpr ⟨le_rfl, hopt⟩)
  have hU := (SA.frameIn_of_callAt hacr.localRun hy hpt.1).2
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hacr.stock] at h34
  have h₂ : {x | x ∈ H (tr.time j) ∧ tr.projAC.awake x (tr.time j) ∧
      SA.JoinedAt tr.projAC x (tr.time j)}.ncard ≤ (H (tr.time j)).ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : (H (tr.time j)).ncard + (H (tr.time j))ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold SA.FaultBoundAt at hf
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time j))ᶜ)
      (t := SA.optimisticVoters sp A ell.frame
        (sp.slot ((tr.projAC.upTo (tr.time j)).time j)) D) (by omega)
  obtain ⟨hvs, q, hqj, e, he, rfl⟩ :=
    SA.optimisticPoint_pool_vote hacr hy hpt hv (not_not.mp hz)
  obtain ⟨hqd, he⟩ := SA.upTo_voteAt.mp he
  exact ⟨_, q, e, hqj, hrun.antitone hqd (not_not.mp hz), he, hvs.trans hsl, R,
    hsub (hU hR), hRr, (hBR.mono hU).mono hsub⟩

/-- **A slot-`(u+1)` optimistic selection of a node honest at it is compatible with the unanimous
proposal `P`**: its supporting vote, of a node honest at its cast, extends both (`hstock`, §S.2
scope-(ii) item, as for `unanimous_next_votes_extend_core_at`). -/
theorem unanimous_next_optimistic_compatible_core_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : SA.gbar g ≤ sp.ts u)
    (hvotes : ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → ∃ q e, SA.VoteAt tr.projAC x q e ∧
      e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ)
    (hfault : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      SA.FaultBoundAt tr.projAC H (tr.time i) (tr.time i))
    (hroot : ∀ y j ell e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P)
    (hfloor : ∀ y j ell e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b → P ∈ (tr.state y j).fg.tree →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC y j (u + 1) D CV)
    (hjb : tr.time j ≤ b) (hstock : sp.committeeSize = sp.n) :
    Compatible (tr.HonestBlocksAt H) D P := by
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have htime : sp.ts (u + 1 : Nat) ≤ tr.time j := by
    obtain ⟨_, _, _, hsl, _, _⟩ := hopt
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by
      change sp.slot (tr.time j) = u + 1 at hsl
      omega)
  obtain ⟨z, q, e, hqj, hz, hv, hs, Hd, hHd, he, hDH⟩ :=
    optimistic_supporter_at hrun hnc hy hopt (hfault j htime hjb)
  obtain ⟨Hd', hHd', he', hPH⟩ := unanimous_next_votes_extend_core_at hrun hnc hsvc hc hP hslot
    hu hun hg hvotes hfault hroot hfloor hstock z q e hz hv ((hrun.time_mono hqj).trans hjb) hs
  obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
  exact SA.anc_total hU hDH hPH

end Consensus.Goldilocks.Healing.Growing

end
