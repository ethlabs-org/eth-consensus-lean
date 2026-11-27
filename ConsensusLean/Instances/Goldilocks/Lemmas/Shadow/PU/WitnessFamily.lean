module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FaultBound
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LaterHead
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.WitnessUnanimity
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin

public section

/-! # The early-witness family over the shadow run (interface)

The stock family (`FollowFinality`, `WitnessUnanimity`/`FollowWitnessBoundary`, `FollowRelay`,
`FreshVotesRelay`, `FollowInduction`, `FollowLaterBoundary`) carries a frozen witness `Q ⪰ X` by
`floor ≤ σ(Q).h` and `kindJ → J ⪯ X`, over a stock `FrameWindow`. Over the shadow frame the `J`
clause moves to the witness (`EarlyWitness`): a witness `Q` held by an honest `z` at cut `c` in a
`Healing.FrameWindow' … M isTop J` carries

  `M − 1 ≤ σ_z(Q).h ∧ (isTop → σ_z(Q).h = M − 1 → J ⪯ Q)` (the witness clause),

which `early_witness_viable'` supplies from `Q ∈ ellw.frame.viableHeads`. A shadow window with
`isTop` may change from top-clean to top-contest inside it (stock kept those apart), so the stock
lemmas are re-proved per cut, not instantiated: split on `σ(Q) ≥ M` (the stock contest and gap
argument) and `σ(Q) = M − 1` in a top window (`J ⪯ Q`).

Interface first: every statement below without a proof is unresolved until proved. The frame-relay
and stamp lemmas read only the frame's tree and `F`, which the shadow frame shares with the stock
one. The optimistic variants follow in this file. -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State} {hold : Time}

/-- A block in an honest frame has an earlier honest FG acceptance, or is genesis
(`frame_block_acceptance_at`). -/
theorem frame_block_acceptance_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {x : Fin sp.n} {q : Nat}
    (hx : x ∈ H (tr.time q)) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt x q ell) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) :
    B = sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload ∨
      ∃ k < q, x ∈ H (tr.time k) ∧ tr.AcceptAt x k B := by
  have hd := hrun.time_nonneg q
  have ht : B ∈ ((tr.upTo (tr.time q)).state x q).fg.tree := by
    rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
    rw [frame_of_projAC_at' hrun hx hc, Node.frame'_eq, Store.toFrame'_tree] at hB
    exact hB.1
  rcases Coherence.tree_accepted' (hrun.upTo hd).toLocalRun' hx ht with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, hk, hrun.antitone (hrun.time_mono hk.le) hx,
      ((RunTrace.upTo_acceptAt _).mp ha).2⟩

/-- An honest acceptance reaches a later honest caller, after GST by relay and before it by
catch-up (`relayed_accept_before_at`). -/
private theorem relayed_accept_before_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {k j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hxk : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {elly : ACLabel (goldilocksNode' sp ro)} (hcy : tr.projAC.CallAt y j elly)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j) (hkt : tr.time k + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ a < j, tr.AcceptAt y a B ∧ tr.time a < max (tr.time k + sp.Δ) (gbar g + 2 * sp.Δ) := by
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl' : ∀ c ≤ j, tr.deadline y c (max (tr.time k) g) sp.Δ ≤ tr.time k + sp.Δ := by
      intro c hc
      rw [max_eq_left ((AC.le_gbar g).trans hnew), ← Compose.projAC_deadline]
      have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
        (fun r hrc hrs => hnr r (hrc.trans hc) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
      rwa [max_eq_left hnew] at h
    obtain ⟨a, haj, ha, hat⟩ := hsvc.relay x k B hxk ha ((AC.le_gbar g).trans hnew)
      y j hy ⟨_, Compose.projAC_callAt.mp hcy⟩ ((hdl' j le_rfl).trans hkt) hF
    refine ⟨a, lt_of_le_of_ne haj ?_, ha,
      lt_max_of_lt_left (hat.trans_le (hdl' a haj))⟩
    intro he
    subst a
    cases Option.some.inj (ha.2.symm.trans (Compose.projAC_callAt.mp hcy).2)
  · obtain ⟨a, hlt, hacc, hat⟩ := hrun.toLocalRun'.fgCatchAt' hcatch hxk ha
      (not_le.mp hnew) hy hg hF
    exact ⟨a, hlt, hacc, lt_max_of_lt_right hat⟩

/-- Historical frame membership relays without requiring the sender to remain honest
(`frame_relay_before_at` over the shadow run). -/
theorem frame_relay_before_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {ellx elly : ACLabel (goldilocksNode' sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hd := hrun.time_nonneg j
  have hp := hrun.upTo hd
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j elly := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcy⟩
  have hac := Compose.goldilocks_ac_projection_from' hp (hnc.upTo _)
  have hPh := AC.frameIn_of_callAt hac.localRun hy hc'
  have hFstate : elly.frame.F = (tr.state y j).fg.F := by
    rw [frame_of_projAC_at' hrun hy hcy, Node.frame'_eq, Store.toFrame'_F]
  rcases frame_block_acceptance_at' hrun hx hcx hB with hgB | ⟨k, hk, hxk, ha⟩
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hac.localRun.toU hy j elly hc'
    have hBU : B ∈ tr.HonestBlocksAt H := by
      have hq0 := hrun.time_nonneg q
      have hcx' : (tr.upTo (tr.time q)).projAC.CallAt x q ellx := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcx⟩
      exact RunTrace.honestBlocks_upTo_subset hrun.time_mono hq0
        ((AC.frameIn_of_callAt (Compose.goldilocks_ac_projection_from' (hrun.upTo hq0)
          (hnc.upTo _)).localRun hx hcx').2 hB)
    have hcoh := Coherence.honestBlocksAt_coherent' hrun hnc
    have he : B = G := hcoh.1 hBU
      (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd hG)
      ((congrArg Block.root hgB).trans hGr.symm)
    rw [he] at hF
    rcases Relation.ReflTransGen.cases_tail hF with heq | ⟨C, _, hpar⟩
    · rw [he]
      exact heq.symm ▸ hPh.1.rooted.1
    · exact (Option.some_ne_none _ (hpar.2.2.symm.trans hGp)).elim
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have hle := hrun.time_mono hk.le
    linarith only [hle, hq]
  obtain ⟨a, haj, ha, -⟩ := relayed_accept_before_at' hrun hsvc hcatch hxk ha hy hnr hcy hg hkt
    (hFstate ▸ hF)
  have ha' : (tr.upTo (tr.time j)).AcceptAt y a B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono haj.le, ha⟩
  obtain ⟨hacc, _, _⟩ := Healing.ac_block_after' hp.toLocalRun' hy ha'
  have hBF : Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) elly.frame.F B := by
    obtain ⟨ella, hca, hba⟩ := hacc
    have ht := (AC.frameIn_of_callAt hac.localRun hy hca).2
      ((AC.accept_new sp hac.localRun hy ⟨ella, hca, hba⟩).1 ella hca)
    exact RunTrace.anc_upTo_of_right' hrun hnc hd ht hF
  exact AC.mem_tree_of_acceptAtU sp hac.localRun.toU hy hacc (by omega) hc' hBF

/-- An early frame witness has a pre-freeze stamp at a later honest cast
(`frame_witness_readPoint_stamp_at` over the shadow run). -/
theorem frame_witness_readPoint_stamp_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {a i s : Nat} (hx : x ∈ H (tr.time a))
    (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode' sp ro)}
    (hcx : tr.projAC.CallAt x a ellx)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hes : e.msg.slot = s + 1) (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (ha : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ellx.frame.tree)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ (tr.state y i).fg.tree ∧
      e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (s + 1)) := by
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hs : sp.slot (tr.time i) = s + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hes
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hs])
  have hts := AC.ts_succ s (sp := sp)
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hQt := frame_relay_before_at' hrun hnc hsvc hcatch hx hy
    (fun r hr' hrs => hnr _ r (hrun.antitone (hrun.time_mono hr') hy) hrs) hcx hc.1 hQ
    (by linarith only [hm, hti, hts, sp.toParams.hΔ])
    (by linarith only [ha, hti, hts, sp.toParams.hΔ]) hFQ
  have hacc : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q
      (AC.freeze sp (s + 1)) := by
    rcases frame_block_acceptance_at' hrun hx hcx hQ with hg | ⟨k, hka, hxk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    have hkt := (hrun.time_mono hka.le).trans_lt ha
    have hfr : ell.frame.F = (tr.state y i).fg.F := by
      rw [frame_of_projAC_at' hrun hy hc.1, Node.frame'_eq, Store.toFrame'_F]
    have hp := hrun.upTo (hrun.time_nonneg i)
    have accepted : ∃ q < i, tr.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hnew : gbar g ≤ tr.time k
      · have hdl : tr.deadline y i (max (tr.time k) g) sp.Δ ≤ tr.time i := by
          rw [max_eq_left ((AC.le_gbar g).trans hnew), ← Compose.projAC_deadline]
          have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := i)
            (fun r hri hrs => hnr y r (hrun.antitone (hrun.time_mono hri) hy)
              (Compose.projAC_restartAt.mp hrs)) (tr.time k)
          change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
          rw [max_eq_left hnew] at h
          exact h.trans (by linarith only [hkt, hti, hts, sp.toParams.hΔ])
        obtain ⟨q, hqi, hq, hqd⟩ := hsvc.relay x k Q hxk hk ((AC.le_gbar g).trans hnew)
          y i hy ⟨_, Compose.projAC_callAt.mp hc.1⟩ hdl (hfr ▸ hFQ)
        have hqi' : q < i := by
          refine lt_of_le_of_ne hqi ?_
          rintro rfl
          cases Option.some.inj (hq.2.symm.trans (Compose.projAC_callAt.mp hc.1).2)
        have hdead := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := q)
          (fun r hrq hrs => hnr y r (hrun.antitone (hrun.time_mono (hrq.trans hqi)) hy)
            (Compose.projAC_restartAt.mp hrs)) (tr.time k)
        change _ ≤ max (tr.time k) (gbar g) + sp.Δ at hdead
        rw [max_eq_left hnew, Compose.projAC_deadline] at hdead
        rw [max_eq_left ((AC.le_gbar g).trans hnew)] at hqd
        exact ⟨q, hqi', hq, by rw [hfz]; linarith only [hqd, hdead, hkt]⟩
      · obtain ⟨q, hq, hacc, hqt⟩ := hrun.toLocalRun'.fgCatchAt' hcatch hxk hk
          (not_le.mp hnew) hy (by linarith only [hm, hti, hts, sp.toParams.hΔ]) (hfr ▸ hFQ)
        exact ⟨q, hq, hacc, by rw [hfz]; linarith only [hqt, hm, sp.toParams.hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := accepted
    have hq' := (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hrun.time_mono hqi.le, hq⟩
    obtain ⟨hqa, htq, _⟩ := Healing.ac_block_after' hp.toLocalRun' hy hq'
    exact Or.inr ⟨q + 1, by rwa [RunTrace.upTo_projAC] at hqa,
      by change tr.time (q + 1) < _; rw [show tr.time (q + 1) = tr.time q from htq]; exact hqt⟩
  refine ⟨?_, ?_⟩
  · rw [frame_of_projAC_at' hrun hy hc.1, Node.frame'_eq, Store.toFrame'_tree] at hQt
    exact hQt.1
  · have h := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
      (by simpa only [hes] using hacc)
      (fun k hki hrs => by
        have h := hnr y k (hrun.antitone (hrun.time_mono hki) hy)
          (Compose.projAC_restartAt.mp ((ACTrace.upTo_restartAt).mp hrs).2)
        change tr.time k < _
        rw [hes, hfz]
        linarith only [h, hm, sp.toParams.hΔ])
      (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hes, hfz];
          linarith only [hti, hts, sp.toParams.hΔ])
    simpa only [hes] using h

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- A finalized tip of one honest observation is below a block held by another, strictly higher
than its finalized height (`finalized_anc_obs` over the shadow run). -/
theorem finalized_anc_obs'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y m).fg.tree)
    (hFt : F ∈ (tr.state y m).fg.tree) (hFr : F.root = ((tr.state y m).fg.σ X.root).F)
    (hW : W ∈ (tr.state x i).fg.tree)
    (hlt : ((tr.state y m).fg.σ X.root).hF < ((tr.state x i).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W :=
  (Store.finalized_anc_of_safe_with Store.finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun hu hy hytime).reachableWith
    (Compose.Growing.reachable_at' hrun ht hx hxtime).reachableWith
    (Coherence.honest_blocks_coherent_at' hrun hnc)
    (Compose.Growing.tree_held_at' hu hy hytime) (Compose.Growing.tree_held_at' ht hx hxtime) hf
    (Consensus.Goldilocks.Healing.Growing.Shadow.held_atts_safe_at' hrun hnc hu hytime hy ht
      hxtime hx (le_max_left _ _) (le_max_right _ _))
    hX hFt hFr hW hlt).mono (Compose.Growing.tree_held_at' ht hx hxtime)

/-- **The finalized tip of an honest observation is below every held block strictly above its
justified height** (the quorum branch of `finalized_below_floor_held_at`, read off the justified
height instead of the stock head-height floor). -/
theorem finalized_below_of_hj_lt_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i m : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (hf : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z m).fg.tree)
    (hgt : (tr.state y i).fg.hj < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have htm := hrun.time_nonneg m
  have hbm : ∀ q < m, tr.time q ≤ tr.time m := fun q hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at' hrun ht hy hb
  have hrz := Compose.Growing.reachable_at' hrun htm hz hbm
  have hU := Coherence.honest_blocks_coherent_at' hrun hnc
  have hsub := Compose.Growing.tree_held_at' ht hy hb
  have hcoh := hU.mono hsub
  obtain ⟨hF, hJm, hFJ, ⟨Bj, hBj, hBjJ, _⟩, hmax, -, X, hX, hXF⟩ := Store.cache_invariants' hr
  have hg := Store.genesis_mem_with Store.finalitySpec_updateFinality' hr.reachableWith
  have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := fun he => by
    rw [hcoh.1 hF hg he]
    exact ((Store.accepted_tree_with Store.finalitySpec_updateFinality'
      hrz.reachableWith).2.2.2 W hW).mono (Compose.Growing.tree_held_at' htm hz hbm)
  rcases Store.fin_pair_entry_with Store.finalitySpec_updateFinality' hr.reachableWith hX with
    he | ⟨E, hE, hEr, _⟩
  · exact hgen (hXF.symm.trans he)
  obtain rfl : E = (tr.state y i).fg.F := hcoh.1 hE hF (hEr.trans hXF)
  obtain ⟨J, hJt, hJr, -, hcase⟩ :=
    Store.J_entry_with Store.finalitySpec_updateFinality' hr.reachableWith hBj
  obtain rfl : J = (tr.state y i).fg.J := hcoh.1 hJt hJm (hJr.trans hBjJ)
  rcases hcase with he | ⟨hJh, -⟩
  · have hgF := (Store.accepted_tree_with Store.finalitySpec_updateFinality'
      hr.reachableWith).2.2.2 _ hF
    rw [he] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have hFh := Store.h_le_of_store_anc_with Store.finalitySpec_updateFinality'
    hr.reachableWith hFJ
  have hstrict : ((tr.state y i).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h := by
    omega
  exact finalized_anc_obs' hrun hnc ht hb hy htm hbm hz hf hX hF hXF.symm hW hstrict

/-- A height bound on an honest witness carries to an honestly held descendant
(`floor_le_of_honest_ancestor_at` over the shadow run). -/
theorem le_height_of_honest_ancestor_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i c : Nat}
    (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} {n : Nat}
    (hX : X ∈ (tr.state z c).fg.tree) (hh : n ≤ ((tr.state z c).fg.σ X.root).h)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    n ≤ ((tr.state x i).fg.σ W.root).h := by
  have hti := hrun.time_nonneg i
  have hbi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hXt := mem_of_honest_anc_at' hrun hnc hti hbi hx hXW hW
  have ha := store_anc_of_honest_anc_at' hrun hnc hti hbi hx hXW hW
  have hle := Store.h_le_of_store_anc_with Store.finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun hti hx hbi).reachableWith ha
  rw [← σ_eq_honest_at' hrun hnc (hrun.time_nonneg c)
    (fun q hq => hrun.time_mono hq.le) hz hti hbi hx hX hXt] at hle
  exact hh.trans hle

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- **A window's witness places every honest finalized tip in it below an independently held
descendant** (`FrameWindow.finalized_below_descendant_at` over the shadow run, with the witness
clause on `X` in place of `floor ≤ σ(X).h` and `kindJ → J ⪯ X`). -/
theorem FrameWindow'.finalized_below_descendant_at' {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x z : Fin sp.n} {j i c : Nat}
    (hy : y ∈ H (tr.time j)) (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time j) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ X.root).h ∧
      (isTop → ((tr.state z c).fg.σ X.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J X))
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F W := by
  have hjt := hrun.time_nonneg j
  have hbj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
  have hM := hframe.M_eq y j hy hjlo hjhi
  have htop := hframe.top_iff y j hy hjlo hjhi
  have hjm := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun hjt hy hbj).reachableWith
  by_cases hcase : isTop ∧ ((tr.state z c).fg.σ X.root).h = M - 1
  · obtain ⟨ht, he⟩ := hcase
    have hJX := hwit.2 ht he
    have hFJ := (Store.cache_invariants' (Compose.Growing.reachable_at' hrun hjt hy hbj)).2.2.1
    rw [hframe.root_eq y j hy hjlo hjhi ht] at hFJ
    exact (hFJ.mono (Compose.Growing.tree_held_at' hjt hy hbj)).trans (hJX.trans hXW)
  · have hWh := Growing.le_height_of_honest_ancestor_at' hrun hnc hx hz hX le_rfl hW hXW
    refine Growing.finalized_below_of_hj_lt_at' hrun hnc hy hx hf hW ?_
    by_cases ht : isTop
    · have hX' : M ≤ ((tr.state z c).fg.σ X.root).h := by
        have := hwit.1
        by_contra hlt
        exact hcase ⟨ht, by omega⟩
      have := htop.2 ht
      omega
    · have := mt htop.1 ht
      have := hwit.1
      omega

/-- **The frame geometry of a viable witness at a reader's cut** (`witness_frame_at` over the
shadow frame): for a reader honest at its call in a `FrameWindow'`, holding a descendant `Q` of `X`
that carries the witness clause, either `X` is below its finalized tip, or `X` and `Q` are in its
frame above `F` with `Q` a P-U viable head. The witness clause is exactly P-U viability at the
window's `M` and `J`; no `fc_root = J` case arises. -/
theorem witness_frame_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : FrameWindow' tr H lo hi M isTop J)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQy : Q ∈ (tr.state y i).fg.tree)
    (hwit : M - 1 ≤ ((tr.state y i).fg.σ Q.root).h ∧
      (isTop → ((tr.state y i).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) :
    Anc (tr.HonestBlocksAt H) X ell.frame.F ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F X ∧ X ∈ ell.frame.tree ∧
        ell.frame.Anc ell.frame.fcRoot X ∧ Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧
        ell.frame.Anc X Q) := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hrun.time_mono hq.le
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have hr := Compose.Growing.reachable_at' hrun ht hy hb
  rw [Consensus.Goldilocks.Shadow.PU.Growing.frame_of_projAC_at' hrun hy hc]
  rcases AC.anc_total hU (hframe.finalized_below_descendant_at' hrun hnc hy hy hy
      (by rwa [max_self]) hlo hhi hQy hwit hQy .refl) hXQ with hFX | hXF
  swap
  · exact Or.inl (by rwa [Node.frame'_eq, Store.toFrame'_F])
  have hΦ := Compose.Growing.frameOK_at' hrun ht hy hb
  have hsub : (Node.frame' (tr.state y i)).tree ⊆ tr.HonestBlocksAt H := by
    rw [Node.frame'_eq, Store.toFrame'_tree]
    exact fun _ h => ⟨y, i, tr.time i, ht, hb, hy, h.1⟩
  have hXy := Growing.mem_of_honest_anc_at' hrun hnc ht hb hy hXQ hQy
  have hFXs := Growing.store_anc_of_honest_anc_at' hrun hnc ht hb hy hFX hXy
  have hFQs := Growing.store_anc_of_honest_anc_at' hrun hnc ht hb hy (hFX.trans hXQ) hQy
  have hXt : X ∈ (Node.frame' (tr.state y i)).tree := by
    rw [Node.frame'_eq, Store.toFrame'_tree]; exact ⟨hXy, hFXs⟩
  have hQt : Q ∈ (Node.frame' (tr.state y i)).tree := by
    rw [Node.frame'_eq, Store.toFrame'_tree]; exact ⟨hQy, hFQs⟩
  have hvQ : Q ∈ (Node.frame' (tr.state y i)).viableHeads := by
    rw [Node.frame'_eq, Store.toFrame'_viableHeads]
    refine ⟨hQy, hFQs, ?_⟩
    rw [Store.isViable'_iff, hframe.M_eq y i hy hlo hhi]
    have hjm := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality'
      hr.reachableWith
    have hM := hframe.M_eq y i hy hlo hhi
    have htop := hframe.top_iff y i hy hlo hhi
    rcases Nat.lt_or_ge ((tr.state y i).fg.σ Q.root).h M with hlt | hge
    · have he : ((tr.state y i).fg.σ Q.root).h = M - 1 := by have := hwit.1; omega
      refine Or.inr ⟨by omega, ?_⟩
      by_cases ht' : isTop
      · right
        have hJQ := Growing.store_anc_of_honest_anc_at' hrun hnc ht hb hy (hwit.2 ht' he) hQy
        rwa [hframe.root_eq y i hy hlo hhi ht']
      · left
        have := mt htop.1 ht'
        omega
    · exact Or.inl hge
  have hXQf := AC.anc_tree_of_anc_U hU hΦ hsub hXt hXQ hQt
  have hFt : (Node.frame' (tr.state y i)).fcRoot ∈ (Node.frame' (tr.state y i)).tree :=
    hΦ.fcRoot_mem
  refine Or.inr ⟨by rwa [Node.frame'_eq, Store.toFrame'_F], hXt, ?_, hQt, hvQ, hXQf⟩
  apply AC.anc_tree_of_anc_U hU hΦ hsub hFt _ hXt
  rw [Node.frame'_eq, Store.toFrame'_fcRoot]
  exact hFX

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State} {hold : Time}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := Compose.goldilocks_ac_projection_from' (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- Fewer than a third faulty is below the replay quorum excess. -/
private theorem quorum_excess' {t : Time} (h : 3 * (H t)ᶜ.ncard ≤ sp.n - 1) :
    (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
  have hn := sp.toParams.hn
  have he : sp.n = sp.toParams.n := rfl
  change (H t)ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.n
  omega

/-- A prefix vote by a node honest at `d` extends `B` in the prefix's honest blocks when it does
in the run's (`narrow_vote`). -/
private theorem narrow_vote'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d)
    {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.VoteAt (tr.projAC.upTo d) x k e)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    AC.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg B := by
  have hr := (acRun_prefix' hrun hnc hd).localRun
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hd
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hrun.vstart hx hc
  have hHdU := (AC.frameIn_of_callAt hr hx hc.1).2 hHd
  obtain ⟨W, hW, hWr, hBW⟩ := hext
  obtain rfl : W = Hd := hU.1 hW (subU hHdU) (hWr.trans hHdr.symm)
  exact ⟨W, hHdU, hWr, RunTrace.anc_upTo_of_right' hrun hnc hd hHdU hBW⟩

/-- The witness clause carries to another honest holder of the witness (`witness_height`). -/
private theorem witness_clause_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z y : Fin sp.n} {c i M : Nat} {isTop : Prop}
    {J Q : AC.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time c))
    (hy : y ∈ H (tr.time i)) (hQ : Q ∈ (tr.state z c).fg.tree)
    (hQy : Q ∈ (tr.state y i).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q)) :
    M - 1 ≤ ((tr.state y i).fg.σ Q.root).h ∧
      (isTop → ((tr.state y i).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q) := by
  rwa [← Healing.Growing.σ_eq_honest_at' hrun hnc (hrun.time_nonneg c)
    (fun _ hq => hrun.time_mono hq.le) hz (hrun.time_nonneg i)
    (fun _ hq => hrun.time_mono hq.le) hy hQ hQy]

/-- Prior votes extending a prefix propagate through a frozen viable witness
(`unanimous_next_votes_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_votes_of_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hgm : gbar g ≤ sp.ts m := by linarith
  suffices hall : ∀ i, ∀ y e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X from
    fun y i e => hall i y e
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro y e hy hv hs
  obtain ⟨ell, hcast⟩ := hv
  have ht0 := hrun.time_nonneg i
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hrun' := acRun_prefix' hrun hnc ht0
  have hr := hrun'.localRun
  have hcast' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hslot : sp.slot (tr.time i) = m + 1 := (AC.castAt_specU hr.toU hy hcast').2.1.symm.trans hs
  have hlo1 : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp ht0 _).mpr (by rw [hslot])
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
    have h := AC.vote_time_leU hr.toU hy ⟨ell, hcast'⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
    simpa only [hslot] using h
  have hib : tr.time i ≤ b := hhi.trans hmb
  have hlo : sp.ts m ≤ tr.time i := by linarith
  obtain ⟨hQy, hstamp⟩ := hheld y i e hy ⟨ell, hcast⟩ hs
  have hwy := witness_clause_at' hrun hnc hz hy hQ hQy hwit
  have hS := hK.healthy_base_before_at' hrun hnc hsvc hawake hf hcatch ht0 hib
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcast'.1
  rcases Healing.witness_frame_at' hrun hnc hframe hy hcast.1 hlo hhi
      (quorum_excess' (hf _ ht0 hib)) hQy hwy hXQ with
    hXF | ⟨hFX, hXt, hrootX, hQt, hvQ, hXQf⟩
  · obtain ⟨W, hW, hWr, hFW⟩ := AC.castAt_head_anc hr hy hcast' (Or.inr rfl)
      (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
    exact ⟨W, subU (hPhiU hW), hWr, hXF.trans ((hFW.mono hPhiU).mono subU)⟩
  have hQdom : Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (m + 1) := ⟨hQt, Or.inl hstamp⟩
  have hdomA := AC.voterBlockTree_ancU hr.toU hrun'.vstart hy hcast'
  rw [hs] at hdomA
  have hviab : AC.ViableAtVote ell e (m + 1) X :=
    Or.inl ⟨hdomA Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩
  have hG' : ∀ x ∈ H (tr.time i), ∀ j e', AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      e'.msg.slot = m → AC.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e'.msg X := by
    intro x hx j e' hv' hs'
    obtain ⟨hjd, hv''⟩ := AC.upTo_voteAt.mp hv'
    exact narrow_vote' hrun hnc ht0 hx hv' (hG x j e' (hrun.antitone hjd hx) hv'' hs')
  have hrelay : ∀ x ∈ H (tr.time i), ∀ k ev, AC.VoteAt (tr.projAC.upTo (tr.time i)) x k ev →
      ev.msg.slot = m → ∀ B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)),
        B.root = ev.msg.head →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ell.frame.F B := by
    intro x hx k ev hv' hs' B hB hBr
    obtain ⟨W, hW, hWr, hXW⟩ := hG' x hx k ev hv' hs'
    obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
    exact RunTrace.anc_upTo_of_right' hrun hnc ht0 hB (hFX.trans (hXW.mono subU))
  have hrestart : ∀ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ gbar g := by
    intro k hk
    obtain ⟨hkd, hk⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _ ro)).mp hk
    exact hnr y k (hrun.antitone hkd hy) (Compose.projAC_restartAt.mp hk)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := AC.goldilocksAC sp _ ro) (tr.projAC.upTo (tr.time i)) y k t ≤
        max t (sp.ts m) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts m)
      (fun r _ hrs => (hrestart r hrs).trans hgm) t
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k < sp.ts m :=
    fun k _ hk => (hrestart k hk).trans_lt (by linarith)
  have hcarry := AC.honest_batch_carry_before hS hy hcast' hs hm
    (show sp.ts m + 2 * sp.Δ ≤ tr.time i by linarith) le_rfl hdl hrs hrelay
  have hhalf := AC.honest_voters_half_before hS hm (show sp.ts m + sp.Δ ≤ tr.time i by linarith)
    (fun x hx r _ hrest => by
      obtain ⟨hrd, hrest⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _ ro)).mp hrest
      rw [AC.ts_sub_one]
      exact (hnr x r (hrun.antitone hrd hx) (Compose.projAC_restartAt.mp hrest)).trans
        (by linarith))
  have hhalf' : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m}.ncard := by
    have hle := Set.ncard_le_ncard (s := {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m ∧
        (tr.projAC.upTo (tr.time i)).time j ≤ sp.ts m + sp.Δ})
      (t := {x | x ∈ H (tr.time i) ∧ ∃ j e',
        AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m})
      (by rintro x ⟨hx, j, e', hv', hs', _⟩; exact ⟨hx, j, e', hv', hs'⟩)
    omega
  have hfault : AC.FaultBoundK K m (tr.projAC.upTo (tr.time i)) (H (tr.time i)) (tr.time i) :=
    Healing.Growing.KernelProof.faultBoundK_upTo le_rfl
      (Healing.PU.faultBoundK_of_service_at' hK hrun hawake hnr hgm (by linarith) ht0 (by
        rw [hslot]
        have heq : ((m + 1 : Nat) : Int) - 1 = m := by omega
        rw [heq]; exact hgm) hib)
  have hext := AC.next_transfer_of_carry sp hrun' K hS.hP hS.hT hS.hsize hy hcast' hs hG' hhalf'
    hcarry hfault (hS.cs2 (m + 1) (by linarith) hlo1) hviab
    (fun x hx k hki ev hv' hsx => by
      obtain ⟨hkd, hv''⟩ := AC.upTo_voteAt.mp hv'
      exact narrow_vote' hrun hnc ht0 hx hv'
        (ih k hki x ev (hrun.antitone hkd hx) hv'' hsx))
  obtain ⟨W, hW, hWr, hXW⟩ := hext
  exact ⟨W, subU hW, hWr, hXW.mono subU⟩

/-- The same prefix reaches an actual next-slot proposal head
(`unanimous_next_proposal_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_proposal_of_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hgm : gbar g ≤ sp.ts m := by linarith
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := by linarith
  have hlo : sp.ts m ≤ tr.time i := by linarith
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hS := hK.healthy_base_before_at' hrun hnc hsvc hawake hf hcatch ht0 hib
  have hr := hS.run.localRun
  have hf3 := hf _ ht0 hib
  have hcp : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hdp : (AC.acProposal sp ((tr.projAC.upTo (tr.time i)).state y i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcp
  have hwy := witness_clause_at' hrun hnc hz hy hQ hQy hwit
  rcases Healing.witness_frame_at' hrun hnc hframe hy hc hlo hhi (quorum_excess' hf3) hQy hwy hXQ
    with hXF | ⟨hFX, hXt, hrootX, hQt, hvQ, hXQf⟩
  · have he := (AC.acProposal_head hdp).2
    rw [he]
    exact hXF.trans (((AC.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU).mono subU)
  have hG' : ∀ x ∈ H (tr.time i), ∀ j e', AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      e'.msg.slot = m → AC.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e'.msg X := by
    intro x hx j e' hv' hs'
    obtain ⟨hjd, hv''⟩ := AC.upTo_voteAt.mp hv'
    exact narrow_vote' hrun hnc ht0 hx hv' (hG x j e' (hrun.antitone hjd hx) hv'' hs')
  have hrelay : ∀ x ∈ H (tr.time i), ∀ k ev, AC.VoteAt (tr.projAC.upTo (tr.time i)) x k ev →
      ev.msg.slot = m → ∀ B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)),
        B.root = ev.msg.head →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ell.frame.F B := by
    intro x hx k ev hv' hs' B hB hBr
    obtain ⟨W, hW, hWr, hXW⟩ := hG' x hx k ev hv' hs'
    obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
    exact RunTrace.anc_upTo_of_right' hrun hnc ht0 hB (hFX.trans (hXW.mono subU))
  have hrestart : ∀ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ gbar g := by
    intro k hk
    obtain ⟨hkd, hk⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _ ro)).mp hk
    exact hnr y k (hrun.antitone hkd hy) (Compose.projAC_restartAt.mp hk)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := AC.goldilocksAC sp _ ro) (tr.projAC.upTo (tr.time i)) y k t ≤
        max t (sp.ts m) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts m)
      (fun r _ hrs => (hrestart r hrs).trans hgm) t
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k < sp.ts m :=
    fun k _ hk => (hrestart k hk).trans_lt (by linarith)
  have hhalf := AC.honest_voters_half_before hS hm (show sp.ts m + sp.Δ ≤ tr.time i by linarith)
    (fun x hx r _ hrest => by
      obtain ⟨hrd, hrest⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _ ro)).mp hrest
      rw [AC.ts_sub_one]
      exact (hnr x r (hrun.antitone hrd hx) (Compose.projAC_restartAt.mp hrest)).trans
        (by linarith))
  have hhalf' : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m}.ncard := by
    have hle := Set.ncard_le_ncard (s := {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m ∧
        (tr.projAC.upTo (tr.time i)).time j ≤ sp.ts m + sp.Δ})
      (t := {x | x ∈ H (tr.time i) ∧ ∃ j e',
        AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m})
      (by rintro x ⟨hx, j, e', hv', hs', _⟩; exact ⟨hx, j, e', hv', hs'⟩)
    omega
  have hpre := hrun.upTo ht0
  refine (AC.batch_proposal hS.run (K := K) (hS.cs2 m hgm (by linarith)) hhalf' hG' hy hcp
    (fun v hv => hS.hP.1 y hy i m v hv) (AC.proposal_slot hti) hdp
    ⟨hXt, Or.inl ⟨hXt, hrootX, Q, hQt, hvQ, hXQf⟩⟩ ?_ ?_).mono subU
  · intro x hx k e hv hs
    obtain ⟨W, hW, hWr, -, hp, -, hb⟩ := AC.late_vote_held_of_frame_before hS hy hcp hm
      (show sp.ts m + 2 * sp.Δ ≤ tr.time i by linarith) le_rfl hdl hrs hx hv hs
      (hrelay x hx k e hv hs)
    exact AC.heldAtProposal_iff.mpr ⟨Or.inl hp, W, hW, hWr, hWr ▸ lt_trans hb
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩
  · apply AC.highLocksCompatible_iff.mpr
    intro l hl _ hlm L hL hLr
    have hl' : l ∈ ((tr.upTo (tr.time i)).state y i).ac.locks := by
      have h := Compose.projAC_state' hpre.toLocalRun' hy i
      rw [RunTrace.upTo_projAC] at h
      rwa [h] at hl
    have hls := Compose.proposal_locks_slot_of' hpre (hnc.upTo _) hy
      (by rw [RunTrace.upTo_projAC]; exact hcp) hcall
      (by rw [RunTrace.upTo_projAC]; exact hdp) hti (by rw [RunTrace.upTo_projAC]; exact hS.hP)
      (hS.cs2 (m + 1) (by linarith) (by linarith)) l hl'
    have heq : l.slot = m := by omega
    obtain ⟨O, hLO, a, CV, hopt⟩ := AC.proposal_high_lockU hr.toU hS.run.vstart hy hti hl hlm hL hLr
    rw [heq] at hopt
    rcases AC.optimisticLock_compatibleU hS.run.toU K hS.hP hy hopt (hS.cs2 m hgm (by linarith))
        hG' with hOX | hXO
    · exact Or.inl (hLO.trans hOX)
    · exact AC.anc_total hr.coherent hLO hXO

/-- **A next-vote base propagates through later labels** from an early viable witness
(`later_heads_of_early_witness_at` over the shadow run). The witness is a viable head of the
witness's call frame (`hvQ`), read inside the window (`halo`); `floor ≤ σ(Q).h` and
`kindJ → J ⪯ X` are replaced by it (`early_witness_viable'`). -/
theorem later_heads_of_early_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) (sp.ts N + sp.Δ) M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hsstep := AC.ts_succ s (sp := sp)
  have hFst {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
      {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell) :
      ell.frame.F = (tr.state y i).fg.F := by
    rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_F]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    rw [frame_of_projAC_at' hrun hw hcw, Node.frame'_eq, Store.toFrame'_tree] at hQw
    exact hQw.1
  intro r hrlo hrN0
  have hsN := hts (show s + 1 ≤ N from hrlo.trans hrN0)
  have hwit := early_witness_viable' hrun hframe hw halo
    (by linarith only [hat, hsstep, hsN, hΔ]) hcw hvQ
  revert hrN0
  induction r, hrlo using Nat.le_induction with
  | base => exact fun _ => ⟨hbase, fun h => by omega⟩
  | succ m hsm ih =>
    intro hrN
    have ht := hts hrN
    have hms := hts hsm
    have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by linarith only [hm, hms, hsstep]
    have hprior := (ih (show m ≤ N by omega)).1
    have hwin := hframe.mono (hts (show s ≤ m by omega))
      (show sp.ts (m + 1 : Nat) + sp.Δ ≤ sp.ts N + sp.Δ by linarith only [ht])
    have hfinal {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
        (hlo : sp.ts s ≤ tr.time i) (hhi : tr.time i ≤ sp.ts N + sp.Δ) :
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q := by
      apply hframe.finalized_below_descendant_at' hrun hnc hy hw hw
        (sp.toParams.fg.faults_lt_quorum_margin
          (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
            (max_le (hhi.trans hmb) (by linarith only [hat, hsstep, hsN, hmb, hΔ]))))
        hlo hhi hQ hwit hQ .refl
    refine ⟨unanimous_next_votes_of_witness_at' hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith only [ht, hmb]) hwin hw hQ hwit hXQ ?_ hprior hK, ?_⟩
    · intro y i e hy hv hes
      obtain ⟨ell, hc⟩ := hv
      have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo (hrun.time_nonneg i))
        (hnc.upTo _)).localRun
      rw [RunTrace.upTo_projAC] at hr
      have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
      have hs : sp.slot (tr.time i) = m + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hes
      have hlo : sp.ts s ≤ tr.time i :=
        (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by
          rw [hs]; exact_mod_cast (by omega : s ≤ m + 1))
      have hhi : tr.time i ≤ sp.ts N + sp.Δ := by
        have h := AC.vote_time_leU hr.toU hy ⟨ell, hc'⟩
        change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
        rw [hs] at h
        linarith only [h, ht]
      exact frame_witness_readPoint_stamp_at' hrun hnc hsvc hcatch hnr hw hy hcw hc hes hwarm
        (by linarith only [hat, hms, hsstep, hΔ]) hQw ((hFst hy hc.1) ▸ hfinal hy hlo hhi)
    · intro _ y i ell hy hc hcall hti d pay hd
      have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
      have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith only [ht, hΔ]
      have hmstep := AC.ts_succ m (sp := sp)
      have hQt := frame_relay_before_at' hrun hnc hsvc hcatch hw hy
        (fun r hr' hrs => hnr _ r (hrun.antitone (hrun.time_mono hr') hy) hrs) hcw hc hQw
        (by rw [hti]; linarith only [hwarm, hmstep, hΔ])
        (by rw [hti]; linarith only [hat, hms, hsstep, hmstep, hΔ])
        ((hFst hy hc) ▸ hfinal hy hlo hhi)
      rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_tree] at hQt
      exact unanimous_next_proposal_of_witness_at' hrun hnc hsvc hawake hf hcatch hnr hwarm
        (by linarith only [ht, hmb]) hwin hw hQ hwit hXQ hprior hy hc hcall hti hd hQt.1 hK

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest
(`frameIn_at`). -/
private theorem frameIn_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H := by
  have h := AC.frameIn_of_callAt (acRun_prefix' hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨h.1, h.2.trans (RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg i))⟩

/-- Joinedness of the cast bounds its relay deadlines (`witness_voterBlockTree_at` over the
shadow run): an early frame witness is in the next-slot voter's block tree. -/
theorem witness_voterBlockTree_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {w y : Fin sp.n} {a i : Nat} (hw : w ∈ H (tr.time a)) (hy : y ∈ H (tr.time i))
    {ellw ell : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQw : Q ∈ ellw.frame.tree)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = s + 1) (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (s + 1) := by
  have ht0 := hrun.time_nonneg i
  have hr := (acRun_prefix' hrun hnc ht0).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht0
  obtain ⟨hPhi, hPhiU⟩ := frameIn_at' hrun hnc hy hc.1
  have hQU := (frameIn_at' hrun hnc hw hcw).2 hQw
  have hslot : sp.slot (tr.time i) = s + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hs
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
  have hts := AC.ts_succ s (sp := sp)
  have hΔ := sp.toParams.hΔ
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hjoined := (AC.castAt_specU hr.toU hy hc').2.2.1
    have hj : AC.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAtU hr.toU hy hc']
      exact hjoined
    intro k hk hrestart
    have h := (AC.joined_awakeU sp _ ro (H (tr.time i)) _ _ hr.toU y hy i ell hc'.1 hj).2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hrun.time_mono hk, hrestart⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at h
    simpa only [hslot, show ((s + 1 : Nat) : Int) - 1 = s by omega] using h
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hr hrestart => hrs r (hr.trans hk) hrestart) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  have ha : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q (AC.freeze sp (s + 1)) := by
    rcases frame_block_acceptance_at' hrun hw hcw hQw with hg | ⟨k, hka, hwk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    obtain ⟨hk', htk, -⟩ := Healing.ac_block_after' (hrun.upTo (hrun.time_nonneg a)).toLocalRun' hw
      ((RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono hka.le, hk⟩)
    rw [RunTrace.upTo_projAC] at hk'
    have hacc := (ACTrace.upTo_acceptAt.mp hk').2
    have hwk' : w ∈ H (tr.time (k + 1)) := by
      change tr.time (k + 1) = tr.time k at htk
      rwa [htk]
    have hkt : tr.time (k + 1) < sp.ts s + 2 * sp.Δ := by
      change tr.time (k + 1) = tr.time k at htk
      rw [htk]
      exact (hrun.time_mono hka.le).trans_lt hat
    have hex : ∃ q ≤ i, tr.projAC.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hkg : gbar g ≤ tr.time (k + 1)
      · obtain ⟨q, hqi, hq, hqt⟩ :=
          (Healing.PU.service_syncACAt' hrun hsvc (lo := g) (hi := tr.time (k + 1)) le_rfl).2
            w (k + 1) Q hwk' hacc ((AC.le_gbar g).trans hkg) le_rfl y i ell hy hc.1
            (by have := hdl i le_rfl _ hkt;
                change tr.projAC.deadline y i (tr.time (k + 1)) ≤ tr.time i;
                linarith only [this, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; exact hqt.trans (hdl q hqi _ hkt)⟩
      · obtain ⟨q, hqi, hq, hqt⟩ := hrun.toLocalRun'.acCatchAt' hcatch hwk' hacc
          (lt_of_not_ge hkg) hy hc.1 (by linarith only [hm, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; linarith only [hqt, hm, hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := hex
    exact Or.inr ⟨q, ACTrace.upTo_acceptAt.mpr ⟨hrun.time_mono hqi, hq⟩, hqt⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy i ell hc'.1
      obtain rfl : Q = G := hU.1 hQU (subU hGU) (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hki : k ≤ i := by
        by_contra hn
        have ht := hrun.time_mono (show i ≤ k by omega)
        change tr.time k < _ at hkt
        rw [hfz] at hkt
        linarith only [ht, hkt, hti, hts, hΔ]
      obtain ⟨ella, hca, hba⟩ := hk
      have hk : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k Q := ⟨ella, hca, hba⟩
      have hQp := (AC.frameIn_of_callAt hr hy hca).2 ((AC.accept_new sp hr hy hk).1 _ hca)
      exact AC.mem_tree_of_acceptAtU sp hr.toU hy hk hki hc'.1
        (RunTrace.anc_upTo_of_right' hrun hnc ht0 hQp hFQ)
  have hstamp := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
    (by simpa only [hs] using ha)
    (fun k hk hrk => by
      have h := hrs k hk (ACTrace.upTo_restartAt.mp hrk).2
      change tr.time k < _
      rw [hs, hfz]
      linarith only [h, hΔ])
    (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hs, hfz];
        linarith only [hti, hts, hΔ])
  exact ⟨hQt, Or.inl (by simpa only [hs] using hstamp)⟩

/-- Common early-witness induction with the lock-specific transfer supplied by the caller
(`next_votes_of_early_witness_at` over the shadow run, witness `hvQ` read inside the window). -/
theorem next_votes_of_early_witness_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) hi M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame' (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hwit := early_witness_viable' hrun hframe hw halo
    (by linarith only [hat, AC.ts_succ s (sp := sp), hnext, sp.toParams.hΔ]) hcw hvQ
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    rw [frame_of_projAC_at' hrun hw hcw, Node.frame'_eq, Store.toFrame'_tree] at hQw
    exact hQw.1
  suffices hall : ∀ i, ∀ y e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X from
    fun y i e hy hv hs => hall i y e hy hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y e hy ⟨ell, hc, he⟩ hs
    have hcast : AC.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have ht0 := hrun.time_nonneg i
    have hr := (acRun_prefix' hrun hnc ht0).localRun
    have hcast' := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
    have hslot : sp.slot (tr.time i) = s + 1 :=
      (AC.castAt_specU hr.toU hy hcast').2.1.symm.trans hs
    have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
      (AC.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
    have hts := AC.ts_succ s (sp := sp)
    have hlo : sp.ts s ≤ tr.time i := by linarith only [hti, hts, sp.toParams.hΔ]
    have hhi : tr.time i ≤ hi := by
      have ht := (Compose.cast_head_fcRoot hr (acRun_prefix' hrun hnc ht0).vstart hy hcast').2
      rw [hs] at ht
      exact ht.trans hnext
    have hmargin : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n :=
      sp.toParams.fg.faults_lt_quorum_margin (hf _ ht0 (hhi.trans hmb))
    have hFQ := hframe.finalized_below_descendant_at' hrun hnc hy hw hw
      (by rw [max_eq_left (show tr.time a ≤ tr.time i by
            linarith only [hat, hti, hts, sp.toParams.hΔ])]; exact hmargin)
      hlo hhi hQ hwit hQ .refl
    rcases AC.anc_total hU hFQ hXQ with hFX | hXF
    swap
    · obtain ⟨hPhi, hPhiU⟩ := frameIn_at' hrun hnc hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := AC.castAt_head_anc hr hy hcast' (Or.inr rfl)
        (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      have hFW := hFW.mono hPhiU
      rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_F] at hFW
      exact ⟨W, hPhiU hW, hWr, hXF.trans hFW⟩
    have hFQ' : Anc (tr.HonestBlocksAt H) ell.frame.F Q := by
      rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_F]
      exact hFX.trans hXQ
    have hdom := witness_voterBlockTree_at' hrun hnc hsvc hcatch hm hw hy hcw hat hQw
      hcast hs hFQ'
    have hQy : Q ∈ (tr.state y i).fg.tree := by
      have ht := hdom.1
      rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_tree] at ht
      exact ht.1
    have hwy := witness_clause_at' hrun hnc hw hy hQ hQy hwit
    have hpath := Healing.witness_frame_at' hrun hnc hframe hy hc hlo hhi hmargin hQy hwy hXQ
    rcases hpath with hXF | ⟨-, hXt, hroot, -, hvQ, hXQf⟩
    · obtain ⟨hPhi, hPhiU⟩ := frameIn_at' hrun hnc hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := AC.castAt_head_anc hr hy hcast' (Or.inr rfl)
        (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      have hFW := hFW.mono hPhiU
      exact ⟨W, hPhiU hW, hWr, hXF.trans hFW⟩
    have hviab : AC.ViableAtVote ell e (s + 1) X := by
      have hdomA := AC.voterBlockTree_ancU hr.toU hrun.vstart hy hcast'
      rw [hs] at hdomA
      exact Or.inl ⟨hdomA Q hdom X hXQf, hroot, Q, hdom, hvQ, hXQf⟩
    exact htransfer y i ell e hy hcast hs hhi
      (by rw [Node.frame'_eq, Store.toFrame'_F]; exact hFX) hviab
      (fun z k ev hki hz hv hes => ih k hki z ev hz hv hes)

end Consensus.Goldilocks.Shadow.PU.Growing

end
