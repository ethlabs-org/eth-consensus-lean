module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Premises
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the counts

The counts that cross a compromise, each charged at one cut (TL §0):

* `faults_lt_voters` (Corollary FB in voter form): the slot-`s` voters still honest at
  `d ∈ [t_s + Δ, t_s + 6Δ]` outnumber the validators compromised by `d`;
* `honest_supporter_at` (`P_{s+1}` core): an origin within `b` has a supporter honest at its
  vote, counted at the writer's update (`d = t_s + 6Δ`, the slot count) or at the optimistic
  check (`2 f_d < n`). Signers are classified at the cut of the pool they are read in
  (Lemma G, `pool_vote_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- `t_s ≥ 0`. -/
theorem ts_natCast_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  simp only [SAParams.ts]
  exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s)

/-- **FB in voter form**: for a slot `s ≥ σ₀`, at `d ∈ [t_s + Δ, min b (t_s + 6Δ)]`, the
validators compromised by `d` are fewer than the slot-`s` voters still honest at `d`. -/
theorem faults_lt_voters (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} {σ₀ : Nat} (hB : SleepyBoundsFrom tr H σ₀ b) {s : Nat} {d : Time} (hs : σ₀ ≤ s)
    (h1 : sp.ts s + sp.Δ ≤ d) (hdb : d ≤ b) (h6 : d ≤ sp.ts s + 6 * sp.Δ) :
    (H d)ᶜ.ncard < (VotersAt tr H s d).ncard := by
  refine (hB.slot s d hs h1 hdb h6).trans_le
    (Set.ncard_le_ncard (fun y hy => ?_) (Set.toFinite _))
  obtain ⟨k, e, hv, hs, -⟩ :=
    vote_of_awake_joined_at hrun hnc (hrun.antitone h1 hy.1)
      (mayVote_stock_at hrun hnc (ts_add_delta_nonneg _) (hrun.antitone h1 hy.1)) hy.2.1 hy.2.2
  exact votersAt_iff.2 ⟨hy.1, k, e, hv, hs⟩

/-- **An origin within `b` has a supporter honest at its vote**: a slot-`s` vote at a time `≤ b`
whose head extends it, for a label `s ≥ σ₀` whose service is available (`a ≤ t_s`). A result's
counted votes meet the validators honest at `d = t_s + 6Δ` that were awake and joined at `t_s + Δ`
(all participants of the writer's update, the slot count at `d`); an optimistic selection's `3n/4`
voters meet `H d` at the check's time `d` (`2 f_d < n`). -/
theorem honest_supporter_at
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : σ₀ ≤ s) (ha : a ≤ sp.ts s) (hC : OriginWithin tr H C s b) :
    ∃ x j e, HVoteAt tr H x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, i₀, CV, hX, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · have hd := hrun.time_nonneg i₀
    have hm := hrun.time_mono
    have hmaj := SA.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ := hB.slot s (tr.time i₀) hs (by rw [ht₀]; linarith) hi₀ ht₀.le
    change (H (tr.time i₀))ᶜ.ncard < {y | y ∈ H (tr.time i₀) ∧ tr.awake y (sp.ts s + sp.Δ) ∧
      tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard at hJ
    have hsvc := hsync.acWindow_upTo hrun hd
    have hJV : {y | y ∈ H (tr.time i₀) ∧ tr.awake y (sp.ts s + sp.Δ) ∧
        tr.JoinedAt y (sp.ts s + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy => by
      have h := awake_participant_window_before (hrun.upTo hd) (hnc.upTo _) hsvc ha hX
        (by rw [RunTrace.upTo_projAC]; exact (sa_updateAt_upTo hm).mpr ⟨le_rfl, hu⟩)
        (le_min hi₀ le_rfl) hy.1 (mayVote_stock (hrun.upTo hd) (hnc.upTo _) hy.1 _)
        ⟨hy.2.1, by rw [ht₀]; linarith⟩ (joinedAt_upTo hy.2.2)
      rwa [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl] at h
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ :
        ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H (tr.time i₀) := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H (tr.time i₀) :=
        fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint {y | y ∈ H (tr.time i₀) ∧ tr.awake y (sp.ts s + sp.Δ) ∧
          tr.JoinedAt y (sp.ts s + sp.Δ)} {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ (H (tr.time i₀))ᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := pool_vote_at hrun hnc hX hvp hwH
    obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hX hu.1
    exact ⟨_, j, e, hve, (hm hj.le).trans hi₀, state_pool_slot_at hrun hnc hX s _ hvp, R,
      hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := id hO
    obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hX hpt.1
    have hsel' := hsel
    unfold SA.optimisticSelect at hsel'
    dsimp only at hsel'
    split_ifs at hsel'
    have h34 := (SA.deepest_mem hsel').1.2.1
    rw [hsl, hrun.stock] at h34
    have hf := hB.two (tr.time i₀) (hrun.time_nonneg i₀) hi₀
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time i₀))ᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H (tr.time i₀) := not_not.1 huH
    have hd := hrun.time_nonneg i₀
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote (acRun_upTo hrun hnc hd) hX
      (by
        refine ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hpt.1, ?_⟩
        rw [projAC_upTo_state hrun le_rfl]
        exact hpt.2) hv huH
    obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
    exact ⟨_, j, e, hVoteAt_iff.2 ⟨hrun.antitone hjd huH, hve⟩, (hrun.time_mono hj).trans hi₀,
      hvs, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩

end Consensus.Goldilocks.Compose.Growing

end
