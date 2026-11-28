module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Premises
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the counts

The counts that cross a compromise, each charged at one cut (TL §0), among the members of a slot
committee `K` (`CommitteeFacts`, `CommitteeBoundsFrom`):

* `faults_lt_voters` (Corollary FB in voter form): the slot-`s` voters still honest at
  `d ∈ [t_s + Δ, t_s + 6Δ]` outnumber the members of `K s` compromised by `d`;
* `honest_supporter_at` (`P_{s+1}` core): an origin within `b` has a supporter honest at its
  vote, counted at the writer's update (`d = t_s + 6Δ`, the committee slot count) or at the
  optimistic check (`2 |K s ∩ (H d)ᶜ| < committeeSize`). Signers are classified at the cut of the
  pool they are read in (Lemma G, `pool_vote_at`); counted signers are members (P). -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- `t_s ≥ 0`. -/
theorem ts_natCast_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  simp only [ACParams.ts]
  exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s)

/-- An optimistic selection of slot `s` is made in `[t_s, t_s + 2Δ)`. -/
theorem optimistic_time_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {i s : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : AC.OptimisticLockAt tr.projAC x i s C CV) :
    sp.ts s ≤ tr.time i ∧ tr.time i < sp.ts s + 2 * sp.Δ := by
  obtain ⟨ℓ, A, -, hsl, hsel, -⟩ := h
  subst hsl
  exact ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 le_rfl,
    (AC.optimisticSelect_guard hsel).2.2.1⟩

/-- A cast of a node honest then is in `[t_σ, t_σ + Δ]` of its slot `σ`. -/
theorem cast_time_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ℓ e) :
    sp.ts e.msg.slot ≤ tr.time i ∧ tr.time i ≤ sp.ts e.msg.slot + sp.Δ := by
  refine ⟨?_, (cast_head_fcRoot_at hrun hnc hy hc).2⟩
  rw [(castAt_spec_at hrun hnc hy hc).2.1]
  exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 le_rfl

/-- **FB in voter form**: for a slot `s ≥ σ₀`, at `d ∈ [t_s + Δ, min b (t_s + 6Δ)]`, the
members of the slot-`s` committee compromised by `d` are fewer than the slot-`s` voters still
honest at `d`. -/
theorem faults_lt_voters {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {b : Time} {σ₀ : Nat} (hBK : CommitteeBoundsFrom tr H K σ₀ b) {s : Nat} {d : Time}
    (hs : σ₀ ≤ s) (h1 : sp.ts s + sp.Δ ≤ d) (hdb : d ≤ b) (h6 : d ≤ sp.ts s + 6 * sp.Δ) :
    (K.committee s ∩ (H d)ᶜ).ncard < (VotersAt tr H s d).ncard := by
  refine (hBK.slotK s d hs h1 hdb h6).trans_le
    (Set.ncard_le_ncard (fun y ⟨hyK, hyH, hyw⟩ => ?_) (Set.toFinite _))
  obtain ⟨hw, hj⟩ := (mem_awakeJoined_projAC hrun).1 hyw
  have hy := hrun.antitone h1 hyH
  obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined_at hrun hnc hy
    (mayVote_of_committee hKB.hGate (ts_add_delta_nonneg _) hy hyK) hw hj
  exact votersAt_iff.2 ⟨hyH, k, e, hv, hs⟩

/-- **An origin within `b` has a supporter honest at its vote**: a slot-`s` vote at a time `≤ b`
whose head extends it, for a label `s ≥ σ₀` whose service is available (`a ≤ t_s`). A result's
counted votes are of slot-`s` committee members and meet the members honest at `d = t_s + 6Δ`
that were awake and joined at `t_s + Δ` (all participants of the writer's update, the committee
slot count at `d`); an optimistic selection's `3/4` of the committee size, all members, meet
`H d` at the check's time `d` (`2 f_d < |K s|` among the committee). -/
theorem honest_supporter_at
    {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hBK : CommitteeBoundsFrom tr H K σ₀ b) {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : σ₀ ≤ s) (ha : a ≤ sp.ts s) (hC : OriginWithin tr H C s b) :
    ∃ x j e, HVoteAt tr H x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, i₀, CV, hX, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · have hd := hrun.time_nonneg i₀
    have hm := hrun.time_mono
    have hmaj := AC.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ : (K.committee s ∩ (H (tr.time i₀))ᶜ).ncard < (K.committee s ∩
        {y | y ∈ H (tr.time i₀) ∧ tr.projAC.awake y (sp.ts s + sp.Δ) ∧
          AC.JoinedAt tr.projAC y (sp.ts s + sp.Δ)}).ncard :=
      hBK.slotK s (tr.time i₀) hs (by rw [ht₀]; linarith) hi₀ ht₀.le
    have hsvc := hsync.acWindow_upTo hrun hd
    have hJV : K.committee s ∩ {y | y ∈ H (tr.time i₀) ∧ tr.projAC.awake y (sp.ts s + sp.Δ) ∧
        AC.JoinedAt tr.projAC y (sp.ts s + sp.Δ)} ⊆
        AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y ⟨hyK, hyH, hyw⟩ => by
      obtain ⟨hw, hj⟩ := (mem_awakeJoined_projAC hrun).1 hyw
      have h := awake_participant_window_before (hrun.upTo hd) (hnc.upTo _) hsvc ha hX
        (by rw [RunTrace.upTo_projAC]; exact (AC.upTo_updateAt hm).mpr ⟨le_rfl, hu⟩)
        (le_min hi₀ le_rfl) hyH (mayVote_upTo hrun (mayVote_of_committee hKB.hGate hd hyH hyK))
        ⟨hw, by rw [ht₀]; linarith⟩ (joinedAt_upTo hj)
      rwa [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl] at h
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    have hSK : {w | ∃ v ∈ CV, v.val = w} ⊆ K.committee s := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact hKB.hP.1 _ X hX i₀ (fun k hk => hm hk.le) s v hv.1
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ :
        ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H (tr.time i₀) := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H (tr.time i₀) :=
        fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint (K.committee s ∩ {y | y ∈ H (tr.time i₀) ∧
          tr.projAC.awake y (sp.ts s + sp.Δ) ∧ AC.JoinedAt tr.projAC y (sp.ts s + sp.Δ)})
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.2.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ (K.committee s ∩ (H (tr.time i₀))ᶜ).ncard :=
        Set.ncard_le_ncard fun y hy => ⟨hSK hy, hno y hy⟩
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
    unfold AC.optimisticSelect at hsel'
    dsimp only at hsel'
    split_ifs at hsel'
    have h34 := (AC.deepest_mem hsel').1.2.1
    rw [hsl] at h34
    have hOK : AC.optimisticVoters sp A ℓ.frame s C ⊆ K.committee s :=
      fun _ ⟨v, hv, hvu, _⟩ => hvu ▸ hKB.hP.2 X i₀ ℓ A hX hpt s v hv
    obtain ⟨ht0, ht2⟩ := optimistic_time_at hrun hO
    have hf := hBK.twoK s (tr.time i₀) hs ht0 hi₀ ht2.le
    rw [hKB.hsize s] at hf
    obtain ⟨u, hu, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ (H (tr.time i₀))ᶜ)
        (t := AC.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : u ∈ H (tr.time i₀) := by_contra fun h => huH ⟨hOK hu, h⟩
    obtain ⟨v, hv, rfl, R, hR, hRr, hCR⟩ := hu
    have hd := hrun.time_nonneg i₀
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := AC.optimisticPoint_pool_voteU (acRun_upTo hrun hnc hd).toU
        hX
      (by
        refine ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hpt.1, ?_⟩
        rw [projAC_upTo_state hrun le_rfl]
        exact hpt.2) hv huH
    obtain ⟨hjd, hve⟩ := AC.upTo_voteAt.mp hve
    exact ⟨_, j, e, hVoteAt_iff.2 ⟨hrun.antitone hjd huH, hve⟩, (hrun.time_mono hj).trans hi₀,
      hvs, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- A node honest at `t ≥ 0` and awake through the catch-up window before `t` is awake and joined
at `t`. The node was honest at each intermediate tick and restart by antitonicity. -/
theorem ready_implies_joined_at {A : NodeAC sp.toParams} {tr : RunTrace A}
    {dg : Digest (List (FG.Att sp.n)) A.Payload} {sg : A.Msg → Fin sp.n}
    {ini : Fin sp.n → A.State}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {y : Fin sp.n}
    {t c : Time} (hy : y ∈ H t) (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  refine Compose.ready_implies_joined_of_cuts hrun.time_mono
    (fun k hk hkt => hrun.sleep_of_restart y k (hrun.antitone hkt hy) hk) ?_ ht hc hawake
  intro u hu hut hpub hw
  obtain ⟨j, x, fgDue, hj⟩ := hrun.tick_of_awake y u (hrun.antitone hut hy) hu hpub hw
  exact ⟨j, Compose.group_call hj⟩

/-- `2 f_d < n` from the count at `d`, with `h_t ≤ |H d|`. -/
private theorem two_faults_lt_of_faultBoundAt {t d : Time} (h : tr.FaultBoundAt H t d) :
    2 * (H d)ᶜ.ncard < sp.n := by
  have hle : {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard ≤ (H d).ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : (H d)ᶜ.ncard < {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard := h
  omega

/-- **The count shapes from the counts after a start `a`** (the look-ahead budget clamped at
`b`), for the slots `s ≥ σ₀` whose slot point `t_s + Δ` is at or after `a`: `2 f_d < n` at
`d ∈ [a, b]` from the count at `d` charged at `min (d + 5Δ) b ≥ d`, and at `d ∈ [0, a)` from the
count at `a` (faults only grow; `a ≤ b` unless `a ≤ 0`); the slot count at
`d ∈ [t_s + Δ, t_s + 6Δ]` from the count at `t_s + Δ` charged at `min (t_s + 6Δ) b ≥ d`, and the
late count likewise from `t_s + 2Δ`. -/
theorem sleepyBoundsFrom_of_faultBoundAt (hanti : Antitone H) {a b : Time} {σ₀ : Nat}
    (hσ : a ≤ sp.ts σ₀ + sp.Δ) (hab : a ≤ max b 0)
    (hfb : ∀ t, 0 ≤ t → a ≤ t → t ≤ b → tr.FaultBoundAt H t (min (t + 5 * sp.Δ) b)) :
    Compose.Growing.SleepyBoundsFrom tr H σ₀ b := by
  have hΔ := sp.toParams.hΔ
  refine ⟨fun d h0 hdb => ?_, fun s d hs h1 hdb h6 => ?_, fun s d hs h1 hdb h7 => ?_⟩
  · rcases le_or_gt a d with had | hda
    · exact two_faults_lt_of_faultBoundAt
        (RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) (hfb d h0 had hdb))
    · have hab' : a ≤ b := (le_max_iff.mp hab).resolve_right (by linarith)
      exact two_faults_lt_of_faultBoundAt (RunTrace.FaultBoundAt.mono_right hanti
        (le_min (by linarith) hdb) (hfb a (by linarith) le_rfl hab'))
  · have hts := Compose.ts_le_ts (sp := sp) hs
    have h0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have h := hfb (sp.ts s + sp.Δ) (by linarith) (by linarith) (h1.trans hdb)
    exact RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) h
  · have hts := Compose.ts_le_ts (sp := sp) hs
    have h0 := Compose.Growing.ts_natCast_nonneg (sp := sp) s
    have h := hfb (sp.ts s + 2 * sp.Δ) (by linarith) (by linarith) (h1.trans hdb)
    exact RunTrace.FaultBoundAt.mono_right hanti (le_min (by linarith) hdb) h

end Consensus.Goldilocks.Obligations.Growing

end
