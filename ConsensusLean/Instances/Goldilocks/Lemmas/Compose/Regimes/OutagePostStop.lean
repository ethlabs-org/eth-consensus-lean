module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready

public section

/-! # Conditional post-stop outage adapters -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-- Among a slow lock's consecutive labels, at least one is outside the outage pollution
window, under the engine gap budget. -/
theorem exists_unpolluted_label (sp : SA.SAParams) {start stop : Time}
    (hΔ : 2 ≤ sp.Δ)
    (hgap : stop - start ≤ (4 * (sp.k : Time) - 6) * (sp.Δ - 1)) (s : Int) :
    ∃ m : Int, s - (sp.k : Int) < m ∧ m ≤ s ∧
      (sp.ts m + 2 * sp.Δ ≤ start ∨ stop ≤ sp.ts m + sp.Δ) := by
  have hk : (2 : Int) ≤ sp.k := by exact_mod_cast sp.two_le_k
  by_contra hn
  have hfirst : start < sp.ts (s - sp.k + 1) + 2 * sp.Δ := by
    by_contra h
    exact hn ⟨s - sp.k + 1, by omega, by omega, Or.inl (le_of_not_gt h)⟩
  have hlast : sp.ts s + sp.Δ < stop := by
    by_contra h
    exact hn ⟨s, by omega, le_rfl, Or.inr (le_of_not_gt h)⟩
  simp only [SA.SAParams.ts] at hfirst hlast
  nlinarith

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Shortening the recent-awake window preserves sleepy participation. -/
theorem etaSleepyAt_mono {c η η' t : Time} (hη : η' ≤ η)
    (h : Regimes.EtaSleepyAt tr H c η t) : Regimes.EtaSleepyAt tr H c η' t := by
  apply lt_of_le_of_lt (Set.ncard_le_ncard ?_) h
  rintro x (hr | ⟨hx, τ, hτ, hτt, haw⟩ | hf)
  · exact Or.inl hr
  · exact Or.inr (Or.inl ⟨hx, τ,
      (max_le_max_left 0 (sub_le_sub_left hη t)).trans hτ, hτt, haw⟩)
  · exact Or.inr (Or.inr hf)

/-- Every honest voter in a successor vote's merged view was awake during the preceding
slot's voting window. The lookback bound is an explicit hypothesis. -/
theorem merged_voters_recently_awake (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {c η : Time} (hη : sp.Δ ≤ η) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (_hs : e.msg.slot = s + 1) :
    SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆
      {x | Regimes.ReadyAt tr H c x (sp.ts s + sp.Δ) ∨
        Regimes.RecentlyAwake tr H η x (sp.ts s + sp.Δ) ∨ x ∉ H} := by
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  rintro x ⟨v, hv, rfl⟩
  by_cases hx : v.val ∈ H
  · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hr hy hc hv hx
    obtain ⟨ℓ', hc'⟩ := hv'
    have hslot : e'.msg.slot = s := by
      rw [he']
      exact SA.merged_vote_slot hr.localRun hy hc v hv
    have hspec := SA.castAt_spec hr.localRun hx hc'
    have hupper := SA.vote_time_le hr.localRun hx ⟨ℓ', hc'⟩
    have hlower := (SA.ts_le_iff_le_slot sp (hr.localRun.time_nonneg j)
      (sp.slot (tr.projAC.time j) : Int)).2 le_rfl
    rw [← hspec.2.1, hslot] at hupper hlower
    change sp.ts s ≤ tr.time j at hlower
    refine Or.inr (Or.inl ⟨hx, tr.time j, ?_, hupper, ?_⟩)
    · exact max_le (hr.localRun.time_nonneg j) (by linarith)
    · exact hr.localRun.awake_of_call v.val hx j ℓ' hc'.1
  · exact Or.inr (Or.inr hx)

/-- A single compatible result in the slow window suffices to make a stored slow lock
compatible. The unpolluted-result producer is an explicit hypothesis. -/
theorem slow_lock_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {l : SA.Lock} (hl : l ∈ (tr.state x i).ac.locks) (hlf : l.fast = false)
    (hgood : ∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < i → SA.ResultAt tr.projAC x c m.toNat C CV →
        Compatible (tr.HonestBlocks H) C B) :
    ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L B := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hl' : l ∈ (tr.projAC.state x i).locks := by
    rw [projAC_state hrun.toLocalRun hx i]; exact hl
  obtain ⟨c, hci, ℓ, C, CV, hu, hC, Lb, hLb, hLbC, ⟨L, hL, hLr, hLLb⟩, hsave⟩ :=
    SA.slow_lock_saved hr hx i l hl' hlf
  obtain ⟨m, hm, hms, hm0, hgood⟩ := hgood
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hx hu.1
  have down : ∀ {X Y}, Anc (tr.HonestBlocks H) X Y → Compatible (tr.HonestBlocks H) Y B →
      Compatible (tr.HonestBlocks H) X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hr.coherent hXY h
  refine ⟨L, hL, hLr, down hLLb ?_⟩
  rcases hms.lt_or_eq with hms | hms
  · obtain ⟨S, hS, hsaved, hLbS⟩ := hsave m hm hms
    have hmn : (m.toNat : Int) = m := Int.toNat_of_nonneg hm0
    obtain ⟨k, hkc, C', CV', hC', hroot⟩ := SA.saved_result hr hx c m.toNat (by
      simpa only [hmn] using hsaved)
    obtain ⟨ℓ', hu', hconf, -⟩ := id hC'
    have hC'mem := (SA.frameIn_of_callAt hr hx hu'.1).2 (SA.deepest_mem hconf).1.1
    have heq : C' = S := hr.coherent.1 hC'mem (hΦU hS) hroot
    exact down (Anc.mono hΦU hLbS) (heq ▸ hgood k C' CV' (hkc.trans hci) hC')
  · have hmn : m.toNat = l.slot := by omega
    exact down (Anc.mono hΦU hLbC) (hgood c C CV hci (hmn ▸ hC))

/-- Consumer interface for post-stop delivery of the preceding honest batch. No producer
of this service is assumed proved here. -/
def PostStopBatchCarry (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s₁ : Nat) : Prop :=
  ∀ s : Nat, s₁ ≤ s → ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = s + 1 →
    ∀ B : SA.Blk sp.n (List (FG.Att sp.n)), Anc (tr.HonestBlocks H) ℓ.frame.F B →
    (∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s}

/-- The post-stop batch service, fault bound, live-lock duty and frozen viability propagate
an all-honest base batch. The lock and viability producers remain explicit hypotheses. -/
theorem post_stop_honest_extend (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {s₁ : Nat}
    (hcarry : PostStopBatchCarry tr H s₁)
    (hfb : ∀ s : Nat, s₁ ≤ s → tr.FaultBound H (sp.ts s + sp.Δ))
    (hbase : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s₁ →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hlocks : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s₁ < e.msg.slot →
      SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i e.msg.slot B →
      (∀ s, s₁ ≤ s → s < e.msg.slot → ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' →
        e'.msg.slot = s → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
        Compatible (tr.HonestBlocks H) L B)
    (hFV : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → s₁ < e.msg.slot →
      (∀ s, s₁ ≤ s → s < e.msg.slot → ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' →
        e'.msg.slot = s → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      SA.ViableAtVote ℓ e e.msg.slot B) :
    ∀ s, s₁ ≤ s → ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hge
    by_cases heq : s = s₁
    · exact heq ▸ hbase
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
    have hq : s₁ ≤ q := by omega
    have hall := ih q (by omega) hq
    intro x hx k
    induction k using Nat.strong_induction_on generalizing x with
    | _ k ikh =>
      rintro e ⟨ℓ, hc⟩ hs
      have hlower : ∀ s, s₁ ≤ s → s < e.msg.slot → ∀ x ∈ H, ∀ j e',
          SA.VoteAt tr.projAC x j e' → e'.msg.slot = s →
          SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
        intro s hs₁ hs₂
        exact ih s (by omega) hs₁
      have hearly : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k e.msg.slot B := by
        intro y hy j hj e' hv hes
        exact ikh j hj y hy e' hv (hes.trans hs)
      have hviab := hFV x hx k ℓ e hc (by omega) hlower
      obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr.localRun hx hc.1
      rcases hviab with hv | hf
      · have hcount : Hᶜ.ncard <
            {y | y ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC y j e' ∧ e'.msg.slot = q}.ncard := by
          refine lt_of_lt_of_le (hfb q hq) (Set.ncard_le_ncard ?_)
          rintro y ⟨hy, hw, hj⟩
          obtain ⟨j, e', hv', hs', -⟩ := vote_of_awake_joined hrun hnc hy hw hj
          exact ⟨hy, j, e', hv', hs'⟩
        have hviab : SA.ViableAtVote ℓ e (q + 1) B := by
          apply Or.inl
          simpa only [hs] using hv
        exact vote_extends_of_batch hr hx hc hs hviab hall hcount
          (hcarry q hq x hx k ℓ e hc hs B (Anc.mono hΦU (hΦ.rooted.2 B hv.1.1)) hall)
          (hlocks x hx k ℓ e hc (by omega) hearly hlower)
      · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr.localRun hx hc
        exact ⟨Hd, hΦU hHd, hHdr, (Anc.mono hΦU hf).trans (Anc.mono hΦU hfHd)⟩

/-- A counted base batch supplies the first all-honest label, provided its carry, live-lock
and frozen-viability duties hold at every honest cast. -/
theorem post_stop_first_honest (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {q₀ : Nat} {SX W : Set (Fin sp.n)}
    (hSXH : SX ⊆ H)
    (hSXv : ∀ x ∈ SX, ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q₀)
    (hall : ∀ x ∈ SX, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q₀ →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hWH : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q₀ → x ∈ W)
    (hWF : Hᶜ ⊆ W)
    (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q₀ + 1 →
      Anc (tr.HonestBlocks H) ℓ.frame.F B →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e q₀
        {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = q₀})
    (hlocks : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q₀ + 1 →
      SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (q₀ + 1) B →
      ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
        Compatible (tr.HonestBlocks H) L B)
    (hFV : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q₀ + 1 →
      SA.ViableAtVote ℓ e (q₀ + 1) B) :
    ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q₀ + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  intro x hx k
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    rintro e ⟨ℓ, hc⟩ hs
    have hearly : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k (q₀ + 1) B :=
      fun y hy j hj e' hv hes => ih j hj y hy e' hv hes
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr.localRun hx hc.1
    rcases hFV x hx k ℓ e hc hs with hv | hf
    · have hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (q₀ + 1)).votes ⊆ W := by
        rintro y ⟨v, hv, rfl⟩
        by_cases hy : v.val ∈ H
        · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hr hx hc hv hy
          exact hWH _ hy j e' hv' (by
            rw [he']; exact SA.merged_vote_slot hr.localRun hx hc v hv)
        · exact hWF hy
      exact vote_extends_of_counted_batch hr hx hc hs (Or.inl hv) hSXH hSXv hall hW hcount
        (hcarry x hx k ℓ e hc hs (Anc.mono hΦU (hΦ.rooted.2 B hv.1.1)))
        (hlocks x hx k ℓ e hc hs hearly)
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr.localRun hx hc
      exact ⟨Hd, hΦU hHd, hHdr, (Anc.mono hΦU hf).trans (Anc.mono hΦU hfHd)⟩

/-- The two-time count for the first post-stop step. Proposal transport and acceptance are
represented only by the explicit case hypothesis. -/
theorem first_step_count {q : Nat} {c : Time} (hΔ : 2 ≤ sp.Δ)
    (h₁ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + (sp.Δ - 1)))
    (h₂ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + sp.Δ))
    {V : Set (Fin sp.n)}
    (hV : ∀ x ∈ V, x ∉ H ∨ tr.awake x (sp.ts q))
    (hK : ∀ x, Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ) → x ∈ V)
    (hcase : (∀ x, Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1)) → x ∈ V) ∨
      (∀ x ∈ V, x ∈ H → Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ) ∨
        Regimes.RecentlyAwake tr H (sp.Δ - 1) x (sp.ts q + sp.Δ))) :
    V.ncard < 2 * ({x | Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)} ∪
      ({x | Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1))} ∩ V)).ncard := by
  let R : Set (Fin sp.n) := {x | Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1))}
  let K : Set (Fin sp.n) := {x | Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)}
  let W₁ : Set (Fin sp.n) := {x | x ∈ R ∨
    Regimes.RecentlyAwake tr H (sp.Δ - 1) x (sp.ts q + (sp.Δ - 1)) ∨ x ∉ H}
  let W₂ : Set (Fin sp.n) := {x | x ∈ K ∨
    Regimes.RecentlyAwake tr H (sp.Δ - 1) x (sp.ts q + sp.Δ) ∨ x ∉ H}
  have ht : 0 ≤ sp.ts q := by simp only [SA.SAParams.ts]; positivity
  have hVW₁ : V ⊆ W₁ := by
    intro x hx
    rcases hV x hx with hf | hw
    · exact Or.inr (Or.inr hf)
    by_cases hh : x ∈ H
    · exact Or.inr (Or.inl ⟨hh, sp.ts q,
        max_le ht (by linarith), by linarith, hw⟩)
    · exact Or.inr (Or.inr hh)
  have hIR : (R ∩ V).ncard ≤ (K ∪ (R ∩ V)).ncard :=
    Set.ncard_le_ncard Set.subset_union_right
  have hKK : K.ncard ≤ (K ∪ (R ∩ V)).ncard :=
    Set.ncard_le_ncard Set.subset_union_left
  change W₁.ncard < 2 * R.ncard at h₁
  change W₂.ncard < 2 * K.ncard at h₂
  change V.ncard < 2 * (K ∪ (R ∩ V)).ncard
  rcases hcase with hR | hV₂
  · have hRV : R ⊆ V := hR
    have hI : R ∩ V = R := Set.inter_eq_left.mpr hRV
    have hle := Set.ncard_le_ncard hVW₁
    rw [hI] at hIR
    rw [hI]
    omega
  · have hVW₂ : V ⊆ W₂ := by
      intro x hx
      by_cases hh : x ∈ H
      · exact (hV₂ x hx hh).imp_right Or.inl
      · exact Or.inr (Or.inr hh)
    have hNW₁ : R \ V ⊆ W₁ := fun _ hx => Or.inl hx.1
    have hNW₂ : R \ V ⊆ W₂ := by
      rintro x ⟨hx, hxV⟩
      have hh : x ∈ H := hx.1
      by_cases hc : c < -1
      · exact False.elim (hxV (hK x ⟨hh, fun τ hτ hτ' => by
          have := le_of_max_le_right hτ
          linarith⟩))
      have hw := hx.2 (sp.ts q + (sp.Δ - 1))
        (max_le (by linarith) (by linarith)) le_rfl
      exact Or.inr (Or.inl ⟨hh, sp.ts q + (sp.Δ - 1),
        max_le (by linarith) (by linarith), by linarith, hw⟩)
    have hle₁ := Set.ncard_le_ncard (Set.union_subset hVW₁ hNW₁)
    have hle₂ := Set.ncard_le_ncard (Set.union_subset hVW₂ hNW₂)
    have hdis : Disjoint V (R \ V) := Set.disjoint_sdiff_right
    rw [Set.ncard_union_eq hdis] at hle₁ hle₂
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard R V
    omega

/-- The first-step dichotomy separates ready receipt forwarding from vote extension. -/
theorem first_step_hcase (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {q : Nat} (hq : 0 < q) {c : Time} (hc : 8 * sp.Δ ≤ c + 1) (hΔ : 2 ≤ sp.Δ)
    (hrelay : (∃ x ∈ H, ∃ i ℓ, tr.projAC.CallAt x i ℓ ∧ tr.time i = sp.ts q ∧
        SA.voteReady sp ℓ.frame q) →
      ∀ y, Regimes.ReadyAt tr H c y (sp.ts q + (sp.Δ - 1)) →
        ∃ i ℓ, tr.projAC.CallAt y i ℓ ∧
          ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) ∧
          sp.ts q ≤ tr.time i ∧ tr.time i ≤ sp.ts q + (sp.Δ - 1) ∧
          SA.voteReady sp ℓ.frame q) :
    (∀ x, Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1)) →
        x ∈ {x | x ∉ H ∨ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q}) ∨
      (∀ x ∈ {x | x ∉ H ∨ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q}, x ∈ H →
        Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ) ∨
          Regimes.RecentlyAwake tr H (sp.Δ - 1) x (sp.ts q + sp.Δ)) := by
  classical
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have ht : 0 ≤ sp.ts q := by simp only [SA.SAParams.ts]; positivity
  have hnext : sp.ts q + sp.Δ < sp.ts (q + 1 : Nat) := by
    simp only [SA.SAParams.ts]; push_cast; nlinarith
  by_cases hsome : ∃ x ∈ H, ∃ i ℓ, tr.projAC.CallAt x i ℓ ∧ tr.time i = sp.ts q ∧
      SA.voteReady sp ℓ.frame q
  · left
    intro x hx
    obtain ⟨i, ℓ, hi, hkind, hlo, hhi, hready⟩ := hrelay hsome x hx
    have hslot := SA.slot_of_mem sp q hlo (by linarith : tr.time i < sp.ts (q + 1 : Nat))
    have hslot₁ := SA.slot_of_mem sp q (by linarith : sp.ts q ≤ sp.ts q + (sp.Δ - 1))
      (by linarith : sp.ts q + (sp.Δ - 1) < sp.ts (q + 1 : Nat))
    have hj := (ready_implies_joined sp ro dg H tr proposer hrun x hx.1
      (sp.ts q + (sp.Δ - 1)) c (by linarith) hc hx.2).2
    have hjoin : tr.JoinedAt x (tr.time i) := by
      intro k hk hkt
      have hh := hj k hk (hkt.trans hhi)
      change 0 < sp.slot (tr.time i) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (tr.time i) - 1)
      change 0 < sp.slot (sp.ts q + (sp.Δ - 1)) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts q + (sp.Δ - 1)) - 1) at hh
      simpa only [hslot, hslot₁] using hh
    obtain ⟨k, -, e, he, hs, -⟩ := vote_of_ready_receipt hrun hnc hx.1 hq hi hkind
      hslot (by linarith) hjoin hready
    exact Or.inr ⟨k, e, he, hs⟩
  · right
    intro x hx hxH
    obtain ⟨k, e, ⟨ℓ, hcast⟩, hs⟩ := hx.resolve_left (not_not.mpr hxH)
    have hspec := SA.castAt_spec hr hxH hcast
    have hlo := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) (q : Int)).2
      (by rw [← hspec.2.1, hs])
    have hhi := SA.vote_time_le hr hxH ⟨ℓ, hcast⟩
    rw [← hspec.2.1, hs] at hhi
    change sp.ts q ≤ tr.time k at hlo
    change tr.time k ≤ sp.ts q + sp.Δ at hhi
    have hne : tr.time k ≠ sp.ts q := by
      intro heq
      exact hsome ⟨x, hxH, k, ℓ, hcast.1, heq,
        hs ▸ SA.cast_ready hr hxH hcast (by
          rw [hs]; change tr.time k < sp.ts q + sp.Δ; linarith)⟩
    have hstrict : sp.ts q < tr.time k := lt_of_le_of_ne hlo (Ne.symm hne)
    have hstep : sp.ts q + 1 ≤ tr.time k := by
      exact Int.add_one_le_iff.mpr hstrict
    exact Or.inr ⟨hxH, tr.time k, max_le (by linarith) (by linarith), hhi,
      hr.awake_of_call x hxH k ℓ hcast.1⟩

/-- Handler facts assemble the counted batch; relay and extension remain explicit producers. -/
theorem first_step_batch (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {q : Nat} (hq : 0 < q) {c : Time} (hc : 8 * sp.Δ ≤ c + 1) (hΔ : 2 ≤ sp.Δ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h₁ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + (sp.Δ - 1)))
    (h₂ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + sp.Δ))
    (hrelay : (∃ x ∈ H, ∃ i ℓ, tr.projAC.CallAt x i ℓ ∧ tr.time i = sp.ts q ∧
        SA.voteReady sp ℓ.frame q) →
      ∀ y, Regimes.ReadyAt tr H c y (sp.ts q + (sp.Δ - 1)) →
        ∃ i ℓ, tr.projAC.CallAt y i ℓ ∧
          ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) ∧
          sp.ts q ≤ tr.time i ∧ tr.time i ≤ sp.ts q + (sp.Δ - 1) ∧
          SA.voteReady sp ℓ.frame q)
    (hB1 : ∀ x, (Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1)) ∨
        Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)) →
      ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    let V := {x | x ∉ H ∨ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q}
    let S := {x | Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)} ∪
      ({x | Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1))} ∩ V)
    S ⊆ H ∧ (∀ x ∈ S, ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q) ∧
      (∀ x ∈ S, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B) ∧
      (∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q → x ∈ V) ∧
      Hᶜ ⊆ V ∧ V.ncard < 2 * S.ncard := by
  dsimp only
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have ht : 0 ≤ sp.ts q := by simp only [SA.SAParams.ts]; positivity
  have hK : ∀ x, Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ) →
      ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q := by
    intro x hx
    obtain ⟨hw, hj⟩ := ready_implies_joined sp ro dg H tr proposer hrun x hx.1
      (sp.ts q + sp.Δ) c (by linarith) hc hx.2
    obtain ⟨k, e, he, hs, -⟩ := vote_of_awake_joined hrun hnc hx.1 hw hj
    exact ⟨k, e, he, hs⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, first_step_count hΔ h₁ h₂ ?_ ?_
    (first_step_hcase hrun hnc hq hc hΔ hrelay)⟩
  · rintro x (hx | ⟨hx, -⟩) <;> exact hx.1
  · rintro x (hx | ⟨hx, hv⟩)
    · exact hK x hx
    · exact hv.resolve_left (not_not.mpr hx.1)
  · intro x hx
    apply hB1 x
    rcases hx with hx | ⟨hx, -⟩
    · exact Or.inr hx
    · exact Or.inl hx
  · intro x _ k e he hs
    exact Or.inr ⟨k, e, he, hs⟩
  · intro x hx
    exact Or.inl hx
  · intro x hx
    rcases hx with hx | ⟨k, e, ⟨ℓ, hcast⟩, hs⟩
    · exact Or.inl hx
    by_cases hxH : x ∈ H
    · right
      obtain ⟨-, hslot, hjoin, -⟩ := SA.castAt_spec hr hxH hcast
      have hjp : SA.joined sp (tr.projAC.post k) (tr.projAC.time k) := by
        unfold SA.joined
        rw [SA.restartTime_of_castAt hr hxH hcast]
        exact hjoin
      have hw := (SA.joined_awake sp _ ro H _ tr.projAC hr x hxH k ℓ hcast.1 hjp).1
      have hlo := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) (q : Int)).2
        (by rw [← hslot, hs])
      apply hw (sp.ts q) (max_le ht ?_) hlo
      rw [← hslot, hs]
      simp only [SA.SAParams.ts]
      nlinarith [sp.toParams.hΔ]
    · exact Or.inl hxH
  · intro x hx
    exact Or.inr (hK x hx)

/-- The counted first batch and explicit post-stop duties propagate the prefix to every
honest vote from the next slot onward. -/
theorem post_stop_chain (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {q : Nat} (hq : 0 < q) {c : Time} (hc : 8 * sp.Δ ≤ c + 1) (hΔ : 2 ≤ sp.Δ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h₁ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + (sp.Δ - 1)))
    (h₂ : Regimes.EtaSleepyAt tr H c (sp.Δ - 1) (sp.ts q + sp.Δ))
    (hrelay : (∃ x ∈ H, ∃ i ℓ, tr.projAC.CallAt x i ℓ ∧ tr.time i = sp.ts q ∧
        SA.voteReady sp ℓ.frame q) →
      ∀ y, Regimes.ReadyAt tr H c y (sp.ts q + (sp.Δ - 1)) →
        ∃ i ℓ, tr.projAC.CallAt y i ℓ ∧
          ((∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) ∧
          sp.ts q ≤ tr.time i ∧ tr.time i ≤ sp.ts q + (sp.Δ - 1) ∧
          SA.voteReady sp ℓ.frame q)
    (hB1 : ∀ x, (Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1)) ∨
        Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)) →
      ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = q →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hcarry₀ : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q + 1 →
      Anc (tr.HonestBlocks H) ℓ.frame.F B →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e q
        {v | ∃ x ∈ ({x | Regimes.ReadyAt tr H c x (sp.ts q + sp.Δ)} ∪
          ({x | Regimes.ReadyAt tr H c x (sp.ts q + (sp.Δ - 1))} ∩
            {x | x ∉ H ∨ ∃ k e, SA.VoteAt tr.projAC x k e ∧ e.msg.slot = q})),
          ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = q})
    (hlocks₀ : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q + 1 →
      SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (q + 1) B →
      ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
        Compatible (tr.HonestBlocks H) L B)
    (hFV₀ : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → e.msg.slot = q + 1 →
      SA.ViableAtVote ℓ e (q + 1) B)
    (hcarry : PostStopBatchCarry tr H (q + 1))
    (hfb : ∀ s : Nat, q + 1 ≤ s → tr.FaultBound H (sp.ts s + sp.Δ))
    (hlocks : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → q + 1 < e.msg.slot →
      SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i e.msg.slot B →
      (∀ s, q + 1 ≤ s → s < e.msg.slot → ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' →
        e'.msg.slot = s → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
        Compatible (tr.HonestBlocks H) L B)
    (hFV : ∀ y ∈ H, ∀ i ℓ e, SA.CastAt tr.projAC y i ℓ e → q + 1 < e.msg.slot →
      (∀ s, q + 1 ≤ s → s < e.msg.slot → ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' →
        e'.msg.slot = s → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      SA.ViableAtVote ℓ e e.msg.slot B) :
    ∀ s, q + 1 ≤ s → ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  obtain ⟨hSXH, hSXv, hall, hWH, hWF, hcount⟩ :=
    first_step_batch hrun hnc hq hc hΔ h₁ h₂ hrelay hB1
  exact post_stop_honest_extend hrun hnc hcarry hfb
    (post_stop_first_honest hrun hnc hSXH hSXv hall hWH hWF hcount hcarry₀ hlocks₀ hFV₀)
    hlocks hFV

end Consensus.Goldilocks.Compose
