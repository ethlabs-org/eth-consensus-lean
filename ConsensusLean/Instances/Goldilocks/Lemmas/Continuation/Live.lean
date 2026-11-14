module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.LiveAdopt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Read
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Sleepy
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The continued liveness after a hand-over

Proposal liveness of the confirmed output after a hand-over at `T`, for deadlines after `T`, from
the seeded invariant (`SeededInvariant`, floors `r`, `r + k − 1`, from `t₁`), the reset service
with its catch-up, and the slot counts from `r`. Deadlines up to `T` are healthy ones.

* `continued_include_at`: the seeded form of the finite sleepy inclusion (`include_sleepy_at`): a
  proposal of a slot `p ≥ r + k + 1` released at `τ ≥ t₁ + 8Δ` by a proposer ready then and
  honest through its hold is in the confirmed read of every node ready at `t ∈ [τ + 6Δ, b]`, for
  `T ≤ b`, `t_{r+k} ≤ t₁` and conviction below a third on held chains. Slots `p ≤ σ` are healthy
  ones (`operational_update_selection_at`); later slots go through the seeded walk, votes and
  adoption (`Continuation/LiveWalk`, `LiveReader`, `LiveVotes`, `LiveAdopt`).
* `handover_query_regime`: the hand-over premise of `Continues` gives the hand-over disjunct of
  `ConfirmedQueryAt.regime`, which restates the regime conjuncts of `System.Handover`;
* `continued_proposal_live_at`: for a nonfinal query after `t₁` and `t_{r+k}`, with progress from
  the healthy readiness, some proposal released after the query by a key ready then is in every
  ready read at the deadline: the producer slot of the progress window
  (`sleepy_query_producer_at`), its inclusion (`continued_include_at`) and the payload projection
  (`confirmed_payload_projection_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- **A node honest at its proposal is the designated proposer of its slot.** -/
private theorem proposesAt_designated (hrun : Growing.GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k))
    (hP : tr.ProposesAt p k P) : p = proposer P.slot := by
  have hk0 := hrun.time_nonneg k
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, -⟩ := hP
  rcases blockCall_cases (hrun.upTo hk0).toLocalRun hp
      ((Trace.upTo_callAt_of_le _ le_rfl).mpr hcB) with
    hg | ⟨j, x, rfl, -, hPr, d', pay', -, hB, -⟩
  · have h := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
    simp only [Nat.add_zero] at h
    exact absurd h hpos
  rw [← hpp, hB]
  exact hPr.2.2.symm

/-- **The effective record after an update extends `P`** when the updater's `Σ.F` extends `P`, or
the record names a block of the update's frame extending `P`: the AC update leaves the FG store,
so the frame, unchanged, and the effective record is the frame block of the record, above `Σ.F`,
or `Σ.F`. -/
private theorem eff_record_of_update (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {k₀ m : Nat} (hy : y ∈ H (tr.time k₀))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ m ℓ)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) P (tr.state y (k₀ + 1)).fg.F ∨
      ∃ E ∈ ℓ.frame.tree, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocksAt H) P E) :
    Anc (tr.HonestBlocksAt H) P
      ((SA.lookup (Node.frame (tr.state y (k₀ + 1))) (tr.state y (k₀ + 1)).ac.latestConfirmed).getD
        (tr.state y (k₀ + 1)).fg.F) := by
  obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hu.1.2
  obtain rfl : c = .ac ℓ := by
    cases c with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨hfr, -, hfg, -⟩ := hrun.cutLaw y k₀ (.ac ℓ) ⟨hu.1.1, hc⟩ hy
  have hpost : tr.state y (k₀ + 1) = tr.post k₀ := by
    rw [Trace.state, ite_eq_left ⟨hu.1.1, by rw [hc]; exact Option.some_ne_none _⟩]
  have hframe : Node.frame (tr.state y (k₀ + 1)) = ℓ.frame := by
    rw [frame_of_projAC_at hrun hy hu.1, hpost]
    unfold Node.frame
    rw [hfg]
  have hFeq : (tr.state y (k₀ + 1)).fg.F = ℓ.frame.F := by
    rw [hframe.symm]
    rfl
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  rw [hframe]
  cases hl : SA.lookup ℓ.frame (tr.state y (k₀ + 1)).ac.latestConfirmed with
  | none =>
    simp only [Option.getD_none]
    rcases h with h | ⟨E, hE, hEr, -⟩
    · exact h
    · exact absurd ⟨E, hE, hEr⟩ (SA.lookup_eq_none hl)
  | some R =>
    simp only [Option.getD_some]
    obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
    rcases h with h | ⟨E, hE, hEr, hPE⟩
    · rw [hFeq] at h
      exact h.trans ((hΦ.rooted.2 R hR).mono hHB)
    · rwa [hΦ.coherent.1 hR hE (hRr.trans hEr.symm)]

/-- **Finite inclusion after a hand-over.** Through `b ≥ T`, a proposal of a slot `p` with
`t_p ≥ t_{r+k+1}` and `t_p ≥ t₁ + 8Δ`, released at `τ = t_p` by a proposer ready at `τ` and honest
through its hold, is in the confirmed read of every node ready at `t ∈ [τ + 6Δ, b]`, after all
events at `t`. Every honest update of slot `p` returns `P`, not vetoed: in the healthy prefix for
`p ≤ σ` (`operational_update_selection_at`), by the seeded sleepy argument otherwise
(`seeded_adopt_result`); so `P` is a member of the healed family. The reader's update of the slot
`m = slot(t − 6Δ) ≥ p` adopts `P` (`update_adopts_of` at `m = p`; for `m > p`,
`update_adopts_extended_from` with S1 and S2 for the member `P`), the effective record only
extends to the read (`seeded_effective_record_mono_at`), and the read is the effective record
(`seeded_ready_read_record_at`). -/
theorem continued_include_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hcv : ChainConvictedBelow tr H) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    (hdt₁ : sp.ts (r + sp.k : Nat) ≤ t₁) {τ : Time}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Regimes.Growing.ReadyProposalAt tr H (Regimes.catchUp sp) τ (Regimes.Growing.hold sp) P)
    (ht₁ : t₁ + 8 * sp.Δ ≤ τ) (hrτ : sp.ts (r + sp.k + 1 : Nat) ≤ τ) {y : Fin sp.n} {t : Time}
    {j : Nat} (hmargin : τ + 6 * sp.Δ ≤ t) (htb : t ≤ b)
    (hy : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) (hj : Regimes.CutAfter tr j t) :
    Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j t) := by
  have hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b :=
    ⟨hrun, hnc, hseed, hsvc, hB, hinv, hcv, hTb, hdt₁, hseed.reset.elim fun _ h => h.1.stock⟩
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  obtain ⟨pp, kP, -, hph, hPa, hkP⟩ := hP
  set p := P.slot with hpdef
  have hτ : τ = sp.ts p := by rw [← hkP, hPa.2.2, sp.slotTime_eq]; rfl
  have hp : pp ∈ H (sp.ts p + sp.Δ) := by rw [← hτ]; exact hph
  have hpk : pp ∈ H (tr.time kP) :=
    hrun.antitone (by rw [hkP]; change τ ≤ τ + sp.Δ; linarith) hph
  have hrp : r + sp.k + 1 ≤ p := by
    have := (SA.ts_le_iff sp).1 (hτ ▸ hrτ)
    exact_mod_cast this
  have ht₁p : t₁ ≤ sp.ts p := by linarith
  have htp : sp.ts p + 6 * sp.Δ ≤ b := by linarith
  have hga : SA.gbar g + 20 * sp.Δ ≤ sp.ts p := hS.gbar_le (by omega)
  -- every honest update of slot `p` returns `P`, not vetoed
  have hadopt : ∀ z k₀ (ℓ : ACLabel (goldilocksNode sp ro)), z ∈ H (tr.time k₀) →
      SA.UpdateAt tr.projAC z k₀ p ℓ → tr.time k₀ ≤ b →
      SA.getConfirmation sp (tr.state z k₀).ac ℓ.frame p = some P ∧
        ¬ SA.conflictsWithLock sp (tr.state z k₀).ac.locks ℓ.frame (tr.time k₀) P := by
    intro z k₀ ℓ hz hu hk₀
    by_cases hpσ : p ≤ σ
    · obtain ⟨a, hpr, hr⟩ := hseed.reset
      have hdrain : Healing.drainTime sp a = sp.ts (r + sp.k : Nat) := by
        rw [Healing.drainTime_eq, hr, Healing.cleanLabel_eq]
        congr 2
        omega
      have hσT := hseed.timing.1
      have htσ : sp.ts p ≤ sp.ts σ := ts_le_ts hpσ
      obtain ⟨-, hconf, hnv, -⟩ := Healing.Growing.operational_update_selection_at hpr
        hseed.catchRun hp (proposesAt_designated hrun hpk hPa) hPa rfl
        (by rw [hdrain]; exact hdt₁.trans ht₁p) (by linarith) (by linarith) hz hu
      rw [projAC_state_at hrun hz] at hconf hnv
      exact ⟨hconf, hnv⟩
    · exact seeded_adopt_result hS (by omega) hp hPa rfl ht₁p hz hu hk₀
  -- `P` is a member of the healed family of label `p`
  have hPm : HealedOrigin tr H g r (r + sp.k - 1) P p b := by
    have hT : sp.ts (p + 1 : Nat) + 2 * sp.Δ = sp.ts p + 6 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hf := hB.late (p + 1) (sp.ts (p + 1 : Nat) + 2 * sp.Δ) (by omega) le_rfl
      (by rw [hT]; exact htp) (by linarith)
    rw [hT] at hf
    obtain ⟨x, hx, hw, hjx⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hf).ne'
    obtain ⟨kx, ℓx, hux⟩ := update_of_awake_joined_at hrun hx hw hjx
    have hkx : tr.time kx = sp.ts p + 6 * sp.Δ := hux.2.2.1
    have hxk : x ∈ H (tr.time kx) := hkx ▸ hx
    have hC := (hadopt x kx ℓx hxk hux (by rw [hkx]; exact htp)).1
    exact .of_origin (by omega) (originWithin_iff.2 ⟨x, kx, _, hxk, by rw [hkx]; exact htp,
      Or.inl ⟨ℓx, hux, by rw [projAC_state_at hrun hxk]; exact hC, rfl⟩⟩)
  -- the reader's latest update before `t`: of slot `m = slot(t − 6Δ) ≥ p`, at `u = t_m + 6Δ ≤ t`
  have ht0 : 0 ≤ t - 6 * sp.Δ := by linarith [ts_natCast_nonneg (sp := sp) p]
  set m := sp.slot (t - 6 * sp.Δ)
  have hms : p ≤ m := by
    have := (SA.ts_le_iff_le_slot sp ht0 (p : Int)).1 (by linarith)
    omega
  have hm₁ : sp.ts m ≤ t - 6 * sp.Δ := (SA.ts_le_iff_le_slot sp ht0 (m : Int)).2 le_rfl
  have hm₂ : t - 6 * sp.Δ < sp.ts m + 4 * sp.Δ := by
    by_contra hh
    have := (SA.ts_le_iff_le_slot sp ht0 ((m : Int) + 1)).1 (by
      simp only [SAParams.ts] at hh ⊢; linarith)
    omega
  set u := sp.ts m + 6 * sp.Δ with hu_def
  have hut : u ≤ t := by linarith
  have hpu : sp.ts p ≤ sp.ts m := ts_le_ts hms
  have hu0 : 0 ≤ u := by simp only [u, SAParams.ts]; positivity
  have hyu : y ∈ H u := hrun.antitone hut hy.1
  have hcu : Regimes.catchUp sp = 18 * sp.Δ := rfl
  obtain ⟨hJw, hJj⟩ : tr.awake y u ∧ tr.JoinedAt y u := by
    obtain ⟨hw, hj'⟩ := Compose.ready_implies_joined _ _ _ _ _ _ (hrun.upTo hu0) y hyu u
      (14 * sp.Δ - 1) hu0 (by linarith) fun v h₁ h₂ =>
        ⟨hy.2 v (le_trans (max_le_max le_rfl (by rw [hcu]; linarith)) h₁) (by linarith), h₂⟩
    exact ⟨hw.1, fun k hk hkt => hj' k ((RunTrace.upTo_restartAt tr).2 ⟨hkt, hk⟩) hkt⟩
  obtain ⟨k₁, ℓ₁, hupd⟩ := update_of_awake_joined_at hrun hyu hJw hJj
  have hk₁ : tr.time k₁ = u := hupd.2.2.1
  have hyk₁ : y ∈ H (tr.time k₁) := hk₁ ▸ hyu
  have hk₁b : tr.time k₁ ≤ b := by rw [hk₁]; linarith
  have ht₁u : t₁ ≤ tr.time k₁ := by rw [hk₁]; linarith
  have hcall₁ := hS.called hyk₁ (hdt₁.trans ht₁u) le_rfl
  -- after the update, the effective record extends `P`
  have hPeff := eff_record_of_update hrun hnc hyk₁ hupd (P := P) (by
    rcases hms.lt_or_eq with hlt | heq
    · have hFc := (hinv.caches y k₁ (tr.time k₁) ht₁u (fun _ h => hrun.time_mono h.le) hk₁b
        hyk₁ hcall₁).1
      refine update_adopts_extended_from hrun hnc hS.sync hB hyk₁ hupd hk₁b (by omega)
        (by linarith [hS.gbar_le (show r ≤ m by omega)])
        (by linarith [hS.gbar_le (show r ≤ m by omega)])
        (OnHealedChain.compatible hrun hnc hinv.origins_compatible hFc hPm).symm
        (fun x i e hv hes => hinv.vote_extends P p hPm x i e hv ?_ (by omega))
        (fun C hC => seeded_result_not_vetoed hS hyk₁ hupd ht₁u hk₁b (l := m)
          (.of_origin (by omega) (originWithin_iff.2 ⟨y, k₁, _, hyk₁, hk₁b,
            Or.inl ⟨ℓ₁, hupd, by rw [projAC_state_at hrun hyk₁]; exact hC, rfl⟩⟩))
          (SA.deepest_mem hC).1.1) hS.stock
      obtain ⟨hx, ℓx, hc, he⟩ := hVoteAt_iff.1 hv
      have h := (cast_head_fcRoot_at hrun hnc hx ⟨hc, he⟩).2
      rw [hes] at h
      linarith
    · rw [← heq] at hupd
      obtain ⟨hC, hv⟩ := hadopt y k₁ ℓ₁ hyk₁ hupd hk₁b
      exact Or.inr (update_adopts_of hrun hnc hyk₁ hupd hC hv))
  -- the effective record only extends from the update to `j`, and the read is it
  have hj₁j : k₁ + 1 ≤ j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ k₁ by omega)
    linarith [hj.2]
  have hrp₁ : Regimes.ReadPoint tr (k₁ + 1) (tr.time k₁) :=
    ⟨fun k hk => hrun.time_mono (by omega), hrun.time_mono (Nat.le_succ k₁)⟩
  have hrp : Regimes.ReadPoint tr j t := ⟨hj.1, hj.2.le⟩
  have hmono := seeded_effective_record_mono_at hrun hnc hinv ht₁u
    (show sp.ts (r + sp.k - 1 + 1 : Nat) ≤ tr.time k₁ by
      rw [show r + sp.k - 1 + 1 = r + sp.k by omega]; exact hdt₁.trans ht₁u)
    hrp₁ hrp hj₁j (by rw [hk₁]; exact hut) le_rfl htb hyk₁ hy.1
    (let ⟨c, hc, h⟩ := hcall₁; ⟨c, by omega, h⟩)
  rw [seeded_ready_read_record_at hrun hnc hseed hsvc hB hinv hrp hdt₁ (by linarith) htb hy]
  exact hPeff.trans hmono

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The query's hand-over regime from `System.Handover`**: a run handing over at `T` at or
after the heal point, with progress from readiness and a query at or after the heal point, is in
the hand-over disjunct of `ConfirmedQueryAt.regime` (the regime conjuncts of `Handover`, without
its conviction bound). -/
theorem handover_query_regime {run : (Sys (goldilocks S) V).Run} {cap : Capability}
    {index : (K S A).Idx} {gst T query : Time}
    (h : (Sys (goldilocks S) V).Handover (K S A) gst T run)
    (hT : (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ T)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
      ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run)
    (hq : (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ query) :
    ∃ T, ((Sys (goldilocks S) V).log run).PSync ((Sys (goldilocks S) V).pt run) gst ∧
      ((Sys (goldilocks S) V).pt run).HealthyOn (K S A).params.β gst T ∧
      ((Sys (goldilocks S) V).pt run).env.ΔFG ≤
        ((K S A).params.fgDelay : Time) * ((Sys (goldilocks S) V).pt run).env.ΔAC ∧
      ((Sys (goldilocks S) V).pt run).SleepyOn (K S A).params.θ
        ((Sys (goldilocks S) V).cDur (K S A) run) ((Sys (goldilocks S) V).aheadDur (K S A) run) T
        ((Sys (goldilocks S) V).pt run).horizon ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ T ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ query :=
  ⟨T, h.1, h.2.1, h.2.2.1, h.2.2.2.1, hT, hp, hq⟩

/-- **Proposal liveness after a hand-over**, for a nonfinal query at or after `t₁` and `t_{r+k}`,
with progress from the healthy readiness `ready ≤ query`: some proposal released after the query
by a key ready then is in every ready read at the deadline. The proposal of the progress window's
slot (`sleepy_query_producer_at`) is after the query, so of a slot `≥ r + k + 1`, and included
at the deadline (`continued_include_at`); its payload projection is the engine obligation. -/
theorem continued_proposal_live_at (Q : ConfirmedQueryAt S A V) {ΔF T : Time} {r σ : Nat}
    (hcv : Compose.Growing.ChainConvictedBelow Q.trace Q.keys)
    (hseed : Compose.Growing.HandoverSeed Q.trace Q.keys (runProposer ⟨S, stock⟩ Q.run.2 Q.hn)
      (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔF T r σ) (hTb : T ≤ Q.deadline) {t₁ : Time}
    (hsvc : Healing.Growing.ResetService Q.trace Q.keys Q.gst ΔF Q.deadline)
    (hB : Compose.Growing.SleepyBoundsFrom Q.trace Q.keys r Q.deadline)
    (hinv : Compose.Growing.SeededInvariant Q.trace Q.keys Q.gst r (r + Q.params.k - 1) t₁
      Q.deadline)
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) Q.run.2.horizon Q.run)
    (hready : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run ≤ Q.query)
    (hdt₁ : Q.params.ts (r + Q.params.k : Nat) ≤ t₁) (ht₁ : t₁ + 8 * Q.params.Δ ≤ Q.query) :
    ∃ τ k h, Q.query < τ ∧ Q.run.2.point.Ready Q.duration (Q.run.2.key k) τ ∧
      HonestProposal Q.run.2 τ k h ∧ InBy Q.run.2 Q.duration .confirmed h Q.deadline := by
  have hrq : Q.params.ts (r + Q.params.k : Nat) ≤ Q.query := by
    linarith [Q.params.toParams.hΔ]
  have h0 : 0 ≤ Q.query := (Compose.Growing.ts_natCast_nonneg _).trans hrq
  obtain ⟨P, hm, hh⟩ := sleepy_query_producer_at S A V Q hprogress (max_le hready h0)
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have hd := confirmed_duration_supply_at S A V Q
  -- the proposal's slot time is after `t_{r+k}`, so it is `≥ t_{r+k+1}`
  have hslot : Q.params.ts (r + Q.params.k + 1 : Nat) ≤ Q.trace.time P.cut := by
    have hpt := P.proposal.2.2
    rw [Q.params.slotTime_eq] at hpt
    have hlt : Q.params.ts (r + Q.params.k : Nat) < Q.trace.time P.cut := hrq.trans_lt P.fresh
    rw [hpt] at hlt ⊢
    have := (SA.ts_lt_iff Q.params).1 hlt
    exact (SA.ts_le_iff Q.params).2 (by push_cast at this ⊢; omega)
  refine confirmed_payload_projection_at S A V Q h0 P fun y j hy hj => ?_
  exact Compose.Growing.continued_include_at hrun hnc hcv hseed hTb hsvc hB hinv hdt₁
    ⟨P.block.proposer, P.cut, confirmed_ready_mono_at S A V Q hd P.ready, hh, P.proposal, rfl⟩
    (ht₁.trans P.fresh.le) hslot hm le_rfl (confirmed_ready_mono_at S A V Q hd hy) hj

end Consensus.Goldilocks.Obligations.Growing

end
