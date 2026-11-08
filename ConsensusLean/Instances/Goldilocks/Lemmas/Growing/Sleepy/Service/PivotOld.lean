module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the proposal walk passes the old origins

The σ-copies of the first half of `Compose/Service/Pivot`: the old origins of slot `s`
(`OldOrigin`, by nodes honest at their event), the relay of honest heads to the slot's proposer,
and the walk's children towards an old origin. The proposer is honest at its proposal cut
(`t_s`); the voters, writers and relaying nodes are honest at their own cuts.

The counts in `proposal_best_toward_old_at` are at the proposer's cut, `d = t_s`: the pool's
validators honest at `d` cast their votes (Lemma G, `pool_vote_at`) and have one vote in it, the
others are in `(H d)ᶜ`; the honest slot-`(s−1)` batch is `VotersAt (s − 1) d`, which outnumbers
`(H d)ᶜ` (`faults_lt_voters`, `d = t_{s−1} + 4Δ`); an optimistic origin of label `s − 1` has
`3n/4` counted seats against `2 f_d < n`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The old origins of slot `s`**: the regular origins of labels at most `s − 2` and the
optimistic origins of labels at most `s − 1`, each by a node honest at its event. -/
def OldOrigin (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (s : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ x k m CV, x ∈ H (tr.time k) ∧ ((SA.ResultAt tr.projAC x k m O CV ∧ m + 2 ≤ s) ∨
    (SA.OptimisticLockAt tr.projAC x k m O CV ∧ m + 1 ≤ s))

theorem oldOrigin_iff {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))} : OldOrigin tr H s O ↔
    ∃ x k m CV, x ∈ H (tr.time k) ∧ ((SA.ResultAt tr.projAC x k m O CV ∧ m + 2 ≤ s) ∨
      (SA.OptimisticLockAt tr.projAC x k m O CV ∧ m + 1 ≤ s)) := Iff.rfl

/-- Old origins are within every horizon containing the slot's proposal time. -/
theorem OldOrigin.within (hrun : Growing.GoldilocksRun proposer dg H tr)
    {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time}
    (h : OldOrigin tr H s O) (hb : sp.ts s ≤ b) :
    ∃ m < s, OriginWithin tr H O m b := by
  obtain ⟨x, k, m, CV, hx, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := oldOrigin_iff.1 h
  · refine ⟨m, by omega, originWithin_iff.2 ⟨x, k, CV, hx, ?_, Or.inl hR⟩⟩
    obtain ⟨ℓ, hu, _⟩ := hR
    have ht : tr.time k = sp.ts m + 6 * sp.Δ := hu.2.2.1
    have hs : (m : Int) + 2 ≤ s := by exact_mod_cast hm
    have hΔ := sp.toParams.hΔ
    simp only [SAParams.ts] at hb ht
    linarith only [hb, ht, sp.toParams.hΔ, mul_le_mul_of_nonneg_left hs sp.toParams.hΔ.le]
  · refine ⟨m, by omega, originWithin_iff.2 ⟨x, k, CV, hx, ?_, Or.inr hO⟩⟩
    obtain ⟨ℓ, A, _, hs, _⟩ := hO
    change sp.slot (tr.time k) = m at hs
    have ht : tr.time k < sp.ts s := by
      by_contra ht
      have hle := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) (s : Int)).1 (le_of_not_gt ht)
      rw [hs] at hle
      omega
    exact ht.le.trans hb

/-- A block held while honest with the genesis root is below every block held while honest. -/
theorem honestAt_genesis_root_anc (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hU : Coherent (tr.HonestBlocksAt H)) {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hr : B.root = sp.genesisRoot) (hC : C ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) B C := by
  rw [honestAt_eq_genesis hrun hU hB hr]
  exact (honestAt_genesis_anc hrun hC).2

/-- The proposer's restarts up to its proposal are at or before `t_{s−1}` (lifted at the
proposal's time). -/
theorem proposal_call_restarts_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {i : Nat} (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay)) :
    ∀ c ≤ i, tr.projAC.RestartAt p c →
      tr.projAC.time c ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := by
  have hm := hrun.time_mono
  have h := proposal_call_restarts (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hp
    (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hcall
    (by rw [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl]; exact hd)
  intro c hci hrc
  have := h c hci (by rw [RunTrace.upTo_projAC]; exact (ac_restartAt_upTo _).mpr ⟨hm hci, hrc⟩)
  exact this

/-- **A block accepted before `t_{s−1} + 2Δ` by a node honest then reaches the proposer** of slot
`s` (the finite service; the proposer awake since its last restart at or before `t_{s−1}`): when
the proposer's `Σ.F` is below it, it is in the proposal's frame, accepted before `t_{s−1} + 3Δ`. -/
theorem proposer_relay_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b)
    {x : Fin sp.n} {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, x ∈ H (tr.time kx) ∧ tr.projAC.AcceptAt x kx B ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocksAt H) ℓp.frame.F B) :
    B ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((s : Int) - 1) + 3 * sp.Δ) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  rcases hacc with hg | ⟨kx, hx, hacc, hkxt⟩
  · refine ⟨?_, Or.inl hg⟩
    have h2 := (honestAt_genesis_anc hrun (hΦU hΦ.rooted.1)).2
    rw [← honestAt_eq_genesis hrun hU hB hg] at h2
    rw [← Anc.antisymm hU hFB h2]
    exact hΦ.rooted.1
  have hsi : sp.slot (tr.time i) = s := by
    rw [hti]; simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hts : sp.ts (s : Int) = sp.ts ((s : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hrs := proposal_call_restarts_at hrun hnc hp hc hcall hd
  rw [hsi] at hrs
  have hdl : ∀ c ≤ i, tr.projAC.deadline p c (tr.projAC.time kx) ≤
      sp.ts ((s : Int) - 1) + 3 * sp.Δ := fun c hc' => by
    have h1 := ac_deadline_le_of_restarts (T := tr.projAC)
      (fun k hk hrk => hrs k (hk.trans hc') hrk) (tr.projAC.time kx)
    have h2 := max_le hkxt.le (show sp.ts ((s : Int) - 1) ≤ sp.ts ((s : Int) - 1) + 2 * sp.Δ from
      le_add_of_nonneg_right (mul_nonneg zero_le_two hΔ.le))
    linarith only [h1, h2]
  have hdi : tr.projAC.deadline p i (tr.projAC.time kx) ≤ tr.time i := by
    have := hdl i le_rfl
    linarith only [this, hti, hts, hΔ]
  obtain ⟨k', hk'i, hAp, hk't⟩ := hsync.acRelay x kx B hx hacc (hrun.time_nonneg kx)
    p i ℓp hp hc (hdi.trans hb) hdi hFB
  exact ⟨mem_tree_of_acceptAt_at hrun hnc hp hAp hk'i hc hFB,
    Or.inr ⟨k', hAp, lt_of_lt_of_le hk't (hdl k' hk'i)⟩⟩

/-- **The head of a vote of a slot before `s`, cast by a node honest then, reaches the proposer**
of slot `s`: its voter accepted it (or it is genesis) by `t_{s−1} + Δ`, and
`proposer_relay_at`. -/
theorem proposer_accepts_head_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b)
    {x : Fin sp.n} {j : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x j e) (hes : e.msg.slot + 1 ≤ s)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocksAt H)
    (hHdr : Hd.root = e.msg.head) (hFHd : Anc (tr.HonestBlocksAt H) ℓp.frame.F Hd) :
    Hd ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p Hd (sp.ts ((s : Int) - 1) + 3 * sp.Δ) ∧
      Hd.slot ≤ e.msg.slot := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hjt⟩ := cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩
  have hHdeq : Hd' = Hd :=
    hU.1 ((frameIn_at hrun hnc hx hcx).2 hHd't) hHd (hHd'r.trans hHdr.symm)
  rw [hHdeq] at hHd't
  have hj0 : tr.projAC.time j = tr.time j := rfl
  have hjt' : tr.projAC.time j ≤ sp.ts ((s : Int) - 1) + sp.Δ := by
    have : sp.ts (e.msg.slot : Int) ≤ sp.ts ((s : Int) - 1) := by
      simp only [SAParams.ts]
      exact mul_le_mul_of_nonneg_left (show (e.msg.slot : Int) ≤ (s : Int) - 1 by omega)
        (mul_nonneg zero_le_four hΔ.le)
    linarith only [hjt, this, hj0]
  have hslot : Hd.slot ≤ e.msg.slot := by
    rw [(castAt_spec_at hrun hnc hx ⟨hcx, hex⟩).2.1]
    exact frame_slot_le_at hrun hnc hx hcx Hd hHd't
  have hacc : Hd.root = sp.genesisRoot ∨ ∃ kx, x ∈ H (tr.time kx) ∧ tr.projAC.AcceptAt x kx Hd ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ := by
    rcases frame_anc_accepted_at hrun hnc hx hcx hHd't .refl with hg | ⟨kx, hkx, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨kx, hrun.antitone (hrun.time_mono hkx) hx, hacc,
        lt_of_le_of_lt (hrun.time_mono hkx) (by linarith only [hjt', hΔ, hj0])⟩
  obtain ⟨h1, h2⟩ := proposer_relay_at hrun hnc hsync hp hc hcall hd hti hb hHd hacc hFHd
  exact ⟨h1, h2, hslot⟩

/-- **The proposer holds every old origin, or it is below its `Σ.F`**: an old origin has a
supporting vote of a slot before `s` by a node honest at it (`honest_supporter_at`), whose head
reaches the proposer when `Σ.F` is below the origin (`proposer_accepts_head_at`); otherwise
`Σ.F`, on the origin chain, is compatible with it (S1) and above it. -/
theorem proposal_holds_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {s i : Nat}
    (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocksAt H) O ℓp.frame.F := by
  intro O hO
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨m, hm, hOm⟩ := hO.within hrun (hti ▸ hb)
  obtain ⟨x, j, e, hv, _, hes, Hd, hHd, hHdr, hOHd⟩ := honest_supporter_at hrun hnc
    (hsync.toFrom hrun) hB (Nat.zero_le _) (ts_natCast_nonneg _) hOm
  have hOU : O ∈ tr.HonestBlocksAt H := by
    by_cases h : O = Hd
    · exact h ▸ hHd
    · exact (Anc.mem hOHd h).1
  have hFc : OnOriginChainWithin tr H ℓp.frame.F b := by
    rw [frame_of_projAC_at hrun hp hc]
    exact (hinv.caches_at_cut hrun ((hrun.time_nonneg i).trans hb) hp
      (fun k hk => (hrun.time_mono hk.le).trans hb)).1
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible
      (hΦU hΦ.rooted.1) hOU hFc
      (onOriginChainWithin_iff.2 (Or.inr ⟨O, m, hOm, .refl⟩)) with hFO | hOF
  · left
    have hHdt := (proposer_accepts_head_at hrun hnc hsync hp hc hcall hd hti hb hv
      (by omega) hHd hHdr (hFO.trans hOHd)).1
    exact mem_between hU hΦ hΦU hΦ.rooted.1 hHdt hFO hOHd
  · exact Or.inr hOF

/-- **The children towards an old origin win the proposal walk**: at every block `X` (of the full
viable tree, with the proposal's slot-`(s−1)` pool view `pay`), a viable child `Cx` of `X` below an
old origin held by the proposer is the best eligible child. Counted at the proposer's cut,
`d = t_s`: a validator honest at `d` has one vote in the pool (`pool_vote_at`,
`one_vote_per_slot_at`), the others are in `(H d)ᶜ`. For an origin of label below `s − 1`, every
slot-`(s−1)` vote by a node honest at it extends it (S2), is relayed to the proposer
(`sync_before_forward_at`) and resolved there (`proposer_accepts_head_at`), so the slot-`(s−1)`
voters still honest at `d` support it and outnumber `(H d)ᶜ` (`faults_lt_voters`). For an
optimistic origin of label `s − 1`, its at least `3n/4` counted votes are relayed likewise, so
each of its seats supports it or equivocates, against `2 f_d < n` (`SA.isBest_of_cover`). -/
theorem proposal_best_toward_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {s i : Nat}
    (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree → ∀ X Cx : SA.Blk sp.n (List (FG.Att sp.n)),
      Cx ∈ ℓp.frame.viableTree ℓp.frame.tree → Cx.parent = some X.root → ℓp.frame.Anc Cx O →
      SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B}
        Cx := by
  intro O hO hOt X Cx hCx hpar hCxO
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := hB.two _ (hrun.time_nonneg i) hb
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := by
    obtain ⟨x, k, m, CV, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hO
    · exact ⟨s - 1, by omega⟩
    · exact ⟨s - 1, by omega⟩
  have hσ : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s' + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hii : tr.projAC.time i = tr.time i := rfl
  rw [hσ]
  set A := tr.projAC.state p i with hA
  -- the payload is the proposer's slot-`(s−1)` pool
  have hpay : pay = SA.voteViewList A ℓp.frame (s' : Int) ⊤ := by
    have h := hd
    unfold SA.acProposal at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2, hsi, hσ]
  have hvotes : ∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s' ∧ A.voteStamp v < ⊤ := by
    intro v
    rw [hpay]
    simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
  have hsupv : ∀ v, v ∈ (SA.View.ofLists pay).support ↔
      (v ∈ A.pool s' ∧ A.voteStamp v < ⊤) ∧ SA.resolutionTime A ℓp.frame v < ⊤ := by
    intro v
    rw [hpay]
    simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
    tauto
  have hsub : (SA.View.ofLists pay).support ⊆ (SA.View.ofLists pay).votes := fun v hv =>
    (hvotes v).2 ((hsupv v).1 hv).1
  have hvotes' : ∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s' := fun v =>
    ⟨fun h => ((hvotes v).1 h).1, fun h => (hvotes v).2 ⟨h, pool_stamp_lt_top_at hrun hnc hp h⟩⟩
  -- a validator honest at the proposal has at most one vote in the pool
  have hnoeq : ∀ w ∈ H (tr.time i), w ∉ SA.equivocators {v | v ∈ A.pool s'} := by
    rintro w hw ⟨v₁, hv₁, v₂, hv₂, hne, rfl, h2⟩
    obtain ⟨j₁, -, e₁, hve₁, rfl⟩ := pool_vote_at hrun hnc hp hv₁ hw
    obtain ⟨j₂, -, e₂, hve₂, rfl⟩ := pool_vote_at hrun hnc hp hv₂ (h2 ▸ hw)
    have hs₁ := state_pool_slot_at hrun hnc hp s' _ hv₁
    have hs₂ := state_pool_slot_at hrun hnc hp s' _ hv₂
    rw [h2] at hve₂
    obtain ⟨-, rfl⟩ := one_vote_per_slot_at hrun hnc hve₁ hve₂ (hs₁.trans hs₂.symm)
    exact hne rfl
  have hequiv : SA.equivocators (SA.View.ofLists pay).votes ⊆ (H (tr.time i))ᶜ := by
    rintro w ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ hw
    exact hnoeq w hw ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩
  -- the proposer's restarts, and the relay window
  have hrs := proposal_call_restarts_at hrun hnc hp hc hcall hd
  rw [hsi, hσ] at hrs
  -- a vote sent or admitted in `[t_{s−1}, t_{s−1} + 2Δ)` by a node honest then is in the pool
  have hfwd : ∀ x kx v, x ∈ H (tr.time kx) → tr.projAC.SendOrAdmit x kx v → v.slot = s' →
      sp.ts (s' : Int) ≤ tr.projAC.time kx → tr.projAC.time kx < sp.ts (s' : Int) + 2 * sp.Δ →
      v ∈ A.pool s' ∨ v.val ∈ SA.equivocators {w | w ∈ A.pool s'} := by
    intro x kx v hx hsend hvs hk1 hk2
    have hk0 : tr.projAC.time kx = tr.time kx := rfl
    have h := sync_before_forward_at hrun hnc hsync hx hsend
      (by rw [hti, hts] at hb; linarith only [hk2, hb, hΔ, hk0]) hp hc
      (fun k' hk' hrk' => (hrs k' hk' hrk').trans (hk0 ▸ hk1))
      (by rw [hti, hts]; linarith only [hk2, hΔ, hk0])
      (fun t ht1 ht2 => by
        have := SA.slot_of_mem sp s' ((hk0 ▸ hk1).trans ht1)
          (by rw [hts]; linarith only [ht2, hk2, hΔ, hk0])
        omega)
    rwa [hvs] at h
  -- a vote of the pool whose head, of a slot at most its own, the proposer accepted is resolved
  have hres : ∀ v ∈ A.pool s', ∀ Hv ∈ ℓp.frame.tree, Hv.root = v.head → Hv.slot ≤ v.slot →
      SA.AcceptedBefore tr.projAC p Hv (sp.ts (s' : Int) + 3 * sp.Δ) →
      v ∈ (SA.View.ofLists pay).support := by
    intro v hv Hv hHv hHvr hHvs hacc
    refine (hsupv v).2 ⟨⟨hv, pool_stamp_lt_top_at hrun hnc hp hv⟩, ?_⟩
    have hbs := blockStamp_lt_of_acceptedBefore_at hrun hnc hp hc hHv hacc
      (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk) (lt_add_of_pos_right _ (mul_pos three_pos hΔ)))
      (by
        rw [hti, hts]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num : (3 : Time) ≤ 4) hΔ.le))
    unfold SA.resolutionTime
    split
    · rename_i hl
      exact absurd ⟨Hv, hHv, hHvr⟩ (SA.lookup_eq_none hl)
    · rename_i Hd' hl
      obtain ⟨hHd', hr'⟩ := SA.lookup_eq_some hl
      obtain rfl : Hd' = Hv := hΦ.coherent.1 hHd' hHv (hr'.trans hHvr.symm)
      split_ifs with hlt
      · omega
      · rw [← hHvr]
        exact max_lt (pool_stamp_lt_top_at hrun hnc hp hv)
          (lt_trans hbs (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)))
  have hFO : Anc (tr.HonestBlocksAt H) ℓp.frame.F O := Anc.mono hΦU (hΦ.rooted.2 O hOt)
  have hcase : (∃ m < s', OriginWithin tr H O m b) ∨
      ∃ x k CV, x ∈ H (tr.time k) ∧ SA.OptimisticLockAt tr.projAC x k s' O CV := by
    obtain ⟨x, k, m, CV, hx, ⟨hR, hm⟩ | ⟨hOp, hm⟩⟩ := hO
    · refine Or.inl ⟨m, by omega, originWithin_iff.2 ⟨x, k, CV, hx, ?_, Or.inl hR⟩⟩
      obtain ⟨ℓ, hu, _⟩ := hR
      have ht : tr.time k = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hm' : (m : Int) + 2 ≤ s' + 1 := by exact_mod_cast hm
      rw [hts] at hti
      simp only [SAParams.ts] at ht hti
      linarith only [ht, hti, hb, hΔ, mul_le_mul_of_nonneg_left hm' (SA.four_delta_pos sp).le]
    rcases Nat.lt_or_ge m s' with hm' | hm'
    · refine Or.inl ⟨m, hm', originWithin_iff.2 ⟨x, k, CV, hx, ?_, Or.inr hOp⟩⟩
      obtain ⟨ℓ, A, _, hs, _⟩ := hOp
      change sp.slot (tr.time k) = m at hs
      have ht : tr.time k < sp.ts (s' + 1 : Nat) := by
        by_contra ht
        have hh := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) ((s' + 1 : Nat) : Int)).1
          (le_of_not_gt ht)
        rw [hs] at hh
        omega
      exact ht.le.trans (hti ▸ hb)
    obtain rfl : s' = m := by omega
    exact Or.inr ⟨x, k, CV, hx, hOp⟩
  rcases hcase with ⟨m, hml, hOm⟩ | ⟨x, k, CV, hx, hOp⟩
  · -- an origin of label below `s − 1`: every honest slot-`(s−1)` vote extends it
    refine SA.isBest_of_majority hΦ hsub (fun B hB => hB.1)
      (SX := VotersAt tr H s' (tr.time i)) (VX := VotersAt tr H s' (tr.time i) ∪ (H (tr.time i))ᶜ)
      ?_ ?_ ?_ hCx hpar hCxO
    · rintro w hwS
      obtain ⟨hw, j, e, hv, hes⟩ := votersAt_iff.1 hwS
      obtain ⟨hwj, ℓw, hcw, hew⟩ := hVoteAt_iff.1 hv
      have hj0 : tr.projAC.time j = tr.time j := rfl
      have hjt := (cast_head_fcRoot_at hrun hnc hwj ⟨hcw, hew⟩).2
      have hjb : tr.time j ≤ b := by
        rw [hes] at hjt
        rw [hti, hts] at hb
        linarith only [hjt, hb, hΔ]
      obtain ⟨Hd, hHd, hHdr, hOHd⟩ := hinv.vote_extends O m hOm w j e hv hjb (by omega)
      obtain ⟨hHdt, hacc, hHds⟩ := proposer_accepts_head_at hrun hnc hsync hp hc hcall hd hti hb
        hv (by omega) hHd hHdr (hFO.trans hOHd)
      have hvw : e.msg.val = w := (castAt_spec_at hrun hnc hwj ⟨hcw, hew⟩).1
      have hj1 : sp.ts (s' : Int) ≤ tr.projAC.time j := by
        rw [← hes, (castAt_spec_at hrun hnc hwj ⟨hcw, hew⟩).2.1]
        exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 le_rfl
      have hvp : e.msg ∈ A.pool s' := by
        rcases hfwd w j e.msg hwj ⟨ℓw, hcw, Or.inl ⟨e, hew, rfl⟩⟩ hes hj1
          (by rw [hes] at hjt; linarith only [hjt, hΔ, hj0]) with h | h
        · exact h
        · exact absurd (hvw ▸ h) (hnoeq w hw)
      refine ⟨fun h => hnoeq w hw (by
          obtain ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ := h
          exact ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩),
        e.msg, hres e.msg hvp Hd hHdt hHdr hHds (by rw [← hσ]; exact hacc), hvw, by rw [hes],
        Hd, hHdt, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHd hHdt⟩
    · rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H (tr.time i)
      · obtain ⟨j, -, e, hve, rfl⟩ := pool_vote_at hrun hnc hp ((hvotes' v).1 hv) hw
        exact Or.inl (votersAt_iff.2
          ⟨hw, j, e, hve, state_pool_slot_at hrun hnc hp s' _ ((hvotes' _).1 hv)⟩)
      · exact Or.inr hw
    · have hcount := faults_lt_voters hrun hnc hB (s := s') (d := tr.time i) (Nat.zero_le _)
        (by rw [hti, hts]; linarith only [hΔ]) hb (by rw [hti, hts]; linarith only [hΔ])
      have := Set.ncard_union_le (VotersAt tr H s' (tr.time i)) (H (tr.time i))ᶜ
      omega
  · -- an optimistic origin of label `s − 1`: its counted votes
    have hW := optimistic_writer_votes_at hrun hnc hx hOp
    obtain ⟨ℓx, Ax, hpt, hslx, hsel, rfl⟩ := hOp
    have hsel' := hsel
    unfold SA.optimisticSelect at hsel'
    dsimp only at hsel'
    split_ifs at hsel'
    have h34 := (SA.deepest_mem hsel').1.2.1
    rw [hslx] at h34
    have hΦxU := (frameIn_at hrun hnc hx hpt.1).2
    refine SA.isBest_of_cover hΦ hsub (fun B hB => hB.1) (SX := SA.optimisticVoters sp Ax ℓx.frame
      s' O) ?_ ?_ hCx hpar hCxO
    · rintro u ⟨v, hvA, rfl, R, hR, hRr, hOR⟩
      obtain ⟨hvs, ⟨kx, hxkx, hsend, hk1, hk2⟩, Hv, hHv, hHvr, hOHv, hacc⟩ :=
        hW v ⟨hvA, R, hR, hRr, hOR⟩
      have hRHv : R = Hv := hU.1 (hΦxU hR) hHv (hRr.trans hHvr.symm)
      rw [← hRHv] at hHv hOHv hacc
      by_cases heq : v.val ∈ SA.equivocators (SA.View.ofLists pay).votes
      · exact Or.inr heq
      left
      rcases hfwd x kx v hxkx hsend hvs hk1 hk2 with hvp | ⟨a₁, ha₁, a₂, ha₂, hne, h1, h2⟩
      swap
      · exact absurd ⟨a₁, (hvotes' a₁).2 ha₁, a₂, (hvotes' a₂).2 ha₂, hne, h1, h2⟩ heq
      obtain ⟨hRt, hacc'⟩ := proposer_relay_at hrun hnc hsync hp hc hcall hd hti hb hHv
        (by rw [hσ]; exact hacc)
        (hFO.trans hOHv)
      have hRs : R.slot ≤ v.slot := by
        rw [hvs, ← hslx]
        exact frame_slot_le_at hrun hnc hx hpt.1 R hR
      exact ⟨heq, v, hres v hvp R hRt hRr hRs (by rw [← hσ]; exact hacc'), rfl,
        by rw [hvs], R, hRt, hRr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHv hRt⟩
    · have hle : (SA.voters (SA.View.ofLists pay).votes \ SA.optimisticVoters sp Ax ℓx.frame s'
          O).ncard + (SA.optimisticVoters sp Ax ℓx.frame s' O).ncard ≤ sp.n := by
        rw [← Set.ncard_union_eq Set.disjoint_sdiff_left]
        exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp)
      have := Set.ncard_le_ncard hequiv (Set.toFinite _)
      omega

end Consensus.Goldilocks.Compose.Growing

end
