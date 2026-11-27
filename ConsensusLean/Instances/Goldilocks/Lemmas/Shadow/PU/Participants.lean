module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.CommitteeRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.SideCount

public section

/-! # Shadow P-U: honest participants

A copy of stock `Compose/Sleepy/Compare` (`honest_participants_window_before`, and the public
`vote_of_awake_joined` and `awake_participant_early`) over the shadow run law `GoldilocksRun'`,
through the shadow AC projection `Compose.goldilocks_ac_projection_from'`.
The statement is static; a growing consumer applies it to `hrun.upTo`. Private copies: the AC
helpers of `Compare` (`acOnTick_votes`, `update_restarts`, ...),
`awake_participant_window_before`, and the joined-at-a-call part of `joined_projection_from` with
`group_not_restart`, `restartCall_group`, `exec_restart`, `lastBefore` and `restartTime_eq`. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-! ### AC helpers (copies of the private ones of `Compare`) -/

section ACHelpers

variable {FGP : Type} {ro' : ReplayOrder sp FGP} {H' : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {gtr : AC.GTrace sp FGP ro'}

private theorem acOnTick_votes (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    {t : Time} (hj : AC.joined sp A t) (ht : t = sp.ts (sp.slot t) + sp.Δ)
    (hm : A.mayVote (sp.slot t) = true) :
    A.votedSlot = sp.slot t ∨ ∃ e ∈ (AC.acOnTick sp self A Φ t).2, e.msg.slot = sp.slot t := by
  unfold AC.acOnTick
  simp only [hj, not_true_eq_false, ↓reduceIte, ← ht]
  unfold AC.tryVote
  simp only [hm, ↓reduceIte]
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact Or.inl h
    · exact absurd ht h.ne'
  · exact absurd ht h₂.1.ne
  all_goals exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩

private theorem add_mul_delta_le {x a b : Time} (h : a ≤ b) : x + a * sp.Δ ≤ x + b * sp.Δ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right h sp.toParams.hΔ.le)

private theorem add_mul_delta_lt {x a b : Time} (h : a < b) : x + a * sp.Δ < x + b * sp.Δ :=
  add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right h sp.toParams.hΔ)

private theorem add_delta_add_delta (x : Time) : x + sp.Δ + sp.Δ = x + 2 * sp.Δ := by
  rw [add_assoc, ← two_mul]

private theorem ts_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  simp only [ACParams.ts]
  exact mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (Int.natCast_nonneg s)

private theorem update_restarts {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro') H' U gtr ini)
    {Y : Fin sp.n} (hY : Y ∈ H') {c s : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro')}
    (hu : AC.UpdateAt gtr Y c s ℓ) :
    ∀ k ≤ c, gtr.RestartAt Y k → gtr.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
  rw [hc.1, hcall] at he
  have hpost : AC.joined sp (gtr.post c) (gtr.time c) := by
    have : gtr.post c = (AC.acOnTick sp Y (gtr.state Y c) ℓ.frame (gtr.time c)).1 :=
      (congrArg Prod.fst he).symm
    unfold AC.joined at hj ⊢
    rw [this, show (AC.acOnTick sp Y (gtr.state Y c) ℓ.frame (gtr.time c)).1.restartTime =
      (gtr.state Y c).restartTime from AC.step_restartTime (ro := ro') Y _ _ _ .tick nofun]
    exact hj
  have hsl : sp.slot (gtr.time c) = s + 1 :=
    AC.CompatibleSides.slot_of_lt (s := s + 1)
      (by
        rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), AC.ts_add, add_zero]
        exact add_mul_delta_le (by norm_num))
      (by rw [ht, AC.ts_add, add_assoc, ← add_mul]; exact add_mul_delta_lt (by norm_num))
  intro k hk hrk
  have := (AC.joined_awakeU sp FGP ro' H' U gtr hr.toU Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

end ACHelpers

/-! ### Handler facts over `exec'` -/

private theorem tick_cuts_if (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) (fgDue : Bool) :
    (Node.exec proposer dg y st t (.tick x fgDue)).2 =
      (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (if fgDue then (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal).1 t x .fgUpdate).2 else []) := by
  cases fgDue <;> simp [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps]

/-- An AC restart call is a restart event (a copy of `exec_restart`). -/
private theorem exec_restart (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (e : Node.Event (goldilocksNode sp ro)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (Node.exec proposer dg y st t e).2) (hm : ℓ.call = .restart) :
    e = .restart := by
  cases e with
  | message m' =>
    simp only [Node.exec_eq, Node.onMessage_eq, Node.acCall_eq, List.mem_singleton,
      Cut.ac.injEq] at h
    subst h
    cases hm
  | attestation a => simp [Node.exec_eq, Node.onAttestation] at h
  | restart => rfl
  | block B =>
    simp only [Node.exec_eq, Node.onBlock_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp [Node.acCall_eq] at h
      subst h
      cases hm
  | tick x fgDue =>
    rw [tick_cuts_if] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [Node.tickStep_eq, Node.acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
      subst h
      cases hm
    · simp only [Node.tickStep_eq] at h
      split_ifs at h
      · split at h
        · simp only [Node.acProposal_eq, List.mem_singleton, Cut.ac.injEq] at h
          subst h
          cases hm
        · rcases List.mem_cons.1 h with h | h
          · simp only [Node.acProposal_eq, Cut.ac.injEq] at h
            subst h
            cases hm
          · simp only [Node.proposeBlock_eq, Node.onBlock_eq] at h
            split_ifs at h
            · simp at h
            · split at h <;> simp [Node.acCall_eq] at h
              subst h
              cases hm
      · simp at h
    · split at h
      · simp only [Node.tickStep_eq] at h
        split at h
        · simp only [Node.acToFG_eq, List.mem_singleton, Cut.ac.injEq] at h
          subst h
          cases hm
        · rcases List.mem_cons.1 h with h | h
          · simp only [Node.acToFG_eq, Cut.ac.injEq] at h
            subst h
            cases hm
          · simp only [Node.attest] at h
            split at h <;> simp at h
      · simp at h

/-! ### Joining at a call (copies from `Compose/Run/Projection` and `Compose/Run/Handlers`) -/

/-- A call that is not a restart is in a group of a tick or a delivery (a copy of
`group_not_restart`). -/
private theorem group_not_restart {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hc : tr.IsCall y i) (hnr : ¬ tr.RestartAt y i) :
    ∃ j e, j ≤ i ∧ tr.GroupAt proposer dg y j (tr.time i) e ∧ 0 < e.phase := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨j, e, k, hg, rfl, hk⟩ := Coherence.call_in_group hrun.toLocalRun hy hc
  refine ⟨j, e, by omega, hg, ?_⟩
  cases e with
  | restart =>
    rcases k with _ | k <;> simp [Node.exec_eq, Node.restart_eq, Node.acCall_eq] at hk
    exact absurd ⟨_, by rw [← hk] at hc; exact hc, rfl⟩ hnr
  | _ => simp [Node.Event.phase]

/-- A restart call is a restart group of its own (a copy of `restartCall_group`). -/
private theorem restartCall_group {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) :
    tr.GroupAt proposer dg y k (tr.time k) .restart := by
  obtain ⟨ℓ, hc, hr⟩ := hk
  obtain ⟨j, e, m, hg, rfl, hm⟩ := Coherence.call_in_group hrun.toLocalRun hy hc
  obtain rfl := exec_restart y _ _ e (List.mem_of_getElem? hm) hr
  rcases m with _ | m
  · exact hg
  · simp [Node.exec_eq, Node.restart_eq, Node.acCall_eq] at hm

/-- The latest restart time before cut `i`. -/
private noncomputable def lastBefore (tr : GoldilocksTrace sp ro) (y : Fin sp.n) :
    Nat → WithBot Time
  | 0 => ⊥
  | i + 1 => tr.lastWake y i

open Classical in
private theorem lastBefore_succ (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat) :
    lastBefore tr y (i + 1) =
      if tr.RestartAt y i then (tr.time i : WithBot Time) else lastBefore tr y i := by
  cases i <;> rfl

private theorem lastBefore_le {ini} (h : GoldilocksRun proposer dg H tr ini)
    (y : Fin sp.n) (x : Time) :
    ∀ i, lastBefore tr y i ≤ x ↔ ∀ k < i, tr.RestartAt y k → tr.time k ≤ x := by
  intro i
  induction i with
  | zero => simp [lastBefore]
  | succ i ih =>
    rw [lastBefore_succ]
    split_ifs with hr
    · refine ⟨fun hx k hk hk' => ?_, fun hall => WithBot.coe_le_coe.2 (hall i (by omega) hr)⟩
      exact (h.time_mono (show k ≤ i by omega)).trans (WithBot.coe_le_coe.1 hx)
    · rw [ih]
      refine ⟨fun hall k hk hk' => ?_, fun hall k hk => hall k (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      exacts [hall k hk hk', absurd hk' hr]

private theorem restartTime_eq {ini} (h : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i, (tr.state y i).ac.restartTime = lastBefore tr y i := by
  intro i
  induction i with
  | zero =>
    obtain ⟨m, hm⟩ := AC.voteStart_iff.1 (h.vstart y)
    rw [Trace.state, h.init y hy]
    simp only [Node.initWith, hm]
    rfl
  | succ i ih =>
    rw [lastBefore_succ, ← ih]
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := h.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        have hlaw := (Node.cutStep_ac _ _ _ _ _).1 hlaw
        have hpost : (tr.post i).ac = ((goldilocksNode sp ro).step y (tr.state y i).ac ℓ.frame
            (tr.time i) ℓ.call).1 := (congrArg Prod.fst hlaw.2.1).symm
        rw [hpost]
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', hr⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
          rw [hr]
          have hΦ : FrameOK ℓ.frame := hlaw.1 ▸ frameOK_state' h.toLocalRun hy i
          exact (AC.restart_state sp _ ro y _ ℓ.frame (tr.time i) hΦ
            (h.time_nonneg i)).2.2.2.2.2.2.1
        · exact AC.step_restartTime y _ _ _ _ fun hr => hR ⟨ℓ, hc, hr⟩
      | fg ℓ =>
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', _⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
        congr 1
        cases ℓ with
        | block B acc =>
          cases acc
          · rw [((Node.cutStep_block_false _ _ _ _ _).1 hlaw).2]
          · exact ((Node.cutStep_block_true _ _ _ _ _).1 hlaw).2.2.1
        | attestation a => exact ((Node.cutStep_attestation _ _ _ _ _).1 hlaw).2.1
        | attest C s =>
          cases s
          · rw [((Node.cutStep_attest_none _ _ _ _ _).1 hlaw).2]
          · exact ((Node.cutStep_attest_some _ _ _ _ _ _).1 hlaw).2.2
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      split_ifs with hR
      · obtain ⟨ℓ, hℓ, _⟩ := hR
        exact absurd ⟨_, hℓ⟩ hc
      · rfl

/-- At a call other than a restart at `t`, the run's joined test is the AC state's (the
second part of a copy of `joined_projection_from`). -/
theorem joined_at_call {ini} (h : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {t : Time} (i : Nat) (hi : tr.IsCall y i)
    (hnr : ¬ tr.RestartAt y i) (hit : tr.time i = t) :
    tr.JoinedAt y t ↔ AC.joined sp (tr.state y i).ac t := by
  have hset : ∀ k, tr.RestartAt y k → (tr.time k ≤ t ↔ k < i) := by
    intro k hk
    refine ⟨fun hkt => ?_, fun hki => hit ▸ h.time_mono hki.le⟩
    by_contra hik
    rcases Nat.lt_or_eq_of_le (not_lt.1 hik) with hik | rfl
    · obtain ⟨j, e, hj, hg, hp⟩ := group_not_restart h hy hi hnr
      have htk : tr.time k = t := le_antisymm hkt (hit ▸ h.time_mono hik.le)
      have hgk := restartCall_group h hy hk
      rw [htk] at hgk
      rw [hit] at hg
      have : e.phase ≤ 0 := h.phase_order y hy y hy j k t e .restart hg hgk (by omega) (.inl rfl)
      omega
    · exact hnr hk
  unfold AC.joined
  rw [joinedAt_iff_restartCuts y t (fun k _ => h.time_nonneg k), restartTime_eq h hy,
    lastBefore_le h]
  exact ⟨fun hj k hki hk => hj k hk ((hset k hk).2 hki),
    fun hj k hk hkt => hj k ((hset k hk).1 hkt) hk⟩

/-! ### Honest votes and participants -/

/-- An honest validator awake and joined at `t_s + Δ` votes in slot `s`, at or before
`t_s + Δ` (a copy of `vote_of_awake_joined`). -/
theorem vote_of_awake_joined' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, AC.VoteAt tr.projAC y k e ∧ e.msg.slot = s ∧ tr.projAC.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection_from' hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 := ts_nonneg (sp := sp) s
  have hslot : sp.slot (sp.ts s + sp.Δ) = s :=
    AC.slot_of_mem sp s (le_add_of_nonneg_right hΔ.le)
      (by simp only [ACParams.ts]; push_cast; linarith)
  obtain ⟨j, hj'⟩ := hrun.tick_of_awake y hy _ (add_nonneg h0 hΔ.le)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 1)
      (by simp only [ACParams.ts]; ring)) hw
  obtain ⟨x, fgDue, hj'⟩ := (RunTrace.tickAt_iff _ _ _ _ _ _).1 hj'
  obtain ⟨-, hk, -⟩ := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hj'
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j)
      (sp.ts s + sp.Δ) (.tick x fgDue)).2.length := by
    rw [tick_cuts_if]; simp [Node.tickStep_eq, Node.acCall_eq]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ)
      (.tick x fgDue)).2[0]'hlen =
      .ac ⟨.tick, Node.frame (tr.state y j), ((goldilocksNode sp ro).step y (tr.state y j).ac
        (Node.frame (tr.state y j)) (sp.ts s + sp.Δ) .tick).2⟩ := by
    simp only [tick_cuts_if, Node.tickStep_eq, Node.acCall_eq]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  have hc : tr.projAC.CallAt y j ℓ := ⟨hn0, by simp [RunTrace.projAC, hl, RunTrace.acLabel]⟩
  have htj : tr.projAC.time j = sp.ts s + sp.Δ := ht0
  have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hemit : (AC.acOnTick sp y (tr.projAC.state y j) ℓ.frame (tr.projAC.time j)).2 = ℓ.emits :=
    congrArg Prod.snd he
  have hnr : ¬ tr.RestartAt y j := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have hjo : AC.joined sp (tr.projAC.state y j) (tr.projAC.time j) := by
    rw [projAC_state' hrun.toLocalRun hy j, htj]
    exact (joined_at_call hrun hy j ⟨_, hn0, hl⟩ hnr ht0).1 hj
  rcases acOnTick_votes y _ ℓ.frame hjo (by rw [htj, hslot])
      (by rw [htj, hslot, projAC_state' hrun.toLocalRun hy j]; exact hmv j) with
    hv | ⟨e, he', hes⟩
  · rw [htj, hslot] at hv
    rcases AC.cast_of_votedSlotU hr.toU hrun.vstart hy j s hv with
      ⟨k, hk, e, hve, hes⟩ | hmf
    · exact ⟨k, e, hve, hes, (hr.time_mono hk.le).trans htj.le⟩
    · rw [projAC_state' hrun.toLocalRun hy j, hmv j] at hmf
      exact absurd hmf (by decide)
  · refine ⟨j, e, ⟨ℓ, hc, hemit ▸ he'⟩, ?_, htj.le⟩
    rwa [htj, hslot] at hes

/-- Awake joined validators participate in a result observed before the finite deadline cutoff
(a copy of `awake_participant_window_before`). -/
private theorem awake_participant_window_before {ini}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) {s : Nat} {a b : Time}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from' hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined' hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := AC.castAt_specU hr.toU hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans (((add_delta_add_delta _).trans_le
      (add_mul_delta_le (by norm_num))).trans (ht.symm.trans_le hib))
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((add_delta_add_delta _).trans_le
      (add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := AC.sync_window_before_forward hr hsync hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (ha.trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := AC.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [add_delta_add_delta]; exact add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rw [← hval]
  exact AC.voter_of_backed this

/-- Awake joined validators participate in a result whose update may be after `b`: the votes are
due by `t_s + 2Δ ≤ b`, so only the early cutoff needs to be within the service horizon (a copy of
`awake_participant_early`). -/
theorem awake_participant_early' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {b : Time}
    (hsync : AC.ServiceBefore H (tr.HonestBlocks H) b tr.projAC) (hb : sp.ts s + 2 * sp.Δ ≤ b)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    {y : Fin sp.n} (hy : y ∈ H) (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from' hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined' hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := AC.castAt_specU hr.toU hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans ((add_delta_add_delta _).trans_le hb)
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((add_delta_add_delta _).trans_le
      (add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := AC.sync_window_before_forward hr ⟨hsync.message, hsync.relay⟩ hy
    ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩ ((ts_nonneg s).trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := AC.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [add_delta_add_delta]; exact add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rw [← hval]
  exact AC.voter_of_backed this

/-- If every honest member of the slot-`s` committee is awake, joined and permitted to vote,
windowed forwarding makes the faulty participants of the actual update pool fewer than half of
its participants (a copy of `honest_participants_window_before`). -/
theorem honest_participants_window_before' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    {a b : Time} {s : Nat}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b)
    (hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ))
    (hmv : ∀ y ∈ H, y ∈ K.committee s → ∀ i, (tr.state y i).ac.mayVote s = true)
    (hP : ∀ v ∈ (tr.projAC.state X i₀).pool s, v.val ∈ K.committee s)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard) :
    2 * (Hᶜ ∩ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard <
      (AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard := by
  set V := AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}
  have hVK : V ⊆ K.committee s := by
    rintro w ⟨v, hv, rfl⟩
    exact hP v hv
  have hsub : K.committee s ∩ H ⊆ V ∩ H := fun y hy =>
    ⟨awake_participant_window_before hrun hnc hsync ha hX hu hib hy.2 (hmv y hy.2 hy.1)
      (hready y hy.2).1 (hready y hy.2).2, hy.2⟩
  have hfV : Hᶜ ∩ V ⊆ K.committee s ∩ Hᶜ := fun w hw => ⟨hVK hw.2, hw.1⟩
  have hcount := Set.ncard_le_ncard hsub
  have hcountF := Set.ncard_le_ncard hfV
  have hsplitK := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee s) H (Set.toFinite _)
  have hsplitV := Set.ncard_inter_add_ncard_sdiff_eq_ncard V H (Set.toFinite _)
  rw [Set.sdiff_eq_compl_inter] at hsplitK hsplitV
  rw [Set.inter_comm Hᶜ] at hsplitK
  omega

end Consensus.Goldilocks.Compose

end
