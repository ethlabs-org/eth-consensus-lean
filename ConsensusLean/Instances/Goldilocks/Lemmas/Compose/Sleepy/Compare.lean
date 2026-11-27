module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
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
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.SideCount

public section

/-! # Goldilocks under `Sleepy`: honest votes and participants

* **Honest votes** (`vote_of_awake_joined`): an honest validator awake and joined at `t_s + Δ`
  votes in slot `s`, at or before `t_s + Δ`; `mayVote_of_start` and `mayVote_stock` give the vote
  permission.
* **Honest participants** (`awake_participant_window_before`, `awake_participant_early`,
  `honest_participants_window_before`): awake joined validators participate in a result observed
  before a finite deadline, and with every honest committee member awake, joined and permitted, the
  faulty participants of the update pool are fewer than half. -/

/-! ## Over AC traces: `voted_slot`, and the relay of one slot's votes to a writer -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {proposer : Nat → Fin sp.n}

/-- At the tick at `t_s + Δ` of a joined node, `try_vote` runs: the node votes in slot `s`, or
`voted_slot = s` already. -/
private theorem acOnTick_votes (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (ht : t = sp.ts (sp.slot t) + sp.Δ)
    (hm : A.mayVote (sp.slot t) = true) :
    A.votedSlot = sp.slot t ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg.slot = sp.slot t := by
  unfold acOnTick
  simp only [hj, not_true_eq_false, ↓reduceIte, ← ht]
  unfold tryVote
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

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
private theorem update_restarts {ini} (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    {Y : Fin sp.n}
    (hY : Y ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)} (hu : UpdateAt tr Y c s ℓ) :
    ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
  rw [hc.1, hcall] at he
  have hpost : joined sp (tr.post c) (tr.time c) := by
    have : tr.post c = (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1 :=
      (congrArg Prod.fst he).symm
    unfold joined at hj ⊢
    rw [this, show (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1.restartTime =
      (tr.state Y c).restartTime from step_restartTime Y _ _ _ .tick nofun]
    exact hj
  have hsl : sp.slot (tr.time c) = s + 1 :=
    CompatibleSides.slot_of_lt (s := s + 1)
      (by
        rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), ts_add, add_zero]
        exact add_mul_delta_le (by norm_num))
      (by rw [ht, ts_add, add_assoc, ← add_mul]; exact add_mul_delta_lt (by norm_num))
  intro k hk hrk
  have := (joined_awakeU sp FGP H U tr hr.toU Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

/-- `u` has a slot-`s` vote whose head extends `D` inside `U`, which `X` sent or admitted at a
time in `[t_s, t_s + 2Δ)`. -/
private def Relayed (tr : GTrace sp FGP) (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat)
    (D : Blk sp.n FGP) (u : Fin sp.n) : Prop :=
  ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ

/-- **A result's side.** At an honest update of slot `s` with result `D`: the node's restarts were
at or before `t_s`; its counted validators `S` are more than half of its voters; each has a vote
in its pool, extending `D`, and does not equivocate there, and that vote was admitted in
`[t_s, t_s + 2Δ)`. -/
private theorem result_side (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksAC sp FGP)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Relayed tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hr := hrun.localRun
  have hmaj := result_majority hR
  obtain ⟨ℓ, hu, -, rfl⟩ := hR
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hY hu.1
  refine ⟨ℓ, _, hu.1, hu.2.2.1, update_restarts hr hY hu, hmaj, ?_, ?_⟩
  · rintro u ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvs := state_pool_slotU sp hr.toU (fun _ => voteStart_initial _) hY c s v hvp
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩,
      admitted_of_heldU hr.toU (fun _ => voteStart_initial _) hY hvs hvp le_rfl
      fun k _ hst => ?_⟩
    have hst' : (tr.state Y c).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) := by
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · split_ifs at hres
        · exact absurd hres (by simp [ETime.of])
        · exact lt_of_le_of_lt (le_max_left _ _) hres
    rw [hst] at hst'
    exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst')
  · rintro u ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- **An optimistic selection's seats.** At an honest optimistic confirmation of slot `s` on `D`,
three quarters of the committee are optimistic voters of `D`, each with a vote extending `D` that
the node admitted (or cast) in `[t_s, t_s + 2Δ)`. -/
private theorem optimistic_seats
    (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV)
    (hstock : sp.committeeSize = sp.n) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Relayed tr U X s D := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hfl
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hX hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hcond
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34 hcond
  rw [hstock] at h34
  refine ⟨ℓ, A, hpt, hΦU, h34, ?_⟩
  rintro u ⟨v, hv, rfl, R, hR, hRr, hDR⟩
  have hvs := optimisticPoint_pool_slotU hr.toU (fun _ => voteStart_initial _) hX hpt hv
  have htk : tr.time k < sp.ts s + 2 * sp.Δ :=
    not_le.1 (not_or.1 (not_or.1 (not_or.1 hcond).2).2).1
  refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
  exact admitted_of_heldU hr.toU (fun _ => voteStart_initial _) hX hvs
    (optimisticPoint_pool_postU hr.toU hX hpt s hv) le_rfl
    fun k' hk' _ => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk')) htk

end Consensus.Goldilocks.AC

/-! ## Over a Goldilocks run -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem ts_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  simp only [ACParams.ts]
  exact mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (Int.natCast_nonneg s)

/-- Slot starts are monotone in the slot. -/
theorem ts_le_ts {s s' : Nat} (h : s ≤ s') : sp.ts s ≤ sp.ts s' :=
  (AC.ts_le_iff sp).2 (by exact_mod_cast h)

variable {b : Time} {s₀ : Nat}

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp)) (t : Time)
    (x : Nat) (fgDue : Bool) :
    (Node.exec proposer dg y st t (.tick x fgDue)).2 =
      (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (if fgDue then (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal).1 t x .fgUpdate).2 else []) := by
  cases fgDue <;> simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- **An honest validator awake and joined at `t_s + Δ` votes in slot `s`**, at or before
`t_s + Δ`: its tick there runs `try_vote` unless it voted in slot `s` already. -/
theorem vote_of_awake_joined {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, AC.VoteAt tr.projAC y k e ∧ e.msg.slot = s ∧ tr.projAC.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 := ts_nonneg (sp := sp) s
  have hslot : sp.slot (sp.ts s + sp.Δ) = s :=
    AC.slot_of_mem sp s (le_add_of_nonneg_right hΔ.le)
      (by simp only [ACParams.ts]; push_cast; linarith)
  obtain ⟨j, x, fgDue, hj'⟩ := hrun.tick_of_awake y hy _ (add_nonneg h0 hΔ.le)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 1)
      (by simp only [ACParams.ts]; ring)) hw
  obtain ⟨-, hk, -⟩ := hj'
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j)
      (sp.ts s + sp.Δ) (.tick x fgDue)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ) (.tick x fgDue)).2[0]'hlen =
      (Node.acCall y (tr.state y j) (sp.ts s + sp.Δ) .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp),
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
    rw [projAC_state hrun.toLocalRun hy j, htj]
    exact ((joined_projection_from hrun hy _).2.1 j ⟨_, hn0, hl⟩ hnr ht0).1 hj
  rcases AC.acOnTick_votes y _ ℓ.frame hjo (by rw [htj, hslot])
      (by rw [htj, hslot, projAC_state hrun.toLocalRun hy j]; exact hmv j) with hv | ⟨e, he', hes⟩
  · rw [htj, hslot] at hv
    rcases AC.cast_of_votedSlotU hr.toU hrun.vstart hy j s hv with
      ⟨k, hk, e, hve, hes⟩ | hmf
    · exact ⟨k, e, hve, hes, (hr.time_mono hk.le).trans htj.le⟩
    · rw [projAC_state hrun.toLocalRun hy j, hmv j] at hmf
      exact absurd hmf (by decide)
  · refine ⟨j, e, ⟨ℓ, hc, hemit ▸ he'⟩, ?_, htj.le⟩
    rwa [htj, hslot] at hes

/-- `hmv` from any starts up to the vote permission: the start's own permission, kept along the
trace (`trace_mayVote`). -/
theorem mayVote_of_start {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {s : Nat} (h₀ : AC.ACState.mayVote (ini y) s = true) :
    ∀ i, (tr.state y i).ac.mayVote s = true := fun i => by
  rw [← projAC_state hrun.toLocalRun hy i,
    AC.trace_mayVote (goldilocks_ac_projection_from hrun hnc).localRun hy i]
  exact h₀

/-- `hmv` on a stock run: `mayVote_of_start` at the initial starts, whose permission is
`fun _ => true`. -/
theorem mayVote_stock (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (s : Nat) : ∀ i, (tr.state y i).ac.mayVote s = true :=
  mayVote_of_start hrun hnc hy rfl

/-- Awake joined validators participate in a result observed before the finite deadline
cutoff. Only their vote deadlines are used; later receiver wakes are irrelevant. -/
theorem awake_participant_window_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {a b : Time}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := AC.castAt_specU hr.toU hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans (((AC.add_delta_add_delta _).trans_le
      (AC.add_mul_delta_le (by norm_num))).trans (ht.symm.trans_le hib))
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((AC.add_delta_add_delta _).trans_le
      (AC.add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := AC.sync_window_before_forward hr hsync hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (ha.trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (AC.update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := AC.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [AC.add_delta_add_delta]; exact AC.add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rw [← hval]
  exact AC.voter_of_backed this

/-- Awake joined validators participate in a result whose update may be after `b`: the votes are
due by `t_s + 2Δ ≤ b`, so only the early cutoff needs to be within the service horizon. -/
theorem awake_participant_early {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {b : Time}
    (hsync : AC.ServiceBefore H (tr.HonestBlocks H) b tr.projAC) (hb : sp.ts s + 2 * sp.Δ ≤ b)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
    {y : Fin sp.n} (hy : y ∈ H) (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := AC.castAt_specU hr.toU hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans ((AC.add_delta_add_delta _).trans_le hb)
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((AC.add_delta_add_delta _).trans_le
      (AC.add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := AC.sync_window_before_forward hr ⟨hsync.message, hsync.relay⟩ hy
    ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩ ((ts_nonneg s).trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (AC.update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := AC.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [AC.add_delta_add_delta]; exact AC.add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rw [← hval]
  exact AC.voter_of_backed this

/-- If every honest member of the slot-`s` committee is awake, joined and permitted to vote,
windowed forwarding makes the faulty participants of the actual update pool fewer than half of
its participants, given that every pool vote is signed by a member and fewer than half of the
committee is faulty. No head resolution is needed. -/
theorem honest_participants_window_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    {a b : Time} {s : Nat}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC X i₀ s ℓX)
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
