module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.3 (b): later votes and proposal parents

HS.3 (b), for subsequent slots by the unanimous honest batch,
under the settled context `Γ` (`DrainCommon`): when every honest vote of a clean slot `s` is
exactly `P`, every in-phase honest vote of a later slot extends `P` (`later_votes_extend`) and
every in-phase honest proposal of a later slot has a parent extending `P`
(`later_parents_extend`).

* The votes, by induction on the cut of the vote (the first violating event): a vote whose
  `fc_root` is above `P` extends it; one of slot `s` is `P`; a later one by A1.3 (`next_transfer`)
  from the preceding honest batch (half of the committee and `f < h_t` after `c_z`; its `Carry`,
  `honest_batch_carry`; the frozen viability of `P` from the voter's own slot-`s` vote,
  `viable_of_clean_vote`): `Drain`'s `origin_extends` with the first label given.
* The proposals: the `ac_proposal` cut precedes the proposal's own block cut (one tick per node
  and time), so it is in the phase; ProposalCore's `batch_proposal` from the slot-`(s'−1)`
  honest batch (`DrainProposal`'s `proposal_head_of_batch`, keyed on the proposal cut).

It also has the start of HS.3's walk comparison (the unequal-root prefix): a voter below
the proposer's `fc_root` reaches it (`voter_passes_proposer_root`), and a clean proposer lock
start is below the vote under (b)'s premises (`proposer_lock_extends`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- A live lock comes from a stored lock that is live at the same time, with the same slot and
fast bit, whose block is below its own (in the frame). -/
private theorem liveLocks_live_source {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set Lock}
    {t : Time} {l' : Lock} (h : l' ∈ liveLocks sp L Φ t) :
    ∃ l ∈ L, l.LiveAt sp t ∧ l'.slot = l.slot ∧ l'.fast = l.fast ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ ∃ B' ∈ Φ.tree, B'.root = l'.block ∧ Φ.Anc B' B := by
  obtain ⟨l, hl, B, hB, hr, hlive, rfl⟩ := h
  exact ⟨l, hl, hlive, rfl, rfl, B, hB, hr, _, (viableAncestor_anc hΦ hB).1, rfl,
    (viableAncestor_anc hΦ hB).2⟩

/-- `liveLocks_live_source` through `unlock`, which only moves live locks back. -/
private theorem unlock_live_source {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set Lock}
    {t : Time} {s : Int} {V : View sp.n} {l' : Lock} (h : l' ∈ unlock sp L Φ t s V) :
    ∃ l ∈ L, l.LiveAt sp t ∧ l'.slot = l.slot ∧ l'.fast = l.fast ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ ∃ B' ∈ Φ.tree, B'.root = l'.block ∧ Φ.Anc B' B := by
  obtain ⟨l, hl, B, hB, hr, rfl⟩ := h
  obtain ⟨l₀, hl₀, hlive, hs, hf, B₀, hB₀, hr₀, B₁, hB₁, hr₁, hB₁B₀⟩ :=
    liveLocks_live_source hΦ hl
  have hBB₁ : B = B₁ := hΦ.coherent.1 hB hB₁ (hr.trans hr₁.symm)
  subst hBB₁
  split_ifs
  · exact ⟨l₀, hl₀, hlive, hs, hf, B₀, hB₀, hr₀, _, (unlockTarget_anc sp hΦ V s hB).1, rfl,
      (unlockTarget_anc sp hΦ V s hB).2.trans hB₁B₀⟩
  · exact ⟨l₀, hl₀, hlive, hs, hf, B₀, hB₀, hr₀, B, hB, hr, hB₁B₀⟩

/-- `readPoint_locks_below_stored` with the stored lock live at the vote: a read-point lock of a
slot other than the vote's sits below a stored lock of the same slot that is live at the cast. -/
private theorem readPoint_live_source {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {l' : Lock} (hl' : l' ∈ e.readPoint.locks)
    (hne : l'.slot ≠ sp.slot (tr.time i)) :
    ∃ l ∈ (tr.state y i).locks, l.LiveAt sp (tr.time i) ∧ l'.slot = l.slot ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
        ℓ.frame.Anc B' B := by
  obtain ⟨P, he, hP⟩ := vote_tryVote_input hr hy hc
  have hΦ := (frameIn_of_callAt hr hy hc.1).1
  rw [tryVote_readPoint_locks_eq he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, hlive₁, hs₁, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ := unlock_live_source hΦ hl'
  rcases hP with rfl | ⟨A, rfl, hAl⟩
  · exact ⟨l₁, hl₁, hlive₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  unfold optimisticConfirmation at hl₁
  split at hl₁
  · exact ⟨l₁, hAl ▸ hl₁, hlive₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  rw [updateLatestConfirmed_locks_eq] at hl₁
  obtain ⟨l₂, hl₂, hlive₂, hs₂, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
    liveLocks_live_source hΦ hl₁
  rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
  · obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
    exact ⟨l₂, hAl ▸ hl₂, hlive₂, hs₁.trans hs₂, B₂, hB₂, hB₂r, B', hB', hB'r, hA.trans hA'⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact absurd (hs₁.trans hs₂) hne

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- **The later votes extend `P`** (HS.3 (b)): under `Γ` (without
`Prop⁺`), when every honest vote of a slot `s` with `t_{s−1} ≥ w + 4Δ` is exactly `P`, every
in-phase honest vote of a later slot extends `P`. -/
theorem later_votes_extend (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {s : Nat}
    (hs1 : 1 ≤ s) (hsw : w + 4 * sp.Δ ≤ sp.ts (s - 1 : Nat))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocks H)
    (hexact : ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s ≤ e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hS := healthyBase_of_hs hrun hs hc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  have hss : sp.ts (s - 1 : Nat) + 4 * sp.Δ = sp.ts s := by
    simp only [SAParams.ts]; push_cast [Nat.cast_sub hs1]; ring
  have hsw' : w + 4 * sp.Δ ≤ sp.ts s := by linarith
  intro k y hy ℓ e hv hjs hk
  refine origin_extends hrun hs hc hw hsw
    (fun y hy k ℓ e hv h1 _ _ _ => ⟨P, hPU, (hexact y hy k e ⟨ℓ, hv⟩ (by omega)).symm, .refl⟩)
    (fun y hy k ℓ e hv hjs hk => ?_) k y hy ℓ e hv (by omega) hk
  -- the frozen viability of `P`, from the voter's own slot-`s` vote
  obtain ⟨k₀, e₀, hv₀, hs₀⟩ := SA.honest_votes_in_slot hS (m := s) (by linarith) y hy
  exact viable_of_clean_vote hrun hs hc hw hy hv₀ hsw' hs₀
    ⟨P, hPU, (hexact y hy k₀ e₀ hv₀ hs₀).symm, .refl⟩ hy hv (by omega) hk

/-- **The `ac_proposal` cut precedes the proposal's own block cut** (one tick per node and time:
the own block call follows the tick's `ac_proposal`; as `DrainProposal`'s private
`proposal_before_holder`). -/
private theorem proposal_call_lt_own (hrun : GoldilocksRun proposer dg H tr) {p : Fin sp.n}
    (hpH : p ∈ H) {kP s : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hcP : tr.projAC.CallAt p kP ℓp) (hcall : ℓp.call = .proposal)
    (htP : tr.time kP = sp.ts s) {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = s)
    {k' : Nat} (hown : tr.ProposesAt p k' P) : kP < k' := by
  have hl := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hown
  rcases Compose.blockCall_cases hl hpH hc with hg |
    ⟨j'', x, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hcP) hcall
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [htP, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by rw [← ht]; exact ⟨x, hg⟩)
  omega

/-- **The later proposal parents extend `P`** (HS.3 (b)): under
`Γ` (without `Prop⁺`), when every honest vote of a slot `s` with `t_{s−1} ≥ w + 4Δ` is exactly
`P`, every in-phase honest proposal of a later slot has a parent extending `P`: its `ac_proposal`
cut precedes its own block cut (`proposal_call_lt_own`), so it is in the phase, and every honest
vote of a slot `≥ s` before it extends `P` (`later_votes_extend`); `proposal_head_of_batch`, with
the proposer's own slot-`s` vote as the witness. -/
theorem later_parents_extend (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {s : Nat}
    (hs1 : 1 ≤ s) (hsw : w + 4 * sp.Δ ≤ sp.ts (s - 1 : Nat))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocks H)
    (hexact : ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr := by
  intro s' P' k' hss' hP's hprop' hpH hk'
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hS := healthyBase_of_hs hrun hs hc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  have hss : sp.ts (s - 1 : Nat) + 4 * sp.Δ = sp.ts s := by
    simp only [SAParams.ts]; push_cast [Nat.cast_sub hs1]; ring
  have hsw' : w + 4 * sp.Δ ≤ sp.ts s := by linarith
  obtain ⟨kP, ℓp, d, pay, hcP, hcall, hd, htP, hpar, -⟩ :=
    Compose.proposal_data hrun hpH hprop' hP's
  have hkPk := proposal_call_lt_own hrun hpH hcP hcall htP hP's hprop'
  have hkP : PhaseOn tr.projFG H i₀ kP m c := hk'.mono_right hkPk.le
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  have hvotes := later_votes_extend hrun hs hc hw hs1 hsw hPU hexact
  obtain ⟨k₀, e₀, hv₀, hs₀⟩ := SA.honest_votes_in_slot hS (m := s) (by linarith) _ hpH
  refine ⟨d.head, hpar, proposal_head_of_batch hrun hs hc hw hpH hv₀ hsw' hs₀
    ⟨P, hPU, (hexact _ hpH k₀ e₀ hv₀ hs₀).symm, .refl⟩ (by omega) hpH hcP hd htP hkP
    fun z hz k'' hk'' e'' ⟨ℓ'', hc'', he''⟩ hsl'' => ?_⟩
  -- an earlier honest vote of a slot `≥ s` is in the phase
  have htz : sp.ts e''.msg.slot ≤ tr.time k'' :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k'') _).2
      (by rw [(SA.castAt_spec hr hz ⟨hc'', he''⟩).2.1])
  have hsz : sp.ts s ≤ sp.ts e''.msg.slot := (SA.ts_le_iff sp).2 (by omega)
  exact hvotes k'' z hz ℓ'' e'' ⟨hc'', he''⟩ (by omega)
    fun k₁ h₁ h₂ => hkP k₁ h₁ (h₂.trans hk''.le)

/-- `t_s ≥ r` gives a clean previous label: `t_{s−1} ≥ t_a ≥ w + 4Δ`. -/
theorem clean_pred_of_rTime {s : Nat} (hr : rTime sp w ≤ sp.ts s) :
    1 ≤ s ∧ w + 4 * sp.Δ ≤ sp.ts (s - 1 : Nat) := by
  have ha := slotA_spec sp w
  have h1 : ((slotA sp w + 2 * sp.k + 2 : Nat) : Int) ≤ s := (SA.ts_le_iff sp).1 hr
  push_cast at h1
  have hk := sp.two_le_k
  exact ⟨by omega, ha.trans ((SA.ts_le_iff sp).2 (by omega))⟩

/-- **HS.3 (b)'s later votes and proposal parents**, in
HS.3's setting with `t_s ≥ r`: with every honest slot-`s` vote exactly `P`
(`later_votes_extend`, `later_parents_extend`). -/
theorem later_extend_of_setting {p : Fin sp.n} {kP s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {i iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hr : rTime sp w ≤ sp.ts s)
    (hexact : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root) :
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr := by
  obtain ⟨hs1, hsw⟩ := clean_pred_of_rTime hr
  have hpH : p ∈ H := hS.ready.1
  have hPU : P ∈ tr.HonestBlocks H :=
    ⟨p, hpH, kP + 1, (accept_of_proposesAt hS.run hS.shared.noColl hpH hS.ready.2.2.2.1).2.1⟩
  have hex : ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = s →
      e.msg.head = P.root := fun y hy k e ⟨ℓ, hc, he⟩ hs => hexact y hy k ℓ e ⟨hc, he⟩ hs
  exact ⟨fun y hy k ℓ e hv hs hk => later_votes_extend hS.run hS.shared hS.catchUp hS.settled
      hs1 hsw hPU hex k y hy ℓ e hv hs.le hk,
    later_parents_extend hS.run hS.shared hS.catchUp hS.settled hs1 hsw hPU hex⟩

/-! ### HS.3 (b): the voter passes the proposal walk's start -/

section Start

variable {p : Fin sp.n} {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {i iP : Nat}
  {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
  {pay : Payload sp.n}

/-- **The proposal walk starts at the proposer's `fc_root` or at a live lock block** of its
unlocked state (`get_anchor` after `unlock` at `ac_proposal`). -/
theorem proposal_start_cases
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) :
    d.start = ℓp.frame.fcRoot ∨
      d.start ∈ SA.liveLockBlocks sp (SA.unlock sp (tr.projAC.state p iP).locks ℓp.frame
        (tr.time iP) ((sp.slot (tr.time iP) : Int) - 1)
        (SA.View.ofLists (SA.voteViewList (tr.projAC.state p iP) ℓp.frame
          ((sp.slot (tr.time iP) : Int) - 1) ⊤))) ℓp.frame (tr.time iP) := by
  have hpay := hS.payload
  unfold SA.acProposal at hpay
  split_ifs at hpay
  simp only [Option.some.injEq, Prod.mk.injEq] at hpay
  obtain ⟨rfl, -⟩ := hpay
  change SA.getAnchor sp _ ℓp.frame (tr.time iP) = _ ∨ SA.getAnchor sp _ ℓp.frame (tr.time iP) ∈ _
  unfold SA.getAnchor
  rcases hD : SA.deepest ℓp.frame (SA.liveLockBlocks sp _ ℓp.frame (tr.time iP) ∪
      {ℓp.frame.fcRoot}) with _ | D
  · exact Or.inl rfl
  · rcases (SA.deepest_mem hD).1 with h | h
    · exact Or.inr h
    · exact Or.inl (Set.mem_singleton_iff.1 h)

/-- **The proposer's stored locks at its proposal are of labels `< s`**: a regular write of a
label `≥ s` is at `t_s + 6Δ` or later, after the proposal; an optimistic one (of label `s`, at
`t_s`) has an honest slot-`s` supporter, whose vote follows the proposal (`proposal_cut_lt`). -/
theorem proposer_stored_lock_lt
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) {l : SA.Lock}
    (hl : l ∈ (tr.projAC.state p iP).locks) : l.slot < s := by
  have hrun := hS.run
  have hl' := hrun.toLocalRun
  have hs := hS.shared
  have hnc := hs.noColl
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr' := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  have hps : p = proposer s := hS.ready.2.1
  have htP : tr.time iP = sp.ts s := hS.time
  by_contra hls
  -- a write of a label `≥ s` at the proposer before its proposal is impossible
  have hreg : ∀ {r : Nat} {ℓX : ACLabel (goldilocksNode sp ro)}, r < iP →
      ¬ SA.UpdateAt tr.projAC p r l.slot ℓX := by
    intro r ℓX hri hupd
    have h1 := hl'.time_mono hri.le
    have h2 : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    have h3 : sp.ts s ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast not_lt.1 hls)
    linarith
  cases hf : l.fast
  · rw [Compose.projAC_state hl' hpH] at hl
    obtain ⟨r, hrk, O, hO, -⟩ := stored_slow_lock_provenance hrun hnc hpH iP l hl hf
    obtain ⟨ℓw, D, -, ⟨ℓX, C, hupd, -⟩, -⟩ := hO
    exact hreg hrk hupd
  obtain ⟨r, hrk, CV, ℓ', D, -, hfl, -⟩ := stored_fast_lock_provenance hr' hpH iP l hl hf
  rcases hfl with ⟨ℓX, C, hupd, -⟩ | ⟨ℓo, A, hpt, hsl, hsel, -⟩
  · exact hreg hrk hupd
  -- an optimistic lock of label `≥ s` has an honest slot-`s` supporter before the proposal
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 : 3 * sp.n ≤ 4 * (SA.optimisticVoters sp A ℓo.frame (sp.slot (tr.time r)) D).ncard :=
    (SA.deepest_mem hsel).1.2.1
  change sp.slot (tr.time r) = _ at hsl
  obtain ⟨z, ⟨v, hv, rfl, -⟩, hzH⟩ :
      ∃ z ∈ SA.optimisticVoters sp A ℓo.frame (sp.slot (tr.time r)) D, z ∈ H := by
    by_contra hno
    push Not at hno
    have h1 : (SA.optimisticVoters sp A ℓo.frame (sp.slot (tr.time r)) D).ncard ≤ Hᶜ.ncard :=
      Set.ncard_le_ncard (fun z hz => hno z hz) (Set.toFinite _)
    have h2 : 3 * Hᶜ.ncard ≤ sp.n - 1 := hs.healthy.2.2
    have h5 : 0 < sp.n := sp.toParams.hn
    omega
  obtain ⟨hvs, j', hj', e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hrun' hpH hpt hv hzH
  have hrs : sp.slot (tr.time r) ≤ s := by
    have h1 := hl'.time_mono hrk.le
    have := SA.slot_mono sp (hr'.time_nonneg r) (h1.trans (le_of_eq htP))
    rwa [SA.slot_of_mem sp s le_rfl (by simp only [SAParams.ts]; push_cast; linarith)] at this
  obtain ⟨ℓv, hcv, hev⟩ := hv'
  have hcut := proposal_cut_lt hrun hnc (hps ▸ hpH) (hps ▸ hS.call) hS.call_proposal htP
    hS.one_le_slot hzH ⟨hcv, hev⟩ (by rw [hvs]; omega)
  omega

/-- **A live lock block of the proposer's unlocked state is below every in-phase honest
slot-`s` vote** (the proposal-boundary helper; HS.3 (b)): the lock
sits below a stored live lock of the proposer (`unlock` moves locks back), of a label `< s`
(`proposer_stored_lock_lt`), clean as `t_s ≥ r` (`live_lock_clean`), below the stored block `O`
of an origin of its label written by the proposer (`stored_fast_lock_provenance`,
`stored_slow_lock_provenance`), which every later in-phase honest vote extends (HS.2's extension,
`clean_fast_extends`, `clean_slow_extends`). -/
theorem proposer_lock_extends
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hr : rTime sp w ≤ sp.ts s) {σ : Int} {V : SA.View sp.n}
    {B' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB' : B' ∈ SA.liveLockBlocks sp (SA.unlock sp (tr.projAC.state p iP).locks ℓp.frame
      (tr.time iP) σ V) ℓp.frame (tr.time iP))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) : SA.VoteExtends (tr.HonestBlocks H) e.msg B' := by
  have hrun := hS.run
  have hl := hrun.toLocalRun
  have hs := hS.shared
  have hnc := hs.noColl
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr' := hrun'.localRun
  have hU := hr'.coherent
  have hpH : p ∈ H := hS.ready.1
  have htP : tr.time iP = sp.ts s := hS.time
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr' hpH hS.call
  -- the lock moves back from a stored live lock of the proposer
  obtain ⟨hB't, l', ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlB'⟩ := hB'
  obtain rfl : B' = ℓp.frame.viableAncestor B₀ :=
    hU.1 (hΦU hB't) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlB'.symm
  obtain ⟨l₁, hl₁, hlive, hs₁, hf₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
    SA.unlock_live_source hΦ hl₀
  obtain rfl : B₀ = B₀' := hΦ.coherent.1 hB₀ hB₀' (hB₀r.trans hB₀'r.symm)
  have hlv : (⟨(ℓp.frame.viableAncestor B₁).root, l₁.slot, l₁.fast, l₁.expiry⟩ : SA.Lock) ∈
      SA.liveLocks sp (tr.projAC.state p iP).locks ℓp.frame (tr.time iP) :=
    ⟨l₁, hl₁, B₁, hB₁, hB₁r, hlive, rfl⟩
  have hwf : SA.LocksWF sp (tr.projAC.state p iP).locks := by
    rw [Compose.projAC_state hl hpH]; exact Compose.locksWF_state hrun hnc hpH iP
  have hclean := live_lock_clean (hwf := hwf) (hr.trans (le_of_eq htP.symm)) hlv
  dsimp only at hclean
  have hB'B₁ : Anc (tr.HonestBlocks H) (ℓp.frame.viableAncestor B₀) B₁ :=
    Anc.mono hΦU ((SA.anc_viableAncestor _ B₀).trans hA)
  have hls := proposer_stored_lock_lt hS hl₁
  -- the vote is in the phase from `i₀`
  have htj : sp.ts s ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp (hr'.time_nonneg j) _).2
      (by rw [← hes, (SA.castAt_spec hr' hy hcy).2.1])
  have hij : i ≤ j := by
    by_contra hn
    have := hl.time_mono (not_le.1 hn).le
    have hst := hS.start_time
    have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    linarith
  have hph := hS.phase y hy j ℓy e hcy hes
  have hk : PhaseOn tr.projFG H i₀ j m c :=
    phaseOn_squeeze hrun hs hS.settled.2.2 (hph j hij le_rfl)
  cases hf : l₁.fast
  · rw [Compose.projAC_state hl hpH] at hl₁
    obtain ⟨r, -, O, hO, L, hL, hLr, hLO⟩ := stored_slow_lock_provenance hrun hnc hpH iP l₁ hl₁ hf
    obtain rfl : L = B₁ := hU.1 hL (hΦU hB₁) (hLr.trans hB₁r.symm)
    obtain ⟨Hd, hHd, hHdr, hOHd⟩ := clean_slow_extends hrun hs hS.catchUp hS.settled hpH hO
      (hclean.2 hf) j y hy ℓy e hcy (by omega) hk
    exact ⟨Hd, hHd, hHdr, hB'B₁.trans (hLO.trans hOHd)⟩
  · obtain ⟨r, -, CV, ℓ', D, hcw, hfl, L, hL, hLr, hLO⟩ :=
      stored_fast_lock_provenance hr' hpH iP l₁ hl₁ hf
    obtain rfl : L = B₁ := hU.1 hL (hΦU hB₁) (hLr.trans hB₁r.symm)
    obtain ⟨Hd, hHd, hHdr, hOHd⟩ := clean_fast_extends hrun hs hS.catchUp hS.settled hpH
      (⟨ℓ', D, hcw, hfl, rfl⟩ : Compose.StoredFastLockAt tr p r l₁.slot _ CV) (hclean.1 hf)
      j y hy ℓy e hcy (by omega) hk
    exact ⟨Hd, hHd, hHdr, hB'B₁.trans (hLO.trans hOHd)⟩

/-- **Every live lock block of an honest slot-`s` voter's read point is below `P`**
(with anchors on the parent path), at a vote before which every
honest slot-`s` vote is `P`: a read-point lock of a label `< s` sits below a stored live lock of
that label (`readPoint_locks_below_stored`), below `P` or at or below `fc_root ⪯ P` (the lock
premise); a lock of a label `≥ s` sits below a block of three quarters of the committee in a
pool of earlier votes (`lock_origin_readPoint`), which has an honest supporter (`3f < n`), of
slot `s` (no earlier vote is of a later slot), so `P`. -/
theorem readPoint_lockBlocks_below
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root) :
    ∀ B ∈ SA.liveLockBlocks sp e.readPoint.locks ℓy.frame (tr.time j),
      Anc (tr.HonestBlocks H) B P := by
  have hrun := hS.run
  have hl := hrun.toLocalRun
  have hnc := hS.shared.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hcy
  have hsj : sp.slot (tr.time j) = s := by rw [← hes]; exact hys.symm
  have hPv := proposal_frozen_viable hS hy hcy hes
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := hPv.2.1.mono hΦU
  have hPU : P ∈ tr.HonestBlocks H := hΦU hPv.1.1
  have hHc := hS.shared.healthy.2.2
  intro B' hB'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩ := SA.mem_liveLockBlocks hΦ hB'
  have hva := SA.viableAncestor_spec hΦ hB₀
  have hvaU : Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor B₀) B₀ := hva.1.mono hΦU
  rcases lt_or_ge l₀.slot s with hlt | hge
  · -- a lock of an earlier slot sits below a stored live lock: the lock premise
    obtain ⟨l, hlm, hlivel, hsl, B, hB, hBr, B'', hB'', hB''r, hB''B⟩ :=
      SA.readPoint_live_source hr hy hcy (by omega) hl₀ (by omega)
    obtain rfl : B'' = B₀ := hΦ.coherent.1 hB'' hB₀ (hB''r.trans hB₀r.symm)
    have hlv : (⟨(ℓy.frame.viableAncestor B).root, l.slot, l.fast, l.expiry⟩ : SA.Lock) ∈
        SA.liveLocks sp (tr.state y j).ac.locks ℓy.frame (tr.time j) := by
      refine ⟨l, ?_, B, hB, hBr, hlivel, rfl⟩
      rw [← Compose.projAC_state hl hy]
      exact hlm
    have hvaB := SA.viableAncestor_spec hΦ hB
    have hle : ℓy.frame.Anc (ℓy.frame.viableAncestor B'') (ℓy.frame.viableAncestor B) :=
      hvaB.2.2 _ (hva.1.trans hB''B) hva.2.1
    rcases hlock y hy j ℓy e hcy hes _ hlv (by rw [← hsl]; exact hlt) _
        (SA.viableAncestor_anc hΦ hB).1 rfl with h | h
    · exact (hle.mono hΦU).trans h
    · exact (hle.mono hΦU).trans (h.trans hfP)
  · -- a lock of slot `≥ s` sits below a block of three quarters of the committee: an honest
    -- supporter voted before, for `P`
    obtain ⟨Φ, A, D, -, hΦ'U, -, hcnt, hpool, -, L, hL, hLr, hLD⟩ :=
      SA.lock_origin_readPoint hac hy hcy l₀ hl₀ (by rw [hes]; omega)
    obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    obtain ⟨z, ⟨x, hx, rfl, R, hR, hRr, hDR⟩, hzH⟩ : ∃ z ∈ SA.optimisticVoters sp A Φ l₀.slot D,
        z ∈ H := by
      by_contra hno
      push Not at hno
      have hsub : SA.optimisticVoters sp A Φ l₀.slot D ⊆ Hᶜ := fun z hz => hno z hz
      have h1 : (SA.optimisticVoters sp A Φ l₀.slot D).ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : 3 * Hᶜ.ncard ≤ sp.n - 1 := hHc
      have h3 : 3 * sp.n ≤ 4 * (SA.optimisticVoters sp A Φ l₀.slot D).ncard := hcnt
      have h5 : 0 < sp.n := sp.toParams.hn
      omega
    obtain ⟨-, j', hj', e', hv', he'⟩ := hpool x hx hzH
    obtain ⟨ℓ', hc', hem'⟩ := hv'
    obtain ⟨-, hys', -, -⟩ := SA.castAt_spec hr hzH ⟨hc', hem'⟩
    have hys'' : e'.msg.slot = sp.slot (tr.time j') := hys'
    have hle : sp.slot (tr.time j') ≤ s :=
      hsj ▸ SA.slot_mono sp (hl.time_nonneg j') (hl.time_mono hj'.le)
    have hxs : x.slot = s := by
      have := (hpool x hx hzH).1
      rw [← he'] at this ⊢
      omega
    have hhead := hIH _ hzH j' hj' e' ⟨ℓ', hc', hem'⟩ (by rw [he']; exact hxs)
    rw [he'] at hhead
    obtain rfl : R = P := hU.1 (hΦ'U hR) hPU (hRr.trans hhead)
    exact hvaU.trans (hLD.trans (hDR.mono hΦ'U))

/-- Below a block `B`, a sibling `C` of `B` is deeper than every strict ancestor `A` of `B`. -/
private theorem slot_lt_of_sibling {FGP : Type} {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {A B C : SA.Blk sp.n FGP} (hAB : Anc U A B) (hne : A ≠ B) (hC : C ∈ U)
    (hpar : C.parent = B.parent) : A.slot < C.slot := by
  obtain rfl | ⟨q, hAq, hq⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hAB
  · exact absurd rfl hne
  exact (Anc.slot_le hU hAq).1.trans_lt (hU.2 q hq.1 C hC (hpar.trans hq.2.2))

/-- **The proposer's `fc_root` is below every viable head of an honest slot-`s` voter's voter
block tree**, when `R ⪯ P` (the unequal-root prefix): such a
head `W` is allowed (aligned readers at the vote, `viableHeads_iff`), so above the proposer's
`Σ.F` (HS.1, `finalized_anc_of_allowed`); the proposer holds it (stamped before the freeze, it
is relayed to the proposer by `t_s`, `mem_frame_of_relay`; otherwise it is below the slot-`s`
block `P`, so `P` or below `d.head`); so it is a viable head of the proposer (aligned readers at
the proposal cut), which extends `R`. -/
private theorem root_below_voterHeads
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hRP : Anc (tr.HonestBlocks H) ℓp.frame.fcRoot P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hWV : W ∈ SA.voterBlockTree sp e.readPoint ℓy.frame s) (hWv : W ∈ ℓy.frame.viableHeads) :
    Anc (tr.HonestBlocks H) ℓp.frame.fcRoot W := by
  have hrun := hS.run
  have hs := hS.shared
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  obtain ⟨hiP0, hiPj, hwin, hev⟩ := phase_at_vote hS hy hcy hes
  have hi0j : i₀ ≤ j := hiP0.trans hiPj.le
  have hfry : ℓy.frame = Node.frame (tr.state y j) := Compose.frame_of_projAC hrun hy hcy.1
  have hfrp : ℓp.frame = Node.frame (tr.state p iP) := Compose.frame_of_projAC hrun hpH hS.call
  obtain ⟨-, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hpH hS.call
  by_cases hWP : W = P
  · exact hWP ▸ hRP
  -- `W` is allowed, so above the proposer's `Σ.F`
  have hWy : W ∈ (tr.state y j).fg.tree := mem_tree_of_frame hrun hy hcy.1 hWV.1
  have hWv' : W ∈ (Node.frame (tr.state y j)).viableHeads := hfry ▸ hWv
  obtain ⟨-, hWE⟩ := (viableHeads_iff hrun hs hS.catchUp hy (hwin j hi0j le_rfl)
    (hev y hy j hi0j) hWy).1 hWv'
  have hFj := finalized_anc_of_allowed hrun hs (fun k' h1 h2 => hwin k' (hi0j.trans h1) h2) hy
    hWE hpH le_rfl le_rfl
  have hFp : Anc (tr.HonestBlocks H) (tr.state p iP).fg.F W :=
    (run_F_mono hl hpH hiPj.le).trans hFj
  have hFp' : Anc (tr.HonestBlocks H) ℓp.frame.F W := by rw [hfrp]; exact hFp
  -- the proposer holds `W`
  have hWp : W ∈ (tr.state p iP).fg.tree := by
    rcases hWV.2 with hst | ⟨P', hP't, hP's, hWP'⟩
    · rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
      rcases stamp_origin hr hy j ℓy hcy.1 W hWV.1 with hg | ⟨k', -, ℓk', hck', hWk', hsk⟩
      · have hG := Store.genesis_mem (Compose.fg_reachable hl hpH iP)
        obtain rfl := hU.1 (hΦyU hWV.1) ⟨p, hpH, iP, hG⟩ hg
        exact hG
      rw [hsk] at hst
      have hlt : tr.time k' < SA.freeze sp s :=
        WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
      have hfz : SA.freeze sp s = sp.ts ((s : Int) - 1) + 3 * sp.Δ := rfl
      have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by
        simp only [SAParams.ts]; ring
      have hwi : w ≤ tr.time i := hS.settled.2.1.1.trans (hl.time_mono hS.settled_le)
      have hgw : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hS.settled.1.late
      exact mem_tree_of_frame hrun hpH hS.call (mem_frame_of_relay hS hy hpH
        (mem_tree_of_frame hrun hy hck' hWk') (u := sp.ts s) (by linarith [hS.start_time])
        (by linarith) hS.call hS.time.ge hFp')
    · obtain rfl := frame_slot_eq_proposal hS hy hcy.1 P' hP't hP's
      have hQ := hΦp.viableHeads_subset (proposal_head_viableHead hS hy hcy hes)
      have hQt : d.head ∈ (tr.state p iP).fg.tree := mem_tree_of_frame hrun hpH hS.call hQ
      obtain rfl | ⟨q, hWq, hq⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (Anc.mono hΦyU hWP')
      · exact absurd rfl hWP
      obtain rfl : q = d.head := hU.1 hq.1 (hΦpU hQ)
        (Option.some_injective _ (hq.2.2.symm.trans hS.parent))
      have hst := store_anc_of_honest_anc hrun hnc hpH hWq hQt
      rcases eq_or_ne W d.head with h | h
      · exact h ▸ hQt
      · exact (Anc.mem hst h).1
  -- so it is a viable head of the proposer, above its `fc_root`
  have hWvp : W ∈ (Node.frame (tr.state p iP)).viableHeads :=
    (viableHeads_iff hrun hs hS.catchUp hpH (hwin iP hiP0 hiPj.le) (hev p hpH iP hiP0) hWp).2
      ⟨store_anc_of_honest_anc hrun hnc hpH hFp hWp, effAllowed_transfer hrun hnc hy hpH hWE hWp⟩
  rw [← hfrp] at hWvp
  exact Anc.mono hΦpU (hΦp.fcRoot_anc_viableHeads W hWvp)

/-- **A voter below the proposer's `fc_root` reaches it** (the
unequal-root prefix): in HS.3's setting, with (a)'s lock premise and `R ⪯ P` for the proposer's
`fc_root` `R` (no premise of (b) is needed),
an honest slot-`s` vote, before which every honest slot-`s` vote is `P`, extends `R`. When
`R ⪯` the voter's `fc_root` the head extends it; otherwise `R` is frozen-viable (between the
voter's `fc_root` and `P`, `proposal_frozen_viable`) and `anc_getHead` (AC/Steps/Core) applies:
the voter's live lock blocks are below `P` (`readPoint_lockBlocks_below`), so compatible with
`R`; and at each block `X` strictly below `R` the child `Cx` towards `R` is the only eligible
viable child, since every viable head of the voter block tree extends `R`
(`root_below_voterHeads`): `X` is no viable head (so `Cx` is eligible), and a competing viable
child has a viable head witness extending `R`, so it is on `R`'s path. -/
theorem voter_passes_proposer_root
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root)
    (hRP : Anc (tr.HonestBlocks H) ℓp.frame.fcRoot P)
    (_hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (_hlow : ¬ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot
      (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg ℓp.frame.fcRoot := by
  have hrun := hS.run
  have hnc := hS.shared.noColl
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hPv := proposal_frozen_viable hS hy hcy hes
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := hPv.2.1.mono hΦU
  rcases SA.anc_total hU hRP hfP with hRf | hfR
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcy
    exact ⟨Hd, hΦU hHd, hHdr, hRf.trans (Anc.mono hΦU hfHd)⟩
  -- `R` is in the viable voter block tree
  have hPt : P ∈ ℓy.frame.tree := hPv.1.1
  have hRt : ℓp.frame.fcRoot ∈ ℓy.frame.tree :=
    SA.mem_tree_of_between hU hΦ hΦU ((hΦ.F_anc_fcRoot.mono hΦU).trans hfR) hRP hPt
  have hRPy : ℓy.frame.Anc ℓp.frame.fcRoot P := SA.anc_tree_of_anc_U hU hΦ hΦU hRt hRP hPt
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  obtain ⟨-, -, W, hW, hWv, hPW⟩ := hPv
  have hRv : ℓp.frame.fcRoot ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) :=
    ⟨⟨hRt, Or.inr ⟨P, hPt, hPs, hRPy⟩⟩,
      SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfR hRt, W, hW, hWv, hRPy.trans hPW⟩
  have hdomA := SA.voterBlockTree_anc hr hy hcy
  rw [hes] at hdomA
  have hkey := fun W hW hWv => root_below_voterHeads hS hRP hy hcy hes (W := W) hW hWv
  have hlk := readPoint_lockBlocks_below hS hlock hy hcy hes hIH
  have hRG := SA.anc_getHead hU hΦ hΦU e.readPoint (tr.time j)
    (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) (fun _ h => h.1) hdomA
    (Or.inl hRv) (fun L hL => SA.anc_total hU (hlk L hL) hRP) ?_
  · have hGt : SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) ∈ ℓy.frame.tree :=
      SA.getHead_mem hΦ (fun _ hB => hB.1.1) _ _ _ _
    have hhead := SA.castAt_head_of_viable hr hy hcy (hes ▸ ⟨_, hRv⟩)
    rw [hes] at hhead
    exact ⟨_, hΦU hGt, hhead.symm, Anc.mono hΦU hRG⟩
  -- the child towards `R` is the only eligible viable child
  intro X Cx hCx hpx hCxR
  have hCxU : Cx ∈ tr.HonestBlocks H := hΦU hCx.1.1
  have hCxR' : Anc (tr.HonestBlocks H) Cx ℓp.frame.fcRoot := Anc.mono hΦU hCxR
  refine ⟨⟨hCx, hpx, Or.inl ?_⟩, fun D hD hne => absurd ?_ hne⟩
  · rintro ⟨W', hW'v, hW'r⟩
    have hW't := hΦ.viableHeads_subset hW'v
    have hW'C : ℓy.frame.Anc W' Cx := Relation.ReflTransGen.single ⟨hW't, hCx.1.1, hW'r⟩
    have hRW := hkey W' (hdomA Cx hCx.1 W' hW'C) hW'v
    have h1 := hU.2 W' (hΦU hW't) Cx hCxU hW'r
    have h3 := (Anc.slot_le hU (Anc.mono hΦU hW'C)).1
    have h4 := (Anc.slot_le hU hCxR').1
    have h5 := (Anc.slot_le hU hRW).1
    omega
  · obtain ⟨hDV, -, W', hW', hW'v, hDW'⟩ := hD.1
    have hDU : D ∈ tr.HonestBlocks H := hΦU hDV.1
    have hpar : D.parent = Cx.parent := hD.2.1.trans hpx.symm
    have hRW' := hkey W' hW' hW'v
    have hDR : Anc (tr.HonestBlocks H) D ℓp.frame.fcRoot := by
      rcases SA.anc_total hU (Anc.mono hΦU hDW') hRW' with hDR | hRD
      · exact hDR
      by_cases hRDe : ℓp.frame.fcRoot = D
      · exact hRDe ▸ .refl
      have h1 := slot_lt_of_sibling hU hRD hRDe hCxU hpar.symm
      have h2 := (Anc.slot_le hU hCxR').1
      omega
    by_contra h
    rcases SA.anc_total hU hDR hCxR' with hDC | hCD
    · exact absurd (slot_lt_of_sibling hU hDC h hDU hpar) (lt_irrefl _)
    · exact absurd (slot_lt_of_sibling hU hCD (Ne.symm h) hCxU hpar.symm) (lt_irrefl _)

/-! ### HS.3 (a): a proposal walk starting at a lock of the proposer -/

/-- A nonempty set of blocks of a well-formed frame has a deepest block. -/
private theorem exists_isDeepest {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {S : Set (SA.Blk sp.n FGP)} (hS : S ⊆ Φ.tree) {X : SA.Blk sp.n FGP} (hX : X ∈ S) :
    ∃ D, SA.IsDeepest Φ S D := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D₀, hD₀, hmax⟩ := hfin.toFinset.exists_max_image (SA.depth Φ) ⟨X, hfin.mem_toFinset.2 hX⟩
  rw [hfin.mem_toFinset] at hD₀
  have hfin' : {B | B ∈ S ∧ SA.depth Φ B = SA.depth Φ D₀}.Finite := hfin.subset fun _ h => h.1
  obtain ⟨D, hD', hmin⟩ := hfin'.toFinset.exists_min_image (·.root)
    ⟨D₀, hfin'.mem_toFinset.2 ⟨hD₀, rfl⟩⟩
  obtain ⟨hD, hDd⟩ := hfin'.mem_toFinset.1 hD'
  refine ⟨D, hD, fun C hC hne => ?_⟩
  rcases lt_or_eq_of_le (hmax C (hfin.mem_toFinset.2 hC)) with h | h
  · exact Or.inl (hDd ▸ h)
  · exact Or.inr ⟨h.trans hDd.symm, lt_of_le_of_ne (hmin C (hfin'.mem_toFinset.2 ⟨hC, h⟩))
      fun he => hne (hΦ.coherent.1 (hS hC) (hS hD) he.symm)⟩

/-- A candidate of the anchor (a live lock block or `fc_root`) that is compatible with it, both
below a common block, is at or below the anchor (the anchor is the deepest candidate). -/
private theorem anc_getAnchor_of_mem {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    (A : SA.SAState sp.n) (t : Time) {X Y : SA.Blk sp.n FGP}
    (hX : X ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) (hXY : Φ.Anc X Y)
    (haY : Φ.Anc (SA.getAnchor sp A Φ t) Y) : Φ.Anc X (SA.getAnchor sp A Φ t) := by
  have hsub : SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro B (hB | hB)
    exacts [hB.1, (Set.mem_singleton_iff.1 hB) ▸ hΦ.fcRoot_mem]
  obtain ⟨D₀, hD₀⟩ := exists_isDeepest hΦ hsub hX
  unfold SA.getAnchor at haY ⊢
  rcases hD : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with _ | D
  · unfold SA.deepest at hD
    split_ifs at hD with hex
    exact absurd ⟨D₀, hD₀⟩ hex
  rw [hD, Option.getD_some] at haY
  rw [Option.getD_some]
  have hDd := SA.deepest_mem hD
  rcases SA.anc_total hΦ.coherent hXY haY with h | h
  · exact h
  by_cases he : D = X
  · exact he ▸ .refl
  have hlt := SA.depth_lt_of_anc hΦ h he (hsub hX)
  rcases hDd.2 X hX (Ne.symm he) with h' | h' <;> omega

/-- The proposer's stored locks after its proposal are its `ac_proposal`'s unlocked locks. -/
theorem proposal_post_locks
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) :
    (tr.post iP).ac.locks = SA.unlock sp (tr.projAC.state p iP).locks ℓp.frame (tr.time iP)
      ((sp.slot (tr.time iP) : Int) - 1)
      (SA.View.ofLists (SA.voteViewList (tr.projAC.state p iP) ℓp.frame
        ((sp.slot (tr.time iP) : Int) - 1) ⊤)) := by
  have hrun := hS.run
  have hl := hrun.toLocalRun
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr
    proposer hrun hS.shared.noColl).localRun
  have hpH : p ∈ H := hS.ready.1
  have hx := hr.exec iP ℓp hS.call.2 (hS.call.1 ▸ hpH)
  rw [hS.call.1, hS.call_proposal] at hx
  have hpost : tr.projAC.post iP =
      (SA.acProposal sp (tr.projAC.state p iP) ℓp.frame (tr.time iP)).1 :=
    (congrArg Prod.fst hx).symm
  have hc := Compose.projAC_callAt.1 hS.call
  have h1 : tr.state p (iP + 1) = tr.post iP := by simp [Trace.state, hc.1, hc.2]
  have h2 : tr.projAC.state p (iP + 1) = tr.projAC.post iP := by
    simp [Trace.state, hS.call.1, hS.call.2]
  rw [← h1, ← Compose.projAC_state hl hpH, h2, hpost]
  have hpay := hS.payload
  unfold SA.acProposal at hpay ⊢
  split_ifs at hpay ⊢
  rfl

end Start

end Consensus.Goldilocks.Healing

end
