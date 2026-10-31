module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # Goldilocks Healing, HS.3 (b): later votes and proposal parents

`hs234-exact-interface.md` §2.2 ("for subsequent slots use the unanimous honest batch") and §4
(b), under the settled context `Γ` (`DrainCommon`): when every honest vote of a clean slot `s` is
exactly `P`, every in-phase honest vote of a later slot extends `P` (`later_votes_extend`) and
every in-phase honest proposal of a later slot has a parent extending `P`
(`later_parents_extend`).

* The votes, by induction on the cut of the vote (the first violating event): a vote whose
  `fc_root` is above `P` extends it; one of slot `s` is `P`; a later one by A1.3 (`next_transfer`)
  from the preceding honest batch (half of the committee and `f < h_t` after `c_z`; its `Carry`,
  `honest_batch_carry`; the frozen viability of `P` from the voter's own slot-`s` vote,
  `viable_of_clean_vote`). This is `Drain`'s private `origin_extends` with the first label given.
* The proposals: the `ac_proposal` cut precedes the proposal's own block cut (one tick per node
  and time), so it is in the phase; ProposalCore's `batch_proposal` from the slot-`(s'−1)`
  honest batch, as `DrainProposal`'s `proposal_extends_of_batch`, keyed on the proposal cut
  instead of a slot-`s'` vote. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- `f < h_t` at an honest vote after the cut `c_z`, on the AC projection. -/
private theorem faultBound_proj (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : cutZ sp.toParams g ≤ tr.time k) :
    SA.FaultBound tr.projAC H (tr.time k) := by
  unfold SA.FaultBound
  rw [← (Compose.joined_projection sp ro dg H tr hrun y hy (tr.time k)).2.2]
  exact faultBound_of_healthy hrun hs hk

/-- **The later votes extend `P`** (`hs234-exact-interface.md` §2.2, §4 (b)): under `Γ` (without
`Prop⁺`), when every honest vote of a slot `s` with `t_{s−1} ≥ w + 4Δ` is exactly `P`, every
in-phase honest vote of a later slot extends `P`. -/
theorem later_votes_extend (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {s : Nat}
    (hs1 : 1 ≤ s) (hsw : w + 4 * sp.Δ ≤ sp.ts (s - 1 : Nat))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocks H)
    (hexact : ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s ≤ e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl
  have hr := hrun'.localRun
  have hS := healthyBase_of_hs hrun hs hc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  have hss : sp.ts (s - 1 : Nat) + 4 * sp.Δ = sp.ts s := by
    simp only [SAParams.ts]; push_cast [Nat.cast_sub hs1]; ring
  have hsw' : w + 4 * sp.Δ ≤ sp.ts s := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro y hy ℓ e hv hjs hk
  have hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → s ≤ e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg P :=
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      ih k' hk' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr hy hv
  have hΦU := (SA.frameIn_of_callAt hr hy hv.1).2
  by_cases hs0 : e.msg.slot = s
  · exact ⟨P, hPU, (hexact y hy k e ⟨ℓ, hv⟩ hs0).symm, .refl⟩
  by_cases hBf : Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hsm' : s ≤ m' := by omega
  have h0 := hr.time_nonneg k
  have hsl := (SA.castAt_spec hr hy hv).2.1
  have hjm : sp.ts s ≤ sp.ts m' := (SA.ts_le_iff sp).2 (by exact_mod_cast hsm')
  have htk : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp h0 _).2 (by rw [hsl])
  have hmk : sp.ts m' ≤ tr.time k := ((SA.ts_le_iff sp).2 (by omega)).trans htk
  have hsync := syncRun_of_gst (b := sp.ts e.msg.slot + sp.Δ) hs.healthy.1
    ((le_gbar g).trans (gbar_le_of_clean hw (hsw'.trans hjm)))
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF _ _ hrun.toLocalRun hsync
  have hall : ∀ z ∈ H, ∀ k' e', SA.VoteAt tr.projAC z k' e' → e'.msg.slot = m' →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg P := by
    intro z hz k' e' hv' hs'
    have hk' : k' < k := by
      by_contra hkk
      obtain ⟨ℓ', hc', he'⟩ := hv'
      have h₁ := (SA.castAt_spec hr hz ⟨hc', he'⟩).2.1
      have h₂ := SA.slot_mono sp h0 (hr.time_mono (not_lt.mp hkk))
      omega
    exact hprior z hz k' hk' e' hv' (by omega)
  -- the frozen viability of `P`, from the voter's own slot-`s` vote
  have hviab : P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot := by
    obtain ⟨k₀, e₀, hv₀, hs₀⟩ := SA.honest_votes_in_slot hS (m := s) (by linarith) y hy
    exact viable_of_clean_vote hrun hs hc hw hy hv₀ hsw' hs₀
      ⟨P, hPU, (hexact y hy k₀ e₀ hv₀ hs₀).symm, .refl⟩ hy hv (by omega) hk
  refine SA.next_transfer sp _ ro H _ tr.projAC hrun' m' y k P ℓ e hy hv hm' hall
    (half_committee_of_healthy hrun hs (cutZ_le_of_clean hw (hsw'.trans hjm)))
    (honest_batch_carry hrun hs hc hw (hsw'.trans hjm) hall hy hv hm' hviab hBf)
    (faultBound_proj hrun hs hy ((cutZ_le_of_clean hw hsw').trans (hjm.trans hmk)))
    (Compose.syncAC_mono hsync0 le_rfl hle) ?_ ?_
  · rw [← hm']
    exact Or.inl (hviab.resolve_right hBf)
  · rw [← hm']
    exact fun z hz j' hj' e' hv' hsl' => hprior z hz j' hj' e' hv' (by omega)

/-- **The `ac_proposal` cut precedes the proposal's own block cut** (one tick per node and time:
the own block call follows the tick's `ac_proposal`; as `DrainProposal`'s private
`proposal_before_holder`). -/
private theorem proposal_call_lt_own (hrun : GoldilocksRun dg H tr) {p : Fin sp.n}
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

/-- **The proposal of slot `σ + 1` follows `B`, at its own cut** (`hs234-exact-interface.md`
§2.2; `DrainProposal`'s `proposal_extends_of_batch` keyed on the in-phase proposal cut): under
`Γ` (without `Prop⁺`), let an honest vote of a clean slot `jw ≤ σ` extend `B`, and let every
honest vote of a slot `≥ σ` before the proposal's `ac_proposal` cut extend `B`. Then its head
extends `B`: unless `B ⪯ Σ.F`, `B` is viable in the proposer's full tree (`clean_vote_frame`),
the honest slot-`σ` votes reach it (`late_vote_held_of_frame`), its locks of a label `≥ σ` are
optimistic over earlier honest votes (a result of such a label is written after `t_{σ+1}`), and
`batch_proposal` applies. -/
private theorem proposal_head_of_batch (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {jw : Nat} (hjw : w + 4 * sp.Δ ≤ sp.ts jw)
    (hes : e'.msg.slot = jw) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {σ : Nat} (hjσ : jw ≤ σ)
    {p : Fin sp.n} (hpH : p ∈ H) {kP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcP : tr.projAC.CallAt p kP ℓp)
    (hprop : (SA.acProposal sp (tr.projAC.state p kP) ℓp.frame (tr.time kP)).2 = some (d, pay))
    (htP : tr.time kP = sp.ts (σ + 1 : Nat)) (hkP : PhaseOn tr.projFG H i₀ kP m c)
    (hprior : ∀ z ∈ H, ∀ k' < kP, ∀ e', SA.VoteAt tr.projAC z k' e' → σ ≤ e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthyBase_of_hs hrun hs hc
  have hrun' := hS.run
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hcP
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hjσ' : sp.ts jw ≤ sp.ts σ := (SA.ts_le_iff sp).2 (by exact_mod_cast hjσ)
  have hdt : d.head ∈ ℓp.frame.tree := by
    rw [(SA.acProposal_head hprop).2]
    exact SA.getHead_mem hΦ (fun _ hX => hX.1) _ _ _ _
  by_cases hBF : Anc (tr.HonestBlocks H) B ℓp.frame.F
  · exact hBF.trans ((hΦ.rooted.2 _ hdt).mono hΦU)
  -- (V) at the proposer
  have hVq := clean_vote_frame hrun hs hc hw hz hvz hjw hes hext hpH hkP
    (by rw [htP, hσ]; linarith) B .refl
  rw [← Compose.frame_of_projAC hrun hpH hcP] at hVq
  obtain ⟨hV, hFB⟩ : (B ∈ ℓp.frame.tree ∧
      (B ∈ ℓp.frame.viableTree ℓp.frame.tree ∨ ℓp.frame.Anc B ℓp.frame.fcRoot)) ∧
      Anc (tr.HonestBlocks H) ℓp.frame.F B := by
    rcases hVq with h | h
    · have hFB := (SA.anc_total hU h ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU)).resolve_left hBF
      have hBt := SA.mem_tree_of_between hU hΦ hΦU hFB h hΦ.fcRoot_mem
      exact ⟨⟨hBt, Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hBt h hΦ.fcRoot_mem)⟩, hFB⟩
    · exact ⟨⟨h.1, Or.inl h⟩, (hΦ.rooted.2 B h.1).mono hΦU⟩
  -- the honest slot-`σ` votes are before the proposal, so they extend `B`
  have hB : ∀ x ∈ H, ∀ j' e'', SA.VoteAt tr.projAC x j' e'' → e''.msg.slot = σ →
      SA.VoteExtends (tr.HonestBlocks H) e''.msg B := by
    intro x hx j' e'' hv'' hs''
    refine hprior x hx j' ?_ e'' hv'' hs''.ge
    obtain ⟨ℓ'', hc'', he''⟩ := hv''
    have h1 := (Compose.cast_head_fcRoot hr hx ⟨hc'', he''⟩).2
    rw [hs''] at h1
    change tr.time j' ≤ _ at h1
    by_contra hn
    have := hr.time_mono (not_lt.1 hn)
    change tr.time kP ≤ tr.time j' at this
    linarith
  have hσg : gbar g + 4 * sp.Δ ≤ sp.ts σ := by linarith
  have hPv : ∀ x ∈ H, ∀ j' e'', SA.VoteAt tr.projAC x j' e'' → e''.msg.slot = σ →
      SA.HeldAtProposal (tr.projAC.state p kP) ℓp.frame σ e''.msg := by
    intro x hx j' e'' hv'' hs''
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hB x hx j' e'' hv'' hs''
    obtain ⟨Hd, hHdt, hHdr, -, hh⟩ := SA.late_vote_held_of_frame hS hpH hcP hσg
      (by change _ ≤ tr.time kP; rw [htP, hσ]; linarith) hx hv'' hs'' fun Hd hHd hHdr => by
        rw [hU.1 hHd hHd' (hHdr.trans hHd'r.symm)]
        exact hFB.trans hBHd'
    obtain ⟨hmem, -, hbs⟩ := hh kP (Or.inl rfl)
    exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHdt, hHdr,
      (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩
  -- (L-high): the proposer's locks of a label `≥ σ` are optimistic over earlier honest votes
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p kP) (tr.time kP)
      σ B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, k', hk', CV, hO⟩ := SA.lock_below_origin hr hpH kP l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hO' : Compatible (tr.HonestBlocks H) O B := by
      rcases hO with ⟨ℓ', ⟨-, -, htk', -⟩, -⟩ | ⟨ℓo, A, hpt, hsl, hsel, -⟩
      · exfalso
        have h1 := hr.time_mono hk'.le
        have h2 : sp.ts σ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hlσ)
        change tr.time k' ≤ tr.time kP at h1
        change tr.time k' = _ at htk'
        rw [htk', htP, hσ] at h1
        linarith
      · obtain ⟨-, hΦoU⟩ := SA.frameIn_of_callAt hr hpH hpt.1
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦoU h34 hS.two_faulty_lt fun v hv hvH => ?_
        obtain ⟨hvs, j', hj', e'', hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hpH hpt hv hvH
        exact hprior _ hvH j' (by omega) e'' hve (by rw [hvs]; omega)
    rcases hO' with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  exact SA.batch_proposal hrun' hS.two_faulty_lt (SA.honest_voters_half hS hσg) hB hpH hcP
    (SA.proposal_slot htP) hprop hV hPv hhigh

/-- **The later proposal parents extend `P`** (`hs234-exact-interface.md` §2.2, §4 (b)): under
`Γ` (without `Prop⁺`), when every honest vote of a slot `s` with `t_{s−1} ≥ w + 4Δ` is exactly
`P`, every in-phase honest proposal of a later slot has a parent extending `P`: its `ac_proposal`
cut precedes its own block cut (`proposal_call_lt_own`), so it is in the phase, and every honest
vote of a slot `≥ s` before it extends `P` (`later_votes_extend`); `proposal_head_of_batch`, with
the proposer's own slot-`s` vote as the witness. -/
theorem later_parents_extend (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {s : Nat}
    (hs1 : 1 ≤ s) (hsw : w + 4 * sp.Δ ≤ sp.ts (s - 1 : Nat))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocks H)
    (hexact : ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr := by
  intro s' P' k' hss' hP's hprop' hpH hk'
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
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

/-- **HS.3 (b)'s later votes and proposal parents** (`hs234-exact-interface.md` §2.2, §4 (b)), in
HS.3's setting with `t_s ≥ r`: with every honest slot-`s` vote exactly `P`
(`later_votes_extend`, `later_parents_extend`). -/
theorem later_extend_of_setting {p : Fin sp.n} {kP s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {i iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hr : rTime sp w ≤ sp.ts s)
    (hexact : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = P.root) :
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
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
theorem proposal_start_cases (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) :
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

/-- **A live lock block of the proposer's unlocked state is below every in-phase honest
slot-`s` vote** (`hs234-exact-interface.md` §3 "the proposal-boundary helper", §4 (b)): the lock
sits below a stored live lock of the proposer (`unlock` moves locks back), clean as `t_s ≥ r`
(`live_lock_clean`), below the stored block `O` of an origin of its label written by the proposer
(`stored_fast_lock_provenance`, `stored_slow_lock_provenance`). A label `< s` gives `O ⪯` the vote
(HS.2's extension, `clean_fast_extends`, `clean_slow_extends`); a label `≥ s` is impossible
before the proposal: a regular write of it is after `t_s`, and an optimistic one has an honest
slot-`s` supporter, whose vote follows the proposal (`proposal_cut_lt`). -/
theorem proposer_lock_extends (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
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
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr' := hrun'.localRun
  have hU := hr'.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  have hps : p = sp.toParams.proposer s := hS.ready.2.1
  have htP : tr.time iP = sp.ts s := hS.time
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr' hpH hS.call
  -- the lock moves back from a stored live lock of the proposer
  obtain ⟨hB't, l', ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hlB'⟩ := hB'
  obtain rfl : B' = ℓp.frame.viableAncestor B₀ :=
    hU.1 (hΦU hB't) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlB'.symm
  obtain ⟨l₁, hl₁, hs₁, hf₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
    ((SA.locks_move_back sp) _ ℓp.frame _ (tr.time iP) hΦ).2.2 σ V l₀ hl₀
  obtain rfl : B₀ = B₀' := hΦ.coherent.1 hB₀ hB₀' (hB₀r.trans hB₀'r.symm)
  have hlv : (⟨(ℓp.frame.viableAncestor B₁).root, l₁.slot, l₁.fast⟩ : SA.Lock) ∈
      SA.liveLocks sp (tr.projAC.state p iP).locks ℓp.frame (tr.time iP) :=
    ⟨l₁, hl₁, B₁, hB₁, hB₁r, by rw [← hs₁]; exact hlive, rfl⟩
  have hclean := live_lock_clean (hr.trans (le_of_eq htP.symm)) hlv
  dsimp only at hclean
  have hB'B₁ : Anc (tr.HonestBlocks H) (ℓp.frame.viableAncestor B₀) B₁ :=
    Anc.mono hΦU ((SA.anc_viableAncestor _ B₀).trans hA)
  -- the vote is in the phase from `i₀`
  have htj : sp.ts s ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp (hr'.time_nonneg j) _).2
      (by rw [← hes, (SA.castAt_spec hr' hy hcy).2.1])
  have hij : i ≤ j := by
    by_contra hn
    have := hl.time_mono (not_le.1 hn).le
    have hst := hS.start_time
    have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
    linarith
  have hph := hS.phase y hy j ℓy e hcy hes
  have hk : PhaseOn tr.projFG H i₀ j m c :=
    phaseOn_squeeze hrun hs hS.settled.2.2 (hph j hij le_rfl)
  -- a write of a label `≥ s` at the proposer before its proposal is impossible
  have hreg : ∀ {r : Nat} {l : Nat} {ℓX : ACLabel (goldilocksNode sp ro)}, r < iP → s ≤ l →
      ¬ SA.UpdateAt tr.projAC p r l ℓX := by
    intro r l ℓX hri hsl hupd
    have h1 := hl.time_mono hri.le
    have h2 : tr.time r = sp.ts l + 6 * sp.Δ := hupd.2.2.1
    have h3 : sp.ts s ≤ sp.ts l := (SA.ts_le_iff sp).2 (by exact_mod_cast hsl)
    linarith
  cases hf : l₁.fast
  · rw [Compose.projAC_state hl hpH] at hl₁
    obtain ⟨r, hrk, O, hO, L, hL, hLr, hLO⟩ := stored_slow_lock_provenance hrun hnc hpH iP l₁ hl₁ hf
    obtain rfl : L = B₁ := hU.1 hL (hΦU hB₁) (hLr.trans hB₁r.symm)
    by_cases hls : l₁.slot < s
    · obtain ⟨Hd, hHd, hHdr, hOHd⟩ := clean_slow_extends hrun hs hS.catchUp hS.settled hpH hO
        (hclean.2 hf) j y hy ℓy e hcy (by omega) hk
      exact ⟨Hd, hHd, hHdr, hB'B₁.trans (hLO.trans hOHd)⟩
    · obtain ⟨ℓw, D, -, ⟨ℓX, C, hupd, -⟩, -⟩ := hO
      exact absurd hupd (hreg hrk (by omega))
  · obtain ⟨r, hrk, CV, ℓ', D, hcw, hfl, L, hL, hLr, hLO⟩ :=
      stored_fast_lock_provenance hr' hpH iP l₁ hl₁ hf
    obtain rfl : L = B₁ := hU.1 hL (hΦU hB₁) (hLr.trans hB₁r.symm)
    by_cases hls : l₁.slot < s
    · obtain ⟨Hd, hHd, hHdr, hOHd⟩ := clean_fast_extends hrun hs hS.catchUp hS.settled hpH
        (⟨ℓ', D, hcw, hfl, rfl⟩ : Compose.StoredFastLockAt tr p r l₁.slot _ CV) (hclean.1 hf)
        j y hy ℓy e hcy (by omega) hk
      exact ⟨Hd, hHd, hHdr, hB'B₁.trans (hLO.trans hOHd)⟩
    exfalso
    rcases hfl with ⟨ℓX, C, hupd, -⟩ | ⟨ℓo, A, hpt, hsl, hsel, -⟩
    · exact hreg hrk (by omega) hupd
    -- an optimistic lock of label `s` has an honest slot-`s` supporter before the proposal
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
      have h1 := hl.time_mono hrk.le
      have := SA.slot_mono sp (hr'.time_nonneg r) (h1.trans (le_of_eq htP))
      rwa [SA.slot_of_mem sp s le_rfl (by simp only [SAParams.ts]; push_cast; linarith)] at this
    obtain ⟨ℓv, hcv, hev⟩ := hv'
    have hcut := proposal_cut_lt hrun hnc (hps ▸ hpH) (hps ▸ hS.call) hS.call_proposal htP
      hS.one_le_slot hzH ⟨hcv, hev⟩ (by rw [hvs]; omega)
    omega

/-- **A voter below the proposer's `fc_root` reaches it** (`hs234-exact-interface.md` §4, "the
unequal-root prefix"; open): under HS.3 (b)'s premises, at an honest slot-`s` vote whose anchor is
below `P` and not above the proposer's `fc_root` `R`, the vote extends `R`. Plan: when
`R ⪯` the voter's `fc_root` the head extends it; otherwise `R` is frozen-viable
(`proposal_frozen_viable`, `R ⪯ P`) and `anc_getHead` (AC/Steps/Core) applies with
(i) the voter's live lock blocks compatible with `R` (they are below `P`, as in
`voter_anchor_below`; `R ⪯ P`) and (ii) at each block `X` strictly below `R` the child towards `R`
is the only eligible viable child. (ii) rests on one fact: every viable head `W` of the voter in
its voter block tree extends `R` (if `W` is stamped before the freeze it is relayed to the
proposer before `t_s`, above its `Σ.F` (HS.1 (a)), hence a viable head there, which extends `R`;
if `W ⪯ P` it is `P` or held by the proposer below `d.head`, again a viable head there). Then `X`
is no viable head (so the child towards `R` is eligible), and a competing viable child has a
viable head witness extending `R`, so it is on `R`'s path. -/
theorem voter_passes_proposer_root {Gp : Time}
    (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    (hp : PropPlus tr H g Gp) (hr : rTime sp w ≤ sp.ts s) (hdrain : CleanLockDrain)
    (hlock : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
        ∀ L ∈ ℓ.frame.tree, L.root = l.block →
          Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hIH : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root)
    (hbelow : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P)
    (hlow : ¬ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot
      (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg ℓp.frame.fcRoot := by
  sorry

end Start

end Consensus.Goldilocks.Healing

end
