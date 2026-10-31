module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint

public section

/-! # Goldilocks Healing: H.2 (i), the votes of a slot with an honest proposal and `Geo`

workbench `h2-open-items.md` §§1, 4, 6, by induction on the cut of the first honest slot-`p`
vote not on `P`: the voter's anchor is below `P` (`Duty(P)`'s first clause, §6 with §6.1,
`h2_duty_anchor`); then the voter's walk reaches the proposer's path (§6, second clause),
the retained heads give equal scores and majority eligibility on it (§1), `Geo` aligns the
low-parent eligibility arm, and the persist/reflect comparison (§4) makes the vote `P`
(`h2_votes_of_duty`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- A stored lock of an honest node has a slot at most the current one: it was written by an
optimistic confirmation of its slot or by the update of its slot, at an earlier cut. -/
private theorem stored_lock_slot_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {l : Lock} (hl : l ∈ (tr.state y i).locks) :
    l.slot ≤ sp.slot (tr.time i) := by
  obtain ⟨j, hj, B, horig, -⟩ := lock_provenance hr hy i l hl
  have hmono := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
  rcases horig with ⟨CV, ℓ, A, -, hsl, -⟩ | ⟨ℓ, -, -, htj, -⟩
  · omega
  · have : (l.slot : Int) ≤ sp.slot (tr.time j) :=
      (ts_le_iff_le_slot sp (hr.time_nonneg j) _).1 (by rw [htj]; linarith [sp.toParams.hΔ])
    omega

/-- **§6 `Duty(P)`, first clause, with §6.1**: at every honest vote of slot `p` before the first
one not on `P`, the anchor of the voter's walk after its unlocking is an ancestor of `P`:
`fc_root` is below the viable head `P` (`Geo`); a lock of a slot below `p` is settled, so the
proposal head `parent(P)` extends it; a slot-`p` lock is optimistic, with an honest supporter
of an earlier cut, whose head is `P`. -/
theorem h2_duty_anchor (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo proposer tr H p P) :
    ∀ x ∈ H, ∀ i ℓ e, CastAt tr x i ℓ e → e.msg.slot = p → (∀ y ∈ H, ∀ j e', VoteAt tr y j e' →
      e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) P := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg := hI.le
  have hg0 := gbar_nonneg g
  obtain ⟨k, ℓp, d, pay, hck, hcallk, hpay, htk, hPpar, -, -, -, ja, -, ⟨ℓa, hca, hcalla⟩, -⟩ :=
    hP
  have hPU : P ∈ U := (frameIn_of_callAt hr hpH hca).2
    ((accept_new sp hr hpH ⟨ℓa, hca, hcalla⟩).1 ℓa hca)
  have hdP : Anc U d.head P := by
    obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
    have hdU : d.head ∈ U := by
      rw [(acProposal_head hpay).2]
      exact hΦpU (getHead_mem hΦp (fun _ hX => hX.1) _ _ _ _)
    exact Relation.ReflTransGen.single ⟨hdU, hPU, hPpar⟩
  intro x hx i ℓ e hce hes hfirst
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hce.1
  have hsl : sp.slot (tr.time i) = p := by rw [← hes]; exact (castAt_spec hr hx hce).2.1.symm
  have hti : sp.ts p ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hsl])
  have hp0 : 0 < p := by
    have h0 : sp.ts 0 = 0 := by simp [SAParams.ts]
    have : (0 : Int) < p := (ts_lt_iff sp).1 (by rw [h0]; linarith)
    omega
  have hfc : Anc U ℓ.frame.fcRoot P :=
    (hΦ.fcRoot_anc_viableHeads P (hgeo k ℓp hck hcallk htk x hx i ℓ e hce hes).1).mono hΦU
  have hlock : ∀ D ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Anc U D P := by
    rintro D ⟨hDt, l', ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩, hDr⟩
    have hva := anc_viableAncestor ℓ.frame B₀
    obtain rfl : D = ℓ.frame.viableAncestor B₀ :=
      hΦ.coherent.1 hDt (mem_of_anc hva hB₀) hDr.symm
    refine (hva.mono hΦU).trans ?_
    by_cases hlp : l.slot = p
    · -- a slot-`p` lock: optimistic, with an honest supporter of an earlier cut on `P`
      obtain ⟨Φ', A, D', -, hΦ'U, -, h34, hpool, -, L, hL, hLr, hLD⟩ :=
        lock_origin_readPoint hrun hx hce l hl (by rw [hes, hlp]; omega)
      obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
      have hf := hI.two_faulty_lt
      have hlt : Hᶜ.ncard < (optimisticVoters sp A Φ' l.slot D').ncard := by omega
      obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hu⟩ :=
        Set.exists_mem_notMem_of_ncard_lt_ncard hlt
      have huH : v.val ∈ H := not_not.1 hu
      obtain ⟨hvs, j', hj', e', hve, rfl⟩ := hpool v hv huH
      obtain rfl : R = P :=
        hU.1 (hΦ'U hR) hPU (hRr.trans (hfirst _ huH j' e' hve (hvs.trans hlp) hj'))
      exact hLD.trans (hDR.mono hΦ'U)
    · -- an older lock: settled, below the proposal head
      obtain ⟨l₀, hl₀, hsl₀, B, hB, hBr, B', hB', hB'r, hB'B⟩ :=
        readPoint_locks_below_stored hr hx hce (by rw [hsl]; exact hp0) l hl
          (by rw [hsl]; exact hlp)
      obtain rfl : B' = B₀ := hΦ.coherent.1 hB' hB₀ (hB'r.trans hB₀r.symm)
      have hle := stored_lock_slot_le hr hx i hl₀
      rw [hsl] at hle hlive
      obtain ⟨-, hprops⟩ := locksSettled_iff.1 hset x hx i (by linarith) l₀ hl₀
        (by rw [hsl]; omega) B (hΦU hB) hBr
      exact (hB'B.mono hΦU).trans ((proposalsExtendAfter_iff.1 hprops _ hpH k ℓp p d pay hck
        hcallk htk (by omega) hpay).trans hdP)
  unfold getAnchor
  rcases hD : deepest ℓ.frame (liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i) ∪
      {ℓ.frame.fcRoot}) with _ | D
  · exact hfc
  · rcases (deepest_mem hD).1 with h | h
    · exact hlock D h
    · rw [Set.mem_singleton_iff.1 h]; exact hfc

/-- **§3, no current-slot lock at the proposal input** (claims, driven trace (b): at `t_p` the
proposer runs its tick, then `ac_proposal`, then the objects received): every stored lock of the
honest proposer of slot `p` at its `ac_proposal` at `t_p` has a slot below `p`: a slot-`p` lock
needs an optimistic check at an object call at a time `≥ t_p`, after the proposal. -/
theorem h2_proposal_locks_below (hI : InclusionRun tr H U proposer g t₀) {p : Nat}
    (hpH : proposer p ∈ H) {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt (proposer p) k ℓp) (hcall : ℓp.call = .proposal)
    (htk : tr.time k = sp.ts p) :
    ∀ l ∈ (tr.state (proposer p) k).locks, l.slot < p := by
  have hr := hI.run.localRun
  have hΔ := sp.toParams.hΔ
  intro l hl
  obtain ⟨j, hj, B, horig, -⟩ := lock_provenance hr hpH k l hl
  have ht : tr.time j ≤ sp.ts p := by simpa only [htk] using hr.time_mono hj.le
  rcases horig with ⟨CV, ℓ, A, ⟨hc, hop⟩, hslot, -⟩ | ⟨ℓ, -, -, htj, -⟩
  · by_contra hn
    have hstart : sp.ts p ≤ tr.time j :=
      (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by
        rw [hslot]; exact_mod_cast Nat.le_of_not_gt hn)
    have htime : tr.time j = sp.ts p := le_antisymm ht hstart
    have hslots : sp.slot (tr.time j) = p := by
      rw [htime]
      exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
    have hobj : (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B := by
      rcases hop with ⟨m, hm, -⟩ | ⟨B, hB, -⟩ | ⟨e, he, -⟩
      · exact Or.inl ⟨m, hm⟩
      · exact Or.inr ⟨B, hB⟩
      have hexec := hr.exec j ℓ hc.2 (hc.1 ▸ hpH)
      rw [hc.1] at hexec
      have hem : e ∈ ((goldilocksSA sp FGP ro).step (proposer p)
          (tr.state (proposer p) j) ℓ.frame
          (tr.time j) ℓ.call).2 := by rw [hexec]; exact he
      cases hcl : ℓ.call with
      | message m => exact Or.inl ⟨m, rfl⟩
      | block B => exact Or.inr ⟨B, rfl⟩
      | tick =>
        rw [hcl] at hem
        change e ∈ (acOnTick sp _ _ _ _).2 at hem
        have hne : tr.time j ≠ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
          rw [hslots, htime]; linarith
        unfold acOnTick at hem
        split_ifs at hem <;> simp_all
      | proposal => simp [hcl, ACInterface.step] at hem
      | toFG => simp [hcl, ACInterface.step] at hem
      | restart =>
        rw [hcl] at hem
        change e ∈ (acRestart sp ro _ _ _ _).2 at hem
        rw [((restart_state sp) FGP ro _ _ ℓ.frame (tr.time j)
          (frameIn_of_callAt hr hpH hc).1 (hr.time_nonneg j)).1] at hem
        simp at hem
    have := hI.driven.proposal_first _ hpH j k ℓ ℓp hc hck hcall (htime.trans htk.symm) hobj
    omega
  · have hlt : sp.ts l.slot < sp.ts p := by rw [htj] at ht; linarith
    exact_mod_cast (ts_lt_iff sp).1 hlt

/-- **§§1, 4, with §6's second clause**: with every honest slot-`p` voter's anchor below `P` up to
the first vote not on `P`, `Geo(P)` makes every honest vote of slot `p` the proposal (the
reader's walk reaches the proposer's path, §6; on it the retained heads give equal scores and
majority eligibility, §1; `Geo` aligns the low-parent arm; persistence and reflection along the
path, §4). -/
theorem h2_votes_of_duty (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo proposer tr H p P)
    (hduty : ∀ x ∈ H, ∀ i ℓ e, CastAt tr x i ℓ e → e.msg.slot = p →
      (∀ y ∈ H, ∀ j e', VoteAt tr y j e' → e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) P) :
    ∀ i, ∀ x ∈ H, ∀ ℓ e, CastAt tr x i ℓ e → e.msg.slot = p →
      (∀ y ∈ H, ∀ j e', VoteAt tr y j e' → e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      e.msg.head = P.root := by
  have hS := hI.toHealthyBase
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg := hI.le
  have hg0 := gbar_nonneg g
  have hp0 : 0 < p := by
    by_contra hn
    have : p = 0 := by omega
    subst p
    have hz : sp.ts (0 : Nat) = 0 := by simp [SAParams.ts]
    rw [hz] at hp
    linarith
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp0)
  have hP' := hP
  obtain ⟨k, ℓp, d, pay, hck, hcall, hpay, htk, hQP, hPs, -, hPpay,
    j, hkj, hacc, -⟩ := hP'
  have hPnot := (accept_new sp hr hpH hacc).2 k hkj ℓp hck
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro i x hx ℓ e hc hes hfirst
  have haP := hduty x hx i ℓ e hc hes hfirst
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  have hPv := (hgeo k ℓp hck hcall htk x hx i ℓ e hc hes).1
  have hPt := hΦ.viableHeads_subset hPv
  obtain ⟨heq, hvot, hsup⟩ := h2_views_agree hS hpH hP hck hcall htk hpay hPpay hPs
    (by rw [hts] at hp; linarith) hx hc hes hPt
  have hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓ.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1))
        (((s + 1 : Nat) : Int) - 1) B =
      goldfishScore sp ℓp.frame (View.ofLists pay) (((s + 1 : Nat) : Int) - 1) B := by
    intro B hBp hBy
    have hσ : ((s + 1 : Nat) : Int) - 1 = s := by push_cast; ring
    simp only [goldfishScore, hσ, heq, hsup B hBp hBy]
  refine h2_compare_reader hS hp0 hpH hP hck hcall htk (by linarith) hgeo hPnot hPs
    hpay hQP hx hc hes hvot hsc haP ?_
  obtain ⟨hst, hfs, hw⟩ := h2_parent_walkEnd hΦp hpay
  have hQt : d.head ∈ ℓp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc (fun _ h => h.1) hst) he).2
  have hsP : Anc U d.start P := (hw.anc (fun _ h => hΦpU h.1) (hΦpU hst)).tail
    ⟨hΦpU hQt, hΦU hPt, hQP⟩
  have hh := (castAt_spec hr hx hc).2.2.2
  rw [hes] at hh
  rcases h2_proposal_anchor hr hpH hck htk hpay
      (h2_proposal_locks_below hI hpH hck hcall htk) hset with he | hall
  · rw [he]
    rcases anc_total hU haP ((hfs.mono hΦpU).trans hsP) with haR | hRa
    · exact h2_reader_reaches_root hS hpH hck hcall htk hgeo
        ((hfs.mono hΦpU).trans hsP) hx hc hes hPs haR
    · exact hRa.trans (anc_ghost (fun B hB => hΦU hB.1.1) ℓ.frame.tree.ncard
        (by
          have hfa := fcRoot_anc_getAnchor hΦ e.readPoint (tr.time i)
          rcases Relation.ReflTransGen.cases_tail hfa with he | ⟨_, _, he⟩
          · exact he.symm ▸ hΦU hΦ.fcRoot_mem
          · exact hΦU he.2.1))
  · obtain ⟨Hd, hHd, hHdr, hsHd⟩ := hall x hx i e ⟨ℓ, hc⟩ hes
    have hget := getHead_mem hΦ (T := ℓ.frame.viableTree
      (voterBlockTree sp e.readPoint ℓ.frame (s + 1))) (fun B hB => hB.1.1) e.readPoint (tr.time i)
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (((s + 1 : Nat) : Int) - 1)
    obtain rfl := hU.1 hHd (hΦU hget) (hHdr.trans hh)
    exact hsHd

/-- **H.2 (i), §§1, 4, 6**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ` with
the locks settled from `t_{p−1}`, `Geo(P)` makes every honest vote of slot `p` the proposal (by
induction on the cut of the first vote not on `P`). -/
theorem h2_proposal_votes (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo proposer tr H p P) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  have hstep := h2_votes_of_duty hI hpH hP hp hset hgeo (h2_duty_anchor hI hpH hP hp hset hgeo)
  suffices h : ∀ j, ∀ x ∈ H, ∀ e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root from
    fun x hx j e hv hs => h j x hx e hv hs
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hx e ⟨ℓ, hc, he⟩ hs
    exact hstep j x hx ℓ e ⟨hc, he⟩ hs fun y hy j' e' hv hs' hj => ih j' hj y hy e' hv hs'

end Consensus.Goldilocks.SA

end
