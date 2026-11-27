module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase

public section

/-! # Historical report roots and proposal lock bounds in the P-U frame

The report root is the actual P-U fork-choice root, the finalized block `F`,
not the stock conditional root `J`. Proposal lock bounds use the ordering of
handler cuts and lock origins, independently of the fork-choice root.
-/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A report lies in the reporter's tree above the actual P-U frame root, `F`. -/
theorem report_root_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R) :
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.F R := by
  have hret := hR.2.2
  change (AC.acToFG sp _ _ _).2 = some R at hret
  have hroot : R ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot R :=
    ⟨(AC.toFG_source hret).1.1, (AC.toFG_source hret).1.2.1⟩
  rw [frame_of_projAC_at hrun hy hR.1, Node.frame_eq,
    Store.toFrame_tree, Store.toFrame_fcRoot] at hroot
  exact ⟨hroot.1.1, hroot.2.mono fun _ h => by
    rw [Store.toFrame_tree] at h
    exact h.1⟩

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Compose

open Node
open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem proposal_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (x : Nat) :
    ProposalCuts proposer y t (tickStep proposer dg y st t x .proposal).2 := by
  simp only [tickStep_eq]
  split_ifs with hp
  · refine Or.inr ⟨hp, ⟨.proposal, frame st, []⟩, rfl, ?_⟩
    split
    · exact Or.inl (by rw [acProposal_eq])
    · rename_i d p _
      refine Or.inr ?_
      simp only [proposeBlock_eq, onBlock_eq]
      split_ifs with hf
      · exact absurd hf (by simp [mkBlock])
      · refine ⟨mkBlock dg y (Node.acProposal st t).1.fg t x d.head p, rfl, rfl, ?_⟩
        split
        · exact Or.inl (by rw [acProposal_eq])
        · rename_i fg' _
          let st' : NodeState (goldilocksNode sp ro) :=
            { (Node.acProposal st t).1 with fg := fg' }
          let B := mkBlock dg y (Node.acProposal st t).1.fg t x d.head p
          refine Or.inr ⟨⟨.block B, frame st',
            ((goldilocksNode sp ro).step y st'.ac (frame st') t (.block B)).2⟩, rfl, ?_⟩
          simp only [B, st', acProposal_eq, acCall_eq]
  · exact Or.inl ⟨hp, rfl⟩

private theorem update_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (x : Nat) :
    UpdateCuts (tickStep proposer dg y st t x .fgUpdate).2 := by
  refine ⟨⟨.toFG, frame st, []⟩, rfl, ?_⟩
  simp only [tickStep_eq, acToFG_eq]
  split
  · exact Or.inl rfl
  · rename_i C _
    simp only [attest]
    split
    · exact Or.inr (Or.inl ⟨C, rfl⟩)
    · exact Or.inr (Or.inr ⟨C, _, rfl⟩)

private theorem tick_order (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (x : Nat) (fgDue : Bool) :
    TickShape proposer y fgDue t (onTick proposer dg y st t x fgDue).2 := by
  let st₁ := (tickStep proposer dg y st t x .acTick).1
  let st₂ := (tickStep proposer dg y st₁ t x .proposal).1
  cases fgDue
  · simp only [onTick_eq, runSteps_eq, tickSteps, Bool.false_eq_true, ↓reduceIte,
      List.foldl_cons, List.foldl_nil, List.nil_append]
    refine ⟨⟨.tick, frame st,
      ((goldilocksNode sp ro).step y st.ac (frame st) t .tick).2⟩,
      (tickStep proposer dg y st₁ t x .proposal).2, [], rfl, ?_,
      proposal_cuts (dg := dg) y st₁ t x, rfl⟩
    simp only [st₁, tickStep_eq, acCall_eq, List.append_nil, List.cons_append,
      List.nil_append]
  · simp only [onTick_eq, runSteps_eq, tickSteps, ↓reduceIte, List.foldl_cons,
      List.foldl_nil, List.nil_append]
    refine ⟨⟨.tick, frame st,
      ((goldilocksNode sp ro).step y st.ac (frame st) t .tick).2⟩,
      (tickStep proposer dg y st₁ t x .proposal).2,
      (tickStep proposer dg y st₂ t x .fgUpdate).2, rfl, ?_,
      proposal_cuts (dg := dg) y st₁ t x, ?_⟩
    · simp only [st₁, st₂, tickStep_eq, acCall_eq, List.cons_append, List.nil_append]
    · simpa only [↓reduceIte] using update_cuts (proposer := proposer) (dg := dg) y st₂ t x

private theorem acProposal_in_tick {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {e : Event (goldilocksNode sp ro)} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (exec proposer dg y st t e).2) (hm : ℓ.call = .proposal) :
    ∃ x fgDue, e = .tick x fgDue := by
  cases e with
  | tick x fgDue => exact ⟨x, fgDue, rfl⟩
  | message m =>
    simp only [exec_eq, onMessage_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  | attestation a => simp [exec_eq, onAttestation] at h
  | restart =>
    simp only [exec_eq, restart_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  | block B =>
    simp only [exec_eq, onBlock_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp [acCall_eq] at h
      subst h
      cases hm

private theorem tick_ac_positions {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {x c : Nat} {fgDue : Bool} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : (exec proposer dg y st t (.tick x fgDue)).2[c]? = some (Cut.ac ℓ)) :
    (ℓ.call = .tick ∧ c = 0) ∨ ℓ.call = .toFG ∨
      (Proposes proposer y t ∧
        ((ℓ.call = .proposal ∧ c = 1) ∨ (ℓ.call ≠ .proposal ∧ 2 ≤ c))) := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, hupdate⟩ :=
    tick_order (proposer := proposer) (dg := dg) y st t x fgDue
  have huc' : ∀ ℓ', Cut.ac ℓ' ∈ uc → ℓ'.call = .toFG := by
    cases fgDue
    · simp only [Bool.false_eq_true, ↓reduceIte] at hupdate
      simp [hupdate]
    simp only [↓reduceIte] at hupdate
    obtain ⟨ℓu, hlu, huc⟩ := hupdate
    intro ℓ' hm
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp at hm <;> (rw [hm]; exact hlu)
  rw [exec_eq] at h
  rw [hcs] at h
  rcases c with _ | c
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inl ⟨h ▸ hlt, rfl⟩
  rw [List.getElem?_cons_succ] at h
  rcases hpc with ⟨-, rfl⟩ | ⟨hpr, ℓ₀, hℓ₀, hpc⟩
  · exact Or.inr (Or.inl (huc' ℓ (by simpa using List.mem_of_getElem? h)))
  obtain ⟨rest, rfl, hrest⟩ : ∃ rest, pc = Cut.ac ℓ₀ :: rest ∧
      ∀ ℓ', Cut.ac ℓ' ∈ rest → ℓ'.call ≠ .proposal := by
    rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩
    · exact ⟨[], rfl, by simp⟩
    · exact ⟨_, rfl, by simp⟩
    · refine ⟨_, rfl, fun ℓ'' hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, Cut.ac.injEq, reduceCtorEq, false_or,
        or_false] at hm
      rw [hm, hℓ']
      simp
  rcases c with _ | c
  · simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inr (Or.inr ⟨hpr, Or.inl ⟨h ▸ hℓ₀, rfl⟩⟩)
  rw [List.cons_append, List.getElem?_cons_succ] at h
  rcases List.mem_append.1 (List.mem_of_getElem? h) with hm | hm
  · exact Or.inr (Or.inr ⟨hpr, Or.inr ⟨hrest ℓ hm, by omega⟩⟩)
  · exact Or.inr (Or.inl (huc' ℓ hm))

private theorem group_start {y y' : Fin sp.n} {j j' : Nat} {t t' : Time}
    {e e' : Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j t e) (hg' : tr.GroupAt proposer dg y' j' t' e')
    (h₁ : j ≤ j') (h₂ : j' < j + (exec proposer dg y (tr.state y j) t e).2.length) :
    j' = j := by
  rw [RunTrace.groupAt_iff] at hg hg'
  have := (hg.2.1 (j' - j) (by omega)).2.2.1
  rw [Nat.add_sub_cancel' h₁] at this
  exact le_antisymm (hg'.2.2 j this.symm).1 h₁

private theorem not_ownPublicationAt_of_ac_cut {y : Fin sp.n} {j k : Nat} {t : Time}
    {e : Event (goldilocksNode sp ro)} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j t e)
    (hk : (exec proposer dg y (tr.state y j) t e).2[k]? = some (.ac ℓ)) :
    ¬ tr.OwnPublicationAt proposer dg y j t := by
  rw [RunTrace.ownPublicationAt_iff]
  rintro ⟨a, ha, -⟩
  rw [RunTrace.groupAt_iff] at hg ha
  have hlen := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨-, -, hev, -, hl⟩ := hg.2.1 k hlen
  have hbound := (ha.2.2 (j + k) hev).2
  simp only [exec_eq, onAttestation, List.length_singleton] at hbound
  have hzero : k = 0 := by omega
  subst k
  have hlabel := (ha.2.1 0 (by simp [exec_eq, onAttestation])).2.2.2.2
  rw [(List.getElem?_eq_some_iff.mp hk).2] at hl
  simpa [exec_eq, onAttestation] using hl.symm.trans hlabel

private def cutPhase : Cut (goldilocksNode sp ro) → Nat
  | .ac ℓ => match ℓ.call with
    | .restart => 0
    | .tick => 1
    | _ => 2
  | .fg _ => 2

private theorem exec_head (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (e : Event (goldilocksNode sp ro)) :
    ∀ c ∈ (exec proposer dg y st t e).2.head?, cutPhase c = e.phase := by
  cases e with
  | block B =>
    simp only [exec_eq, onBlock_eq]
    split_ifs
    · simp
    · cases st.fg.onBlock B <;> simp [cutPhase, Event.phase]
  | tick x fgDue =>
    cases fgDue <;> simp [exec_eq, onTick_eq, runSteps_eq, tickSteps, tickStep_eq,
      acCall_eq, cutPhase, Event.phase]
  | _ => simp [exec_eq, onMessage_eq, onAttestation, restart_eq, acCall_eq,
      cutPhase, Event.phase]

private theorem group_phase {y : Fin sp.n} {j : Nat} {t : Time}
    {e e' : Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j t e) (hg' : tr.GroupAt proposer dg y j t e') :
    e.phase = e'.phase := by
  rw [RunTrace.groupAt_iff] at hg hg'
  have h₀ := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.2
  have h₀' := (hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).2.2.2.2
  rw [h₀'] at h₀
  have mem {l : List (Cut (goldilocksNode sp ro))} (h : l ≠ []) :
      l[0]'(List.length_pos_iff.2 h) ∈ l.head? := by
    cases l
    · exact absurd rfl h
    · rfl
  rw [← exec_head y (tr.state y j) t e _ (mem hg.1),
    ← exec_head y (tr.state y j) t e' _ (mem hg'.1), Option.some.inj h₀]

private theorem acOnTick_emits {self : Fin sp.n} {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {t : Time} {e : AC.Em sp (List (FG.Att sp.n))}
    (he : e ∈ (AC.acOnTick sp self A Φ t).2) : t = sp.ts (sp.slot t) + sp.Δ := by
  unfold AC.acOnTick at he
  dsimp only at he
  split_ifs at he <;> first | assumption | simp at he

private theorem honest_vote_call {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    (ℓ.call = .tick → tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ) ∧ ℓ.call ≠ .proposal ∧
      ℓ.call ≠ .toFG ∧ ℓ.call ≠ .restart := by
  have hr := (goldilocks_ac_projection_from' hrun hnc).localRun
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have he' : e ∈ ((AC.goldilocksAC sp _ ro).step y (tr.projAC.state y i) ℓ.frame
      (tr.projAC.time i) ℓ.call).2 := by rw [hx]; exact hc.2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at he'
  · exact acOnTick_emits he'
  · simp [ACInterface.step] at he'
  · simp [ACInterface.step] at he'
  · change e ∈ (AC.acRestart sp ro y _ ℓ.frame _).2 at he'
    rw [((AC.restart_state sp) _ ro y _ ℓ.frame _ hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- No honest optimistic check of slot `s` precedes its honest proposal. The honest voter
in an optimistic quorum must cast after the proposal cut of that same tick. -/
theorem proposal_no_optimistic_of' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {s : Nat} {K : AC.CommitteeDict sp.n} (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ AC.OptimisticLockAt tr.projAC x k' s C CV := by
  intro z hz c hci C CV hO
  have hr' := goldilocks_ac_projection_from' hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun'
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨gi, ei, ki, hgi, rfl, hki⟩ := Coherence.call_in_group hl hp (projAC_callAt.1 hc)
  rw [hti] at hgi hki
  obtain ⟨xi, fgDuei, rfl⟩ := acProposal_in_tick (List.mem_of_getElem? hki) hcall
  obtain ⟨hpr, hki1⟩ : Proposes proposer p (sp.ts s) ∧ ki = 1 := by
    rcases tick_ac_positions hki with ⟨h, -⟩ | h | ⟨hpr, ⟨-, h⟩ | ⟨h, -⟩⟩
    · rw [hcall] at h; cases h
    · rw [hcall] at h; cases h
    · exact ⟨hpr, h⟩
    · exact absurd hcall h
  have hlen := (List.getElem?_eq_some_iff.1 hki).1
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hct : tr.time c ≤ sp.ts s := hti ▸ hrun.time_mono hci.le
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (AC.deepest_mem hsel).1.2.1
  rw [hslc] at h34
  have hnoH : AC.optimisticVoters sp AO ℓO.frame s C ⊆ Hᶜ := by
    rintro u ⟨v, hv, rfl, -⟩ huH
    obtain ⟨hvs, j', hj', e', ⟨ℓ', hc', he'⟩, rfl⟩ :=
      AC.optimisticPoint_pool_voteU hr'.toU hz hpt hv huH
    have hsl' : sp.slot (tr.projAC.time j') = s :=
      (AC.castAt_specU hr.toU huH ⟨hc', he'⟩).2.1.symm.trans hvs
    have htj : tr.time j' = sp.ts s := le_antisymm ((hrun.time_mono hj').trans hct)
      ((AC.ts_le_iff_le_slot sp (hr.time_nonneg j') (s : Int)).2 (by rw [hsl']))
    obtain ⟨g, eu, k₁, hg, hjeq, hk₁⟩ := Coherence.call_in_group hl huH (projAC_callAt.1 hc')
    rw [htj] at hg hk₁
    obtain ⟨htick, hnp, hnt, hnr⟩ := honest_vote_call hrun hnc huH ⟨hc', he'⟩
    have hph : eu.phase ≤ 1 := by
      rcases lt_trichotomy g gi with h | rfl | h
      · have := hl.phase_order _ huH _ hp g gi (sp.ts s) eu _ hg hgi h
          (.inr (not_ownPublicationAt_of_ac_cut hg hk₁))
        simpa [Event.phase] using this
      · obtain ⟨_, hn₁⟩ := (group_call' hg).1
        obtain ⟨_, hn₂⟩ := (group_call' hgi).1
        have hnode : e'.msg.val = p := hn₁.1.symm.trans hn₂.1
        rw [hnode] at hg
        rw [group_phase hg hgi]
        simp [Event.phase]
      · exact absurd (group_start hgi hg h.le (by omega)) h.ne'
    cases eu with
    | tick xu fgDueu =>
      rcases tick_ac_positions hk₁ with ⟨h, -⟩ | h | ⟨hpu, ⟨h, -⟩ | ⟨-, hk₁2⟩⟩
      · have h5 := htick h
        have hslts : sp.slot (sp.ts s) = s := by
          simpa using (AC.slot_arithmetic sp s).1 0 (by omega)
        rw [htj, hslts] at h5
        linarith only [h5, hΔ]
      · exact hnt h
      · exact hnp h
      have hup : e'.msg.val = p := hpu.2.2.symm.trans hpr.2.2
      rw [hup] at hg
      have := hl.tick_unique p hp g gi (sp.ts s)
        ((RunTrace.tickAt_iff ..).2 ⟨xu, fgDueu, hg⟩)
        ((RunTrace.tickAt_iff ..).2 ⟨xi, fgDuei, hgi⟩)
      omega
    | restart =>
      have hmem := List.mem_of_getElem? hk₁
      simp only [exec_eq, restart_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at hmem
      exact hnr (by rw [hmem])
    | _ => simp [Event.phase] at hph
  have hsub : AC.optimisticVoters sp AO ℓO.frame s C ⊆ K.committee s ∩ Hᶜ := by
    intro u hu
    refine ⟨?_, hnoH hu⟩
    obtain ⟨v, hv, rfl, -⟩ := hu
    exact hP.2 z hz c ℓO AO hpt s v hv
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

set_option linter.unusedVariables false in
/-- All locks stored at an honest proposal have strictly earlier slots. -/
theorem proposal_locks_slot_of' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {K : AC.CommitteeDict sp.n}
    (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    ∀ l ∈ (tr.state p i).ac.locks, l.slot < s := by
  have hr := (goldilocks_ac_projection_from' hrun hnc).localRun
  intro l hl
  obtain ⟨-, -, -, O, hO, -⟩ := lock_origin hrun hnc hp i l hl
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
  · obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
    have := hr.time_mono hki.le
    have := ts_add_two_le (sp := sp) (m := l.slot) (s := s)
      (by linarith only [htk, this, hii, hti, sp.toParams.hΔ])
    omega
  · have hsl_i : sp.slot (tr.time i) = s := by
      rw [hti]
      simpa using (AC.slot_arithmetic sp s).1 0 (by omega)
    have hle := AC.slot_mono sp (hr.time_nonneg k') (hr.time_mono hki.le)
    obtain ⟨-, -, -, hsk, -⟩ := id hOp
    rcases Nat.lt_or_ge l.slot s with h | h
    · exact h
    have hls : l.slot = s := by rw [hii, hsl_i] at hle; omega
    exact absurd (hls ▸ hOp)
      (proposal_no_optimistic_of' hrun hnc hP hfK hp hc hcall hti x hx k' hki O CV)

end Consensus.Goldilocks.Compose

end
