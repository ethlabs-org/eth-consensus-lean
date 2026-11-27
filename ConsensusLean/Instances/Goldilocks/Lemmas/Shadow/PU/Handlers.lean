module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence

public section

/-! # Handler cut chains for the shadow execution -/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

/-- Consecutive shadow cuts, with their intermediate states. -/
end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- Shadow cut chains compose. -/
theorem chain_append' {t : Time} {st st₁ st₂ : NodeState A} {cs cs' : List (Cut A)}
    (h : CutChain self t st cs st₁) (h' : CutChain self t st₁ cs' st₂) :
    CutChain self t st (cs ++ cs') st₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

private theorem chain_single {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep' self t st c st') : CutChain self t st [c] st' :=
  .cons h (.nil _)

private theorem acCall_chain (st : NodeState A) (t : Time) (c : A.Call) :
    CutChain self t st [(acCall self st t c).2] (acCall self st t c).1 := by
  apply chain_single
  simp only [acCall_eq]
  rw [cutStep_ac]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem onBlock_chain (st : NodeState A) (t : Time) (B : A.Blk) :
    CutChain self t st (onBlock self st t B).2 (onBlock self st t B).1 := by
  rw [onBlock_eq]
  split_ifs with hf
  · exact .nil _
  · split
    · rename_i h
      apply chain_single
      rw [cutStep_block_false]
      exact ⟨h, rfl⟩
    · rename_i fg' h
      refine .cons (st₁ := { st with fg := fg' }) ?_ (acCall_chain self _ t _)
      rw [cutStep_block_true]
      exact ⟨Nat.le_of_not_lt hf, h, rfl, rfl⟩

private theorem attest_chain (st : NodeState A) (t : Time) (C : A.Blk) :
    CutChain self t st (attest self st C).2 (attest self st C).1 := by
  unfold attest
  split
  · rename_i h
    apply chain_single
    rw [cutStep_attest_none]
    exact ⟨h, rfl⟩
  · rename_i a Λ' h
    apply chain_single
    rw [cutStep_attest_some]
    exact ⟨h, rfl, rfl⟩

/-- Each shadow tick step executes its recorded cuts. -/
theorem tickStep_chain' (st : NodeState A) (t : Time) (x : Nat) (s : TickStep) :
    CutChain self t st (tickStep proposer dg self st t x s).2
      (tickStep proposer dg self st t x s).1 := by
  cases s <;> simp only [tickStep_eq]
  case acTick => exact acCall_chain self st t .tick
  case proposal =>
    split_ifs
    · split
      · apply chain_single
        simp only [acProposal_eq]
        rw [cutStep_ac]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · rename_i d p _
        rw [proposeBlock_eq]
        refine .cons (st₁ := (Node.acProposal st t).1) ?_
          (onBlock_chain self (Node.acProposal st t).1 t
            (mkBlock dg self (Node.acProposal st t).1.fg t x d.head p))
        simp only [acProposal_eq]
        rw [cutStep_ac]
        exact ⟨rfl, rfl, rfl, rfl⟩
    · exact .nil _
  case fgUpdate =>
    split
    · apply chain_single
      simp only [acToFG_eq]
      rw [cutStep_ac]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · rename_i C _
      refine .cons (st₁ := (Node.acToFG st t).1) ?_
        (attest_chain self (Node.acToFG st t).1 t C)
      simp only [acToFG_eq]
      rw [cutStep_ac]
      exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runSteps_chain (st : NodeState A) (t : Time) (x : Nat)
    (steps : List TickStep) :
    CutChain self t st (runSteps proposer dg self st t x steps).2
      (runSteps proposer dg self st t x steps).1 := by
  rw [runSteps_eq]
  suffices h : ∀ (acc : NodeState A × List (Cut A)), CutChain self t st acc.2 acc.1 →
      CutChain self t st (steps.foldl (fun acc step =>
        let r := tickStep proposer dg self acc.1 t x step; (r.1, acc.2 ++ r.2)) acc).2
        (steps.foldl (fun acc step =>
        let r := tickStep proposer dg self acc.1 t x step; (r.1, acc.2 ++ r.2)) acc).1 from
    h _ (.nil _)
  induction steps with
  | nil => exact fun _ h => h
  | cons s l ih =>
    intro acc h
    exact ih _ (chain_append' self h (tickStep_chain' proposer dg self _ t x s))

/-- All shadow handlers satisfy the cut-chain law. -/
theorem exec_is_cut_chain' (st : NodeState A) (t : Time) (e : Event A) :
    CutChain self t st (exec proposer dg self st t e).2
      (exec proposer dg self st t e).1 := by
  cases e <;> simp only [exec_eq]
  case tick x f => rw [onTick_eq]; exact runSteps_chain proposer dg self st t x _
  case block B => exact onBlock_chain self st t B
  case message m => rw [onMessage_eq]; exact acCall_chain self st t _
  case attestation a =>
    apply chain_single
    rw [cutStep_attestation]
    exact ⟨rfl, rfl, rfl⟩
  case restart => rw [restart_eq]; exact acCall_chain self st t _

private theorem cutStep_unique {y : Fin P.n} {t : Time} {st st₁ st₂ : NodeState A}
    {c : Cut A} (h₁ : CutStep' y t st c st₁) (h₂ : CutStep' y t st c st₂) : st₁ = st₂ := by
  obtain ⟨fg₁, ac₁, r₁⟩ := st₁
  obtain ⟨fg₂, ac₂, r₂⟩ := st₂
  cases c with
  | ac ℓ =>
    rw [cutStep_ac] at h₁ h₂
    obtain ⟨-, e₁, h₁, h₁'⟩ := h₁
    obtain ⟨-, e₂, h₂, h₂'⟩ := h₂
    have := (Prod.mk.inj (e₁.symm.trans e₂)).1
    simp_all
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | true =>
        rw [cutStep_block_true] at h₁ h₂
        obtain ⟨-, e₁, h₁, h₁'⟩ := h₁
        obtain ⟨-, e₂, h₂, h₂'⟩ := h₂
        have := Option.some.inj (e₁.symm.trans e₂)
        simp_all
      | false =>
        rw [cutStep_block_false] at h₁ h₂
        exact h₁.2.trans h₂.2.symm
    | attestation a =>
      rw [cutStep_attestation] at h₁ h₂
      obtain ⟨e₁, h₁, h₁'⟩ := h₁
      obtain ⟨e₂, h₂, h₂'⟩ := h₂
      simp_all
    | attest C s =>
      cases s with
      | none =>
        rw [cutStep_attest_none] at h₁ h₂
        exact h₁.2.trans h₂.2.symm
      | some a =>
        rw [cutStep_attest_some] at h₁ h₂
        obtain ⟨e₁, h₁, h₁'⟩ := h₁
        obtain ⟨e₂, h₂, h₂'⟩ := h₂
        have := (Prod.mk.inj (Option.some.inj (e₁.symm.trans e₂))).2
        simp_all

private def cutPhase : Cut A → Nat
  | .ac ℓ => match ℓ.call with
    | .restart => 0
    | .tick => 1
    | _ => 2
  | .fg _ => 2

private theorem exec_head (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) :
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

variable {proposer dg self} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
  {tr : RunTrace A} {ini : Fin P.n → A.State}

theorem group_call' {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt proposer dg y j t e) : tr.IsCall y j ∧ tr.time j = t := by
  rw [RunTrace.groupAt_iff] at hg
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 0 (List.length_pos_iff.2 hg.1)
  simp only [Nat.add_zero] at hn ht hl
  exact ⟨⟨_, hn, hl⟩, ht⟩

private theorem group_phase {y : Fin P.n} {j : Nat} {t t' : Time} {e e' : Event A}
    (hg : tr.GroupAt proposer dg y j t e) (hg' : tr.GroupAt proposer dg y j t' e') :
    e.phase = e'.phase := by
  have htt : t = t' := (group_call' hg).2.symm.trans (group_call' hg').2
  subst htt
  rw [RunTrace.groupAt_iff] at hg hg'
  have h₀ := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.2
  have h₀' := (hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).2.2.2.2
  rw [h₀'] at h₀
  have mem {l : List (Cut A)} (h : l ≠ []) : l[0]'(List.length_pos_iff.2 h) ∈ l.head? := by
    cases l
    · exact absurd rfl h
    · rfl
  rw [← exec_head proposer dg y (tr.state y j) t e _ (mem hg.1),
    ← exec_head proposer dg y (tr.state y j) t e' _ (mem hg'.1), Option.some.inj h₀]

private theorem group_start {y y' : Fin P.n} {j j' : Nat} {t t' : Time} {e e' : Event A}
    (hg : tr.GroupAt proposer dg y j t e) (hg' : tr.GroupAt proposer dg y' j' t' e')
    (h₁ : j ≤ j') (h₂ : j' < j + (exec proposer dg y (tr.state y j) t e).2.length) :
    j' = j := by
  rw [RunTrace.groupAt_iff] at hg hg'
  have := (hg.2.1 (j' - j) (by omega)).2.2.1
  rw [Nat.add_sub_cancel' h₁] at this
  exact le_antisymm (hg'.2.2 j this.symm).1 h₁

theorem group_cut {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt proposer dg y j t e) {k : Nat} {c : Cut A}
    (hk : (exec proposer dg y (tr.state y j) t e).2[k]? = some c) :
    tr.CallAt y (j + k) c ∧ tr.time (j + k) = t := by
  rw [RunTrace.groupAt_iff] at hg
  obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 k hk'
  exact ⟨⟨hn, hl.trans (congrArg some hc)⟩, ht⟩

theorem cutChain_run' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {t : Time} {st st' : NodeState A} {cs : List (Cut A)}
    (hch : CutChain y t st cs st') :
    ∀ j, tr.state y j = st →
      (∀ k (hk : k < cs.length), tr.node (j + k) = y ∧ tr.time (j + k) = t ∧
        tr.label (j + k) = some cs[k]) → tr.state y (j + cs.length) = st' := by
  induction hch with
  | nil => exact fun j hj _ => hj
  | @cons st st₁ st' c cs hs _ ih =>
    intro j hj hk
    obtain ⟨hn, ht, hl⟩ := hk 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hn ht hl
    have hc : tr.CallAt y j c := ⟨hn, hl⟩
    have hlaw := h.cutLaw y hy j c hc
    rw [ht, hj] at hlaw
    have := ih (j + 1) (by rw [tr.state_succ_of_call hc, cutStep_unique hlaw hs]) fun k hk' => by
      have := hk (k + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at this
      rwa [show j + (k + 1) = j + 1 + k by omega] at this
    simpa only [List.length_cons, show j + (cs.length + 1) = j + 1 + cs.length by omega]
      using this

private theorem group_post (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt proposer dg y j t e) :
    tr.state y (j + (exec proposer dg y (tr.state y j) t e).2.length) =
      (exec proposer dg y (tr.state y j) t e).1 := by
  rw [RunTrace.groupAt_iff] at hg
  exact cutChain_run' h hy (exec_is_cut_chain' proposer dg y (tr.state y j) t e)
    j rfl fun k hk =>
      ⟨(hg.2.1 k hk).1, (hg.2.1 k hk).2.1, (hg.2.1 k hk).2.2.2.2⟩

private structure GInv (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (tr : RunTrace A)
    (y : Fin P.n) (s₀ : A.State) (j : Nat) (cfg : Config A) : Prop where
  reach : Node.Reachable' proposer dg y cfg s₀
  st : cfg.st = tr.state y j
  calls : ∀ k < j, tr.IsCall y k → tr.time k ≤ cfg.time
  time : cfg.time ≤ tr.time j
  phase : cfg.phase = .post ↔
    ∃ j₀ < j, ∃ e₀, tr.GroupAt proposer dg y j₀ cfg.time e₀ ∧ 0 < e₀.phase

variable {s₀ : A.State}

private theorem gInv_skip (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    {j : Nat} {cfg : Config A} (hi : GInv proposer dg tr y s₀ j cfg)
    (hn : ¬ tr.IsCall y j) : GInv proposer dg tr y s₀ (j + 1) cfg where
  reach := hi.reach
  st := by rw [hi.st, tr.state_succ_of_not fun ℓ hc => hn ⟨ℓ, hc⟩]
  calls k hk hc := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    exacts [hi.calls k hk hc, absurd hc hn]
  time := hi.time.trans (h.time_mono (Nat.le_succ j))
  phase := by
    rw [hi.phase]
    refine exists_congr fun j₀ => ⟨fun ⟨hj, hr⟩ => ⟨by omega, hr⟩, fun ⟨hj, e₀, hg, hp⟩ => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    exacts [⟨hj, e₀, hg, hp⟩, absurd (group_call' hg).1 hn]

private theorem phaseAfter_eq {e : Event A} : e.phaseAfter = .post ↔ 0 < e.phase := by
  cases e <;> simp [Event.phaseAfter, Event.phase]

private theorem eventOK (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {e : Event A} {cfg : Config A}
    (hi : GInv proposer dg tr y s₀ j cfg) (hg : tr.GroupAt proposer dg y j t e) :
    EventOK t (Phase.at cfg.time t cfg.phase) e := by
  obtain ⟨hc, ht⟩ := group_call' hg
  have hle : cfg.time ≤ t := ht ▸ hi.time
  have hpre (hp : e.phase ≤ 1) : Phase.at cfg.time t cfg.phase = .pre := by
    unfold Phase.at
    split_ifs with hlt
    · rfl
    cases hph : cfg.phase
    · rfl
    obtain ⟨j₀, hj₀, e₀, hg₀, hp₀⟩ := hi.phase.1 hph
    rw [le_antisymm hle (not_lt.1 hlt)] at hg₀
    have := h.phase_order y hy y hy j₀ j t e₀ e hg₀ hg hj₀ (.inl rfl)
    cases e <;> cases e₀ <;>
      simp only [Event.phase, Nat.reduceLeDiff, Nat.reduceLT] at hp hp₀ this
    apply absurd (h.tick_unique y hy j₀ j t _ _) (by omega)
    all_goals rw [RunTrace.tickAt_iff]; exact ⟨_, _, ‹_›⟩
  cases e with
  | tick x fgDue =>
    exact ⟨h.tick_public y hy j t ((RunTrace.tickAt_iff ..).2 ⟨x, fgDue, hg⟩),
      hpre (by simp [Event.phase])⟩
  | restart => exact hpre (by simp [Event.phase])
  | _ =>
    intro hpub
    obtain ⟨j₀, hg₀⟩ := h.tick_of_awake y hy t (ht ▸ h.time_nonneg j) hpub
      (ht ▸ h.awake_of_call y hy j hc)
    rw [RunTrace.tickAt_iff] at hg₀
    obtain ⟨x₀, f₀, hg₀⟩ := hg₀
    have hj₀ : j₀ < j := by
      rcases lt_trichotomy j₀ j with hlt | rfl | hgt
      · exact hlt
      · exact absurd (group_phase hg₀ hg) (by simp [Event.phase])
      · exact absurd (h.phase_order y hy y hy j j₀ t _ _ hg hg₀ hgt (.inl rfl))
          (by simp [Event.phase])
    have htc : cfg.time = t :=
      le_antisymm hle ((group_call' hg₀).2 ▸ hi.calls j₀ hj₀ (group_call' hg₀).1)
    simp only [htc, Phase.at, lt_self_iff_false, ↓reduceIte]
    exact hi.phase.2 ⟨j₀, hj₀, .tick x₀ f₀, htc ▸ hg₀, by simp [Event.phase]⟩

private theorem gInv_init (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) : GInv proposer dg tr y (ini y) 0 (Config.init A (ini y)) where
  reach := (congrFun (Node.reachable_eq proposer dg y (ini y)) _).mpr .refl
  st := (h.init y hy).symm
  calls k hk := absurd hk (Nat.not_lt_zero k)
  time := h.time_nonneg 0
  phase := by simp [Config.init]

private theorem gInv_nodeStep (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {e : Event A} {cfg : Config A}
    (hi : GInv proposer dg tr y s₀ j cfg) (hg : tr.GroupAt proposer dg y j t e) :
    Node.Step proposer dg y cfg e t
      ⟨(exec proposer dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ := by
  rw [Node.step_iff]
  exact ⟨(group_call' hg).2 ▸ hi.time, eventOK h hy hi hg, h.wire y hy j t e hg,
    by rw [hi.st], rfl, rfl⟩

private theorem gInv_step (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {t : Time} {e : Event A} {cfg : Config A}
    (hi : GInv proposer dg tr y s₀ j cfg) (hg : tr.GroupAt proposer dg y j t e) :
    GInv proposer dg tr y s₀ (j + (exec proposer dg y (tr.state y j) t e).2.length)
      ⟨(exec proposer dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ where
  reach := by
    have hr := (congrFun (Node.reachable_eq proposer dg y s₀) cfg).mp hi.reach
    exact (congrFun (Node.reachable_eq proposer dg y s₀) _).mpr
      (hr.tail ⟨e, t, gInv_nodeStep h hy hi hg⟩)
  st := (group_post h hy hg).symm
  calls k hk hc := by
    by_cases hkj : k < j
    · exact (hi.calls k hkj hc).trans ((group_call' hg).2 ▸ hi.time)
    · rw [RunTrace.groupAt_iff] at hg
      have := (hg.2.1 (k - j) (by omega)).2.1
      rw [Nat.add_sub_cancel' (not_lt.1 hkj)] at this
      exact this.le
  time := by
    rw [← (group_call' hg).2]
    exact h.time_mono (Nat.le_add_right _ _)
  phase := by
    simp only [phaseAfter_eq]
    have hlen := ((RunTrace.groupAt_iff ..).1 hg).1
    refine ⟨fun hp => ⟨j, Nat.lt_add_of_pos_right (List.length_pos_iff.2 hlen), e, hg, hp⟩, ?_⟩
    rintro ⟨j₀, hj₀, e₀, hg₀, hp₀⟩
    by_cases hlt : j₀ < j
    · exact lt_of_lt_of_le hp₀ (h.phase_order y hy y hy j₀ j t e₀ e hg₀ hg hlt (.inl rfl))
    · obtain rfl := group_start hg hg₀ (not_lt.1 hlt) hj₀
      exact group_phase hg₀ hg ▸ hp₀

private theorem gInv_exists (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) (j : Nat)
    (hb : ∀ j' t e, tr.GroupAt proposer dg y j' t e → j' < j →
      j' + (exec proposer dg y (tr.state y j') t e).2.length ≤ j) :
    ∃ cfg, GInv proposer dg tr y (ini y) j cfg := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases j with _ | i
  · exact ⟨_, gInv_init h hy⟩
  by_cases hc : tr.IsCall y i
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨j', e, hg⟩ := h.grouped y hy i c hc
    rw [RunTrace.inGroup_iff] at hg
    obtain ⟨hg, hj'i, hij'⟩ := hg
    obtain ⟨cfg, hcfg⟩ := ih j' (by omega) fun j'' t e hg'' hlt => by
      by_contra
      exact absurd (group_start hg'' hg hlt.le (by omega)) hlt.ne'
    have := hb j' _ e hg (by omega)
    rw [show i + 1 = j' + (exec proposer dg y (tr.state y j') (tr.time i) e).2.length by omega]
    exact ⟨_, gInv_step h hy hcfg hg⟩
  · obtain ⟨cfg, hcfg⟩ := ih i (by omega) fun j' t e hg hlt => by
      have := hb j' t e hg (by omega)
      by_contra
      rw [RunTrace.groupAt_iff] at hg
      have hk := hg.2.1 (i - j') (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at hk
      exact hc ⟨_, hk.1, hk.2.2.2.2⟩
    exact ⟨cfg, gInv_skip h hcfg hc⟩

/-- Each honest shadow group executes from a reachable node configuration. -/
theorem group_step' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {j : Nat} {t : Time} {e : Event A} (hg : tr.GroupAt proposer dg y j t e) :
    ∃ cfg : Config A, Node.Reachable' proposer dg y cfg (ini y) ∧ cfg.st = tr.state y j ∧
      Node.Step proposer dg y cfg e t
        ⟨(exec proposer dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ := by
  obtain ⟨cfg, hcfg⟩ := gInv_exists h hy j fun j' t' e' hg' hlt => by
    by_contra
    exact absurd (group_start hg' hg hlt.le (by omega)) hlt.ne'
  exact ⟨cfg, hcfg.reach, hcfg.st, gInv_nodeStep h hy hcfg hg⟩

private theorem onBlock_no_message (y : Fin P.n) (st : NodeState A) (t : Time)
    (B : A.Blk) {ℓ : ACLabel A} {m : A.Msg}
    (h : Cut.ac ℓ ∈ (onBlock y st t B).2) : ℓ.call ≠ .message m := by
  rw [onBlock_eq] at h
  split_ifs at h
  · simp at h
  · split at h <;> simp [acCall_eq] at h
    subst h
    simp

private theorem tickStep_no_message (y : Fin P.n) (st : NodeState A) (t : Time)
    (x : Nat) (s : TickStep) {ℓ : ACLabel A} {m : A.Msg}
    (h : Cut.ac ℓ ∈ (tickStep proposer dg y st t x s).2) : ℓ.call ≠ .message m := by
  cases s <;> simp only [tickStep_eq] at h
  case acTick =>
    simp only [acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    simp
  case proposal =>
    split_ifs at h
    · split at h
      · simp only [acProposal_eq, List.mem_singleton, Cut.ac.injEq] at h
        subst h
        simp
      · rcases List.mem_cons.1 h with h | h
        · simp only [acProposal_eq, Cut.ac.injEq] at h
          subst h
          simp
        · rw [proposeBlock_eq] at h
          exact onBlock_no_message _ _ _ _ h
    · simp at h
  case fgUpdate =>
    split at h
    · simp only [acToFG_eq, List.mem_singleton, Cut.ac.injEq] at h
      subst h
      simp
    · rcases List.mem_cons.1 h with h | h
      · simp only [acToFG_eq, Cut.ac.injEq] at h
        subst h
        simp
      · simp only [attest] at h
        split at h <;> simp at h

private theorem runSteps_no_message (y : Fin P.n) (st : NodeState A) (t : Time)
    (x : Nat) (steps : List TickStep) {ℓ : ACLabel A} {m : A.Msg}
    (h : Cut.ac ℓ ∈ (runSteps proposer dg y st t x steps).2) : ℓ.call ≠ .message m := by
  rw [runSteps_eq] at h
  have go : ∀ (steps : List TickStep) (acc : NodeState A × List (Cut A)),
      (Cut.ac ℓ ∈ acc.2 → ℓ.call ≠ .message m) →
      Cut.ac ℓ ∈ (steps.foldl (fun acc step =>
        let r := tickStep proposer dg y acc.1 t x step; (r.1, acc.2 ++ r.2)) acc).2 →
      ℓ.call ≠ .message m := by
    intro steps
    induction steps with
    | nil => exact fun _ h => h
    | cons s ss ih =>
      intro acc ha
      apply ih
      intro hm
      rcases List.mem_append.1 hm with hm | hm
      · exact ha hm
      · exact tickStep_no_message _ _ _ _ _ hm
  exact go steps (st, []) (by simp) h

private theorem exec_message (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {ℓ : ACLabel A} {m : A.Msg} (h : Cut.ac ℓ ∈ (exec proposer dg y st t e).2)
    (hm : ℓ.call = .message m) : e = .message m := by
  cases e <;> simp only [exec_eq] at h
  case message m' =>
    simp only [onMessage_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
    rfl
  case attestation a => simp [onAttestation] at h
  case restart =>
    simp only [restart_eq, acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  case block B => exact False.elim (onBlock_no_message y st t B h hm)
  case tick x f =>
    rw [onTick_eq] at h
    exact False.elim (runSteps_no_message y st t x _ h hm)

/-- A shadow AC message call belongs to delivery of that same message. -/
theorem msgCall_group' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel A} {m : A.Msg}
    (hc : tr.CallAt y i (.ac ℓ)) (hm : ℓ.call = .message m) :
    ∃ j, tr.GroupAt proposer dg y j (tr.time i) (.message m) := by
  obtain ⟨j, e, k, hg, -, hk⟩ := Coherence.call_in_group h hy hc
  obtain rfl := exec_message _ _ _ e (List.mem_of_getElem? hk) hm
  exact ⟨j, hg⟩

end Consensus.Goldilocks.Compose

end
