module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Node

public section

/-! # Goldilocks runs: the honest states are reachable node configurations

The cuts of a group are the handler's cuts at consecutive indices, and each obeys the cut law,
which is deterministic, so the state after a group is the handler's result. The groups of an
honest node, in index order, are then the events of a `Node.Reachable` path: their times do not
decrease, and the phase law of the run (restarts, then the tick, then deliveries at each time; one
tick per time; a tick at every public time the node is awake at) is `Node.EventOK`. -/

/-! ### Traces -/

namespace Consensus.Goldilocks.Trace

variable {N S L : Type} (tr : Trace N S L)

theorem state_succ_of_call {y : N} {k : Nat} {ℓ : L} (hc : tr.CallAt y k ℓ) :
    tr.state y (k + 1) = tr.post k := by
  simp [Trace.state, hc.1, hc.2]

theorem state_succ_of_not {y : N} {k : Nat} (hn : ∀ ℓ, ¬ tr.CallAt y k ℓ) :
    tr.state y (k + 1) = tr.state y k := by
  rw [Trace.state]
  split_ifs with h
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 h.2
    exact absurd ⟨h.1, hℓ⟩ (hn ℓ)
  · rfl

end Consensus.Goldilocks.Trace

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}

/-! ### The cut law is deterministic -/

private theorem cutStep_unique {y : Fin P.n} {t : Time} {st st₁ st₂ : NodeState A} {c : Cut A}
    (h₁ : CutStep y t st c st₁) (h₂ : CutStep y t st c st₂) : st₁ = st₂ := by
  obtain ⟨fg₁, ac₁, r₁⟩ := st₁
  obtain ⟨fg₂, ac₂, r₂⟩ := st₂
  cases c with
  | ac ℓ =>
    obtain ⟨-, e₁, h₁, h₁'⟩ := h₁
    obtain ⟨-, e₂, h₂, h₂'⟩ := h₂
    have := (Prod.mk.inj (e₁.symm.trans e₂)).1
    simp_all
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | true =>
        obtain ⟨-, e₁, h₁, h₁'⟩ := h₁
        obtain ⟨-, e₂, h₂, h₂'⟩ := h₂
        have := Option.some.inj (e₁.symm.trans e₂)
        simp_all
      | false => exact h₁.2.trans h₂.2.symm
    | attestation a =>
      obtain ⟨e₁, h₁, h₁'⟩ := h₁
      obtain ⟨e₂, h₂, h₂'⟩ := h₂
      simp_all
    | attest C s =>
      cases s with
      | none => exact h₁.2.trans h₂.2.symm
      | some a =>
        obtain ⟨e₁, h₁, h₁'⟩ := h₁
        obtain ⟨e₂, h₂, h₂'⟩ := h₂
        have := (Prod.mk.inj (Option.some.inj (e₁.symm.trans e₂))).2
        simp_all

/-- **Cut chains are deterministic.** -/
theorem cutChain_unique {y : Fin P.n} {t : Time} {st st₁ st₂ : NodeState A} {cs : List (Cut A)}
    (h₁ : CutChain y t st cs st₁) (h₂ : CutChain y t st cs st₂) : st₁ = st₂ := by
  induction h₁ generalizing st₂ with
  | nil => cases h₂; rfl
  | cons hs _ ih =>
    cases h₂ with
    | cons hs' h' => exact ih (cutStep_unique hs hs' ▸ h')

/-! ### The first cut of an event names its phase -/

/-- The phase of the event a cut can start: a restart, a tick (both start with their AC call),
or a delivery. -/
private def Cut.phase : Cut A → Nat
  | .ac ℓ => match ℓ.call with
    | .restart => 0
    | .tick => 1
    | _ => 2
  | .fg _ => 2

private theorem exec_head (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) :
    ∀ c ∈ (exec dg y st t e).2.head?, Cut.phase c = e.phase := by
  cases e with
  | block B =>
    simp only [exec, onBlock]
    split_ifs
    · simp
    · cases st.fg.onBlock B <;> simp [Cut.phase, Event.phase]
  | _ => simp [exec, onTick, runSteps, tickSteps, tickStep, onMessage, onAttestation, restart,
      acCall, Cut.phase, Event.phase]

variable {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-! ### Groups -/

private theorem group_call {y : Fin P.n} {j : Nat} {t : Time} {e : Event A}
    (hg : tr.GroupAt dg y j t e) : tr.IsCall y j ∧ tr.time j = t := by
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 0 (List.length_pos_iff.2 hg.1)
  simp only [Nat.add_zero] at hn ht hl
  exact ⟨⟨_, hn, hl⟩, ht⟩

/-- Two groups of one node starting at one cut have events of one phase. -/
private theorem group_phase {y : Fin P.n} {j : Nat} {t t' : Time} {e e' : Event A}
    (hg : tr.GroupAt dg y j t e) (hg' : tr.GroupAt dg y j t' e') : e.phase = e'.phase := by
  have h₀ := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.2
  have h₀' := (hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).2.2.2.2
  have htt : t = t' := (group_call hg).2.symm.trans (group_call hg').2
  subst htt
  rw [h₀'] at h₀
  have mem {l : List (Cut A)} (h : l ≠ []) : l[0]'(List.length_pos_iff.2 h) ∈ l.head? := by
    cases l
    · exact absurd rfl h
    · rfl
  rw [← exec_head dg y (tr.state y j) t e _ (mem hg.1),
    ← exec_head dg y (tr.state y j) t e' _ (mem hg'.1), Option.some.inj h₀]

/-- A group of `y` starts at no cut strictly inside another group. -/
private theorem group_start {y y' : Fin P.n} {j j' : Nat} {t t' : Time} {e e' : Event A}
    (hg : tr.GroupAt dg y j t e) (hg' : tr.GroupAt dg y' j' t' e') (h₁ : j ≤ j')
    (h₂ : j' < j + (exec dg y (tr.state y j) t e).2.length) : j' = j := by
  have := (hg.2.1 (j' - j) (by omega)).2.2.1
  rw [Nat.add_sub_cancel' h₁] at this
  exact le_antisymm (hg'.2.2 j this.symm).1 h₁

/-- A cut chain recorded at consecutive cuts of `y` from `j` ends, in the run, at its last
state. -/
theorem cutChain_run (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {t : Time}
    {st st' : NodeState A} {cs : List (Cut A)} (hch : CutChain y t st cs st') :
    ∀ j, tr.state y j = st →
      (∀ k (hk : k < cs.length), tr.node (j + k) = y ∧ tr.time (j + k) = t ∧
        tr.label (j + k) = some cs[k]) →
      tr.state y (j + cs.length) = st' := by
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

/-- The state after a group is the handler's result. -/
private theorem group_post (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {j : Nat} {t : Time} {e : Event A} (hg : tr.GroupAt dg y j t e) :
    tr.state y (j + (exec dg y (tr.state y j) t e).2.length) = (exec dg y (tr.state y j) t e).1 ∧
      tr.post (j + (exec dg y (tr.state y j) t e).2.length - 1) =
        (exec dg y (tr.state y j) t e).1 := by
  have hs := cutChain_run h hy (exec_is_cut_chain dg y (tr.state y j) t e) j rfl fun k hk =>
    ⟨(hg.2.1 k hk).1, (hg.2.1 k hk).2.1, (hg.2.1 k hk).2.2.2.2⟩
  refine ⟨hs, ?_⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (List.length_pos_iff.2 hg.1).ne'
  have hlast := hg.2.1 n (by omega)
  have hc : tr.CallAt y (j + n) _ := ⟨hlast.1, hlast.2.2.2.2⟩
  rw [hn, show j + n.succ - 1 = j + n by omega]
  rw [hn, show j + n.succ = j + n + 1 by omega, tr.state_succ_of_call hc] at hs
  exact hs

/-! ### The configuration of a node before a cut -/

/-- `cfg` is a reachable configuration of `y` for the cut `j`: its state is `y`'s before `j`,
its clock is at or after every earlier call of `y` and at or before cut `j`, and it is in phase
`post` exactly when a group of `y` before `j` at its clock is not a restart. -/
private structure GInv (dg : Digest (List (FG.Att P.n)) A.Payload) (tr : RunTrace A)
    (y : Fin P.n) (j : Nat) (cfg : Config A) : Prop where
  reach : Reachable dg y cfg
  st : cfg.st = tr.state y j
  calls : ∀ k < j, tr.IsCall y k → tr.time k ≤ cfg.time
  time : cfg.time ≤ tr.time j
  phase : cfg.phase = .post ↔ ∃ j₀ < j, ∃ e₀, tr.GroupAt dg y j₀ cfg.time e₀ ∧ 0 < e₀.phase

private theorem gInv_skip (h : Node.LocalRun dg H sg tr) {y : Fin P.n} {j : Nat}
    {cfg : Config A} (hi : GInv dg tr y j cfg) (hn : ¬ tr.IsCall y j) :
    GInv dg tr y (j + 1) cfg where
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
    exacts [⟨hj, e₀, hg, hp⟩, absurd (group_call hg).1 hn]

private theorem phaseAfter_eq {e : Event A} : e.phaseAfter = .post ↔ 0 < e.phase := by
  cases e <;> simp [Event.phaseAfter, Event.phase]

/-- The event of a group may run from the configuration of its first cut. -/
private theorem eventOK (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {t : Time} {e : Event A} {cfg : Config A} (hi : GInv dg tr y j cfg)
    (hg : tr.GroupAt dg y j t e) : EventOK t (Phase.at cfg.time t cfg.phase) e := by
  obtain ⟨hc, ht⟩ := group_call hg
  have hle : cfg.time ≤ t := ht ▸ hi.time
  -- a tick or a restart: the earlier groups of `y` at `t` are restarts
  have hpre (hp : e.phase ≤ 1) : Phase.at cfg.time t cfg.phase = .pre := by
    unfold Phase.at
    split_ifs with hlt
    · rfl
    cases hph : cfg.phase
    · rfl
    obtain ⟨j₀, hj₀, e₀, hg₀, hp₀⟩ := hi.phase.1 hph
    rw [le_antisymm hle (not_lt.1 hlt)] at hg₀
    have := h.phase_order y hy y hy j₀ j t e₀ e hg₀ hg hj₀
    cases e <;> cases e₀ <;> simp_all [Event.phase]
    exact absurd (h.tick_unique y hy j₀ j t hg₀ hg) (by omega)
  cases e with
  | tick => exact ⟨h.tick_public y hy j t hg, hpre (by simp [Event.phase])⟩
  | restart => exact hpre (by simp [Event.phase])
  | _ =>
    -- a delivery at a public time: the tick of `t` ran before
    intro hpub
    obtain ⟨j₀, hg₀⟩ := h.tick_of_awake y hy t (ht ▸ h.time_nonneg j) hpub
      (ht ▸ h.awake_of_call y hy j hc)
    have hj₀ : j₀ < j := by
      rcases lt_trichotomy j₀ j with hlt | rfl | hgt
      · exact hlt
      · exact absurd (group_phase hg₀ hg) (by simp [Event.phase])
      · exact absurd (h.phase_order y hy y hy j j₀ t _ _ hg hg₀ hgt) (by simp [Event.phase])
    have htc : cfg.time = t :=
      le_antisymm hle ((group_call hg₀).2 ▸ hi.calls j₀ hj₀ (group_call hg₀).1)
    simp only [htc, Phase.at, lt_self_iff_false, ↓reduceIte]
    exact hi.phase.2 ⟨j₀, hj₀, .tick, htc ▸ hg₀, by simp [Event.phase]⟩

private theorem gInv_init (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) :
    GInv dg tr y 0 (Config.init A) where
  reach := Relation.ReflTransGen.refl
  st := (h.init y hy).symm
  calls k hk := absurd hk (Nat.not_lt_zero k)
  time := h.time_nonneg 0
  phase := by simp [Config.init]

/-- The event of a group is one `Node.Step` from the configuration of its first cut. -/
private theorem gInv_nodeStep (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {t : Time} {e : Event A} {cfg : Config A} (hi : GInv dg tr y j cfg)
    (hg : tr.GroupAt dg y j t e) :
    Node.Step dg y cfg e t ⟨(exec dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ :=
  ⟨(group_call hg).2 ▸ hi.time, eventOK h hy hi hg, h.wire y hy j t e hg, by rw [hi.st], rfl, rfl⟩

/-- The configuration after a group: one `Node.Step` by its event. -/
private theorem gInv_step (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {t : Time} {e : Event A} {cfg : Config A} (hi : GInv dg tr y j cfg)
    (hg : tr.GroupAt dg y j t e) :
    GInv dg tr y (j + (exec dg y (tr.state y j) t e).2.length)
      ⟨(exec dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ where
  reach := hi.reach.tail ⟨e, t, gInv_nodeStep h hy hi hg⟩
  st := (group_post h hy hg).1.symm
  calls k hk hc := by
    by_cases hkj : k < j
    · exact (hi.calls k hkj hc).trans ((group_call hg).2 ▸ hi.time)
    · have := (hg.2.1 (k - j) (by omega)).2.1
      rw [Nat.add_sub_cancel' (not_lt.1 hkj)] at this
      exact this.le
  time := by
    rw [← (group_call hg).2]
    exact h.time_mono (Nat.le_add_right _ _)
  phase := by
    simp only [phaseAfter_eq]
    refine ⟨fun hp => ⟨j, Nat.lt_add_of_pos_right (List.length_pos_iff.2 hg.1), e, hg, hp⟩, ?_⟩
    rintro ⟨j₀, hj₀, e₀, hg₀, hp₀⟩
    by_cases hlt : j₀ < j
    · exact lt_of_lt_of_le hp₀ (h.phase_order y hy y hy j₀ j t e₀ e hg₀ hg hlt)
    · obtain rfl := group_start hg hg₀ (not_lt.1 hlt) hj₀
      exact group_phase hg₀ hg ▸ hp₀

/-- A cut that no group of `y` straddles has a configuration. -/
private theorem gInv_exists (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) (j : Nat)
    (hb : ∀ j' t e, tr.GroupAt dg y j' t e → j' < j →
      j' + (exec dg y (tr.state y j') t e).2.length ≤ j) :
    ∃ cfg, GInv dg tr y j cfg := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases j with _ | i
  · exact ⟨_, gInv_init h hy⟩
  by_cases hc : tr.IsCall y i
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨j', e, hg, hj'i, hij'⟩ := h.grouped y hy i c hc
    obtain ⟨cfg, hcfg⟩ := ih j' (by omega) fun j'' t e hg'' hlt => by
      by_contra
      exact absurd (group_start hg'' hg hlt.le (by omega)) hlt.ne'
    have := hb j' _ e hg (by omega)
    rw [show i + 1 = j' + (exec dg y (tr.state y j') (tr.time i) e).2.length by omega]
    exact ⟨_, gInv_step h hy hcfg hg⟩
  · obtain ⟨cfg, hcfg⟩ := ih i (by omega) fun j' t e hg hlt => by
      have := hb j' t e hg (by omega)
      by_contra
      have hk := hg.2.1 (i - j') (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at hk
      exact hc ⟨_, hk.1, hk.2.2.2.2⟩
    exact ⟨cfg, gInv_skip h hcfg hc⟩

/-- **The event of an honest group is a step of the node** from a reachable configuration
whose state is the state before the group. -/
theorem group_step (h : Node.LocalRun dg H sg tr) {y : Fin P.n} (hy : y ∈ H) {j : Nat}
    {t : Time} {e : Event A} (hg : tr.GroupAt dg y j t e) :
    ∃ cfg : Config A, Reachable dg y cfg ∧ cfg.st = tr.state y j ∧
      Node.Step dg y cfg e t ⟨(exec dg y (tr.state y j) t e).1, t, e.phaseAfter⟩ := by
  obtain ⟨cfg, hcfg⟩ := gInv_exists h hy j fun j' t' e' hg' hlt => by
    by_contra
    exact absurd (group_start hg' hg hlt.le (by omega)) hlt.ne'
  exact ⟨cfg, hcfg.reach, hcfg.st, gInv_nodeStep h hy hcfg hg⟩

/-- **The honest states of a run are reachable configurations.** -/
theorem group_states_reachable : GroupStatesReachable := by
  intro P A dg H sg tr h y hy j t e hg
  obtain ⟨cfg, hr, hst, hs⟩ := group_step h hy hg
  exact ⟨⟨cfg, hr, hst, hs.1⟩, _, hr.tail ⟨e, t, hs⟩, (group_post h hy hg).2.symm, rfl⟩

end Consensus.Goldilocks.Compose

end
