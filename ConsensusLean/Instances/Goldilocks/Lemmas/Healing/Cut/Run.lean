module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store

public section

/-! # Goldilocks Healing, HR.1: the FG states of the honest nodes of a run

Over a run (`Node.LocalRun`), the FG state of an honest node changes only at its accepted blocks
and processed attestations (`fg_step`; it is a reachable FG state, `Compose.fg_reachable`), its
`Σ.h_max` only grows (`hmax_mono`), its blocks other than genesis were accepted at earlier cuts
(`tree_accepted`) and its pool holds attestations processed at earlier cuts (`pool_processed`).

**The tick order at an `fg_attest` cut** (claims C0.4, F.5 (run)): the only FG cuts of a node at
the time of its tick and before its `fg_attest` are the acceptance of its own proposal, whose
attestations come from its pool at the start of the tick (restarts, the only earlier groups at
that time, make no FG cut: `Compose.before_tick`). So every honest attestation on a block that
a node holds at its `fg_attest` cut was signed at an earlier time (`signed_before_attest`). -/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A} {y : Fin P.n}

/-! ## Traces -/

/-- An FG cut leaves the AC state. -/
private theorem cutStep_fg_ac {t : Time} {st st' : NodeState A} {ℓ : FGLabel P A.Payload}
    (h : CutStep y t st (.fg ℓ) st') : st'.ac = st.ac := by
  rcases ℓ with ⟨B, _ | _⟩ | a | ⟨C, _ | a⟩
  · rw [h.2]
  · exact h.2.2.1
  · exact h.2.1
  · rw [h.2]
  · exact h.2.2

/-! ## The FG state of an honest node -/

/-- One cut of an honest node: its FG state stays, accepts a block, or processes an
attestation. -/
theorem fg_step (h : LocalRun dg H sg tr) (hy : y ∈ H) (m : Nat) :
    (tr.state y (m + 1)).fg = (tr.state y m).fg ∨
      (∃ B, tr.AcceptAt y m B ∧ (tr.state y m).fg.onBlock B = some (tr.state y (m + 1)).fg) ∨
      ∃ a, tr.AttCallAt y m a ∧
        (tr.state y (m + 1)).fg = (tr.state y m).fg.onAttestation a := by
  by_cases hc : tr.IsCall y m
  · obtain ⟨c, hc⟩ := hc
    rw [Trace.state_succ_of_call _ hc]
    have hs := h.cutLaw y hy m c hc
    rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
    · exact Or.inl (by rw [hs.2])
    · exact Or.inr (Or.inl ⟨B, hc, hs.2.1⟩)
    · exact Or.inr (Or.inr ⟨a, hc, hs.1⟩)
    · exact Or.inl (by rw [hs.2])
    · exact Or.inl hs.2.1
    · exact Or.inl hs.2.2.1
  · rw [Trace.state_succ_of_not _ fun c hc' => hc ⟨c, hc'⟩]
    exact Or.inl rfl

/-- `Σ.h_max` of an honest node only grows. -/
theorem hmax_mono (h : LocalRun dg H sg tr) (hy : y ∈ H) :
    Monotone fun m => (tr.state y m).fg.hmax := by
  refine monotone_nat_of_le_succ fun m => ?_
  rcases fg_step h hy m with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
  · rw [he]
  · obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlock_eq_some hB
    obtain ⟨atts, ha⟩ := Store.addAtts_eq (Store.updateFinality { (tr.state y m).fg with
      blocks := Function.update (tr.state y m).fg.blocks B.root (some B),
      σ := Function.update (tr.state y m).fg.σ B.root σ' } σ') B.fgPayload
    rw [he, ha, (Store.updateFinality_spec _ _).2.2.2.1]
    exact le_max_left _ _
  · obtain ⟨atts, ha⟩ := (tr.state y m).fg.onAttestation_eq a
    rw [he, ha]

/-- A block of an honest node's FG state is genesis or was accepted by it at an earlier cut. -/
theorem tree_accepted (h : LocalRun dg H sg tr) (hy : y ∈ H) {m : Nat} {B : A.Blk}
    (hB : B ∈ (tr.state y m).fg.tree) :
    B = P.genesisBlock A.genesisPayload ∨ ∃ k < m, tr.AcceptAt y k B := by
  induction m with
  | zero =>
    left
    change (tr.init y).fg.blocks B.root = some B at hB
    rw [h.init y hy] at hB
    change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
      some B at hB
    split_ifs at hB
    exact (Option.some.inj hB).symm
  | succ m ih =>
    have lift : B ∈ (tr.state y m).fg.tree →
        B = P.genesisBlock A.genesisPayload ∨ ∃ k < m + 1, tr.AcceptAt y k B := fun hB =>
      (ih hB).imp_right fun ⟨k, hk, hA⟩ => ⟨k, by omega, hA⟩
    rcases fg_step h hy m with he | ⟨B', hA, hB'⟩ | ⟨a, -, he⟩
    · exact lift (he ▸ hB)
    · obtain ⟨-, -, -, -, -, -, hb, -, -⟩ := Store.onBlock_fields hB'
      change (tr.state y (m + 1)).fg.blocks B.root = some B at hB
      rw [hb, Function.update_apply] at hB
      split_ifs at hB
      · cases hB
        exact Or.inr ⟨m, by omega, hA⟩
      · exact lift hB
    · refine lift ?_
      change (tr.state y m).fg.blocks B.root = some B
      rw [← (Store.onAttestation_fields _ a).1, ← he]
      exact hB

/-- An attestation in the pool of an honest node was processed by it at an earlier cut. -/
theorem pool_processed (h : LocalRun dg H sg tr) (hy : y ∈ H) {m : Nat} {a : FG.Att P.n}
    (ha : a ∈ (tr.state y m).fg.atts) : ∃ k < m, tr.ProcessAttAt y k a := by
  induction m with
  | zero =>
    change a ∈ (tr.init y).fg.atts at ha
    rw [h.init y hy] at ha
    cases ha
  | succ m ih =>
    have lift : a ∈ (tr.state y m).fg.atts → ∃ k < m + 1, tr.ProcessAttAt y k a := fun ha =>
      let ⟨k, hk, hp⟩ := ih ha
      ⟨k, by omega, hp⟩
    rcases fg_step h hy m with he | ⟨B, hA, hB⟩ | ⟨b, hb, he⟩
    · exact lift (he ▸ ha)
    · rcases (Store.onBlock_fields hB).choose_spec.choose_spec.2.2.2.2.2.2 a ha with ha | ha
      · exact lift ha
      · exact ⟨m, by omega, Or.inr ⟨B, hA, ha⟩⟩
    · rw [he] at ha
      rcases (Store.onAttestation_fields _ b).2.2 a ha with ha | rfl
      · exact lift ha
      · exact ⟨m, by omega, Or.inl hb⟩

/-- A signing of the FG projection is a signing of the run. -/
theorem signAt_of_projFG {v : Fin P.n} {j : Nat} {a : FG.Att P.n} (hs : tr.projFG.SignAt v j a) :
    tr.SignAt v j a := by
  obtain ⟨src, hn, hl⟩ := hs
  refine ⟨src, hn, ?_⟩
  obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hl
  rw [hc]
  rcases c with ℓ | ℓ
  · cases hc'
    rfl
  · cases hc'

/-! ## The tick order at an `fg_attest` cut -/

/-- Only a tick makes an `fg_attest` cut. -/
theorem eq_tick_of_attest_mem {st : NodeState A} {t : Time} {e : Event A} {C : A.Blk}
    {s : Option (FG.Att P.n)} (h : Cut.fg (.attest C s) ∈ (exec dg y st t e).2) :
    ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | block B =>
    simp only [exec, Node.onBlock] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp [acCall] at h
  | message m => simp [exec, onMessage, acCall] at h
  | attestation a => simp [exec, Node.onAttestation] at h
  | restart => simp [exec, restart, acCall] at h

/-- The only block that `on_block(B')` processes is `B'`. -/
private theorem onBlock_cuts {st : NodeState A} {t : Time} {B B' : A.Blk} {acc : Bool}
    (h : Cut.fg (.block B acc) ∈ (Node.onBlock y st t B').2) : B = B' := by
  unfold Node.onBlock at h
  by_cases hs : P.slotOf t < B'.slot
  · simp [hs] at h
  · rcases ho : st.fg.onBlock B' with _ | fg' <;> simp [hs, ho, acCall] at h <;> exact h.1

/-- The only block a tick processes is the own proposal, whose attestations come from the pool
at the start of the tick. -/
theorem tick_block_payload {st : NodeState A} {t : Time} {x : Nat} {B : A.Blk} {acc : Bool}
    (h : Cut.fg (.block B acc) ∈ (onTick dg y st t x).2) : ∀ a ∈ B.fgPayload, a ∈ st.fg.atts := by
  simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil, List.nil_append,
    List.mem_append] at h
  rcases h with (h | h) | h
  · simp [tickStep, acCall] at h
  · simp only [tickStep] at h
    split_ifs at h
    · split at h
      · simp [acProposal] at h
      · simp only [acProposal, List.mem_cons, reduceCtorEq, false_or, proposeBlock] at h
        rw [onBlock_cuts h]
        intro a ha
        exact (List.mem_filter.1 ha).1
    · simp at h
  · simp only [tickStep] at h
    split at h
    · simp [acToFG] at h
    · simp only [acToFG, List.mem_cons, reduceCtorEq, false_or, attest] at h
      split at h <;> simp [Node.onAttestation] at h

/-- An `fg_attest` cut lies in a tick, after the earlier cuts of that tick. -/
theorem tick_of_attest (h : LocalRun dg H sg tr) (hy : y ∈ H) {k : Nat} {C : A.Blk}
    {s : Option (FG.Att P.n)} (hc : tr.CallAt y k (.fg (.attest C s))) :
    ∃ j₀ ≤ k, ∃ x, tr.GroupAt dg y j₀ (tr.time k) (.tick x) ∧ ∀ i, j₀ ≤ i → i ≤ k →
      ∃ c ∈ (onTick dg y (tr.state y j₀) (tr.time k) x).2, tr.label i = some c := by
  obtain ⟨j₀, e, hg, hjk, hkj⟩ := h.grouped y hy k _ hc
  have hl : ∀ i, j₀ ≤ i → i ≤ k →
      ∃ c ∈ (exec dg y (tr.state y j₀) (tr.time k) e).2, tr.label i = some c := by
    intro i hi hik
    have hk := (hg.2.1 (i - j₀) (by omega)).2.2.2.2
    rw [Nat.add_sub_cancel' hi] at hk
    exact ⟨_, List.getElem_mem _, hk⟩
  obtain ⟨c, hcm, hck⟩ := hl k hjk le_rfl
  rw [hc.2] at hck
  cases hck
  obtain ⟨x, rfl⟩ := eq_tick_of_attest_mem hcm
  exact ⟨j₀, hjk, x, hg, hl⟩

/-- **The honest attestations on a block held at an `fg_attest` cut were signed before its
time.** -/
theorem signed_before_attest (h : LocalRun dg H sg tr) (hy : y ∈ H) {k : Nat} {C : A.Blk}
    {s : Option (FG.Att P.n)} (hc : tr.CallAt y k (.fg (.attest C s))) {Y : A.Blk}
    (hY : Y ∈ (tr.state y k).fg.tree) {a : FG.Att P.n} (ha : a ∈ Y.fgPayload) (haH : a.val ∈ H) :
    ∃ j, tr.SignAt a.val j a ∧ tr.time j < tr.time k := by
  rcases tree_accepted h hy hY with rfl | ⟨i, hik, hA⟩
  · cases ha
  obtain ⟨j, hji, hj⟩ := h.att_unforgeable y hy i a (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) haH
  by_cases hlt : tr.time i < tr.time k
  · exact ⟨j, hj, lt_of_le_of_lt (h.time_mono hji.le) hlt⟩
  have hti : tr.time i = tr.time k := le_antisymm (h.time_mono hik.le) (not_lt.1 hlt)
  obtain ⟨j₀, hj₀k, x, ht, hl⟩ := tick_of_attest h hy hc
  have nfg : ∀ m < j₀, ∀ ℓ, tr.CallAt y m (.fg ℓ) → tr.time m = tr.time k → False :=
    fun m hm ℓ hcm htm => by
      obtain ⟨ℓ', he, -⟩ := Compose.before_tick h hy ⟨x, ht⟩ hcm hm htm
      cases he
  rcases lt_or_ge i j₀ with hij₀ | hij₀
  · exact (nfg i hij₀ _ hA hti).elim
  obtain ⟨c, hcm, hci⟩ := hl i hij₀ hik.le
  rw [hA.2] at hci
  cases hci
  obtain ⟨m, hmj₀, hm⟩ := pool_processed h hy (tick_block_payload hcm a ha)
  obtain ⟨j', hj'm, hj'⟩ := h.att_unforgeable y hy m a
    (hm.imp_right fun ⟨B, hB, haB⟩ => ⟨B, ⟨true, hB⟩, haB⟩) haH
  -- `a` was in the pool at the start of the tick, so processed and signed before it
  have htm : tr.time m < tr.time k := by
    refine lt_of_le_of_ne (h.time_mono (by omega)) fun htm => ?_
    rcases hm with hm | ⟨B, hB, -⟩
    · exact nfg m hmj₀ _ hm htm
    · exact nfg m hmj₀ _ hB htm
  exact ⟨j', hj', lt_of_le_of_lt (h.time_mono hj'm.le) htm⟩

end Consensus.Goldilocks.Healing

end
