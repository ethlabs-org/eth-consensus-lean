module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers

public section

/-! # Goldilocks Compose/AnyAC: the components' states at a node (C0.1, C0.2, C0.5)

Along the cut chain of every handler the FG state takes only FG store steps, so it stays
reachable, its tree only grows and `Σ.F` moves only to descendants (FGStore part 1). The AC state
is reachable inside the current tree, with the current frame: each AC call obeys the call law,
since the frame is well formed (G0.4 (height)), equal between calls except for an accepted block,
which is a frame step (`AcceptIsFrameStep`), and the inputs pass their checks (the wire, or
requirement 5 for the own block). The record is the client run over the entry states of the
sources, and each signed attestation enters the pool at once. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-! ### The FG state along cuts -/

/-- One cut from a reachable FG state: the FG state stays reachable, its tree grows and its
finalized tip moves to a descendant. -/
private theorem step_fg {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') (hr : st.fg.Reachable A.genesisPayload) :
    st'.fg.Reachable A.genesisPayload ∧ st.fg.tree ⊆ st'.fg.tree ∧
      st'.fg.Anc st.fg.F st'.fg.F := by
  have same : st'.fg = st.fg → st'.fg.Reachable A.genesisPayload ∧ st.fg.tree ⊆ st'.fg.tree ∧
      st'.fg.Anc st.fg.F st'.fg.F := fun he => by
    rw [he]; exact ⟨hr, subset_rfl, .refl⟩
  cases c with
  | ac ℓ => exact same h.2.2.1
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | true =>
        obtain ⟨-, hb, -, -⟩ := h
        refine ⟨hr.tail (Or.inl ⟨B, hb⟩), ?_, (Store.finalized_monotone P _ _ _ hr).1 B _ hb⟩
        rw [(Store.tree_grows P _ _ _ hr).1 B _ hb]
        exact Set.subset_insert _ _
      | false => obtain ⟨-, rfl⟩ := h; exact same rfl
    | attestation a =>
      obtain ⟨he, -, -⟩ := h
      rw [he, (Store.finalized_monotone P _ _ _ hr).2 a, (Store.tree_grows P _ _ _ hr).2 a]
      exact ⟨hr.tail (Or.inr ⟨a, rfl⟩), subset_rfl, .refl⟩
    | attest C s =>
      cases s with
      | none => obtain ⟨-, rfl⟩ := h; exact same rfl
      | some a => exact same h.2.1

/-- Along a cut chain from a reachable FG state: the FG state stays reachable, its tree grows
and its finalized tip moves to a descendant. -/
theorem chain_fg {t : Time} {st st' : NodeState A} {cs : List (Cut A)}
    (h : CutChain self t st cs st') (hr : st.fg.Reachable A.genesisPayload) :
    st'.fg.Reachable A.genesisPayload ∧ st.fg.tree ⊆ st'.fg.tree ∧
      st'.fg.Anc st.fg.F st'.fg.F := by
  induction h with
  | nil => exact ⟨hr, subset_rfl, .refl⟩
  | cons hs _ ih =>
    obtain ⟨hr₁, hT₁, hF₁⟩ := step_fg self hs hr
    obtain ⟨hr', hT', hF'⟩ := ih hr₁
    exact ⟨hr', hT₁.trans hT', (Anc.mono hT' hF₁).trans hF'⟩

/-- One event from a reachable FG state. -/
theorem exec_fg (st : NodeState A) (t : Time) (e : Event A)
    (hr : st.fg.Reachable A.genesisPayload) :
    (exec dg self st t e).1.fg.Reachable A.genesisPayload ∧
      st.fg.tree ⊆ (exec dg self st t e).1.fg.tree ∧
      (exec dg self st t e).1.fg.Anc st.fg.F (exec dg self st t e).1.fg.F :=
  chain_fg self (exec_is_cut_chain dg self st t e) hr

/-- **C0.5 (c), the FG.** -/
theorem fg_states_reachable : FGStatesReachable dg self := by
  intro cfg h
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨e, t', -, -, -, hst, -, -⟩ := hs
    rw [hst]
    exact (exec_fg dg self _ t' e ih).1

/-- **C0.2.** -/
theorem finalized_monotone : FinalizedMonotone dg self := by
  intro cfg cfg' hr h
  induction h with
  | refl => exact .refl
  | @tail c₁ c₂ h₁ hs ih =>
    obtain ⟨e, t', -, -, -, hst, -, -⟩ := hs
    have hr₁ := fg_states_reachable dg self c₁ (hr.trans h₁)
    obtain ⟨-, hT, hF⟩ := exec_fg dg self c₁.st t' e hr₁
    rw [hst]
    exact (Anc.mono hT ih).trans hF

/-! ### The AC state and the record, handler by handler -/

/-- The node invariant at a state for calls at time `t`: the FG state is reachable; under the
requirements, the AC state is reachable inside the tree with the current frame, by a last call
not after `t`; the record is the client run over some entry states, whose attestations are in
the pool. -/
private def NInv (st : NodeState A) (t : Time) : Prop :=
  st.fg.Reachable A.genesisPayload ∧
  (A.Requirements → ∃ t₀ ≤ t, A.ReachableAt self st.fg.tree st.ac (frame st) t₀) ∧
  ∃ σes : List (FG.ChainState P.n), st.record = (FG.Record.run self FG.Record.empty σes).1 ∧
    ∀ a ∈ (FG.Record.run self FG.Record.empty σes).2, a ∈ st.fg.atts

private theorem frameIn_store {st : NodeState A} (hr : st.fg.Reachable A.genesisPayload) :
    A.FrameIn st.fg.tree (frame st) :=
  ⟨(Store.frame_realization P _ _ _ hr).1, fun _ h => h.1⟩

private theorem reachableAt_mono {U U' : Set A.Blk} (hUU : U ⊆ U') {s : A.State} {Φ : A.Frm}
    {t : Time} (h : A.ReachableAt self U s Φ t) : A.ReachableAt self U' s Φ t := by
  induction h with
  | init Φ hi hin => exact .init Φ hi ⟨hin.1, hin.2.trans hUU⟩
  | step c _ ht hok ih => exact .step c ih ht ⟨⟨hok.1.1, hok.1.2.trans hUU⟩, hok.2⟩

private theorem atts_onAttestation (fg : Store P A.Payload) (a : FG.Att P.n) :
    a ∈ (fg.onAttestation a).atts ∧ fg.atts ⊆ (fg.onAttestation a).atts := by
  unfold Store.onAttestation
  split_ifs with h
  · exact ⟨h, fun _ h => h⟩
  · exact ⟨by simp, List.subset_append_left _ _⟩

private theorem atts_addAtts (fg : Store P A.Payload) (l : List (FG.Att P.n)) :
    fg.atts ⊆ (fg.addAtts l).atts := by
  induction l generalizing fg with
  | nil => exact fun _ h => h
  | cons a l ih =>
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts]
    exact fun b hb => ih _ ((atts_onAttestation fg a).2 hb)

private theorem atts_onBlock {fg fg' : Store P A.Payload} {B : A.Blk}
    (h : fg.onBlock B = some fg') : fg.atts ⊆ fg'.atts := by
  obtain ⟨-, σ', -, -, -, -, -, rfl⟩ := Store.onBlock_eq_some h
  intro a ha
  refine atts_addAtts _ _ ?_
  rw [(Store.updateFinality_spec _ _).2.2.1]
  exact ha

/-- A client run that signs at its last entry state. -/
private theorem run_append (v : Fin P.n) :
    ∀ (Λ : FG.Record) (σes : List (FG.ChainState P.n)) (σe : FG.ChainState P.n)
      (a : FG.Att P.n) (Λ' : FG.Record),
      (FG.Record.run v Λ σes).1.createAtt v σe = some (a, Λ') →
      FG.Record.run v Λ (σes ++ [σe]) = (Λ', (FG.Record.run v Λ σes).2 ++ [a]) := by
  intro Λ σes
  induction σes generalizing Λ with
  | nil =>
    intro σe a Λ' h
    simp only [FG.Record.run] at h ⊢
    simp [FG.Record.run, h]
  | cons x rest ih =>
    intro σe a Λ' h
    simp only [List.cons_append, FG.Record.run] at h ⊢
    cases hx : Λ.createAtt v x with
    | none =>
      simp only [hx] at h ⊢
      exact ih Λ σe a Λ' h
    | some q =>
      obtain ⟨b, Λ₁⟩ := q
      simp only [hx] at h ⊢
      rw [ih Λ₁ σe a Λ' h]
      simp

private theorem NInv.mono {st : NodeState A} {t t' : Time} (h : NInv self st t) (ht : t ≤ t') :
    NInv self st t' :=
  ⟨h.1, fun hq => (h.2.1 hq).imp fun _ h => ⟨h.1.trans ht, h.2⟩, h.2.2⟩

private theorem NInv.acCall {st : NodeState A} {t : Time} (h : NInv self st t) (c : A.Call)
    (hc : A.CallOK st.fg.tree (frame st) t c (frame st)) :
    NInv self (acCall self st t c).1 t := by
  obtain ⟨hr, hac, hrec⟩ := h
  refine ⟨hr, fun hq => ?_, hrec⟩
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  exact ⟨t, le_rfl, .step c hR ht₀ hc⟩

private theorem NInv.acProposal {st : NodeState A} {t : Time} (h : NInv self st t) :
    NInv self (Node.acProposal st t).1 t := by
  obtain ⟨hr, hac, hrec⟩ := h
  refine ⟨hr, fun hq => ?_, hrec⟩
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  exact ⟨t, le_rfl, .step .proposal hR ht₀ ⟨frameIn_store hr, rfl⟩⟩

private theorem NInv.acToFG {st : NodeState A} {t : Time} (h : NInv self st t) :
    NInv self (Node.acToFG st t).1 t := by
  obtain ⟨hr, hac, hrec⟩ := h
  refine ⟨hr, fun hq => ?_, hrec⟩
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  exact ⟨t, le_rfl, .step .toFG hR ht₀ ⟨frameIn_store hr, rfl⟩⟩

/-- Processing an attestation keeps the invariant and puts the attestation in the pool. -/
private theorem NInv.fgAtt {st : NodeState A} {t : Time} (h : NInv self st t) (a : FG.Att P.n)
    (Λ : FG.Record)
    (hrec : ∃ σes : List (FG.ChainState P.n), Λ = (FG.Record.run self FG.Record.empty σes).1 ∧
      ∀ b ∈ (FG.Record.run self FG.Record.empty σes).2, b ∈ (st.fg.onAttestation a).atts) :
    NInv self { st with fg := st.fg.onAttestation a, record := Λ } t := by
  obtain ⟨hr, hac, -⟩ := h
  have htree := (Store.tree_grows P _ _ _ hr).2 a
  have hfr := (Store.accept_is_frame_step P _ _ _ hr).2 a
  refine ⟨hr.tail (Or.inr ⟨a, rfl⟩), fun hq => ?_, hrec⟩
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  refine ⟨t₀, ht₀, ?_⟩
  change A.ReachableAt self (st.fg.onAttestation a).tree st.ac (st.fg.onAttestation a).toFrame t₀
  rw [htree, hfr]
  exact hR

private theorem NInv.onAttestation {st : NodeState A} {t : Time} (h : NInv self st t)
    (a : FG.Att P.n) : NInv self (onAttestation st a).1 t := by
  obtain ⟨σes, hrec, hsub⟩ := h.2.2
  exact h.fgAtt self a st.record ⟨σes, hrec, fun b hb => (atts_onAttestation _ a).2 (hsub b hb)⟩

private theorem NInv.onBlock {st : NodeState A} {t : Time} (h : NInv self st t) (B : A.Blk)
    (hv : A.Requirements → A.validPayload B) : NInv self (onBlock self st t B).1 t := by
  unfold Node.onBlock
  split_ifs with hf
  · exact h
  split
  · exact h
  rename_i fg' hb
  obtain ⟨hr, hac, σes, hrec, hsub⟩ := h
  have hr' : fg'.Reachable A.genesisPayload := hr.tail (Or.inl ⟨B, hb⟩)
  have htree := (Store.tree_grows P _ _ _ hr).1 B fg' hb
  have hstep := (Store.accept_is_frame_step P _ _ _ hr).1 B fg' hb
  refine ⟨hr', fun hq => ?_, σes, hrec, fun a ha => atts_onBlock hb (hsub a ha)⟩
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  refine ⟨t, le_rfl, .step (.block B) (reachableAt_mono self ?_ hR) ht₀
    ⟨frameIn_store (st := { st with fg := fg' }) hr', hstep, hv hq, Nat.le_of_not_lt hf⟩⟩
  change st.fg.tree ⊆ fg'.tree
  rw [htree]
  exact Set.subset_insert _ _

private theorem NInv.attest {st : NodeState A} {t : Time} (h : NInv self st t) (C : A.Blk) :
    NInv self (attest self st C).1 t := by
  unfold Node.attest
  split
  · exact h
  rename_i a Λ' heq
  obtain ⟨σes, hrec, hsub⟩ := h.2.2
  refine h.fgAtt self a Λ' ⟨σes ++ [st.fg.σ (st.fg.σ C.root).Th], ?_⟩
  have hc : (FG.Record.run self FG.Record.empty σes).1.createAtt self
      (st.fg.σ (st.fg.σ C.root).Th) = some (a, Λ') := by
    rw [← hrec]; exact heq
  rw [run_append self _ _ _ _ _ hc]
  refine ⟨rfl, fun b hb => ?_⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact (atts_onAttestation _ a).2 (hsub b hb)
  · rw [List.mem_singleton.1 hb]
    exact (atts_onAttestation _ a).1

private theorem NInv.tickStep {st : NodeState A} {t : Time} (h : NInv self st t)
    (s : TickStep) : NInv self (tickStep dg self st t s).1 t := by
  cases s with
  | acTick => exact h.acCall self .tick ⟨frameIn_store h.1, rfl⟩
  | proposal =>
    simp only [Node.tickStep]
    split_ifs with hp
    · split
      · exact h.acProposal self
      · rename_i d p hdp
        refine (h.acProposal self).onBlock self _ fun hq => ?_
        obtain ⟨t₀, ht₀, hR⟩ := h.2.1 hq
        have hts : t = P.slotTime (P.slotOf t) := hp.2.1
        refine hq.payload self _ (Store.accepted_tree P _ _ _ h.1).2.1 _ _ t₀ hR (P.slotOf t)
          (hts ▸ ht₀) d p ?_ _ rfl rfl
        rw [← hts]
        exact hdp
    · exact h
  | fgUpdate =>
    simp only [Node.tickStep]
    split
    · exact h.acToFG self
    · exact (h.acToFG self).attest self _

private theorem NInv.exec {st : NodeState A} {t : Time} (h : NInv self st t) (e : Event A)
    (hw : WireOK dg e) : NInv self (exec dg self st t e).1 t := by
  cases e with
  | tick =>
    simp only [Node.exec, onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil]
    exact ((h.tickStep dg self _).tickStep dg self _).tickStep dg self _
  | block B => exact h.onBlock self B fun _ => hw.2.2
  | message m => exact h.acCall self _ ⟨frameIn_store h.1, rfl, hw⟩
  | attestation a => exact h.onAttestation self a
  | restart => exact h.acCall self _ ⟨frameIn_store h.1, rfl⟩

private theorem initialFrame : A.InitialFrame (frame (Node.init A)) := by
  refine ⟨Set.ext fun B => ⟨fun hB => ?_, fun hB => ?_⟩, rfl, rfl, rfl, rfl⟩
  · have h := hB.1
    change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
      some B at h
    split_ifs at h
    exact (Option.some.inj h).symm
  · rw [Set.mem_singleton_iff.1 hB]
    refine ⟨?_, .refl⟩
    change (if P.genesisRoot = P.genesisRoot then some (P.genesisBlock A.genesisPayload)
      else none) = some (P.genesisBlock A.genesisPayload)
    simp

private theorem nInv_of_reachable {cfg : Config A} (h : Reachable dg self cfg) :
    NInv self cfg.st cfg.time := by
  induction h with
  | refl =>
    refine ⟨.refl, fun _ => ⟨0, le_rfl, .init _ initialFrame (frameIn_store .refl)⟩,
      [], rfl, by simp [FG.Record.run]⟩
  | tail _ hs ih =>
    obtain ⟨e, t', ht, -, hw, hst, htime, -⟩ := hs
    rw [hst, htime]
    exact (ih.mono self ht).exec dg self e hw

/-- **C0.5 (a), (b).** -/
theorem ac_states_reachable : ACStatesReachable dg self := by
  intro hq cfg h
  obtain ⟨hr, hac, -⟩ := nInv_of_reachable dg self h
  exact ⟨(Store.accepted_tree P _ _ _ hr).2.1, hac hq⟩

/-- **C0.5 (c), the record.** -/
theorem record_is_client_run : RecordIsClientRun dg self := fun _ h =>
  (nInv_of_reachable dg self h).2.2

/-- **C0.1.** -/
theorem three_tips : ThreeTips dg self := by
  intro hq cfg h t ht
  obtain ⟨hr, hac, -⟩ := nInv_of_reachable dg self h
  obtain ⟨t₀, ht₀, hR⟩ := hac hq
  exact tips_nested A hq self _ (Store.accepted_tree P _ _ _ hr).2.1 _ _ t₀ hR t (ht₀.trans ht)

/-- The proposal step signs nothing. -/
private theorem proposal_no_attest (st : NodeState A) (t : Time) (C : A.Blk)
    (s : Option (FG.Att P.n)) : Cut.fg (.attest C s) ∉ (tickStep dg self st t .proposal).2 := by
  simp only [Node.tickStep]
  split_ifs
  · split
    · simp [Node.acProposal]
    · simp only [proposeBlock, Node.onBlock]
      split_ifs
      · simp [Node.acProposal]
      · split <;> simp [Node.acProposal, Node.acCall]
  · simp

/-- The source of a signing cut of the FG update is what `ac_to_fg` returned, and the update
leaves the tree and `Σ.F`. -/
private theorem fgUpdate_attest {st : NodeState A} {t : Time}
    (hr : st.fg.Reachable A.genesisPayload) {C : A.Blk} {s : Option (FG.Att P.n)}
    (h : Cut.fg (.attest C s) ∈ (tickStep dg self st t .fgUpdate).2) :
    (Node.acToFG st t).2.2.1 = some C ∧ (tickStep dg self st t .fgUpdate).1.fg.tree = st.fg.tree ∧
      (tickStep dg self st t .fgUpdate).1.fg.F = st.fg.F := by
  simp only [Node.tickStep, Node.acToFG] at h ⊢
  cases hC' : (A.toFG st.ac (frame st) t).2.1 with
  | none => rw [hC'] at h; simp at h
  | some C' =>
    rw [hC'] at h
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    simp only [Node.attest] at h ⊢
    cases ha : st.fg.attest st.record self C' with
    | none =>
      rw [ha] at h
      simp only [List.mem_singleton, Cut.fg.injEq, FGLabel.attest.injEq] at h
      exact ⟨h.1 ▸ rfl, rfl, rfl⟩
    | some q =>
      obtain ⟨a, Λ'⟩ := q
      rw [ha] at h
      have hCC : C' = C := by
        cases h with
        | head => rfl
        | tail _ h' => cases h' with
          | tail _ h'' => cases h''
      exact ⟨hCC ▸ rfl, (Store.tree_grows P _ _ _ hr).2 _,
        (Store.finalized_monotone P _ _ _ hr).2 _⟩

/-- **C0.5 (c), the sources.** -/
theorem sources_held : SourcesHeld dg self := by
  intro hq cfg cfg' t h hs C s hC
  obtain ⟨ht, -, -, hst, -, -⟩ := hs
  have hI := (nInv_of_reachable dg self h).mono self ht
  have h₂ := (hI.tickStep dg self .acTick).tickStep dg self .proposal
  have hcuts : exec dg self cfg.st t .tick =
      ((tickStep dg self (tickStep dg self (tickStep dg self cfg.st t .acTick).1 t .proposal).1
          t .fgUpdate).1,
        (tickStep dg self cfg.st t .acTick).2 ++
          (tickStep dg self (tickStep dg self cfg.st t .acTick).1 t .proposal).2 ++
          (tickStep dg self (tickStep dg self (tickStep dg self cfg.st t .acTick).1 t .proposal).1
            t .fgUpdate).2) := by
    simp [Node.exec, onTick, runSteps, tickSteps]
  rw [hcuts] at hC
  rw [hst, hcuts]
  simp only [List.mem_append] at hC
  rcases hC with (hC | hC) | hC
  · simp [Node.tickStep, acCall] at hC
  · exact absurd hC (proposal_no_attest dg self _ t C s)
  obtain ⟨hsrc, htree, hF⟩ := fgUpdate_attest dg self h₂.1 hC
  obtain ⟨t₀, ht₀, hR⟩ := h₂.2.1 hq
  obtain ⟨hCt, hFC, -⟩ := source_held A hq self _ (Store.accepted_tree P _ _ _ h₂.1).2.1 _ _ t₀ hR
    t ht₀ C hsrc
  dsimp only
  unfold Store.Anc
  rw [htree, hF]
  exact ⟨hCt.1, Anc.mono (fun _ h => h.1) hFC⟩

end Consensus.Goldilocks.Compose

end
