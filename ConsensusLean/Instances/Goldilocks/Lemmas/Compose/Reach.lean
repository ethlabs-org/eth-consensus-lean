module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Entry

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

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

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
    (exec proposer dg self st t e).1.fg.Reachable A.genesisPayload ∧
      st.fg.tree ⊆ (exec proposer dg self st t e).1.fg.tree ∧
      (exec proposer dg self st t e).1.fg.Anc st.fg.F (exec proposer dg self st t e).1.fg.F :=
  chain_fg self (exec_is_cut_chain proposer dg self st t e) hr

/-- **C0.5 (c), the FG.** -/
theorem fg_states_reachable : FGStatesReachable proposer dg self := by
  intro cfg h
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨e, t', -, -, -, hst, -, -⟩ := hs
    rw [hst]
    exact (exec_fg proposer dg self _ t' e ih).1

/-- **C0.2.** -/
theorem finalized_monotone : FinalizedMonotone proposer dg self := by
  intro cfg cfg' hr h
  induction h with
  | refl => exact .refl
  | @tail c₁ c₂ h₁ hs ih =>
    obtain ⟨e, t', -, -, -, hst, -, -⟩ := hs
    have hr₁ := fg_states_reachable proposer dg self c₁ (hr.trans h₁)
    obtain ⟨-, hT, hF⟩ := exec_fg proposer dg self c₁.st t' e hr₁
    rw [hst]
    exact (Anc.mono hT ih).trans hF

/-! ### The AC state and the record, handler by handler -/

/-- The node invariant at a state for calls at time `t`: the FG state is reachable; under the
requirements, the AC state is reachable inside the tree with the current frame, by a last call
not after `t`, and the pool holds well-formed attestations; the record is the client run over
some entry states, whose attestations are in the pool; when genesis has its digest as root,
every held block does. -/
private structure NInv (v : Fin P.n) (st : NodeState A) (t : Time) : Prop where
  fg : st.fg.Reachable A.genesisPayload
  ac : A.Requirements → ∃ t₀ ≤ t, A.ReachableAt v st.fg.tree st.ac (frame st) t₀
  rcd : ∃ σes : List (FG.ChainState P.n),
    st.record = (FG.Record.run v FG.Record.empty σes).1 ∧
      ∀ a ∈ (FG.Record.run v FG.Record.empty σes).2, a ∈ st.fg.atts
  wf : A.Requirements → ∀ a ∈ st.fg.atts, a.WellFormed
  roots : (P.genesisBlock A.genesisPayload).RootOk dg → ∀ X ∈ st.fg.tree, X.RootOk dg

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

/-- The result of the `finality_pair` scan is an element of the scanned list (or nothing). -/
private theorem foldl_pair_mem {Q : Nat × Nat → Prop} :
    ∀ (l : List (Nat × Nat)) (acc : Option (Nat × Nat)), (∀ r, acc = some r → Q r) →
      (∀ p ∈ l, Q p) → ∀ r, l.foldl (fun acc p => match acc with
        | none => some p
        | some r => if r.1 < p.1 then some p else some r) acc = some r → Q r := by
  intro l
  induction l with
  | nil => exact fun acc h _ r hr => h r hr
  | cons p l ih =>
    intro acc hacc hl r hr
    refine ih _ (fun r' hr' => ?_) (fun q hq => hl q (List.mem_cons_of_mem _ hq)) r hr
    cases acc with
    | none => cases hr'; exact hl p List.mem_cons_self
    | some r₀ =>
      dsimp only at hr'
      split_ifs at hr' with hlt
      · cases hr'; exact hl p List.mem_cons_self
      · cases hr'; exact hacc _ rfl

/-- `create_attestation` at an entry state with the chain invariants (`1 ≤ h`, `h_j < h`, the
pending pairs below `h`) signs a well-formed attestation. -/
theorem createAtt_wellFormed {Λ Λ' : FG.Record} {v : Fin P.n} {σe : FG.ChainState P.n}
    {a : FG.Att P.n} (h1 : 1 ≤ σe.h) (h2 : σe.hj < σe.h) (h3 : ∀ p ∈ σe.pending, p.1 < σe.h)
    (h : Λ.createAtt v σe = some (a, Λ')) : a.WellFormed := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  rename_i hh T τ hhp
  have hh' : hh = σe.h := by
    unfold FG.Record.heightPair at hhp
    split_ifs at hhp <;> cases hhp <;> rfl
  split_ifs at h
  cases h
  subst hh'
  refine ⟨h1, fun p hp => ?_⟩
  unfold FG.Record.finalityPair at hp
  split_ifs at hp
  · simp only [Option.toList_some, List.mem_singleton] at hp
    subst hp
    exact h2
  · simp at hp
  · rcases hf : (σe.pending.filter (fun p => decide (Λ.permits p.1 p.2))).foldl _ none with _ | r
    · rw [hf] at hp; simp at hp
    · rw [hf] at hp
      simp only [Option.toList_some, List.mem_singleton] at hp
      subst hp
      exact foldl_pair_mem (Q := fun p => p.1 < σe.h) _ none (fun _ h => by cases h)
        (fun q hq => h3 q (List.mem_filter.1 hq).1) _ hf

/-- The attestations of `addAtts` are the old ones or the added ones. -/
private theorem mem_addAtts {fg : Store P A.Payload} {l : List (FG.Att P.n)} {a : FG.Att P.n}
    (h : a ∈ (fg.addAtts l).atts) : a ∈ fg.atts ∨ a ∈ l := by
  induction l generalizing fg with
  | nil => exact Or.inl h
  | cons b l ih =>
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts] at h
    rcases ih h with h | h
    · unfold Store.onAttestation at h
      split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_singleton.1 h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem NInv.mono {st : NodeState A} {t t' : Time} (h : NInv dg self st t) (ht : t ≤ t') :
    NInv dg self st t' :=
  ⟨h.fg, fun hq => (h.ac hq).imp fun _ h => ⟨h.1.trans ht, h.2⟩, h.rcd, h.wf, h.roots⟩

/-- An AC call keeps everything but the AC state. -/
private theorem NInv.ac' {st : NodeState A} {t : Time} (h : NInv dg self st t) (s : A.State)
    (hs : A.Requirements → ∃ t₀ ≤ t, A.ReachableAt self st.fg.tree s (frame st) t₀) :
    NInv dg self { st with ac := s } t :=
  ⟨h.fg, hs, h.rcd, h.wf, h.roots⟩

private theorem NInv.acCall {st : NodeState A} {t : Time} (h : NInv dg self st t) (c : A.Call)
    (hc : A.CallOK st.fg.tree (frame st) t c (frame st)) :
    NInv dg self (acCall self st t c).1 t :=
  h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step c hR ht₀ hc⟩

private theorem NInv.acProposal {st : NodeState A} {t : Time} (h : NInv dg self st t) :
    NInv dg self (Node.acProposal st t).1 t :=
  h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .proposal hR ht₀ ⟨frameIn_store h.fg, rfl⟩⟩

private theorem NInv.acToFG {st : NodeState A} {t : Time} (h : NInv dg self st t) :
    NInv dg self (Node.acToFG st t).1 t :=
  h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .toFG hR ht₀ ⟨frameIn_store h.fg, rfl⟩⟩

/-- Processing a well-formed attestation keeps the invariant. -/
private theorem NInv.fgAtt {st : NodeState A} {t : Time} (h : NInv dg self st t) (a : FG.Att P.n)
    (hwf : A.Requirements → a.WellFormed) (Λ : FG.Record)
    (hrec : ∃ σes : List (FG.ChainState P.n), Λ = (FG.Record.run self FG.Record.empty σes).1 ∧
      ∀ b ∈ (FG.Record.run self FG.Record.empty σes).2, b ∈ (st.fg.onAttestation a).atts) :
    NInv dg self { st with fg := st.fg.onAttestation a, record := Λ } t := by
  have hr := h.fg
  have htree := (Store.tree_grows P _ _ _ hr).2 a
  have hfr := (Store.accept_is_frame_step P _ _ _ hr).2 a
  refine ⟨hr.tail (Or.inr ⟨a, rfl⟩), fun hq => ?_, hrec, fun hq b hb => ?_, fun hg => ?_⟩
  · obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    refine ⟨t₀, ht₀, ?_⟩
    change A.ReachableAt self (st.fg.onAttestation a).tree st.ac (st.fg.onAttestation a).toFrame t₀
    rw [htree, hfr]
    exact hR
  · change b ∈ (st.fg.onAttestation a).atts at hb
    unfold Store.onAttestation at hb
    split_ifs at hb
    · exact h.wf hq b hb
    · rcases List.mem_append.1 hb with hb | hb
      · exact h.wf hq b hb
      · exact List.mem_singleton.1 hb ▸ hwf hq
  · change ∀ X ∈ (st.fg.onAttestation a).tree, X.RootOk dg
    rw [htree]
    exact h.roots hg

private theorem NInv.onAttestation {st : NodeState A} {t : Time} (h : NInv dg self st t)
    (a : FG.Att P.n) (hwf : A.Requirements → a.WellFormed) :
    NInv dg self (onAttestation st a).1 t := by
  obtain ⟨σes, hrec, hsub⟩ := h.rcd
  exact h.fgAtt dg self a hwf st.record
    ⟨σes, hrec, fun b hb => (atts_onAttestation _ a).2 (hsub b hb)⟩

private theorem NInv.onBlock {st : NodeState A} {t : Time} (h : NInv dg self st t) (B : A.Blk)
    (hv : A.Requirements → A.validPayload B) (hro : B.RootOk dg) :
    NInv dg self (onBlock self st t B).1 t := by
  unfold Node.onBlock
  split_ifs with hf
  · exact h
  split
  · exact h
  rename_i fg' hb
  have hr := h.fg
  obtain ⟨σes, hrec, hsub⟩ := h.rcd
  have hr' : fg'.Reachable A.genesisPayload := hr.tail (Or.inl ⟨B, hb⟩)
  have htree := (Store.tree_grows P _ _ _ hr).1 B fg' hb
  have hstep := (Store.accept_is_frame_step P _ _ _ hr).1 B fg' hb
  refine ⟨hr', fun hq => ?_, ⟨σes, hrec, fun a ha => atts_onBlock hb (hsub a ha)⟩,
    fun hq a ha => ?_, fun hg X hX => ?_⟩
  · obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    refine ⟨t, le_rfl, .step (.block B) (reachableAt_mono self ?_ hR) ht₀
      ⟨frameIn_store (st := { st with fg := fg' }) hr', hstep, hv hq, Nat.le_of_not_lt hf⟩⟩
    change st.fg.tree ⊆ fg'.tree
    rw [htree]
    exact Set.subset_insert _ _
  · change a ∈ fg'.atts at ha
    obtain ⟨pr, σ', h₁, h₂, h₃, h₄, hσ', hfg⟩ := Store.onBlock_eq_some hb
    subst hfg
    rcases mem_addAtts ha with ha | ha
    · rw [(Store.updateFinality_spec _ _).2.2.1] at ha
      exact h.wf hq a ha
    · exact ((P.fg.stateTransition_eq_some.1 hσ').1.2 a ha).1
  · change X ∈ fg'.tree at hX
    rw [htree] at hX
    rcases hX with rfl | hX
    · exact hro
    · exact h.roots hg X hX

private theorem NInv.attest {st : NodeState A} {t : Time} (h : NInv dg self st t) (C : A.Blk)
    (hC : A.Requirements → C ∈ st.fg.tree) : NInv dg self (attest self st C).1 t := by
  unfold Node.attest
  split
  · exact h
  rename_i a Λ' heq
  obtain ⟨σes, hrec, hsub⟩ := h.rcd
  refine h.fgAtt dg self a (fun hq => ?_) Λ' ⟨σes ++ [st.fg.σ (st.fg.σ C.root).Th], ?_⟩
  · -- the entry state of a held source has the chain invariants
    have hr := h.fg
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Store.entry_state_of_source P _ _ _ hr C (hC hq)
    obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain P _ _ _ hr E hE
    obtain ⟨h1, -, h3, -, -, -, -, h8, -⟩ := FG.chain_invariants P.fg _ _ hcs
    rw [hEr] at h1 h3 h8
    exact createAtt_wellFormed h1 h3 (fun p hp => lt_of_le_of_lt (h8 p hp).2 h3) heq
  have hc : (FG.Record.run self FG.Record.empty σes).1.createAtt self
      (st.fg.σ (st.fg.σ C.root).Th) = some (a, Λ') := by
    rw [← hrec]; exact heq
  rw [run_append self _ _ _ _ _ hc]
  refine ⟨rfl, fun b hb => ?_⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact (atts_onAttestation _ a).2 (hsub b hb)
  · rw [List.mem_singleton.1 hb]
    exact (atts_onAttestation _ a).1

private theorem NInv.tickStep {st : NodeState A} {t : Time} (h : NInv dg self st t)
    (x : Nat) (s : TickStep) : NInv dg self (tickStep proposer dg self st t x s).1 t := by
  cases s with
  | acTick => exact h.acCall dg self .tick ⟨frameIn_store h.fg, rfl⟩
  | proposal =>
    simp only [Node.tickStep]
    split_ifs with hp
    · split
      · exact h.acProposal dg self
      · rename_i d p hdp
        refine (h.acProposal dg self).onBlock dg self _ (fun hq => ?_) rfl
        obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
        have hts : t = P.slotTime (P.slotOf t) := hp.2.1
        refine hq.payload self _ (Store.accepted_tree P _ _ _ h.fg).2.1 _ _ t₀ hR (P.slotOf t)
          (hts ▸ ht₀) d p ?_ _ rfl rfl
        rw [← hts]
        exact hdp
    · exact h
  | fgUpdate =>
    simp only [Node.tickStep]
    split
    · exact h.acToFG dg self
    · rename_i C hC
      refine (h.acToFG dg self).attest dg self _ fun hq => ?_
      obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
      exact (source_held A hq self _ (Store.accepted_tree P _ _ _ h.fg).2.1 _ _ t₀ hR t ht₀ C
        hC).1.1

private theorem NInv.exec {st : NodeState A} {t : Time} (h : NInv dg self st t) (e : Event A)
    (hw : WireOK dg e) : NInv dg self (exec proposer dg self st t e).1 t := by
  cases e with
  | tick x =>
    simp only [Node.exec, onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil]
    exact ((h.tickStep proposer dg self x _).tickStep proposer dg self x _).tickStep
      proposer dg self x _
  | block B => exact h.onBlock dg self B (fun _ => hw.2.2) hw.1
  | message m => exact h.acCall dg self _ ⟨frameIn_store h.fg, rfl, hw⟩
  | attestation a => exact h.onAttestation dg self a fun _ => hw
  | restart => exact h.acCall dg self _ ⟨frameIn_store h.fg, rfl⟩

private theorem mem_init_tree {B : A.Blk} (hB : B ∈ (Node.init A).fg.tree) :
    B = P.genesisBlock A.genesisPayload := by
  change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
    some B at hB
  split_ifs at hB
  exact (Option.some.inj hB).symm

/-- The frame of the initial node state is an initial frame. -/
theorem init_initialFrame : A.InitialFrame (frame (Node.init A)) := by
  refine ⟨Set.ext fun B => ⟨fun hB => mem_init_tree hB.1, fun hB => ?_⟩, rfl, rfl, rfl, rfl⟩
  rw [Set.mem_singleton_iff.1 hB]
  refine ⟨?_, .refl⟩
  change (if P.genesisRoot = P.genesisRoot then some (P.genesisBlock A.genesisPayload)
    else none) = some (P.genesisBlock A.genesisPayload)
  simp

private theorem nInv_of_reachable {cfg : Config A} (h : Reachable proposer dg self cfg) :
    NInv dg self cfg.st cfg.time := by
  induction h with
  | refl =>
    exact
      { fg := .refl
        ac := fun _ => ⟨0, le_rfl, .init _ init_initialFrame (frameIn_store .refl)⟩
        rcd := ⟨[], rfl, by simp [FG.Record.run]⟩
        wf := fun _ a ha => by cases ha
        roots := fun hg X hX => by rw [mem_init_tree hX]; exact hg }
  | tail _ hs ih =>
    obtain ⟨e, t', ht, -, hw, hst, htime, -⟩ := hs
    rw [hst, htime]
    exact (ih.mono dg self ht).exec proposer dg self e hw

/-- **C0.5 (a), (b).** -/
theorem ac_states_reachable : ACStatesReachable proposer dg self := by
  intro hq cfg h
  have hI := nInv_of_reachable proposer dg self h
  exact ⟨(Store.accepted_tree P _ _ _ hI.fg).2.1, hI.ac hq⟩

/-- **C0.5 (c), the record.** -/
theorem record_is_client_run : RecordIsClientRun proposer dg self := fun _ h =>
  (nInv_of_reachable proposer dg self h).rcd

/-- **C0.1.** -/
theorem three_tips : ThreeTips proposer dg self := by
  intro hq cfg h t ht
  have hI := nInv_of_reachable proposer dg self h
  obtain ⟨t₀, ht₀, hR⟩ := hI.ac hq
  exact tips_nested A hq self _ (Store.accepted_tree P _ _ _ hI.fg).2.1 _ _ t₀ hR t
    (ht₀.trans ht)

/-- The proposal step signs nothing. -/
private theorem proposal_no_attest (st : NodeState A) (t : Time) (x : Nat) (C : A.Blk)
    (s : Option (FG.Att P.n)) :
    Cut.fg (.attest C s) ∉ (tickStep proposer dg self st t x .proposal).2 := by
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
    (hr : st.fg.Reachable A.genesisPayload) {C : A.Blk} {s : Option (FG.Att P.n)} {x : Nat}
    (h : Cut.fg (.attest C s) ∈ (tickStep proposer dg self st t x .fgUpdate).2) :
    (Node.acToFG st t).2.2.1 = some C ∧
      (tickStep proposer dg self st t x .fgUpdate).1.fg.tree = st.fg.tree ∧
      (tickStep proposer dg self st t x .fgUpdate).1.fg.F = st.fg.F := by
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
theorem sources_held : SourcesHeld proposer dg self := by
  intro hq cfg cfg' t x h hs C s hC
  obtain ⟨ht, -, -, hst, -, -⟩ := hs
  have hI := (nInv_of_reachable proposer dg self h).mono dg self ht
  have h₂ := (hI.tickStep proposer dg self x .acTick).tickStep proposer dg self x .proposal
  have hcuts : exec proposer dg self cfg.st t (.tick x) =
      ((tickStep proposer dg self
          (tickStep proposer dg self
            (tickStep proposer dg self cfg.st t x .acTick).1 t x .proposal).1
          t x .fgUpdate).1,
        (tickStep proposer dg self cfg.st t x .acTick).2 ++
          (tickStep proposer dg self
            (tickStep proposer dg self cfg.st t x .acTick).1 t x .proposal).2 ++
          (tickStep proposer dg self
            (tickStep proposer dg self
              (tickStep proposer dg self cfg.st t x .acTick).1 t x .proposal).1
            t x .fgUpdate).2) := by
    simp [Node.exec, onTick, runSteps, tickSteps]
  rw [hcuts] at hC
  rw [hst, hcuts]
  simp only [List.mem_append] at hC
  rcases hC with (hC | hC) | hC
  · simp [Node.tickStep, acCall] at hC
  · exact absurd hC (proposal_no_attest proposer dg self _ t x C s)
  obtain ⟨hsrc, htree, hF⟩ := fgUpdate_attest proposer dg self h₂.fg hC
  obtain ⟨t₀, ht₀, hR⟩ := h₂.ac hq
  obtain ⟨hCt, hFC, -⟩ := source_held A hq self _ (Store.accepted_tree P _ _ _ h₂.fg).2.1 _ _ t₀ hR
    t ht₀ C hsrc
  dsimp only
  unfold Store.Anc
  rw [htree, hF]
  exact ⟨hCt.1, Anc.mono (fun _ h => h.1) hFC⟩

/-! ### C0.3: the own block is accepted -/

private theorem slotTime_slotOf_le {t : Time} (ht : 0 ≤ t) : P.slotTime (P.slotOf t) ≤ t :=
  Nat.findGreatest_spec (P := fun s => P.slotTime s ≤ t) (Nat.zero_le _)
    (by rw [P.slotTime_zero]; exact ht)

/-- One cut adds to the tree only a block not of a future slot. -/
private theorem step_tree {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') (hr : st.fg.Reachable A.genesisPayload) :
    ∀ X ∈ st'.fg.tree, X ∈ st.fg.tree ∨ X.slot ≤ P.slotOf t := by
  intro X hX
  cases c with
  | ac ℓ => rw [h.2.2.1] at hX; exact Or.inl hX
  | fg ℓ =>
    cases ℓ with
    | block B acc =>
      cases acc with
      | true =>
        obtain ⟨hs, hb, -, -⟩ := h
        rw [(Store.tree_grows P _ _ _ hr).1 B _ hb] at hX
        rcases hX with rfl | hX
        · exact Or.inr hs
        · exact Or.inl hX
      | false => obtain ⟨-, rfl⟩ := h; exact Or.inl hX
    | attestation a =>
      rw [h.1, (Store.tree_grows P _ _ _ hr).2 a] at hX
      exact Or.inl hX
    | attest C s =>
      cases s with
      | none => obtain ⟨-, rfl⟩ := h; exact Or.inl hX
      | some a => rw [h.2.1] at hX; exact Or.inl hX

private theorem chain_tree {t : Time} {st st' : NodeState A} {cs : List (Cut A)}
    (h : CutChain self t st cs st') (hr : st.fg.Reachable A.genesisPayload) :
    ∀ X ∈ st'.fg.tree, X ∈ st.fg.tree ∨ X.slot ≤ P.slotOf t := by
  induction h with
  | nil => exact fun X hX => Or.inl hX
  | cons hs _ ih =>
    intro X hX
    rcases ih (step_fg self hs hr).1 X hX with hX | hX
    · exact step_tree self hs hr X hX
    · exact Or.inr hX

/-- The slots of the held blocks: genesis, or a block whose slot starts at or before the clock,
before it in phase `pre`. -/
private def SlotInv (cfg : Config A) : Prop :=
  0 ≤ cfg.time ∧ ∀ X ∈ cfg.st.fg.tree, X.slot = 0 ∨
    (P.slotTime X.slot ≤ cfg.time ∧ (cfg.phase = .pre → P.slotTime X.slot < cfg.time))

private theorem slotInv_of_reachable {cfg : Config A} (h : Reachable proposer dg self cfg) :
    SlotInv cfg := by
  induction h with
  | refl => exact ⟨le_rfl, fun X hX => Or.inl (by rw [mem_init_tree hX]; rfl)⟩
  | @tail c₁ c₂ hr₁ hs ih =>
    obtain ⟨e, t', ht, hok, -, hst, htime, hph⟩ := hs
    obtain ⟨h0, hold⟩ := ih
    have hr := (nInv_of_reachable proposer dg self hr₁).fg
    refine ⟨htime ▸ h0.trans ht, fun X hX => ?_⟩
    rw [hst] at hX
    rw [htime, hph]
    cases e with
    | restart =>
      -- a restart adds no block, and the phase at `t'` was `pre`
      rcases hold X hX with h | ⟨h1, h2⟩
      · exact Or.inl h
      refine Or.inr ⟨h1.trans ht, fun _ => ?_⟩
      change Phase.at c₁.time t' c₁.phase = .pre at hok
      unfold Phase.at at hok
      split_ifs at hok with hlt
      · exact lt_of_le_of_lt h1 hlt
      · exact lt_of_lt_of_le (h2 hok) ht
    | _ =>
      rcases chain_tree self (exec_is_cut_chain proposer dg self c₁.st t' _) hr X hX with hX | hX
      · rcases hold X hX with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1.trans ht, fun h => by cases h⟩
      · exact Or.inr ⟨(P.slotTime_strictMono.monotone hX).trans
          (slotTime_slotOf_le (h0.trans ht)), fun h => by cases h⟩

/-- At the tick of a slot start that the node proposes in, every held block is of an earlier
slot (genesis, or accepted before that time: the tick runs before the objects of its time). -/
private theorem slot_lt_of_tick {cfg cfg' : Config A} {t : Time} {x : Nat}
    (h : Reachable proposer dg self cfg) (hs : Step proposer dg self cfg (.tick x) t cfg')
    (hp : Proposes proposer self t) :
    ∀ X ∈ cfg.st.fg.tree, X.slot < P.slotOf t := by
  intro X hX
  obtain ⟨-, hinv⟩ := slotInv_of_reachable proposer dg self h
  obtain ⟨ht, ⟨-, hpre⟩, -⟩ := hs
  rcases hinv X hX with h0 | ⟨h1, h2⟩
  · rw [h0]; exact hp.1
  have hlt : P.slotTime X.slot < t := by
    unfold Phase.at at hpre
    split_ifs at hpre with hlt
    · exact lt_of_le_of_lt h1 hlt
    · exact lt_of_lt_of_le (h2 hpre) ht
  rw [hp.2.1] at hlt
  exact P.slotTime_strictMono.lt_iff_lt.1 hlt

/-- The chain state of a held block has that block's slot. -/
private theorem σ_slot {fg : Store P A.Payload} (hr : fg.Reachable A.genesisPayload) {H : A.Blk}
    (hH : H ∈ fg.tree) : (fg.σ H.root).s ≤ H.slot := by
  obtain ⟨c, -, -, hlast, hcs⟩ := Store.chain_state_of_chain P _ _ _ hr H hH
  rcases hlast with ⟨rfl, -⟩ | hlast
  · have h := (show P.fg.chainState [] = some (FG.ChainState.init P.fg) from rfl).symm.trans hcs
    rw [← Option.some.inj h]
    exact Nat.zero_le _
  · obtain ⟨c', rfl⟩ := List.getLast?_eq_some_iff.1 hlast
    have e : ∀ l : List A.Blk, (List.map Block.fgView l : List (FG.FGBlock P.fg.n)) =
        l.map (fun B => (Block.fgView B : FG.FGBlock P.n)) := fun l => rfl
    rw [e, List.map_append, List.map_singleton] at hcs
    obtain ⟨σ₀, -, hσ⟩ :=
      Option.bind_eq_some_iff.1 ((FG.FGParams.chainState_append P.fg _ _).symm.trans hcs)
    exact (P.fg.stateTransition_L_s hσ).2.1.le

/-- **C0.3.** -/
theorem honest_block_accepted : HonestBlockAccepted proposer dg self := by
  intro hq hg cfg cfg' t x hR hs hp
  dsimp only
  intro d p hdp
  have hI := (nInv_of_reachable proposer dg self hR).mono dg self hs.1
  have h₁ := hI.tickStep proposer dg self x .acTick
  obtain ⟨t₀, ht₀, hRA⟩ := h₁.ac hq
  have hcoh := (Store.accepted_tree P _ _ _ h₁.fg).2.1
  have hts : t = P.slotTime (P.slotOf t) := hp.2.1
  have hprop : (A.proposal (tickStep proposer dg self cfg.st t x .acTick).1.ac
      (frame (tickStep proposer dg self cfg.st t x .acTick).1) (P.slotTime (P.slotOf t))).2 =
      some (d, p) := by
    rw [← hts]; exact hdp
  obtain ⟨hHt, hFH⟩ := proposal_parent_held A hq self _ hcoh _ _ t₀ hRA (P.slotOf t)
    (hts ▸ ht₀) d p hprop
  have hslot := slot_lt_of_tick proposer dg self hR hs hp
  have hHs : d.head.slot < P.slotOf t := hslot _ hHt.1
  have hatts : ∀ a ∈
      (mkBlock dg self (tickStep proposer dg self cfg.st t x .acTick).1.fg t x d.head p).fgPayload,
      a.WellFormed ∧
        ((tickStep proposer dg self cfg.st t x .acTick).1.fg.σ d.head.root).validAtt a := by
    intro a ha
    obtain ⟨ha, hv⟩ := List.mem_filter.1 ha
    simp only [decide_eq_true_eq] at hv
    exact ⟨h₁.wf hq a ha, hv.1⟩
  refine ⟨hHt.1, Anc.mono (fun _ h => h.1) hFH, hHs, hatts,
    hq.payload self _ hcoh _ _ t₀ hRA (P.slotOf t) (hts ▸ ht₀) d p hprop _ rfl rfl, rfl,
    fun hnc => ?_⟩
  set fg := (tickStep proposer dg self cfg.st t x .acTick).1.fg with hfg
  set B := mkBlock dg self fg t x d.head p with hB
  have hnone : fg.blocks B.root = none := by
    cases hb : fg.blocks B.root with
    | none => rfl
    | some X =>
      exfalso
      have hXr := Store.Reachable.blocks_root h₁.fg hb
      have hX : X ∈ fg.tree := by
        change fg.blocks X.root = some X
        rw [hXr]; exact hb
      have hXB := hnc X (Set.mem_insert_of_mem _ hX) B (Set.mem_insert _ _)
        ((h₁.roots hg X hX).symm.trans (hXr.trans rfl))
      have := hslot X hX
      rw [hXB.2.1] at this
      exact lt_irrefl _ this
  refine ⟨hnone, ?_⟩
  change ∃ fg', fg.onBlock B = some fg'
  have hHb : fg.blocks d.head.root = some d.head := hHt.1
  have hst : (fg.σ d.head.root).s < B.slot := lt_of_le_of_lt (σ_slot h₁.fg hHt.1) hHs
  obtain ⟨σ', hσ'⟩ : ∃ σ', P.fg.stateTransition (fg.σ d.head.root) B.fgView = some σ' :=
    ⟨_, P.fg.stateTransition_eq_some.2 ⟨⟨hst, hatts⟩, rfl⟩⟩
  refine Option.ne_none_iff_exists'.1 ?_
  unfold Store.onBlock
  rw [show B.parent = some d.head.root from rfl]
  dsimp only
  split_ifs with hc
  · exfalso
    simp only [hnone, hHb, Option.isSome_none, Option.isNone_some, Bool.false_eq_true,
      false_or] at hc
    exact hc ((Anc.mono (Set.subset_insert _ _) (Anc.mono (fun _ h => h.1) hFH)).tail
      ⟨Set.mem_insert_of_mem _ hHt.1, Set.mem_insert _ _, rfl⟩)
  · rw [hσ']
    exact Option.some_ne_none _

end Consensus.Goldilocks.Compose

end
