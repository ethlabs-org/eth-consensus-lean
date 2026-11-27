module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Shadow node configurations and AC reachability

The event order and wire checks are unchanged. Only execution and its frame are
shadow execution. No stock node reachability is assumed.
-/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

def Step' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) : Prop :=
  cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
    cfg'.st = (exec' proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧
      cfg'.phase = e.phaseAfter

def Reachable' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (a : A.State := A.initial) : Prop :=
  Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step' proposer dg self cfg e t' cfg')
    (Config.init A a) cfg

theorem step'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) :
    Step' proposer dg self cfg e t' cfg' ↔
      cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
        cfg'.st = (exec' proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧
          cfg'.phase = e.phaseAfter := by rfl

theorem reachable'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (a : A.State) :
    Reachable' proposer dg self (a := a) =
      Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step' proposer dg self cfg e t' cfg')
        (Config.init A a) := by rfl

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- The AC part of the node invariant, with payload well-formedness and root provenance
needed to validate an own proposal. The client record is handled by the signed-run supplier. -/
private structure NInv' (v : Fin P.n) (s₀ : A.State) (st : NodeState A) (t : Time) : Prop where
  fg : st.fg.Reachable' A.genesisPayload
  ac : A.ReqPayloadFrom s₀ v →
    ∃ t₀ ≤ t, A.ReachableAtFrom s₀ v st.fg.tree st.ac (frame' st) t₀
  wf : ({ A with initial := s₀ } : NodeAC P).Requirements → ∀ a ∈ st.fg.atts, a.WellFormed
  roots : (P.genesisBlock A.genesisPayload).RootOk dg → ∀ X ∈ st.fg.tree, X.RootOk dg

variable {s₀ : A.State}

private theorem frameIn_store' {st : NodeState A} (hr : st.fg.Reachable' A.genesisPayload) :
    A.FrameIn st.fg.tree (frame' st) := by
  rw [Node.frame'_eq]
  exact ⟨Store.frameOK_toFrame' hr.puSnapshot, fun _ h => by
    rw [Store.toFrame'_tree] at h
    exact h.1⟩

private theorem reachableAt_mono' {U U' : Set A.Blk} (hUU : U ⊆ U')
    {s : A.State} {Φ : A.Frm} {t : Time}
    (h : A.ReachableAtFrom s₀ self U s Φ t) : A.ReachableAtFrom s₀ self U' s Φ t := by
  induction h with
  | init Φ hi hin => exact .init Φ hi ⟨hin.1, hin.2.trans hUU⟩
  | step c _ ht hok ih => exact .step c ih ht ⟨⟨hok.1.1, hok.1.2.trans hUU⟩, hok.2⟩

private theorem NInv'.mono {st : NodeState A} {t t' : Time} (h : NInv' dg self s₀ st t)
    (ht : t ≤ t') : NInv' dg self s₀ st t' :=
  ⟨h.fg, fun hq => (h.ac hq).imp fun _ h => ⟨h.1.trans ht, h.2⟩, h.wf, h.roots⟩

private theorem NInv'.ac' {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (s : A.State) (hs : A.ReqPayloadFrom s₀ self →
      ∃ t₀ ≤ t, A.ReachableAtFrom s₀ self st.fg.tree s (frame' st) t₀) :
    NInv' dg self s₀ { st with ac := s } t := by
  refine ⟨h.fg, ?_, h.wf, h.roots⟩
  simpa only [frame'_eq] using hs

private theorem NInv'.acCall {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (c : A.Call) (hc : A.CallOK st.fg.tree (frame' st) t c (frame' st)) :
    NInv' dg self s₀ (acCall' self st t c).1 t := by
  rw [acCall'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step c hR ht₀ hc⟩

private theorem NInv'.acProposal {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t) :
    NInv' dg self s₀ (Node.acProposal' st t).1 t := by
  rw [acProposal'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .proposal hR ht₀ ⟨frameIn_store' h.fg, rfl⟩⟩

private theorem NInv'.acToFG {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t) :
    NInv' dg self s₀ (Node.acToFG' st t).1 t := by
  rw [acToFG'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .toFG hR ht₀ ⟨frameIn_store' h.fg, rfl⟩⟩

private theorem mem_init_tree' {a : A.State} {B : A.Blk}
    (hB : B ∈ (Node.initWith A a).fg.tree) : B = P.genesisBlock A.genesisPayload := by
  change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
    some B at hB
  split_ifs at hB
  exact (Option.some.inj hB).symm

theorem init_initialFrame' {a : A.State} : A.InitialFrame (frame' (Node.initWith A a)) := by
  rw [frame'_eq]
  simp only [ACInterface.InitialFrame, Store.toFrame'_F]
  refine ⟨Set.ext fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Store.toFrame'_tree] at hB
    exact mem_init_tree' hB.1
  · rw [Set.mem_singleton_iff.1 hB, Store.toFrame'_tree]
    refine ⟨?_, .refl⟩
    change (if P.genesisRoot = P.genesisRoot then some (P.genesisBlock A.genesisPayload)
      else none) = some (P.genesisBlock A.genesisPayload)
    simp
  · rfl
  · rfl
  · rfl
  · rfl

private theorem mem_addAtts' {fg : Store P A.Payload} {l : List (FG.Att P.n)}
    {a : FG.Att P.n} (h : a ∈ (fg.addAtts l).atts) : a ∈ fg.atts ∨ a ∈ l := by
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

private theorem NInv'.attest {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (C : A.Blk) : NInv' dg self s₀ (attest self st C).1 t := by
  unfold Node.attest
  split
  · exact h
  · refine ⟨h.fg, ?_, h.wf, h.roots⟩
    simpa only [frame'_eq] using h.ac

private theorem NInv'.fgAtt {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (a : FG.Att P.n) (hwf : ({ A with initial := s₀ } : NodeAC P).Requirements →
      a.WellFormed) : NInv' dg self s₀ { st with fg := st.fg.onAttestation a } t := by
  have hr := h.fg
  have htree := (Store.tree_grows_with (st := st.fg)
    Store.finalitySpec_updateFinality').2 a
  have hfr := (Store.accept_is_frame_step' A.genesisPayload st.fg hr).2 a
  refine ⟨?_, fun hq => ?_, fun hq b hb => ?_, fun hg => ?_⟩
  · rw [Store.reachable'_eq] at hr ⊢
    exact hr.tail ((Store.step'_iff _ _).2 (Or.inr ⟨a, rfl⟩))
  · obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    refine ⟨t₀, ht₀, ?_⟩
    simpa only [frame'_eq, htree, hfr] using hR
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

private theorem NInv'.onBlock {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (B : A.Blk) (hv : A.ReqPayloadFrom s₀ self → A.validPayload B) (hro : B.RootOk dg) :
    NInv' dg self s₀ (Node.onBlock' self st t B).1 t := by
  rw [Node.onBlock'_eq]
  split_ifs with hf
  · exact h
  split
  · exact h
  rename_i fg' hb
  rw [Node.acCall'_eq]
  have hr := h.fg
  have hr' : fg'.Reachable' A.genesisPayload := by
    rw [Store.reachable'_eq] at hr ⊢
    exact hr.tail ((Store.step'_iff _ _).2 (Or.inl ⟨B, hb⟩))
  have hb' := hb
  rw [Store.onBlock'_eq_onBlockWith] at hb'
  have htree := (Store.tree_grows_with Store.finalitySpec_updateFinality').1 B fg' hb'
  have hstep := (Store.accept_is_frame_step' A.genesisPayload st.fg hr).1 B fg' hb
  refine ⟨hr', fun hq => ?_, fun hq a ha => ?_, fun hg X hX => ?_⟩
  · obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    refine ⟨t, le_rfl, ?_⟩
    simp only [frame'_eq] at hR ⊢
    exact .step (.block B) (reachableAt_mono' self (by
      rw [htree]; exact Set.subset_insert _ _) hR) ht₀
      ⟨by simpa only [frame'_eq] using frameIn_store' (st := { st with fg := fg' }) hr',
        hstep, hv hq, Nat.le_of_not_lt hf⟩
  · change a ∈ fg'.atts at ha
    obtain ⟨pr, σ', _, _, _, _, hσ', hfg⟩ := Store.onBlockWith_eq_some hb'
    subst hfg
    rcases mem_addAtts' ha with ha | ha
    · have hatts (st : Store P A.Payload) (σ : FG.ChainState P.n) :
          (Store.updateFinality' st σ).atts = st.atts := by
        simp only [Store.updateFinality'_eq]
        split <;> repeat' first | split | rfl
      rw [hatts] at ha
      exact h.wf hq a ha
    · exact ((P.fg.stateTransition_eq_some.1 hσ').1.2 a ha).1
  · change X ∈ fg'.tree at hX
    rw [htree] at hX
    rcases hX with rfl | hX
    · exact hro
    · exact h.roots hg X hX

private theorem NInv'.tickStep {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (x : Nat) (s : TickStep) :
    NInv' dg self s₀ (tickStep' proposer dg self st t x s).1 t := by
  cases s with
  | acTick =>
    simpa only [tickStep'_eq] using h.acCall dg self .tick ⟨frameIn_store' h.fg, rfl⟩
  | proposal =>
    simp only [Node.tickStep'_eq]
    split_ifs with hp
    · split
      · exact h.acProposal dg self
      · rename_i d p hdp
        rw [proposeBlock'_eq]
        refine (h.acProposal dg self).onBlock dg self _ (fun hq => ?_) rfl
        obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
        have hts : t = P.slotTime (P.slotOf t) := hp.2.1
        refine hq _ (Store.accepted_tree_with Store.finalitySpec_updateFinality'
          h.fg.reachableWith).2.1 _ _ t₀ hR (P.slotOf t) (hts ▸ ht₀) d p ?_ _ rfl ?_
        · rw [← hts]
          simpa only [acProposal'_eq] using hdp
        · simp only [acProposal'_eq]
          rfl
    · exact h
  | fgUpdate =>
    simp only [Node.tickStep'_eq]
    split
    · exact h.acToFG dg self
    · exact (h.acToFG dg self).attest dg self _

private theorem NInv'.exec {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (e : Event A) (hw : WireOK dg e) : NInv' dg self s₀ (exec' proposer dg self st t e).1 t := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · simp only [Node.exec'_eq, onTick'_eq, runSteps'_eq, tickSteps, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, List.foldl_nil]
      exact (h.tickStep proposer dg self x _).tickStep proposer dg self x _
    · simp only [Node.exec'_eq, onTick'_eq, runSteps'_eq, tickSteps, ↓reduceIte,
        List.foldl_cons, List.foldl_nil]
      exact ((h.tickStep proposer dg self x _).tickStep proposer dg self x _).tickStep
        proposer dg self x _
  | block B => simpa only [exec'_eq] using h.onBlock dg self B (fun _ => hw.2.2) hw.1
  | message m =>
    simpa only [exec'_eq, onMessage'_eq] using
      h.acCall dg self (.message m) ⟨frameIn_store' h.fg, rfl, hw⟩
  | attestation a =>
    simpa only [exec'_eq, Node.onAttestation] using h.fgAtt dg self a fun _ => hw
  | restart =>
    simpa only [exec'_eq, restart'_eq] using
      h.acCall dg self .restart ⟨frameIn_store' h.fg, rfl⟩

private theorem nInv_of_reachable' {cfg : Config A}
    (h : Node.Reachable' proposer dg self cfg s₀) : NInv' dg self s₀ cfg.st cfg.time := by
  rw [congrFun (Node.reachable'_eq proposer dg self s₀) cfg] at h
  induction h with
  | refl =>
    exact
      { fg := by rw [Store.reachable'_eq]; exact .refl
        ac := fun _ => ⟨0, le_rfl, .init _ init_initialFrame'
          (frameIn_store' (by rw [Store.reachable'_eq]; exact .refl))⟩
        wf := fun _ a ha => by cases ha
        roots := fun hg X hX => by rw [mem_init_tree' hX]; exact hg }
  | tail _ hs ih =>
    obtain ⟨e, t', hs⟩ := hs
    rw [Node.step'_iff] at hs
    obtain ⟨ht, _, hw, hst, htime, _⟩ := hs
    rw [hst, htime]
    exact (ih.mono dg self ht).exec proposer dg self e hw

theorem ac_states_reachable' (hp : A.ReqPayloadFrom s₀ self) {cfg : Config A}
    (h : Node.Reachable' proposer dg self cfg s₀) :
    Coherent cfg.st.fg.tree ∧ ∃ t₀ ≤ cfg.time,
      A.ReachableAtFrom s₀ self cfg.st.fg.tree cfg.st.ac (frame' cfg.st) t₀ := by
  have hI := nInv_of_reachable' proposer dg self h
  exact ⟨(Store.accepted_tree_with Store.finalitySpec_updateFinality'
    hI.fg.reachableWith).2.1, hI.ac hp⟩

private theorem onBlock_tree' (st : NodeState A) (t : Time) (B X : A.Blk)
    (hX : X ∈ (Node.onBlock' self st t B).1.fg.tree) :
    X ∈ st.fg.tree ∨ X.slot ≤ P.slotOf t := by
  rw [Node.onBlock'_eq] at hX
  split_ifs at hX with hf
  · exact Or.inl hX
  split at hX
  · exact Or.inl hX
  · rename_i fg' hb
    simp only [acCall'_eq] at hX
    rw [Store.onBlock'_eq_onBlockWith] at hb
    rw [(Store.tree_grows_with Store.finalitySpec_updateFinality').1 B _ hb] at hX
    rcases hX with rfl | hX
    · exact Or.inr (Nat.le_of_not_lt hf)
    · exact Or.inl hX

private theorem tickStep_tree' (st : NodeState A) (t : Time) (x : Nat) (s : TickStep)
    (X : A.Blk) (hX : X ∈ (tickStep' proposer dg self st t x s).1.fg.tree) :
    X ∈ st.fg.tree ∨ X.slot ≤ P.slotOf t := by
  cases s with
  | acTick => exact Or.inl (by simpa only [tickStep'_eq, acCall'_eq] using hX)
  | proposal =>
    simp only [tickStep'_eq] at hX
    split_ifs at hX
    · split at hX
      · exact Or.inl (by simpa only [acProposal'_eq] using hX)
      · rw [proposeBlock'_eq] at hX
        simpa only [acProposal'_eq] using onBlock_tree' self _ _ _ X hX
    · exact Or.inl hX
  | fgUpdate =>
    simp only [tickStep'_eq] at hX
    split at hX
    · exact Or.inl (by simpa only [acToFG'_eq] using hX)
    · simp only [Node.attest] at hX
      split at hX <;> exact Or.inl (by simpa only [acToFG'_eq] using hX)

private theorem exec_tree' (st : NodeState A) (t : Time) (e : Event A) (X : A.Blk)
    (hX : X ∈ (exec' proposer dg self st t e).1.fg.tree) :
    X ∈ st.fg.tree ∨ X.slot ≤ P.slotOf t := by
  cases e with
  | tick x fgDue =>
    cases fgDue <;>
      simp only [exec'_eq, onTick'_eq, runSteps'_eq, tickSteps, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, List.foldl_nil] at hX
    · rcases tickStep_tree' proposer dg self _ _ _ _ X hX with hX | hX
      · exact tickStep_tree' proposer dg self _ _ _ _ X hX
      · exact Or.inr hX
    · rcases tickStep_tree' proposer dg self _ _ _ _ X hX with hX | hX
      · rcases tickStep_tree' proposer dg self _ _ _ _ X hX with hX | hX
        · exact tickStep_tree' proposer dg self _ _ _ _ X hX
        · exact Or.inr hX
      · exact Or.inr hX
  | block B => exact onBlock_tree' self st t B X (by simpa only [exec'_eq] using hX)
  | message m => exact Or.inl (by
      simpa only [exec'_eq, onMessage'_eq, acCall'_eq] using hX)
  | restart => exact Or.inl (by simpa only [exec'_eq, restart'_eq, acCall'_eq] using hX)
  | attestation a =>
    simp only [exec'_eq, Node.onAttestation] at hX
    rw [(Store.tree_grows_with (st := st.fg) Store.finalitySpec_updateFinality').2 a] at hX
    exact Or.inl hX

private def SlotInv' (cfg : Config A) : Prop :=
  0 ≤ cfg.time ∧ ∀ X ∈ cfg.st.fg.tree, X.slot = 0 ∨
    (P.slotTime X.slot ≤ cfg.time ∧ (cfg.phase = .pre → P.slotTime X.slot < cfg.time))

private theorem slotTime_slotOf_le' {t : Time} (ht : 0 ≤ t) :
    P.slotTime (P.slotOf t) ≤ t :=
  Nat.findGreatest_spec (P := fun s => P.slotTime s ≤ t) (Nat.zero_le _)
    (by rw [P.slotTime_zero]; exact ht)

private theorem slotInv_of_reachable' {cfg : Config A}
    (h : Node.Reachable' proposer dg self cfg s₀) : SlotInv' cfg := by
  rw [congrFun (Node.reachable'_eq proposer dg self s₀) cfg] at h
  induction h with
  | refl => exact ⟨le_rfl, fun X hX => Or.inl (by rw [mem_init_tree' hX]; rfl)⟩
  | @tail c₁ c₂ _ hs ih =>
    obtain ⟨e, t', hs⟩ := hs
    rw [Node.step'_iff] at hs
    obtain ⟨ht, hok, _, hst, htime, hph⟩ := hs
    obtain ⟨h0, hold⟩ := ih
    refine ⟨htime ▸ h0.trans ht, fun X hX => ?_⟩
    rw [hst] at hX
    rw [htime, hph]
    cases e with
    | restart =>
      simp only [exec'_eq, restart'_eq, acCall'_eq] at hX
      rcases hold X hX with h | ⟨h1, h2⟩
      · exact Or.inl h
      refine Or.inr ⟨h1.trans ht, fun _ => ?_⟩
      change Phase.at c₁.time t' c₁.phase = .pre at hok
      unfold Phase.at at hok
      split_ifs at hok with hlt
      · exact lt_of_le_of_lt h1 hlt
      · exact lt_of_lt_of_le (h2 hok) ht
    | _ =>
      rcases exec_tree' proposer dg self _ _ _ X hX with hX | hX
      · rcases hold X hX with h | ⟨h1, _⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1.trans ht, fun h => by cases h⟩
      · exact Or.inr ⟨(P.slotTime_strictMono.monotone hX).trans
          (slotTime_slotOf_le' (h0.trans ht)), fun h => by cases h⟩

private theorem slot_lt_of_tick' {cfg cfg' : Config A} {t : Time} {x : Nat} {fgDue : Bool}
    (h : Node.Reachable' proposer dg self cfg s₀)
    (hs : Node.Step' proposer dg self cfg (.tick x fgDue) t cfg')
    (hp : Proposes proposer self t) : ∀ X ∈ cfg.st.fg.tree, X.slot < P.slotOf t := by
  intro X hX
  obtain ⟨_, hinv⟩ := slotInv_of_reachable' proposer dg self h
  rw [Node.step'_iff] at hs
  obtain ⟨ht, ⟨_, hpre⟩, _⟩ := hs
  rcases hinv X hX with h0 | ⟨h1, h2⟩
  · rw [h0]; exact hp.1
  have hlt : P.slotTime X.slot < t := by
    unfold Phase.at at hpre
    split_ifs at hpre with hlt
    · exact lt_of_le_of_lt h1 hlt
    · exact lt_of_lt_of_le (h2 hpre) ht
  rw [hp.2.1] at hlt
  exact P.slotTime_strictMono.lt_iff_lt.1 hlt

private theorem σ_slot' {fg : Store P A.Payload} (hr : fg.Reachable' A.genesisPayload)
    {H : A.Blk} (hH : H ∈ fg.tree) : (fg.σ H.root).s ≤ H.slot := by
  obtain ⟨c, _, _, hlast, hcs⟩ := Store.chain_state_of_chain_with
    Store.finalitySpec_updateFinality' hr.reachableWith H hH
  rcases hlast with ⟨rfl, _⟩ | hlast
  · have h := (show P.fg.chainState [] = some (FG.ChainState.init P.fg) from rfl).symm.trans hcs
    rw [← Option.some.inj h]
    exact Nat.zero_le _
  · obtain ⟨c', rfl⟩ := List.getLast?_eq_some_iff.1 hlast
    have e : ∀ l : List A.Blk, (List.map Block.fgView l : List (FG.FGBlock P.fg.n)) =
        l.map (fun B => (Block.fgView B : FG.FGBlock P.n)) := fun _ => rfl
    rw [e, List.map_append, List.map_singleton] at hcs
    obtain ⟨σ₀, _, hσ⟩ :=
      Option.bind_eq_some_iff.1 ((FG.FGParams.chainState_append P.fg _ _).symm.trans hcs)
    exact (P.fg.stateTransition_L_s hσ).2.1.le

theorem honest_block_accepted_from' {s₀ : A.State}
    (hq : ({ A with initial := s₀ } : NodeAC P).Requirements)
    (hg : (P.genesisBlock A.genesisPayload).RootOk dg) (cfg cfg' : Config A) (t : Time) (x : Nat)
    (fgDue : Bool) (hR : Node.Reachable' proposer dg self cfg s₀)
    (hs : Node.Step' proposer dg self cfg (.tick x fgDue) t cfg')
    (hp : Proposes proposer self t) :
    let st₁ := (tickStep' proposer dg self cfg.st t x .acTick).1
    let r := acProposal' st₁ t
    ∀ d p, r.2.2 = some (d, p) →
      let B := mkBlock dg self r.1.fg t x d.head p
      d.head ∈ r.1.fg.tree ∧ r.1.fg.Anc r.1.fg.F d.head ∧ d.head.slot < B.slot ∧
      (∀ a ∈ B.fgPayload, a.WellFormed ∧ (r.1.fg.σ d.head.root).validAtt a) ∧
      A.validPayload B ∧ B.RootOk dg ∧
      (NoCollOn dg (insert B r.1.fg.tree) → r.1.fg.blocks B.root = none ∧
        ∃ fg', r.1.fg.onBlock' B = some fg') := by
  dsimp only
  intro d p hdp
  rw [Node.step'_iff] at hs
  have hI := (nInv_of_reachable' proposer dg self hR).mono dg self hs.1
  have h₁ := hI.tickStep proposer dg self x .acTick
  obtain ⟨t₀, ht₀, hRA⟩ := h₁.ac (payloadFrom_initial hq self)
  have hcoh := (Store.accepted_tree_with Store.finalitySpec_updateFinality'
    h₁.fg.reachableWith).2.1
  have hts : t = P.slotTime (P.slotOf t) := hp.2.1
  have hprop : (A.proposal (tickStep' proposer dg self cfg.st t x .acTick).1.ac
      (frame' (tickStep' proposer dg self cfg.st t x .acTick).1)
      (P.slotTime (P.slotOf t))).2 = some (d, p) := by
    rw [← hts]
    simpa only [acProposal'_eq] using hdp
  obtain ⟨hHt, hFH⟩ := proposal_parent_held _ hq.heads self _ hcoh _ _ t₀
    (ACInterface.reachableAtFrom_iff.1 hRA) (P.slotOf t) (hts ▸ ht₀) d p hprop
  have hslot := slot_lt_of_tick' proposer dg self hR
    ((Node.step'_iff _ _ _ _ _ _ _).2 hs) hp
  have hHt' : d.head ∈ (tickStep' proposer dg self cfg.st t x .acTick).1.fg.tree := by
    rw [frame'_eq, Store.toFrame'_tree] at hHt
    exact hHt.1
  have hFH' : (tickStep' proposer dg self cfg.st t x .acTick).1.fg.Anc
      (tickStep' proposer dg self cfg.st t x .acTick).1.fg.F d.head := by
    rw [frame'_eq, Store.toFrame'_F] at hFH
    exact hFH.mono fun _ h => by rw [Store.toFrame'_tree] at h; exact h.1
  have hHs : d.head.slot < P.slotOf t := hslot _ (by
    simpa only [tickStep'_eq, acCall'_eq] using hHt')
  have hatts : ∀ a ∈
      (mkBlock dg self (tickStep' proposer dg self cfg.st t x .acTick).1.fg t x d.head p).fgPayload,
      a.WellFormed ∧
        ((tickStep' proposer dg self cfg.st t x .acTick).1.fg.σ d.head.root).validAtt a := by
    intro a ha
    obtain ⟨ha, hv⟩ := List.mem_filter.1 ha
    simp only [decide_eq_true_eq] at hv
    exact ⟨h₁.wf hq a ha, hv.1⟩
  simp only [acProposal'_eq] at ⊢
  refine ⟨hHt', hFH', hHs, hatts,
    hq.payload self _ hcoh _ _ t₀ (ACInterface.reachableAtFrom_iff.1 hRA)
      (P.slotOf t) (hts ▸ ht₀) d p hprop _ rfl rfl, rfl, fun hnc => ?_⟩
  set fg := (tickStep' proposer dg self cfg.st t x .acTick).1.fg with hfg
  set B := mkBlock dg self fg t x d.head p with hB
  have hnone : fg.blocks B.root = none := by
    cases hb : fg.blocks B.root with
    | none => rfl
    | some X =>
      exfalso
      have hXr := Store.blocks_root_with Store.finalitySpec_updateFinality' h₁.fg.reachableWith hb
      have hX : X ∈ fg.tree := by
        change fg.blocks X.root = some X
        rw [hXr]; exact hb
      have hXB := hnc X (Set.mem_insert_of_mem _ hX) B (Set.mem_insert _ _)
        ((h₁.roots hg X hX).symm.trans (hXr.trans rfl))
      have := hslot X (by simpa only [hfg, tickStep'_eq, acCall'_eq] using hX)
      rw [hXB.2.1] at this
      exact lt_irrefl _ this
  refine ⟨hnone, ?_⟩
  have hHb : fg.blocks d.head.root = some d.head := hHt'
  have hst : (fg.σ d.head.root).s < B.slot := lt_of_le_of_lt (σ_slot' h₁.fg hHt') hHs
  obtain ⟨σ', hσ'⟩ : ∃ σ', P.fg.stateTransition (fg.σ d.head.root) B.fgView = some σ' :=
    ⟨_, P.fg.stateTransition_eq_some.2 ⟨⟨hst, hatts⟩, rfl⟩⟩
  refine Option.ne_none_iff_exists'.1 ?_
  rw [Store.onBlock'_eq, show B.parent = some d.head.root from rfl]
  dsimp only
  split_ifs with hc
  · exfalso
    simp only [hnone, hHb, Option.isSome_none, Option.isNone_some, Bool.false_eq_true,
      false_or] at hc
    exact hc ((Anc.mono (Set.subset_insert _ _) hFH').tail
      ⟨Set.mem_insert_of_mem _ hHt', Set.mem_insert _ _, rfl⟩)
  · rw [hσ']
    exact Option.some_ne_none _

end Consensus.Goldilocks.Compose

end
