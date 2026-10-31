module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Goldilocks Refinement: the engine's outbox

The bookkeeping of the bodies (votes and attestations) an honest node queues for release.

* **One vote between ticks.** Only `try_vote` emits: at most one vote per call, from a state with
  `voted_slot ≠ slot(t)`, after which `voted_slot = slot(t)`; a restart emits nothing (it is not
  joined at its own time). So the deliveries of one time queue at most one vote
  (`process_oneVote`).
* **The engine's duty steps** (`dutyStep_poll_rel`, `dutyStep_poll_sub`,
  `dutyStep_propose_shape`, `gossip_unsigned`, `dutyStep_carried`): a poll step releases at most
  the head of its outbox, the proposal at most the own block, the gossip only unsigned objects.
* **The outbox across a tick** (`outbox_after_tick`): the node's tick and the own block queue at
  most one vote between them (the AC votes on its tick at `t_s + Δ`, on its own block only at
  `t_s`), so the two trailing polls leave the outbox empty.
* **At most one vote queued at every cut** (`outbox_inv`), and the queued bodies go out at the
  next tick (`pending_released`). Delivery polls also drain votes; the outbox is empty between
  engine events (`outbox_empty`), discharging `releasedFrom_of_pending`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

/-! ## One vote per slot -/

section OneVote

variable {sp : SAParams} {FGP : Type}

/-- A call from `A` at `t` that is not a restart, to `A'` with the emissions `es`: it keeps
`restart_time`, keeps `voted_slot` or sets it to `slot(t)`, and emits at most one vote, only from a
joined `A` with `voted_slot ≠ slot(t)`, after which `voted_slot = slot(t)`. -/
def VoteStep (A A' : SAState sp.n) (es : List (SA.Em sp FGP)) (t : Time) : Prop :=
  A'.restartTime = A.restartTime ∧
    (A'.votedSlot = A.votedSlot ∨ A'.votedSlot = sp.slot t) ∧ es.length ≤ 1 ∧
    ∀ e ∈ es, SA.joined sp A t ∧ A.votedSlot ≠ sp.slot t ∧ A'.votedSlot = sp.slot t

private theorem VoteStep.refl (A : SAState sp.n) (t : Time) :
    VoteStep (FGP := FGP) A A [] t :=
  ⟨rfl, Or.inl rfl, Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩

private theorem VoteStep.pre {A B A' : SAState sp.n} {es : List (SA.Em sp FGP)} {t : Time}
    (h : VoteStep B A' es t) (hv : B.votedSlot = A.votedSlot)
    (hr : B.restartTime = A.restartTime) : VoteStep A A' es t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₁.trans hr, hv ▸ h₂, h₃, fun e he => ?_⟩
  obtain ⟨e₂, e₃, e₄⟩ := h₄ e he
  exact ⟨by unfold SA.joined at e₂ ⊢; rwa [← hr], hv ▸ e₃, e₄⟩

private theorem VoteStep.post {A A' A'' : SAState sp.n} {es : List (SA.Em sp FGP)} {t : Time}
    (h : VoteStep A A' es t) (hv : A''.votedSlot = A'.votedSlot)
    (hr : A''.restartTime = A'.restartTime) : VoteStep A A'' es t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨hr.trans h₁, hv ▸ h₂, h₃, fun e he => hv ▸ h₄ e he⟩

private theorem admitVote_keeps (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (SA.admitVote sp A t v).votedSlot = A.votedSlot ∧
      (SA.admitVote sp A t v).restartTime = A.restartTime := by
  unfold SA.admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem updateLatestConfirmed_keeps (A : SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (C : SA.Blk sp.n FGP) : (SA.updateLatestConfirmed sp A Φ C).votedSlot = A.votedSlot ∧
      (SA.updateLatestConfirmed sp A Φ C).restartTime = A.restartTime := by
  unfold SA.updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_keeps (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot ∧
      (SA.optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold SA.optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_keeps _ _ _

private theorem updateConfirmation_keeps (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    (s : Nat) : (SA.updateConfirmation sp A Φ t s).votedSlot = A.votedSlot ∧
      (SA.updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold SA.updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs
    · exact ⟨rfl, rfl⟩
    · exact updateLatestConfirmed_keeps _ _ _

private theorem blockReceipt_keeps (A : SAState sp.n) (t : Time) (B : SA.Blk sp.n FGP) :
    (SA.blockReceipt sp A t B).votedSlot = A.votedSlot ∧
      (SA.blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold SA.blockReceipt
  generalize SA.blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => SA.admitVote sp A t v) A').votedSlot = A'.votedSlot ∧
      (l.foldl (fun A v => SA.admitVote sp A t v) A').restartTime = A'.restartTime from
    h { A with blockStamp := Function.update A.blockStamp B.root (SA.ETime.of t) }
  induction l with
  | nil => exact fun _ => ⟨rfl, rfl⟩
  | cons v l ih =>
    intro A'
    simp only [List.foldl_cons]
    exact ⟨(ih _).1.trans (admitVote_keeps _ _ _).1, (ih _).2.trans (admitVote_keeps _ _ _).2⟩

private theorem tryVote_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : VoteStep A (SA.tryVote sp self A Φ t).1 (SA.tryVote sp self A Φ t).2 t := by
  unfold SA.tryVote
  dsimp only
  split_ifs with h₁ h₂
  · exact VoteStep.refl A t
  · exact VoteStep.refl A t
  all_goals
    simp only [not_or, not_not, not_lt] at h₁
    obtain ⟨hj, hv, -⟩ := h₁
    have k₁ := fun A₁ v => ((optimistic_keeps (SA.admitVote sp A₁ t v) Φ t).1.trans
      (admitVote_keeps A₁ t v).1)
    have k₂ := fun A₁ v => ((optimistic_keeps (SA.admitVote sp A₁ t v) Φ t).2.trans
      (admitVote_keeps A₁ t v).2)
    refine ⟨k₂ _ _, Or.inr (k₁ _ _), by simp, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact ⟨hj, hv, k₁ _ _⟩

private theorem acOnBlock_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) (B : SA.Blk sp.n FGP) :
    VoteStep A (SA.acOnBlock sp self A Φ t B).1 (SA.acOnBlock sp self A Φ t B).2 t :=
  (tryVote_voteStep _ _ _ _).pre
    ((optimistic_keeps _ _ _).1.trans (blockReceipt_keeps _ _ _).1)
    ((optimistic_keeps _ _ _).2.trans (blockReceipt_keeps _ _ _).2)

private theorem acRestart_emits_nil (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (ht : 0 ≤ t) :
    (SA.acRestart sp ro self A Φ t).2 = [] := by
  unfold SA.acRestart
  suffices h : ∀ (l : List (SA.Blk sp.n FGP)) (acc : SAState sp.n × List (SA.Em sp FGP)),
      acc.1.restartTime = (t : WithBot Time) → acc.2 = [] →
      (l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2))
        acc).2 = [] from h _ _ rfl rfl
  intro l
  induction l with
  | nil => exact fun _ _ h => h
  | cons B l ih =>
    intro acc hr he
    obtain ⟨h₁, -, -, h₄⟩ := acOnBlock_voteStep self acc.1 Φ t B
    have hnil : (SA.acOnBlock sp self acc.1 Φ t B).2 = [] := by
      cases hc : (SA.acOnBlock sp self acc.1 Φ t B).2 with
      | nil => rfl
      | cons e es =>
        exact absurd (h₄ e (hc ▸ List.mem_cons_self)).1
          (SA.not_joined_of_restartTime sp ht hr)
    exact ih _ (h₁.trans hr) (by simp [he, hnil])

/-- **One vote per call.** A call of the node's AC at `t ≥ 0` other than a restart is a
`VoteStep`; a restart emits nothing. -/
theorem step_voteStep (ro : ReplayOrder sp (List (FG.Att sp.n))) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : (goldilocksNode sp ro).Frm) (t : Time) (ht : 0 ≤ t)
    (c : (goldilocksNode sp ro).Call) :
    (c = .restart ∧ ((goldilocksNode sp ro).step self A Φ t c).2 = []) ∨
      VoteStep A ((goldilocksNode sp ro).step self A Φ t c).1
        ((goldilocksNode sp ro).step self A Φ t c).2 t := by
  cases c with
  | tick =>
    right
    change VoteStep A (SA.acOnTick sp self A Φ t).1 (SA.acOnTick sp self A Φ t).2 t
    unfold SA.acOnTick
    dsimp only
    have hr : VoteStep A
        (if t = sp.ts (sp.slot t) + sp.Δ then SA.tryVote sp self A Φ t else (A, [])).1
        (if t = sp.ts (sp.slot t) + sp.Δ then SA.tryVote sp self A Φ t else (A, [])).2 t := by
      split_ifs
      · exact tryVote_voteStep _ _ _ _
      · exact VoteStep.refl A t
    generalize (if t = sp.ts (sp.slot t) + sp.Δ then SA.tryVote sp self A Φ t else (A, [])) = r
      at hr ⊢
    split_ifs
    · exact hr.post (updateConfirmation_keeps _ _ _ _).1 (updateConfirmation_keeps _ _ _ _).2
    · exact hr
    · exact VoteStep.refl A t
  | proposal =>
    right
    change VoteStep A (SA.acProposal sp A Φ t).1 [] t
    refine ⟨?_, Or.inl ?_, Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩ <;>
      (unfold SA.acProposal; split_ifs <;> rfl)
  | toFG =>
    right
    change VoteStep A (SA.acToFG sp A Φ t).1 [] t
    have h : (SA.acToFG sp A Φ t).1.votedSlot = A.votedSlot ∧
        (SA.acToFG sp A Φ t).1.restartTime = A.restartTime := by
      unfold SA.acToFG
      dsimp only
      split_ifs
      · split
        · exact ⟨rfl, rfl⟩
        · split_ifs <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    exact ⟨h.2, Or.inl h.1, Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩
  | message m =>
    right
    exact (tryVote_voteStep _ _ _ _).pre
      ((optimistic_keeps _ _ _).1.trans (admitVote_keeps _ _ _).1)
      ((optimistic_keeps _ _ _).2.trans (admitVote_keeps _ _ _).2)
  | block B => exact Or.inr (acOnBlock_voteStep _ _ _ _ _)
  | restart => exact Or.inl ⟨rfl, acRestart_emits_nil ro self A Φ t ht⟩

/-- A restart at `t ≥ 0` emits nothing (it is not joined at its own time). -/
theorem restart_emits_nil (ro : ReplayOrder sp (List (FG.Att sp.n))) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : (goldilocksNode sp ro).Frm) (t : Time) (ht : 0 ≤ t) :
    ((goldilocksNode sp ro).step self A Φ t .restart).2 = [] :=
  acRestart_emits_nil ro self A Φ t ht

/-- The AC's tick emits only at `t_s + Δ`. -/
theorem acOnTick_emits (ro : ReplayOrder sp (List (FG.Att sp.n))) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : (goldilocksNode sp ro).Frm) (t : Time)
    (h : ((goldilocksNode sp ro).step self A Φ t .tick).2 ≠ []) :
    t = sp.ts (sp.slot t) + sp.Δ := by
  change (SA.acOnTick sp self A Φ t).2 ≠ [] at h
  unfold SA.acOnTick at h
  dsimp only at h
  split_ifs at h with h₁ h₂ <;> first | exact absurd rfl h | assumption

end OneVote

/-! ## The outbox at a delivery -/

section Deliver

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The votes a handler's cuts queue: its AC cut's emissions. -/
private theorem handler_voteStep (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (ht : 0 ≤ t)
    (e : Event (goldilocksNode sp ro)) (hne : ∀ x, e ≠ .tick x) (hnr : e ≠ .restart) :
    ∃ (A' : SAState sp.n) (es : List (SA.Em sp (List (FG.Att sp.n)))),
      VoteStep st.ac A' es t ∧ (exec proposer dg self st t e).1.ac = A' ∧
        emitted (exec proposer dg self st t e).2 = es.map fun e => .vote (encodeVote e.msg) := by
  have hstep : ∀ (st' : NodeState (goldilocksNode sp ro)) (c : (goldilocksNode sp ro).Call),
      st'.ac = st.ac → c ≠ .restart →
      VoteStep st.ac ((goldilocksNode sp ro).step self st'.ac (frame st') t c).1
        ((goldilocksNode sp ro).step self st'.ac (frame st') t c).2 t := by
    intro st' c hac hc
    rw [hac]
    rcases step_voteStep ro self st.ac (frame st') t ht c with ⟨h, -⟩ | h
    · exact absurd h hc
    · exact h
  cases e with
  | tick x => exact absurd rfl (hne x)
  | restart => exact absurd rfl hnr
  | attestation a => exact ⟨st.ac, [], VoteStep.refl _ _, rfl, rfl⟩
  | message m =>
    refine ⟨_, _, hstep st (.message m) rfl (by simp), rfl, ?_⟩
    simp [exec, onMessage, acCall, emitted]
  | block B =>
    by_cases hf : sp.toParams.slotOf t < B.slot
    · exact ⟨st.ac, [], VoteStep.refl _ _, by simp [exec, onBlock, hf], by
        simp [exec, onBlock, hf, emitted]⟩
    · cases hfg : st.fg.onBlock B with
      | none =>
        exact ⟨st.ac, [], VoteStep.refl _ _, by simp [exec, onBlock, hf, hfg], by
          simp [exec, onBlock, hf, hfg, emitted]⟩
      | some fg' =>
        refine ⟨_, _, hstep { st with fg := fg' } (.block B) rfl (by simp), ?_, ?_⟩
        · simp [exec, onBlock, hf, hfg, acCall]
        · simp [exec, onBlock, hf, hfg, acCall, emitted]

/-- At most one queued vote, of a state that has voted in the slot of `t`. -/
def OneVote (t : Time) (σ : State sp ro) : Prop :=
  (∀ b ∈ σ.outbox, ∃ w, b = .vote w) ∧
    (σ.outbox = [] ∨ ∃ b, σ.outbox = [b] ∧ σ.node.ac.votedSlot = sp.slot t)

/-- At most one vote queued, all votes. -/
def AtMostOneVote (σ : State sp ro) : Prop :=
  (∀ b ∈ σ.outbox, ∃ w, b = .vote w) ∧ σ.outbox.length ≤ 1

/-- `AtMostOneVote` unfolded. -/
theorem atMostOneVote_iff (σ : State sp ro) :
    AtMostOneVote σ ↔ (∀ b ∈ σ.outbox, ∃ w, b = .vote w) ∧ σ.outbox.length ≤ 1 := Iff.rfl

theorem OneVote.atMost {t : Time} {σ : State sp ro} (h : OneVote t σ) : AtMostOneVote σ := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h | ⟨b, h, -⟩ <;> simp [h]

/-- Processing one received object at clock `t ≥ 0` keeps `OneVote t`. -/
theorem processOne_oneVote (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) {t : Time} (ht : 0 ≤ t) (σ : State sp ro) (o : Wire sp.n)
    (hnow : σ.now = t) (h : OneVote t σ) : OneVote t (processOne hs σ o) := by
  obtain ⟨-, -, -, -, -, hnode⟩ := processOne_eq (fun _ => σ.self) dg hs σ o
  have hout := processOne_outbox_eq (fun _ => σ.self) dg hs σ o
  cases he : canonEvent sp ro hs o with
  | none =>
    rw [he] at hnode hout
    simp only [Option.elim_none, List.append_nil] at hnode hout
    unfold OneVote
    rw [hout, hnode]
    exact h
  | some e =>
    rw [he] at hnode hout
    simp only [Option.elim_some] at hnode hout
    obtain ⟨A', es, hvs, hac, hem⟩ := handler_voteStep (fun _ => σ.self)
      dg σ.self σ.node σ.now (hnow ▸ ht) e
      (canonEvent_ne_tick he) (by
        rintro rfl
        rcases canonEvent_eq_some he with ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> cases h)
    rw [hnow] at hvs
    obtain ⟨-, hv₁, hlen, hv₂⟩ := hvs
    unfold OneVote
    rw [hout, hnode, hac, hem]
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · exact h.1 b hb
      · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
        exact ⟨_, rfl⟩
    rcases h.2 with h0 | ⟨b, hb, hvs⟩
    · rw [h0, List.nil_append]
      cases es with
      | nil => exact Or.inl rfl
      | cons e es =>
        cases es with
        | nil => exact Or.inr ⟨_, rfl, (hv₂ e List.mem_cons_self).2.2⟩
        | cons => simp at hlen
    · have hnil : es = [] := by
        cases es with
        | nil => rfl
        | cons e _ => exact absurd hvs (hv₂ e List.mem_cons_self).2.1
      subst hnil
      refine Or.inr ⟨b, by simp [hb], ?_⟩
      rcases hv₁ with h' | h'
      · exact h'.trans hvs
      · exact h'

/-- A delivery at clock `t ≥ 0` keeps `OneVote t`. -/
theorem process_oneVote (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) {t : Time} (ht : 0 ≤ t) :
    ∀ (os : List (Wire sp.n)) (σ : State sp ro), σ.now = t → OneVote t σ →
      OneVote t (os.foldl (processOne hs) σ)
  | [], _, _, h => h
  | o :: os, σ, hnow, h => by
    rw [List.foldl_cons]
    obtain ⟨-, -, -, hnow₁, -, -⟩ := processOne_eq (fun _ => σ.self) dg hs σ o
    exact process_oneVote dg hs ht os _ (hnow₁.trans hnow)
      (processOne_oneVote dg hs ht σ o hnow h)

end Deliver

/-! ## The engine's duty steps, release by release -/

section Duties

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The state a poll step pops from: after the FG update when it is due. -/
noncomputable def pollPre (st : State sp ro) : State sp ro :=
  if st.fgDue then fgUpdate st else st

/-- `pollPre` unfolded. -/
theorem pollPre_eq (st : State sp ro) : pollPre st = if st.fgDue then fgUpdate st else st := by
  rfl

/-- A recorded unsigned object keeps the outbox. -/
theorem recordOwn_none_outbox (st : State sp ro) (m : Model.Msg (Header Info) Body)
    (cs : List (Wire sp.n)) hs : (recordOwn st (.mk .none m cs) hs).outbox = st.outbox := by
  cases m with
  | data b => cases b <;> rfl
  | item h => rfl

/-- The FG update queues at most the attestation it signs. -/
theorem fgUpdate_outbox (st : State sp ro) :
    (fgUpdate st).outbox = st.outbox ∨ ∃ a, (fgUpdate st).outbox = st.outbox ++ [.att a] := by
  unfold fgUpdate
  dsimp only
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩

/-- A poll step pops the head of `pollPre`'s outbox. -/
theorem poll_outbox (st : State sp ro) (t : Time) :
    (poll st t).1.outbox = (pollPre st).outbox.tail ∧
      (poll st t).2 = (pollPre st).outbox.head?.map fun b => (b, []) := by
  unfold poll pollPre
  dsimp only
  split <;> rename_i h <;> rw [h] <;> exact ⟨rfl, rfl⟩

/-- Two poll steps empty an outbox of at most one body. -/
theorem poll_poll_nil (st : State sp ro) (t t' : Time) (h : st.outbox.length ≤ 1) :
    (poll (poll st t).1 t').1.outbox = [] := by
  have h₁ : (pollPre st).outbox.length ≤ 2 := by
    unfold pollPre
    split
    · rcases fgUpdate_outbox st with h' | ⟨a, h'⟩
      · rw [h']; omega
      · rw [h', List.length_append, List.length_singleton]; omega
    · omega
  have h₂ : pollPre (poll st t).1 = (poll st t).1 := by
    unfold pollPre; rw [poll_fgDue]; rfl
  rw [(poll_outbox _ t').1, h₂, (poll_outbox st t).1]
  match hq : (pollPre st).outbox with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rw [hq] at h₁; simp at h₁

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The object a poll step of `v` releases for the body `b`. -/
noncomputable abbrev pollObj (v : V) (b : Body) : (Model.protoOf (compiled (family S)) E).Object :=
  .mk (.signed (rho.ownKey v) .poll) (.data b) []

omit [DecidableEq V] in
/-- The candidate of the engine's poll duty is the shape's poll body. -/
theorem act_poll_snd (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Nat) :
    ((Model.protoOf (compiled (family S)) E).act nd.st (.poll t)).2 =
      (poll (shapeOf S hn nd) t).2.map (fun bc => (.data bc.1, bc.2)) := by
  change Option.map _ ((family S (pubOf E)).poll nd.st.1 t).2 = _
  simp only [family, dite_eq_left hn]; rfl

omit [DecidableEq V] in
/-- A duty step appends what it releases to `seen`. -/
theorem dutyStep_seen (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty) :
    (rho.dutyStep v nd d).1.seen = nd.seen ++ (rho.dutyStep v nd d).2 := by
  unfold Model.Run.dutyStep
  split
  · exact Model.releaseAll_seen _ _ _ _
  · exact (List.append_nil _).symm

omit [DecidableEq V] in
/-- A duty step releases only objects whose carried objects the node has seen. -/
theorem dutyStep_carried (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty) :
    ∀ c ∈ (rho.dutyStep v nd d).2, ∀ x ∈ c.carried, x ∈ Model.closure nd.seen := by
  intro c hc x hx
  unfold Model.Run.dutyStep at hc
  split at hc <;> (try simp at hc)
  generalize hl : rho.signedCandidate v d ((Model.protoOf (compiled (family S)) E).act nd.st d).2
    = l at hc
  have hlen : l.length ≤ 1 := by
    rw [← hl]; unfold Model.Run.signedCandidate
    split
    · split <;> simp
    · simp
  match l, hlen with
  | [], _ => simp [Model.releaseAll] at hc
  | [c'], _ =>
    unfold Model.releaseAll at hc
    split at hc
    · rename_i h
      simp only [Model.releaseAll, List.mem_singleton] at hc
      subst hc
      have h1 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1
      unfold Model.releasable at h1
      exact of_decide_eq_true (List.all_eq_true.1 h1 x hx)
    · simp [Model.releaseAll] at hc

omit [DecidableEq V] in
/-- What a poll step releases: at most the poll object of the head of `pollPre`'s outbox. -/
theorem dutyStep_poll_sub (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Nat) : ∀ o ∈ (rho.dutyStep v nd (.poll t)).2,
      ∃ b, (pollPre (shapeOf S hn nd)).outbox.head? = some b ∧ o = pollObj S rho v b := by
  intro o ho
  unfold Model.Run.dutyStep at ho
  split at ho <;> (try simp at ho)
  obtain ⟨m, cs, hact, -, rfl⟩ :=
    (rho.mem_signedCandidate).mp (Model.releaseAll_subset _ _ _ _ o ho)
  rw [act_poll_snd S hn, (poll_outbox _ _).2] at hact
  cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
  | none => simp [hh] at hact
  | some b =>
    simp only [hh, Option.map_some] at hact
    obtain ⟨rfl, rfl⟩ := hact
    exact ⟨b, rfl, rfl⟩

omit [DecidableEq V] in
/-- A poll step of a node selected in the poll role releases the head of `pollPre`'s outbox
when the own-object guard passes. -/
theorem dutyStep_poll_rel (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) {b : Body}
    (hb : (pollPre (shapeOf S hn nd)).outbox.head? = some b)
    (hp : Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
      (pollObj S rho v b) = true) :
    (rho.dutyStep v nd (.poll t)).2 = [pollObj S rho v b] := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (family S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [act_poll_snd S hn, (poll_outbox _ _).2, hb]
  have hrole : (Model.protoOf (compiled (family S)) E).role (.poll t) = .poll := rfl
  simp only [Option.map_some, Model.Run.signedCandidate, hrole]
  rw [ite_eq_left hsel]
  have hc : (Model.releasable nd.seen (pollObj S rho v b) &&
      Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v) nd.seen
        (pollObj S rho v b)) = true :=
    Bool.and_eq_true_iff.2 ⟨by simp [Model.releasable, Model.Obj.carried], hp⟩
  unfold Model.releaseAll
  split
  · rfl
  · rename_i h
    apply False.elim
    apply h
    apply Bool.and_eq_true_iff.2
    refine ⟨hc, ?_⟩
    change (dependencies _).ready _ (.mk (.signed _ .poll) (.data b) []) = true
    cases b <;> rfl

omit [DecidableEq V] in
include hn in
/-- The node's tick step releases nothing. -/
theorem dutyStep_pollPropose_snd (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Nat) :
    (rho.dutyStep v nd (.pollPropose t)).2 = [] := by
  unfold Model.Run.dutyStep
  have h2 : ((Model.protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).2 = none := by
    change Option.map _ ((family S (pubOf E)).pollPropose nd.st.1 t).2 = none
    simp only [family, dite_eq_left hn]; rfl
  dsimp only
  rw [h2]
  split <;> rfl

omit [DecidableEq V] in
/-- The gossip releases only unsigned objects. -/
theorem gossip_unsigned (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) :
    ∀ o ∈ (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) nd.st t)).2,
      o.auth = .none := by
  intro o ho
  obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp (Model.releaseAll_subset _ _ _ _ o ho)
  rfl

omit [DecidableEq V] in
/-- The gossip keeps the outbox: its candidates are unsigned. -/
theorem gossip_outbox (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) :
    (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) nd.st t)).1).outbox =
      (shapeOf S hn nd).outbox := by
  suffices h : ∀ (nd' : Model.Node (Model.protoOf (compiled (family S)) E))
      (cs : List (Model.protoOf (compiled (family S)) E).Object), (∀ c ∈ cs, c.auth = .none) →
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd'
        cs).1).outbox = (shapeOf S hn nd').outbox from
    h _ _ fun c hc => by
      obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp hc
      rfl
  intro nd' cs
  induction cs generalizing nd' with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hc
    unfold Model.releaseAll
    split
    · rw [ih _ fun c' h => hc c' (List.mem_cons_of_mem _ h)]
      obtain ⟨a, m, cs'⟩ := c
      have : a = .none := hc _ List.mem_cons_self
      subst this
      exact recordOwn_none_outbox _ _ _ _
    · exact ih _ fun c' h => hc c' (List.mem_cons_of_mem _ h)

omit [DecidableEq V] in
/-- The shape after the proposal duty: the proposal's, possibly with the own block recorded. -/
theorem dutyStep_propose_shape (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.ownKey v ∈ rho.sel (.proposer s)) :
    shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1 = (propose (shapeOf S hn nd) s).1 ∨
      ∃ c hs', shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1 =
        recordOwn (propose (shapeOf S hn nd) s).1 c hs' := by
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (family S)) E).role (.propose s hs) =
    .proposer s from rfl, hsel, ↓reduceIte]
  generalize (Model.protoOf (compiled (family S)) E).act nd.st (.propose s hs) = a at hact1
  cases hc : rho.signedCandidate v (.propose s hs) a.2 with
  | nil => exact Or.inl hact1
  | cons c cs =>
    have hcs : cs = [] := by
      unfold Model.Run.signedCandidate at hc
      split at hc
      · split at hc
        · simp only [List.cons.injEq] at hc; exact hc.2.symm
        · cases hc
      · cases hc
    subst hcs
    unfold Model.releaseAll
    split
    · exact Or.inr ⟨c, Model.digests rho.hash c, by
        change recordOwn (a.1.1 hn) _ _ = _; rw [hact1]⟩
    · exact Or.inl hact1

/-- Recording an own object queues at most the emissions of the own block's handler. -/
theorem recordOwn_outbox (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    (recordOwn st o hs).outbox = st.outbox ∨ ∃ B,
      (recordOwn st o hs).outbox =
        st.outbox ++ emitted (Node.onBlock st.self st.node st.now B).2 := by
  unfold recordOwn
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- The slot proposal keeps the outbox, the own index and the clock. -/
theorem propose_keeps' (st : State sp ro) (s : Slot) :
    (propose st s).1.outbox = st.outbox ∧ (propose st s).1.self = st.self ∧
      (propose st s).1.now = st.now := by
  refine ⟨?_, propose_self _ _, propose_now _ _⟩
  unfold propose
  dsimp only
  split <;> rfl

end Duties

/-! ## The outbox across a tick -/

section TickOutbox

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- The AC does not vote on its tick at a slot start: it votes on its tick only at `t_s + Δ`. -/
theorem slotStart_ne_tickVote (t : Time) (s : Nat)
    (hts : t = (skeleton (pubOf E)).grid.slotTime s) :
    t ≠ (S.params (pubOf E) hn).ts ((S.params (pubOf E) hn).slot t) +
      (S.params (pubOf E) hn).Δ := by
  intro h
  rw [← slotTime_eq S hn s, (S.params (pubOf E) hn).slotTime_eq] at hts
  have hΔ : 0 < (S.params (pubOf E) hn).Δ := (S.params (pubOf E) hn).toParams.hΔ
  set k : Int := ((S.params (pubOf E) hn).slot t : Int)
  have h' : (S.params (pubOf E) hn).Δ * (4 * (s : Int) - 4 * k - 1) = 0 := by
    have e1 := hts
    have e2 := h
    simp only [SA.SAParams.ts] at e2
    change t = 4 * (S.params (pubOf E) hn).Δ * (s : Int) at e1
    linear_combination e1.symm.trans e2
  clear_value k
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' hΔ.ne'
  · have h3 : (4 * (s : ℤ) - 4 * k - 1 : ℤ) = 0 := h''
    omega

omit [DecidableEq V] in
/-- The shape after the tick's first three duties: the node's tick after two poll steps of the
clocked state. -/
theorem pre_shape (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    shapeOf S hn (rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
      (Model.mempool rho.inbox v t), nd.seen⟩
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
        List (Model.protoOf (compiled (family S)) E).Duty)).1 =
      nodeTick (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1 := by
  erw [runDuties_fst_cons, runDuties_fst_cons, runDuties_fst_cons, runDuties_fst_nil]
  rw [dutyStep_pollPropose _ _ _ _ _ _ hsel, dutyStep_poll _ _ _ _ _ _ hsel,
    dutyStep_poll _ _ _ _ _ _ hsel]
  rfl

omit [DecidableEq V] in
/-- After the proposal duty of a tick at `t ≥ 0` (from the node `N3` after the first three duties,
with at most one body queued before the tick and no FG update due) at most one body is queued. -/
theorem outbox_after_pre (v : V) (σ : State (S.params (pubOf E) hn) (S.ro _)) (t : Time)
    (ht : 0 ≤ t) (hf : σ.fgDue = false) (hb : σ.outbox.length ≤ 1)
    (N3 : Model.Node (Model.protoOf (compiled (family S)) E))
    (hN3 : shapeOf S hn N3 = nodeTick (poll (poll { σ with now := t } t.toNat).1 t.toNat).1) :
    (shapeOf S hn (rho.runDuties v N3
      ((skeleton (pubOf E)).proposeAt t)).1).outbox.length ≤ 1 := by
  set σc : State (S.params (pubOf E) hn) (S.ro _) := { σ with now := t }
  have h2 : (poll (poll σc t.toNat).1 t.toNat).1.outbox = [] := by
    rw [(poll_outbox _ _).1]
    have e1 : pollPre σc = σc := by unfold pollPre; rw [show σc.fgDue = false from hf]; rfl
    have e2 : pollPre (poll σc t.toNat).1 = (poll σc t.toNat).1 := by
      unfold pollPre; rw [poll_fgDue]; rfl
    rw [e2, (poll_outbox _ _).1, e1]
    change σ.outbox.tail.tail = []
    match hq : σ.outbox with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rw [hq] at hb; simp at hb
  have h2s : (poll (poll σc t.toNat).1 t.toNat).1.now = t := by rw [poll_now, poll_now]
  have h3 : (shapeOf S hn N3).outbox.length ≤ 1 ∧
      ((shapeOf S hn N3).outbox ≠ [] →
        t = (S.params (pubOf E) hn).ts ((S.params (pubOf E) hn).slot t) +
          (S.params (pubOf E) hn).Δ) := by
    rw [hN3]
    unfold nodeTick
    split_ifs
    · simp only [apply, h2, List.nil_append, emitted, acCall, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_map]
      rw [h2s]
      constructor
      · rcases step_voteStep (sp := S.params (pubOf E) hn) (S.ro _) _ _ _ t ht .tick with
          ⟨h, -⟩ | ⟨-, -, h, -⟩
        · cases h
        · exact h
      · intro hne
        exact acOnTick_emits (S.ro _) _ _ _ t (fun h => hne (by rw [h]; rfl))
    · rw [h2]; simp
  have hnow : (shapeOf S hn N3).now = t := by rw [hN3, nodeTick_now, h2s]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, _⟩ | ⟨s, hs, hone, hts⟩
  · rw [hnil]; erw [runDuties_fst_nil]; exact h3.1
  · rw [hone]; erw [runDuties_fst_cons, runDuties_fst_nil]
    change (shapeOf S hn (rho.dutyStep v N3 (.propose s hs)).1).outbox.length ≤ 1
    by_cases hsel : rho.ownKey v ∉ rho.sel (.proposer s)
    · unfold Model.Run.dutyStep
      rw [ite_eq_right (show rho.ownKey v ∉ rho.sel
        ((Model.protoOf (compiled (family S)) E).role (.propose s hs)) from hsel)]
      exact h3.1
    have hsel := Classical.not_not.mp hsel
    have h30 : (shapeOf S hn N3).outbox = [] := by
      by_contra hne
      exact slotStart_ne_tickVote S hn t s hts (h3.2 hne)
    rcases dutyStep_propose_shape S rho hn v N3 s hs hsel with h | ⟨c, hs', h⟩
    · refine (congrArg (fun st : State _ _ => st.outbox.length) h).trans_le ?_
      rw [(propose_keeps' _ _).1, h30]; simp
    · refine (congrArg (fun st : State _ _ => st.outbox.length) h).trans_le ?_
      rcases recordOwn_outbox (propose (shapeOf S hn N3) s).1 c hs' with h' | ⟨B, h'⟩
      · rw [h', (propose_keeps' _ _).1, h30]; simp
      · rw [h', (propose_keeps' _ _).1, h30, List.nil_append, (propose_keeps' _ _).2.2, hnow]
        obtain ⟨A', es, hvs, -, hem⟩ := handler_voteStep (runProposer S rho hn)
          (digestOf S rho) _ _ t ht (.block B)
          (fun x h => by cases h) (fun h => by cases h)
        change (emitted
          (exec (runProposer S rho hn) (digestOf S rho) _ _ t (.block B)).2).length ≤ 1
        rw [hem, List.length_map]
        exact hvs.2.2.1

omit [DecidableEq V] in
/-- The outbox after an awake tick at `t ≥ 0` from a state with no FG update due and at most one
body queued is empty. -/
theorem outbox_after_tick (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true) (hf : (shapeOf S hn nd).fgDue = false)
    (hb : (shapeOf S hn nd).outbox.length ≤ 1) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (rho.tick nd v t).1).outbox = [] := by
  rw [tick_of_awake S rho v nd t hw, gossip_outbox, duties_eq S t ht, runDuties_fst_append]
  erw [runDuties_fst_cons, runDuties_fst_nil, dutyStep_poll _ _ _ _ _ _ hsel]
  unfold dutiesInit
  erw [runDuties_fst_append, runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil,
    dutyStep_poll _ _ _ _ _ _ hsel]
  exact poll_poll_nil _ _ _
    (outbox_after_pre S rho hn v (shapeOf S hn nd) t ht hf hb _ (pre_shape S rho hn v nd t hsel))

end TickOutbox

/-! ## At most one vote queued at every cut -/

section Invariant

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The last event of `v` before cut `i` is a restart. -/
def LastRestart (v : V) (i : Nat) : Prop :=
  ∃ r < i, ∃ t, rho.events[r]? = some (.restart v t) ∧
    ∀ l, r < l → l < i → ∀ e, rho.events[l]? = some e → e.node ≠ v

/-- A delivery never directly follows a restart of its node: the node's tick at the restart's time
comes in between. -/
theorem not_lastRestart_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) : ¬ LastRestart S rho v i := by
  rintro ⟨r, hri, t', hr, hno⟩
  have hmr := List.mem_of_getElem? hr
  obtain ⟨ht', hw, -⟩ := hv.restart_at_wake v t' hmr
  have hh := hv.in_horizon _ hmr
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp
    (hv.tick_total v (hv.honest_only _ hmr) t' hh.1 hh.2 hw)
  have hrq : r < q := by
    rcases lt_trichotomy q r with h | rfl | h
    · rcases keyLe_of_index_lt S rho hv hq hr h with h' | h'
      · exact absurd h' (lt_irrefl _)
      · exact absurd h'.2 (by simp [Model.Event.phase])
    · rw [hr] at hq; cases hq
    · exact h
  have hqi : q < i := by
    rcases lt_trichotomy q i with h | rfl | h
    · exact h
    · rw [he] at hq; cases hq
    · have h1 := keyLe_of_index_lt S rho hv hr he hri
      rcases keyLe_of_index_lt S rho hv he hq h with h' | h'
      · rcases h1 with h1 | h1
        · have a : t' < t := h1; have b : t < t' := h'; exact absurd (a.trans b) (lt_irrefl _)
        · have a : t' = t := h1.1; have b : t < t' := h'; rw [a] at b; exact absurd b (lt_irrefl _)
      · exact absurd h'.2 (by simp [Model.Event.phase])
  exact hno q hrq hqi _ hq rfl

/-- **At most one vote queued.** At every cut an honest node's outbox holds at most one body, a
vote; unless its last event was a restart, a queued vote is one of the slot of its clock, cast by
the node (`voted_slot`). -/
theorem outbox_inv (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) :
    ∀ i, AtMostOneVote (stateAt S rho hn v i) ∧
      (LastRestart S rho v i ∨ OneVote (stateAt S rho hn v i).now (stateAt S rho hn v i))
  | 0 => ⟨⟨fun b hb => absurd hb List.not_mem_nil, Nat.zero_le _⟩,
      Or.inr ⟨fun b hb => absurd hb List.not_mem_nil, Or.inl rfl⟩⟩
  | i + 1 => by
    obtain ⟨ih₁, ih₂⟩ := outbox_inv hv v hv' i
    have hext : LastRestart S rho v i → (∀ e, rho.events[i]? = some e → e.node ≠ v) →
        LastRestart S rho v (i + 1) := by
      rintro ⟨r, hri, t, hr, hno⟩ hi
      refine ⟨r, by omega, t, hr, fun l h1 h2 e he => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
      · exact hno l h1 h2 e he
      · exact hi e he
    match he : rho.events[i]? with
    | none =>
      rw [stateAt_succ_none S rho hn v he]
      exact ⟨ih₁, ih₂.imp_left fun h => hext h fun e he' => by rw [he] at he'; cases he'⟩
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          have hm := List.mem_of_getElem? he
          rw [stateAt_tick S rho hn w he]
          have h0 := outbox_after_tick S rho hn w (rho.stateBefore i w) t
            (hv.in_horizon _ hm).1 (hv.tick_awake w t hm) (fgDue_eq_false S rho hn w i) ih₁.2
            (poll_selected S rho hv w)
          refine ⟨⟨fun b hb => ?_, by rw [h0]; exact Nat.zero_le _⟩,
            Or.inr ⟨fun b hb => ?_, Or.inl h0⟩⟩ <;>
            (rw [h0] at hb; exact absurd hb List.not_mem_nil)
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          have hm := List.mem_of_getElem? he
          have ht : 0 ≤ t := (hv.in_horizon _ hm).1
          have hnow : (stateAt S rho hn w i).now = t :=
            (now_eq_lastClock S rho hn hv w i).trans (lastClock_of_deliver S rho hv w he)
          have h1 : OneVote t (stateAt S rho hn w i) := by
            rcases ih₂ with h | h
            · exact absurd h (not_lastRestart_deliver S rho hv he)
            · rwa [hnow] at h
          rw [stateAt_deliver S rho hn w he]
          have h2 := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht
            (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn w i) hnow h1
          have hnow' : (process (stateAt S rho hn w i) o (Model.digests rho.hash o)).now = t :=
            (process_now _ _ _).trans hnow
          have hd := deliver_pres S rho hn
            (fun st => st.fgDue = false ∧ st.now = t ∧ OneVote t st)
            (by
              intro st τ h
              rcases h with ⟨hf, hn', hq⟩
              unfold poll
              simp only [hf, Bool.false_eq_true, ite_false]
              rcases hq with ⟨hvotes, hnil | ⟨b, hb, hslot⟩⟩
              · simp only [hnil]; exact ⟨hf, hn', hvotes, Or.inl hnil⟩
              · simp only [hb]
                exact ⟨trivial, hn', (by simp), Or.inl rfl⟩)
            (by
              intro st m cs hs h
              cases m with
              | item => exact h
              | data b => cases b <;> exact h)
            w (rho.stateBefore i w) o t
            ⟨(process_fgDue _ _ _).trans (fgDue_eq_false S rho hn w i), hnow', h2⟩
          refine ⟨hd.2.2.atMost, Or.inr ?_⟩
          rw [hd.2.1]
          exact hd.2.2
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          have hm := List.mem_of_getElem? he
          have ht : 0 ≤ t := (hv.in_horizon _ hm).1
          rw [stateAt_restart S rho hn w he]
          have hout : (restore (rho.ownKey w) (stateAt S rho hn w i) t).outbox =
              (stateAt S rho hn w i).outbox := by
            change (stateAt S rho hn w i).outbox ++ emitted [Cut.ac ⟨.restart, _,
              ((goldilocksNode _ _).step _ _ _ t .restart).2⟩] = _
            have h0 : ((goldilocksNode (S.params (pubOf E) hn) (S.ro _)).step (rho.ownKey w)
                (stateAt S rho hn w i).node.ac (frame (stateAt S rho hn w i).node) t .restart).2 =
                [] := restart_emits_nil _ _ _ _ t ht
            rw [h0]
            simp [emitted]
          refine ⟨by unfold AtMostOneVote; rw [hout]; exact ih₁, Or.inl ?_⟩
          exact ⟨i, by omega, t, he, fun l h1 h2 => absurd h2 (by omega)⟩
      · rw [state_of_other S rho hn v i e he hne]
        exact ⟨ih₁, ih₂.imp_left fun h => hext h fun e' he' => by
          rw [he] at he'; cases he'; exact hne⟩

end Invariant

section DeliveryReleases

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

include hn in
/-- A delivery releases only a queued vote or unsigned gossip, never an attestation. -/
theorem deliver_not_att (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    {o : (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) (a : FG.Att (Fintype.card V)) :
    attObj a ∉ rho.releasesAt i := by
  have hm := List.mem_of_getElem? he
  have ht := (hv.in_horizon _ hm).1
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hpre : OneVote t (stateAt S rho hn v i) := by
    rcases (outbox_inv S rho hn hv v (hv.honest_only _ hm) i).2 with h | h
    · exact absurd h (not_lastRestart_deliver S rho hv he)
    · rwa [hnow] at h
  have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht
    (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) hnow hpre
  intro h
  simp only [Model.Run.releasesAt, he] at h
  unfold Model.Run.deliver at h
  simp only at h
  rcases List.mem_append.mp h with h | h
  · rw [deliverDuties_eq S t ht] at h
    erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at h
    simp only [List.append_nil] at h
    obtain ⟨b, hb, heq⟩ := dutyStep_poll_sub S rho hn v _ _ _ h
    have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
      (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
    change (pollPre (process (stateAt S rho hn v i) o (Model.digests rho.hash o))).outbox.head? =
      some b at hb
    rw [pollPre_eq, hf] at hb
    obtain ⟨w, rfl⟩ := hproc.1 b (List.mem_of_mem_head? hb)
    have hmsg := congrArg Model.Obj.msg heq
    simp only [attObj, Model.Obj.msg] at hmsg
    cases hmsg
  · have := gossip_unsigned S rho _ _ _ _ h
    simp [attObj, Model.Obj.auth] at this

end DeliveryReleases

/-! ## Pending bodies go out at the next tick -/

section Pending

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- In an admitted run the poll role selects every key. -/
theorem selValid_poll (hsel : rho.SelValid) : rho.sel .poll = Finset.univ := by
  have h := hsel .poll
  change ((family S (pubOf E)).skel.pollSel).Admits _ at h
  exact h

/-- **Pending bodies go out at the next tick.** At a tick of an honest node, every body queued in
its outbox before the tick (at most one vote, `outbox_inv`) is released, signed by the node's own
key in the poll role, by the tick's first poll step. -/
theorem pending_released (hv : rho.ExecutionValid) {j : Nat} {v : V} {t : Time}
    (hv' : v ∈ rho.honest) (he : rho.events[j]? = some (.tick v t)) :
    ∀ b ∈ (stateAt S rho hn v j).outbox, pollObj S rho v b ∈ rho.releasesAt j := by
  intro b hb
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ t := (hv.in_horizon _ hm).1
  obtain ⟨⟨hvote, hlen⟩, -⟩ := outbox_inv S rho hn hv v hv' j
  have hone : (stateAt S rho hn v j).outbox = [b] := by
    match hq : (stateAt S rho hn v j).outbox with
    | [] => rw [hq] at hb; cases hb
    | [b'] => rw [hq, List.mem_singleton] at hb; rw [hb]
    | _ :: _ :: _ => rw [hq] at hlen; simp at hlen
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ v t (hv.tick_awake v t hm), duties_eq S t ht]
  unfold dutiesInit
  simp only [List.cons_append]
  refine List.mem_append_left _ ?_
  erw [Model.Run.runDuties_cons]
  refine List.mem_append_left _ ?_
  have hsel : rho.ownKey v ∈ rho.sel .poll := by
    rw [selValid_poll S rho hv.selValid]; exact Finset.mem_univ _
  have key : ∀ l, l = [pollObj S rho v b] → pollObj S rho v b ∈ l :=
    fun l hl => hl ▸ List.mem_singleton_self _
  refine key _ (dutyStep_poll_rel S rho hn v _ _ hsel (b := b) ?_ ?_)
  · have hf := fgDue_eq_false S rho hn v j
    change (pollPre { stateAt S rho hn v j with now := t }).outbox.head? = some b
    unfold pollPre
    rw [show ({ stateAt S rho hn v j with now := t } : State _ _).fgDue = false from hf]
    simp only [Bool.false_eq_true, ite_false]
    rw [hone]; rfl
  · obtain ⟨w, rfl⟩ := hvote b hb
    exact protects_of_not_att S _ _ _ (fun k w' h => by cases h)

/-- A delivery's poll drains its at-most-one queued vote. -/
private theorem outbox_after_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    {o : (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v (i + 1)).outbox = [] := by
  have hm := List.mem_of_getElem? he
  have ht := (hv.in_horizon _ hm).1
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hpre : OneVote t (stateAt S rho hn v i) := by
    rcases (outbox_inv S rho hn hv v (hv.honest_only _ hm) i).2 with h | h
    · exact absurd h (not_lastRestart_deliver S rho hv he)
    · rwa [hnow] at h
  have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht
    (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) hnow hpre
  have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
    (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
  rw [stateAt_deliver S rho hn v he]
  unfold Model.Run.deliver
  rw [gossip_outbox, deliverDuties_eq S t ht]
  erw [runDuties_fst_cons, runDuties_fst_nil, dutyStep_poll _ _ _ _ _ _ (poll_selected S rho hv v)]
  change (poll (process (stateAt S rho hn v i) o (Model.digests rho.hash o)) t.toNat).1.outbox = []
  rw [(poll_outbox _ _).1, pollPre_eq, hf]
  simp only [Bool.false_eq_true, ite_false]
  change OneVote t (process (stateAt S rho hn v i) o (Model.digests rho.hash o)) at hproc
  rcases hproc.2 with h | ⟨b, h, -⟩ <;> rw [h] <;> rfl

/-- Honest nodes have no pending bodies between engine events: ticks and deliveries drain
their queues, and restarts emit nothing. -/
private theorem outbox_empty (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) :
    ∀ i, (stateAt S rho hn v i).outbox = []
  | 0 => rfl
  | i + 1 => by
    have ih := outbox_empty hv v hv' i
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hnode : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_tick S rho hn v he]
          exact outbox_after_tick S rho hn v _ t
            (hv.in_horizon _ (List.mem_of_getElem? he)).1
            (hv.tick_awake v t (List.mem_of_getElem? he)) (fgDue_eq_false S rho hn v i)
            (by change (stateAt S rho hn v i).outbox.length ≤ 1; rw [ih]; simp)
            (poll_selected S rho hv v)
        | deliver w o t =>
          simp only [Model.Event.node] at hnode
          subst w
          exact outbox_after_deliver S rho hn hv he
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_restart S rho hn v he]
          have hnil := restart_emits_nil (S.ro _) (rho.ownKey v)
            (stateAt S rho hn v i).node.ac (frame (stateAt S rho hn v i).node) t
            (hv.in_horizon _ (List.mem_of_getElem? he)).1
          change (stateAt S rho hn v i).outbox ++ emitted [Cut.ac ⟨.restart, _, _⟩] = []
          rw [hnil, ih]
          simp [emitted]
      · rw [state_of_other S rho hn v i ev he hnode]; exact ih

/-- **A body pending after an event was released at that event's time.** In this engine
there is no pending body after an honest event. -/
theorem releasedFrom_of_pending (hv : rho.ExecutionValid) {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) {b : Body}
    (hb : b ∈ (stateAt S rho hn ev.node (i + 1)).outbox) :
    ReleasedFrom S rho ev.node
      (Model.Obj.mk (.signed (rho.ownKey ev.node) .poll) (.data b) []) ev.time := by
  rw [outbox_empty S rho hn hv ev.node (hv.honest_only _ (List.mem_of_getElem? he))] at hb
  exact absurd hb List.not_mem_nil


end Pending

end Consensus.Goldilocks.Refinement

end
