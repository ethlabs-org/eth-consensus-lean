module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import Mathlib.Tactic.IntervalCases

public section

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

section Pools

variable {sp : SAParams} {FGP : Type}

private def PoolIn (P : Vote sp.n → Prop) (A : SAState sp.n) : Prop :=
  ∀ s, ∀ v ∈ A.pool s, P v

private theorem pool_admit {P : Vote sp.n → Prop} {A : SAState sp.n}
    (h : PoolIn P A) (t : Time) (v : Vote sp.n) (hv : P v) :
    PoolIn P (SA.admitVote sp A t v) := by
  intro s w hw
  unfold SA.admitVote at hw
  split_ifs at hw
  · exact h s w hw
  · exact h s w hw
  · simp only [Function.update_apply] at hw
    split_ifs at hw with hs
    · rcases List.mem_append.mp hw with hw | hw
      · exact h _ w hw
      · exact (List.mem_singleton.mp hw) ▸ hv
    · exact h s w hw

private theorem pool_tryVote {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (h : PoolIn P A)
    (he : ∀ e ∈ (SA.tryVote sp self A Φ t).2, P e.msg) :
    PoolIn P (SA.tryVote sp self A Φ t).1 := by
  unfold SA.tryVote at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢
  · exact h
  · exact h
  all_goals
    intro s v hv
    rw [SA.optimistic_pool_eq] at hv
    apply pool_admit (A := _) (P := P) (t := t) (v := _) ?_ ?_ s v hv
    · exact h
    · exact he _ (List.mem_singleton_self _)

private theorem pool_receipt {P : Vote sp.n → Prop} (A : SAState sp.n) (t : Time)
    (B : SA.Blk sp.n FGP) (h : PoolIn P A) (hB : ∀ v ∈ SA.blockVotes B, P v) :
    PoolIn P (SA.blockReceipt sp A t B) := by
  unfold SA.blockReceipt
  generalize hl : SA.blockVotes B = l at *
  have key : ∀ (l : List (Vote sp.n)) (A : SAState sp.n), PoolIn P A →
      (∀ v ∈ l, P v) → PoolIn P (l.foldl (fun A v => SA.admitVote sp A t v) A) := by
    intro l
    induction l with
    | nil => exact fun _ h _ => h
    | cons v l ih =>
      intro A h hl
      exact ih _ (pool_admit h t v (hl v List.mem_cons_self))
        (fun w hw => hl w (List.mem_cons_of_mem v hw))
  exact key l _ h hB

private theorem pool_block {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (B : SA.Blk sp.n FGP)
    (h : PoolIn P A) (hB : ∀ v ∈ SA.blockVotes B, P v)
    (he : ∀ e ∈ (SA.acOnBlock sp self A Φ t B).2, P e.msg) :
    PoolIn P (SA.acOnBlock sp self A Φ t B).1 := by
  apply pool_tryVote self _ Φ t _ he
  intro s v hv
  rw [SA.optimistic_pool_eq] at hv
  exact pool_receipt A t B h hB s v hv

private theorem pool_message {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (m : Vote sp.n)
    (h : PoolIn P A) (hm : P m)
    (he : ∀ e ∈ (SA.acOnMessage sp self A Φ t m).2, P e.msg) :
    PoolIn P (SA.acOnMessage sp self A Φ t m).1 := by
  apply pool_tryVote self _ Φ t _ he
  intro s v hv
  rw [SA.optimistic_pool_eq] at hv
  exact pool_admit h t m hm s v hv

private theorem pool_tick {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (h : PoolIn P A)
    (he : ∀ e ∈ (SA.acOnTick sp self A Φ t).2, P e.msg) :
    PoolIn P (SA.acOnTick sp self A Φ t).1 := by
  unfold SA.acOnTick at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢
  all_goals first
    | exact h
    | exact pool_tryVote self A Φ t h he
    | intro s v hv
      rw [SA.updateConfirmation_pool_eq] at hv
      first | exact h s v hv | exact pool_tryVote self A Φ t h he s v hv

/-- Restart replay only imports votes from its frame and its own emissions. The replay
enumeration exists for every well-formed frame; no global collision assumption is needed. -/
theorem restart_pool_inventory (P : Vote sp.n → Prop) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    (hΦ : FrameOK Φ) (hB : ∀ B ∈ Φ.tree, ∀ v ∈ SA.blockVotes B, P v)
    (he : ∀ e ∈ (SA.acRestart sp ro self A Φ t).2, P e.msg) :
    ∀ s, ∀ v ∈ (SA.acRestart sp ro self A Φ t).1.pool s, P v := by
  have hl := ro.parentOrder t Φ (SA.parentOrder_exists sp hΦ)
  have hlist : ∀ B ∈ ro.order t Φ, ∀ v ∈ SA.blockVotes B, P v :=
    fun B h => hB B ((hl.2.1 B).mp h).1
  unfold SA.acRestart at he ⊢
  generalize ro.order t Φ = l at hlist he ⊢
  have key : ∀ (l : List (SA.Blk sp.n FGP)) (acc : SAState sp.n × List (SA.Em sp FGP)),
      PoolIn P acc.1 → (∀ B ∈ l, ∀ v ∈ SA.blockVotes B, P v) →
      (∀ e ∈ (l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).2, P e.msg) →
      PoolIn P (l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1 := by
    intro l
    induction l with
    | nil => exact fun _ h _ _ => h
    | cons B l ih =>
      intro acc h hB he
      have append_mem : ∀ (l : List (SA.Blk sp.n FGP)) acc,
          acc.2 ⊆ (l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
            (r.1, acc.2 ++ r.2)) acc).2 := by
        intro l
        induction l with
        | nil => exact fun _ _ h => h
        | cons B l ih => exact fun acc e he => ih _ (List.mem_append_left _ he)
      apply ih ((SA.acOnBlock sp self acc.1 Φ t B).1,
        acc.2 ++ (SA.acOnBlock sp self acc.1 Φ t B).2)
        (pool_block self _ Φ t B h (hB B List.mem_cons_self) ?_)
        (fun C hC => hB C (List.mem_cons_of_mem B hC)) he
      intro e he'
      exact he e (append_mem l _ (List.mem_append_right _ he'))
  exact key l _ (fun s v hv => False.elim (List.not_mem_nil hv)) hlist he

end Pools

section Inventory

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Inventory before an engine operation. The predicate will be membership in the seen
closure or in the queue; stored block payloads are needed again by restart replay. -/
private structure Inventory (P : Wire sp.n → Prop)
    (st : NodeState (goldilocksNode sp ro)) : Prop where
  reachable : st.fg.Reachable ([], [])
  blocks : ∀ B ∈ st.fg.tree, ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o
  votes : PoolIn (fun v => P (voteObj v)) st.ac
  atts : ∀ a ∈ st.fg.atts, P (attObj a)

private theorem inventory_init (P : Wire sp.n → Prop) :
    Inventory P (Node.init (goldilocksNode sp ro)) := by
  refine ⟨Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
  · intro B hB o ho
    change (if B.root = sp.genesisRoot then some (sp.toParams.genesisBlock ([], []))
      else none) = some B at hB
    split_ifs at hB
    · cases Option.some.inj hB
      simp [payloadObjs, Params.genesisBlock] at ho
  · intro s v hv
    exact False.elim (List.not_mem_nil hv)
  · intro a ha
    exact False.elim (List.not_mem_nil ha)

private theorem payload_vote {P : Wire sp.n → Prop} {B : Blk sp}
    (h : ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o) :
    ∀ v ∈ SA.blockVotes B, P (voteObj v) := by
  intro v hv
  exact h _ (List.mem_append_right _
    (List.mem_map.mpr ⟨v, List.mem_append_left _ hv, rfl⟩))

private theorem inventory_att {P : Wire sp.n → Prop} {st : NodeState (goldilocksNode sp ro)}
    (h : Inventory P st) (a : FG.Att sp.n) (ha : P (attObj a)) :
    Inventory P (Node.onAttestation st a).1 := by
  obtain ⟨hb, _, hats⟩ := Store.onAttestation_fields st.fg a
  refine ⟨h.reachable.tail (Or.inr ⟨a, rfl⟩), ?_, h.votes, ?_⟩
  · intro B hB
    exact h.blocks B (by
      change (st.fg.onAttestation a).blocks B.root = some B at hB
      rwa [hb] at hB)
  · intro b hb
    rcases hats b hb with hb | rfl
    · exact h.atts b hb
    · exact ha

private theorem inventory_accept {P : Wire sp.n → Prop} {st : NodeState (goldilocksNode sp ro)}
    (h : Inventory P st) {B : Blk sp} {fg' : Store sp.toParams (Payload sp.n)}
    (hacc : st.fg.onBlock B = some fg')
    (hB : ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o) :
    Inventory P { st with fg := fg' } := by
  obtain ⟨_, _, _, _, _, _, hblocks, _, hatts⟩ := Store.onBlock_fields hacc
  refine ⟨h.reachable.tail (Or.inl ⟨B, hacc⟩), ?_, h.votes, ?_⟩
  · intro C hC
    rw [(Store.tree_grows sp.toParams (Payload sp.n) ([], []) st.fg h.reachable).1 B fg' hacc] at hC
    rcases hC with rfl | hC
    · exact hB
    · exact h.blocks C hC
  · intro a ha
    rcases hatts a ha with ha | ha
    · exact h.atts a ha
    · exact hB _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))

private theorem inventory_call {P : Wire sp.n → Prop} {st : NodeState (goldilocksNode sp ro)}
    (h : Inventory P st) (self : Fin sp.n) (t : Time)
    (c : (goldilocksNode sp ro).Call)
    (hc : match c with
      | .block B => ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o
      | .message v => P (voteObj v)
      | _ => True)
    (he : ∀ e ∈ ((goldilocksNode sp ro).step self st.ac (frame st) t c).2,
      P (voteObj e.msg)) : Inventory P (Node.acCall self st t c).1 := by
  refine ⟨h.reachable, h.blocks, ?_, h.atts⟩
  cases c with
  | block B => exact pool_block self _ _ t B h.votes (payload_vote hc) he
  | message v => exact pool_message self _ _ t v h.votes hc he
  | tick => exact pool_tick self _ _ t h.votes he
  | restart =>
    refine restart_pool_inventory (fun v => P (voteObj v)) ro self st.ac (frame st) t
      (Store.frame_realization sp.toParams (Payload sp.n) ([], []) st.fg h.reachable).1 ?_ he
    intro B hB
    exact payload_vote (h.blocks B hB.1)
  | proposal =>
    change PoolIn _ (SA.acProposal sp st.ac (frame st) t).1
    unfold SA.acProposal
    split_ifs <;> exact h.votes
  | toFG =>
    change PoolIn _ (SA.acToFG sp st.ac (frame st) t).1
    unfold SA.acToFG
    split_ifs
    · split
      · exact h.votes
      · split_ifs <;> exact h.votes
    · exact h.votes

private theorem inventory_mono {P Q : Wire sp.n → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory P st) (hPQ : ∀ o, P o → Q o) :
    Inventory Q st :=
  ⟨h.reachable, fun B hB o ho => hPQ o (h.blocks B hB o ho),
    fun s v hv => hPQ _ (h.votes s v hv), fun a ha => hPQ _ (h.atts a ha)⟩

private theorem inventory_block {P : Wire sp.n → Prop} {st : NodeState (goldilocksNode sp ro)}
    (h : Inventory P st) (self : Fin sp.n) (t : Time) (B : Blk sp)
    (hB : ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o)
    (he : ∀ b ∈ emitted (Node.onBlock self st t B).2,
      ∀ v, b = .vote (encodeVote v) → P (voteObj v)) :
    Inventory P (Node.onBlock self st t B).1 := by
  unfold Node.onBlock at he ⊢
  split_ifs at he ⊢
  · exact h
  · split
    · exact h
    · rename_i fg' hfg
      rw [hfg] at he
      apply inventory_call (inventory_accept h hfg hB) self t (.block B) hB
      intro e he'
      apply he (.vote (encodeVote e.msg)) ?_ e.msg rfl
      simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil]
      exact List.mem_map.mpr ⟨e, he', rfl⟩

private theorem inventory_proposal {P : Wire sp.n → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory P st) (t : Time) :
    Inventory P (Node.acProposal st t).1 := by
  refine ⟨h.reachable, h.blocks, ?_, h.atts⟩
  change PoolIn _ (SA.acProposal sp st.ac (frame st) t).1
  unfold SA.acProposal
  split_ifs <;> exact h.votes

private theorem inventory_toFG {P : Wire sp.n → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory P st) (t : Time) :
    Inventory P (Node.acToFG st t).1 := by
  refine ⟨h.reachable, h.blocks, ?_, h.atts⟩
  change PoolIn _ (SA.acToFG sp st.ac (frame st) t).1
  unfold SA.acToFG
  split_ifs
  · split
    · exact h.votes
    · split_ifs <;> exact h.votes
  · exact h.votes

private theorem proposal_inventory {P : Wire sp.n → Prop} (st : State sp ro)
    (h : Inventory P st.node) (s : Slot) {par : ParentRef} {info : Info}
    {cs : List (Wire sp.n)} (hp : (propose st s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, P o := by
  unfold propose Node.acProposal at hp
  dsimp only [goldilocksNode, SA.goldilocksSA] at hp
  unfold SA.acProposal at hp
  dsimp only at hp
  split_ifs at hp
  · have hcs := (Option.some.inj hp)
    cases hcs
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
      exact h.atts a (List.mem_filter.mp ha).1
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ho
      have hv' : v ∈ st.node.ac.poolAt ((sp.slot st.now : Int) - 1) := by
        rcases List.mem_append.mp hv with hv | hv
        · exact (List.mem_filter.mp hv).1
        · exact (List.mem_filter.mp (List.mem_filter.mp hv).1).1
      unfold SAState.poolAt at hv'
      split_ifs at hv'
      · cases hv'
      · exact h.votes _ v hv'

end Inventory

section ShapeInventory

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

private def Pending (st : State sp ro) (o : Wire sp.n) : Prop :=
  (∃ v, o = voteObj v ∧ .vote (encodeVote v) ∈ st.outbox) ∨
    ∃ a, o = attObj a ∧ .att (encodeAtt a) ∈ st.outbox

private def Available (seen : List (Wire sp.n)) (st : State sp ro) (o : Wire sp.n) : Prop :=
  o ∈ seen.flatMap Model.Obj.parts ∨ Pending st o

/-- Every pending admission envelope still has its vote in the stored pool. -/
private def QueuedInPool (st : State sp ro) : Prop :=
  ∀ tv ∈ st.voteForwards, tv.2 ∈ st.node.ac.pool tv.2.slot

private theorem apply_queuedInPool (st : State sp ro) r (h : QueuedInPool st)
    (hg : ∀ σ, st.node.ac.pool σ ⊆ r.1.ac.pool σ) : QueuedInPool (apply st r) := by
  intro tv htv
  by_cases hold : tv ∈ st.voteForwards
  · exact hg _ (h tv hold)
  · exact (apply_voteForward_fresh st r tv.1 tv.2 htv hold).2.2

private theorem block_queuedInPool (st : State sp ro) (B : Blk sp) (h : QueuedInPool st) :
    QueuedInPool (apply st (Node.onBlock st.self st.node st.now B)) := by
  apply apply_queuedInPool st _ h
  unfold Node.onBlock
  split_ifs
  · exact fun _ => List.Subset.refl _
  · split
    · exact fun _ => List.Subset.refl _
    · exact SA.step_pool_subset st.self st.node.ac _ st.now (.block B) (by simp)

private theorem processOne_queuedInPool hs (st : State sp ro) o (h : QueuedInPool st) :
    QueuedInPool (processOne hs st o) := by
  unfold processOne
  split
  · dsimp only
    unfold relayIf
    split <;> exact block_queuedInPool st _ h
  · apply apply_queuedInPool st _ h
    exact SA.step_pool_subset st.self st.node.ac _ st.now (.message _) (by simp)
  · unfold relayIf
    split <;> apply apply_queuedInPool st _ h <;> exact fun _ => List.Subset.refl _
  · exact h

private theorem process_queuedInPool (st : State sp ro) o hs (h : QueuedInPool st) :
    QueuedInPool (process st o hs) := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => exact h
  | cons o os ih => exact ih _ (processOne_queuedInPool hs st o h)

private theorem record_queuedInPool (st : State sp ro) o hs (h : QueuedInPool st) :
    QueuedInPool (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact block_queuedInPool st _ h
    · exact h
  · exact h

private theorem propose_queuedInPool (st : State sp ro) s (h : QueuedInPool st) :
    QueuedInPool (propose st s).1 := by
  have hp : (Node.acProposal st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acProposal sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  unfold propose
  dsimp only
  split <;> intro tv htv <;> rw [hp] <;> exact h tv htv

private theorem nodeTick_queuedInPool (st : State sp ro) (h : QueuedInPool st) :
    QueuedInPool (nodeTick st) := by
  unfold nodeTick
  split
  · apply apply_queuedInPool st _ h
    exact SA.step_pool_subset st.self st.node.ac _ st.now .tick (by simp)
  · exact h

private theorem poll_queuedInPool (st : State sp ro) t : QueuedInPool (poll st t).1 := by
  intro tv htv
  rw [poll_voteForwards] at htv
  cases htv

private theorem block_pool_subset (st : State sp ro) (B : Blk sp) (σ : Nat) :
    st.node.ac.pool σ ⊆ (apply st (Node.onBlock st.self st.node st.now B)).node.ac.pool σ := by
  unfold apply Node.onBlock
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · split
    · exact List.Subset.refl _
    · exact SA.step_pool_subset st.self st.node.ac _ st.now (.block B) (by simp) σ

private theorem record_pool_subset (st : State sp ro) o hs (σ : Nat) :
    st.node.ac.pool σ ⊆ (recordOwn st o hs).node.ac.pool σ := by
  unfold recordOwn
  split
  · exact List.Subset.refl _
  · split
    · exact block_pool_subset st _ σ
    · exact List.Subset.refl _
  · exact List.Subset.refl _

private theorem propose_pool_eq (st : State sp ro) s :
    (propose st s).1.node.ac.pool = st.node.ac.pool := by
  have hp : (Node.acProposal st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acProposal sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  unfold propose
  dsimp only
  split <;> exact hp

private theorem nodeTick_pool_subset (st : State sp ro) (σ : Nat) :
    st.node.ac.pool σ ⊆ (nodeTick st).node.ac.pool σ := by
  unfold nodeTick
  split
  · exact SA.step_pool_subset st.self st.node.ac _ st.now .tick (by simp) σ
  · exact List.Subset.refl _

/-- Polling, including the due FG update, leaves vote pools unchanged. -/
theorem poll_pool_eq (st : State sp ro) t :
    (poll st t).1.node.ac.pool = st.node.ac.pool := by
  have hp : (Node.acToFG st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acToFG sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acToFG
    split_ifs
    · split
      · rfl
      · split_ifs <;> rfl
    · rfl
  have hg : (fgUpdate st).node.ac.pool = st.node.ac.pool := by
    unfold fgUpdate
    dsimp only
    split
    · exact hp
    · split <;> exact hp
  unfold poll
  split_ifs <;> dsimp only <;> split <;> first | exact hg | rfl

private theorem parts_append {n : Nat} (a b : List (Wire n)) :
    a.flatMap Model.Obj.parts ⊆ (a ++ b).flatMap Model.Obj.parts := by
  rw [List.flatMap_append]
  exact List.subset_append_left _ _

private theorem carried_parts {n : Nat} (auth : Model.Auth n (ShapeRole Empty))
    (m : Model.Msg (Header Info) Body) (cs : List (Wire n)) {x : Wire n}
    (hx : x ∈ cs) : x ∈ (Model.Obj.mk auth m cs).parts := by
  rw [Model.Obj.parts_eq]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨x, hx,
    by rw [Model.Obj.parts_eq]; exact List.mem_cons_self⟩)

private def VoteOwned (st : State sp ro) : Prop :=
  ∀ v, .vote (encodeVote v) ∈ st.outbox → v.val = st.self

private theorem emitted_owned (self : Fin sp.n)
    (cs : List (Cut (goldilocksNode sp ro)))
    (h : ∀ ℓ, Cut.ac ℓ ∈ cs → ∀ e ∈ ℓ.emits, e.msg.val = self) :
    ∀ v, .vote (encodeVote v) ∈ emitted cs → v.val = self := by
  intro v hv
  obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
  cases c with
  | fg c => cases hv
  | ac ℓ =>
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hv
    have heq' := congrArg (decodeVote sp.n) (Body.vote.inj heq)
    simp only [decodeVote_encodeVote, Option.some.injEq] at heq'
    subst v
    exact h ℓ hc e he

private theorem apply_owned (st : State sp ro) r (h : VoteOwned st)
    (he : ∀ v, .vote (encodeVote v) ∈ emitted r.2 → v.val = st.self) :
    VoteOwned (apply st r) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h v hv
  · exact he v hv

private theorem call_owned (st : State sp ro) (c : (goldilocksNode sp ro).Call)
    (h : VoteOwned st) :
    VoteOwned (apply st ((Node.acCall st.self st.node st.now c).1,
      [(Node.acCall st.self st.node st.now c).2])) := by
  apply apply_owned st _ h
  apply emitted_owned
  intro ℓ hℓ e he
  have hℓ := Cut.ac.inj (List.mem_singleton.mp hℓ)
  subst ℓ
  exact emits_val st.self st.node.ac (frame st.node) st.now c e he

private theorem tick_owned (st : State sp ro) (h : VoteOwned st) :
    VoteOwned (nodeTick st) := by
  unfold nodeTick
  split
  · exact call_owned st .tick h
  · exact h

private theorem block_owned (st : State sp ro) (B : Blk sp) (h : VoteOwned st) :
    VoteOwned (apply st (Node.onBlock st.self st.node st.now B)) := by
  apply apply_owned st _ h
  apply emitted_owned
  intro ℓ hℓ e he
  unfold Node.onBlock at hℓ
  split_ifs at hℓ
  · cases hℓ
  · split at hℓ
    · simp at hℓ
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with hℓ | hℓ
      · cases hℓ
      · have hℓ := Cut.ac.inj hℓ
        subst ℓ
        exact emits_val _ _ _ _ _ e he

private theorem processOne_owned hs (st : State sp ro) o (h : VoteOwned st) :
    VoteOwned (processOne hs st o) := by
  classical
  unfold processOne
  split
  · dsimp only
    unfold relayIf
    split <;> exact block_owned st _ h
  · dsimp only
    exact call_owned st _ h
  · unfold relayIf
    split <;> simpa only [VoteOwned, apply, Node.onAttestation, emitted,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil] using h
  · exact h

private theorem process_owned (st : State sp ro) o hs (h : VoteOwned st) :
    VoteOwned (process st o hs) := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => exact h
  | cons o os ih => exact ih _ (processOne_owned hs st o h)

private theorem record_owned (st : State sp ro) o hs (h : VoteOwned st) :
    VoteOwned (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact block_owned st _ h
    · exact h
  · exact h

private theorem fg_owned (st : State sp ro) (h : VoteOwned st) :
    VoteOwned (fgUpdate st) := by
  unfold fgUpdate
  dsimp only
  split
  · exact h
  · split
    · exact h
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h v hv
      · cases List.mem_singleton.mp hv

private theorem poll_owned (st : State sp ro) (t : Time) (h : VoteOwned st) :
    VoteOwned (poll st t).1 := by
  have hi : VoteOwned (if st.fgDue then fgUpdate st else st) := by
    split
    · exact fg_owned st h
    · exact h
  unfold poll
  generalize (if st.fgDue then fgUpdate st else st) = pre at hi ⊢
  dsimp only
  split
  · exact hi
  · rename_i b rest he
    intro v hv
    apply hi v
    rw [he]
    exact List.mem_cons_of_mem _ hv

private theorem pending_mono {st st' : State sp ro} (h : st.outbox ⊆ st'.outbox)
    {o : Wire sp.n} : Pending st o → Pending st' o := by
  rintro (⟨v, rfl, hv⟩ | ⟨a, rfl, ha⟩)
  · exact Or.inl ⟨v, rfl, h hv⟩
  · exact Or.inr ⟨a, rfl, h ha⟩

private theorem available_mono {seen seen' : List (Wire sp.n)} {st st' : State sp ro}
    (hs : seen.flatMap Model.Obj.parts ⊆ seen'.flatMap Model.Obj.parts)
    (hq : st.outbox ⊆ st'.outbox)
    {o : Wire sp.n} : Available seen st o → Available seen' st' o :=
  Or.imp (fun h => hs h) (pending_mono hq)

private theorem apply_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (hr : ∀ P : Wire sp.n → Prop, Inventory P st.node →
      (∀ o ∈ seen.flatMap Model.Obj.parts, P o) →
      (∀ b ∈ emitted r.2, ∀ v, b = .vote (encodeVote v) → P (voteObj v)) →
      Inventory P r.1)
    (h : Inventory (Available seen st) st.node) :
    Inventory (Available seen (apply st r)) (apply st r).node := by
  apply hr
  · exact inventory_mono h (fun _ => available_mono (fun _ h => h)
      (List.subset_append_left _ _))
  · exact fun _ h => Or.inl h
  · intro b hb v hv
    exact Or.inr (Or.inl ⟨v, rfl, List.mem_append_right _ (hv ▸ hb)⟩)

private theorem tick_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (h : Inventory (Available seen st) st.node) :
    Inventory (Available seen (nodeTick st)) (nodeTick st).node := by
  unfold nodeTick
  split
  · apply apply_inventory seen st
      ((Node.acCall st.self st.node st.now .tick).1,
        [(Node.acCall st.self st.node st.now .tick).2]) ?_ h
    intro P h _ he
    apply inventory_call h st.self st.now .tick trivial
    intro e he'
    apply he (.vote (encodeVote e.msg)) ?_ e.msg rfl
    simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.mem_map.mpr ⟨e, he', rfl⟩
  · exact h

private theorem restore_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (k : Fin sp.n) (t : Time) (h : Inventory (Available seen st) st.node) :
    Inventory (Available seen (restore k st t)) (restore k st t).node := by
  apply apply_inventory seen { st with self := k, now := t }
    ((Node.acCall k st.node t .restart).1, [(Node.acCall k st.node t .restart).2]) ?_ h
  intro P h _ he
  apply inventory_call h k t .restart trivial
  intro e he'
  apply he (.vote (encodeVote e.msg)) ?_ e.msg rfl
  simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_map.mpr ⟨e, he', rfl⟩

private theorem fg_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (h : Inventory (Available seen st) st.node) :
    Inventory (Available seen (fgUpdate st)) (fgUpdate st).node := by
  unfold fgUpdate
  dsimp only
  split
  · exact inventory_toFG h st.now
  · split
    · exact inventory_toFG h st.now
    · rename_i C hC a Λ' ha
      apply inventory_att
      · have ht := inventory_toFG h st.now
        have ht' : Inventory (Available seen st)
            { (Node.acToFG st.node st.now).1 with record := Λ' } :=
          ⟨ht.reachable, ht.blocks, ht.votes, ht.atts⟩
        apply inventory_mono ht'
        intro o ho
        exact available_mono (fun _ h => h) (List.subset_append_left _ _) ho
      · exact Or.inr (Or.inr ⟨a, rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩)

private theorem processOne_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (h : Inventory (Available seen st) st.node)
    (ho : ∀ x ∈ o.parts, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (Available seen (processOne hs st o)) (processOne hs st o).node := by
  unfold processOne
  split
  · rename_i B hB
    have hcanon : o = blockObj sp B := by
      rcases canonEvent_eq_some hB with ⟨B', he, ho⟩ | ⟨v, he, _⟩ | ⟨a, he, _⟩
      · cases he; exact ho
      · cases he
      · cases he
    unfold relayIf
    dsimp only
    split_ifs <;>
      apply apply_inventory seen st (Node.onBlock st.self st.node st.now B) ?_ h
    all_goals
      intro P h hseen he
      apply inventory_block h st.self st.now B ?_ he
      intro x hx
      apply hseen x (ho x ?_)
      rw [hcanon, Model.Obj.parts_eq]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨x, hx, by rw [Model.Obj.parts_eq]; exact List.mem_cons_self⟩)
  · rename_i v hv
    have hcanon : o = voteObj v := by
      rcases canonEvent_eq_some hv with ⟨B, he, _⟩ | ⟨v', he, ho⟩ | ⟨a, he, _⟩
      · cases he
      · cases he; exact ho
      · cases he
    dsimp only
    apply apply_inventory seen st (Node.onMessage st.self st.node st.now v) ?_ h
    all_goals
      intro P h hseen he
      apply inventory_call h st.self st.now (.message v) ?_ ?_
      · apply hseen _
        rw [← hcanon]
        apply ho
        rw [Model.Obj.parts_eq]
        exact List.mem_cons_self
      · intro e he'
        apply he (.vote (encodeVote e.msg)) ?_ e.msg rfl
        simp only [Node.onMessage, emitted, acCall, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_map.mpr ⟨e, he', rfl⟩
  · rename_i a ha
    have hcanon : o = attObj a := by
      rcases canonEvent_eq_some ha with ⟨B, he, _⟩ | ⟨v, he, _⟩ | ⟨a', he, ho⟩
      · cases he
      · cases he
      · cases he; exact ho
    apply apply_inventory seen st (Node.onAttestation st.node a) ?_ h
    intro P h hseen _
    apply inventory_att h
    apply hseen _
    rw [← hcanon]
    apply ho
    rw [Model.Obj.parts_eq]
    exact List.mem_cons_self
  · exact h

private theorem process_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (h : Inventory (Available seen st) st.node)
    (ho : ∀ x ∈ o.parts, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (Available seen (process st o hs)) (process st o hs).node := by
  unfold process
  have key : ∀ (l : List (Wire sp.n)) (st : State sp ro),
      Inventory (Available seen st) st.node →
      (∀ x ∈ l, ∀ y ∈ x.parts, y ∈ seen.flatMap Model.Obj.parts) →
      Inventory (Available seen (l.foldl (processOne hs) st))
        (l.foldl (processOne hs) st).node := by
    intro l
    induction l with
    | nil => exact fun _ h _ => h
    | cons x l ih =>
      intro st h hl
      exact ih _ (processOne_inventory seen st hs x h (hl x List.mem_cons_self))
        (fun y hy => hl y (List.mem_cons_of_mem x hy))
  apply key _ st h
  intro x hx y hy
  exact ho y (Model.Obj.Contains.trans hx hy)

private theorem record_inventory (seen : List (Wire sp.n)) (st : State sp ro)
    (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (h : Inventory (Available seen st) st.node)
    (hp : ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
      ∀ atts p, decodeInfo sp.n hd.info = some (atts, p) →
      ∀ x ∈ payloadObjs atts p, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (Available seen (recordOwn st o hs)) (recordOwn st o hs).node := by
  unfold recordOwn
  split
  · exact h
  · rename_i k s hd cs
    split
    · rename_i atts p d hi hdig
      apply apply_inventory seen st _ ?_ h
      intro P h hseen he
      apply inventory_block h st.self st.now _ ?_ he
      intro x hx
      apply hseen x
      exact hp _ _ _ _ rfl _ _ hi x hx
    · exact h
  · exact h

private theorem poll_inventory (seen seen' : List (Wire sp.n)) (st : State sp ro)
    (t : Time) (h : Inventory (Available seen st) st.node)
    (hs : seen.flatMap Model.Obj.parts ⊆ seen'.flatMap Model.Obj.parts)
    (hv : ∀ v, (if st.fgDue then fgUpdate st else st).outbox.head? =
      some (.vote (encodeVote v)) → voteObj v ∈ seen'.flatMap Model.Obj.parts)
    (ha : ∀ a, (if st.fgDue then fgUpdate st else st).outbox.head? =
      some (.att (encodeAtt a)) → attObj a ∈ seen'.flatMap Model.Obj.parts) :
    Inventory (Available seen' (poll st t).1) (poll st t).1.node := by
  have hi : Inventory (Available seen (if st.fgDue then fgUpdate st else st))
      (if st.fgDue then fgUpdate st else st).node := by
    split
    · exact fg_inventory seen st h
    · exact h
  generalize he : (if st.fgDue then fgUpdate st else st) = pre at hi hv ha
  unfold poll
  rw [he]
  cases hq : pre.outbox with
  | nil =>
    simp only [hq]
    apply inventory_mono hi
    exact fun _ => available_mono hs (by simp [hq])
  | cons b rest =>
    simp only [hq]
    apply inventory_mono hi
    intro o ho
    rcases ho with ho | (⟨v, rfl, hv'⟩ | ⟨a, rfl, ha'⟩)
    · exact Or.inl (hs ho)
    · rw [hq] at hv'
      rcases List.mem_cons.mp hv' with hb | hr
      · exact Or.inl (hv v (by simp [hq, ← hb]))
      · exact Or.inr (Or.inl ⟨v, rfl, hr⟩)
    · rw [hq] at ha'
      rcases List.mem_cons.mp ha' with hb | hr
      · exact Or.inl (ha a (by simp [hq, ← hb]))
      · exact Or.inr (Or.inr ⟨a, rfl, hr⟩)

end ShapeInventory

section EngineInventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Every duty prefix preserves the fact that queued vote envelopes name stored
votes. In particular this applies to the polls of a tick, not only deliveries. -/
theorem runDuties_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.runDuties v nd ds).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool tv.2.slot := by
  exact runDuties_pres S rho hn QueuedInPool record_queuedInPool propose_queuedInPool
    nodeTick_queuedInPool (fun st t _ => poll_queuedInPool st t) v nd ds h

omit [DecidableEq V] in
/-- A single duty preserves queue backing, including its own released blocks. -/
theorem dutyStep_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.dutyStep v nd d).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool tv.2.slot := by
  exact dutyStep_pres S rho hn QueuedInPool record_queuedInPool propose_queuedInPool
    nodeTick_queuedInPool (fun st t _ => poll_queuedInPool st t) v nd d h

omit [DecidableEq V] in
/-- A single duty retains stored votes through its own-object release callbacks. -/
theorem dutyStep_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool σ := by
  intro m hm
  exact dutyStep_pres S rho hn (fun st => m ∈ st.node.ac.pool σ)
    (fun st o hs h => record_pool_subset st o hs σ h)
    (fun st s h => by rw [propose_pool_eq]; exact h)
    (fun st h => nodeTick_pool_subset st σ h)
    (fun st t h => by rw [poll_pool_eq]; exact h) v nd d hm

omit [DecidableEq V] in
/-- Duty execution never removes a stored vote; only restart replay can do so. -/
theorem runDuties_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool σ := by
  intro m hm
  exact runDuties_pres S rho hn (fun st => m ∈ st.node.ac.pool σ)
    (fun st o hs h => record_pool_subset st o hs σ h)
    (fun st s h => by rw [propose_pool_eq]; exact h)
    (fun st h => nodeTick_pool_subset st σ h)
    (fun st t h => by rw [poll_pool_eq]; exact h) v nd ds hm

omit [DecidableEq V] in
private theorem release_owned (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs)
    (h : VoteOwned (shapeOf S hn nd)) :
    VoteOwned (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
      rho.hash k nd cs).1) := by
  induction cs generalizing nd with
  | nil => exact h
  | cons c cs ih =>
    unfold Model.releaseAll
    split
    · exact ih _ (record_owned (shapeOf S hn nd) c _ h)
    · exact ih nd h

omit [DecidableEq V] in
private theorem duty_owned (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (d)
    (h : VoteOwned (shapeOf S hn nd)) :
    VoteOwned (shapeOf S hn (rho.dutyStep v nd d).1) := by
  classical
  unfold Model.Run.dutyStep
  split
  · apply release_owned
    cases d with
    | act s k => exact k.elim
    | poll t =>
      change VoteOwned (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).1.1 hn)
      rw [shapeOf_act_poll S hn]
      exact poll_owned _ _ h
    | pollPropose t =>
      change VoteOwned
          (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose t)).1.1 hn)
      rw [shapeOf_act_pollPropose S hn]
      exact tick_owned _ h
    | propose s hs =>
      change VoteOwned
          (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
      rw [shapeOf_act_propose S hn]
      intro v hv
      rw [(propose_keeps' _ _).1] at hv
      exact (h v hv).trans (propose_self _ _).symm
  · exact h

omit [DecidableEq V] in
private theorem duties_owned (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (ds)
    (h : VoteOwned (shapeOf S hn nd)) :
    VoteOwned (shapeOf S hn (rho.runDuties v nd ds).1) := by
  induction ds generalizing nd with
  | nil => exact h
  | cons d ds ih =>
    rw [runDuties_fst_cons]
    exact ih _ (duty_owned S rho hn v nd d h)

private theorem cut_owned (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i p : Nat} {nd} (hc : EngineDutyCut S rho v i p nd) :
    VoteOwned (shapeOf S hn nd) := by
  have hbase : VoteOwned (stateAt S rho hn v i) := by
    intro w hw
    rw [outbox_empty S rho hn hv v hv' i] at hw
    cases hw
  rw [stateAt_eq] at hbase
  cases hc with
  | tick he hw hp =>
    exact duties_owned S rho hn v _ _ hbase
  | deliver he hp =>
    apply duties_owned
    exact process_owned _ _ _ hbase

/-- Pending canonical votes at actual duty boundaries belong to the local signer. -/
theorem duty_cut_vote_signer (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    {i p : Nat} {nd} (hc : EngineDutyCut S rho v i p nd) (m : Vote (Fintype.card V))
    (hm : Body.vote (encodeVote m) ∈ (shapeOf S hn nd).outbox) :
    m.val = rho.ownKey v :=
  (cut_owned S rho hn hv hv' hc m hm).trans (cut_self S rho hn hc)

private theorem poll_duty_inventory (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (h : Inventory (Available nd.seen (shapeOf S hn nd)) (shapeOf S hn nd).node) :
    Inventory (Available (rho.dutyStep v nd (.poll k)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.poll k)).1))
      (shapeOf S hn (rho.dutyStep v nd (.poll k)).1).node := by
  have hsel := poll_selected S rho hv v
  rw [dutyStep_poll S rho hn v nd k hsel]
  have hmem : ∀ b, (pollPre (shapeOf S hn nd)).outbox.head? = some b →
      Model.protects (Model.protoOf (compiled (goldilocks S)) E) (rho.ownKey v) nd.seen
        (pollObj S rho v b) = true →
      pollObj S rho v b ∈ (rho.dutyStep v nd (.poll k)).1.seen.flatMap Model.Obj.parts := by
    intro b hb hp
    apply Model.mem_closure_of_mem
    rw [Simulation.dutyStep_seen S rho v nd (.poll k)]
    exact List.mem_append_right _ (dutyStep_poll_rel S rho hn v nd k hsel hb hp)
  apply poll_inventory nd.seen _ _ _ h
  · rw [Simulation.dutyStep_seen S rho v nd (.poll k)]
    exact parts_append _ _
  · intro w hw
    rw [← pollPre_eq] at hw
    have hown : VoteOwned (pollPre (shapeOf S hn nd)) := by
      rw [pollPre_eq]
      split
      · exact fg_owned _ (cut_owned S rho hn hv hv' hc)
      · exact cut_owned S rho hn hv hv' hc
    have hval := (hown w (List.mem_of_mem_head? (Option.mem_def.mpr hw))).trans
      ((by rw [pollPre_eq]; split <;> simp [fgUpdate_self] :
        (pollPre (shapeOf S hn nd)).self = (shapeOf S hn nd).self).trans
          (cut_self S rho hn hc))
    have ho : voteObj w = pollObj S rho v (.vote (encodeVote w)) := by
      unfold voteObj pollObj
      rw [hval]
      rfl
    rw [ho]
    exact hmem _ hw (protects_of_not_att S _ _ _ (fun k w h => by cases h))
  · intro a ha
    rw [← pollPre_eq] at ha
    have hpoll : (poll (nd.st.1 hn) k).2 = some (.att (encodeAtt a), []) := by
      rw [(poll_outbox _ _).2, ha]
      rfl
    obtain ⟨a', j, q, he, hval, hsign⟩ := engine_poll_att_signed S rho hn hc hd hsel hpoll
    have he' := congrArg (decodeAtt (Fintype.card V)) he
    simp only [decodeAtt_encodeAtt, Option.some.injEq] at he'
    subst a'
    have ho : attObj a = pollObj S rho v (.att (encodeAtt a)) := by
      unfold attObj pollObj
      rw [hval.trans (cut_self S rho hn hc)]
      rfl
    rw [ho]
    exact hmem _ ha (engine_poll_att_protected S rho hn hv hv' hc hd hsel hpoll)

private def PayloadCarried (o : Wire (Fintype.card V)) : Prop :=
  ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
    ∀ atts p, decodeInfo (Fintype.card V) hd.info = some (atts, p) →
      ∀ x ∈ payloadObjs atts p, x ∈ o.parts

omit [DecidableEq V] in
private theorem release_inventory (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs)
    (h : Inventory (Available nd.seen (shapeOf S hn nd)) (shapeOf S hn nd).node)
    (hp : ∀ o ∈ cs, PayloadCarried o) :
    Inventory (Available (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1.seen
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1))
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1).node := by
  induction cs generalizing nd with
  | nil => exact h
  | cons c cs ih =>
    unfold Model.releaseAll
    split
    · apply ih
      · apply record_inventory (nd.seen ++ [c]) (shapeOf S hn nd) _ c
        · apply inventory_mono h
          intro o ho
          exact available_mono (parts_append _ _)
            (fun _ h => h) ho
        · intro key s hd os he atts p hi x hx
          apply List.mem_flatMap.mpr
          exact ⟨c, List.mem_append_right _ (List.mem_singleton_self _),
            hp c List.mem_cons_self key s hd os he atts p hi x hx⟩
      · exact fun o ho => hp o (List.mem_cons_of_mem _ ho)
    · exact ih nd h (fun o ho => hp o (List.mem_cons_of_mem _ ho))

omit [DecidableEq V] in
include hn in
private theorem proposal_carried (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s) :
    ∀ o ∈ rho.signedCandidate v (.propose s hs)
      ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2,
      PayloadCarried o := by
  intro o ho
  obtain ⟨m, cs, hm, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_propose_snd S hn] at hm
  obtain ⟨⟨par, info, os⟩, hp, he⟩ := Option.mem_toList.mp hm |> Option.mem_map.mp
  cases he
  intro key slot hd cs he atts p hi x hx
  cases he
  unfold propose at hp
  dsimp only at hp
  split at hp
  · cases hp
  · cases Option.some.inj hp
    simp only [decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact carried_parts _ _ _ hx

omit [DecidableEq V] in
private theorem proposal_duty_inventory (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (h : Inventory (Available nd.seen (shapeOf S hn nd)) (shapeOf S hn nd).node) :
    Inventory (Available (rho.dutyStep v nd (.propose s hs)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1))
      (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).node := by
  unfold Model.Run.dutyStep
  split
  · apply release_inventory
    · have hact := shapeOf_act_propose S hn nd.st s hs
      change Inventory (Available nd.seen
        (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn))
        (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn).node
      rw [hact]
      have hi := inventory_proposal h (shapeOf S hn nd).now
      unfold propose
      dsimp only
      split <;> exact hi
    · exact proposal_carried S rho hn v nd s hs
  · exact h

omit [DecidableEq V] in
private theorem tick_duty_inventory (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (k : Nat)
    (h : Inventory (Available nd.seen (shapeOf S hn nd)) (shapeOf S hn nd).node) :
    Inventory (Available (rho.dutyStep v nd (.pollPropose k)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.pollPropose k)).1))
      (shapeOf S hn (rho.dutyStep v nd (.pollPropose k)).1).node := by
  rw [Simulation.dutyStep_seen S rho v nd (.pollPropose k), dutyStep_pollPropose_snd S rho hn,
    List.append_nil]
  by_cases hsel : rho.ownKey v ∈ rho.sel .poll
  · rw [dutyStep_pollPropose S rho hn v nd k hsel]
    exact tick_inventory _ _ h
  · unfold Model.Run.dutyStep
    simp only
        [show (Model.protoOf (compiled (goldilocks S)) E).role (.pollPropose k) = .poll from rfl,
      hsel, ↓reduceIte]
    exact h

private theorem prefix_inventory (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) (i : Nat)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (hcut : ∀ p, p ≤ ds.length → EngineDutyCut S rho v i p
      (rho.runDuties v nd (ds.take p)).1)
    (hsched : ∀ (p k : Nat), ds[p]? = some (ShapeDuty.poll k) →
      (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (h : Inventory (Available nd.seen (shapeOf S hn nd)) (shapeOf S hn nd).node) :
    ∀ p, p ≤ ds.length →
      let out := (rho.runDuties v nd (ds.take p)).1
      Inventory (Available out.seen (shapeOf S hn out)) (shapeOf S hn out).node := by
  intro p
  induction p with
  | zero => exact fun _ => h
  | succ p ih =>
    intro hp
    have hlt : p < ds.length := by omega
    have hi := ih (Nat.le_of_lt hlt)
    have hd := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hd]
    simp only [Option.toList_some]
    rw [runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil]
    cases he : ds[p] with
    | act s k => exact k.elim
    | propose s hs => exact proposal_duty_inventory S rho hn v _ s hs hi
    | pollPropose k => exact tick_duty_inventory S rho hn v _ k hi
    | poll k =>
      exact poll_duty_inventory S rho hn hv hv' (hcut p (Nat.le_of_lt hlt))
        (hsched p k (hd.trans (congrArg some he))) hi

private theorem event_inventory (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) :
    ∀ i, Inventory (Available (rho.stateBefore i v).seen (stateAt S rho hn v i))
      (stateAt S rho hn v i).node := by
  intro i
  induction i with
  | zero => rw [stateAt_zero]; exact inventory_init _
  | succ i ih =>
    rw [stateAt_eq] at ih ⊢
    change Inventory (Available (rho.stateBefore i v).seen (shapeOf S hn (rho.stateBefore i v)))
      (shapeOf S hn (rho.stateBefore i v)).node at ih
    have hg : ∀ nd t, Inventory (Available nd.seen (shapeOf S hn nd))
        (shapeOf S hn nd).node →
        Inventory (Available (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
          rho.hash (rho.ownKey v) nd (Model.gossipCandidates _ nd.st t)).1.seen
          (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v) nd (Model.gossipCandidates _ nd.st t)).1))
          (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
            rho.hash (rho.ownKey v) nd (Model.gossipCandidates _ nd.st t)).1).node := by
      intro nd t h
      apply release_inventory S rho hn _ nd _ h
      intro o ho
      obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
      intro key s hd cs he
      cases he
    cases he : rho.events[i]? with
    | none =>
      have heq : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp only [Model.Run.stateBefore, List.take_add_one, he, Option.toList_none,
          List.append_nil]
      simpa only [stateAt_eq, heq] using ih
    | some e =>
      change Inventory (Available (rho.stateBefore (i + 1) v).seen
        (shapeOf S hn (rho.stateBefore (i + 1) v)))
        (shapeOf S hn (rho.stateBefore (i + 1) v)).node
      rw [rho.stateBefore_succ he]
      cases e with
      | tick u t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.tick]
          split
          · rename_i hw
            apply hg
            have hi := prefix_inventory S rho hn hv hv' i
              ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
                (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
              (fun p hp => .tick he hw hp)
              (fun p k hk => Or.inl ⟨t, he, hw, hk⟩) ih _ (Nat.le_refl _)
            simpa only [List.take_length] using hi
          · exact ih
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih
      | deliver u o t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver]
          apply hg
          have hp : Inventory (Available ((rho.stateBefore i v).seen ++ [o])
              (process (stateAt S rho hn v i) o (Model.digests rho.hash o)))
              (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node := by
            rw [stateAt_eq]
            apply process_inventory
            · exact inventory_mono ih (fun _ => available_mono (parts_append _ _) (fun _ h => h))
            · intro x hx
              exact List.mem_flatMap.mpr
                ⟨o, List.mem_append_right _ (List.mem_singleton_self _), hx⟩
          rw [stateAt_eq] at hp
          have hi := prefix_inventory S rho hn hv hv' i
            ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
              (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩ _
            (fun p hp => .deliver he hp)
            (fun p k hk => Or.inr ⟨t, o, he, hk⟩) hp _ (Nat.le_refl _)
          simpa only [List.take_length] using hi
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih
      | restart u t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self]
          exact restore_inventory _ _ _ _ ih
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih

/-- At a tick duty prefix, every pooled vote is already held or pending in the
ordinary outbox. This retains the actual prefix state needed by release guards. -/
theorem tick_prefix_pool_available (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length)
    (σ : Nat) (m : Vote (Fintype.card V)) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1
    m ∈ (shapeOf S hn nd).node.ac.pool σ →
      voteObj m ∈ Model.closure nd.seen ∨
        Body.vote (encodeVote m) ∈ (shapeOf S hn nd).outbox := by
  intro nd hm
  have hi := prefix_inventory S rho hn hv hv' i
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
      (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
    (fun q hq => .tick he hw hq) (fun q k hk => Or.inl ⟨t, he, hw, hk⟩)
    (by
      have hi := event_inventory S rho hn hv v hv' i
      rw [stateAt_eq] at hi
      exact hi) p hp
  rcases hi.votes σ m hm with h | ⟨w, heq, hw⟩ | ⟨a, heq, _⟩
  · exact Or.inl h
  · have henc := congrArg Model.Obj.msg heq
    simp only [voteObj, Model.Obj.msg] at henc
    have hdec := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj (Model.Msg.data.inj henc))
    simp only [decodeVote_encodeVote, Option.some.injEq] at hdec
    exact Or.inr (hdec ▸ hw)
  · have hbad := congrArg Model.Obj.msg heq
    simp only [voteObj, attObj, Model.Obj.msg, Model.Msg.data.injEq] at hbad
    cases hbad

/-- Delivery processing keeps every queued admission's vote in the final pool. The actual
event-boundary queue is empty, and none of the delivery handlers restarts the AC. -/
theorem delivery_voteForward_in_pool (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (tv : Time × Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    tv.2 ∈ (process (stateAt S rho hn v i) o
      (Model.digests rho.hash o)).node.ac.pool tv.2.slot := by
  apply process_queuedInPool (stateAt S rho hn v i) o (Model.digests rho.hash o) ?_ tv htv
  intro q hq
  rw [voteForwards_empty S rho hn hv v i] at hq
  cases hq

/-- After processing a delivery, every stored vote is either actually held (including in
the delivered object's closure) or queued as a canonical own vote in the ordinary outbox. -/
theorem delivery_pool_available (hv : rho.ExecutionValid) {v : V} (hv' : v ∈ rho.honest)
    (i : Nat) (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (σ : Nat) (m : Vote (Fintype.card V))
    (hm : m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool σ) :
    voteObj m ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      Body.vote (encodeVote m) ∈
        (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox := by
  have hi := event_inventory S rho hn hv v hv' i
  have hp : Inventory (Available ((rho.stateBefore i v).seen ++ [o])
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)))
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node := by
    apply process_inventory
    · exact inventory_mono hi (fun _ => available_mono (parts_append _ _) (fun _ h => h))
    · intro x hx
      exact List.mem_flatMap.mpr ⟨o, List.mem_append_right _ (List.mem_singleton_self _), hx⟩
  rcases hp.votes σ m hm with h | ⟨w, he, hw⟩ | ⟨a, he, _⟩
  · exact Or.inl h
  · have henc := congrArg Model.Obj.msg he
    simp only [voteObj, Model.Obj.msg] at henc
    have hdec := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj (Model.Msg.data.inj henc))
    simp only [decodeVote_encodeVote, Option.some.injEq] at hdec
    exact Or.inr (hdec ▸ hw)
  · have hbad := congrArg Model.Obj.msg he
    simp only [voteObj, attObj, Model.Obj.msg, Model.Msg.data.injEq] at hbad
    cases hbad

/-- At an actual delivery, the only not-yet-held stored vote is the ordinary outbox head:
the reachable one-vote invariant rules out a later queued vote. -/
theorem delivery_pool_held_or_head (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (σ : Nat) (m : Vote (Fintype.card V))
    (hm : m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool σ) :
    voteObj m ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
        some (.vote (encodeVote m)) := by
  have hv' := hv.honest_only _ (List.mem_of_getElem? he)
  rcases delivery_pool_available S rho hn hv hv' i o σ m hm with hh | hq
  · exact Or.inl hh
  right
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hpre : OneVote t (stateAt S rho hn v i) := by
    rcases (outbox_inv S rho hn hv v hv' i).2 with h | h
    · exact absurd h (not_lastRestart_deliver S rho hv he)
    · rwa [hnow] at h
  have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o)
    (hv.in_horizon _ (List.mem_of_getElem? he)).1
    (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i) hnow hpre
  have hlen := ((atMostOneVote_iff _).mp hproc.atMost).2
  change Body.vote (encodeVote m) ∈
    (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox at hq
  change (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.length ≤ 1 at hlen
  generalize (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox = q at hq hlen ⊢
  cases q with
  | nil => cases hq
  | cons b bs =>
    cases bs with
    | nil => exact congrArg some (List.mem_singleton.mp hq).symm
    | cons c cs => simp at hlen

/-- Any ordinary vote left by delivery processing is signed by the receiving node. -/
theorem delivery_outbox_vote_signer (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (m : Vote (Fintype.card V))
    (hm : Body.vote (encodeVote m) ∈
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox) :
    m.val = rho.ownKey v := by
  have hb : VoteOwned (stateAt S rho hn v i) := by
    intro w hw
    rw [outbox_empty S rho hn hv v hv' i] at hw
    cases hw
  have hs := process_owned (stateAt S rho hn v i) o (Model.digests rho.hash o) hb m hm
  exact hs.trans ((process_self _ _ _).trans (stateAt_self S rho hn v i))

/-- Every envelope queued by an actual delivery has its canonical dependency held or at
the ordinary outbox head. No queue-to-pool or readiness premise is left to the caller. -/
theorem delivery_voteForward_held_or_head (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (tv : Time × Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    voteObj tv.2 ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
        some (.vote (encodeVote tv.2)) :=
  delivery_pool_held_or_head S rho hn hv he tv.2.slot tv.2
    (delivery_voteForward_in_pool S rho hn hv v i o tv htv)

/-- Proposal payloads of actual scheduled honest duties were already released or received.
The proof uses engine-event inventory and the empty queue at the slot-start proposal. -/
theorem scheduled_proposal_releasable (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p : Nat} {t : Time} {s : Slot}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hscheduled : EngineProposalAt S rho v i p t s nd)
    {par : ParentRef} {info : Info} {cs : List (Wire (Fintype.card V))}
    (hprop : (propose (shapeOf S hn nd) s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure nd.seen := by
  obtain ⟨he, hw, hs, hd, hsel, rfl⟩ :=
    (engineProposalAt_iff S rho v i p t s nd).mp hscheduled
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hi := prefix_inventory S rho hn hv hv' i
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
      (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
    (fun q hq => .tick he hw hq) (fun q k hk => Or.inl ⟨t, he, hw, hk⟩)
    (by
      have hi := event_inventory S rho hn hv v hv' i
      rw [stateAt_eq] at hi
      exact hi) p
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1)
  have hout : (shapeOf S hn (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1).outbox = [] := by
    rw [duties_eq S t ht] at hd ⊢
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with ⟨hnone, _⟩ |
      ⟨s', hs', hone, htime⟩
    · simp only [dutiesInit, hnone, List.append_nil] at hd
      change ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat,
        .poll t.toNat, .poll t.toNat] : List (ShapeDuty Empty))[p]? = some (.propose s hs) at hd
      have hm := List.mem_of_getElem? hd
      simp at hm
    · have hp : p = 3 ∧ s = s' := by
        simp only [dutiesInit, hone] at hd
        change ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat,
          .propose s' hs', .poll t.toNat, .poll t.toNat] : List (ShapeDuty Empty))[p]? =
            some (.propose s hs) at hd
        have hlt := (List.getElem?_eq_some_iff.mp hd).1
        simp only [List.length_cons, List.length_nil] at hlt
        interval_cases p <;> simp_all
      obtain ⟨rfl, rfl⟩ := hp
      simp only [dutiesInit, hone]
      change (shapeOf S hn (rho.runDuties v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
          (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
        [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]).1).outbox = []
      rw [← atProposal_eq]
      exact atProposal_outbox_nil S rho hn hv i hv' s
        (htime.trans (slotTime_eq S hn s).symm)
  intro o ho
  rcases proposal_inventory _ hi s hprop o ho with hseen | (⟨w, _, hw⟩ | ⟨a, _, ha⟩)
  · exact hseen
  · rw [hout] at hw
    cases hw
  · rw [hout] at ha
    cases ha

end EngineInventory

end Consensus.Goldilocks.Simulation

end
