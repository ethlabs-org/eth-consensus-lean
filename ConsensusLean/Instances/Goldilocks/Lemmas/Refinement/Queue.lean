module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame

public section

namespace Consensus.Goldilocks.Refinement

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

private theorem pool_optimistic (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem pool_confirmation (A : SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) (s : Nat) : (SA.updateConfirmation sp A Φ t s).pool = A.pool := by
  unfold SA.updateConfirmation SA.updateLatestConfirmed
  dsimp only
  split
  · rfl
  · split_ifs <;> rfl

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
    rw [pool_optimistic] at hv
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
  rw [pool_optimistic] at hv
  exact pool_receipt A t B h hB s v hv

private theorem pool_message {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (m : Vote sp.n)
    (h : PoolIn P A) (hm : P m)
    (he : ∀ e ∈ (SA.acOnMessage sp self A Φ t m).2, P e.msg) :
    PoolIn P (SA.acOnMessage sp self A Φ t m).1 := by
  apply pool_tryVote self _ Φ t _ he
  intro s v hv
  rw [pool_optimistic] at hv
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
      rw [pool_confirmation] at hv
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
    dsimp only
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
  dsimp only
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
    unfold relayIf
    dsimp only
    split_ifs <;>
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

end Consensus.Goldilocks.Refinement

end
