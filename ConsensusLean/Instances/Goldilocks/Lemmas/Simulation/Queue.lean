module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.QueuePool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ProvenanceGuard
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteMember
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeInventory
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AttGuard
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Lemmas.Problem.Constant
import ConsensusLean.Lemmas.Model.Credentials
public import Mathlib.Tactic.IntervalCases

public section

/-! # Vote-pool and release-queue inventories

`Pools` proves preservation under node operations; `Inventory` relates queued material to
those pools; `ShapeInventory` lifts the facts to shape handlers; `EngineInventory` follows
duties and deliveries. `scheduled_proposal_releasable` is the proposal-facing endpoint:
the selected proposal's payload objects are already in the engine's seen closure.
`Steps` uses this inventory to relate engine events to node steps.
`QueuePool` keeps the vote-forward envelopes in the pool. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload ACState)

variable {binding : VoteBinding}

section Pools

variable {sp : ACParams} {FGP : Type}

private def PoolIn (P : Vote sp.n → Prop) (A : ACState sp.n) : Prop :=
  ∀ s, ∀ v ∈ A.pool s, P v

private theorem pool_admit {P : Vote sp.n → Prop} {A : ACState sp.n}
    (h : PoolIn P A) (t : Time) (v : Vote sp.n) (hv : P v) :
    PoolIn P (AC.admitVote sp A t v) := by
  intro s w hw
  unfold AC.admitVote at hw
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
    (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (h : PoolIn P A)
    (he : ∀ e ∈ (AC.tryVote sp self A Φ t).2, P e.msg) :
    PoolIn P (AC.tryVote sp self A Φ t).1 := by
  unfold AC.tryVote at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢
  · exact h
  · exact h
  all_goals try exact h
  all_goals
    intro s v hv
    rw [AC.optimistic_pool_eq] at hv
    apply pool_admit (A := _) (P := P) (t := t) (v := _) ?_ ?_ s v hv
    · exact h
    · exact he _ (List.mem_singleton_self _)

private theorem pool_block {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (B : AC.Blk sp.n FGP)
    (h : PoolIn P A)
    (he : ∀ e ∈ (AC.acOnBlock sp self A Φ t B).2, P e.msg) :
    PoolIn P (AC.acOnBlock sp self A Φ t B).1 := by
  apply pool_tryVote self _ Φ t _ he
  intro s v hv
  rw [AC.optimistic_pool_eq] at hv
  exact h s v hv

private theorem pool_message {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (m : Vote sp.n)
    (h : PoolIn P A) (hm : P m)
    (he : ∀ e ∈ (AC.acOnMessage sp self A Φ t m).2, P e.msg) :
    PoolIn P (AC.acOnMessage sp self A Φ t m).1 := by
  apply pool_tryVote self _ Φ t _ he
  intro s v hv
  rw [AC.optimistic_pool_eq] at hv
  exact pool_admit h t m hm s v hv

private theorem pool_tick {P : Vote sp.n → Prop} (self : Fin sp.n)
    (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (h : PoolIn P A)
    (he : ∀ e ∈ (AC.acOnTick sp self A Φ t).2, P e.msg) :
    PoolIn P (AC.acOnTick sp self A Φ t).1 := by
  unfold AC.acOnTick at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢
  all_goals first
    | exact h
    | exact pool_tryVote self A Φ t h he
    | intro s v hv
      rw [AC.updateConfirmation_pool_eq] at hv
      first | exact h s v hv | exact pool_tryVote self A Φ t h he s v hv

/-- Restart replay can only add actual emissions to its cleared pools. -/
theorem restart_pool_inventory (P : Vote sp.n → Prop) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time)
    (he : ∀ e ∈ (AC.acRestart sp ro self A Φ t).2, P e.msg) :
    ∀ s, ∀ v ∈ (AC.acRestart sp ro self A Φ t).1.pool s, P v := by
  classical
  by_cases h : FrameOK Φ ∧ 0 ≤ t
  · rw [AC.acRestart_eq_stamp sp ro self A Φ t h.1 h.2, AC.restartStamp_eq]
    exact fun _ _ hv => False.elim (List.not_mem_nil hv)
  clear h
  unfold AC.acRestart at he ⊢
  generalize ro.order t Φ = l at he ⊢
  have key : ∀ (l : List (AC.Blk sp.n FGP)) (acc : ACState sp.n × List (AC.Em sp FGP)),
      PoolIn P acc.1 →
      (∀ e ∈ (l.foldl (fun acc B => let r := AC.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).2, P e.msg) →
      PoolIn P (l.foldl (fun acc B => let r := AC.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1 := by
    intro l
    induction l with
    | nil => exact fun _ h _ => h
    | cons B l ih =>
      intro acc h he
      have append_mem : ∀ (l : List (AC.Blk sp.n FGP)) acc,
          acc.2 ⊆ (l.foldl (fun acc B => let r := AC.acOnBlock sp self acc.1 Φ t B;
            (r.1, acc.2 ++ r.2)) acc).2 := by
        intro l
        induction l with
        | nil => exact fun _ _ h => h
        | cons B l ih => exact fun acc e he => ih _ (List.mem_append_left _ he)
      apply ih ((AC.acOnBlock sp self acc.1 Φ t B).1,
        acc.2 ++ (AC.acOnBlock sp self acc.1 Φ t B).2)
        (pool_block self _ Φ t B h ?_) he
      intro e he'
      exact he e (append_mem l _ (List.mem_append_right _ he'))
  exact key l _ (fun s v hv => False.elim (List.not_mem_nil hv)) he

/-- **One AC call keeps a vote predicate on the pool**, given it of its message input
(if any) and of its emissions. -/
theorem pool_step_inventory (P : Vote sp.n → Prop) (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (c : (AC.goldilocksAC sp FGP ro).Call)
    (h : ∀ s, ∀ v ∈ A.pool s, P v)
    (hc : match c with
      | .message v => P v
      | _ => True)
    (he : ∀ e ∈ ((AC.goldilocksAC sp FGP ro).step self A Φ t c).2, P e.msg) :
    ∀ s, ∀ v ∈ ((AC.goldilocksAC sp FGP ro).step self A Φ t c).1.pool s, P v := by
  cases c with
  | block B => exact pool_block self A Φ t B h he
  | message v => exact pool_message self A Φ t v h hc he
  | tick => exact pool_tick self A Φ t h he
  | restart => exact restart_pool_inventory P ro self A Φ t he
  | proposal =>
    change PoolIn P (AC.acProposal sp A Φ t).1
    unfold AC.acProposal
    split_ifs <;> exact h
  | toFG =>
    change PoolIn P (AC.acToFG sp A Φ t).1
    unfold AC.acToFG
    split_ifs <;> exact h

end Pools

section Inventory

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Inventory before an engine operation. The predicate will be membership in the seen
closure or in the queue; stored block payloads are needed again by restart replay. Every pool
vote has a signed object with some token; `gate`: the node's vote authentication `io` holds an
own token for every slot its AC may vote in, so own emissions are released. -/
private structure Inventory (io : VoteAuth sp.n binding) (P : Wire sp.n binding → Prop)
    (st : NodeState (goldilocksNode sp ro)) : Prop where
  reachable : st.fg.Reachable ([], [])
  blocks : ∀ B ∈ st.fg.tree, ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o
  votes : PoolIn (fun v => ∃ z, P (voteObj v z)) st.ac
  atts : ∀ a ∈ st.fg.atts, P (attObj a)
  gate : ∀ m : Vote sp.n, st.ac.mayVote m.slot = true → ∃ z, ownToken io m = some z

private theorem inventory_init (io : VoteAuth sp.n binding) (P : Wire sp.n binding → Prop)
    (B : VoteBinding) (q : ShapeRole B.Kind → Bool)
    (hg : ∀ m : Vote sp.n, (Node.initWith (goldilocksNode sp ro)
      (B.installVote q (goldilocksNode sp ro).initial)).ac.mayVote m.slot = true →
        ∃ z, ownToken io m = some z) :
    Inventory io P (Node.initWith (goldilocksNode sp ro)
      (B.installVote q (goldilocksNode sp ro).initial)) := by
  have hpool : (B.installVote q (goldilocksNode sp ro).initial).pool =
      (goldilocksNode sp ro).initial.pool := by
    unfold VoteBinding.installVote
    split <;> rfl
  refine ⟨Relation.ReflTransGen.refl, ?_, ?_, ?_, hg⟩
  · intro B hB o ho
    change (if B.root = sp.genesisRoot then some (sp.toParams.genesisBlock ([], []))
      else none) = some B at hB
    split_ifs at hB
    · cases Option.some.inj hB
      simp [payloadObjs, Params.genesisBlock] at ho
  · intro s v hv
    change v ∈ (B.installVote q (goldilocksNode sp ro).initial).pool s at hv
    rw [hpool] at hv
    exact False.elim (List.not_mem_nil hv)
  · intro a ha
    exact False.elim (List.not_mem_nil ha)

private theorem inventory_att {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
  {st : NodeState (goldilocksNode sp ro)}
    (h : Inventory io P st) (a : FG.Att sp.n) (ha : P (attObj a)) :
    Inventory io P (Node.onAttestation st a).1 := by
  have hfg := NodeAsChainShape.inventory_att (wireCodec sp ro binding io) attObj
    ⟨h.reachable, h.blocks, h.atts⟩ a ha
  exact ⟨hfg.reachable, hfg.blocks, h.votes, hfg.atts, h.gate⟩

/-- Processing a list of attestations, each of which satisfies `P`, keeps the inventory. -/
private theorem inventory_foldl_att {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory io P st) (l : List (FG.Att sp.n))
    (hl : ∀ a ∈ l, P (attObj a)) :
    Inventory io P (l.foldl (fun n a => (Node.onAttestation n a).1) st) := by
  induction l generalizing st with
  | nil => exact h
  | cons a l ih =>
    exact ih (inventory_att h a (hl a List.mem_cons_self))
      fun b hb => hl b (List.mem_cons_of_mem _ hb)

private theorem inventory_accept {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
  {st : NodeState
    (goldilocksNode sp ro)}
    (h : Inventory io P st) {B : Blk sp} {fg' : Store sp.toParams (Payload sp.n)}
    (hacc : st.fg.onBlock B = some fg')
    (hB : ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o) :
    Inventory io P { st with fg := fg' } := by
  have hatt : ∀ a ∈ B.fgPayload,
      attObj a ∈ payloadObjs (binding := binding) B.fgPayload B.acPayload :=
    fun a ha => List.mem_map.mpr ⟨a, ha, rfl⟩
  have hfg := NodeAsChainShape.inventory_accept (wireCodec sp ro binding io) attObj
    ⟨h.reachable, h.blocks, h.atts⟩ hacc hB hatt
  exact ⟨hfg.reachable, hfg.blocks, h.votes, hfg.atts, h.gate⟩

private theorem inventory_call {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
  {st : NodeState
    (goldilocksNode sp ro)}
    (h : Inventory io P st) (self : Fin sp.n) (t : Time)
    (c : (goldilocksNode sp ro).Call)
    (hc : match c with
      | .message v => ∃ z, P (voteObj v z)
      | _ => True)
    (he : ∀ e ∈ ((goldilocksNode sp ro).step self st.ac (frame st) t c).2,
      ∃ z, P (voteObj e.msg z)) : Inventory io P (Node.acCall self st t c).1 := by
  refine ⟨h.reachable, h.blocks, pool_step_inventory _ ro self st.ac (frame st) t c h.votes
    ?_ he, h.atts, fun m hm => h.gate m ?_⟩
  · cases c <;> exact hc
  · change ((goldilocksNode sp ro).step self st.ac (frame st) t c).1.mayVote m.slot = true at hm
    rwa [AC.step_mayVote] at hm

private theorem inventory_mono {io : VoteAuth sp.n binding} {P Q : Wire sp.n binding → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory io P st) (hPQ : ∀ o, P o → Q o) :
    Inventory io Q st :=
  ⟨h.reachable, fun B hB o ho => hPQ o (h.blocks B hB o ho),
    fun s v hv => (h.votes s v hv).imp fun _ => hPQ _, fun a ha => hPQ _ (h.atts a ha), h.gate⟩

private theorem inventory_block {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
  {st : NodeState
    (goldilocksNode sp ro)}
    (h : Inventory io P st) (self : Fin sp.n) (t : Time) (B : Blk sp)
    (hB : ∀ o ∈ payloadObjs B.fgPayload B.acPayload, P o)
    (he : ∀ b ∈ emitted io (Node.onBlock self st t B).2,
      ∀ v z, b = .vote (encodeVote v) z → P (voteObj v z)) :
    Inventory io P (Node.onBlock self st t B).1 := by
  unfold Node.onBlock at he ⊢
  split_ifs at he ⊢
  · exact h
  · split
    · exact h
    · rename_i fg' hfg
      rw [hfg] at he
      apply inventory_call (inventory_accept h hfg hB) self t (.block B) trivial
      intro e he'
      obtain ⟨z, hz⟩ := h.gate e.msg (AC.emits_mayVote ro _ _ _ _ _ e he')
      refine ⟨z, he (.vote (encodeVote e.msg) z) ?_ e.msg z rfl⟩
      simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil]
      exact List.mem_filterMap.mpr ⟨e, he', by rw [hz]; rfl⟩

private theorem inventory_proposal {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory io P st) (t : Time) :
    Inventory io P (Node.acProposal st t).1 := by
  refine ⟨h.reachable, h.blocks, ?_, h.atts, fun m hm => h.gate m ?_⟩
  · change PoolIn _ (AC.acProposal sp st.ac (frame st) t).1
    unfold AC.acProposal
    split_ifs <;> exact h.votes
  · change (AC.acProposal sp st.ac (frame st) t).1.mayVote m.slot = true at hm
    unfold AC.acProposal at hm
    split_ifs at hm <;> exact hm

private theorem inventory_toFG {io : VoteAuth sp.n binding} {P : Wire sp.n binding → Prop}
    {st : NodeState (goldilocksNode sp ro)} (h : Inventory io P st) (t : Time) :
    Inventory io P (Node.acToFG st t).1 := by
  refine ⟨h.reachable, h.blocks, ?_, h.atts, fun m hm => h.gate m ?_⟩
  · change PoolIn _ (AC.acToFG sp st.ac (frame st) t).1
    unfold AC.acToFG
    split_ifs <;> exact h.votes
  · change (AC.acToFG sp st.ac (frame st) t).1.mayVote m.slot = true at hm
    unfold AC.acToFG at hm
    split_ifs at hm <;> exact hm

private theorem proposal_inventory {P : Wire sp.n binding → Prop} (st : State sp ro binding)
    (h : Inventory st.voteIO P st.node) (s : Slot) {par : ParentRef} {info : Info}
    {cs : List (Wire sp.n binding)} (hp : (propose st s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, P o ∧ ∃ a, o = attObj a := by
  simp only [propose_eq, Node.acProposal] at hp
  dsimp only [goldilocksNode, AC.goldilocksAC] at hp
  unfold AC.acProposal at hp
  dsimp only at hp
  split_ifs at hp
  · have hcs := (Option.some.inj hp)
    cases hcs
    intro o ho
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    exact ⟨h.atts a (List.mem_filter.mp ha).1, a, rfl⟩

end Inventory

section ShapeInventory

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Own material not yet released: a vote or attestation queued in the outbox. (A held
attestation is not in the node's pool: it enters the pool when it is released.) -/
private def Pending (st : State sp ro binding) (o : Wire sp.n binding) : Prop :=
  (∃ v z, o = voteObj v z ∧ .vote (encodeVote v) z ∈ st.outbox) ∨
    ∃ a, o = attObj a ∧ .att (encodeAtt a) ∈ st.outbox

private def Available (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (o : Wire sp.n binding) : Prop :=
  o ∈ seen.flatMap Model.Obj.parts ∨ Pending st o

private theorem parts_append {n : Nat} (a b : List (Wire n binding)) :
    a.flatMap Model.Obj.parts ⊆ (a ++ b).flatMap Model.Obj.parts := by
  rw [List.flatMap_append]
  exact List.subset_append_left _ _

private theorem carried_parts {n : Nat} (auth : Model.Auth n (ShapeRole binding.Kind))
    (m : Model.Msg (Header Info) Body) (cs : List (Wire n binding)) {x : Wire n binding}
    (hx : x ∈ cs) : x ∈ (Model.Obj.mk auth m cs).parts := by
  rw [Model.Obj.parts_eq]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨x, hx,
    by rw [Model.Obj.parts_eq]; exact List.mem_cons_self⟩)

private theorem pending_mono {st st' : State sp ro binding} (h : st.outbox ⊆ st'.outbox)
    {o : Wire sp.n binding} : Pending st o → Pending st' o := by
  rintro (⟨v, z, rfl, hv⟩ | ⟨a, rfl, ha⟩)
  · exact Or.inl ⟨v, z, rfl, h hv⟩
  · exact Or.inr ⟨a, rfl, h ha⟩

private theorem available_mono {seen seen' : List (Wire sp.n binding)}
    {st st' : State sp ro binding}
    (hs : seen.flatMap Model.Obj.parts ⊆ seen'.flatMap Model.Obj.parts)
    (hq : st.outbox ⊆ st'.outbox)
    {o : Wire sp.n binding} : Available seen st o → Available seen' st' o :=
  Or.imp (fun h => hs h) (pending_mono hq)

private theorem apply_inventory (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    origin (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (hr : ∀ P : Wire sp.n binding → Prop, Inventory st.voteIO P st.node →
      (∀ o ∈ seen.flatMap Model.Obj.parts, P o) →
      (∀ b ∈ emitted st.voteIO r.2, ∀ v z, b = .vote (encodeVote v) z → P (voteObj v z)) →
      Inventory st.voteIO P r.1)
    (h : Inventory st.voteIO (Available seen st) st.node) :
    Inventory st.voteIO (Available seen (apply st origin r)) (apply st origin r).node := by
  apply hr
  · exact inventory_mono h (fun _ => available_mono (st := st) (st' := apply st origin r)
      (fun _ h => h) (List.subset_append_left _ _))
  · exact fun _ h => Or.inl h
  · intro b hb v z hv
    exact Or.inr (Or.inl ⟨v, z, rfl, List.mem_append_right _ (hv ▸ hb)⟩)

private theorem tick_inventory (seen : List (Wire sp.n binding)) {sign : Fin sp.n → Time → Bool}
    (st : State sp ro binding)
    (h : Inventory st.voteIO (Available seen st) st.node) :
    Inventory (nodeTick st sign).voteIO (Available seen (nodeTick st sign))
      (nodeTick st sign).node := by
  rw [nodeTick_eq (sign := _)]
  split
  · apply apply_inventory seen st none
      ((Node.acCall st.self st.node st.now .tick).1,
        [(Node.acCall st.self st.node st.now .tick).2]) ?_ h
    intro P h _ he
    apply inventory_call h st.self st.now .tick trivial
    intro e he'
    obtain ⟨z, hz⟩ := h.gate e.msg (AC.emits_mayVote ro _ _ _ _ _ e he')
    refine ⟨z, he (.vote (encodeVote e.msg) z) ?_ e.msg z rfl⟩
    simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.mem_filterMap.mpr ⟨e, he', by rw [hz]; rfl⟩
  · exact h

private theorem restore_inventory (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (k : Fin sp.n) (t : Time) (h : Inventory st.voteIO (Available seen st) st.node) :
    Inventory (restore k st t).voteIO (Available seen (restore k st t)) (restore k st t).node := by
  apply apply_inventory seen { st with self := k, now := t } none
    ((Node.acCall k st.node t .restart).1, [(Node.acCall k st.node t .restart).2]) ?_ h
  intro P h _ he
  apply inventory_call h k t .restart trivial
  intro e he'
  obtain ⟨z, hz⟩ := h.gate e.msg (AC.emits_mayVote ro _ _ _ _ _ e he')
  refine ⟨z, he (.vote (encodeVote e.msg) z) ?_ e.msg z rfl⟩
  simp only [emitted, acCall, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_filterMap.mpr ⟨e, he', by rw [hz]; rfl⟩

/-- The FG update keeps the inventory: its attestation is queued in the outbox when the schedule
releases at the node's time, and held otherwise. -/
private theorem fg_inventory (release : Fin sp.n → Time → Bool) (seen : List (Wire sp.n binding))
    (st : State sp ro binding) (h : Inventory st.voteIO (Available seen st) st.node) :
    Inventory (fgUpdate st release).voteIO (Available seen (fgUpdate st release))
      (fgUpdate st release).node := by
  rw [fgUpdate_eq st release]
  dsimp only
  split
  · exact inventory_toFG h st.now
  · split
    · exact inventory_toFG h st.now
    · rename_i C hC a Λ' ha
      have ht := inventory_toFG h st.now
      have ht' : Inventory st.voteIO (Available seen st)
          { (Node.acToFG st.node st.now).1 with record := Λ' } :=
        ⟨ht.reachable, ht.blocks, ht.votes, ht.atts, ht.gate⟩
      split
      · apply inventory_att
        · refine inventory_mono ht' fun o ho => ?_
          rcases ho with ho | ⟨v, z, rfl, hv⟩ | ⟨b, rfl, hb⟩
          · exact Or.inl ho
          · exact Or.inr (Or.inl ⟨v, z, rfl, List.mem_append_left _ hv⟩)
          · exact Or.inr (Or.inr ⟨b, rfl, List.mem_append_left _ hb⟩)
        · exact Or.inr (Or.inr ⟨a, rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩)
      · exact inventory_mono ht' fun o ho => ho

private theorem processOne_inventory (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat)) (o : Wire sp.n binding)
    (h : Inventory st.voteIO (Available seen st) st.node)
    (ho : ∀ x ∈ o.parts, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (processOne io hs st o).voteIO (Available seen (processOne io hs st o))
      (processOne io hs st o).node := by
  rw [processOne_voteIO, AsChainShape.processOne_eq]
  split
  · rename_i B hB
    have hcanon : o = blockObj sp B := by
      rcases canonEvent_eq_some hB with ⟨B', he, ho⟩ | ⟨v, z, he, _⟩ | ⟨a, he, _⟩
      · cases he; exact ho
      · cases he
      · cases he
    unfold relayIf
    dsimp only
    split_ifs <;>
      apply apply_inventory seen st none (Node.onBlock st.self st.node st.now B) ?_ h
    all_goals
      intro P h hseen he
      apply inventory_block h st.self st.now B ?_ he
      intro x hx
      apply hseen x (ho x ?_)
      rw [hcanon, Model.Obj.parts_eq]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨x, hx, by rw [Model.Obj.parts_eq]; exact List.mem_cons_self⟩)
  · rename_i v hv
    obtain ⟨z₀, hcanon⟩ : ∃ z, o = voteObj v z := by
      rcases canonEvent_eq_some hv with ⟨B, he, _⟩ | ⟨v', z, he, ho, -⟩ | ⟨a, he, _⟩
      · cases he
      · cases he; exact ⟨z, ho⟩
      · cases he
    apply apply_inventory seen st (some o) (Node.onMessage st.self st.node st.now v) ?_ h
    all_goals
      intro P h hseen he
      apply inventory_call h st.self st.now (.message v) ?_ ?_
      · refine ⟨z₀, hseen _ ?_⟩
        rw [← hcanon]
        apply ho
        rw [Model.Obj.parts_eq]
        exact List.mem_cons_self
      · intro e he'
        obtain ⟨z, hz⟩ := h.gate e.msg (AC.emits_mayVote ro _ _ _ _ _ e he')
        refine ⟨z, he (.vote (encodeVote e.msg) z) ?_ e.msg z rfl⟩
        simp only [Node.onMessage, emitted, acCall, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_filterMap.mpr ⟨e, he', by rw [hz]; rfl⟩
  · rename_i a ha
    have hcanon : o = attObj a := by
      rcases canonEvent_eq_some ha with ⟨B, he, _⟩ | ⟨v, z, he, _⟩ | ⟨a', he, ho⟩
      · cases he
      · cases he
      · cases he; exact ho
    apply apply_inventory seen st none (Node.onAttestation st.node a) ?_ h
    intro P h hseen _
    apply inventory_att h
    apply hseen _
    rw [← hcanon]
    apply ho
    rw [Model.Obj.parts_eq]
    exact List.mem_cons_self
  · exact h

private theorem process_inventory (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (hs : List (Header Info × Nat)) (o : Wire sp.n binding)
    (h : Inventory st.voteIO (Available seen st) st.node)
    (ho : ∀ x ∈ o.parts, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (process st o hs).voteIO (Available seen (process st o hs))
      (process st o hs).node := by
  rw [process_eq]
  have key : ∀ (io : VoteAuth sp.n binding) (l : List (Wire sp.n binding))
      (st : State sp ro binding),
      Inventory st.voteIO (Available seen st) st.node →
      (∀ x ∈ l, ∀ y ∈ x.parts, y ∈ seen.flatMap Model.Obj.parts) →
      Inventory (l.foldl (processOne io hs) st).voteIO
        (Available seen (l.foldl (processOne io hs) st))
        (l.foldl (processOne io hs) st).node := by
    intro io l
    induction l with
    | nil => exact fun _ h _ => h
    | cons x l ih =>
      intro st h hl
      exact ih _ (processOne_inventory seen st io hs x h (hl x List.mem_cons_self))
        (fun y hy => hl y (List.mem_cons_of_mem x hy))
  apply key _ _ st h
  intro x hx y hy
  exact ho y (Model.Obj.Contains.trans (mem_delivered st.voteIO hs hx) hy)

private theorem record_inventory (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (hs : List (Header Info × Nat)) (o : Wire sp.n binding)
    (h : Inventory st.voteIO (Available seen st) st.node)
    (hp : ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
      ∀ atts p, decodeInfo sp.n hd.info = some (atts, p) →
      ∀ x ∈ payloadObjs atts p, x ∈ seen.flatMap Model.Obj.parts) :
    Inventory (recordOwn st o hs).voteIO (Available seen (recordOwn st o hs))
      (recordOwn st o hs).node := by
  rw [AsChainShape.recordOwn_eq]
  split
  · exact h
  · rename_i k s hd cs
    split
    · rename_i atts p d hi hdig
      apply apply_inventory seen st none _ ?_ h
      intro P h hseen he
      apply inventory_block h st.self st.now _ ?_ he
      intro x hx
      apply hseen x
      exact hp _ _ _ _ rfl _ _ hi x hx
    · exact h
  · exact h

private theorem poll_inventory_core (release : Fin sp.n → Time → Bool)
    (seen : List (Wire sp.n binding)) (st : State sp ro binding)
    (t : Time) (h : Inventory st.voteIO (Available seen st) st.node)
    (hv : ∀ v z, (pollPre st release).outbox.head? =
      some (.vote (encodeVote v) z) → voteObj v z ∈ seen.flatMap Model.Obj.parts)
    (ha : ∀ a, (pollPre st release).outbox.head? =
      some (.att (encodeAtt a)) → attObj a ∈ seen.flatMap Model.Obj.parts) :
    Inventory (poll st t release).1.voteIO (Available seen (poll st t release).1)
      (poll st t release).1.node := by
  have hi : Inventory (pollPre st release).voteIO (Available seen (pollPre st release))
      (pollPre st release).node := by
    rw [pollPre_eq]
    split
    · exact fg_inventory release seen st h
    · exact h
  rw [pollPre_eq] at hi hv ha
  generalize he : (if st.fgDue then fgUpdate st release else st) = pre at hi hv ha
  unfold poll
  rw [he]
  cases hq : pre.outbox with
  | nil =>
    simp only [hq]
    apply inventory_mono hi
    intro o ho
    rcases ho with ho | ⟨v, z, rfl, hv'⟩ | ⟨a, rfl, ha'⟩
    · exact Or.inl ho
    · rw [hq] at hv'; cases hv'
    · rw [hq] at ha'; cases ha'
  | cons b rest =>
    simp only [hq]
    apply inventory_mono hi
    intro o ho
    rcases ho with ho | (⟨v, z, rfl, hv'⟩ | ⟨a, rfl, ha'⟩)
    · exact Or.inl ho
    · rw [hq] at hv'
      rcases List.mem_cons.mp hv' with hb | hr
      · exact Or.inl (hv v z (by simp [hq, ← hb]))
      · exact Or.inr (Or.inl ⟨v, z, rfl, hr⟩)
    · rw [hq] at ha'
      rcases List.mem_cons.mp ha' with hb | hr
      · exact Or.inl (ha a (by simp [hq, ← hb]))
      · exact Or.inr (Or.inr ⟨a, rfl, hr⟩)

/-- A batch poll keeps the inventory, given that its ordinary emission and the held
attestations it flushes are in the new `seen` log. -/
private theorem poll_inventory (release : Fin sp.n → Time → Bool)
    (seen seen' : List (Wire sp.n binding)) (st : State sp ro binding)
    (t : Time) (h : Inventory st.voteIO (Available seen st) st.node)
    (hs : seen.flatMap Model.Obj.parts ⊆ seen'.flatMap Model.Obj.parts)
    (hv : ∀ v z, (pollPre st release).outbox.head? =
      some (.vote (encodeVote v) z) → voteObj v z ∈ seen'.flatMap Model.Obj.parts)
    (ha : ∀ a, (pollPre st release).outbox.head? =
      some (.att (encodeAtt a)) → attObj a ∈ seen'.flatMap Model.Obj.parts)
    (hf : ∀ a ∈ pollFlush st release, attObj a ∈ seen'.flatMap Model.Obj.parts) :
    Inventory (pollBatch st t release).1.voteIO (Available seen' (pollBatch st t release).1)
      (pollBatch st t release).1.node := by
  have hcore : ∀ st₀ : State sp ro binding,
      (pollPre st₀ release).outbox = (pollPre st release).outbox →
      Inventory st₀.voteIO (Available seen' st₀) st₀.node →
      Inventory (poll st₀ t release).1.voteIO (Available seen' (poll st₀ t release).1)
        (poll st₀ t release).1.node := fun st₀ ho h₀ =>
    poll_inventory_core release seen' st₀ t h₀ (ho ▸ hv) (ho ▸ ha)
  have h' : Inventory st.voteIO (Available seen' st) st.node :=
    inventory_mono h fun _ => available_mono hs (fun _ h => h)
  rw [pollBatch_fst]
  split
  · rename_i hr
    refine hcore _ (by rw [pollPre_heldDrain_outbox]) ?_
    have hio : (heldDrain st).voteIO = st.voteIO := by
      obtain ⟨atts, he⟩ := heldDrain_eq st; rw [he]
    rw [heldDrain_node, hio]
    have hfl : ∀ a ∈ st.held, attObj a ∈ seen'.flatMap Model.Obj.parts := fun a ha' =>
      hf a (by rw [pollFlush_eq, ite_eq_left hr]; exact ha')
    have hmono : Inventory st.voteIO (Available seen' (heldDrain st)) st.node :=
      inventory_mono h' fun o ho => by
        rcases ho with ho | ⟨v, z, rfl, hv'⟩ | ⟨b, rfl, hb⟩
        · exact Or.inl ho
        · exact Or.inr (Or.inl ⟨v, z, rfl, by rw [heldDrain_outbox]; exact hv'⟩)
        · exact Or.inr (Or.inr ⟨b, rfl, by rw [heldDrain_outbox]; exact hb⟩)
    exact inventory_foldl_att hmono st.held fun a ha' => Or.inl (hfl a ha')
  · exact hcore _ rfl h'

end ShapeInventory

section EngineInventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem cut_member (hv : rho.ExecutionValid) {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) :
    VoteMember (fun s => decide (rho.ownKey v ∈ rho.sel (S.vote.voteRole s)))
      (shapeOf S hn nd) := by
  have hbase := stateAt_voteMember S rho hn hv v i
  rw [stateAt_eq] at hbase
  cases hc with
  | tick he hw hp =>
    have hb := (VoteMember_iff _).1 hbase
    exact runDuties_voteMember S rho hn v _ _ ((VoteMember_iff _).2 hb)
  | deliver he hp => exact runDuties_voteMember S rho hn v _ _ (process_voteMember _ _ _ hbase)

/-- Pending canonical votes at actual duty boundaries are own votes of a slot whose vote role
selects the local signer. -/
theorem duty_cut_vote_member (hv : rho.ExecutionValid) {v : V} (_hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd} (hc : EngineDutyCut S rho v i p nd) (m : Vote (Fintype.card V)) {z : Nat}
    (hm : Body.vote (encodeVote m) z ∈ (shapeOf S hn nd).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  have h := ((VoteMember_iff _).1 (cut_member S rho hn hv hc)).2 m z hm
  ⟨h.1.trans (cut_self S rho hn hc), of_decide_eq_true h.2⟩

omit [DecidableEq V] in
/-- A candidate that carries nothing and whose dependencies are always ready is released. -/
private theorem mem_releaseAll_free {pub : Model.Public} {Out : Type} {P : Model.Protocol pub Out}
    (hash : P.Item → Nat) (k : Model.Key pub) :
    ∀ (nd : Model.Node P) (cs : List P.Object) {c : P.Object}, c ∈ cs → c.carried = [] →
      (∀ held, P.dependencies.ready held c = true) → c ∈ (Model.releaseAll P hash k nd cs).2
  | _, [], _, hc, _, _ => absurd hc List.not_mem_nil
  | nd, d :: cs, c, hc, hcar, hready => by
    unfold Model.releaseAll
    split
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_releaseAll_free hash k _ cs hc hcar hready)
    · rename_i hf
      rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd (by simp [Model.releasable, hcar, hready]) hf
      · exact mem_releaseAll_free hash k nd cs hc hcar hready

private theorem poll_duty_inventory (hv : rho.ExecutionValid)
    {v : V} {i p : Nat} {nd} {k : Nat}
    (hc : EngineDutyCut S rho v i p nd)
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (h : Inventory (shapeOf S hn nd).voteIO (Available nd.seen (shapeOf S hn nd))
      (shapeOf S hn nd).node) :
    Inventory (shapeOf S hn (rho.dutyStep v nd (.poll k)).1).voteIO (Available
      (rho.dutyStep v nd (.poll k)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.poll k)).1))
      (shapeOf S hn (rho.dutyStep v nd (.poll k)).1).node := by
  have hsel := poll_selected S rho hv v
  rw [dutyStep_poll S rho hn v nd k hsel]
  have hmem : ∀ b, (pollPre (shapeOf S hn nd) (S.release (pubOf E))).outbox.head? = some b →
      rho.ownKey v ∈ rho.sel (pollRole S.vote (pubOf E).n b) →
      pollObj S rho v b ∈ (rho.dutyStep v nd (.poll k)).1.seen.flatMap Model.Obj.parts := by
    intro b hb hk
    apply Model.mem_closure_of_mem
    rw [Simulation.dutyStep_seen S rho v nd (.poll k)]
    exact List.mem_append_right _ (dutyStep_poll_rel S rho hn v nd k hsel hb hk)
  apply poll_inventory _ nd.seen _ _ _ h
  · rw [Simulation.dutyStep_seen S rho v nd (.poll k)]
    exact parts_append _ _
  · intro w z hw
    have hown : VoteMember (fun s => decide (rho.ownKey v ∈ rho.sel (S.vote.voteRole s)))
        (pollPre (shapeOf S hn nd) (S.release (pubOf E))) := by
      rw [pollPre_eq]
      split
      · exact fgUpdate_voteMember _ (cut_member S rho hn hv hc)
      · exact cut_member S rho hn hv hc
    have hw' := ((VoteMember_iff _).1 hown).2 w z
      (List.mem_of_mem_head? (Option.mem_def.mpr hw))
    have hval := hw'.1.trans
      ((by rw [pollPre_eq]; split <;> simp [fgUpdate_self] :
        (pollPre (shapeOf S hn nd) (S.release (pubOf E))).self =
          (shapeOf S hn nd).self).trans (cut_self S rho hn hc))
    rw [voteObj_eq_pollObj S rho z hval]
    exact hmem _ hw (by rw [pollRole_vote]; exact of_decide_eq_true hw'.2)
  · intro a ha
    have hpoll : (poll (nd.st.1 hn) k (S.release (pubOf E))).2 =
        some (.att (encodeAtt a), []) := by
      rw [(poll_outbox _ _).2, ha]
      rfl
    obtain ⟨a', j, q, he, hval, -⟩ := engine_poll_att_signed S rho hn hc hd hsel hpoll
    have he' := congrArg (decodeAtt (Fintype.card V)) he
    simp only [decodeAtt_encodeAtt, Option.some.injEq] at he'
    subst a'
    have hav := hval.trans (cut_self S rho hn hc)
    rw [attObj_eq_pollObj_of_val S rho hav]
    exact hmem _ ha (pollRole_selected_of_not_vote S rho hsel (fun w z h => by cases h))
  · -- a held attestation the batch flushes is released by it
    intro a ha
    have hah : a ∈ (shapeOf S hn nd).held := by
      rw [pollFlush_eq] at ha
      split at ha
      · exact ha
      · cases ha
    have hav := (engine_held_att_signed S rho hn hc hah).1.trans (cut_self S rho hn hc)
    rw [attObj_eq_pollObj_of_val S rho hav]
    apply Model.mem_closure_of_mem
    rw [Simulation.dutyStep_seen S rho v nd (.poll k)]
    refine List.mem_append_right _ ?_
    unfold Model.Run.dutyStep
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k) = .poll from rfl,
      hsel, ↓reduceIte]
    rw [signedCandidate_poll S rho hn v nd k hsel]
    refine mem_releaseAll_free _ _ _ _ (List.mem_append_right _
      (List.mem_map.mpr ⟨a, ha, ?_⟩)) rfl fun held => pollObj_ready S rho v held _
    rw [← attObj_eq_pollObj_of_val S rho hav]
    unfold attObj
    rw [hav]
    rfl

private def PayloadCarried (o : Wire (Fintype.card V) binding) : Prop :=
  ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
    ∀ atts p, decodeInfo (Fintype.card V) hd.info = some (atts, p) →
      ∀ x ∈ payloadObjs atts p, x ∈ o.parts

omit [DecidableEq V] in
private theorem release_inventory (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs)
    (h : Inventory (shapeOf S hn nd).voteIO (Available nd.seen (shapeOf S hn nd))
      (shapeOf S hn nd).node)
    (hp : ∀ o ∈ cs, PayloadCarried o) :
    Inventory (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1).voteIO (Available (Model.releaseAll (Model.protoOf
          (compiled (goldilocks S)) E)
        rho.hash k nd cs).1.seen
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1))
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash k nd cs).1).node := by
  refine NodeAsChainShape.CanonicalTrace.release_inventory rho k nd cs
    (Inv := fun n => Inventory (shapeOf S hn n).voteIO (Available n.seen (shapeOf S hn n))
      (shapeOf S hn n).node)
    (Admissible := PayloadCarried) ?_ h hp
  intro n c hi hc
  apply record_inventory (n.seen ++ [c]) (shapeOf S hn n) _ c
  · exact inventory_mono hi (fun _ =>
      available_mono (parts_append _ _) (fun _ h => h))
  · intro key s hd os he atts p hi x hx
    exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (List.mem_singleton_self _),
      hc key s hd os he atts p hi x hx⟩

omit [DecidableEq V] in
include hn in
private theorem proposal_carried (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s) :
    ∀ o ∈ rho.signedCandidate v (.propose s hs)
      ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2,
      PayloadCarried o := by
  intro o ho
  obtain ⟨m, cs, hm, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_propose_snd S hn] at hm
  obtain ⟨⟨par, info, os⟩, hp, he⟩ := Option.mem_toList.mp hm |> Option.mem_map.mp
  cases he
  intro key slot hd cs he atts p hi x hx
  injection he with _ hmsg hcs
  injection hmsg with hhd
  subst hhd hcs
  rw [propose_eq] at hp
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
    (h : Inventory (shapeOf S hn nd).voteIO (Available nd.seen (shapeOf S hn nd))
      (shapeOf S hn nd).node) :
    Inventory (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).voteIO (Available
      (rho.dutyStep v nd (.propose s hs)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1))
      (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).node := by
  unfold Model.Run.dutyStep
  split
  · apply release_inventory
    · have hact := shapeOf_act_propose S hn nd.st s hs
      change Inventory
        (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn).voteIO
        (Available nd.seen
        (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn))
        (((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn).node
      rw [hact]
      have hi := inventory_proposal h (shapeOf S hn nd).now
      rw [propose_eq]
      dsimp only
      split <;> exact hi
    · exact proposal_carried S rho hn v nd s hs
  · exact h

omit [DecidableEq V] in
private theorem tick_duty_inventory (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (k : Nat)
    (h : Inventory (shapeOf S hn nd).voteIO (Available nd.seen (shapeOf S hn nd))
      (shapeOf S hn nd).node) :
    Inventory (shapeOf S hn (rho.dutyStep v nd (.pollPropose k)).1).voteIO (Available
      (rho.dutyStep v nd (.pollPropose k)).1.seen
      (shapeOf S hn (rho.dutyStep v nd (.pollPropose k)).1))
      (shapeOf S hn (rho.dutyStep v nd (.pollPropose k)).1).node := by
  rw [Simulation.dutyStep_seen S rho v nd (.pollPropose k), dutyStep_pollPropose_snd S rho hn,
    List.append_nil]
  by_cases hsel : rho.ownKey v ∈ rho.sel .poll
  · rw [dutyStep_pollPropose S rho hn v nd k hsel]
    exact tick_inventory _ _ h
  · unfold Model.Run.dutyStep
    simp only
        [show (Model.protoOf (compiled (goldilocks S)) E).role (.pollPropose k)
            = .poll from rfl,
      hsel, ↓reduceIte]
    exact h

private theorem prefix_inventory (hv : rho.ExecutionValid)
    {v : V} (i : Nat)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (hcut : ∀ p, p ≤ ds.length → EngineDutyCut S rho v i p
      (rho.runDuties v nd (ds.take p)).1)
    (hsched : ∀ (p k : Nat), ds[p]? = some (ShapeDuty.poll k) →
      (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some (.poll k))
    (h : Inventory (shapeOf S hn nd).voteIO (Available nd.seen (shapeOf S hn nd))
      (shapeOf S hn nd).node) :
    ∀ p, p ≤ ds.length →
      let out := (rho.runDuties v nd (ds.take p)).1
      Inventory (shapeOf S hn out).voteIO (Available out.seen (shapeOf S hn out))
        (shapeOf S hn out).node := by
  refine NodeAsChainShape.CanonicalTrace.prefix_inventory rho nd ds (EngineDutyCut S rho v i)
    (Inv := fun n => Inventory (shapeOf S hn n).voteIO (Available n.seen (shapeOf S hn n))
      (shapeOf S hn n).node)
    hcut ?_ h
  intro j n d hcut hd hi
  cases d with
  | act s k => rw [dutyStep_act S rho v _ s k]; exact hi
  | propose s hs => exact proposal_duty_inventory S rho hn v _ s hs hi
  | pollPropose k => exact tick_duty_inventory S rho hn v _ k hi
  | poll k => exact poll_duty_inventory S rho hn hv hcut (hsched j k hd) hi

private theorem event_inventory (hv : rho.ExecutionValid)
    (v : V) :
    ∀ i, Inventory (stateAt S rho hn v i).voteIO (Available (rho.stateBefore i v).seen
      (stateAt S rho hn v i))
      (stateAt S rho hn v i).node := by
  simp only [stateAt_eq]
  refine NodeAsChainShape.CanonicalTrace.event_inventory rho v hv
    (Inv := fun n => Inventory (shapeOf S hn n).voteIO (Available n.seen (shapeOf S hn n))
      (shapeOf S hn n).node)
    (Admissible := PayloadCarried) (inventory_init _ _ _ _ ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have hmv := stateAt_mayVote S rho hn hv v 0
    rw [stateAt_eq] at hmv
    have hm' : (shapeOf S hn (rho.stateBefore 0 v)).node.ac.mayVote m.slot = true := hm
    rw [hmv] at hm'
    exact ⟨_, rho.voteIO_own_isSome (of_decide_eq_true hm') _⟩
  · intro nd t _ hi
    rw [NodeAsChainShape.CanonicalTrace.afterClock_eq]
    exact hi
  · intro nd o hi
    apply process_inventory
    · exact inventory_mono hi (fun _ =>
        available_mono (parts_append _ _) (fun _ h => h))
    · intro x hx
      exact List.mem_flatMap.mpr ⟨o, List.mem_append_right _ (List.mem_singleton_self _), hx⟩
  · intro nd t _ hi
    exact restore_inventory _ _ _ _ hi
  · intro nd c hi hc
    apply record_inventory (nd.seen ++ [c]) (shapeOf S hn nd) _ c
    · exact inventory_mono hi (fun _ =>
        available_mono (parts_append _ _) (fun _ h => h))
    · intro key s hd os he atts p hi x hx
      exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (List.mem_singleton_self _),
        hc key s hd os he atts p hi x hx⟩
  · intro nd t o ho
    obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
    intro key s hd cs he
    cases he
  · intro i j nd ds d hp hd hi
    cases d with
    | act s k => rw [dutyStep_act S rho v _ s k]; exact hi
    | propose s hs => exact proposal_duty_inventory S rho hn v _ s hs hi
    | pollPropose k => exact tick_duty_inventory S rho hn v _ k hi
    | poll k =>
      cases hp with
      | tick he hw =>
        rw [NodeAsChainShape.CanonicalTrace.afterClock_eq] at hi ⊢
        exact poll_duty_inventory S rho hn hv (.tick he hw (List.getElem?_eq_some_iff.mp hd).1.le)
          (Or.inl ⟨_, he, hw, hd⟩) hi
      | deliver he =>
        exact poll_duty_inventory S rho hn hv (.deliver he (List.getElem?_eq_some_iff.mp hd).1.le)
          (Or.inr ⟨_, _, he, hd⟩) hi

/-- A vote allowed by the engine state's gate has a token from its installed issuer. -/
theorem stateAt_ownToken_exists (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (m : Vote (Fintype.card V))
    (hm : (stateAt S rho hn v i).node.ac.mayVote m.slot = true) :
    ∃ z, ownToken (stateAt S rho hn v i).voteIO m = some z :=
  (event_inventory S rho hn hv v i).gate m hm

/-- Proposal payloads of actual scheduled honest duties were already released or received.
The proof uses engine-event inventory and the empty queue at the slot-start proposal. -/
theorem scheduled_proposal_releasable (hv : rho.ExecutionValid)
    {v : V} {i p : Nat} {t : Time} {s : Slot}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hscheduled : EngineProposalAt S rho v i p t s nd)
    {par : ParentRef} {info : Info} {cs : List (Wire (Fintype.card V) S.vote)}
    (hprop : (propose (shapeOf S hn nd) s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure nd.seen := by
  obtain ⟨he, hw, hs, hd, hsel, rfl⟩ :=
    (engineProposalAt_iff S rho v i p t s nd).mp hscheduled
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hi := prefix_inventory S rho hn hv i
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
      (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ _
    (fun q hq => .tick he hw hq) (fun q k hk => Or.inl ⟨t, he, hw, hk⟩)
    (by
      have hi := event_inventory S rho hn hv v i
      rw [stateAt_eq] at hi
      exact hi) p
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hd).1)
  have hout : (shapeOf S hn (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1).outbox = [] := by
    rw [duties_eq S t ht] at hd ⊢
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnone, _⟩ |
      ⟨s', hs', hone, htime⟩
    · simp only [dutiesInit, hnone, List.append_nil] at hd
      change ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat,
        .poll t.toNat, .poll t.toNat] : List (ShapeDuty S.vote.Kind))[p]? = some
            (.propose s hs) at hd
      have hm := List.mem_of_getElem? hd
      simp at hm
    · have hp : p = 3 ∧ s = s' := by
        simp only [dutiesInit, hone] at hd
        change ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat,
          .propose s' hs', .poll t.toNat, .poll t.toNat] : List (ShapeDuty S.vote.Kind))[p]? =
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
      exact atProposal_outbox_nil S rho hn hv i s
        (htime.trans (slotTime_eq S hn s).symm)
  intro o ho
  obtain ⟨hav, a, rfl⟩ := proposal_inventory _ hi s hprop o ho
  rcases hav with hseen | ⟨w, z, _, hw⟩ | ⟨b, _, hb⟩
  · exact hseen
  · rw [hout] at hw
    cases hw
  · rw [hout] at hb
    cases hb

end EngineInventory

end Consensus.Goldilocks.Simulation

end
