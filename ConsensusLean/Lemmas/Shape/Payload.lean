module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Lemmas.Model.Laws
public import ConsensusLean.Lemmas.Model.Mempool
public import ConsensusLean.Lemmas.Model.Causal
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Lemmas.Model.Adequate
public import ConsensusLean.Lemmas.Blocks.Facts

public section

/-! # Shape-level payload facts (L2)

Signed objects come only from duties, and the only item-producing duties are
the slot and poll proposals, whose `input` `compile` writes from the
post-clock mempool. Gossip may emit unsigned items with any `input`, so the
payload facts are about *signed* item candidates only. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf Obj Msg Public)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

section Compile

variable {pub : Public} {Out : Type}

/-- `compile`'s duties keep the mempool. -/
theorem compile_act_mempool (S : ChainShape pub Out Info) (st : (compile S).State)
    (d : (compile S).Duty) : ((compile S).act st d).1.2 = st.2 := by
  cases d <;> rfl

/-- Every state a tick of a compiled shape reaches has the post-clock mempool. -/
theorem tickReach_mempool {S : ChainShape pub Out Info} {ds : List (compile S).Duty}
    {st₁ st : (compile S).State} (h : Model.TickReach (compile S) ds st₁ st) : st.2 = st₁.2 :=
  Model.TickReach.invariant (fun s : (compile S).State => s.2 = st₁.2) rfl
    (fun s d _ hs => (compile_act_mempool S s d).trans hs) (fun _ _ _ hs => hs) h

/-- A duty's item is a proposal whose payload is the encoded mempool of the
state it acts from. -/
theorem act_item_payload (S : ChainShape pub Out Info) (st : (compile S).State)
    (d : (compile S).Duty) {h : Header Info} {cs}
    (hact : ((compile S).act st d).2 = some (.item h, cs)) : h.input = encodeTxs st.2 := by
  cases d with
  | propose s _ =>
    cases hp : (S.propose st.1 s).2 with
    | none => simp [compile, withMempool, hp] at hact
    | some x =>
      obtain ⟨par, info, cs'⟩ := x
      simp only [compile, withMempool, hp, Option.map_some, Option.some.injEq] at hact
      injection hact with hm
      injection hm with hm
      rw [← hm]
  | act s k =>
    cases hp : (S.act st.1 s k).2 with
    | none => simp [compile, withMempool, hp] at hact
    | some x =>
      simp only [compile, withMempool, hp, Option.map_some, Option.some.injEq] at hact
      injection hact with hm
      cases hm
  | pollPropose u =>
    cases hp : (S.pollPropose st.1 (u : Time)).2 with
    | none => simp [compile, withMempool, hp] at hact
    | some x =>
      obtain ⟨par, pos, info, cs'⟩ := x
      simp only [compile, withMempool, hp, Option.map_some, Option.some.injEq] at hact
      injection hact with hm
      injection hm with hm
      rw [← hm]
  | poll u =>
    cases hp : (S.poll st.1 (u : Time)).2 with
    | none => simp [compile, withMempool, hp] at hact
    | some x =>
      simp only [compile, withMempool, hp, Option.map_some, Option.some.injEq] at hact
      injection hact with hm
      cases hm

end Compile

/-- In a valid run, a node's state at a delivery at `τ` holds its mempool at
`τ`: the node is awake at `τ`, so it ticked at `τ`, before the delivery (ticks
come before deliveries within a time), and the events of the node in between
are deliveries at `τ`, which keep the mempool. -/
theorem deliver_state_mempool {rho : Model.Run (compiled F) E} (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {p : (protoOf (compiled F) E).Object} {τ : Time}
    (he : rho.events[i]? = some (.deliver v p τ)) :
    (rho.stateBefore i v).st.2 = Model.mempool rho.inbox v τ := by
  have hmem := List.mem_of_getElem? he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hv.tick_total v (hv.honest_only _ hmem) τ
    (hv.in_horizon _ hmem).1 (hv.in_horizon _ hmem).2 (hv.deliver_awake v p τ hmem))
  have hord {a b : Nat} {ea eb : Model.Event V (protoOf (compiled F) E).Object}
      (ha : rho.events[a]? = some ea) (hb : rho.events[b]? = some eb)
      (hab : a < b) : ea.time < eb.time ∨ (ea.time = eb.time ∧ ea.phase ≤ eb.phase) := by
    obtain ⟨ha', rfl⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hb', rfl⟩ := List.getElem?_eq_some_iff.mp hb
    exact List.pairwise_iff_getElem.mp hv.sorted a b ha' hb' hab
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · rw [hj] at he; cases he
    · rcases hord he hj h with h | ⟨-, h⟩ <;> simp [Model.Event.time, Model.Event.phase] at h
  have hil : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have key : ∀ m, j < m → m ≤ i → (rho.stateBefore m v).st.2 = Model.mempool rho.inbox v τ := by
    intro m hjm hmi
    induction m, hjm using Nat.le_induction with
    | base =>
      rw [rho.stateBefore_succ hj]
      simp only [Model.Run.step, Function.update_self]
      exact rho.tick_invariant (fun s => s.2 = _) _ v τ
        (fun s d _ hs => (compile_act_mempool _ s d).trans hs) (fun _ _ _ _ hs => hs) rfl
    | succ m hjm ih =>
      have ih := ih (by omega)
      have hem : rho.events[m]? = some rho.events[m] := List.getElem?_eq_getElem (by omega)
      generalize rho.events[m] = e at hem
      rw [rho.stateBefore_succ hem]
      have h₁ := hord hj hem (by omega)
      have h₂ := hord hem he (by omega)
      cases e with
      | restart w t =>
        simp only [Model.Event.time, Model.Event.phase] at h₁ h₂
        dsimp only [Time] at h₁ h₂
        omega
      | tick w t =>
        by_cases hw : v = w
        · subst hw
          simp only [Model.Event.time, Model.Event.phase] at h₁ h₂
          obtain rfl : t = τ := by dsimp only [Time] at h₁ h₂ ⊢; omega
          have := (hv.nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hj).1).mp (hj.trans hem.symm)
          omega
        · simpa [Model.Run.step, Function.update_of_ne hw] using ih
      | deliver w q t =>
        by_cases hw : v = w
        · subst hw
          simp only [Model.Run.step, Function.update_self]
          exact rho.deliver_invariant (fun s => s.2 = _) _ v q t
            (fun s d _ hs => (compile_act_mempool _ s d).trans hs) (fun _ _ _ _ hs => hs) ih
        · simpa [Model.Run.step, Function.update_of_ne hw] using ih
  exact key i hji le_rfl

/-- The payload of an honest proposal is the proposer's mempool at the release
time `τ` (whatever the release filter or a restart before the tick did). A
proposal released at a delivery at `τ` carries the mempool of the node's tick
at `τ`, which in a valid run precedes the delivery (`deliver_state_mempool`). -/
theorem honestProposal_payload {rho : Model.Run (compiled F) E} (hv : rho.ExecutionValid)
    {τ : Time} {k : Fin (Fintype.card V)} {h : Header Info} (hp : HonestProposal rho τ k h) :
    h.input = encodeTxs (Model.mempool rho.inbox (rho.key k) τ) := by
  obtain ⟨-, r, cs, -, hr⟩ := hp
  rcases rho.releases_provenance hr with ⟨i, -, hd | hc⟩ | ⟨i, q, hi, hd | hc⟩
  · obtain ⟨d, -, st', hst', hc⟩ := (rho.dutyCandidate_iff).mp hd
    obtain ⟨m, cs', hact, -, he⟩ := (rho.mem_signedCandidate).mp hc
    injection he with _ hm
    subst hm
    rw [act_item_payload (F (pubOf E)) st' d hact, tickReach_mempool hst']
    rfl
  · obtain ⟨mc, -, he⟩ := Model.mem_gossipCandidates.mp hc
    injection he with ha
    cases ha
  · obtain ⟨d, -, st', hst', hc⟩ := (rho.deliverCandidate_iff).mp hd
    obtain ⟨m, cs', hact, -, he⟩ := (rho.mem_signedCandidate).mp hc
    injection he with _ hm
    subst hm
    rw [act_item_payload (F (pubOf E)) st' d hact, tickReach_mempool hst']
    exact congrArg encodeTxs (deliver_state_mempool hv hi)
  · obtain ⟨mc, -, he⟩ := Model.mem_gossipCandidates.mp hc
    injection he with ha
    cases ha

end Consensus.Shape

end
