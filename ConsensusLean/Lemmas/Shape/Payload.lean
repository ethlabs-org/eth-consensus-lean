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

/-- The payload of an honest proposal is the proposer's mempool at the release
time `τ` (whatever the release filter or a restart before the tick did). -/
theorem honestProposal_payload {rho : Model.Run (compiled F) E} {τ : Time}
    {k : Fin (Fintype.card V)} {h : Header Info} (hp : HonestProposal rho τ k h) :
    h.input = encodeTxs (Model.mempool rho.inbox (rho.key k) τ) := by
  obtain ⟨-, r, cs, -, hr⟩ := hp
  obtain ⟨i, -, hd | hc⟩ := rho.releases_provenance hr
  · obtain ⟨d, -, st', hst', hc⟩ := (rho.dutyCandidate_iff).mp hd
    obtain ⟨m, cs', hact, -, he⟩ := (rho.mem_signedCandidate).mp hc
    injection he with _ hm
    subst hm
    rw [act_item_payload (F (pubOf E)) st' d hact, tickReach_mempool hst']
    rfl
  · obtain ⟨mc, -, he⟩ := Model.mem_gossipCandidates.mp hc
    injection he with ha
    cases ha

end Consensus.Shape

end
