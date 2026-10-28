module
public import ConsensusShape.Run

@[expose] public section

/-! # Shape-level payload facts (layer 1)

Signed objects come only from duties, and the only item-producing duties are
the slot and poll proposals, whose `input` `compile` writes from the
post-clock mempool. Gossip may emit unsigned items with any `input`, so the
payload facts are about *signed* item candidates only. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf Obj)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

omit [DecidableEq V] in
/-- Every signed item candidate is a proposal whose payload is the encoded
mempool of the candidate state. -/
theorem candidate_payload (rho : Model.Run (compiled F) E)
    (st : (compile (F (pubOf E))).State) (v : V) (t : Time) {k r} {h : Header Info} {cs}
    (ho : Obj.mk (.signed k r) (.item h) cs ∈ rho.candidates st v t) :
    h.input = encodeTxs st.2 := by
  obtain ⟨d, -, -, hact⟩ := rho.candidates_duty st v t ho rfl
  change (compile (F (pubOf E))).act st d = some (.item h, cs) at hact
  cases d with
  | propose s _ =>
    cases hp : (F (pubOf E)).propose st.1 s with
    | none => simp [compile, hp] at hact
    | some x =>
      obtain ⟨par, info, cs'⟩ := x
      simp only [compile, hp, Option.map_some] at hact
      injection hact with hact
      injection hact with hm
      injection hm with hm
      rw [← hm]
  | act s k =>
    cases hp : (F (pubOf E)).act st.1 s k with
    | none => simp [compile, hp] at hact
    | some x =>
      simp only [compile, hp, Option.map_some] at hact
      injection hact with hact
      injection hact with hm
      cases hm
  | pollPropose u =>
    cases hp : (F (pubOf E)).pollPropose st.1 (u : Time) with
    | none => simp [compile, hp] at hact
    | some x =>
      obtain ⟨par, pos, info, cs'⟩ := x
      simp only [compile, hp, Option.map_some] at hact
      injection hact with hact
      injection hact with hm
      injection hm with hm
      rw [← hm]
  | poll u =>
    cases hp : (F (pubOf E)).poll st.1 (u : Time) with
    | none => simp [compile, hp] at hact
    | some x =>
      simp only [compile, hp, Option.map_some] at hact
      injection hact with hact
      injection hact with hm
      cases hm

/-- The payload of an honest proposal is the proposer's mempool at the release
time `τ` (whatever the release filter or a restart before the tick did). -/
theorem honestProposal_payload {rho : Model.Run (compiled F) E} {τ : Time}
    {k : Fin (Fintype.card V)} {h : Header Info} (hp : HonestProposal rho τ k h) :
    h.input = encodeTxs (Model.mempool rho.inbox (rho.key k) τ) := by
  obtain ⟨-, r, cs, -, hr⟩ := hp
  obtain ⟨st, hc⟩ := rho.releases_candidate hr
  exact candidate_payload rho _ _ _ hc

end Consensus.Shape

end
