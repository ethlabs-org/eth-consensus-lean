module
public import ConsensusLean.Comparison.Cost

@[expose] public section

/-! # Cost sanity tests

`SigningRate` counts own signatures at any depth of what a validator releases: a vote released
inside a container (an unsigned object carrying it) is counted as the vote, so a release of such a
container while honest refutes a zero vote coordinate. `⊤` is no claim. -/

namespace Consensus.Comparison.Test

open Consensus.Comparison Consensus.Shape Blocks
open Consensus.Model (Obj Auth Msg pubOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]

/-- **A vote inside a container is counted**: if `v`, honest at `τ`, releases at `τ` an unsigned
object carrying a vote `d` signed with its own key in role `.duty s k`, then `d` is one of `v`'s
signed objects of class `duty k` at slot `s`. -/
theorem nested_vote_counted {E : Env V} (rho : Model.Run (compiled F) E) (v : V) (τ : Time)
    (s : Slot) (k : (F (pubOf E)).skel.Kind) (m : Msg (Blocks.Header Info) (F (pubOf E)).Body)
    (cs : List (Model.protoOf (compiled F) E).Object)
    (b : Msg (Blocks.Header Info) (F (pubOf E)).Body) (hv : rho.point.HonestAt v τ)
    (hrel : rho.releases v (Obj.mk .none b [Obj.mk (.signed (rho.ownKey v) (.duty s k)) m cs]) τ) :
    Obj.mk (.signed (rho.ownKey v) (.duty s k)) m cs ∈ signedFor rho v (.duty k) s :=
  ⟨_, τ, hv, hrel, by
    simp only [Obj.parts, Obj.parts.partsList, List.append_nil]
    exact List.mem_cons_of_mem _ List.mem_cons_self, .duty s k, rfl, rfl⟩

/-- **A nested vote refutes a zero vote coordinate**: a valid run in which an honest validator
releases a container carrying its own vote of kind `k` violates every signing rate whose `duty k`
coordinate is `0`. -/
theorem nested_vote_refutes_zero (r : (Sys F V).Run) (hr : (Sys F V).Valid r) (v : V) (τ : Time)
    (s : Slot) (k : (F (pubOf r.1)).skel.Kind) (m : Msg (Blocks.Header Info) (F (pubOf r.1)).Body)
    (cs : List (Model.protoOf (compiled F) r.1).Object)
    (b : Msg (Blocks.Header Info) (F (pubOf r.1)).Body) (hv : r.2.point.HonestAt v τ)
    (hrel : r.2.releases v
      (Obj.mk .none b [Obj.mk (.signed (r.2.ownKey v) (.duty s k)) m cs]) τ)
    (σ : (pub : Model.Public) → SlotClass (F pub).skel.Kind → WithTop ℕ)
    (hσ : σ (pubOf r.1) (.duty k) = (0 : ℕ)) : ¬ SigningRate F V σ := by
  intro h
  have hle := h r hr v (.duty k) s 0 hσ
  have hmem := nested_vote_counted r.2 v τ s k m cs b hv hrel
  rw [Nat.cast_zero, nonpos_iff_eq_zero, Set.encard_eq_zero] at hle
  rw [hle] at hmem
  exact hmem

/-- `⊤` is no claim: every family meets the signing rate `⊤`. -/
theorem signingRate_top : SigningRate F V (fun _ _ => ⊤) := by
  intro r _ v c s d h
  simp at h

end Consensus.Comparison.Test

end
