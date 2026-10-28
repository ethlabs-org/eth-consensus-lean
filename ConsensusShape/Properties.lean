module
public import ConsensusShape.Run
public import ConsensusProblem.Assumptions
@[expose] public section

/-! Block properties at event cuts and end-of-time cuts, using the shape chain getters. -/
namespace Consensus.Shape
open Model

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}

namespace Run

variable (rho : Model.Run (compiled F) E)

/-- Provenance, linkage and slot order, at every event cut: an honest read of
`g` is a chain linked by the run's hash from genesis, with slots strictly
increasing from 1, and every header in it has a proposal time not after the
cut and was seen by the reader, before the cut, as a proposal under its own
slot's key. Unconditional: it holds even with hash collisions. -/
def OutputValid (g : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Linked rho.hash (readChainIdx rho g v i) ∧ Chain.SlotsFrom 0 (readChainIdx rho g v i) ∧
    ∀ h ∈ readChainIdx rho g v i, (protoOf F E).proposalTime h.slot ≤ rho.cutTime i ∧
      ∃ cs, (Model.Obj.mk
        (.signed (.inr h.slot) ⟨0, Nat.lt_min.mpr ⟨by decide, Fintype.card_pos⟩⟩)
        (.item h) cs : (compile (protoOf F E)).Object) ∈ rho.ViewIdx v i

/-- Header `h` is in the read of `g` of every ready reader at `t`. (Without a
hash collision, linkage and provenance fix the ancestry of `h`.) -/
def InBy (A : Assumptions) (g : Output F E) (h : Header) (t : Time) : Prop :=
  ∀ v, rho.point.Ready ((A.catchUp : Time) * E.Δ) v t → h ∈ readChainOut rho g v t

/-- Inclusion into `g` from `t₀` with delay `c·Δ`: for every slot after `t₀`
with a ready proposer, the proposer's own header is in every ready read
`c·Δ` after the proposal time. -/
def IncludedFrom (A : Assumptions) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ s : Slot, t₀ < (protoOf F E).proposalTime s → ReadyProposer rho ((A.catchUp : Time) * E.Δ) s →
    (protoOf F E).proposalTime s + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ h, HonestProposal rho s h ∧
      InBy rho A g h ((protoOf F E).proposalTime s + (c : Time) * E.Δ)

/-- Growth of `g` from `t₀` with delay `c·Δ`: at every time `t`, the header
`h` of a later honest ready proposer is in every ready read by `t + c·Δ`, and
every ready read at `t` is a strict prefix of every such later read cut at
`h`. -/
def LiveFrom (A : Assumptions) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ t, t₀ ≤ t → t + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ s h, t < (protoOf F E).proposalTime s ∧ ReadyProposer rho ((A.catchUp : Time) * E.Δ) s ∧
      HonestProposal rho s h ∧ InBy rho A g h (t + (c : Time) * E.Δ) ∧
      ∀ v w, rho.point.Ready ((A.catchUp : Time) * E.Δ) v t →
        rho.point.Ready ((A.catchUp : Time) * E.Δ) w (t + (c : Time) * E.Δ) →
        Chain.Prec (readChainOut rho g v t)
          (Chain.upTo h (readChainOut rho g w (t + (c : Time) * E.Δ)))

end Run

end Consensus.Shape
end
