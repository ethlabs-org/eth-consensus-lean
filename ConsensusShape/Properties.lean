module
public import ConsensusShape.Run
@[expose] public section

/-! Block properties at event cuts and end-of-time cuts, using the shape chain getters. -/
namespace Consensus.Shape
open AvailableChain (Slot Time)
open AvailableChain.Generic
open Model

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Model.Run (compiled F) E)

/-- Two outputs do not conflict across honest reads at event cuts from `t₀`
on. -/
def ConsistentFrom (g₁ g₂ : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j, InCuts rho t₀ i → InCuts rho t₀ j →
    Chain.Compatible (readChainIdx rho g₁ u i) (readChainIdx rho g₂ v j)

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (g : Output F E) (t₀ : Time) : Prop := ConsistentFrom rho g g t₀

/-- Each honest node's reads of `g` only extend, event by event, from `t₀`
on. -/
def MonotoneFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ i j, InCuts rho t₀ i → i ≤ j → InCuts rho t₀ j →
    Chain.Preceq (readChainIdx rho g v i) (readChainIdx rho g v j)

/-- Safety of `g` from `t₀`. -/
structure SafeFrom (g : Output F E) (t₀ : Time) : Prop where
  agree : AgreeFrom rho g t₀
  monotone : MonotoneFrom rho g t₀

/-- Safety of `g` from `t₀` for ready readers: reads of nodes that are ready at
the time of the cut agree, and a node's reads at two cuts where it is ready
only extend. (Used after recovery: a node asleep since before GST may keep an
old fork.) -/
structure ReadySafeFrom (C : Constants) (g : Output F E) (t₀ : Time) : Prop where
  agree : ∀ u v i j, InCuts rho t₀ i → InCuts rho t₀ j →
    rho.Ready ((C.catchUp : Time) * E.Δ) u (rho.cutTime i) →
    rho.Ready ((C.catchUp : Time) * E.Δ) v (rho.cutTime j) →
    Chain.Compatible (readChainIdx rho g u i) (readChainIdx rho g v j)
  monotone : ∀ v i j, InCuts rho t₀ i → i ≤ j → InCuts rho t₀ j →
    rho.Ready ((C.catchUp : Time) * E.Δ) v (rho.cutTime i) →
    rho.Ready ((C.catchUp : Time) * E.Δ) v (rho.cutTime j) →
    Chain.Preceq (readChainIdx rho g v i) (readChainIdx rho g v j)

/-- Provenance, linkage and slot order, at every event cut: an honest read of
`g` is a chain linked by the run's hash from genesis, with slots strictly
increasing from 1, and every header in it has a proposal time not after the
cut and was seen by the reader, before the cut, as a proposal under its own
slot's key. Unconditional: it holds even with hash collisions. -/
def OutputValid (g : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Linked rho.hash (readChainIdx rho g v i) ∧ Chain.SlotsFrom 0 (readChainIdx rho g v i) ∧
    ∀ h ∈ readChainIdx rho g v i, (protoOf F E).proposalTime h.slot ≤ rho.cutTime i ∧
      ∃ cs, (Model.Obj.mk (.signed (.inr h.slot) ⟨0, by exact Nat.zero_lt_succ 0⟩) (.item h) cs :
         (compile (protoOf F E)).Object) ∈ rho.ViewIdx v i

/-- Output `g₁` is a prefix of output `g₂` in every honest read, at every
event cut. -/
def Below (g₁ g₂ : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Preceq (readChainIdx rho g₁ v i) (readChainIdx rho g₂ v i)

/-- Header `h` is in the read of `g` of every ready reader at `t`. (Without a
hash collision, linkage and provenance fix the ancestry of `h`.) -/
def InBy (C : Constants) (g : Output F E) (h : Header) (t : Time) : Prop :=
  ∀ v, rho.Ready ((C.catchUp : Time) * E.Δ) v t → h ∈ readChainOut rho g v t

/-- Inclusion into `g` from `t₀` with delay `c·Δ`: for every slot after `t₀`
with a ready proposer, the proposer's own header is in every ready read
`c·Δ` after the proposal time. -/
def IncludedFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ s : Slot, t₀ < (protoOf F E).proposalTime s → ReadyProposer rho ((C.catchUp : Time) * E.Δ) s →
    (protoOf F E).proposalTime s + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ h, HonestProposal rho s h ∧
      InBy rho C g h ((protoOf F E).proposalTime s + (c : Time) * E.Δ)

/-- Growth of `g` from `t₀` with delay `c·Δ`: at every time `t`, the header
`h` of a later honest ready proposer is in every ready read by `t + c·Δ`, and
every ready read at `t` is a strict prefix of every such later read cut at
`h`. -/
def LiveFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ t, t₀ ≤ t → t + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ s h, t < (protoOf F E).proposalTime s ∧ ReadyProposer rho ((C.catchUp : Time) * E.Δ) s ∧
      HonestProposal rho s h ∧ InBy rho C g h (t + (c : Time) * E.Δ) ∧
      ∀ v w, rho.Ready ((C.catchUp : Time) * E.Δ) v t →
        rho.Ready ((C.catchUp : Time) * E.Δ) w (t + (c : Time) * E.Δ) →
        Chain.Prec (readChainOut rho g v t)
          (Chain.upTo h (readChainOut rho g w (t + (c : Time) * E.Δ)))

/-- Persistence of `g` on `[b₀, b₁)`: every honest read at `T` is, at every
time `t` of `[b₀, b₁)`, a prefix of the read of every honest node awake
throughout `[max 0 (b₀ − catchUp·Δ − 1), t]` (so ready before the outage
started and not restarted since). -/
def PersistsThrough (C : Constants) (g : Output F E) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, b₀ ≤ t → t < b₁ → ∀ w ∈ rho.honest,
    AwakeOnClosed E w (max 0 (b₀ - (C.catchUp : Time) * E.Δ - 1)) t →
    Chain.Preceq (readChainOut rho g v T) (readChainOut rho g w t)
noncomputable def slashedBy (A : Set (compile (protoOf F E)).Object) : Finset V := by
  classical
  exact Finset.univ.filter (rho.Slashable A)

def AccountablySafeFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j, InCuts rho t₀ i → InCuts rho t₀ j →
    Chain.Compatible (readChainIdx rho g u i) (readChainIdx rho g v j) ∨
      Fintype.card V ≤ 3 * (slashedBy rho (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card

end Run

end Consensus.Shape
end
