module
public import AvailableChainContract.Conditions

@[expose] public section

/-! # Properties of outputs

An output is one of the protocol's getters, `P.State → Chain`. Safety,
order and provenance read it at every event cut (`Run.readIdx`), since a client
can expose the state between any two events; liveness reads it at the end of a
time (`Run.readOut`). Safety speaks about every honest read. Inclusion,
growth and persistence speak about ready readers: honest nodes awake through
the catch-up window. Inclusion is of the honest proposer's own block, built
and signed by the engine. Provenance bounds every output from above: it holds
only linked, proposed headers that the reader has seen. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

/-- An output of the protocol run by `F` in `E`. -/
abbrev Output (F : Family) (E : Env V) := (protoOf F E).State → Chain

namespace Run

variable (rho : Run F E)

/-- Event cut `i` is at or after time `t₀`: it includes at least one event at
a time `≥ t₀` (and at most all events). -/
def InCuts (t₀ : Time) (i : Nat) : Prop := rho.cutAt t₀ < i ∧ i ≤ rho.events.length

/-- Two outputs do not conflict across honest reads at event cuts from `t₀`
on. -/
def ConsistentFrom (g₁ g₂ : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j, rho.InCuts t₀ i → rho.InCuts t₀ j →
    Chain.Compatible (rho.readIdx g₁ u i) (rho.readIdx g₂ v j)

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (g : Output F E) (t₀ : Time) : Prop := rho.ConsistentFrom g g t₀

/-- Each honest node's reads of `g` only extend, event by event, from `t₀`
on. -/
def MonotoneFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ i j, rho.InCuts t₀ i → i ≤ j → rho.InCuts t₀ j →
    Chain.Preceq (rho.readIdx g v i) (rho.readIdx g v j)

/-- Safety of `g` from `t₀`. -/
structure SafeFrom (g : Output F E) (t₀ : Time) : Prop where
  agree : rho.AgreeFrom g t₀
  monotone : rho.MonotoneFrom g t₀

/-- Safety of `g` from `t₀` for ready readers: reads of nodes that are ready at
the time of the cut agree, and a node's reads at two cuts where it is ready
only extend. (Used after recovery: a node asleep since before GST may keep an
old fork.) -/
structure ReadySafeFrom (C : Constants) (g : Output F E) (t₀ : Time) : Prop where
  agree : ∀ u v i j, rho.InCuts t₀ i → rho.InCuts t₀ j →
    rho.Ready C u (rho.cutTime i) → rho.Ready C v (rho.cutTime j) →
    Chain.Compatible (rho.readIdx g u i) (rho.readIdx g v j)
  monotone : ∀ v i j, rho.InCuts t₀ i → i ≤ j → rho.InCuts t₀ j →
    rho.Ready C v (rho.cutTime i) → rho.Ready C v (rho.cutTime j) →
    Chain.Preceq (rho.readIdx g v i) (rho.readIdx g v j)

/-- Provenance, linkage and slot order, at every event cut: an honest read of
`g` is a chain linked by the run's hash from genesis, with slots strictly
increasing from 1, and every header in it has a proposal time not after the
cut and was seen by the reader, before the cut, as a proposal under its own
slot's key. Unconditional: it holds even with hash collisions. -/
def OutputValid (g : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Linked rho.hash (rho.readIdx g v i) ∧ Chain.SlotsFrom 0 (rho.readIdx g v i) ∧
    ∀ h ∈ rho.readIdx g v i, (protoOf F E).proposalTime h.slot ≤ rho.cutTime i ∧
      ∃ cs, (Obj.mk (.proposer h.slot) (.prop h) cs : (protoOf F E).Object) ∈ rho.ViewIdx v i

/-- Output `g₁` is a prefix of output `g₂` in every honest read, at every
event cut. -/
def Below (g₁ g₂ : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    Chain.Preceq (rho.readIdx g₁ v i) (rho.readIdx g₂ v i)

/-- Header `h` is in the read of `g` of every ready reader at `t`. (Without a
hash collision, linkage and provenance fix the ancestry of `h`.) -/
def InBy (C : Constants) (g : Output F E) (h : Header) (t : Time) : Prop :=
  ∀ v, rho.Ready C v t → h ∈ rho.readOut g v t

/-- Inclusion into `g` from `t₀` with delay `c·Δ`: for every slot after `t₀`
with a ready proposer, the proposer's own header is in every ready read
`c·Δ` after the proposal time. -/
def IncludedFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ s : Slot, t₀ < (protoOf F E).proposalTime s → rho.ReadyProposer C s →
    (protoOf F E).proposalTime s + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ h, rho.HonestProposal s h ∧
      rho.InBy C g h ((protoOf F E).proposalTime s + (c : Time) * E.Δ)

/-- Growth of `g` from `t₀` with delay `c·Δ`: at every time `t`, the header
`h` of a later honest ready proposer is in every ready read by `t + c·Δ`, and
every ready read at `t` is a strict prefix of every such later read cut at
`h`. -/
def LiveFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ t, t₀ ≤ t → t + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ s h, t < (protoOf F E).proposalTime s ∧ rho.ReadyProposer C s ∧
      rho.HonestProposal s h ∧ rho.InBy C g h (t + (c : Time) * E.Δ) ∧
      ∀ v w, rho.Ready C v t → rho.Ready C w (t + (c : Time) * E.Δ) →
        Chain.Prec (rho.readOut g v t) (Chain.upTo h (rho.readOut g w (t + (c : Time) * E.Δ)))

/-- Persistence of `g` on `[b₀, b₁)`: every honest read at `T` is, at every
time `t` of `[b₀, b₁)`, a prefix of the read of every honest node awake
throughout `[max 0 (b₀ − catchUp·Δ − 1), t]` (so ready before the outage
started and not restarted since). -/
def PersistsThrough (C : Constants) (g : Output F E) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, b₀ ≤ t → t < b₁ → ∀ w ∈ rho.honest,
    AwakeOnClosed E w (max 0 (b₀ - (C.catchUp : Time) * E.Δ - 1)) t →
    Chain.Preceq (rho.readOut g v T) (rho.readOut g w t)

end Run

end AvailableChain.Contract

end
