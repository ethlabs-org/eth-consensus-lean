module
public import AvailableChainContract.Conditions

@[expose] public section

/-! # Properties of outputs

An output is one of the protocol's getters, `P.State → CBlock`. Safety,
order and provenance read it at every event cut (`Run.readIdx`), since a client
can expose the state between any two events; liveness reads it at the end of a
time (`Run.readOut`). Safety speaks about every honest read. Inclusion,
growth and persistence speak about ready readers: honest nodes awake through
the catch-up window. Inclusion is of the honest proposer's own block, built
and signed by the engine. Provenance bounds every output from above: it holds
only proposed blocks that the reader has seen. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

/-- An output of the protocol run by `F` in `E`. -/
abbrev Output (F : Family) (E : Env V) := (protoOf F E).State → CBlock

namespace Run

variable (rho : Run F E)

/-- Event cut `i` is at or after time `t₀`: it includes at least one event at
a time `≥ t₀` (and at most all events). -/
def InCuts (t₀ : Time) (i : Nat) : Prop := rho.cutAt t₀ < i ∧ i ≤ rho.events.length

/-- Two outputs do not conflict across honest reads at event cuts from `t₀`
on. -/
def ConsistentFrom (g₁ g₂ : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j, rho.InCuts t₀ i → rho.InCuts t₀ j →
    CBlock.Compatible (rho.readIdx g₁ u i) (rho.readIdx g₂ v j)

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (g : Output F E) (t₀ : Time) : Prop := rho.ConsistentFrom g g t₀

/-- Each honest node's reads of `g` only extend, event by event, from `t₀`
on. -/
def MonotoneFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ i j, rho.InCuts t₀ i → i ≤ j → rho.InCuts t₀ j →
    CBlock.Preceq (rho.readIdx g v i) (rho.readIdx g v j)

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
    CBlock.Compatible (rho.readIdx g u i) (rho.readIdx g v j)
  monotone : ∀ v i j, rho.InCuts t₀ i → i ≤ j → rho.InCuts t₀ j →
    rho.Ready C v (rho.cutTime i) → rho.Ready C v (rho.cutTime j) →
    CBlock.Preceq (rho.readIdx g v i) (rho.readIdx g v j)

/-- Provenance and slot order, at every event cut: every non-genesis block `B`
in an honest read of `g` (the tip or any ancestor) has a slot above its
parent's slot and a proposal time not after the cut, and the reader has seen,
before the cut, a proposal of `B` under the proposer key of `B`'s slot. Slot 0
is genesis's slot, so no other block of slot 0 can be output. -/
def OutputValid (g : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i B, i ≤ rho.events.length →
    CBlock.Preceq B (rho.readIdx g v i) → B ≠ .genesis →
    B.parent.slot < B.slot ∧ (protoOf F E).proposalTime B.slot ≤ rho.cutTime i ∧
    ∃ cs, (Obj.mk (.proposer B.slot) (.prop B) cs : (protoOf F E).Object) ∈ rho.ViewIdx v i

/-- Output `g₁` is below output `g₂` in every honest read, at every event
cut. -/
def Below (g₁ g₂ : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ i, i ≤ rho.events.length →
    CBlock.Preceq (rho.readIdx g₁ v i) (rho.readIdx g₂ v i)

/-- `B` is in the read of `g` of every ready reader at `t`. -/
def InBy (C : Constants) (g : Output F E) (B : CBlock) (t : Time) : Prop :=
  ∀ v, rho.Ready C v t → CBlock.Preceq B (rho.readOut g v t)

/-- Inclusion into `g` from `t₀` with delay `c·Δ`: for every slot after `t₀`
with a ready proposer, the proposer's own block is in every ready read
`c·Δ` after the proposal time. -/
def IncludedFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ s : Slot, t₀ < (protoOf F E).proposalTime s → rho.ReadyProposer C s →
    (protoOf F E).proposalTime s + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ B, rho.HonestProposal s B ∧
      rho.InBy C g B ((protoOf F E).proposalTime s + (c : Time) * E.Δ)

/-- Growth of `g` from `t₀` with delay `c·Δ`: at every time `t`, the block of
a later honest ready proposer is strictly above every ready read at `t` and in
every ready read by `t + c·Δ`. -/
def LiveFrom (C : Constants) (g : Output F E) (t₀ : Time) (c : Nat) : Prop :=
  ∀ t, t₀ ≤ t → t + (c : Time) * E.Δ ≤ rho.horizon →
    ∃ s B, t < (protoOf F E).proposalTime s ∧ rho.ReadyProposer C s ∧
      rho.HonestProposal s B ∧
      (∀ v, rho.Ready C v t → CBlock.Prec (rho.readOut g v t) B) ∧
      rho.InBy C g B (t + (c : Time) * E.Δ)

/-- Persistence of `g` on `[b₀, b₁)`: every block in an honest read at `T` is,
at every time `t` of `[b₀, b₁)`, in the read of every honest node awake
throughout `[b₀ − catchUp·Δ − 1, t]` (so ready before the outage started and
not restarted since). -/
def PersistsThrough (C : Constants) (g : Output F E) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ B, CBlock.Preceq B (rho.readOut g v T) →
    ∀ t, b₀ ≤ t → t < b₁ → ∀ w ∈ rho.honest,
      AwakeOnClosed E w (b₀ - (C.catchUp : Time) * E.Δ - 1) t →
      CBlock.Preceq B (rho.readOut g w t)

end Run

end AvailableChain.Contract

end
