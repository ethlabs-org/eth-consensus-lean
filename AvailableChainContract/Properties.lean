module
public import AvailableChainContract.Conditions

@[expose] public section

/-! # Properties of outputs

An output is one of the protocol's getters, `P.State → CBlock`, read at a node
and a time (`Run.readOut`). Safety speaks about every honest read. Inclusion,
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

/-- Two outputs do not conflict across honest reads from `t₀` to the horizon. -/
def ConsistentFrom (g₁ g₂ : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    CBlock.Compatible (rho.readOut g₁ u t) (rho.readOut g₂ v t')

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (g : Output F E) (t₀ : Time) : Prop := rho.ConsistentFrom g g t₀

/-- Each honest node's reads of `g` only extend from `t₀` on. -/
def MonotoneFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
    CBlock.Preceq (rho.readOut g v t) (rho.readOut g v t')

/-- Safety of `g` from `t₀`. -/
structure SafeFrom (g : Output F E) (t₀ : Time) : Prop where
  agree : rho.AgreeFrom g t₀
  monotone : rho.MonotoneFrom g t₀

/-- Provenance and slot order: every non-genesis block `B` in an honest read
of `g` at `t` (the tip or any ancestor) has a slot above its parent's slot and
not after `t`, and the reader has seen a proposal of `B` under the proposer key
of `B`'s slot. -/
def OutputValid (g : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ t B, CBlock.Preceq B (rho.readOut g v t) → B ≠ .genesis →
    B.parent.slot < B.slot ∧ (protoOf F E).proposalTime B.slot ≤ t ∧
    ∃ cs, (Obj.mk (.proposer B.slot) (.prop B) cs : (protoOf F E).Object) ∈ rho.View v t

/-- Output `g₁` is below output `g₂` in every honest read. -/
def Below (g₁ g₂ : Output F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, CBlock.Preceq (rho.readOut g₁ v t) (rho.readOut g₂ v t)

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
