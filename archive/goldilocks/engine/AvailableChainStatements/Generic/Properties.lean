module
public import AvailableChainStatements.Generic.Interface

@[expose] public section

namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} {P : AvailableChain.Generic.ProtocolSpec n} [DecidableEq V]

/-- Two outputs do not conflict across honest reads from `t₀` to the horizon. -/
def ConsistentFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g₁ g₂ : Output P)
    (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (readAt P rho g₁ u t) (readAt P rho g₂ v t')

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (t₀ : Time) : Prop :=
  ConsistentFrom P rho g g t₀

/-- Each honest node's reads of `g` only extend from `t₀` on. -/
def MonotoneFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (readAt P rho g v t) (readAt P rho g v t')

/-- Safety of `g` from `t₀`: honest reads agree and only extend. -/
structure SafeFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (t₀ : Time) : Prop where
  agree : AgreeFrom P rho g t₀
  monotone : MonotoneFrom P rho g t₀

/-- One output is below another at every node and time. -/
def Prefix (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g₁ g₂ : Output P) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, Block.Preceq (readAt P rho g₁ v t) (readAt P rho g₂ v t)

/-- The stable and confirmed outputs are ordered by prefix. -/
structure OutputOrder (P : AvailableChain.Generic.ProtocolSpec n)
    (I : Interface P) (rho : AvailableChain.Generic.Run V P) : Prop where
  stableBelowConfirmed : Prefix P rho I.stable I.confirmed

/-- Block `B` is in every honest read of `g` at time `t`. -/
def InBy (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (B : Block) (t : Time) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq B (readAt P rho g v t)

/-- The honest proposal of slot `s` is `B`: the honest proposer of `s` emitted,
at the proposal time, a proposal object whose payload proposes `B`. -/
def HonestProposalAt (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (s : Slot)
    (B : Block) : Prop :=
  rho.proposerOf s ∈ rho.honest ∧
    ∃ p, I.block p = some B ∧
      AvailableChain.Generic.Run.emits P E rho (rho.proposerOf s)
        ⟨.proposer s, p⟩ (P.proposalTime s)

/-- The proposer of slot `s` is honest and awake at the proposal time. -/
def HonestAwakeProposer (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) (s : Slot) : Prop :=
  rho.proposerOf s ∈ rho.honest ∧ E.awake (rho.proposerOf s) (P.proposalTime s) = true

/-- A block proposed by an honest proposer strictly after `t`. -/
def honestAfter (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (t : Time)
    (B : Block) : Prop :=
  ∃ s : Slot, t < P.proposalTime s ∧ HonestProposalAt E I rho s B

/-- Liveness of `g` from `t₀`: from every time `t ≥ t₀`, some block proposed by an honest proposer
after `t` is strictly above every honest read at `t` and in every honest read by `t + D`. -/
def LiveFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (rho : AvailableChain.Generic.Run V P)
    (g : Output P) (t₀ D : Time) : Prop :=
  ∀ t : Time, t₀ ≤ t → t + D ≤ rho.horizon →
    ∃ B : Block, honestAfter E I rho t B ∧
      (∀ v ∈ rho.honest, Block.Prec (readAt P rho g v t) B) ∧ InBy P rho g B (t + D)

/-- Inclusion into `g` from `t₀`: every slot after `t₀` whose proposer is honest
and awake at the proposal time has an honest proposal, and that block is in
every honest read within `D` of the proposal time. -/
def IncludedFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (t₀ D : Time) : Prop :=
  ∀ s : Slot, t₀ < P.proposalTime s → HonestAwakeProposer E rho s →
    P.proposalTime s + D ≤ rho.horizon →
    ∃ B : Block, HonestProposalAt E I rho s B ∧
      InBy P rho g B (P.proposalTime s + D)

/-- Persistence of `g`: every block in an honest read of `g` at `T` is in every honest read of `g`
at every time from `b₀` to the horizon. -/
def PersistsFrom (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (T b₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (readAt P rho g v T) →
    ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy P rho g B t

/-- Persistence only through the half-open interval `[b₀,b₁)`. -/
def PersistsThrough (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (readAt P rho g v T) →
    ∀ t, b₀ ≤ t → t < b₁ → InBy P rho g B t

/-- A proposed block is in no honest read before its proposal time. -/
def NoFutureRead (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (g : Output P) : Prop :=
  ∀ v ∈ rho.honest, ∀ t (s : Slot) (B : Block),
    HonestProposalAt E I rho s B → t < P.proposalTime s →
    ¬ Block.Preceq B (readAt P rho g v t)

end AvailableChain.Statements.Generic

end
