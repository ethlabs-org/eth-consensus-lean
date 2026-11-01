module
public import AvailableChainFGCompose.Statements.EventReads
public import AvailableChainSimplexFG.Store
public import AvailableChainKitFG.HeightLawsDef -- shake: keep (Compose import policy)

@[expose] public section
namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {V In : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal RowWire : Type}
structure FGCore (n : Nat) (Base Proposal RowWire : Type) where
  base : Base
  fg : Store (Fin n)
  proposals : List Proposal
  rowPool : List RowWire
structure FGCoreReads (P : V2.ProtocolSpecD In) (n : Nat) (Base Proposal RowWire : Type) where
  core : P.State → FGCore n Base Proposal RowWire
  erase : FGBlock (Fin n) → Block
  source : P.State → Option (FGBlock (Fin n))
  headVote : P.State → Slot → Block
  finalityHead : P.State → Option (FGBlock (Fin n))
  proposalFG : P.State → P.Object → Option (FGBlock (Fin n))
variable (R : FGCoreReads P n Base Proposal RowWire)
structure FGCoreLaws (R : FGCoreReads P n Base Proposal RowWire) : Prop where
  clock_fg : ∀ nd t, (R.core (P.clock nd t)).fg = (R.core nd).fg
  clock_proposals : ∀ nd t, (R.core (P.clock nd t)).proposals = (R.core nd).proposals
  clock_rowPool : ∀ nd t, (R.core (P.clock nd t)).rowPool = (R.core nd).rowPool
  process_tf : ∀ nd o, (R.core nd).fg.TF ⊆ (R.core (P.process nd o)).fg.TF
  process_proposals : ∀ nd o, (R.core nd).proposals <+: (R.core (P.process nd o)).proposals
  process_rowPool : ∀ nd o, (R.core nd).rowPool <+: (R.core (P.process nd o)).rowPool
  own_core : ∀ nd o, R.core (P.recordOwn nd o) = R.core nd
  source_mem : ∀ nd C, R.source nd = some C → C ∈ (R.core nd).fg.TF
  erase_inj : Function.Injective R.erase
structure FGHeadLaws (R : FGCoreReads P n Base Proposal RowWire)
    (E : Generic.Env V) (rho : V2.D.Run V P) : Prop where
  head_mem : ∀ i x t s, ∃ B ∈ (R.core (P.clock (V2.D.Run.stateBefore E rho i x) t)).fg.TF,
    R.erase B = R.headVote (P.clock (V2.D.Run.stateBefore E rho i x) t) s
  parent_closed : ∀ i x B, B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
    B.parent ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF
def TFAt (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) : Finset (FGBlock (Fin n)) :=
  (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF
theorem TFAt_def (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    TFAt R E rho i x = (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF := rfl
def ChainRowsBefore (E : Generic.Env V) (rho : V2.D.Run V P) (X : FGBlock (Fin n))
    (cut : Time) : Prop :=
  ∀ W, FGBlock.Preceq W X → ∀ row ∈ W.rows, ∃ x t, x ∈ rho.honest ∧ t < cut ∧
    Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ (R.core nd).fg.TF) t x
theorem ChainRowsBefore_def (E : Generic.Env V) (rho : V2.D.Run V P) (X : FGBlock (Fin n))
    (cut : Time) :
    ChainRowsBefore R E rho X cut = (∀ W, FGBlock.Preceq W X → ∀ row ∈ W.rows, ∃ x t,
      x ∈ rho.honest ∧ t < cut ∧
      Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ (R.core nd).fg.TF) t x) :=
  rfl
structure FGSourceService (R : FGCoreReads P n Base Proposal RowWire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time)
    (opening roundSlot : Nat) (D : FGBlock (Fin n)) : Prop where
  openingSource : opening = roundSlot → ∃ nd, postClock E rho x t = some nd ∧ R.source nd = some D
  coveredSource : opening < roundSlot → ∃ nd C, postClock E rho x t = some nd ∧
    R.source nd = some C ∧ FGBlock.Preceq D C

end AvailableChain.FGCompose
end
