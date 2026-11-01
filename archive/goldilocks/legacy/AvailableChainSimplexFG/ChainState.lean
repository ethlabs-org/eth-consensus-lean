module
public import AvailableChainSimplexFG.Objects

@[expose] public section

namespace AvailableChain.SimplexFG

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:204–234
/-- The fixed FG-SA parameter: the timeout delay `δ_t` in slots. The module
permits `δ_t = 0`; no statement of this module can depend on `δ_t > 0`. The
module has no `K` and no `D`: they belong to the `nj` latch, which this module
does not have. -/
structure FGConfig where
  timeoutDelay : Nat
  deriving DecidableEq, Repr

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:248–284
/-- A chain state `σ`, in the document's field order, with no `nj` field:
this module is FG-only. -/
structure ChainState (V : Type) where
  /-- The latest block. -/
  L : FGBlock V
  /-- `s = L.slot`. The state keeps it as a field because the fold writes it
  before `L`. -/
  s : Slot
  /-- The current height. -/
  h : Height
  /-- The block that carried the transition into height `h`. -/
  T_h : FGBlock V
  /-- The target-participation quorum set. -/
  target_participation : Finset V
  /-- The progress quorum set. -/
  progress : Finset V
  /-- The finality quorum set. -/
  finalize : Finset V
  /-- The latest justification on the chain. -/
  J : FGBlock V
  /-- The height of that justification. -/
  h_j : Height
  /-- The latest finalization on the chain. -/
  F : FGBlock V
  /-- The height of that finalization. -/
  h_F : Height
  deriving DecidableEq

namespace ChainState
variable {V : Type}

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:290–310
/-- The initial chain state: `L = T_h = J = F = genesis`, `s = 0`, `h = 1`,
`h_j = h_F = 0`, every quorum set empty. -/
def initial : ChainState V :=
  { L := .genesis
    s := 0
    h := 1
    T_h := .genesis
    target_participation := ∅
    progress := ∅
    finalize := ∅
    J := .genesis
    h_j := 0
    F := .genesis
    h_F := 0 }

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:312–327
def Q_target (σ : ChainState V) : Finset V := σ.target_participation
def Q_prog (σ : ChainState V) : Finset V := σ.progress
def Q_finality (σ : ChainState V) : Finset V := σ.finalize

variable [DecidableEq V] [Fintype V]

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:331–345
/-- `w(Q_target(σ)) ≥ q`. -/
def targetQuorum (E : Electorate V) (σ : ChainState V) : Bool :=
  decide (E.q ≤ E.weightOf σ.Q_target)

/-- `w(Q_prog(σ)) ≥ q`. -/
def progQuorum (E : Electorate V) (σ : ChainState V) : Bool :=
  decide (E.q ≤ E.weightOf σ.Q_prog)

/-- `w(Q_finality(σ)) ≥ q`. -/
def finalityQuorum (E : Electorate V) (σ : ChainState V) : Bool :=
  decide (E.q ≤ E.weightOf σ.Q_finality)

end ChainState

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:423–437
/-- `process_attestation` on the entry-bound pair (fgsa-protocol.tex Fig.
`alg:chain-full`). A finality pair equal to the chain's own `(h_j, J.root)`,
with `h_j > h_F`, sets the finality bit; a pair for another checkpoint does
not count. A height pair that matches `(σ.h, σ.T_h.root)` sets progress, and
sets target participation when it is not a timeout. -/
def process_row (σ : ChainState V) (row : Row V) : ChainState V :=
  let i := row.signer
  let afterFinality :=
    if decide (σ.h_F < σ.h_j) &&
        decide (row.finality_pair = some ⟨σ.h_j, σ.J.root⟩) then
      { σ with finalize := insert i σ.finalize }
    else σ
  if row.height_pair.matchesEntry σ.h σ.T_h.root then
    match row.height_pair with
    | .vote _ _ timeout =>
        if timeout then
          { afterFinality with progress := insert i afterFinality.progress }
        else
          { afterFinality with
            target_participation := insert i afterFinality.target_participation
            progress := insert i afterFinality.progress }
    | .empty => afterFinality
  else afterFinality

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:445–459
/-- The finality guard: `h_j > h_F`, and `Q_finality` is a quorum. -/
def finalityReady (E : Electorate V) (σ : ChainState V) : Bool :=
  decide (σ.h_F < σ.h_j) && σ.finalityQuorum E

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:467–474
/-- The progress guard: the transition consumes an exact target quorum
immediately. It consumes a progress quorum that can contain timeout rows only
at or after slot `T_h.slot + δ_t`. -/
def progReady (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) : Bool :=
  σ.targetQuorum E ||
    (decide (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s) && σ.progQuorum E)

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:476–496
/-- Enter the next height: carry `L` into `T_h`, clear target and progress.
There is no `nj` write: this module has no `nj` field. This function does not
clear `σ.finalize`; only the justification branch clears it. -/
def advance_height (σ : ChainState V) : ChainState V :=
  { σ with
    h := σ.h + 1
    T_h := σ.L
    target_participation := ∅
    progress := ∅ }

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:498–520
/-- Three branches in the document's order. The finality branch falls
through: it mutates `(F, h_F)` and the two height branches then read the
mutated state. The justification branch has priority over progress; its
guard is `targetQuorum` alone, because this module has no `nj`. The
justification write `(J, h_j) ← (T_h, h)` uses the height that the chain
leaves. -/
def process_height_events (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) :
    ChainState V :=
  let afterFinality :=
    if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ
  if afterFinality.targetQuorum E then
    advance_height
      { afterFinality with
        J := afterFinality.T_h
        h_j := afterFinality.h
        finalize := ∅ }
  else if progReady E cfg afterFinality then
    advance_height afterFinality
  else afterFinality

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:587–594
/-- Fold `rows` into `σ` at the geometry `geometry`, then run the height
events. -/
def transition (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (geometry : FGBlock V) (rows : List (Row V)) : ChainState V :=
  process_height_events E cfg
    { rows.foldl process_row { σ with s := geometry.slot } with L := geometry }

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:601–604
/-- [helper] The chain state at `B`: `derive` folds the rows of every ancestor
in order (alfs4 Fig. `alg:chain-full`, lines 890–954). -/
def derive (E : Electorate V) (cfg : FGConfig) : FGBlock V → ChainState V
  | .genesis => .initial
  | B@(.node p _ _ _ rs) => transition E cfg (derive E cfg p) B rs

def E4 : Electorate (Fin 4) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
def cfg1 : FGConfig := ⟨1⟩
def rowT (i : Fin 4) : Row (Fin 4) := ⟨i, .vote 1 genesisRoot false, none⟩
/-- `B1`: slot 1, body `0` (the honest body), three targets at height 1 for
genesis. -/
def B1 : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ 0 [rowT 0, rowT 1, rowT 2]

/-- Three of four matching targets at height 1 justify genesis at height 1. -/
example : (derive E4 cfg1 B1).h = 2 ∧ (derive E4 cfg1 B1).h_j = 1 := by decide
/-- Two rows are not a quorum: the height stays 1. -/
example : (derive E4 cfg1 (.node .genesis 1 ⟨15⟩ 0 [rowT 0, rowT 1])).h = 1 := by decide

def cfg0 : FGConfig := ⟨0⟩
def rowX (i : Fin 4) : Row (Fin 4) := ⟨i, .vote 1 genesisRoot true, none⟩
def BX : FGBlock (Fin 4) := .node .genesis 1 ⟨9⟩ 0 [rowX 0, rowX 1, rowX 2]
/-- δ_t = 0 is allowed: three timeouts at slot 1 cross height 1 at once, and
justify nothing. -/
example : (derive E4 cfg0 BX).h = 2 ∧ (derive E4 cfg0 BX).h_j = 0 := by decide
/-- With δ_t = 2 the same timeouts are not mature at slot 1 (1 < 0 + 2). -/
example : (derive E4 ⟨2⟩ BX).h = 1 := by decide

end AvailableChain.SimplexFG
end
