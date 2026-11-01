module
public import AvailableChainGeneric.Statements.AC.Duty.Reads

@[expose] public section

namespace AvailableChain.Gen.AC.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A covering raw result passes the guard and writes the served block at
the fast level, with at least the proposed deadline.
Source: S1b R5 G1:361–367; blueprint 21 H.22:3207–3216; spec:899–921. -/
def GateService {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V) (D
    : Block) : Prop :=
  ∃ C, A.raw i s x = some C ∧ Block.Preceq D C ∧
    (∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) C) ∧
    D ∈ A.fast i s x ∧ ∃ deadline, SA.gateTime A.prm s + SA.lifetime A.prm ≤ deadline ∧
      (D, SA.releaseThreshold A.prm, deadline) ∈ A.leases (i + 1) x

theorem GateService_def {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x
    : V) (D : Block) :
    GateService A i s x D =
      (∃ C, A.raw i s x = some C ∧ Block.Preceq D C ∧
        (∀ lease ∈ (A.gateView i x s).obligations,
          Block.Compatible (Lease.target lease) C) ∧
        D ∈ A.fast i s x ∧ ∃ deadline,
          SA.gateTime A.prm s + SA.lifetime A.prm ≤ deadline ∧
          (D, SA.releaseThreshold A.prm, deadline) ∈ A.leases (i + 1) x) := by
  rw [GateService]

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The AC part of G1. The count and walk supplier gives `hcover` and
`hsupport` from the early clean batch and the anchor bound (G23/G10).
Only the lease and fast-set clauses of the local acceptance law are used.
`hlevel` leaves admission policy to the instance. A skipped gate cannot
supply `hwrite` for a covering result with a passing guard.
Source: S1b:361–367; blueprint 21:3199–3216; 22:1430–1437; spec:899–921.
Instances (F-31): FG-SA uses T7.15 `fgsaAC`, a fresh label, and the fast
branch of SA admission; SA uses the full view and genesis anchor. -/
def GateOfCoveringBatchStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
    {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V) (D : Block)
    (hwrite : ∀ C, A.raw i s x = some C →
      (∀ lease ∈ (A.gateView i x s).obligations,
        Block.Compatible (Lease.target lease) C) →
      A.leases (i + 1) x = A.gateLeases i x s C ∧ A.fast i s x = A.gateFast i x s C)
    (hcover : ∃ C, A.raw i s x = some C ∧ Block.Preceq D C)
    (hguard : ∀ C, A.raw i s x = some C →
      ∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) C)
    (hne : D ≠ .genesis) (hmem : D ∈ (A.gateView i x s).blocks)
    (hsupport : SA.releaseThreshold A.prm ≤ GridCO.prefixSupport A.prm.engine (A.gateView i x s)
      s D)
    (hlevel : SA.releaseThreshold A.prm ∈ A.gateLevels i x s D),
    GateService A i s x D

set_option linter.unusedVariables false in
theorem GateOfCoveringBatchStatement_def : GateOfCoveringBatchStatement =
    (∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
      {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V) (D : Block)
      (hwrite : ∀ C, A.raw i s x = some C →
        (∀ lease ∈ (A.gateView i x s).obligations,
          Block.Compatible (Lease.target lease) C) →
        A.leases (i + 1) x = A.gateLeases i x s C ∧ A.fast i s x = A.gateFast i x s C)
      (hcover : ∃ C, A.raw i s x = some C ∧ Block.Preceq D C)
      (hguard : ∀ C, A.raw i s x = some C →
        ∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) C)
      (hne : D ≠ .genesis) (hmem : D ∈ (A.gateView i x s).blocks)
      (hsupport : SA.releaseThreshold A.prm ≤ GridCO.prefixSupport A.prm.engine (A.gateView i x
        s) s D)
      (hlevel : SA.releaseThreshold A.prm ∈ A.gateLevels i x s D),
      GateService A i s x D) := by
  rw [GateOfCoveringBatchStatement]

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The AC part of G2. The two output-origin arguments supply `hold`:
an old gate output has an earlier slot, and an old finality output
precedes `X`. Only their consequence, no strict descendant of `X`, is
needed. `hbelow` is IF.4 at this node and post-gate index.
Source: S1b:368–371; blueprint 21:1110–1118, 2834–2847; spec:706–709, 909.
Instances (F-31): FG-SA uses T7.15's acceptance and lease facts; SA uses
the same advance rule, genesis normalization, and its lease invariant. -/
def SEqOfExactStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
    {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V) (X : Block)
    (hwrite : A.raw i s x = some X →
      (∀ lease ∈ (A.gateView i x s).obligations,
        Block.Compatible (Lease.target lease) X) →
      A.output (i + 1) x = normalizeOutput (A.anchor i x) (GridCO.advance (A.output i x) X))
    (hraw : A.raw i s x = some X)
    (hguard : ∀ lease ∈ (A.gateView i x s).obligations,
      Block.Compatible (Lease.target lease) X)
    (hold : Block.Preceq X (A.output i x) → A.output i x = X)
    (hanchor : Block.Preceq (A.anchor i x) X)
    (hbelow : ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
      Block.Preceq (Lease.target lease) (A.output (i + 1) x)),
    A.output (i + 1) x = X ∧
      ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
        Block.Preceq (Lease.target lease) X

set_option linter.unusedVariables false in
theorem SEqOfExactStatement_def : SEqOfExactStatement =
    (∀ {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}
      {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x : V) (X : Block)
      (hwrite : A.raw i s x = some X →
        (∀ lease ∈ (A.gateView i x s).obligations,
          Block.Compatible (Lease.target lease) X) →
        A.output (i + 1) x = normalizeOutput (A.anchor i x) (GridCO.advance (A.output i x) X))
      (hraw : A.raw i s x = some X)
      (hguard : ∀ lease ∈ (A.gateView i x s).obligations,
        Block.Compatible (Lease.target lease) X)
      (hold : Block.Preceq X (A.output i x) → A.output i x = X)
      (hanchor : Block.Preceq (A.anchor i x) X)
      (hbelow : ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
        Block.Preceq (Lease.target lease) (A.output (i + 1) x)),
      A.output (i + 1) x = X ∧
        ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
          Block.Preceq (Lease.target lease) X) := by
  rw [SEqOfExactStatement]

end AvailableChain.Gen.AC.Duty
