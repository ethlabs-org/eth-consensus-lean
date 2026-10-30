module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Goldilocks SA: the lock store at reachable states (A0.4 (a), (b), (d), (f), A0.5, A0.6)

Unlocking is idempotent (`LockStore/Unlock`); at reachable states the live locks lie on one
chain and are viable or at or below `fc_root`, the FG candidates lie on one chain below the
anchor, and every live lock is below the effective record (`LockStore/Chain`, from the lock
invariant of `LockStore/Inv`); and the SA meets the interface requirements 1–4
(`LockStore/Requirements`). -/
