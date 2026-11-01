module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.RegressionFixture

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.ReplayObligations
open AvailableChain.SimplexFG

-- Sleep intervals match the source specifications; clock-only environments do not.
abbrev staleEnv : Generic.Env (Fin 4) :=
  ⟨1, by decide, 21, by decide, fun x t =>
    !(decide (x = 1 ∨ x = 2) && decide (19 ≤ t ∧ t < 21))⟩
abbrev slowEnv : Generic.Env (Fin 7) :=
  ⟨1, by decide, 1001, by decide, fun x t =>
    if x = 0 then !decide (999 ≤ t ∧ t < 1000)
    else !(decide (x.val ≤ 4) && decide (1000 ≤ t ∧ t < 1001))⟩
abbrev splitEnv : Generic.Env (Fin 7) :=
  ⟨2, by decide, 2002, by decide, fun x t =>
    if x = 0 then !decide (1998 ≤ t ∧ t < 2000)
    else !(decide (x.val ≤ 4) && decide (2000 ≤ t ∧ t < 2002))⟩

-- A full execution chooses a digest for its complete finite receipt domain.
-- The simple local digest is fixed only on the supplied certificate bodies.
def prefixDigest {n : Nat} (bodies : List (NamedProposal n))
    (digest : DigestInput n → BlockId) : Prop :=
  ∀ N ∈ bodies, digest N.digestInput = N.root

abbrev stale3Params (digest : DigestInput 4 → BlockId) : Params :=
  { StaleLeaseReplay.p3 with digest := digest }
abbrev stale4Params (digest : DigestInput 4 → BlockId) : Params :=
  { StaleLeaseReplay.p4 with digest := digest }
abbrev slowParams (digest : DigestInput 7 → BlockId) : Params :=
  { SlowLeaseReplay.params with digest := digest }
abbrev splitParams (digest : DigestInput 7 → BlockId) : Params :=
  { SplitBatchReplay.params with digest := digest }

-- These exact existential goals are OPEN. No theorem supplies their witnesses.
def k3Replay : Prop := ∃ digest : DigestInput 4 → BlockId,
  prefixDigest [StaleLeaseReplay.bodyB StaleLeaseReplay.p3,
    StaleLeaseReplay.bodyD StaleLeaseReplay.p3] digest ∧
  ∃ rho : V2.D.Run (Fin 4) (fgsa (stale3Params digest) unitCodec),
  rho.honest = {0, 1, 2} ∧
  RecoverySleep₂ (stale3Params digest) unitCodec staleEnv rho 8 1 ∧
  38 ≤ rho.horizon ∧
  PhaseInterval (stale3Params digest) unitCodec staleEnv rho 21 26 1 (some .genesis) false ∧
  PhaseBody (stale3Params digest) unitCodec staleEnv rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p3).erase ∧
  ¬ Transfers (stale3Params digest) unitCodec staleEnv rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p3).erase 26

def k4Replay : Prop := ∃ digest : DigestInput 4 → BlockId,
  prefixDigest [StaleLeaseReplay.bodyB StaleLeaseReplay.p4,
    StaleLeaseReplay.bodyD StaleLeaseReplay.p4] digest ∧
  ∃ rho : V2.D.Run (Fin 4) (fgsa (stale4Params digest) unitCodec),
  rho.honest = {0, 1, 2} ∧
  RecoverySleep₂ (stale4Params digest) unitCodec staleEnv rho 8 1 ∧
  38 ≤ rho.horizon ∧
  PhaseInterval (stale4Params digest) unitCodec staleEnv rho 21 30 1 (some .genesis) false ∧
  PhaseBody (stale4Params digest) unitCodec staleEnv rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p4).erase ∧
  ¬ Transfers (stale4Params digest) unitCodec staleEnv rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p4).erase 30

def slowReplay : Prop := ∃ digest : DigestInput 7 → BlockId,
  prefixDigest [SlowLeaseReplay.B, SlowLeaseReplay.J, SlowLeaseReplay.A] digest ∧
  ∃ rho : V2.D.Run (Fin 7) (fgsa (slowParams digest) unitCodec),
  rho.honest = {0, 1, 2, 3, 4} ∧
  RecoverySleep₂ (slowParams digest) unitCodec slowEnv rho 8 1 ∧ 1018 ≤ rho.horizon ∧
  ∃ J, PhaseInterval (slowParams digest) unitCodec slowEnv rho 1001 1010 3 (some J) false ∧
  PhaseBody (slowParams digest) unitCodec slowEnv rho 251 SlowLeaseReplay.B.erase ∧
  ¬ Transfers (slowParams digest) unitCodec slowEnv rho 251 SlowLeaseReplay.B.erase 1010

def splitCertificate (digest : DigestInput 7 → BlockId)
    (rho : V2.D.Run (Fin 7) (fgsa (splitParams digest) unitCodec)) (horizon : Time) : Prop :=
  prefixDigest [SplitBatchReplay.B, SplitBatchReplay.JA, SplitBatchReplay.JB,
    SplitBatchReplay.JC, SplitBatchReplay.A, SplitBatchReplay.C, SplitBatchReplay.WB] digest ∧
  rho.horizon = horizon ∧ rho.honest = {0, 1, 2, 3, 4} ∧
  RecoverySleep₂ (splitParams digest) unitCodec splitEnv rho 16 2 ∧
  PhaseInterval (splitParams digest) unitCodec splitEnv rho 2008 2058 3 none true ∧
  ∃ Q, HonestProposal splitEnv rho (fgsaInterface (splitParams digest) unitCodec) 254 Q ∧
    ¬ ExactService (splitParams digest) unitCodec splitEnv rho 254 Q

def splitReplay (horizon : Time) : Prop :=
  ∃ digest rho, splitCertificate digest rho horizon

def splitExtensions : Prop := ∃ digest first second,
  splitCertificate digest first 2070 ∧ splitCertificate digest second 2080 ∧
  first.events.take (afterTicksIdx first 2058) = second.events.take (afterTicksIdx second 2058)

/-- A concrete incompatible HEAD suffices to refute the old Transfers obligation. -/
theorem transfers_fail_of_head {p : Params} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p unitCodec))
    {s r : Slot} {B H : Block} {v : Time} {x : V}
    (hx : x ∈ rho.honest) (hsr : s + 1 ≤ r) (hrv : SA.voteTime p.toParams r ≤ v)
    (hhead : headAtLabel p unitCodec E rho x r = some H) (hbad : ¬ Block.Preceq B H) :
    ¬ Transfers p unitCodec E rho s B v :=
  fun h => hbad (h.1 x r H hx hsr hrv hhead)

end AvailableChain.FGSA.Run.Tests.ReplayObligations
end

#print axioms AvailableChain.FGSA.Run.Tests.ReplayObligations.transfers_fail_of_head
