module
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainGeneric.Statements.Pure.PCQuorum
public import AvailableChainEngineV2.Conditions.Duty.Interface -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Committees

@[expose] public section

/-! The PC persistence companion over Duty runs. Source:
`tip-stability/spec/drafts/pcsa34-r3.md` §5.4 and Appendix B, and the premise
ARM(s,B,j₀) of `pcsa34-r3-open.md`. The v1 template is
`AvailableChainStatements/Strong/{Interface,Regimes,Claims}.lean`
(`StrongInterface`, `StrongArmedRegime`, `StrongClaims`); that contract is
frozen and stays unchanged. This module first mirrors, over Duty runs, the
DC properties and conditions that the companion reads (`InBy`, `PersistsFrom`,
`HonestProposalAt`, `HonestAwakeProposer`, `IncludedFrom`, `AwakeMajority`,
`FullParticipation`). It then states the companion. Statements only; the
PCSA instance proves the companion. -/

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D
open AvailableChain.Gen.Pure

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: DecoupledConsensusStatements/Generic/Properties.lean:86 (b241081, 2026-09-28); same:
-- verbatim mirror over Duty runs.
-- AC v1: AvailableChainStatements/Generic/Properties.lean:51 (b15feea).
/-- Block `B` is in every honest read of `g` at time `t`. -/
def InBy (E : Generic.Env V) (rho : D.Run V P) (g : D.Output P) (B : Block) (t : Time) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq B (D.outputAt E rho g v t)

theorem InBy_def (E : Generic.Env V) (rho : D.Run V P) (g : D.Output P) (B : Block)
    (t : Time) :
    InBy E rho g B t = (∀ v ∈ rho.honest, Block.Preceq B (D.outputAt E rho g v t)) := by rfl

-- DC: DecoupledConsensusStatements/Generic/Properties.lean:124 (b241081, 2026-09-28); same:
-- verbatim mirror over Duty runs.
-- AC v1: AvailableChainStatements/Generic/Properties.lean:100 (b15feea).
/-- Every block in an honest read of `g` at `T` is in every honest read of `g`
from `b₀` to the horizon. -/
def PersistsFrom (E : Generic.Env V) (rho : D.Run V P) (g : D.Output P) (T b₀ : Time) :
    Prop :=
  ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (D.outputAt E rho g v T) →
    ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy E rho g B t

theorem PersistsFrom_def (E : Generic.Env V) (rho : D.Run V P) (g : D.Output P)
    (T b₀ : Time) :
    PersistsFrom E rho g T b₀ =
      (∀ v ∈ rho.honest, ∀ B, Block.Preceq B (D.outputAt E rho g v T) →
        ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy E rho g B t) := by rfl

-- DC: DecoupledConsensusStatements/Generic/Properties.lean:92 (b241081, 2026-09-28);
-- INTENTIONAL: the AC v1 form (AvailableChainStatements/Generic/Properties.lean:58,
-- b15feea): emission of a proposal object signed by the slot's single proposal seat,
-- in place of DC's `proposedBlock` reader.
/-- The honest proposal of slot `s` is `B`: the honest proposer of `s` emitted,
at the proposal time, a proposal object whose payload proposes `B`. -/
def HonestProposalAt (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P) (s : Slot)
    (B : Block) : Prop :=
  D.proposerOf rho I s ∈ rho.honest ∧
    ∃ p, I.block p = some B ∧
      D.Run.emits E rho (D.proposerOf rho I s) ⟨.seat (I.propLabel s) (D.propSeat I s), p⟩
        (D.proposalTime I s)

theorem HonestProposalAt_def (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P)
    (s : Slot) (B : Block) :
    HonestProposalAt E I rho s B =
      (D.proposerOf rho I s ∈ rho.honest ∧
        ∃ p, I.block p = some B ∧
          D.Run.emits E rho (D.proposerOf rho I s) ⟨.seat (I.propLabel s) (D.propSeat I s), p⟩
            (D.proposalTime I s)) := by rfl

-- DC: additive (no DC counterpart); reason: the AC v1 inclusion premise
-- (AvailableChainStatements/Generic/Properties.lean:67, b15feea), mirrored over Duty runs.
/-- The proposer of slot `s` is honest and awake at the proposal time. -/
def HonestAwakeProposer (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P)
    (s : Slot) : Prop :=
  D.proposerOf rho I s ∈ rho.honest ∧ E.awake (D.proposerOf rho I s) (D.proposalTime I s) = true

omit [DecidableEq V] in
theorem HonestAwakeProposer_def (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P)
    (s : Slot) :
    HonestAwakeProposer E I rho s =
      (D.proposerOf rho I s ∈ rho.honest ∧
        E.awake (D.proposerOf rho I s) (D.proposalTime I s) = true) := by rfl

-- DC: DecoupledConsensusStatements/Generic/Properties.lean:114 (b241081, 2026-09-28);
-- INTENTIONAL: the AC v1 form (AvailableChainStatements/Generic/Properties.lean:89,
-- b15feea): the proposer is honest and awake.
/-- Every slot after `t₀` whose proposer is honest and awake at the proposal
time has an honest proposal, and that block is in every honest read of `g`
within `delay` of the proposal time. -/
def IncludedFrom (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P) (g : D.Output P)
    (t₀ delay : Time) : Prop :=
  ∀ s : Slot, t₀ < D.proposalTime I s → HonestAwakeProposer E I rho s →
    D.proposalTime I s + delay ≤ rho.horizon →
    ∃ B : Block, HonestProposalAt E I rho s B ∧ InBy E rho g B (D.proposalTime I s + delay)

theorem IncludedFrom_def (E : Generic.Env V) (I : D.Interface P) (rho : D.Run V P)
    (g : D.Output P) (t₀ delay : Time) :
    IncludedFrom E I rho g t₀ delay =
      (∀ s : Slot, t₀ < D.proposalTime I s → HonestAwakeProposer E I rho s →
        D.proposalTime I s + delay ≤ rho.horizon →
        ∃ B : Block, HonestProposalAt E I rho s B ∧
          InBy E rho g B (D.proposalTime I s + delay)) := by rfl

-- DC: additive (no DC counterpart); reason: the AC v1 condition
-- (AvailableChainStatements/Generic/Conditions.lean:194, b15feea), mirrored over Duty runs.
/-- More honest validators are awake than there are faulty validators. -/
def AwakeMajority [Fintype V] (E : Generic.Env V) (rho : D.Run V P) (t : Time) : Prop :=
  (faulty rho).card < (awakeHonest E rho t).card

theorem AwakeMajority_def [Fintype V] (E : Generic.Env V) (rho : D.Run V P) (t : Time) :
    AwakeMajority E rho t = ((faulty rho).card < (awakeHonest E rho t).card) := by rfl

-- DC: DecoupledConsensusStatements/Generic/Conditions.lean:175 (b241081, 2026-09-28);
-- INTENTIONAL: the AC v1 form (AvailableChainStatements/Generic/Conditions.lean:206,
-- b15feea) starts at `start`, not at GST.
/-- Honest validators remain awake from `start` to the horizon. -/
def FullParticipation (E : Generic.Env V) (rho : D.Run V P) (start : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, start ≤ t → t ≤ rho.horizon → E.awake v t = true

omit [DecidableEq V] in
theorem FullParticipation_def (E : Generic.Env V) (rho : D.Run V P) (start : Time) :
    FullParticipation E rho start =
      (∀ v ∈ rho.honest, ∀ t, start ≤ t → t ≤ rho.horizon → E.awake v t = true) := by rfl

/-- The base interface with the PC-floored strong output. The available
output (`confirmed`) is `pcFloor S pc` (`Statements/Pure/PCFloor`), so
`strong ⪯ confirmed` and `B ⪯ strong → B ⪯ confirmed` follow from
`target_preceq_pcFloor` when `strong` is the held PC target. There is no
unconditional order between `strong` and `stable`. -/
structure PCInterface (P : ProtocolSpecD In) extends D.Interface P where
  strong : P.State → Block

/-- The arming regime of PC persistence: `StrongArmedRegime` with arming lag
`3Δ`, the safety fault cap `a < q_A n`, Duty delivery `delayOf`, and no
restart.

Seat counts. `Fam` must be exactly the labels with `n` seats that carry
PC-relevant signatures (HEAD and ack), never the single-seat proposal label.
An over-large `Fam` makes `seats` false for every run, so the claims become
vacuous. `cstar` makes each `Fam` label's seat map a bijection
onto the validators and `seats` gives each such label `n` seats, so a faulty
validator holds exactly one seat of each `Fam` label and the validator count
`(faulty rho).card` is the faulty seat count. This restores the v1 identity
`Fin n ≃ V`, as `cstar` does in FG-SA's `Base₂`
(`AvailableChainFGSAClaims/Statements/Regimes.lean:21`).

Delivery. The instance pins `delayOf`: `Δ` on HEAD, ack, PC and proposal
objects and `Δ_F` on FG rows. The `3Δ` arming arithmetic needs delay exactly
`Δ` on PC, ack and HEAD objects. `delayPos` excludes the degenerate delays
under which `healthy` has no run.

This is the ARM-healthy instance of the premise ARM(s,B,j₀)
(`pcsa34-r3-open.md`): delivery is healthy on the whole prefix from the start
of the run up to `b₀`, not on a suffix only. The suffix form is refuted by the
M-A execution of the Opus review. The read time `T` with `T + 3Δ ≤ b₀` gives
part (a) of ARM (the PC is stamped before `z_{j₀−1}` at every honest node);
the healthy prefix gives part (b) (every honest ack of slots in `[s+1, j₀)`
extends `B`). After `b₀` delivery is arbitrary. The recovery form
(ARM-same-slot: persistence of PC targets of height above μ after GST) is a
later, separate statement. -/
structure PCArmedRegime [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) (rho : D.Run V P)
    (T b₀ : Time) : Prop where
  execution : D.ExecutionValid E rho
  noRestart : D.NoRestart rho
  cstar : D.CStar Fam rho
  seats : ∀ ℓ, Fam ℓ → P.seats ℓ = n
  rootInjective : D.RootInjective E I.toInterface rho
  delayPos : ∀ o, 0 < delayOf o
  healthy : HealthyPrefixDeliveryBy E rho delayOf b₀
  faultBound : (faulty rho).card < qA n
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ rho.horizon
  armed : T + 3 * E.Δ ≤ b₀
  sleepyBefore : ∀ t, 0 ≤ t → t < b₀ → AwakeMajority E rho t

/-- The inclusion regime of the strong output (`FastRegime` shape): synchrony
from time 0, an awake honest majority, full participation, and the fault cap
`a ≤ n/4`, which lets the honest seats alone reach `q_N`. `Fam`, `cstar`,
`seats` and `delayPos` are as in `PCArmedRegime`. -/
structure PCIncludedRegime [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) (rho : D.Run V P)
    (t₀ : Time) : Prop where
  execution : D.ExecutionValid E rho
  noRestart : D.NoRestart rho
  cstar : D.CStar Fam rho
  seats : ∀ ℓ, Fam ℓ → P.seats ℓ = n
  rootInjective : D.RootInjective E I.toInterface rho
  delayPos : ∀ o, 0 < delayOf o
  partialSynchrony : PartialSynchronyBy E rho delayOf
  gst_zero : E.t_GST = 0
  start_zero : t₀ = 0
  participation : ∀ t, t₀ ≤ t → t ≤ rho.horizon → AwakeMajority E rho t
  fullParticipation : FullParticipation E rho t₀
  -- INTENTIONAL: `4a ≤ n` (spec pcsa34-r3.md §5, a ≤ n/4 on the PC path), not
  -- the v1 `BelowQuarter` (`4a < card V`, AvailableChainStatements/Generic/
  -- Conditions.lean:211): `n − a ≥ ⌈3n/4⌉ = q_N` already holds at `4a = n`.
  quarterCap : 4 * (faulty rho).card ≤ n

/-- PC persistence (spec §5.4, Π_pc = ∞): under the arming regime, every block
below an honest strong read at `T` is in every honest strong read from `b₀`
to the horizon. With `available = pcFloor S pc`, such a block is also below
every honest available read (`Statements/Pure/PCFloor`). -/
def PCPersistenceStatement [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) : Prop :=
  ∀ rho T b₀, PCArmedRegime E I Fam delayOf n rho T b₀ → PersistsFrom E rho I.strong T b₀

theorem PCPersistenceStatement_def [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) :
    PCPersistenceStatement E I Fam delayOf n =
      (∀ rho T b₀, PCArmedRegime E I Fam delayOf n rho T b₀ →
        PersistsFrom E rho I.strong T b₀) := by rfl

/-- Strong inclusion within `3Δ` under the inclusion regime. -/
def PCIncludedStatement [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) : Prop :=
  ∀ rho t₀, PCIncludedRegime E I Fam delayOf n rho t₀ →
    IncludedFrom E I.toInterface rho I.strong t₀ (3 * E.Δ)

theorem PCIncludedStatement_def [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) :
    PCIncludedStatement E I Fam delayOf n =
      (∀ rho t₀, PCIncludedRegime E I Fam delayOf n rho t₀ →
        IncludedFrom E I.toInterface rho I.strong t₀ (3 * E.Δ)) := by rfl

/-- The additive PC companion, modelled on `StrongClaims`. The instance fixes
the PC label family `Fam`, the per-object delivery delay `delayOf` (`Δ` on
HEAD, ack, PC and proposal objects; `Δ_F` on FG rows) and the committee size
`n`. It does not replace or restrict any field of a base contract. -/
structure PCCompanion [Fintype V] (E : Generic.Env V) (I : PCInterface P)
    (Fam : P.Label → Prop) (delayOf : P.Object → Time) (n : Nat) : Prop where
  persistence : PCPersistenceStatement E I Fam delayOf n
  included : PCIncludedStatement E I Fam delayOf n

end AvailableChain.Gen.V2.Duty
