module
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainPCSAClaims.Statements.Regimes

@[expose] public section

/-! [PC-SA claims, M1] The Statements-layer claims of the PC path, as Props
with `_def` equations and no proofs (lead brief 2026-10-05). Each claim is
`∀ {V} [DecidableEq V] [Fintype V] {In} (c E rho), premise → conclusion`,
the FG-SA claim shape (`FGSAClaims/Claims/Foundations.lean`). The proof
phase proves them; the pure lemmas (`qN_head_unique`, `qA_honest`,
`preferPC_*`, `pcFloor_*`) are on the Generic PC branch. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [pcsa34-r3 5.1] PC uniqueness per slot: under fewer than `q_A` faults, two
PCs of one slot held by honest nodes at any times have one target. -/
def PCUniquenessClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    Base₂ p c E rho → FaultsBelowQA p c rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time),
      ∀ c₁ ∈ (storeAt p c E rho x t).pcs, ∀ c₂ ∈ (storeAt p c E rho y t').pcs,
        c₁.slot = c₂.slot → c₁.target = c₂.target

theorem PCUniquenessClaim_def (p : Params) : PCUniquenessClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      Base₂ p c E rho → FaultsBelowQA p c rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time),
        ∀ c₁ ∈ (storeAt p c E rho x t).pcs, ∀ c₂ ∈ (storeAt p c E rho y t').pcs,
          c₁.slot = c₂.slot → c₁.target = c₂.target) := by
  rw [PCUniquenessClaim]

/-- [pcsa34-r3 A6; lead ruling D1] One ack per seat per slot: an honest node
emits at most one ack object per slot and seat (one `ackAction s`, at `e_s`
only, one object per label and seat per tick). -/
def OneAckPerSlotClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    V2.D.ExecutionValid E rho →
    ∀ x ∈ rho.honest, ∀ (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time),
      V2.D.Run.emits E rho x (ackObj p s i r) t → V2.D.Run.emits E rho x (ackObj p s i r') t' →
      r = r' ∧ t = t' ∧ t = SA.earlyTime p.toParams s

theorem OneAckPerSlotClaim_def (p : Params) : OneAckPerSlotClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      V2.D.ExecutionValid E rho →
      ∀ x ∈ rho.honest, ∀ (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time),
        V2.D.Run.emits E rho x (ackObj p s i r) t →
        V2.D.Run.emits E rho x (ackObj p s i r') t' →
        r = r' ∧ t = t' ∧ t = SA.earlyTime p.toParams s) := by
  rw [OneAckPerSlotClaim]

/-- [pcsa34-r3 5.2, R4] PC dissemination before `z_s` under synchrony: when
`q_A` honest seats of slot `s` emit acks on one root at `e_s` and delivery is
healthy up to `z_s` (CLEAN, `Clean₂`), every honest node holds a PC of slot
`s` on that root after the ticks at `z_s` (so it is in every frozen view of
slot `s + 1`). The slot is positive: genesis needs no PC.

Premise `StageOneFrame` (plan C3; pcsa34-r4 5.3 (F7), stage 1): the target
must stay `F`-compatible at every honest node through `z_s`, also before
receipt (`reconcile` drops, and `pcValid` refuses, a PC whose target
conflicts with `F`; a block that conflicts with `F` is excluded, and the
delivery premise does not cover it). With the stage-1 frame `F` stays
genesis. The stage-2 form needs
CI (vi) ([FGSA.cleanFrame] HAND). The composed CLEAN result is
`CleanDisseminationClaim`. -/
def PCDisseminationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (s : Slot) (r : BlockId), 0 < s → SA.freezeTime p.toParams s ≤ b₀ →
      (∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
        rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
          (SA.earlyTime p.toParams s)) →
      ∀ y ∈ rho.honest, ∃ c' ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
        c'.slot = s ∧ c'.target.root = r

theorem PCDisseminationClaim_def (p : Params) : PCDisseminationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (s : Slot) (r : BlockId), 0 < s → SA.freezeTime p.toParams s ≤ b₀ →
        (∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
          rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
          V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
            (SA.earlyTime p.toParams s)) →
        ∀ y ∈ rho.honest,
          ∃ c' ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
            c'.slot = s ∧ c'.target.root = r) := by
  rw [PCDisseminationClaim]

/-- [pcsa34-r3 3.2, R7] Output nesting at every honest node and time:
`strong ⪯ available` and `F ⪯ available` (erased). No fault premise. -/
def OutputNestingClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    V2.D.ExecutionValid E rho →
    ∀ x ∈ rho.honest, ∀ t : Time,
      Block.Preceq (strong (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t)) ∧
      Block.Preceq (eraseFG (storeAt p c E rho x t).fg.F) (confirmed (storeAt p c E rho x t))

theorem OutputNestingClaim_def (p : Params) : OutputNestingClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      V2.D.ExecutionValid E rho →
      ∀ x ∈ rho.honest, ∀ t : Time,
        Block.Preceq (strong (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t)) ∧
        Block.Preceq (eraseFG (storeAt p c E rho x t).fg.F)
          (confirmed (storeAt p c E rho x t))) := by
  rw [OutputNestingClaim]

/-- [r4.2 §5.0 (CLEAN) and §5.2.3; SA clean safety] Available monotonicity on a healthy
prefix: at an honest node, the available output at `t ≤ t'` within the
prefix is below the available output at `t'`. Regime: CLEAN(b₀)
(`Clean₂`). Premise `StageOneFrame` (stage 1): if `F` moved so that it
conflicts with a held PC target, `reconcile` would drop the PC and the
output would fall from the target to `S`; with the stage-1 frame `F` stays
genesis. The stage-2 form needs CI (vi) ([FGSA.cleanFrame] HAND). -/
def AvailableMonotoneClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ x ∈ rho.honest, ∀ (t t' : Time), 0 ≤ t → t ≤ t' → t' ≤ b₀ →
      Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t'))

theorem AvailableMonotoneClaim_def (p : Params) : AvailableMonotoneClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ x ∈ rho.honest, ∀ (t t' : Time), 0 ≤ t → t ≤ t' → t' ≤ b₀ →
        Block.Preceq (confirmed (storeAt p c E rho x t))
          (confirmed (storeAt p c E rho x t'))) := by
  rw [AvailableMonotoneClaim]

/-- [GLY E-11, §C.3; D14; pcsa34-r4.3 §5.2.2 CI(iv)] On a healthy
prefix, every live lock at an honest node has a target below `S`
(`stableRecord`) and compatible with every held PC target.
The scope is `t ≤ b₀`; the outage lane needs its own lock fact after `b₀`.
Regime: CLEAN(b₀) (`Clean₂`), the PC fault premise and the stage-1 frame
(`StageOneFrame`: `F` stays genesis, so `reconcile` removes no lock).
Outside this lane, a conflicting PC below the stored rank can leave a
live lock in the store. The `effectiveLease` alias states only that the
lock is live; it does not state this compatibility. -/
def LeaseBelowRecordClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ x ∈ rho.honest, ∀ t : Time, 0 ≤ t → t ≤ b₀ →
      ∀ ℓ ∈ (storeAt p c E rho x t).base.obligations,
        (storeAt p c E rho x t).base.now < ℓ.2.2 →
        Block.Preceq ℓ.1 (storeAt p c E rho x t).base.stableRecord ∧
        ∀ P ∈ (storeAt p c E rho x t).pcs, Block.compatible ℓ.1 P.target = true

theorem LeaseBelowRecordClaim_def (p : Params) : LeaseBelowRecordClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ x ∈ rho.honest, ∀ t : Time, 0 ≤ t → t ≤ b₀ →
        ∀ ℓ ∈ (storeAt p c E rho x t).base.obligations,
          (storeAt p c E rho x t).base.now < ℓ.2.2 →
          Block.Preceq ℓ.1 (storeAt p c E rho x t).base.stableRecord ∧
          ∀ P ∈ (storeAt p c E rho x t).pcs, Block.compatible ℓ.1 P.target = true) := by
  rw [LeaseBelowRecordClaim]

/-- [PC-SA claims, M1] The six claims of the PC path, as one record. -/
structure PCSAPCClaims (p : Params) : Prop where
  pcUnique : PCUniquenessClaim p
  oneAck : OneAckPerSlotClaim p
  dissemination : PCDisseminationClaim p
  outputNesting : OutputNestingClaim p
  availableMonotone : AvailableMonotoneClaim p
  leaseBelowRecord : LeaseBelowRecordClaim p

end AvailableChain.PCSA.Run
end
