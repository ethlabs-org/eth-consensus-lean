module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C6, C7, C9, C14] The Clean lane
statements: the stamp convention of the PC snapshot, the joint clean invariant
CI (pcsa34-r4 5.2.2, stage 1), formation (5.3), and the clean corollaries
(5.2.3). Each claim is `∀ {V} [DecidableEq V] [Fintype V] {In} (c E rho),
premise → conclusion` (FG-SA claim shape), with a `_def` equation and no
proof. Stage 1: every claim takes `StageOneFrame` (CI item (vi) and the
formation premises (F6)/(F7) are vacuous). The fault bounds are as r4.3 §1.1
states them. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty awakeHonest)

/-- [PC-SA claims, W0; pcsa34-r4 1.4 (stamps), 3.3 (sources); plan §5 risk
"stamped < z"] The snapshot of `z_s` holds exactly the PCs held after the
ticks at `z_s`: the PCs accepted before the tick `z_s` (stamp `< z_s`). The
claim fixes the r4.3 stamp convention against the model's `pcSnapshotAt`.
No fault premise. -/
def PCSnapshotStampClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    Base₂ p c E rho →
    ∀ y ∈ rho.honest, ∀ s : Slot, SA.freezeTime p.toParams s ≤ rho.horizon →
      pcSnapshotAt (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)) s =
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs

theorem PCSnapshotStampClaim_def (p : Params) : PCSnapshotStampClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      Base₂ p c E rho →
      ∀ y ∈ rho.honest, ∀ s : Slot, SA.freezeTime p.toParams s ≤ rho.horizon →
        pcSnapshotAt (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)) s =
          (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) := by
  rw [PCSnapshotStampClaim]

section Invariant

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V] [Fintype V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA claims, W0; pcsa34-r4 5.2.2 CI(j), stage 1] The clean invariant at
label `j`, at every honest node and every time `t < v_{j+1}`. Item (vi) (the
frame) is stage 2 and is not a field. Results are the raw gate results
`R_x(i)` (`gateResultAt`); HEADs are the HEADs of honest awake voters.
- (i) `resultsChain`: honest results of labels `≤ j` are pairwise compatible,
  and a result of a later label extends every result of an earlier label
  (r4.3 (i) "D_{i+1} ⪰ D_i" with step (c) "results ⪰ D_{s−1}").
- (ii) `headsAbove`: every honest HEAD of label `i ≤ j` is `⪰` every honest
  result of label `i − 1`; `headsEqual`: at a label with an honest proposal
  `P` every honest HEAD is `P` (step (b)).
- (iii) `pcAck`: every held PC has an honest ack on its target (5.1);
  `pcChain`: held PC targets are pairwise compatible and rank order is prefix
  order (step (d)); `pcResults`: PC targets are compatible with every honest
  result (CL4).
- (iv) `leaseBelowResult`: every lease target is `⪯` an honest result;
  `leaseCompatible`: every live lease is compatible with every PC held at its
  node; `lockWriteAll`, `lockKeep`: L*′ skips or deletes none (no honest
  gate of a label `≤ j` skips a lock write on a block below its result, and
  no event before `v_{j+1}` removes a live lock at an honest node).
- (v) `recordOrigin`: every honest `S` is `F` or an own result of a label
  `≤ j`; `recordMono`, `recordCompatible`: `S` is monotone at a node and
  honest `S` values are pairwise compatible.
- (vii) `roots`: every honest root for `v_{j+1}` is compatible with every
  honest result of label `j` (r4.3a). Step (d) needs a separate proof of
  compatibility with an N target. The root is `Z`, a PC target or a lock
  target, by the definition of `live_root`. -/
structure CleanInvariantAt (j : Slot) : Prop where
  resultsChain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (i i' : Slot) (X Y : Block),
    i ≤ i' → i' ≤ j →
    gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
    (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y)
  headsAbove : ∀ (i : Slot) (x y : V) (H X : Block), 0 < i → i ≤ j →
    HonestHeadAt p c E rho x i H → y ∈ rho.honest →
    gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H
  headsEqual : ∀ (i : Slot) (P : Block) (x : V) (H : Block), i ≤ j →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho i P →
    HonestHeadAt p c E rho x i H → H = P
  pcAck : ∀ x ∈ rho.honest, ∀ (t : Time) (pc : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → pc ∈ (storeAt p c E rho x t).pcs →
    ∃ y, HonestAckAt p c E rho y pc.slot pc.target
  pcChain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time) (pc pc' : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → t' < SA.voteTime p.toParams (j + 1) →
    pc ∈ (storeAt p c E rho x t).pcs → pc' ∈ (storeAt p c E rho y t').pcs →
    Block.Compatible pc.target pc'.target ∧ (pc.slot < pc'.slot → Block.Preceq pc.target pc'.target)
  pcResults : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t : Time) (pc : PC p.n) (i : Slot)
    (X : Block), t < SA.voteTime p.toParams (j + 1) → pc ∈ (storeAt p c E rho x t).pcs →
    i ≤ j → gateResultAt p c E rho y i = some (some X) → Block.Compatible pc.target X
  leaseBelowResult : ∀ x ∈ rho.honest, ∀ (t : Time) row,
    t < SA.voteTime p.toParams (j + 1) → row ∈ (storeAt p c E rho x t).base.obligations →
    ∃ y ∈ rho.honest, ∃ (i : Slot) (X : Block), i ≤ j ∧
      gateResultAt p c E rho y i = some (some X) ∧ Block.Preceq row.1 X
  leaseCompatible : ∀ x ∈ rho.honest, ∀ (t : Time) (B : Block) (pc : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → LiveLease (storeAt p c E rho x t) B →
    pc ∈ (storeAt p c E rho x t).pcs → Block.Compatible B pc.target
  lockWriteAll : ∀ x ∈ rho.honest, ∀ (i : Slot) (st : State p.n) (X b : Block), i ≤ j →
    gateInAt p c E rho x i = some st → gateResultAt p c E rho x i = some (some X) →
    Block.Preceq b X → leaseWriteOK st.pcs (gateRank p st i) b = true
  lockKeep : ∀ x ∈ rho.honest, ∀ (i : Nat) e, rho.events[i]? = some e →
    e.time < SA.voteTime p.toParams (j + 1) →
    ∀ row ∈ (storeBefore p c E rho i x).base.obligations, e.time < row.2.2 →
      ∃ row' ∈ (storeBefore p c E rho (i + 1) x).base.obligations, row'.1 = row.1
  recordOrigin : ∀ x ∈ rho.honest, ∀ t : Time, t < SA.voteTime p.toParams (j + 1) →
    (storeAt p c E rho x t).base.stableRecord = eraseFG (storeAt p c E rho x t).fg.F ∨
      ∃ (i : Slot) (X : Block), i ≤ j ∧ gateResultAt p c E rho x i = some (some X) ∧
        (storeAt p c E rho x t).base.stableRecord = X
  recordMono : ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' → t' < SA.voteTime p.toParams (j + 1) →
    Block.Preceq (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho x t').base.stableRecord
  recordCompatible : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    t < SA.voteTime p.toParams (j + 1) → t' < SA.voteTime p.toParams (j + 1) →
    Block.Compatible (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho y t').base.stableRecord
  roots : ∀ x ∈ rho.honest, ∀ R : Block, liveRootAt p c E rho x (j + 1) = some R →
    ∀ y ∈ rho.honest, ∀ X, gateResultAt p c E rho y j = some (some X) →
      Block.Compatible R X

/-- [PC-SA claims, W0; pcsa34-r4 5.3 Claim] The formation conclusion at slot
`s` with the honest proposal `N` (`P = N.erase`): every honest HEAD at `v_s`
is `P`; `N_s(P) ≥ q_N` at every honest node at `e_s`; every honest node awake
at `e_s` acks `(s, P)`; `PC(s, P)` is stamped before `z_s` at every honest
node; if also `a < h_s`, every honest result at `d_s` is `P`. -/
def FormationConcl (s : Slot) (N : NamedProposal p.n) : Prop :=
  (∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
  (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
    holdsN p (actView nd.st) s N.erase = true) ∧
  (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
    HonestAckAt p c E rho y s N.erase) ∧
  (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) ∧
  ((faulty rho).card < (awakeHonestLabel p c E rho s).card →
    ∀ y ∈ rho.honest, gateResultAt p c E rho y s = some (some N.erase))

theorem FormationConcl_def (s : Slot) (N : NamedProposal p.n) :
    FormationConcl p c E rho s N =
      ((∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
      (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
        holdsN p (actView nd.st) s N.erase = true) ∧
      (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
        HonestAckAt p c E rho y s N.erase) ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) ∧
      ((faulty rho).card < (awakeHonestLabel p c E rho s).card →
        ∀ y ∈ rho.honest, gateResultAt p c E rho y s = some (some N.erase))) := rfl

end Invariant

/-- [PC-SA claims, W0; pcsa34-r4 5.2.2 (CI), stage 1; plan C6] The joint clean
induction: in a run with a healthy prefix up to `b₀` (CLEAN(b₀), `Clean₂`:
strict delivery within `Δ`, rows `Δ_F`, `a < h_j` at every label with
`e_j ≤ b₀`), `a < ⌈n/2⌉` (CL4 and
[pc-trumps §2] need `2q_N > n + a`) and the stage-1 frame, CI(j) holds for
every label `j` whose gate `d_j` is in the prefix. -/
def CleanInvariantClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ j : Slot, SA.gateTime p.toParams j ≤ b₀ → CleanInvariantAt p c E rho j

theorem CleanInvariantClaim_def (p : Params) : CleanInvariantClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ j : Slot, SA.gateTime p.toParams j ≤ b₀ → CleanInvariantAt p c E rho j) := by
  rw [CleanInvariantClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.3, PROVED under (F1)–(F7), a ≤ ⌊n/4⌋;
plan C7] Formation at a slot with an honest awake proposer: under the
premises (F1)–(F7) (`FormationPrem`, stage 1) the formation conclusion holds.
No CI premise: r4.3 discharges (F3), (F4) from CI in a clean run and from 5.6
in recovery. -/
def FormationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (s : Slot) (N : NamedProposal p.n)
    (ΔF : Time),
    FormationPrem p c E rho s N ΔF → FormationConcl p c E rho s N

theorem FormationClaim_def (p : Params) : FormationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (s : Slot) (N : NamedProposal p.n)
      (ΔF : Time),
      FormationPrem p c E rho s N ΔF → FormationConcl p c E rho s N) := by
  rw [FormationClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Dissemination, stage 1; plan C14] An
honest ack `(s, B)` at `e_s` in a clean prefix gives every honest HEAD at
`v_{s+1}` `⪰ B` and every honest result at `d_{s+1}` `⪰ B`. Premises: CLEAN
up to `d_{s+1}`, `a < ⌈n/2⌉` ([pc-trumps §2]), stage-1 frame. -/
def CleanDisseminationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (s : Slot) (y : V) (B : Block), SA.gateTime p.toParams (s + 1) ≤ b₀ →
      HonestAckAt p c E rho y s B →
      (∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
      (∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x (s + 1) = some (some X) →
        Block.Preceq B X)

theorem CleanDisseminationClaim_def (p : Params) : CleanDisseminationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (s : Slot) (y : V) (B : Block), SA.gateTime p.toParams (s + 1) ≤ b₀ →
        HonestAckAt p c E rho y s B →
        (∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
        (∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x (s + 1) = some (some X) →
          Block.Preceq B X)) := by
  rw [CleanDisseminationClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Clean safety, stage 1; plan C14] In a
clean prefix the honest available and strong reads are pairwise compatible
(across nodes and times) and monotone at each node (contract confirmedSafe,
stableSafe, monotone; nesting is `OutputNestingClaim`). Premises: CLEAN(b₀),
`a < ⌈n/2⌉`, stage-1 frame (r4.3: "PROVED modulo (vi) HAND for stage 2;
stage 1 has no (vi)"). -/
def PCSACleanSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time, 0 ≤ t → t ≤ b₀ → 0 ≤ t' → t' ≤ b₀ →
      Block.Compatible (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho y t')) ∧
      Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
      (t ≤ t' →
        Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
        Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t')))

theorem PCSACleanSafetyClaim_def (p : Params) : PCSACleanSafetyClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
        0 ≤ t → t ≤ b₀ → 0 ≤ t' → t' ≤ b₀ →
        Block.Compatible (confirmed (storeAt p c E rho x t))
          (confirmed (storeAt p c E rho y t')) ∧
        Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
        (t ≤ t' →
          Block.Preceq (confirmed (storeAt p c E rho x t))
            (confirmed (storeAt p c E rho x t')) ∧
          Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t')))) := by
  rw [PCSACleanSafetyClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Inclusion, D_c = 6Δ, stage 1; plan
C14] The honest proposal `P` of slot `u` (honest awake proposer) is below
every honest available read from the gate `d_u = t_u + 6Δ` to the end of the
clean prefix. Premises: CLEAN(b₀) with `d_u ≤ b₀`, `a < ⌈n/2⌉`, stage-1
frame. No `q_N` premise: inclusion in `S` needs `a < h_u` only. -/
def PCSACleanInclusionClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (u : Slot) (P : Block),
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u P →
      ∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ b₀ →
        Block.Preceq P (confirmed (storeAt p c E rho x t))

theorem PCSACleanInclusionClaim_def (p : Params) : PCSACleanInclusionClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (u : Slot) (P : Block),
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u P →
        ∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ b₀ →
          Block.Preceq P (confirmed (storeAt p c E rho x t))) := by
  rw [PCSACleanInclusionClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Strong inclusion (3Δ), stage 1;
App. B strongIncluded; plan C9] In a CLEAN(b₀) run (`Clean₂`) with the PC
fault cap `a ≤ ⌊n/4⌋` and the stage-1 frame, the honest proposal `P` of a
slot `u` with `h_u ≥ q_N` (5.3 at `u`) is below every honest strong read from
`z_u = t_u + 3Δ` to the cut. Later PCs extend `P` (CI (iii), rank = prefix).
The participation premise is only `h_u ≥ q_N` at the slot (5.2.3). The
generic `PCIncludedStatement` form (`IncludedFrom` over the whole run) needs
this premise at every honest slot; the stage-2 form is
`StrongIncludedStageTwoClaim`. -/
def StrongIncludedClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → StageOneFrame p c E rho →
    ∀ (u : Slot) (P : Block),
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u P →
      nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card →
      ∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ b₀ →
        Block.Preceq P (strong (storeAt p c E rho x t))

theorem StrongIncludedClaim_def (p : Params) : StrongIncludedClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → StageOneFrame p c E rho →
      ∀ (u : Slot) (P : Block),
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u P →
        nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card →
        ∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ b₀ →
          Block.Preceq P (strong (storeAt p c E rho x t))) := by
  rw [StrongIncludedClaim]

/-! ### Pending-label claims

CI and `CleanDisseminationClaim` reach the labels whose gate is in the clean
prefix (`d_j ≤ b₀`). ARM-healthy (5.4.2 (b)) and slow P1 (5.5 steps 1–2)
also read the pending labels: the labels whose votes or early reads are in
the prefix and whose gate is after `b₀`. The claims below state these facts
additively. They are not fields of `PCSAClaims`. The HEAD facts at the
pending labels (5.2.2 (ii) with `v_i ≤ b₀`, and past the cut with
`e_{i−1} ≤ b₀`) are not claims: as stated, they are false in the boundary
case `v_r ≤ b₀ < d_{r−1}` of 5.5 step 2. The Outage assembly builds the
`CutChain` and `CutFacts` records from these claims and the Clean HEAD cone
theorems. -/

/-- [PC-SA claims; pcsa34-r4.3 5.2.2 (c), 5.4.2 (b), 5.5 steps 1–2; FG-SA
`hnonempty` (outage supplier history)] In a clean prefix, every honest result
of a label `i` with `e_i ≤ b₀` is not empty (5.2.2 (c): `2h > h + a ≥` the
early voters). -/
def CleanResultsNonemptyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ i : Slot, SA.earlyTime p.toParams i ≤ b₀ → ∀ x ∈ rho.honest,
      gateResultAt p c E rho x i ≠ some none

theorem CleanResultsNonemptyClaim_def (p : Params) : CleanResultsNonemptyClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ i : Slot, SA.earlyTime p.toParams i ≤ b₀ → ∀ x ∈ rho.honest,
        gateResultAt p c E rho x i ≠ some none) := by
  rw [CleanResultsNonemptyClaim]

/-- [PC-SA claims; pcsa34-r4.3 5.2.2 (i), 5.5 step 1; CI `resultsChain` at the
pending labels; FG-SA outage supplier history (scope `timeIdx b₀`)] In a clean
prefix, an honest result of a label `i'` with `e_{i'} ≤ b₀` extends every
honest result of an earlier label. -/
def CleanResultsChainPendingClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (i i' : Slot) (x y : V) (X Y : Block), i < i' → SA.earlyTime p.toParams i' ≤ b₀ →
      x ∈ rho.honest → y ∈ rho.honest →
      gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
      Block.Preceq X Y

theorem CleanResultsChainPendingClaim_def (p : Params) : CleanResultsChainPendingClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (i i' : Slot) (x y : V) (X Y : Block), i < i' → SA.earlyTime p.toParams i' ≤ b₀ →
        x ∈ rho.honest → y ∈ rho.honest →
        gateResultAt p c E rho x i = some (some X) →
        gateResultAt p c E rho y i' = some (some Y) → Block.Preceq X Y) := by
  rw [CleanResultsChainPendingClaim]

/-- [PC-SA claims; pcsa34-r4.3 5.2.3 Dissemination, 5.2.2 (d), 5.4.2 (b), 5.5
step 1; `CleanDisseminationClaim` at the pending label] An honest ack `(s, B)`
in a clean prefix gives every honest HEAD of label `s + 1` `⪰ B` when
`v_{s+1} ≤ b₀`, and every honest result of label `s + 1` `⪰ B` when
`e_{s+1} ≤ b₀`. -/
def CleanDisseminationPendingClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (s : Slot) (y : V) (B : Block), HonestAckAt p c E rho y s B →
      (SA.voteTime p.toParams (s + 1) ≤ b₀ →
        ∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
      (SA.earlyTime p.toParams (s + 1) ≤ b₀ → ∀ x ∈ rho.honest, ∀ X,
        gateResultAt p c E rho x (s + 1) = some (some X) → Block.Preceq B X)

theorem CleanDisseminationPendingClaim_def (p : Params) : CleanDisseminationPendingClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (s : Slot) (y : V) (B : Block), HonestAckAt p c E rho y s B →
        (SA.voteTime p.toParams (s + 1) ≤ b₀ →
          ∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
        (SA.earlyTime p.toParams (s + 1) ≤ b₀ → ∀ x ∈ rho.honest, ∀ X,
          gateResultAt p c E rho x (s + 1) = some (some X) → Block.Preceq B X)) := by
  rw [CleanDisseminationPendingClaim]

/-- [PC-SA claims; pcsa34-r4.3 5.2.3 (strict receipt), 5.4.2 ARM-healthy (a);
FG-SA `fgsa_proposal_receipt` (AvailableChainFGSARun Proofs/Receipts)] In a
clean prefix, a block stored by an honest node at `T ≥ 0` with `T + Δ ≤ b₀` is
stored by every honest node after the ticks of every time `≥ T + Δ` (strict
proposal receipt within `Δ`, stage-1 store monotonicity). The relay of a held
PC reads it for the PC target. -/
def CleanBlockReceiptClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ v ∈ rho.honest, ∀ (T : Time) (B : Block), 0 ≤ T → T + E.Δ ≤ b₀ →
      B ∈ (storeAt p c E rho v T).base.blocks → ∀ y ∈ rho.honest, ∀ t : Time,
        T + E.Δ ≤ t → B ∈ (storeAfterTicks p c E rho y t).base.blocks

theorem CleanBlockReceiptClaim_def (p : Params) : CleanBlockReceiptClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ v ∈ rho.honest, ∀ (T : Time) (B : Block), 0 ≤ T → T + E.Δ ≤ b₀ →
        B ∈ (storeAt p c E rho v T).base.blocks → ∀ y ∈ rho.honest, ∀ t : Time,
          T + E.Δ ≤ t → B ∈ (storeAfterTicks p c E rho y t).base.blocks) := by
  rw [CleanBlockReceiptClaim]

end AvailableChain.PCSA.Run

end
