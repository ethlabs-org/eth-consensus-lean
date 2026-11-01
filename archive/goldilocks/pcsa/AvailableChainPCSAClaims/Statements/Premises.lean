module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSAClaims.Statements.Regimes

@[expose] public section

/-! [PC-SA claims, W0] Premise packages that more than one lane reads: the
formation premises (F1)–(F7) of pcsa34-r4 5.3 (Clean formation and Finality
source transfer) and the arming premise ARM(s, B, j₀) of 5.0/5.4 with its
conclusion (Outage persistence and the stage-2 stub), and the Q0-PC premise
package of q0-pc.md §2 with its conclusion (Finality). Statements only. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty awakeHonest)

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V] [Fintype V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA claims, W0; pcsa34-r4 1.4] A wire object that is not an FG row
(HEAD, proposal, ack, PC). These objects have delay `Δ`; rows have `Δ_F`. -/
def IsNonRow {p : Params} (o : Obj p) : Prop :=
  match o.payload with
  | .row _ => False
  | _ => True

theorem pcsa_IsNonRow_def {p : Params} (o : Obj p) :
    IsNonRow o = (match o.payload with | .row _ => False | _ => True) := rfl

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 3.10, 5.3] The honest proposal of slot `s`
is the named proposal `N`: the proposer of `s` is honest and emits `N` at
`t_s` (so it is awake then). `N.erase` is `P`, `N.pc` the carried PC. -/
def HonestNamedProposal (s : Slot) (N : NamedProposal p.n) : Prop :=
  V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s ∈ rho.honest ∧
    V2.D.Run.emits E rho (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      ⟨.seat ((pcsaInterface p c (m := m)).propLabel s)
        (V2.D.propSeat (pcsaInterface p c (m := m)).toInterface s), .proposal N⟩
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)

omit [Fintype V] in
theorem pcsa_HonestNamedProposal_def (s : Slot) (N : NamedProposal p.n) :
    HonestNamedProposal p c E rho s N =
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s ∈ rho.honest ∧
        V2.D.Run.emits E rho (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
          ⟨.seat ((pcsaInterface p c (m := m)).propLabel s)
            (V2.D.propSeat (pcsaInterface p c (m := m)).toInterface s), .proposal N⟩
          (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)) := rfl

/-- [pcsa34-r4.3b 5.3, F4 first clause] The walk from the common base
root reaches the proposer's live root at the proposal read. -/
def FormationRootReachable (s : Slot) : Prop :=
  ∀ nd₀, pcsa_postClock E rho
      (V2.D.proposerOf rho
        (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime
        (pcsaInterface p c (m := m)).toInterface s) = some nd₀ →
    let st := nd₀.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD
      (eraseFG (controls p st).Z)
    let raw := proposerVotes st s
    let support := proposerSupport st s
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks raw support)
        (eligible p st raw support))

/-- [PC-SA claims, W0; pcsa34-r4 5.3 premises (F1)–(F7)] The formation
premises at slot `s` with the honest proposal `N` (`P = N.erase`), stage 1.
- (F1) `delivery`: every non-row object sent or accepted at `t` reaches every
  honest node before `max t z_{s−1} + Δ` (r4.3: "within Δ, strict (so
  z_{s−1} ≥ t_GST)"; an object of an earlier time is held by `t_s`), up to `d_s`.
- (F2) `participation`: `h_s ≥ q_N` honest nodes awake at `v_s` and `e_s`.
- (F3) `commonView`: every honest voter's `view(s)` has the target of the
  carried PC `N.pc` (both `⊥` when `N.pc = ⊥`).
- (F4) first clause, `proposerRootReachable`: the base-root walk reaches
  the proposer's live root at `t_s`.
- (F4) second clause, `leases`: every live lock at the post-clock honest
  voter read that is deeper than the view target (or `Z` without a view)
  and compatible with it is `⪯ parent(P)`.
- (F5) is not a field: r4.3 derives it from (F1) (p accepted the visited
  blocks before `t_s`, so they reach every voter before `v_s`).
- (F6), (F7) `frame`: stage 1, vacuous (`StageOneFrame`).
The fault cap is `a ≤ ⌊n/4⌋` (r4.3 §1.1, 5.3). -/
structure FormationPrem (s : Slot) (N : NamedProposal p.n) (ΔF : Time) : Prop where
  base : Base₂ p c E rho
  quarterCap : QuarterCap p c rho
  frame : StageOneFrame p c E rho
  slotPos : 0 < s
  horizon : SA.gateTime p.toParams s ≤ rho.horizon
  deltaF : E.Δ ≤ ΔF
  proposal : HonestNamedProposal p c E rho s N
  delivery : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
    (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) (SA.gateTime p.toParams s)
  participation : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card
  commonView : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target)
  proposerRootReachable : FormationRootReachable p c E rho s
  leases : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
    ∀ B, LiveLease nd.st B →
      Block.Compatible B ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)) →
      ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)).depth < B.depth →
      Block.Preceq B N.erase.parent

/-- [PC-SA claims, W0; pcsa34-r4 5.0, 5.4.1 ARM(s, B, j₀)] (a) `PC(s, B)` is
stamped before `z_{j₀−1}` at every honest node; (b) every honest ack of a slot
in `[s + 1, j₀)` has a target `⪰ B`. Delivery after `v_{j₀}` is arbitrary. -/
structure Arm (s : Slot) (B : Block) (j₀ : Slot) : Prop where
  stamped : ∀ y ∈ rho.honest,
    PCStampedBefore p c E rho y (SA.freezeTime p.toParams (j₀ - 1)) s B
  acks : ∀ y s' X, s + 1 ≤ s' → s' < j₀ → HonestAckAt p c E rho y s' X → Block.Preceq B X

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 Theorem] The persistence conclusion:
every honest HEAD at `v_j` (`j ≥ j₀`) is `⪰ B`; every honest ack of a slot
`≥ j₀` (hence every PC of that slot, 5.1) has a target `⪰ B`; from the time an
honest node holds `PC(s, B)`, its strong and available outputs are `⪰ B`. -/
def ArmConcl (s : Slot) (B : Block) (j₀ : Slot) : Prop :=
  (∀ j x H, j₀ ≤ j → HonestHeadAt p c E rho x j H → Block.Preceq B H) ∧
  (∀ j x X, j₀ ≤ j → HonestAckAt p c E rho x j X → Block.Preceq B X) ∧
  (∀ w ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
    (∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = s ∧ pc.target = B) →
    Block.Preceq B (strong (storeAt p c E rho w t')) ∧
      Block.Preceq B (confirmed (storeAt p c E rho w t')))

omit [Fintype V] in
theorem pcsa_ArmConcl_def (s : Slot) (B : Block) (j₀ : Slot) :
    ArmConcl p c E rho s B j₀ =
      ((∀ j x H, j₀ ≤ j → HonestHeadAt p c E rho x j H → Block.Preceq B H) ∧
      (∀ j x X, j₀ ≤ j → HonestAckAt p c E rho x j X → Block.Preceq B X) ∧
      (∀ w ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
        (∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = s ∧ pc.target = B) →
        Block.Preceq B (strong (storeAt p c E rho w t')) ∧
          Block.Preceq B (confirmed (storeAt p c E rho w t')))) := rfl

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 5.8.3; q0-pc.md §2 Statement] The Q0-PC
conclusion at the action `a_r` of round `r`, for the honest proposal `D` of
slot `cD` with FG block `Dfg`: every honest node has a source `T ⪰ D` with
`slot(T) ∈ [cD, rR]`; if also the causal cap is `H ≤ y` (`y = ht(D)`) through
`a_r`, every honest source has height `y` and the entry of `D`. -/
def Q0PCConcl (r : Nat) (cD : Slot) (D : Block) (Dfg : FGBlock (Fin p.n)) : Prop :=
  (∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
    actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
      cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
  (HonestStatesThrough p c E rho (p.actionTime r)
      (fun st => st.fg.h_max ≤ (FGSA.heightView p Dfg).h) →
    ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧
        (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
        (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)

omit [Fintype V] in
theorem pcsa_Q0PCConcl_def (r : Nat) (cD : Slot) (D : Block) (Dfg : FGBlock (Fin p.n)) :
    Q0PCConcl p c E rho r cD D Dfg =
      ((∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
          cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
      (HonestStatesThrough p c E rho (p.actionTime r)
          (fun st => st.fg.h_max ≤ (FGSA.heightView p Dfg).h) →
        ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
          actionSourceAt p c E rho x r = some (some C) ∧
            (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
            (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)) := rfl

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 5.8.3; q0-pc.md §2 Statement and "Exact
premise list"; fg-port-r8-gaps.md §6] The Q0-PC premise package at round `r`
for the honest proposal `D` (FG block `Dfg`, height `y = ht(D)`) of slot `cD`,
with the reset time `t*` and the heights `M` and `μ`. The PC-SA producers of
the package are OPEN (q0-pc.md §2: "the full PC-SA package is OPEN"):
`healing` is HEALING_INPUT(t*) (H3 and L-PC1; [FG-HEAL] 21 H.22),
`h2'` is H2′, `muBound` is H.11/H0, `ff2` is FF2, `ff2C` is FF2-C, and
`transfer` is the source-transfer premise with the retained-side choice of
(1c) (H.13-PC′, OPEN). The causal cap `H ≤ y + 1` and `F ⪯ D` are
hypotheses of the statement.
- `proposal`, `afterReset`: `D` is the honest proposal of slot `cD`, after `t*`.
- `lift`, `high`, `liftHeld`: `Dfg` erases to `D`, `ht(D) ≥ M + 1`, and every
  honest node holds `Dfg` at `a_r`.
- `window`: `cD ≤ rR < cD + R`; `horizon`: `a_r` is in the run.
- `healing`: at every honest proposal `P` of a slot `u` with `t_u ≥ t*`, every
  honest HEAD at `v_u` is `P` (H3) and `PC(u, P)` is stamped before `z_u` at
  every honest node (L-PC1).
- `h2'`: every honest HEAD of a label in `(cD, rR]` covers `D`.
- `fCover`: `F ⪯ D` at every honest event state through `a_r` (1b).
- `cap`: `H ≤ y + 1` at every honest event state through `a_r`.
- `muBound`: `μ ≤ M`, and every honest source whose PC label votes before
  `t_GST` has height `≤ μ`.
- `ff2` (blueprint 22 FF2, entry and certificate identity only): at a height
  `h ≥ M + 1` with an honest source `C` (action through `a_r`), every honest
  source of height `h` has the entry `E_h = T_h(C)`, and every justification
  of height `h` held at an honest event state through `a_r` names `E_h`.
  Other held blocks of height `h` are not constrained: two carriers can reuse
  one lower-height quorum and both stay in the tree. `HeldJustification` is
  the justification part of FF2 only; FF2's honest-record clause (target,
  timeout, lock) and its target, progress and finality QCs are not stated
  (step (1c) uses the justification part, `transfer` and the equal-height
  entry fact I2).
- `ff2C`: a contested frame has `H ≤ M + 1` (honest event states through `a_r`).
- `transfer`: every justification `J` at height `y` held at an honest event
  state through `a_r` has an honest row source `S ⪰ J` of height `y`, sent
  at an action through `a_r`, that is compatible with `D` (the retained-side
  source of (1c)). -/
structure Q0PCPackage (tStar : Time) (M μ r : Nat) (cD : Slot) (D : Block)
    (Dfg : FGBlock (Fin p.n)) : Prop where
  proposal : Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho cD D
  afterReset : tStar ≤ V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface cD
  lift : eraseFG Dfg = D
  high : M + 1 ≤ (FGSA.heightView p Dfg).h
  liftHeld : ∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
    Dfg ∈ nd.st.fg.TF
  window : cD ≤ r * p.R ∧ r * p.R < cD + p.R
  horizon : p.actionTime r ≤ rho.horizon
  healing : ∀ (u : Slot) (P : Block),
    tStar ≤ V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface u →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u P →
    (∀ x H, HonestHeadAt p c E rho x u H → H = P) ∧
      ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams u) u P
  h2' : ∀ (s' : Slot) (x : V) (H : Block), cD < s' → s' ≤ r * p.R →
    HonestHeadAt p c E rho x s' H → Block.Preceq D H
  fCover : HonestStatesThrough p c E rho (p.actionTime r)
    (fun st => Block.Preceq (eraseFG st.fg.F) D)
  cap : HonestStatesThrough p c E rho (p.actionTime r)
    (fun st => st.fg.h_max ≤ (FGSA.heightView p Dfg).h + 1)
  muBound : μ ≤ M ∧ ∀ x ∈ rho.honest, ∀ (r' : Nat) (C : FGBlock (Fin p.n)),
    actionSourceAt p c E rho x r' = some (some C) →
    SA.voteTime p.toParams (eraseFG C).slot < E.t_GST → (FGSA.heightView p C).h ≤ μ
  ff2 : ∀ x ∈ rho.honest, ∀ (r₁ : Nat) (C : FGBlock (Fin p.n)), r₁ ≤ r →
    actionSourceAt p c E rho x r₁ = some (some C) → M + 1 ≤ (FGSA.heightView p C).h →
    (∀ x' ∈ rho.honest, ∀ (r₂ : Nat) (C' : FGBlock (Fin p.n)), r₂ ≤ r →
      actionSourceAt p c E rho x' r₂ = some (some C') →
      (FGSA.heightView p C').h = (FGSA.heightView p C).h →
      (FGSA.heightView p C').T_h = (FGSA.heightView p C).T_h) ∧
    HonestStatesThrough p c E rho (p.actionTime r) (fun st =>
      ∀ X, HeldJustification p st (FGSA.heightView p C).h X →
        X = (FGSA.heightView p C).T_h)
  ff2C : HonestStatesThrough p c E rho (p.actionTime r)
    (fun st => (controls p st).contest = true → st.fg.h_max ≤ M + 1)
  transfer : HonestStatesThrough p c E rho (p.actionTime r) (fun st =>
    ∀ J, HeldJustification p st (FGSA.heightView p Dfg).h J →
      ∃ x ∈ rho.honest, ∃ (r' : Nat) (S : FGBlock (Fin p.n)), r' ≤ r ∧
        actionSourceAt p c E rho x r' = some (some S) ∧
        (FGSA.heightView p S).h = (FGSA.heightView p Dfg).h ∧
        FGBlock.Preceq J S ∧ Block.Compatible (eraseFG S) D)

omit [Fintype V] in
/-- [PC-SA claims; pcsa34-r4 5.7 Claim (honest opening), healed suffix; 5.3
(F1)–(F7)] The premises of source transfer at the opening `rR = r·R` after
the healing time, with every frame item explicit (no `StageOneFrame`).
- `recovery`: RECOVERY (`Recovery₂`: delivery within `Δ` after `t_GST`,
  every honest node awake, `a ≤ ⌊n/4⌋`); `proposal`: the honest awake proposer
  of `rR` sends `N` (`P = N.erase`); `horizon`: `a_r ≤` horizon.
- `afterGST` (timing): `t_GST + Δ ≤ t_{rR}`, so `z_{rR−1} ≥ t_GST` and (F1)
  follows from `recovery`.
- `participation` (F2): `h_{rR} ≥ q_N`.
- `commonView` (F3): the formation common view at `rR`.
- `proposerRootReachable` (F4 first clause): the base-root walk reaches
  the proposer's live root at `t_{rR}`.
- `locks` (F4 second clause): the post-clock voter lock upper bound, as in
  `FormationPrem`. After `t*` their producers are the HEALING_INPUT items
  H2/H3 of [FG-HEAL] (OPEN).
- `equalFrames` (F6): every honest voter awake at `v_{rR}` reads the
  proposer's frame (`Z`, `lo`) at `t_{rR}`.
- `fCompat` (F7): at every honest node at `e_{rR}`, `F` is compatible with `P`.
- `frameActive` (5.7): `PC(rR, P)` is frame-active at every honest node at
  `a_r`. -/
structure HealedSourcePrem (G ΔF : Time) (r : Nat) (N : NamedProposal p.n) : Prop where
  recovery : Recovery₂ p c E rho G ΔF
  proposal : HonestNamedProposal p c E rho (r * p.R) N
  horizon : p.actionTime r ≤ rho.horizon
  afterGST : E.t_GST + E.Δ ≤
    V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface (r * p.R)
  participation : nQuorum p.n ≤ (awakeHonestLabel p c E rho (r * p.R)).card
  commonView : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams (r * p.R)) = true →
    (viewAt p c E rho y (r * p.R)).map (Option.map PC.target) = some (N.pc.map PC.target)
  proposerRootReachable : FormationRootReachable p c E rho (r * p.R)
  locks : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams (r * p.R)) = true →
    ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams (r * p.R)) = some nd →
    ∀ B, LiveLease nd.st B →
      Block.Compatible B ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)) →
      ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)).depth < B.depth →
      Block.Preceq B N.erase.parent
  equalFrames : ∀ nd₀, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface (r * p.R))
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface (r * p.R)) = some nd₀ →
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams (r * p.R)) = true →
    ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams (r * p.R)) = some nd →
      (controls p nd.st).Z = (controls p nd₀.st).Z ∧
        (controls p nd.st).lo = (controls p nd₀.st).lo
  fCompat : ∀ y ∈ rho.honest,
    ∀ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams (r * p.R)) = some nd →
      Block.Compatible (eraseFG nd.st.fg.F) N.erase
  frameActive : ∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
    ∃ B ∈ fullTree p nd.st, eraseFG B = N.erase

end AvailableChain.PCSA.Run

end
