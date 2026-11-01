# Open inputs of the Recovery lane (C11)

`pcsa_fastRecoveredClaim` and `pcsa_longBreakRecoveredClaim` in
`Assembly/Recovery.lean` are unconditional. Each takes only `(p : Params)`.
`Recovery/Export.lean` retains the conditional interfaces as
`pcsa_fastRecoveredClaim_of_inputs` and `pcsa_longBreakRecoveredClaim_of_inputs`,
with unchanged types. No recovery suffix supplier remains OPEN.
Status of the inputs:

- First slot (`firstSlot`: a `FormationPrem` at `s₁` with the corrected F4
  clause `RecoveryRootReachable`):
  - F3, the common view at `v_{s₁}`: CLOSED by `recovery_commonView`
    (`Recovery/View.lean`, from the Shared `pcsa_commonView_of_delivery`).
  - Short break: CLOSED by `pcsa_recovery_firstSlot_short`
    (`Assembly/Recovery.lean`). It supplies `FormationPrem` and the separate
    `RecoveryRootReachable` predicate from `ShortBreakPrem`.
  - Long break: PROVED from the long claim premises by
    `pcsa_recovery_firstSlot_long_of_run` (`Assembly/Recovery.lean`). All seven
    transport suppliers are proved. No OPEN transport premise remains.
    The earlier explicit-supplier wrappers are retained. The final assembly
    keeps `hafter` from `long_recovery_slot` and uses the specified-slot
    supplier. The long first-slot proof is unchanged.
- Formation with corrected F4 (`formation`: every honest node holds the
  stamped PC of `N.erase` before `z_{s₁}`): its producer is now on main as
  `pcsa_formationClaim`. `FormationPrem` carries `proposerRootReachable`.
  `pcsa_formation_concl_of_premise` exports the conclusion through Clean.
- Persistence (`persistence`, ARM at `s₁` with `j₀ = s₁ + 1`): CLOSED by
  `recovery_persistence_of_run` (`Assembly/Recovery.lean`), from the
  unconditional C8 `pcsa_armPersistence`.
- Clean-anchor inputs: `recovery_cleanSaved_of_ci` and
  `recovery_cleanSaved_of_ci_pc` (`Assembly/Recovery.lean`) take CI at the
  anchor `cA` and the anchor gate result or stamped PC. The short-break
  producers are now CLOSED: `pcsa_recovery_cleanSaved_from_anchor` bounds
  saved results from `Clean₂` at the anchor freeze; and
  `pcsa_recovery_anchor_from_shortBreak` supplies the honest proposal,
  common stamp, ARM, and its conclusion. Both are in `Assembly/Recovery.lean`.
  `ShortBreakPrem.anchorPos` (`0 < cA`) leaves the genesis-anchor case to
  `LongBreakRecoveredClaim`.
- CI restart (`ciRestart`: the restarted chain invariant from `d_{s₁}`):
  CLOSED by `pcsa_recovery_chainRestart` in Assembly. Formation supplies the
  seed. RECOVERY supplies the window through the horizon. `Clean/RestartStamp`
  and C8 supply strong inclusion for each later honest proposal.

Block admission under RECOVERY at a slot `s > 0` with `t_GST + Δ ≤ t_s` and
`d_s` in the run is CLOSED:

- (B1) `recovery_installed_target_body`: the target of a PC held by an
  honest node before `z_{s-1}` is stored at every honest node before `t_s`.
- (B2) `pcsa_honest_proposal_from_vote` (proposal wire and valid PC target)
  and `pcsa_honest_proposal_body_from_vote` (the body `N.erase`), at every
  honest read in `[v_s, d_s]`.

## Long-break lock history progress

`Recovery/LockRank.lean` proves `recovery_live_lock_rank_compatible` from
store reachability. Every held PC at or above a live lock's rank has a
compatible target.

`Recovery/LockHistory.lean` proves `recovery_lock_write_witness` from a
stored row and the schedule. It derives an actual fresh gate, the current
result, the preceding saved window, the checked write rank, and an
uninterrupted interval of that exact row and rank. It proves the deadline
equality `row.2.2 = SA.gateTime p.toParams s + pcsaL p`.
`recovery_live_lock_last_write` derives this witness at the actual post-clock
read index.

The witness also exposes every saved result in the full k-window. The exact
row and rank remain present at every event state after the selected gate.
`recovery_lock_no_later_successful_renewal` excludes every later successful
renewal in this interval. It uses the actual fresh-gate and slow-write tests.
The witness is not a claim premise. Later modules use it to prove surviving
HEAD coverage and both long-slot F4 clauses.

Step 2 is implemented as the lane-neutral `RecoveryLockTransport` structure
and the Assembly constructor `pcsa_recovery_lock_transport`. The constructor
retains seven named supplier parameters. The new constructor
`pcsa_recovery_lock_transport_of_run` supplies all seven from the run.
The Clean `_win` exports use strict synchrony after GST.
`OPEN_sameLabel` includes label `g`, also when `t_g < GST ≤ v_g`.
The other fields are `OPEN_earlyForward`, `OPEN_voterBackward`,
`OPEN_pcReceipt`, `OPEN_honestVoterInputs`, `OPEN_honestProposerInputs`, and
`OPEN_rootResolution`. The structure and the constructor state each field in
full. They do not assume lock coverage, root compatibility, or walk dominance.

Step 3 is proved. `Recovery/LockOverlap.lean` proves:

- A live write after the mix has a window wholly at labels at least `g`.
- Two coexisting live deadlines force their saved windows to overlap.
- A live lock at `v_(j+1)` has a write label in the pending write's window.
- The same-label transport field excludes conflicting window prefixes.
- All live locks at the first HEAD are compatible with the pending target.
- All live locks after the write are compatible while its deadline is live.
- Post-mix live locks at different honest nodes are compatible.
- A conflicting PC at or above the saved rank blocks the write when relayed
  from `v_(j+1)` before `d_j`. At later reads it cannot coexist with the
  exact row if the receipt deadline is inside the surviving interval.

`Recovery/LockRank.lean` also proves the stored-row rank invariant and
extracts an active, early-stamped PC witness of a nonempty gate rank.
`Recovery/LockStamp.lean` now derives the held key before `e_j` from the
actual stamp history. `recovery_gate_rank_disseminated` relays the same rank
before `z_j`. `Recovery/LockView.lean` retains that PC in each later frozen
view and proves `recovery_voter_rank_bound`. The selected view's key is held
before `v_r`, including when a proposal carries it.
`recovery_write_voter_compatible` and `recovery_survivor_voter_compatible`
close K without an assumed rank lower bound. The survival theorem retains
the exact receipt-index bounds for `v_r + Δ = e_r`. It does not assert
receipt before an arbitrary faulty-slot HEAD.

Steps 4–5 are now proved. `LockFollow` derives F′ from the last write and
exact-row survival. `ProposalPaths` uses the actual preceding HEAD batch
at proposal time and proves both F4 bodies. `LongFirstSlot` constructs
`FormationPrem` with the explicit root-walk conjunct. Step 6 now converts
that conjunct with the appended `RecoveryRootReachable_def` equation.
The exact export and `pcsa_recovery_firstSlot_long` wrapper are proved.
The equation changes no claim premise. See the continuation 4 section.

## Continuation transport statements

The exact OPEN parameter names in `Assembly/Recovery.lean` are `OPEN_`
followed by each field name below. The intended supplier premises are
`Recovery₂ p c E rho G ΔF`, `StageOneFrame p c E rho`, and
`E.t_GST ≤ SA.voteTime p.toParams g`. There is no `GST ≤ t_g` premise.
No existing Clean export on this branch supplies these statements from
those recovery premises. The Assembly constructor takes them explicitly.

```lean
structure RecoveryLockTransport (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (g : Slot) : Prop where
  sameLabel : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y
  earlyForward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ GridCO.earlyVotes p.toParams.engine (actView src.st) r,
      ∀ i, GridCO.headSeat? o = some i → ∀ H,
        GridCO.resolvedHead? (actView src.st) o = some H →
        ((o ∈ headSupport p dst.st (r + 1) ∧
          GridCO.resolvedHead? dst.st.base o = some H ∧
          GridCO.stampVote dst.st.base o < SA.freezeTime p.toParams r) ∨
          GridCO.equivocates (headVotes p dst.st (r + 1)) i = true) ∧
        H ∈ dst.st.base.blocks ∧
        GridCO.stampBlock dst.st.base H < SA.freezeTime p.toParams r ∧
        (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  voterBackward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true
  pcReceipt : ∀ t, (∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target
  honestVoterInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  honestProposerInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st))
  rootResolution : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y
```

## Continuation signature locations

The full proved signatures are in the source declarations:

- `recovery_lock_no_later_successful_renewal` in `LockHistory.lean`.
  It takes the exact deadline and uninterrupted interval from
  `recovery_lock_write_witness`. It rules out every later successful
  fresh-gate slow-write branch before the read.
- `RecoveryLockTransport` above and `pcsa_recovery_lock_transport` in
  `Assembly/Recovery.lean`. The latter constructs only the transport value.
- `recovery_postmix_lock_window`, `recovery_postmix_live_locks_compatible`,
  `recovery_window_next_vote_locks_compatible`, and
  `recovery_window_later_locks_compatible` in `LockOverlap.lean`.
- `recovery_survivor_received_pc_compatible`,
  `recovery_survivor_relay_pc_compatible`, and
  `recovery_write_relay_pc_compatible` in `LockOverlap.lean`.
  These K kernels retain an explicit PC rank lower bound.

The final firstSlot signature is now proved under the transport interface:

```lean
∃ N : NamedProposal p.n,
  FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
```

## Proved checkpoint signatures

The source namespace is `AvailableChain.PCSA.Run`. The usual implicit
parameters are `{p : Params} {In V : Type} [DecidableEq V]`,
`{c : AppCodec In}`, and `{m : FGMode}`.

```lean
theorem recovery_lock_no_later_successful_renewal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (i j : Nat) (x : V) (s : Slot) (row : Block × Nat × Time)
    (hj : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hd : row.2.2 = SA.gateTime p.toParams s + pcsaL p)
    (hsurv : ∀ q, j < q → q ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho q x).st.base.obligations)
    (k : Nat) (r : Slot) (hjk : j < k) (hki : k < i)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams r))) :
    let pre := clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams r)
    ¬ (GridCO.savedGenuine pre.base r = none ∧
      ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) r = some C ∧
        (pre.base.obligations.any (fun q => pre.base.now < q.2.2 &&
          !Block.compatible q.1 C)) = false ∧
        row.1 ∈ (actView pre).blocks ∧ row.1 ≠ .genesis ∧
        Block.Preceq row.1 C ∧ leaseWriteOK pre.pcs (gateRank p pre r) row.1 = true ∧
        SA.Root.slowEligible p.toParams
          (actView (gateFrom p (eraseFG pre.fg.F) pre.pcs (gateRank p pre r) pre r))
          r row.1 = true)
```

```lean
theorem recovery_postmix_lock_window (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) (B : Block) (hB : LiveLease nd.st B)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t) :
    ∃ a s, g ≤ s + 1 - p.k ∧ SA.gateTime p.toParams s ≤ t ∧
      t < SA.gateTime p.toParams s + pcsaL p ∧
      ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
        GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
        Block.Preceq B D
```

```lean
theorem recovery_survivor_relay_pc_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (i j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, j < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (t : Time) (ht : E.t_GST ≤ t) (horizon : t + p.Δ ≤ rho.horizon)
    (hlo : j < V2.D.Run.idxBefore rho (t + p.Δ))
    (hhi : V2.D.Run.idxBefore rho (t + p.Δ) ≤ i)
    (pc : PC p.n) (hpc : pc ∈ (V2.D.Run.stateBeforeTime E rho t y).st.pcs)
    (hrank : rankAtLeast pc
      (leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) = true) :
    Block.Compatible pc.target row.1
```

## Checked continuation report (2026-10-08)

Code commits:

- `a8304cb6`: step 1, no later successful renewal.
- `86fde434`: step 2, transport interface and named OPEN suppliers.
- `a14fced9`: step 3 overlap proofs and rank-conditional K kernels.
- `b8debb9d`: remove the foreign rank equation export. No signature change.

```text
┌──────┬─────────┬──────────────────────────────────────────────────────────┐
│ Step │ Status  │ Result or exact remaining work                           │
├──────┼─────────┼──────────────────────────────────────────────────────────┤
│ 1    │ PROVED  │ Explicit no-later-successful-renewal corollary.          │
│ 2    │ PROVED  │ Interface only. Seven lane suppliers remain OPEN.        │
│ 3    │ STOPPED │ Rank dissemination and selected-view rank bound missing. │
│ 4    │ STOPPED │ Not started. Step 3 is incomplete.                       │
│ 5    │ STOPPED │ Not started. Step 3 is incomplete.                       │
│ 6    │ STOPPED │ Not started. The long firstSlot wrapper is absent.       │
└──────┴─────────┴──────────────────────────────────────────────────────────┘
```

This is a budget checkpoint. No counterexample or false statement was found.
The next proof must connect the gate-rank witness's early stamp to a PC held
before `e_j`. Then apply PC receipt before `z_j` and derive the rank lower
bound in later frozen views. This completes the missing part of K before F′.

Validation of the code at `b8debb9d`:

- Default `lake build --wfail`: PASS, 4,589 jobs.
- `LC_ALL=C bash scripts/check-build.sh`: PASS, including all self-tests.
- Layers: PASS, zero new findings. Layer self-test: PASS, 37 controls.
- GLY and F-13 under `LC_ALL=C`: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 421 entries in 21 modules; hashes match.
- Normal proof coverage: PASS, 5,901 declarations across 13 audits.
- All 25 new public names have explicit axiom audits. Only standard axioms occur.
- New declaration names have no collision on the six requested refs.
- Main precheck: expected ancestry refusal, main `b698238`, target `b8debb9d`.
  Fixed ref `222cf06a` is also not an ancestor. No main merge or push.

The first full check found `rankAtLeast.eq_1` exported from `LockOverlap`.
Commit `b8debb9d` uses `rankAtLeast_def` instead. The full rerun has zero
unaccepted equation exports. No checker, policy, or model change was made.
The five shared lock theorem signatures remain unchanged. No file named
`Recovery/RestartSeed.lean` was created. All tracked edits are within the
allowed file list. This report commit changes only this Markdown file.

## Continuation 2 coordination

The intended label-`g` majority supplier is `pcsa_gate_majority_of_label`
in `Clean/HonestBatch.lean` on `pcsa-ci-win-2`. Its floor is `T₀ ≤ v_s`.
Use it for the boundary `t_g < GST ≤ v_g` behind `OPEN_sameLabel`.
That branch has not been merged. The seven Assembly transport parameters
remain OPEN on this branch. Their exact statements above are unchanged.

Formation is adding `FormationPrem.proposerRootReachable`. Step 6 must set
`proposerRootReachable := hroot` from the same proof as the separate
`RecoveryRootReachable` conjunct. This branch still has the old structure.
No Formation or Claims file is changed here.

## Continuation 2 proved signatures

Namespace: `AvailableChain.PCSA.Run`. The implicit parameters remain
`{p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}`.
These are derived run facts. No new claim premise is added.

```lean
theorem recovery_gate_rank_disseminated (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (rank : PCRank) (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (horizon : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hrank : gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s = some rank) :
    ∃ D ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.pcs,
      D.rank = rank
```

```lean
theorem recovery_voter_rank_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s r : Slot) (hsr : s < r) (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd)
    (D : PC p.n) (hD : voterPC p nd.st r = some D) :
    rankAtLeast D (gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s) = true
```

```lean
theorem recovery_write_voter_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (g s : Slot)
    (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)))
    (hg : E.t_GST ≤ SA.earlyTime p.toParams s) (B : Block)
    (hwrite : leaseWriteOK
      (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).pcs
      (gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s) B = true)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams (s + 1)) = some nd)
    (C : PC p.n) (hC : voterPC p nd.st (s + 1) = some C) : Block.Compatible C.target B
```

```lean
theorem recovery_survivor_voter_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (g s r : Slot) (hsr : s < r)
    (transport : RecoveryLockTransport p c E rho g)
    (i k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, k < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (hrank : leaseRank (V2.D.Run.stateBefore E rho i x).st row.1 =
      gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s)
    (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (horizon : SA.voteTime p.toParams r + p.Δ ≤ rho.horizon)
    (hlo : k < V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ))
    (hhi : V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) ≤ i)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd)
    (C : PC p.n) (hC : voterPC p nd.st r = some C) : Block.Compatible C.target row.1
```

## Checked continuation 2 report (2026-10-08)

Commits:

- `68b7687d`: step 3, PC stamp history, rank dissemination, the voter-view
  bound, and K for actual selected voter keys.
- `13d00d9a`: remove four generated equation exports. No signature change.

```text
┌──────┬─────────┬────────────────────────────────────────────────────────────────┐
│ Step │ Status  │ Result or exact remaining work                                 │
├──────┼─────────┼────────────────────────────────────────────────────────────────┤
│ 3    │ PROVED  │ Rank receipt before z_j, voter bound, and K.                   │
│ 4    │ STOPPED │ Budget checkpoint. Survival-indexed F′ is not implemented.     │
│ 5    │ STOPPED │ Needs F′, actual proposal-pool paths, and both F4 clauses.     │
│ 6    │ STOPPED │ Needs steps 4–5. Long firstSlot export and wrapper are absent. │
└──────┴─────────┴────────────────────────────────────────────────────────────────┘
```

Step 3 uses the unchanged `RecoveryLockTransport` argument. All seven
Assembly suppliers remain OPEN: `OPEN_sameLabel`, `OPEN_earlyForward`,
`OPEN_voterBackward`, `OPEN_pcReceipt`, `OPEN_honestVoterInputs`,
`OPEN_honestProposerInputs`, and `OPEN_rootResolution`. Their exact
statements remain in “Continuation transport statements” above.
The label-`g` supplier and Formation integration are recorded above.

The final firstSlot target is still absent:

```lean
∃ N : NamedProposal p.n,
  FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
```

Validation of the final Lean sources at `13d00d9a`:

- Default `lake build --wfail`: PASS, 4,591 jobs.
- `LC_ALL=C bash scripts/check-build.sh`: PASS, including all self-tests.
- Layers: PASS, zero new findings. Stable self-test: PASS, 37 controls.
- GLY and F-13 under `LC_ALL=C`: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 421 entries in 21 modules; hashes match.
- Normal proof coverage: PASS, 5,915 declarations across 13 audits.
- All 14 new public names have explicit standard-axiom audits.
- Equation audit: zero unaccepted exports after the proof-only correction.
- All 22 new source names are clear on main, `222cf06a`,
  `pcsa-w2-formation-next`, `pcsa-ci-win-1/-2/-3`, and `nuc/pcsa-fsrc`.
- Main precheck: expected ancestry refusal, main `b698238`, target `13d00d9`.
  Fixed ref `222cf06a` is also not an ancestor. No main merge or push.

One layer self-test overlapped a commit and detected the changed worktree.
Its stable rerun passed. No checker, policy, model, or claim record changed.
`LockHistory.lean` and `LockRank.lean` have no diff from `a9f73cd8`.
No file named `Recovery/RestartSeed.lean` was created.
This is a budget checkpoint. No counterexample or false-statement blocker
was found. Start the next continuation with step 4 and the actual
HEAD-pool count transfer. Do not add the missing coverage as a claim premise.

## Continuation 3 interface change needed

The long proposer walk proof has the exact body of `RecoveryRootReachable`.
The predicate is opaque outside `Recovery/Suffix.lean`. That file is outside
the job's allowed list. Step 6 needs the following defining equation in that
file, immediately after the definition. This changes no predicate or premise.

```lean
theorem RecoveryRootReachable_def (s : Slot) :
    RecoveryRootReachable p c E rho s =
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s))) := rfl
```

## Continuation 3 proof signatures

The exact source signatures are:

- `recovery_lock_follow` in `LockFollow.lean`: F′ for `s < r < S`, indexed by the
  write event `k`, final read event `i`, exact row, and unchanged rank.
  The PC receipt deadline `v_r + Δ` is before the final read.
- `recovery_live_lock_preceding_heads` in `LockFollow.lean`: from `Recovery₂`,
  `StageOneFrame`, `RecoveryLockTransport`, `GST ≤ v_g`, a post-mix
  live read at `t_S` or `v_S`, derive `B ⪯ H` for every honest HEAD at
  label `S - 1`. The last-write witness is derived from the run.
- `recovery_long_proposer_root` in `ProposalPaths.lean`: the full body of
  `RecoveryRootReachable`, from the same premises, an honest proposer,
  `v_(g+2k-1) ≤ t_s`, and `d_s ≤ horizon`.
- `recovery_long_voter_leases` in `ProposalPaths.lean`: each live voter lock
  compatible with the carried PC base is below `N.erase.parent`.
  This is stronger than the requested depth-filtered F4 clause.
- `recovery_firstSlot_long_body` in `LongFirstSlot.lean`: the long-slot premises
  and one explicit `RecoveryLockTransport` argument give
  `∃ N, FormationPrem p c E rho s N ΔF ∧` the explicit root-walk body.

No coverage, root compatibility, or dominant path was added as a run or
claim premise. All seven transport suppliers remain OPEN with the exact
statements above. `pcsa_gate_majority_of_label` on `pcsa-ci-win-2` remains
the intended label-`g` supplier. That branch was not merged.

The local branch and inspected main still lack
`FormationPrem.proposerRootReachable`. The literal in `LongFirstSlot.lean`
already has the local proof `hroot`. The one-line integration is:

```lean
    proposerRootReachable := hroot
```

Keep the separate root conjunct after that integration.

## Checked continuation 3 report (2026-10-08)

Code commits:

- `b9498443`: step 4, F′ from the last write and exact-row survival.
- `f8742ab8`: step 5, actual proposal-pool paths and both F4 bodies.
- `a678c134`: step 6 body, `FormationPrem` and the explicit root walk.

Step 4: PROVED under the unchanged transport interface.
Step 5: PROVED under the unchanged transport interface.
Step 6: STOPPED at the predicate interface. The complete first-slot body
is proved. The exact `Recovery/Export` kernel and the Assembly wrapper
`pcsa_recovery_firstSlot_long` are absent.

Exact reason: `RecoveryRootReachable` is not exposed from
`Recovery/Suffix.lean`. That file has no defining-equation theorem and is
outside the allowed file list. A module-mode Lean check of direct
`exact hroot` fails with: “The following definitions were not unfolded
because their definition is not exposed: RecoveryRootReachable”.
The required equation is shown above. Scope approval was requested and
is still pending. No import-all, exposure-policy, or checker bypass was used.

The final proved body signature is below. Its namespace is
`AvailableChain.PCSA.Run`. Implicit parameters are `{p : Params}`,
`{In V : Type}`, `[DecidableEq V]`, `[Fintype V]`, `{c : AppCodec In}`,
and `{m : FGMode}`.

```lean
theorem recovery_firstSlot_long_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ N : NamedProposal p.n, FormationPrem p c E rho s N ΔF ∧
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s)))
```

The exact final target still needs the predicate conversion:

```lean
∃ N : NamedProposal p.n,
  FormationPrem p c E rho s N ΔF ∧ RecoveryRootReachable p c E rho s
```

All seven Assembly parameters remain OPEN: `OPEN_sameLabel`,
`OPEN_earlyForward`, `OPEN_voterBackward`, `OPEN_pcReceipt`,
`OPEN_honestVoterInputs`, `OPEN_honestProposerInputs`, and
`OPEN_rootResolution`. Their full statements in “Continuation transport
statements” are unchanged. No new transport field or claim premise was added.
The label-`g` supplier and Formation field integration are recorded above.

Validation of the final Lean sources at `a678c134`:

- Default `lake build --wfail`: PASS, 4,597 jobs.
- `LC_ALL=C bash scripts/check-build.sh`: PASS, all checks and self-tests.
- Layers: PASS, zero new findings. Layer self-test: PASS, 37 controls.
- GLY and F-13 under `LC_ALL=C`: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 421 entries in 21 modules; hashes match.
- Normal proof coverage: PASS, 5,941 declarations across 13 audits.
- All 26 new public declarations have explicit standard-axiom audits.
- Equation audit: zero unaccepted exports.
- All 43 new public and private source names are clear on main, `222cf06a`,
  `pcsa-w2-formation-next`, `pcsa-ci-win-1/-2/-3`, and `nuc/pcsa-fsrc`.
- Main precheck: expected ancestry refusal, main `b698238`, target `a678c13`.

`LockHistory.lean` and `LockRank.lean` have no diff from `9b22048e`.
All tracked changes are inside the allowed file list. No `RestartSeed.lean`,
main merge, or push. The defining-equation scope question is the remaining
block for the exact first-slot export and wrapper.

## Continuation 4: exact first-slot export

Step 6 is PROVED under the unchanged step-2 transport boundary.
`RecoveryRootReachable_def` is appended after the old end of `Suffix.lean`.
No earlier byte of that file changes. The lead approved this scope exception.
Its name differs from formation's planned
`pcsa_recovery_rootReachable_iff_formation` bridge. The new names were checked
with `LC_ALL=C` against `form-land3` and the seven required refs.

Namespace: `AvailableChain.PCSA.Run`. Implicit parameters are `{p : Params}`,
`{In V : Type}`, `[DecidableEq V]`, `[Fintype V]`, `{c : AppCodec In}`,
and `{m : FGMode}`.

```lean
theorem recovery_firstSlot_long (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s N ΔF ∧ RecoveryRootReachable p c E rho s
```

The Assembly declaration `pcsa_recovery_firstSlot_long` has the same slot
premises, with `s₁` for `s`. It replaces the one `transport` argument with
`OPEN_sameLabel`, `OPEN_earlyForward`, `OPEN_voterBackward`,
`OPEN_pcReceipt`, `OPEN_honestVoterInputs`, `OPEN_honestProposerInputs`, and
`OPEN_rootResolution`. Their exact statements are the seven fields in
“Continuation transport statements” above. The wrapper writes each
statement in full and calls `pcsa_recovery_lock_transport`.
No extra coverage or claim premise is added. Minimality of `g` is not needed
for this kernel; the inputs supplied by `long_recovery_slot` suffice.

The same-label supplier is `pcsa_same_label_gate_results_win` in
`Clean/GateCounts.lean:91` on `05052c10`, with floor `T₀ ≤ z_r`.
It supplies `OPEN_sameLabel`, including
`t_g < GST ≤ v_g`. That branch was not merged. All seven lane suppliers
remain OPEN here. Formation and CI restart remain separate suffix inputs.
This result does not close the unconditional `LongBreakRecoveredClaim`.

Main and this branch still lack `FormationPrem.proposerRootReachable`.
The existing literal in `LongFirstSlot.lean` uses the local root proof
`hroot` for the separate conjunct. When the Formation field lands, add:

```lean
    proposerRootReachable := hroot
```

Keep the separate `RecoveryRootReachable` conjunct. The new export converts
that same root proof; it does not construct a second Formation literal.
LockHistory and LockRank statements are unchanged. No RestartSeed file,
main merge, push, or checker/policy change was made.

## Checked continuation 4 report (2026-10-08)

Code commit: `f87b1c21` — exact first-slot equation, export, and Assembly wrapper.

- Step 1: PROVED. Last write, rank invariant, and no later successful renewal.
- Step 2: PROVED as an interface. Seven lane suppliers remain OPEN.
- Step 3: PROVED. Lock overlap and K for the selected voter key.
- Step 4: PROVED. F′ from exact-row survival and preceding honest HEAD coverage.
- Step 5: PROVED. Actual proposal paths and both F4 bodies.
- Step 6: PROVED. Exact `Recovery/Export.recovery_firstSlot_long` kernel and
  `Assembly/Recovery.pcsa_recovery_firstSlot_long` wrapper.

The kernel's full signature is in “Continuation 4: exact first-slot export”.
The Assembly signature has the same slot premises and exact target, with
all seven named OPEN parameters written in full in `Assembly/Recovery.lean`.
Their exact statements remain in “Continuation transport statements”.
The approved step-6 scope has no remaining proof item. The transport
suppliers, Formation producer, and CI restart are separate OPEN work.

Validation of `f87b1c21`:

- Default `lake build --wfail`: PASS, 4,597 jobs.
- `LC_ALL=C bash scripts/check-build.sh`: PASS, all checks and self-tests.
- `check-layers.py`: PASS, zero new findings. Self-test: PASS, 37 controls.
- `LC_ALL=C` GLY and F-13: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS, including compiled axioms, lease,
  equation, and unused-import checks.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 421 entries in 21 modules; hashes match.
- Normal `check-proof-coverage.py`: PASS, 5,944 declarations across 13 audits.
- All three new public names have `#print axioms` lines and coverage rows.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Equation audit: zero unaccepted exports.
- New names have no collision on main, `222cf06a`, `pcsa-w2-formation-next`,
  `pcsa-ci-win-1/-2/-3`, `nuc/pcsa-fsrc`, or `form-land3`, under `LC_ALL=C`.
- Main precheck: expected ancestry refusal, main `a1f0b3b`, target `f87b1c2`.
  No main merge or push.
- `Suffix.lean` is append-only relative to `9c043312`. LockHistory and
  LockRank are byte-for-byte unchanged. The seven Assembly OPEN statements
  match the existing constructor byte for byte. No RestartSeed file exists.

The initial equation proof `:= rfl` failed Lean's exported definitional
equality check. The proof `:= by rfl` passes in the owning module. No
predicate, premise, exposure policy, or checker was changed. The initial
sandboxed build could not write the global Lean throttle lock. Validation
then used the normal throttle with lock access; no bypass was used.

## Review fixes and transport suppliers (2026-10-08)

This section supersedes the OPEN supplier status in the continuation reports
above. Those reports describe their recorded commits.

Part A: DONE. `OPEN_sameLabel` uses `pcsa_same_label_gate_results_win`,
with floor `T₀ ≤ z_r`. The voter rank bound and predicate conversion are
proved. The two architecture records now state this.

Part B: DONE. Main `a1f0b3be` was merged in `1facafb2`. The five suppliers
are named theorems in `Assembly/Recovery.lean`:

- `pcsa_recovery_rootResolution_of_run`: named body scope and collision freedom.
- `pcsa_recovery_earlyForward_of_run`: early wire/body relay, resolution, stamps,
  and every prefix in the frozen voter tree.
- `pcsa_recovery_honestVoterInputs_of_run`: honest support, authentication,
  raw membership, resolution, and frozen-tree prefixes.
- `pcsa_recovery_honestProposerInputs_of_run`: honest support, authentication,
  raw membership, resolution, and full-tree prefixes.
- `pcsa_recovery_pcReceipt_of_run`: public-cut PC key relay. The field now
  accepts only `e_s` and `v_r`; every caller discarded the former body conjunct.
  The exact revised statement is in “Continuation transport statements”.

All needed Clean modules are already re-exported by `Clean.Export`. No Clean
file was edited. Strict delivery comes from `pcsa_strictFrom_of_sync`.

Part C: DONE. Both required `_win` theorems are already in `a1f0b3be`.
`pcsa_recovery_sameLabel_of_run` and `pcsa_recovery_voterBackward_of_run`
convert the indexed read facts and use `GST ≤ v_g ≤ v_r < z_r`. The proof
retains label `g`, including `t_g < GST ≤ v_g`.

Main `d1491021` was then merged in `5e0992e1`. The new Formation field is
filled by `proposerRootReachable := hroot` in `LongFirstSlot`. The separate
`RecoveryRootReachable` conjunct is retained.

Remaining OPEN transport fields: **none**. The old explicit-supplier wrappers
remain available. `pcsa_recovery_lock_transport_of_run` supplies their
`RecoveryLockTransport` argument. Its signature is:

```lean
theorem pcsa_recovery_lock_transport_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    RecoveryLockTransport p c E rho g
```

The final wrapper selects the slot with `long_recovery_slot`. Its only
premises are the long claim's premises:

```lean
theorem pcsa_recovery_firstSlot_long_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (horizon : E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ≤ rho.horizon) :
    ∃ (s₁ : Slot) (N : NamedProposal p.n),
      SA.gateTime p.toParams s₁ ≤ E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ∧
      FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
```

The seven supplier signatures are written in full in Assembly/Recovery.
Each conclusion is its corresponding field in “Continuation transport
statements”. Each takes `Recovery₂`. The receipt, support, and same-label
suppliers also take `StageOneFrame`. The five label-indexed suppliers take
`g` and `GST ≤ v_g`; the root and PC-key suppliers do not.

The complete `LongBreakRecoveredClaim` still needs suffix assembly and CI
restart. This result proves its first-slot input.

Commits:

- `1facafb2`: merge main `a1f0b3be`.
- `b62a7418`: Part A record corrections.
- `3153eb50`: all seven suppliers, narrowed PC receipt, and the run wrapper.
- `5e0992e1`: merge main `d1491021` with Formation integration.
- `24e1d86d`: fill the long first-slot Formation root field.
- This report commit: nine proof-coverage entries and the checked status.

Validation of the final Lean source:

- `lake build --wfail`: PASS, default targets, 4,636 jobs.
- `bash scripts/check-build.sh`: PASS, all steps and self-tests. The rebuild
  test changed exactly one module. No unaccepted equation export remains.
- `check-layers.py`: PASS, 72 baseline findings and zero new findings.
  Layer self-test: PASS, 37 rule controls.
- `LC_ALL=C check-gly-rules`: PASS. Separate F-13 check: PASS. F-20: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 424 entries in 21 modules; hashes match.
- `check-proof-coverage.py --write` and the following normal check: PASS.
  The diff adds exactly nine entries. Total: 6,216 declarations in 13 audits.
- All nine new public declarations have compiled `#print axioms` entries.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Main precheck: PASS against `d1491021`, after both main merges.
- `LC_ALL=C` name checks: PASS on main, `222cf06a`,
  `pcsa-w2-formation-next`, `pcsa-ci-win-1`, `pcsa-ci-win-2`,
  `pcsa-ci-win-3`, `nuc/pcsa-fsrc`, `form-land3`, `pcsa-ci-win-k2`,
  and `pcsa-ci-win-5b`. All twelve new names are clear.
- `git diff --check`: PASS. `LockHistory` and `LockRank` are unchanged.

No rebase or push. No direct Claims, Model, Clean, Shared, checker, or policy
edit. The authorized main merges retain their upstream changes.

## Final recovery assembly (2026-10-08)

This section supersedes the earlier suffix-assembly status.
All five assembly steps are PROVED. No new OPEN hypothesis was needed.
Formation supplies the seed stamp and result. RECOVERY supplies the window
through `rho.horizon`. The output adapter combines the suffix invariant,
later-slot stamps and C8 persistence. A later strong-inclusion read needs
only its freeze inside the horizon.

```lean
pcsa_fastRecoveredClaim (p : Params) : FastRecoveredClaim p
pcsa_longBreakRecoveredClaim (p : Params) : LongBreakRecoveredClaim p
```

The conditional wrappers keep their original types. Every new public name
has a `#print axioms` audit. The proof coverage file is regenerated with
`check-proof-coverage.py --write`.
