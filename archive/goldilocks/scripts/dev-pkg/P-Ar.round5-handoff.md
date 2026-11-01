# P-Ar Round 5 handoff

Base: sleep-int b1c840a5. Branch: sleep-par5.
Status: CLOSED. Group 1: 04281d84. Final validation is in docs/SLEEP-LEDGER.md.
Public claim and protocol declarations are unchanged.

Import `AvailableChainFGSAProofs.Proofs.Outage.ArmingDutySleep`.
The five Round 4 export names and types are unchanged. Their signatures below
are checked against P-Ar.round4-handoff.md.

## General construction

`fast_arming_scoped_on` includes the equal cut. It does not take hLast or a
strict-cut premise. When no label-l result exists, its comparison comes from
label l-1. The previous joined batch covers every joined label-(l+1) HEAD.
The certificate records the actual comparison label q <= l and FG lift.
`slow_arming_scoped_on` keeps the actual protected receiver and saved-row
supplier. Both producers keep current finality as an alternative to gate input.

`pending_gate_lease_or_F_scoped_on` has the same result as the Round 4 full
gate consumer, with the general certificate. Its hRows input remains explicit:
compatibility of earlier named rows through the post-pending tick cut, for
every FG lift of B. P-Ou must supply that from its source history.

`arming_sleep_history_on` assembles the pre-pending consumers. Its certificate
supplies pending_duties for actual honest emissions, inflight_heads for the
actual label-(l+2) HEAD, and F compatibility. pending_cover applies to protected
confirmed readers. The current caught-up read derives an enabled label-l gate.
It does not claim stable output at an arbitrary unjoined or uncaught-up reader.

T25: `arming_healthy_batch_window` gives exact receipts from joined selected
voters at the receiver's actual early tick. `arming_duty_batch` derives this
batch from the general certificate and the joined duty receiver window.
The retention and stamp proofs use that receiver's event epoch. No sleep
consumer calls the legacy NoRestart ArmingMain or ArmingCover producers.

## Actual assembly suppliers

- hState: cleanState_of_hist with clean_invariant, h.sleepPre, FaultQ,
  FGFoundation and SrcFrameAboveStmt, at each index through timeIdx(b0).
- hHist: clean_invariant at timeIdx(b0).
- htransfer: (cleanHistoryAt_body ...).2.2.1. The joined guard precedes the
  cut argument in the arming port; the actual supplier has the opposite order.
- hprov: clean_headVotes_provenance at the actual joined HEAD read. The
  regime's delta and tick-total facts supply its previous-label start tick.
  joined_provenance_consumer checks this supplier directly.
- hOutput: clean_gateOutput_body with the same Clean inputs and hHist.
  Project the result and successor-S bound; keep the enabled-gate guard.
- hSaved: clean_epoch_saved_row h.sleepPre hq hf hsrc, for slow mode only.
- htsrc: the existing TSrc input.

Checked consumers: Tests.OutageArming.fast_general_gate_consumer,
fast_history_consumer and slow_history_consumer. Clean proof modules are
imported only by the standalone test, which checks the assembly boundary.

## Exact types

Namespace: `AvailableChain.FGSA.Run`, with `open AvailableChain.SimplexFG`.
Implicit context: `{p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}`.
The signatures are copied directly from the production sources.

### ArmingJoinedProvenance

```lean
abbrev ArmingJoinedProvenance (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ s i y, y ∈ rho.honest →
    rho.events[i]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    ∀ o ∈ headVotes p (clock p (storeAt p c E rho i y)
      (SA.voteTime p.toParams (s + 1))) (s + 1), ∀ q, GridCO.headSeat? o = some q →
      o ∈ GridCO.votesAt (storeAt p c E rho i y).base s ∨
        GridCO.equivocates (GridCO.votesAt (storeAt p c E rho i y).base s) q = true
```

### ArmingSleepGateCert

```lean
structure ArmingSleepGateCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ : Time)
    (B : Block) (l : Slot) (D : Block) (Dh : FGBlock (Fin p.n)) : Prop where
  origin : ∃ r C, 1 ≤ r ∧ (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
    SA.gateTime p.toParams r ≤ T ∧ Block.Preceq B C
  max_lift : eraseFG Dh = D
  max_read : Block.Preceq B D
  max_mem : ∃ q, q ≤ l ∧ (q, D) ∈ cleanResults p c E rho (timeIdx rho b₀)
  max_le : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
    Block.Preceq C D
  gate_le_cut : SA.gateTime p.toParams l ≤ b₀
  cut_lt_pending : b₀ < SA.gateTime p.toParams (l + 1)
  cover_label : coverLabel p b₀ = l + 1
  source_below : ∀ y r C, y ∈ rho.honest →
    p.actionTime r < SA.gateTime p.toParams (l + 1) →
    actionSource p c E rho y r = some (some C) → Block.Preceq C D
  joined_heads : ∀ z, z ∈ rho.honest →
    joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
    ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
    Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
      (SA.voteTime p.toParams (l + 1))) (l + 1))
  f_below : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
    y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D
  pending_input : ∀ i y, IsGateTick p c rho i y (l + 1) →
    y ∈ coveredNodes p E rho fast b₀ →
    Block.Preceq B (F_at p c E rho i y) ∨
      ArmingGateInput p (clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1))) fast (l + 1) B D
```

### fast_arming_scoped_on

```lean
theorem fast_arming_scoped_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh
```

### slow_arming_scoped_on

```lean
theorem slow_arming_scoped_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀) :
    ∃ D Dh, ArmingSleepGateCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh
```

### arming_sleep_gate_core_scoped

```lean
theorem arming_sleep_gate_core_scoped {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧ B ∈ st.base.blocks))
```

### pending_gate_lease_or_F_scoped_on

```lean
theorem pending_gate_lease_or_F_scoped_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hf : FGFoundation p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hRows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)) (Bh : FGBlock (Fin p.n)),
      eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z))))
```

### ArmingSleepHistoryCert

```lean
structure ArmingSleepHistoryCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ : Time)
    (B : Block) (l : Slot) (D : Block) (Dh : FGBlock (Fin p.n)) : Prop where
  gate : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh
  pending_cover : ∀ y t, y ∈ coveredNodes p E rho fast b₀ →
    confirmedReader p c E rho y t → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Preceq B (S_at p c E rho (timeIdx rho t) y)
  pending_duties : ∀ y o t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → V2.D.Run.emits E rho y o t →
    (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)
  pending_compat : ∀ y t, y ∈ rho.honest → 0 ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Compatible B (F_at p c E rho (timeIdx rho t) y)
  inflight_heads : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest →
    V2.D.Run.emits E rho y o t → o.auth = .seat (.base (.head (l + 2))) q →
    HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H
```

### arming_sleep_history_on

```lean
theorem arming_sleep_history_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ArmingSleepHistoryCert p c E rho fast T b₀ B l D Dh
```

### arming_cover_sleep

```lean
theorem arming_cover_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) :
    ∀ y t, y ∈ coveredNodes p E rho fast b₀ → confirmedReader p c E rho y t →
      SA.gateTime p.toParams l ≤ t → t < SA.gateTime p.toParams (l + 1) →
      t ≤ rho.horizon → Block.Preceq B (S_at p c E rho (timeIdx rho t) y)
```

### arming_pending_duties_sleep

```lean
theorem arming_pending_duties_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ∀ y o t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
      t < SA.gateTime p.toParams (l + 1) → V2.D.Run.emits E rho y o t →
      (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
      (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)
```

### arming_inflight_heads_sleep

```lean
theorem arming_inflight_heads_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (l + 2))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H
```

### arming_duty_batch

```lean
theorem arming_duty_batch [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {y : V} {t : Time} (hw : ArmingReadWindow (c := c) E rho y (l + 1) t)
    (het : SA.earlyTime p.toParams (l + 1) < t) :
    ArmingJoinedBatchState p c E rho l D y
```

### ArmingReadWindow

```lean
structure ArmingReadWindow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) (C : Time) : Prop where
  honest : x ∈ rho.honest
  awake : AwakeClosed E x (slotStartZ p (s : Int)) C
  epoch : RestartFreeTime rho x (slotStartZ p (s : Int)) C
```

### arming_healthy_batch_window

```lean
theorem arming_healthy_batch_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hHeads : ∀ z, z ∈ rho.honest →
      joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
      ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
      Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
        (SA.voteTime p.toParams (l + 1))) (l + 1)))
    {x : V}
    (hw : ArmingReadWindow (c := c) E rho x (l + 1) (SA.earlyTime p.toParams (l + 1)))
    (hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams (l + 1)) x).st.fg.F) D) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick x (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k x).base.votes ∧
        K ∈ (storeAt p c E rho k x).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k x).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
            SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k x).base K <
          SA.earlyTime p.toParams (l + 1)
```

### fast_arming_on

```lean
theorem fast_arming_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hLast : ∃ C, (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat, C) ∈
      cleanResults p c E rho (timeIdx rho b₀)) :
    ∃ D Dh, ArmingSleepCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh
```

### slow_arming_on

```lean
theorem slow_arming_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀) :
    ∃ D Dh, ArmingSleepCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh
```

### arming_sleep_gate_core

```lean
theorem arming_sleep_gate_core {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧ B ∈ st.base.blocks))
```

### pending_gate_lease_or_F_on

```lean
theorem pending_gate_lease_or_F_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hf : FGFoundation p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hRows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)) (Bh : FGBlock (Fin p.n)),
      eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z))))
```

### arming_genesis_on

```lean
theorem arming_genesis_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (i : Nat) (y : V) :
    Block.Preceq .genesis (S_at p c E rho i y) ∧
      Block.Preceq .genesis (F_at p c E rho i y)
```
