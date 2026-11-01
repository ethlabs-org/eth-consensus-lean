# P-Ar Round 4 handoff

Base: sleep-int 36781bff. Branch: sleep-par4. Full P-Ar remains PREPARED.
P-Cl1 fixture audit is CLOSED (3c6cee8d). The canonical fragment defect is CLOSED
(7c071cfc). Public claims and protocol declarations are unchanged.

## Scoped certificate

Import `AvailableChainFGSAProofs.Proofs.Outage.ArmingSleep`.

`ArmingSleepCert` supplies the protected pending gate. It keeps the actual Clean
origin, comparison result and FG lift, source bound, F bound and pending input.
The pending input keeps the current-F alternative. It does not supply the legacy
all-honest healthy batch or the pre-pending duty history.

`slow_arming_on` derives a last-label result from a named slow protected receiver.
Its window includes this receiver's label-l gate, including equality at b₀.
The produced certificate covers every slow protected receiver. There is no
NoRestart premise, existing saved row premise or receipt-service premise.

`fast_arming_on` still takes an actual last-label result. Its checked consumer
derives that result when gateTime(l) < b₀. Fast construction when gateTime(l) = b₀
remains OPEN. Do not infer participation at b₀ from joinedPartBefore.

Both producers consume these proven Clean inputs through the assembly boundary:

- `hState`: at each i ≤ timeIdx(b₀), use `cleanState_of_hist` with the actual
  `clean_invariant`, `h.sleepPre`, FaultQ, FGFoundation and SrcFrameAboveStmt.
- `hHist`: use `clean_invariant` at timeIdx(b₀).
- `htransfer`: use `(cleanHistoryAt_body ...).2.2.1`. Its joined argument precedes
  the cut argument in the arming port; the fixture checks the argument order.
- `hSaved`: use `clean_epoch_saved_row h.sleepPre hq hf hsrc`. Only the slow mode
  needs this input. Current finality remains an alternative to the saved rows.
- `htsrc`: the existing `TSrc` source-discipline input.

The actual suppliers are checked by `Tests.OutageArming.slow_certificate_consumer`
and `fast_certificate_consumer`. The latter has an explicit strict-cut input.
Clean proof modules are imported by the standalone test, never by the Outage lane.

## Pending input and consumers

`arming_sleep_pending_input` uses the joined seat count. It retains the batch
from its actual early tick to the actual gate tick in that receiver's epoch.
The cut-to-strict-read and strict-read-to-tick epochs remain separate.
`arming_pending_epochs` derives all three epochs from the protected scope.

`arming_sleep_gate_core` uses the enabled executed gate. It returns B below S
and either B below F, or a release-level lease through at least gateTime(j) + L.
The lease branch also supplies B in the actual post-gate block pool.
The current-F branch reaches the same output directly through output nesting.

`pending_gate_lease_or_F_on` returns the full domain alternative needed by P-Ou:
B is in fullTree, or B is below the frame root. It consumes the existing scoped
frame theorem. Its explicit `hRows` input is compatibility of every earlier honest
named row with the same lifted B, through the post-pending tick cut. P-Ou must
supply this input from its source history. The type does not hide it in the
certificate. `Tests.OutageArming.slow_gate_consumer` applies the actual slow
producer and this consumer. No P-Ou file was edited.

`arming_genesis_on` uses direct prefix order for S and F. It needs no certificate.
The lower ArmingStep write and enabled-gate exports from Round 3 are unchanged.

## Remaining general construction

The fast equality case needs a comparison/batch construction that does not assume
a label-l executed result. A fast protected receiver is joined at the pending
label's gate; this does not make its previous-label gate enabled. The regime
counts joined voters strictly before b₀. It gives no such count at b₀.

The pre-pending HEAD/proposal coverage and duty-history adapters remain OPEN.
The old `arming_head_covers`, `arming_proposal_covers`, `arming_cert`,
`fast_arming` and `slow_arming` remain explicit legacy NoRestart producers.
No new sleep consumer calls them. The new pending certificate is not the old
ArmingData. P-Ou must use the scoped types below and retain the `hRows` boundary.

Do not mark full P-Ar CLOSED from compilation of these scoped gate ports.
No public STOP or claim amendment was introduced.

## Exact checked types

The following signatures are copied from the production source. The namespace is
`AvailableChain.FGSA.Run`, with `open AvailableChain.SimplexFG`. The implicit
context is `{p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}`.

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

```lean
theorem arming_genesis_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (i : Nat) (y : V) :
    Block.Preceq .genesis (S_at p c E rho i y) ∧
      Block.Preceq .genesis (F_at p c E rho i y)
```
