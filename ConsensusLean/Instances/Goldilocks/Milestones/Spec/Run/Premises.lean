module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.GenericPremises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks

/-! # Goldilocks runs: the premises

The premises of the claims (`specs/goldilocks/tex/goldilocks-claims.tex` §"Premises")
over a run (`Spec/Run/Model`), for the honest validators `H`:

* **`Sync`** (`SyncOn`, with a window `W` on the send time, a window `Wr` on the acceptance time
  for the acceptance relay, and a map `eff` to the effective send time; `SyncRun a b` is
  `Sync[a, b]`, `GSTRun g` is `GST(g)`): every AC message that an
  honest `x` sends or admits (also from the payload of an accepted block) at a time `τ` in the
  window is processed by every honest `y` at a time in `[τ, max(eff τ, w_y) + Δ)`, `w_y` the
  latest wake of `y` at or before its processing (the delivery of that send or forward, not an
  earlier processing; a refused receipt triggers nothing); every block an honest `x` sends (its
  own proposal) or accepts at `τ` in the window is processed (`fg_on_block`, accepted or
  refused) by every honest `y` in that interval, and **acceptance relay**: a block accepted at a
  time in the relay window is accepted by every honest `y` whose `Σ.F` it extends before the
  deadline; attestations likewise with `Δ_F`, from a signing or an admission, except that an
  attestation has no lower bound: a processing before the signing or admission counts. Its
  processing is never refused (`fg_on_attestation` only adds it to the pool, which keeps it,
  also across a restart), so an earlier one leaves `a` in the pool as a later one would; and an
  honest node forwards an admitted attestation as the same object, which the network counts as
  held from an earlier receipt (absent a wake in between). Not in CLAIMS, whose `Sync` attestation
  has attestations "in the same form" (not before the send). Blocks and messages keep the lower
  bound: they are forwarded in fresh wrappers, and an earlier receipt of a block can be refused.
  Over the run, "processed by `y` before the deadline" reads: at every call of `y` at or after
  the deadline, `y` has processed it at a cut before its own deadline (as `SyncAC`).
  `GST(g)` is `Sync[g, ∞)` with every object sent
  before `g` processed as if sent at `g` (`eff τ = max τ g`). The claims' "as if sent at `g`"
  is read for the deadline only: the deadline becomes `max(g, w_y) + Δ`, while the lower bound
  of the delivery interval stays the real send time, so an object sent before `g` may be
  delivered before `g`. The acceptance relay
  of `GST(g)` covers only acceptances at `τ ≥ g` (claims: `Sync`'s relay "covers only `τ ≥ g`";
  `GST(g)` re-delivers old objects, it does not make them accepted, since a block refused for a
  missing parent is not delivered again): pre-`g` acceptance catch-up is the separate regime
  premise `Catch(κ)` (`Healing.CatchRun`).
  `SyncOn` also carries the positivity `0 < Δ_F` and the order `Δ ≤ Δ_F` (claims
  §"Parameters"; the generic network keeps the two bounds unordered), so every premise built on
  it has them. The order is there because an attestation admitted from a block is forwarded in
  the block's relay wrapper, which the network serves within `Δ`, not `Δ_F`
  (`docs/decisions.md` §"Network and delivery").
* **`Sleepy`**: `Sync[0, ∞)` and `f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}`, `h_t` the
  honest validators awake and joined at `t` (`JoinedAt`: every restart at or before `t` is at
  or before `t_{slot(t) − 1}`; in slot `0`, no restart).
* **`Healthy(g)`**: `GST(g)`, every honest validator awake on `[max(g, 0), ∞)`,
  `f ≤ ⌊(n − 1)/3⌋`.

**Infinite runs.** Under `Healthy(g)` (an honest node awake at every later time) and under
`Sleepy` (`f < h_t` needs an honest node awake at every slot's `t_s`), the awake clamp
`awake_in_horizon` makes cut times unbounded, with labelled coverage beyond any finite
observation horizon, and a tick of every awake honest node at every public time
(`tick_of_awake`). This is the intended reading:
runs are `Nat`-indexed traces of the protocol running forever, and a finite trace is a prefix
that says nothing after its last cut, so it satisfies neither regime premise. That the two
premises are satisfiable by such a run (together with `Node.LocalRun`) is the kind (a) witness
`periodicRun_localRun` with `periodicRun_healthy` and `periodicRun_sleepy` in
`ConsensusLeanTest/Goldilocks/Run/Statements.lean`.

`NoColl` is `Compose.NoCollRun` (`Statements/Compose/Run`: `Compose.NoCollOn` on the blocks
that occur in the run and genesis), stated where it is used. `Outage` and `Weak` have no run
form here: R.5 and R.6, which took them, are archived with R.3 and R.4
(`archive/consensus-lean-regimes`). -/
