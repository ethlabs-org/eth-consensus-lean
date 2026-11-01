# Protocol framework — design (v7, 2026-09-28)

**Current policy — 2026-10-09.** APIs and anchors can change. Generate the current
snapshots, then review all additions, removals, statements, and dependency changes.
Older freeze, append-only, no-widening, and zero-rename rules below are history.
They do not set current acceptance rules. Kernel, proof, source, and import checks
still apply. A snapshot update does not approve a changed claim.


_Status: v7 DRAFT. v6 answered the second Astra audit; v7 answers the
third (`docs/audit/framework-v6-audit-report.md`: REVISE, 3 blocking,
6 major, 0 minor; the framework items W01, W02, W04, W06, W08, W09). The exact FG
statements moved to `docs/FG-COMPOSITION.md`, a separate versioned
registry that follows the research. This file fixes the framework and
the FG interface shapes only. The user APPROVED §0–§6 and §9 on
2026-09-28; §7 stays DRAFT until Phase 4._

_History: v0–v2 core design agreed by both sessions. v3–v4 user FG
decisions (fixed Simplex FG, anchors, modular recovery, HavocFG). v5
answers the first Astra audit. v6 answers the second; §11 maps the
findings._

## 0. Purpose and scope

The current repository proves one fixed bundle (`AvailableChain`,
Draft 4.3) per protocol. This design replaces the bundle with a framework
that stays stable while the protocol search changes direction.

```text
┌────┬───────────────────────────────────────────────────────────────────┐
│ G1 │ Protocol-agnostic within the engine scope (below).                │
│ G2 │ Additive evolution: a new assumption, claim, output kind or key   │
│    │ scheme is an addition; existing certificates stay valid.          │
│ G3 │ Partial certification: an instance certifies any subset of the    │
│    │ claims, at any number of parameter points, over one fixed         │
│    │ protocol and facet bundle.                                        │
│ G4 │ Mechanical comparison: checked transports and Pareto sets.        │
│ G5 │ Composition with one fixed, verified FG (our Simplex FG) through   │
│    │ a typed interface.                                                │
│ G6 │ Cheap falsification: executable instances, kernel-checked         │
│    │ refutations.                                                      │
└────┴───────────────────────────────────────────────────────────────────┘
```

Non-goals: probability inside Lean; one generic proof for all
protocols; porting verified-consensus; unbounded ("eventually")
liveness (every catalog claim has a deadline).

**Engine scope.** Engine v2 covers scheduled-duty models: a finite
validator set; labels with a fixed act time and seat count; committees
or the full validator set, with public assignment conditions;
identity-free honest code (no private key or private randomness); one
global time; a static honest set; finite runs; emission only on ticks.

Out of scope by decision (user, 2026-09-28): private VRF
self-selection. Also outside v2, each needing a new engine version with a
lift simulation: clock drift (one logical duty at different local
times); signed replies on receipt; explicit compromise or key erasure;
unbounded liveness.

Additions inside the scope (not covered by existing certificates):
integer stake weights (seat multiplicity, weighted links and quorum
lemmas; the unit-weight FG proofs do not transfer by themselves); fixed
size sampled committees with a Balanced-ε premise; public fixed-size age
buckets; inclusion-list committees; multiple proposers with proposal
identifiers and a selection claim; DAG state in scheduled models (the FG
needs a chain projection); monotone corruption traces with new regimes;
late joiners in a fixed validator set (after E6); protocol-driven relay
with send provenance; signature aggregation with extraction proofs; a
second FG as a new module with its own composition proofs (a gadget whose
private record controls AP proposals needs a new isolation interface).

## 1. Layers

```text
┌────┬──────────────┬───────────────────────────────┬────────────────────┐
│ L  │ Layer        │ Content                       │ Change policy      │
├────┼──────────────┼───────────────────────────────┼────────────────────┤
│ L0 │ Engine       │ events, world, run, emission, │ versioned; content │
│    │              │ restart, own-record step      │ current snapshot   │
│ L1 │ Conditions   │ run predicates; regimes;      │ current snapshot   │
│    │              │ execution-prefix predicates   │                    │
│ LM │ Modules      │ fixed-component definitions:  │ versioned; content │
│    │              │ Simplex FG, duty frames,      │ current snapshot   │
│    │              │ policy type, AP template      │                    │
│ L2 │ Facets       │ what an instance exposes      │ current snapshot   │
│ L3 │ Catalog      │ claim specs, transports,      │ current snapshot;  │
│    │              │ relation lemmas               │ immutable ids      │
│ L4 │ Instances    │ protocol + parameters +       │ free               │
│    │              │ facets; certificates and      │                    │
│    │              │ refutations                   │                    │
│ L5 │ Kits         │ proofs: engine, Goldfish, FG, │ free; never        │
│    │              │ compose                       │ imported by L0–L3  │
│ L6 │ Registry     │ generated matrix; explorer    │ generated          │
└────┴──────────────┴───────────────────────────────┴────────────────────┘
```

L0, L1, LM, L2 and L3 import nothing from L4–L6. LM holds definitions
only. A hole in L1–L3 is fixed by a new versioned entry plus, when
useful, a relation lemma to the old one.

## 2. Engine v2 (L0)

**E1. Duties and keys.** `Auth = seat (ℓ : Label) (i : Fin (seats ℓ)) | none`.
A proposal duty is a one-seat label. `act st ℓ` produces every duty
payload. `ProtocolSpec` has no global `n`.

**E2. Seats and assignment.** `seats : Label → Nat`,
`Run.seatOf ℓ : Fin (seats ℓ) → V`. Committee models are L1 conditions:
`CStar F` (seats = |V| and a proved `Fin (seats ℓ) ≃ V`), `Linked F` (one
fixed bijection for all labels in F), `SingleSeat F`, and later
`Weighted w F`, `Balanced ε F`. Honest code never sees keys. The
protocol declares its AP label family `APLabels` and its FG label family
explicitly (E5).

**E3. Weights** are additions (seat multiplicity plus conditions).

**E4. Delivery outcomes and deliverability (audit V01).**
A delivery of `o` calls the handler; for each `o'` with `handles o o'`,
the protocol classifies the call's effect on `o'` as one of:
- *accepted*: `processed o'` becomes true;
- *permanently rejected*: `excludes o'` holds from then on;
- *temporarily refused*: the state does not change for `o'`, and
  `excludes o'` is false (for example SA-PC's PC before
  `pcEnvelopeReady`; a future-label faulty HEAD).

A refusal that can never end in the current epoch is a PERMANENT
rejection, and the protocol must report it through `excludes` (async
review of v7). Examples: Grid CO's HEAD for label r after slot r+1 (the
clock only goes forward; `Model/Protocol.lean:306`), and a HEAD from a
seat that already has two HEADs at label r (a third equivocation).
Today Grid CO sets `excludes := fun _ _ => false`, so Phase 1 must
define it for these two cases, and for SA and SA-PC too.

The network conditions are about handler calls, as today. Temporary
refusal is allowed and needs no flag. Obligations (`HooksSound P`):
- `excludes` is stable under `clock`, `process` and `recordOwn` within
  an epoch, and implies that `process` leaves the state unchanged.
  `restore` may clear an exclusion that depends on lost receipts (the
  equivocation case), but not a time-based one;
- `processed` and `depsPresent` are monotone WITHIN ONE RESTART EPOCH of
  the node (`processed` may be derived; audit W04);
- `handles o o'` implies `o = o' ∨ carries o o'`.

Feasibility contract (audit W01). `HooksSound` alone does not give
continuation: a protocol can emit a malformed object after one trigger,
and then no synchronous run passes the next broadcast deadline. So every
instance also proves:
- `EmitWellFormed`: every object that an honest node emits satisfies
  `wellFormed`;
- `HandlerCoverage`: a delivery of `o` makes a handler call for `o` and
  for every `o'` with `handles o o'`, as the outcome classification says;
- `Deliverable`: every dependency of an honest emission was ACCEPTED by
  the emitter before the emission (a faulty object is allowed), and the
  emitter's acceptance order is a finite delivery plan;
- `RelayFeasible`: if an honest node accepts `o` at t, then at an honest
  receiver that has accepted `o`'s dependencies, a delivery of `o` before
  t + Δ (after GST, or on a healthy prefix) is accepted or permanently
  rejected (`excludes`), not temporarily refused.

The acceptance-relay regime condition gets the same exemption as the
handler-call relay in `PartialSynchrony`: no obligation for an object
that the receiver excludes at the deadline. Today `AcceptedObjectRelay`
and `HealthyAcceptedObjectRelay` (`Generic/Conditions.lean`) have NO
exemption. So for Grid CO and SA, a faulty HEAD released to one honest
node in the last Δ of its window takes the run out of EVERY regime:
today's certificates do not cover that adversary behavior. This is a
coverage gap in the current contract. Phase 1 fixes the condition and
checks again each SA and SA-PC proof that uses `acceptedRelay` (it may
use acceptance only before the object's exclusion time).

`WindowMargin` (per instance, per object class; async review): the last
cutoff at which a rule reads the object, plus Δ, is at most the
receiver's exclusion time. With it, the exempt relay implies the old
relay at every cutoff that the proofs use. Grid CO/SA: the label-r HEAD
cutoffs are t_r+2Δ, +3Δ, +5Δ and +6Δ (`earlyTime`, `freezeTime`,
`releaseTime`, `gateTime`); the window closes at t_r+8Δ; margin 2Δ ≥ Δ.
An excluded third equivocation is harmless: the late test drops the
seat on two accepted copies. FG rows: check the same margin for the
w_F inclusion window in Phase 4.

`Kit.Engine` proves the run-extension theorem from these four and
`HooksSound`: every valid execution prefix in a regime extends by the
canonical synchronous scheduler to any horizon, with both handler calls
and acceptance relay. This gives continuation from every accepted input,
including inputs that trigger malformed emissions (which the contract
forbids).

Two limits (async review):
- Temporary refusal and synchrony. If the only delivery within Δ is
  temporarily refused, the handler-call premise is met but the object is
  not processed. A proof may assume later processing only if (a) the
  regime includes the optional L1 condition `ReOffer` (the object is
  delivered again within Δ after the first time it is no longer refused,
  after GST), or (b) the protocol buffers the object in its state and
  processes it later, or (c) the object reaches acceptance through the
  relay premise (today's SA-PC). Each instance states which.
- The run-extension theorem guarantees handler calls on the delivery
  plan, not acceptance. A receiver may permanently reject an object that
  the emitter accepted (for example FG admission with a different F,
  possible only at a > f); excluded objects carry no obligation.

These are NEW eligibility obligations. They are proved per migrated
instance; they are not silently added to the v1 hooks (V07, M03).

**As implemented in plan 1b (2026-09-29).** This note does not change
the text above.

- Relay condition. The paragraph "The acceptance-relay regime condition
  …" is out of date. The receipt-relay merge (`1a3f73a`) removed the
  field `acceptedRelay` from `SleepyRegime`, `OutageRegime`,
  `RecoveryRegime` and `StrongArmedRegime` (`CONTRACT.md`, "Relay
  premise — 2026-09-28"), and SA-PC's `QuorumRecoveryRegime` has no such
  field. Each regime uses `PartialSynchrony` or `HealthyPrefixDelivery`
  (`Generic/Conditions.lean`). Both conditions give a handler call, not
  acceptance, and both have no obligation for an object that the
  receiver excludes at the deadline. `AcceptedObjectRelay` and
  `HealthyAcceptedObjectRelay` keep their text, but only derived results
  use them: the SA-PC adapters
  (`AvailableChainSAPC/Proofs/ReceiptRelay.lean`),
  `healthyPrefix_acceptedRelay` and Counter's `canonical_relay`. Thus the
  coverage gap that the paragraph describes is closed, and plan 1b did
  not change `AvailableChainStatements`. The reason to define `excludes`
  is the delivery classification of `RelayFeasible` (plan 1c): with
  `excludes = false`, a permanent refusal counts as a temporary refusal
  that never ends.
- E4 classification per protocol. The "and for SA and SA-PC too" above
  holds for SA only.

```text
┌──────────┬───────────────────────────────────────────┬─────────────────────────────┐
│ Protocol │ excludes (an object that is not processed)│ Where                       │
├──────────┼───────────────────────────────────────────┼─────────────────────────────┤
│ Grid CO  │ a HEAD of label r with r + 1 < the current│ `excludes`,                 │
│          │ slot (the clock only goes forward), or a  │ `AvailableChainGridCO/Model/│
│          │ HEAD whose seat already equivocates at r. │ Protocol.lean`; shape:      │
│          │ Never a proposal.                         │ `excludes_head_iff`,        │
│          │                                           │ `excludes_proposal`,        │
│          │                                           │ `excludes_not_processed`    │
│          │                                           │ (`Proofs/Hooks.lean`)       │
│ SA       │ the same as Grid CO (`sa p` is `gridCO`   │ as Grid CO                  │
│          │ with `slowLeasePolicy`)                   │                             │
│ SA-PC    │ none: `excludes := fun _ _ => false`. A   │ `AvailableChainSAPC/Proofs/ │
│          │ HEAD is processed when it is in the       │ Hooks.lean` (module         │
│          │ archive `receivedHeads`; `receiveHead`    │ docstring gives the reason  │
│          │ refuses only a future label (temporary).  │ per object class)           │
│          │ The Grid CO refusals act only on the base │                             │
│          │ cache. A PC is refused only before        │                             │
│          │ `pcEnvelopeReady` (temporary).            │                             │
│ L*       │ a HEAD whose seat already equivocates at  │ `excludes`,                 │
│          │ its label (a third equivocation); a       │ `AvailableChainLStar/Model/ │
│          │ proposal wire whose block is already      │ Protocol.lean`;             │
│          │ stored (a faulty proposer can sign two    │ `excludes_head_iff`,        │
│          │ wires with one block). L* admits late     │ `excludes_proposal_iff`,    │
│          │ votes of old labels, so it has no         │ `excludes_second_wire`      │
│          │ old-label clause.                         │ (`Proofs/Hooks.lean`)       │
└──────────┴───────────────────────────────────────────┴─────────────────────────────┘
```

- Shape and direction. `excludes_head_iff`, `excludes_proposal` and
  `excludes_not_processed` give the shape of `excludes` (they unfold the
  definition). Against the handler, Lean proves one direction: an
  excluded object is refused for the rest of the run (`excludes_inert`,
  `excludes_stable`). The other direction (an unprocessed object that the
  handler refuses for good is excluded) is not proved. It is a plan 1c
  input, because `RelayFeasible` needs it.
- Hook facts. Each protocol library proves the five hook facts
  (`excludes_inert`, `excludes_stable`, `processed_stable`,
  `deps_stable`, `handles_carries`) in its own namespace, with the
  statement shape of the `HooksSound` fields. The protocol libraries do
  not import `AvailableChainFramework`. The Registry assembles the values
  `gridHooks` (SA uses it at `slowLeasePolicy`), `sapcHooks` and
  `lstarHooks`. The Phase 0 variant `gridCOx` and its `gridExcludes`,
  `gridCOx_hooks` and `inWindow_not_excluded` are removed.
- `WindowMargin` is a per-protocol lemma module,
  `AvailableChainGridCO/Proofs/WindowMargin.lean`, not a framework
  predicate. Each Grid CO relay lemma that used `excludes = false` by
  `rfl` (`synchronous_head_handled_early`,
  `synchronous_proposal_delivered`, `synchronous_receipt_before`,
  `synchronous_block_path_at_gate`, `handled_before_proposal_of_ready`)
  has a premise: the reader does not exclude the object at any time up
  to the lemma's cutoff. The module proves that premise for each caller.
  A label-r HEAD whose seat does not equivocate is not excluded before
  `proposalTime p (r + 2)` (`head_not_excluded_before`), and every
  caller's cutoff is at most `gateTime p r`, a margin of 2Δ. An honest
  HEAD is never excluded in that window
  (`honest_head_not_excluded_before`). For a HEAD of any seat, the
  caller gets the case split `head_not_excluded_or_equivocates` and
  ends in its existing "or equivocates" outcome. A proposal is never
  excluded (`proposal_not_excluded`). If `excludes` covers more objects
  later (I9, §12), only this module changes. Superseded 2026-09-29 by
  the user's I9 decision (§12): no `rootOK` in `wellFormed`; the root
  check is the dependency lookup.
- Not in plan 1b: `EmitWellFormed`, `HandlerCoverage`, `Deliverable`,
  `RelayFeasible`, the predicate `Eligible` and the run-extension theorem.
  Their only consumer is the run-extension theorem. A definition in a
  locked module of `AvailableChainFramework` gets its lock line when it
  is first written, so a later change to it is a lock change. Thus plan
  1c defines them and proves the theorem in the same plan.

*Note 2026-09-29 (plan I9).* This note does not change the text above.
Plan I9 (derived roots, §12) added no clause to any `excludes`. A
proposal with an unknown parent root is a temporary missing dependency:
the handler returns the state unchanged (`admitProposal_missingParent`
in Grid CO, SA-PC and L*), and the proposal can enter after its parent.
So the E4 table above and `Proofs/WindowMargin.lean` did not change. The
sentence "If `excludes` covers more objects later (I9, §12), only this
module changes" did not apply.

**E5. Own-signature record.**
- `selfVisible : Label → Bool`, `recordOwn : State → Object → State`.
- `World.step` takes the run context (seat assignment and `awake`).
- Atomic tick: `clock`; every due payload from that post-clock state;
  signing; `recordOwn` folded over self-visible objects in label order,
  then seat order; release.
- Separation: every label in `APLabels`, and every label in a `CStar`
  family, has `selfVisible = false`.
  *Note 2026-09-29 (Phase 2a; fgsa-impl via DC-simplify):* the restriction
  applies to the AP labels and to the declared fresh family (`F.fresh`),
  not to every `CStar` family. `Linked` implies `CStar`, and `Linked`
  labels (FG rows) may be self-visible. The 2a `separation` field states
  it this way: `F.ap ℓ ∨ F.fresh ℓ → selfVisible ℓ = false`.
- Isolation laws, with `base : State → B`:
  - `base` after `clock` and `process` is a function of `base` before and
    of the time or object; `recordOwn` does not change `base`;
  - `act` on `APLabels`, all gossip and every output getter factor
    through `base`;
  - restore law: `base (restore d)` depends only on the base-visible part
    of `d` (for an FG composite: F and its basis), never on record-only
    data (audit V11: otherwise a restart could copy a self-visible seat
    index into the base);
  - hook projection: `wellFormed`, `depsPresent`, `processed`,
    `excludes` and `handles` restricted to AP objects factor through
    `base`, so delivery regimes transport between a composite and its AP
    projection.

**E6. Restart.** `Event.restart v t`; order at one time: restart, ticks,
deliveries. Step: `st ↦ restore (durable st)`. For an FG composite,
`durable` = Λ + F + the F basis; h_max and J are derived again from
received chain states. *Note 2026-09-29 (user decisions, via DC-simplify; this replaces two
earlier notes of the same day):* the faithful form: an FG composite keeps
Λ (the slashing-protection database) and F with F's chain state (the
anchor) durable, and the history below F is pruned. This form comes with the
planned anchor-and-pruning feature (§8). Until then FG-SA uses an INTERIM
form: Λ is kept and the store is reset to its initial state; no FG-SA claim
reads F across a restart. Each restart starts a new EPOCH of the node. Receipt facts (`processed`,
`depsPresent`) reset with the epoch (audit W04): a block outside the
durable part is lost, and it can be delivered again (the freshness check
allows it). Delivery obligations toward a restarted node cover objects
re-offered after its rejoin; regimes with restarts add a rejoin
condition (state transfer or re-offer of the needed objects).
Output monotonicity and inclusion compare reads of one node only within
one epoch; a separate optional entry `catchUp` states that a rejoined
node reaches its last exposed output within a bound (V11). Existing
regimes add `NoRestart`.

**Lift (v1 → v2).** A simulation, not only equal reads: disjoint label
sum; `proposer s` ↦ seat 0 of `prop s`; `proposerOf s` = that seat's
holder; old committee bijections from `CStar`'s proved equivalence (with
the dependent `Fin` casts); old duty and proposal order preserved; no
self-visible labels, `NoRestart`, trivial `durable`. Every v2 run in the
lifted legacy regime has a corresponding v1 run. The lift transports
claim PROPOSITIONS; certificate eligibility (E4, §5) is proved
separately per instance. Scope: the simulation relation, its step
correspondence for each event kind, and the claim transport.

**As implemented in Phase 2a (2026-09-29).** This note does not change
the text above. Plan: `docs/plans/2026-09-29-phase2a-engine-v2-core.md`.
Current API: `docs/V2-API.md`. Report: `docs/PHASE2A-REPORT.md`. The
shapes below record Phase 2a. A current structure, inductive, or definition can
change after review of its statement and dependency diff.

- Libraries. Engine v2 is in `AvailableChainEngineV2` (`Engine`,
  `Conditions`, `Laws`; namespace `AvailableChain.V2`). Its lemmas are in
  `AvailableChainKitV2` (L5; namespace `AvailableChain.V2.Engine`). The
  Framework does not import the Kit. One Framework declaration,
  `AvailableChain.Framework.V2.anchor`, references the 224 engine entries
  of the manifest, so the lock line of the anchor covers them (plan D6).
- E1. `ProtocolSpec (In : Type)` has 24 fields: `State`, `Label`,
  `seats`, `Payload`, `Durable`, `init`, `clock`, `actTime`, `duties`,
  `duties_spec`, `duties_nodup`, `act`, `gossip`, `process`,
  `selfVisible`, `recordOwn`, `durable`, `restore`, `wellFormed`,
  `depsPresent`, `processed`, `excludes`, `handles`, `carries`. The input
  type `In` is a parameter, not a field, so a protocol cannot choose it
  (plan D3); `act : State → Label → In → Option Payload`. `Auth` is
  `seat ℓ i | none`, and a wire object is `Signed` (`auth`, `payload`).
  `Run V P` has `honest`, `horizon`, `events`, `seatOf` and
  `input : V → Time → In`.
- `selfVisible` (the agreed text, plan Task 1 Step 2): "`selfVisible`
  controls the private own-signature record. A normal delivery to the
  emitting node may occur at the emission timestamp, after the tick
  phase."
- Tick. `tick E rho st v t` gives the post-tick state and the released
  objects. It runs `clock`. An awake node then signs, for each label of
  `duties t` and each of its seats, the payload of `act` from the
  post-clock state and `rho.input v t`, in label order and then seat order;
  unsigned gossip follows. Then `recordOwn` is folded over the released
  self-visible objects. An asleep node releases and records nothing.
  Emission is indexed by the tick event (`emitsAt E rho i`), so a restart
  at the same time (phase 0) is included.
- E2. `LabelFamilies P` names three families, `ap`, `fresh` and `linked`
  (each `P.Label → Prop`); it holds no law. `CStar F rho`: every seat map
  of a label of `F` is bijective. `Linked F rho`: one `e : Fin N ≃ V` for
  all labels of `F`, so `Linked` implies `CStar` (`Linked.toCStar`).
  `SingleSeat P F`: every label of `F` has one seat. The FG-SA reference
  assignment: HEAD labels in `ap` and `fresh`; FG labels in `linked`;
  proposal labels in `ap`, with `SingleSeat`.
- E5. `Isolation P F` has data factors and laws. The hook projection
  applies to `F.APObject`: objects signed with an `F.ap` label, and
  unsigned objects (the AP projection emits unsigned gossip). `wellFormed`
  reads no state, so it has no factor. There is no restore law; plan 2c
  adds `RestoreLaw` with `restore_base` and `durable_base` as a separate
  structure. The lemma `base_tick` follows: the base after a tick is
  `clockB` of the base before it.

```text
┌─────────────────────┬──────────────────────────────────────────────────────────┐
│ Field               │ Law                                                      │
├─────────────────────┼──────────────────────────────────────────────────────────┤
│ Base, base          │ the part of the state that the AP protocol reads         │
│ clockB              │ clock_base: base (clock st t) = clockB (base st) t       │
│ processB            │ process_base: for every object, not only AP objects      │
│ (none)              │ recordOwn_base: base (recordOwn st o) = base st          │
│ actB                │ act_base: on F.ap labels; actB takes the input           │
│ gossipB             │ gossip_base: all gossip                                  │
│ depsB, processedB,  │ hooks_base: on F.APObject o, the three hooks equal their │
│ excludesB, handlesB │ factors at base st; handles (a Prop) for both objects in │
│                     │ F.APObject, as an ↔ with the relation handlesB           │
│ (none)              │ separation: F.ap ℓ ∨ F.fresh ℓ → selfVisible ℓ = false   │
└─────────────────────┴──────────────────────────────────────────────────────────┘
```

- E4. `HooksSound P` stays run-level (plan D7). Fields: `excludes_inert`;
  `excludes_stable`, `processed_stable` and `deps_stable` on the
  `restartFree` intervals of every run with `ScheduleWellFormed` (over every
  `V` with `DecidableEq`; v1 also asked for `Fintype V`);
  `handles_carries`; and three own-record laws: `recordOwn_processed` and
  `recordOwn_deps` (equalities) and `recordOwn_excludes` (true stays
  true). `HooksSound` puts no law on a restart.
- Self-delivery (plan D4). `EmitOk E rho st v t o` has four fields: `wire`
  (`wellFormed o`), `deps` (`depsPresent` in the post-tick state),
  `fresh` (not `processed` in the POST-CLOCK state) and `noCarried` (`o`
  carries no object). `selfDelivery_admissible`: if the tick at index `i`
  releases `o` with `EmitOk`, and the state of `v` at index `j` is its
  post-tick state, then a delivery of `o` to `v` at `j` passes the wire,
  dependency and freshness checks of `DeliveryWellFormed` and the checks
  of `UnforgeableSignatures`. It does not claim acceptance by the handler.
  Append form, `ExecutionValid.snoc_selfDelivery`: if `rho` is
  `ExecutionValid`, `HooksSound P` holds, every event key is at most
  `(t, 2)`, the tick of `v` at `t` is at index `i` and no later event is
  of `v`, and `o` is released there with `EmitOk`, then `rho` with
  `.deliver v o t` appended is `ExecutionValid`. `SelfDelivery E rho` is
  an optional condition; the FG-SA regimes do not require it.
- `Interface P`: `confirmed`, `stable`, `block`, `opening`, `propLabel`,
  `propLabel_single` (one seat) and `propLabel_injective` (each slot has
  its own proposal duty, as each slot had its own `Auth.proposer s` in
  v1). It has no proposal schedule and no proposer field: `proposalTime`
  is the act time of `propLabel s`, and `proposerOf` is the holder of its
  one seat. The output reader is `outputAt`; `Run.readAt` is the world
  reader. `RootInjective` holds for every run (`rootInjective_all`).
- `OutputsFactor I iso`: `confirmedB`, `stableB` and the laws
  `confirmed_base`, `stable_base`. So the own record does not change an
  output (`confirmed_recordOwn`, `confirmed_tick` and the `stable`
  forms).
- Delivery conditions. `PartialSynchrony` and `HealthyPrefixDelivery`
  have the v1 texts over v2 runs: `broadcast` of emitted objects and
  `relay` of accepted objects, each with the exemption for an object that
  the receiver excludes at the deadline. There is no other forwarding
  rule (plan D5). `broadcast` includes the emitter, as in v1. With
  restarts, both premises read the receiver's current epoch; restart
  regimes add a rejoin condition (2c). `AcceptedObjectRelay` and
  `HealthyAcceptedObjectRelay` are not ported.
- Restart (reserved, E6). `Event.restart` (phase 0), `durable`, `restore`,
  `NoRestart` and `restartFree rho v i j` (no restart of `v` at an index
  in `[i, j)`) exist. No E6 law, epoch or rejoin condition exists yet.
- Kit v2 restart premises (plan D9). A lemma takes a restore premise:
  `hrestore : ∀ st, Q st → Q (P.restore (P.durable st))` for an invariant,
  and `hrestore_now : ∀ d, C.now (P.restore d) ≤ 0` for a clock lemma.
  `NoRestart` occurs only where a lemma is false after a restart, and in
  the `_noRestart` corollaries. Each stability or invariant lemma also has
  a `recordOwn` premise. With `restore := fun _ => init`, `hrestore` holds
  for every `Q` with `Q init`, and `hrestore_now` holds by
  `ClockLaws.init`.

```text
┌─────────────────────────────────────┬─────────────────────────────────────────────────┐
│ Kit v2 lemma                        │ Restart premise                                 │
├─────────────────────────────────────┼─────────────────────────────────────────────────┤
│ stateBefore_now_le_event            │ hrestore_now; holds across restarts             │
│ stateBefore_now_source              │ hrestore_now; first alternative now ≤ 0         │
│ stateBefore_invariant               │ hrestore and hrestore_now                       │
│ stateBefore_now_mono                │ hrestore_now and restartFree on [i, j)          │
│ stateBefore_stable_clock            │ hrestore_now and restartFree on [i, j)          │
│ stateBefore_stable_clock_restore    │ hrestore_now and hrestore; restarts allowed     │
│ stateBefore_stable                  │ restartFree on [i, j)                           │
│ clock_field_origin                  │ hrestore_field (restore adds no rows)           │
│ stateBefore_field_prefix            │ restartFree on [i, j)                           │
│ stateBefore_field_prefix_restore    │ field st <+: field (restore (durable st))       │
│ delivery_now_ge_public              │ NoRestart (false after a restart)               │
│ stateBefore_tick_eq_stateBeforeTime │ NoRestart (false after a restart)               │
│ ownRecord_fold                      │ NoRestart; ownRecord_fold_interval: restartFree │
└─────────────────────────────────────┴─────────────────────────────────────────────────┘
```

## 3. Instances and facets (L2, L4)

```lean
structure Instance where
  P       : ProtocolSpec
  pparams : ProtocolParams      -- k, L, τ, q, Δ, …: fixed protocol identity
  facets  : FacetBundle P       -- every exposed facet, once
  hooks   : HooksSound P
  deliv   : Deliverable P
  iso     : RecordIsolated P
```

Protocol parameters and facets are bound once. Claim constants are NOT
in the instance; they belong to certificates (§5). So one instance can
hold several certified tradeoff points of one claim (for example SA's P1
with (A, Π) and fast P1 with (A_f, Π); SA-PC recovery at h > a and at
a ≤ f with different ρ).

Facets: `ChainOutputs`, `Proposals` (labels, times, proposal identifier,
`block`, `opening`), `Protected`, `Base`, `Durable`, and the FG facets
of §7. Every output getter reads only `base`. Claims are schemas over
output names. Phase 0 selects an extensible representation for
`FacetBundle`, `FacetNeeds`, `ProtocolParams` and constant records
(typed maps or separate facet records), because adding a field to a
frozen Lean structure changes its declaration.

**As implemented in plan 1a (2026-09-28).** This note does not change
the text above. `ClaimDomain` (`ClaimDomain.lean`) is in place of
`needs` and `FacetBundle`. A claim domain gives the type of the
instances that a claim speaks about and the type of their run contexts.
The v1 claim domain `ClaimDomain.v1` has `Instance` and `V1Ctx` (an
environment and a v1 run). A facet is a structure that extends
`Instance` (for example `StrongInstance` in `Facets/Strong.lean`), with
its own claim domain and a `DomainMap` to `ClaimDomain.v1`. A base claim
and its certificates pull back along the map (`ClaimSpec.pull`,
`Cert.pull`). `Instance` is closed: its fields are `n`, `P`, `Δ`,
`Δ_pos`, `iface` and `hooks`. It has no field for deliverability or
record isolation; eligibility is a separate predicate `Eligible I` (plan
1b). The field `Δ_pos : 0 < Δ` is new: without it, no environment has
the instance's Δ, and every claim holds vacuously.

**As implemented in plan 1b (2026-09-29).** This note does not change
the text above. The Registry has four protocol instances, in
`AvailableChainRegistry/Instances/`. Each is an instance with hooks, not
an eligible candidate: `Eligible I` moved to plan 1c (E4 note).

```text
┌─────────────────────┬─────────────┬───────────────────┬──────────────────────────────┐
│ Instance            │ P           │ hooks             │ holdsAt theorems             │
├─────────────────────┼─────────────┼───────────────────┼──────────────────────────────┤
│ gridInst p          │ gridCO p    │ gridHooks p       │ grid_holds (ac-4.3 at        │
│ (GridCO.Params)     │ (default    │                   │ gridConstants p 1),          │
│                     │ lease       │                   │ grid_holds_core (core.v1 at  │
│                     │ policy)     │                   │ its D_c)                     │
│ saInst p            │ sa p        │ @gridHooks        │ sa_holds, sa_holds_core      │
│ (SA.Params)         │             │ slowLeasePolicy   │                              │
│                     │             │ p.engine          │                              │
│ sapcInst p          │ sapc p      │ sapcHooks p       │ sapc_holds_ac43,             │
│ (SAPC.Params; a     │             │                   │ sapc_holds_strong1,          │
│ StrongInstance)     │             │                   │ sapc_holds_core,             │
│                     │             │                   │ sapc_holds_shared            │
│ lstarInst p n       │ lstar p n   │ lstarHooks p n    │ none: L* has no contract     │
│ (LStar.Params, Nat) │             │                   │ proof                        │
└─────────────────────┴─────────────┴───────────────────┴──────────────────────────────┘
```

- The rows are at the proposer gap `G = 1`. Each has an `_of_pos` form
  for every `0 < G`. `sapc_holds_shared` states both SA-PC profiles at
  one constant, `C := sapcConstants p G`.
- A `holdsAt` theorem proves the claim propositions at one constant,
  without inhabitation (§5). It is not a certificate, and it does not
  make the instance a `Candidate`.
- The core rows use `core_holdsAt_of_ac43`
  (`AvailableChainFramework/Catalog/Relations.lean`): `ac-4.3` at `C`
  gives `core.v1` at `C.D_c`. It is the one lock line that plan 1b adds;
  no lock line changed.
- The Registry shows the theorems as rows of kind `profile-holds`. A
  row whose only binder has a type in the syntactic allowlist
  `familyBinders` (`GridCO.Params`, `SA.Params`, `SAPC.Params`, each
  with a checked witness) is a family row, with status `LEAN (family)`.
  The `_of_pos` rows are CONDITIONAL. `docs/MATRIX.md` shows a family
  row as `holds*`, never as `cert`. `sapc_holds_shared` is a
  conjunction, so it has no row.
- No protocol instance has a certificate. The certificates need
  inhabitation (a run for every horizon; none is proved for these four
  protocols) and, for persistence, a budget above zero, but every
  `Params` allows `η = 0`. Both are inputs for plan 1c.

## 4. Claim catalog (L3)

```lean
structure ClaimSpec where
  id        : Lean.Name
  needs     : FacetNeeds
  Const     : Type                           -- this claim's constants
  valid     : Const → Prop
  le        : Const → Const → Bool           -- decidable; `le c c'`: c' is
                                             -- at least as weak as c
  le_refl   : ∀ c, le c c
  le_trans  : ∀ a b c, le a b → le b c → le a c
  holds     : Instance → Const → Prop
  transport : ∀ I c c', valid c → valid c' → le c c' →
                holds I c → holds I c'
  trigger   : Instance → Const → Run → Prop  -- the claim's trigger occurs
                                             -- with its deadline in the run
  inhabited : Instance → Const → Prop        -- §5
  refutable : RefutationKind
```

- Per-parameter behaviour (audit tables): the claim is weaker when θ ↑,
  θrec ↑, η ↑, A ↑, A_f ↑, ρ ↑, recoveryFull false → true, G ↓, Π ↓,
  faultCap ↓, and D ↑ for persistent inclusion. Exact-time inclusion is
  `fixed` in D: its `le` is equality on D.
- `transport` is a proof, not metadata. Composite comparisons compose
  transports; `le_refl` and `le_trans` make that sound.
- Relation lemmas may combine certificates of ONE instance and require
  equal values for their shared constants. Example:
  `Safe o ∧ included o D ⇒ includedPersist o D` (same D). `Safe o` is one
  conjunction: agreement and per-node monotonicity, as today's `SafeFrom`.
- `includedPersist o D` (B is in every honest read of `o` at every time
  from `s + D` to the horizon) is a DERIVED lemma in `Kit.Core`, not a
  catalog entry: every instance is safe (core floor), so it follows from
  `Safe o` and `included o D` (user decision 2026-09-28).
- Regimes with a minimum horizon (Outage b₁, Recovery GST + ρ, StrongArmed
  b₀) are closed under complete time truncation only above it. Causal
  arguments use separate EXECUTION-PREFIX predicates (L1), not the
  complete-run regimes; an event-list prefix inside one time can break
  `tick_total`.

**Profiles.** A profile is a set of catalog ids plus shared constant
names. A profile certificate is a set of certificates of one instance
that agree on the shared constants. `ac-4.3` is today's bundle: the
equivalence is between claim PROPOSITIONS (`AvailableChain ↔` the
conjunction of the `ac-4.3` `holds`). Eligibility (hooks,
deliverability, inhabitation) is separate, because `AvailableChain`
contains none of it (V07). `strong-1` is `StrongClaims`.

Tiers:

```text
┌──────────────┬───────────────────────────────────────────────────────┐
│ Tier         │ Entries                                               │
├──────────────┼───────────────────────────────────────────────────────┤
│ core (floor) │ Safe(confirmed), Safe(stable), prefix(stable ⪯        │
│              │ confirmed), included(confirmed) under Sleepy          │
│ standard     │ included(stable) under StableSleepy, fast             │
│              │ inclusion, persistence (general, fast), recovered     │
│              │ variants                                              │
│ extra        │ strong claims; base exports; P1 from a recovered      │
│              │ handoff; noFutureRead; catchUp; later additions       │
│ fg-ready     │ AP-side FG entries (FG-COMPOSITION.md)                │
│ composite    │ derived by Kit.Compose (FG-COMPOSITION.md)            │
└──────────────┴───────────────────────────────────────────────────────┘
```

The core is a FLOOR (user decision 2026-09-28): an instance is a
candidate protocol only if it certifies every core claim. A refutation
of a core claim rejects the instance. Selection of claims ("all but
one", optional extras) applies only above the core. The explorer and
the Pareto comparison consider only instances that pass the floor.
Unsafe or not-live protocols are out of scope.

**As implemented in plan 1a (2026-09-28).** This note does not change
the text above. `ClaimSpec K` is generic over a claim domain `K` and has
no `needs` field. `holds` and `inhabited` are definitions over the
fields `regime`, `conclusion` and `trigger`. The trigger takes a time
`H`, and `inhabited` needs the trigger at a time of at least `H` (the
late trigger; I2 in §12). The type does not force this, so each claim
with a trigger other than `True` proves `<claim>_trigger_late`. A
profile has a type of shared constants `Profile.Shared`, and each entry
projects the shared constant to the constant of its claim
(`Profile.Entry.share`). `Profile.valid` holds the conditions between
the constants of different claims. `ac-4.3` (`ac43` in
`Catalog/Profiles.lean`) has `Shared := Constants` and nine claims;
`ac43_iff` is its proposition equivalence with `AvailableChain`.
`strong-1` (`strong1`) has `Shared := Constants × StrongConstants` and
five claims over the strong claim domain; `strong1_iff` is its
equivalence with `StrongClaims`. The standard tier is in
`Catalog/Standard.lean`, the strong claims are in `Catalog/Strong.lean`,
and the core floor is `core` in `Catalog/Core.lean` (`Shared := Time`,
the D of confirmed inclusion).

## 5. Certificates, refutations, registry (L4, L6)

```lean
structure Cert (c : ClaimSpec) (I : Instance) where
  const     : c.Const
  valid     : c.valid const
  inhabited : c.inhabited I const
  proof     : c.holds I const

structure Refutation (c : ClaimSpec) (I : Instance) where
  const     : c.Const
  valid     : c.valid const
  proof     : ¬ c.holds I const
```

**Inhabitation (V07).** `inhabited I c`: for every horizon H there is a
run of I in the claim's regime, with horizon ≥ H, in which the claim's
TRIGGER occurs with its deadline inside the run: for inclusion, an
honest awake proposer slot; for persistence, a non-genesis armed read;
for FG entries, a nonempty source. Boundary cases are allowed (no fault
when the regime forbids one). `Kit.Engine` supplies the runs through the
run-extension theorem (E4). Transport of `holds` does not transport
`inhabited`.

**Refutations.** Finite runs for bounded claims; parameterized finite
families for "no constant works" (as the Sanity theorem does for every
D). Kernel checking with `decide_cbv` or a reflective checker whose
soundness covers the execution, the regime and the failed conclusion;
`native_decide` is not allowed. Executable checkers exist only for
instances with finite representations and equivalence proofs.

**Registry.** Checked attributes (`@[cert]`, `@[refutes]`) verify the
elaborated type, including instance and constants; a theorem with extra
unproved premises is not a certificate. Per instance and claim the
registry keeps the Pareto set of proved constants, the refuted
constants, the proof status (Lean certificate, paper, conditional),
assumptions, output names and module versions. A paper result never
appears as a Lean certificate.

**Current snapshot.** `catalog.lock`: per L1, LM, L2, L3 declaration, a
deterministic hash of the transitive dependency closure (types, bodies,
inductives, opaque bodies via `getUsedConstantsAsSet`; fail if a body is
unavailable). Per L0 and LM version, a recorded content hash. The
toolchain and Lake manifest are pinned. Each certificate records its
instance, constants and dependency hashes. The snapshot is syntactic; it
does not replace kernel checking.

**As implemented in plan 1a (2026-09-28).** This note does not change
the text above. `Cert c I`, `Refutation c I` and `RefutationFamily c I`
take `c : ClaimSpec K` and `I : K.Inst`. `inhabited` needs the trigger
at a time of at least `H` (the late trigger). The Outage persistence
triggers also need `b₀ < b₁`, so that the window is not empty (Review
Focus 6). `ProfileCert p I` has one
shared constant, a proof of `p.valid` for it, and one certificate per
entry at the projection of that constant. The registry is a type scan
(deviation (a)), with the row kind `profile-cert` and the status
`KNOWN-GAP` for the modules under `AvailableChainRegistry.Gaps`. The
lock hashes the closure of each declaration in a fixed order and
compares by name; see the lock change log in §8.

## 6. Kits and explorer (L5, L6)

- `Kit.Engine`: honest origin; transfer within Δ after GST and on a
  healthy prefix; relay closure; clean start; the run-extension theorem
  and inhabitation (E4, §5).
- `Kit.Goldfish`: the substrate of Grid CO, SA, SA-PC and L*. Optional.
- `Kit.FG`, `Kit.Compose`: see §7 and FG-COMPOSITION.md.
- Explorer: executable instances; regime and conclusion checkers;
  refutation files.

**As implemented in plan 1b (2026-09-29).** This note does not change
the text above. Plan 1b made two Lake libraries, both default targets.
`AvailableChainFramework` imports neither.

- `AvailableChainKit` (L5). `Core` (namespace
  `AvailableChain.Framework.Kit`: `includedPersist_of_safe`,
  `block_preceq_trans`) came from `AvailableChainFramework/Kit/`.
  `Engine/{Execution, EngineClock, RunPrefix, HealthyPrefix,
  HealthyInterior, ProtectionInduction, SourceHistory}` (namespace
  `AvailableChain.Engine`) came from the Grid CO library; `Execution`
  was split, and its Grid CO part stays in Grid CO. `Engine/Stable` has
  `stateBefore_stable`, which came from the Registry. The library imports
  only `AvailableChainModel`, `AvailableChainStatements`, Mathlib and its
  own modules.
- `AvailableChainEngineV2` (L0). After plan 1b, its only module was
  `Sketch`, the former `AvailableChainFramework/Engine/V2Sketch.lean`.
  *Correction 2026-09-29 (Phase 2a gate):* Phase 2a did not grow the
  Sketch into engine v2. It wrote engine v2 in new modules (`Engine/*`,
  `Conditions/*`, `Laws/*`), and the gate deleted `Sketch` (`64a48cd`).
  The library has no `Sketch` now. See §2, "As implemented in Phase 2a".
- No name and no namespace changed, with one exception:
  `stateBefore_stable` is now `AvailableChain.Engine.stateBefore_stable`.
  Two lemmas of `Engine/Execution` are no longer private, because the
  Grid CO part uses them.
- No dedupe: the Kit's `block_preceq_trans` and Grid CO's private
  `block_preceq_trans` (`Map.lean`) have different statements, and both
  stay.
- Still open: the Counter run and step helpers (`Counter.lean`,
  `CounterRun.lean`) stay in the Registry. The run-extension work of
  plan 1c generalizes them. `Kit.Engine` has no run-extension theorem
  and no inhabitation lemma yet.

## 7. FG composition: interface shapes

The exact FG statements, their proof status and their sources are in
`docs/FG-COMPOSITION.md`. Each registry entry PINS its statement (full
text and hypotheses, copied), its module variant, and the SHA-256 of the
source file at registration (audit W08). A changed statement is a new
id; a proof-status change is a separate, dated status line. The entries
enter the catalog as versioned ids. This section fixes only the shapes that the
framework must support.

**7.1 Decisions (user).** The FG is our Simplex FG, ONE fixed module:
`SimplexFG.fj` (user decision 2026-09-28: "just fj for now"). NJ is not
formalized now; if the research needs it later, it is a new versioned
module (an addition). DC can be an fj protocol: the module is DC's FG
(without SG and grades) with the FJ root rule in place of NJ ("DC-fj"). The module is FG-ONLY: the AP
(for example SA) enters through the framework interface. FJ is proved
only with the SA base (FG-SA); FJ together with DC's SG (graded fork
choice, safe votes) is NOT checked and needs its own check before any
claim about "DC with SG, fj". Only DC's static FG ports with the fj rule
(client, transition with nj = false, accountable safety, provenance,
causal cap, F2, F10, F12). DC's Lean recovery chain is NJ-only and does
not port; FJ recovery (r148, r151) has no Lean counterpart yet. `SimplexFG.fj` uses the FJ root rule (a frontier test; root F and band
{H} in a contest). FJ changes the frame rule, so it has its own frame
and noninterference interface, not a base-selection plug-in (audit W06). The FJ interface is r148 F9 (the
sources of honest rows at heights ≥ M+1 stay canonical), with the
descent/reset lemma, F10 and F12; it is not HNI. APs vary. FG heights never skip. Every
height pair (target or timeout) needs the AP's source; with none, the
pair is empty. FG interference is relative to a height m. Fallback: an AP
that cannot meet the AP-side entries is certified white-box.

**7.2 Duty frame (LM; audit V09).** `frameOf : View → Frame` returns the
duty frame (F_d, Z_d, H_d, (j_d, J_d), D_d) and the view V_d, with
D_d = {B ∈ V_d : F_d ⪯ B, Z_d ⪯ B, ∃ W ∈ V_d, B ⪯ W ∧ h(W) ≥ H_d − 1}
and Z_d = J_d if H_d = j_d + 1, else F_d. The view is the duty's frozen
view closed under the F basis. This is the R1 VARIANT of DC: DC reads
live control caches; R1 reads the duty view. Two correspondence theorems
(versioned, in `Kit.FG`) relate the frame to the R1 variant of DC's
viable tree and to its filtered tree, separately (the root covers the
prefix up to Z_d). `anchors` (the entries at H_d − 1 in D_d) are a derived
view of the frame; the AP may pick among them with its `AnchorChoice`. The
FG module exports the frame only (Z, lo, D, viability). Head selection
(the walk, its score, and eligibility tests such as a majority or the
current slot) is AP data (user decision 2026-09-28). The FG constrains it
through the AP obligation `ap.headReachesLo.v6` (PROVED-paper; source
`research/async-resilient-committees/tip-stability/blueprint/21-healing.md`,
"Registry restatement — ap.headReachesLo.v6", 2026-09-29). The
blueprint states it as follows. Authority is the current spec 4e85ff34.
Clauses 1–3 use its live-cache FJ frame, frozen voter domain,
full-domain live start, and exact HEAD merge. Clauses 4–6 use Recovery₂
(`a≤f`, `R≥2`, `δ_t=2R`), strict receipt `<Δ` with receiver exclusion,
and the stated phase premises.

1. If start A is in `D(V_s)`, or has an eligible child there, the HEAD
   is in `D(V_s)` at height at least lo.
2. Otherwise the HEAD is A, including when `D(V_s)` is nonempty.
3. If A=Z and `D(V_s)` is nonempty, Z belongs to `D(V_s)`.
4. In a settled phase, every honest HEAD K has a full-store witness
   `W⪰K` with `ht(W)≥lo`. Every honest receiver admits W and its path
   before `e_s`; for a protected prefix of K use admission or finality
   coverage. This does not assert `ht(K)≥lo` for an outside start.
5. Let β be the first proposal label strictly after settlement u and
   `ℓ=β+2k−1`. Every honest P at `t_s>t_ℓ` has exact HEAD and fresh
   fast-write service if the phase persists through d_s. Such a gate
   occurs by `u+ρΓ`, or the phase stops sooner. Service continues for
   later honest proposals in that phase. Equal scores are required
   only on the retained comparison suffix, with H.5's path premises.
6. Evidence first accepted at `w≥GST` is in all full stores before
   `w+Δ`, and in every HEAD view with `v_s≥w+3Δ`, unless a frontier
   rise ends the task. Thus one effective event costs `θ=3Δ` before
   repair starts. Lower F moves and individual outside-start returns
   do not add event charges. A later effective event stops the attempt.

Thus the HEAD is in D with height ≥ lo only under clause 1; clause 2
keeps the outside-start exception (the HEAD is A), and clause 4 gives
a witness, not `ht(K)≥lo`. `ap.headReachesLo.v5` is WITHDRAWN for
current use; it is still true in its stated scope (R ≥ 3, θ = 4Δ, spec
bd942ca0). v6 is its successor with changed hypotheses, not a SUPERSEDED
replacement (§10).

*History (text to 2026-09-29, replaced by v6):* "The FG constrains it
through one generic AP obligation (`ap.headReachesLo.v1`, both
phases): for each duty view, the AP head read from it is in D and has
state height ≥ lo. A weaker "the head may leave H−1" form is not enough:
a tie rule or a filter can still stall (N12). SA discharges it with its
walk (start at the live root; below lo a child is eligible without a
majority; every viable node below lo has a viable child in D)."

*Note 2026-09-29 (STALE, marked for correction; DC-simplify, modular-spec
study `research/async-resilient-committees/tip-stability/codex/scratch/
modular-spec-study.md` item 9):* the obligation above ("the AP head read
from each duty view is in D with height ≥ lo") is false for the current
FG-SA design, because 21 H.3 permits an outside-anchor return. The duty
view frame is also older than the spec frame, which reads live caches and
"never reads a view" (spec 749–752). The section stays as history until the
FG interface is restated with the F0 channel files (ARCHITECTURE.md §2).
*Resolved 2026-09-29 by `ap.headReachesLo.v6`:* the unconditional
obligation is replaced by the v6 clauses above, which keep the
outside-start exception and use the live-cache FJ frame of spec 4e85ff34.
The `frameOf` text at the start of §7.2 still describes the duty-view
frame; it changes when the FG interface is restated with the F0 channel
files.

**7.3 AP template and policy type (LM; audit V10).**
- `Policy`: the type of honest FG signing rules. A policy reads the FG
  sub-state, the record, and the AP facets through `base`; it emits
  objects only on the FG label family (`Linked`); it writes only the
  record. The AP transitions are fixed.
- `APTemplate`: an AP spec with a policy slot. `inst T σ : Instance` is
  the composite for policy σ.
- An AP-side certificate is a FAMILY certificate (audit W02):
  `FamilyCert c T := { const, valid, proof : ∀ σ : Policy, c.holds (inst T σ) const,
  inhabited : c.inhabited (inst T simplex) const }`. The proof is uniform
  over σ; the witness is required only for the Simplex policy.
- Family entries state only AP SERVICE facts: repair within ρ, production
  of a common source, carrier and row service, source safety. They never
  state FG progress (a height rise): an arbitrary policy can withhold all
  progress rows. So (L) splits: its service part (repair by u+ρ, a
  common fresh source, row folding, carrier retention) stays in `ap.*`
  entries, and the rise moves to `comp.rise.*` entries. Height progress, and every Simplex law (provenance,
  quorum uniqueness, causal cap, no slashing), are derived in
  `Kit.Compose` after specialization to the Simplex policy.

**7.4 Composition (`Kit.Compose`).** It combines AP-side certificate
families, specialized to the Simplex policy, with `Kit.FG` lemmas, in
the causal induction over execution prefixes, with separate invariants
for clean history, post-reset source history (per-body first-transfer
time), and armed-prefix Outage history (V03). Base selection returns a
witness record, not a bare condition (audit W09): the causal cut M, a
height x > M, the first honest row above x after the cut with its
first-transfer view facts, and the arm witness (the NJ prefix record
facts, the actual finalized checkpoint F*, or the FJ facts of its
variant). Run-wide HNI is DERIVED inside the joint induction, not taken
as an input. Its outputs are the
composite entries of FG-COMPOSITION.md (`comp.fgHealed`, `comp.healed`,
and finality entries that stay conditional until their timed
obligations are proved).

## 8. Migration (phases)

```text
┌───┬───────────────────────────┬─────────────────────────────────────────┐
│ P │ Work                      │ Acceptance                              │
├───┼───────────────────────────┼─────────────────────────────────────────┤
│ 0 │ Compiled prototype on v1: │ Instance, ClaimSpec with transport and  │
│   │ interfaces, extensible    │ trigger, Cert, profiles, a type-        │
│   │ facet and constant        │ scanning registry, not attributes; a    │
│   │ records, facets as type   │ Pareto comparison; catalog.lock over    │
│   │ classes, core claims,     │ statements only, not proofs; Safe and   │
│   │ Sanity and Counter        │ included certified for Counter and      │
│   │ instances, a toy E4       │ refuted for Sanity; E4 checked for a    │
│   │ classification, a toy     │ Grid CO variant (Deliverable,           │
│   │ E5/E6 step, the run-      │ RelayFeasible, WindowMargin to Phase    │
│   │ extension theorem         │ 1); the theorem from genesis only, the  │
│   │                           │ Counter canonical run; ProfileCert and  │
│   │                           │ Candidate in Type 1                     │
│   │                           │ not delivered: (g) shared constants     │
│   │                           │ (Profile has no ProtocolParams); (h)    │
│   │                           │ HooksSound has no depsPresent; (i)      │
│   │                           │ HooksSound is run-level, not per-step   │
│   │                           │ (letters as in PHASE0-REPORT.md §5.1)   │
│ 1 │ Full catalog on v1        │ ac-4.3 and strong-1 proposition         │
│   │                           │ equivalences; eligibility per migrated  │
│   │                           │ instance; MATRIX.md; build --wfail      │
│ 2 │ Engine v2 + lift          │ v1 propositions transported; a toy      │
│   │                           │ Linked, self-visible, restart protocol; │
│   │                           │ finite checked v2 traces: the 2a toy    │
│   │                           │ runs `toyRun` (a self-delivery at the   │
│   │                           │ emission time) and `pre` (append form), │
│   │                           │ `AvailableChainKitV2/Tests/Toy.lean`    │
│   │                           │ (2026-09-29); one trace per migrated    │
│   │                           │ real instance (2b)                      │
│ 3 │ Kits, explorer, checker   │ r107, Sanity, Accumulation, CE-1        │
│   │                           │ rediscovered                            │
│ 4 │ LM Simplex FG, frames,    │ correspondence theorems; FG-COMPOSITION │
│   │ policy, template; Kit.FG; │ entries at the status the research has  │
│   │ Kit.Compose; FG-SA        │ reached                                 │
└───┴───────────────────────────┴─────────────────────────────────────────┘
```

**Row 0 deviations after plan 1a (2026-09-28).** (d) superseded by claim
domains (plan 1a); (g), (h) delivered (plan 1a); (i) kept.

Phases 0–2 land before the FG-SA Lean instance starts.

**Order after plan 1b (2026-09-29; user, DC-simplify, Astra
`docs/audit/phase2-order-check-report.md`).** The FG-SA store merge, then
the I9 plan, then Phase 2 (2a: core, E1, E2, E5, with the NoRestart,
`durable` and input interfaces reserved; 2b: the lift; 2c: E6, the toy
protocol, I1 with a versioned floor), then plan 1c on engine v2. The Phase 1
acceptance item "eligibility per migrated instance" is OPEN and moves to
plan 1c; until then MATRIX shows `holds*` and no protocol certificate. The
FG-SA run lift (T7) is on v2 and can start after 2a. Details:
`docs/PHASE1B-REPORT.md`.

*Planned item, not scheduled (2026-09-29, user decisions via DC-simplify):*
anchor and pruning, as an OPTIONAL CLAIM. A protocol may prove "prunable at
F": every later read and output does not change when the store prunes below
F as F advances. A protocol may also start from an anchor (a block and its
chain state) instead of genesis; genesis is the special case. This is not an
engine or protocol obligation: a protocol that does not make the claim
changes nothing, and the target for such protocols is zero changed lock
lines. For FG composites the claim gives the faithful E6 restart form.
Inputs: a protocol study (r207, `codex/pruning-rule.md`, landed; an Opus
red-team runs), an extraction of the decoupled-consensus pruning method, and
a Lean design and impact study (fgsa-impl). Its place in the order is decided
when these land (after I9 and 2a).

**Lock change log.**
- 2026-09-28, approved by the user. The receipt-relay merge (`1a3f73a`, r162)
  removed the `acceptedRelay` field from `SleepyRegime`. The regimes now use
  DC's receipt premise. Eight L3 lock lines changed: `sleepy`, `safeOf`,
  `safeStable`, `safeConfirmed`, `includedConfirmed`, `core`, `Candidate` and
  `not_candidate_of_family`. The premise is weaker, and no conclusion
  changed. All certificates still hold (`docs/REGISTRY.md`: 8 rows, all
  LEAN). The lock was rewritten in place, with no new ids. This entry
  records the change.
- 2026-09-28, format change (plan 1a Task 0): order-independent hashes,
  generated names by metadata, claims always locked, a separate axiom
  check. No declaration changed; every line hash changes because the hash
  function changed; lines of generated names are gone. The own hash of a
  declaration includes a tag for its kind (definition, opaque, theorem,
  axiom, inductive, constructor, recursor, quotient). The old lock is git blob
  `0cd36b38defadd055c6ecde9422eb9e3ad78d734` (188 lines); the new lock has
  87 lines, all with a new hash. Removed generated names (101): for
  `Cert`, `ClaimSpec`, `HooksSound`, `Instance`, `Outcome`, `Profile`,
  `Refutation`, `RefutationFamily`, `RefutationKind` and `Validators`, the
  `rec`, `recOn`, `casesOn`, `ctorIdx`, `noConfusion`, `noConfusionType`,
  `mk.inj`, `mk.injEq`, `mk.noConfusion`, `mk.sizeOf_spec`, `ctorElim`,
  `ctorElimType`, `ofNat`, `ofNat_ctorIdx`, `toCtorIdx`, `<ctor>.elim` and
  `<ctor>.sizeOf_spec` that Lean made for each, and
  `ClaimSpec.stronger.eq_1`. Two writes (426009e, blob 464f709; 6b7155a,
  blob 2e79312, which added the kind tag).
- 2026-09-29, the gate of plan 1a (Tasks 1–5), approved by the user with the
  plan on 2026-09-28. This is the one approved break of the gate. The old
  lock is git blob `2e7931279eae4bb2763e45571bf4f019278d59d0` (87 lines, the
  Task 0 lock); the new lock has 141 lines. `CatalogLock --check` against
  the old lock gave 66 `CHANGED`, 1 `REMOVED` and 55 `ADDED` names, listed
  below. All names are under `AvailableChain.Framework`; `Catalog.` is
  `AvailableChain.Framework.Catalog.`. A declaration with the same source
  can change its hash through a dependency (for example `sleepy` through
  `Instance`).
  - `CHANGED` (66):
    `Catalog.{Candidate, core, includedConfirmed, not_candidate_of_family,
    prefixOrder, safeConfirmed, safeOf, safeStable, sleepy}`;
    `Cert` and `Cert.{const, inhabited, mk, not_refuted, proof, valid,
    weaken}`;
    `ClaimSpec` and `ClaimSpec.{Const, Point, conclusion, holds, id,
    inhabited, le, le_refl, le_trans, mk, pareto, pareto_covers, pareto_sub,
    refutable, regime, stronger, stronger_count_lt, stronger_irrefl,
    stronger_trans, transport, trigger, valid}`;
    `HooksSound` and `HooksSound.{excludes_inert, excludes_stable,
    handles_carries, mk, processed_stable}`;
    `Instance` and `Instance.{P, hooks, iface, mk, n, Δ}`;
    `Profile` and `Profile.{id, mk}`;
    `ProfileCert`;
    `Refutation` and `Refutation.{const, family_of, mk, proof, valid}`;
    `RefutationFamily` and `RefutationFamily.{mk, proof}`.
  - `REMOVED` (1): `Profile.claims`. Task 2 replaced the claim list with
    `Profile.entries` (claims with the projection of the shared constants).
  - `ADDED` (55):
    `Catalog.{includedConfirmed_holds_iff, includedConfirmed_inhabited_iff,
    includedConfirmed_trigger_late, prefixOrder_holds_iff,
    prefixOrder_inhabited_iff, safeConfirmed_holds_iff,
    safeConfirmed_inhabited_iff, safeStable_holds_iff,
    safeStable_inhabited_iff}`;
    `Cert.pull`;
    `ClaimDomain` and `ClaimDomain.{Ctx, Inst, admissible, horizon, id, mk,
    ofV1, strong, v1}`;
    `ClaimSpec.{holds_pull, inhabited_pull, pull}`;
    `DomainMap` and `DomainMap.{admissible, ctx, horizon, inst, mk, ofV1,
    strongV1}`;
    `HooksSound.deps_stable`;
    `Instance.Δ_pos`;
    `Profile.{Entry, Entry.mk, Entry.share, Entry.spec, Shared, entries,
    holdsAt, valid}`;
    `ProfileCert.{certs, holdsAt, mk, shared, valid}`;
    `StrongInstance` and `StrongInstance.{mk, sface, strong, toInstance}`;
    `V1Ctx` and `V1Ctx.{E, mk, rho}`.
  - Changed L3 declarations, old and new type (old: `426009e`):
    - `safeConfirmed`, old: `ClaimSpec`, with `regime` and `conclusion`
      over `E : Env W.V` and `rho : Run W.V I.P`.
      New: `ClaimSpec ClaimDomain.v1`, over `x : V1Ctx I W` (`x.E`,
      `x.rho`); `trigger` also takes the time `H`.
    - `safeOf`, old: `safeOf (id : Lean.Name) (g : (I : Instance) → Output
      I.P) : ClaimSpec`.
      New: the same arguments, returns `ClaimSpec ClaimDomain.v1`.
    - `safeStable`, old: `ClaimSpec` (as `safeConfirmed`).
      New: `ClaimSpec ClaimDomain.v1` (as `safeConfirmed`).
    - `prefixOrder`, old: `ClaimSpec`, `regime` and `trigger` are `True`.
      New: `ClaimSpec ClaimDomain.v1`, `regime` and `trigger` are `True`.
    - `includedConfirmed`, old: `ClaimSpec`, trigger `∃ s, t₀ <
      proposalTime s ∧ HonestAwakeProposer E rho s ∧ proposalTime s + D ≤
      rho.horizon`.
      New: `ClaimSpec ClaimDomain.v1`, trigger with `H ≤ proposalTime s`
      added (I2; `includedConfirmed_trigger_late`).
    - `core`, old: `Profile`, `claims := [safeConfirmed, safeStable,
      prefixOrder, includedConfirmed]`.
      New: `Profile ClaimDomain.v1`, `Shared := Time`, `valid D := 0 ≤ D`,
      the same four claims as `entries`; `includedConfirmed` gets `D`.
    - `Candidate`, old: `Candidate (I : Instance) : Type 1 := ProfileCert
      core I`, with `ProfileCert p I := ∀ c ∈ p.claims, Cert c I`.
      New: `Candidate (I : Instance) : Type 1 := ProfileCert core I`, with
      `ProfileCert` a structure: one `shared` constant, `valid`, and a
      certificate per entry at `e.share shared`.
    - `not_candidate_of_family`, old: takes `c ∈ core.claims` and
      `RefutationFamily c I`, gives `Candidate I → False`.
      New: takes `e ∈ core.entries` and `RefutationFamily e.spec I`, gives
      `Candidate I → False`.
  - No certificate conclusion changed. The `id`, `holds` and `conclusion`
    of each core claim are the Phase 0 ones (`Catalog/Meaning.lean` pins
    `holds` and `inhabited`). The Counter certificates `certSafeConfirmed`,
    `certSafeStable`, `certPrefix` and `certIncluded`, and the Sanity rows,
    certify the same claim ids as at `426009e`. The registry has no Grid CO
    certificate (`GridCOHooks` gives a `HooksSound` value only). What
    changed is on the premise side: `includedConfirmed` inhabitation needs a
    proposal at a time of at least `H` (the Counter certificate was rebuilt),
    `Instance` needs `Δ_pos`, and `HooksSound` needs `deps_stable`.
  - Note (2026-09-29, plan 1b). `GridCOHooks` as named above is gone:
    plan 1b Task 1 removed `gridCOx` and `gridCOx_hooks`. The registry
    still has no Grid CO certificate. It now has the instance `gridInst`,
    with the hooks `gridHooks` of `gridCO` itself, and `profile-holds`
    rows for it (§3 note).
  - Registry after the regeneration (`docs/REGISTRY.md`, 16 rows): Counter
    4 `cert` rows and `candidate` (`profile-cert`, `core.v1`), all `LEAN`;
    `Gaps.NoInput` 4 `cert` rows and `clockCandidate` (`profile-cert`,
    `core.v1`), all `KNOWN-GAP`; Sanity 3 `cert` rows and 1
    `refutation-family` row, all `LEAN`; `Tests.certSafeStableStrong`
    (`safeStable (pulled)`) and `Tests.refutedBadStrong` (`testStrongSafe
    NON-CATALOG`), both `LEAN`. New row kind `profile-cert` (for
    `ProfileCert K p I` and `Candidate I`; the claim column shows the
    profile `id`). A pulled claim shows its base claim and `(pulled)`.
- 2026-09-29, plan 1b Task 4 (`06a5267`): one `ADDED` line,
  `AvailableChain.Framework.Catalog.core_holdsAt_of_ac43`, written with
  `--write` and no `--allow-changes`. No line changed, and no line was
  removed.
- 2026-09-29, I9 Task 11 (derived roots, §12; user decisions
  2026-09-29): 91 `CHANGED` lines, 0 `ADDED`, 0 `REMOVED`, written with
  `--write --allow-changes` on the tree with main merged in (`f756404`).
  The old lock is git blob `6a4d14869c409efa92f1c27cf3ce7a7d2bebc773`
  (250 lines); the new lock has 250 lines. Reason: the closure of each
  line reaches `Block`. `Block.node` has no root field now, and
  `Block.root` is derived from the content. No file of
  `AvailableChainFramework/` changed (`git diff main`), so no locked
  declaration changed its source text or its type. The changed or new
  definitions that the 91 closures reach are only these: the
  constructor `Block.node` and the declarations that Lean generated for
  `Block` (`rec`, `casesOn`, `below`, `brecOn.go`, the matchers of
  `preceq` and `slot`, and `DecidableEq`); `Block.root` and
  `Block.root._f`; `nodeRoot`; and the codec `epair`, `lpair`, `bitLen`,
  `bitLenDouble` and `bitLenSearch`. The closures also reach
  `BlockId.value` and the core `ShiftRight` instances, which did not
  change. The names are the 91 rows of `docs/plans/i9-lock-expected.tsv`
  (set equality with the `--check` output): 69 `Catalog.` names, and
  `Instance` and `Instance.{P, hooks, iface, mk, n, Δ, Δ_pos}`;
  `StrongInstance` and `StrongInstance.{mk, sface, strong, toInstance}`;
  `V1Ctx` and `V1Ctx.{E, mk, rho}`; `ClaimDomain.{ofV1, strong, v1}`;
  `DomainMap.{ofV1, strongV1}`.
- 2026-10-05, ROOT-DIGEST-2 option 3: source base `c24711d`, integration base
  `f106ff8`, and W3b input `54e6aa4`. The result is an uncommitted working tree;
  the owner makes the commit. The measured catalog set has 0 CHANGED, 0 REMOVED,
  and 0 ADDED names. All 252 hashes and the lock bytes remain unchanged.
  The prior 77-name prediction came from 78 internal declarations that the old
  type snapshot omitted. That prediction treated absent names as changes.
  The exact root-to-cause map clears all 77 false positives. No lock write is needed.
  FG-SA has 919 CHANGED and 46 ADDED frozen entries; Gen has 125 CHANGED and
  37 ADDED entries; v2 has no delta from the source base. The option-3 exception,
  the 64-entry Gen mode extension, and the prior named exceptions remain recorded.
  The compact [ROOT-DIGEST-2 record](lock-log/root-digest-2/README.md) contains the
  exact names, hashes, causes, public-type comparison, axiom sets, and final checks.
  Large type records and command logs are held for owner transfer to
  `TS/codex/reports/rdigest2/w3c/`. The owner must check the committed-tree self-test
  after the commit if the working-tree run reports a HEAD snapshot failure.
  Current results: all 31 old equation keys are hidden; all 133 E1 public types stay.
  The full build and Claims shake pass. Full acceptance remains open on the new
  Hooks equation export, stale HeadMode arguments in two gate fixtures, and the
  committed-HEAD EOF whitespace. The (j) self-tests pass; the working EOF fix is ready.
- 2026-10-04, ROOT-DIGEST W3b/W3c (user option 3; plan §2 and r2.1–r2.3):
  93 CHANGED lock lines, no REMOVED or ADDED line. Cost/source base: `98a62cd`.
  W3b input: `027f2f1`; W3c input: `b4bf03f`. W3c changes are not committed.
  The expected set is the 91 I9 closure names plus `V2.anchor` and `V2.dutyAnchor`.
  Set equality was checked before the W3b `--write --allow-changes`.
  The closure change comes from explicit Block roots, Params.digest, generated constructor
  helpers, and the two approved anchor-reference deletions. The BODY codec stays.
  Exact names, old/new hashes, frozen classifications, exceptions, and the W3c check summary
  are in [the compact ROOT-DIGEST record](lock-log/root-digest/README.md).
  It includes all four r2.1/r2.2 Gen walk entries, the r2.3 CPPrefix scope restriction,
  and the retained GUP/LIVE-DC/TF-SEED exceptions. Large census and declaration-delta
  files and supporting audits are held for owner copy to `TS/codex/reports/rdigest/w3c/`.
  Both W3b fixture STOPs are closed. The Claims idealization uses local finite certificates.
  Full acceptance stays open: `WeakContinuationW1` does not build. The exact base precheck
  also fails on committed W3b census whitespace. The default checker self-test still lists
  the moved files. No checker rule changed. The compact summary keeps each real exit code.
- 2026-09-29, the Phase 2a gate (`fa190ec`; plan D6): one `ADDED` line,
  `AvailableChain.Framework.V2.anchor d7bf19c118bcf687`, written with
  `--write` and no `--allow-changes`. `lockedModulePrefixes` gained
  `AvailableChainFramework.V2`. No line changed, and no line was removed;
  the lock has 251 lines. The closure of the anchor contains the 224
  engine entries of `docs/V2-API.md`, so a change to one of them gives a
  `CHANGED` line. `64a48cd` deleted the Sketch and changed docstrings only;
  the anchor line did not change.
- 2026-09-29, the port to Lean v4.34.1 and mathlib d13f23b7 (branch
  `port-v434`). Re-baseline approved by the user, 2026-09-29 (relayed by
  DC-simplify); the axiom-set change below accepted by DC-simplify,
  2026-09-29. Written with `--write`: 193 `CHANGED` lines
  of 251, 0 `ADDED`, 0 `REMOVED`. The old lock is git blob
  `1626dc7494e8190bcb8e69c5c8369fe6e0902af7` (251 lines, `a6733c2`).
  Evidence files are in `docs/lock-log/v4.34.1/`:
  - The port commit changes no file of `AvailableChainFramework/`. The
    local-closure lock (`CatalogLock --local`: the closure stops at
    non-project constants, which are hashed by name) is the same on both
    toolchains: `local-lock-rc2.lock` and `local-lock-v4.34.1.lock`, 0 of
    251 lines differ.
  - `lock-diff-causes.txt`: each of the 193 lines with its old and new hash
    and its cause. A line changed if and only if its closure reaches one
    of 21 core or Mathlib constants whose own hash changed (193 of 193
    lines explained; no unchanged line reaches one). The 21: `Finset`,
    `Finset.mk`, `Finset.val`, `Finset.instSetLike` and its `_proof_1`
    (Finset is now `SetLike`); `Fintype`, `Fintype.mk`, `Fintype.elems`,
    `Fintype.card`; `Bool.and`, `Bool.or`, `Bool.not`, and the removed
    `Bool.and.match_1` and `cond.match_1`; `Rat.instDecidableLe`;
    `Nat.instDecidableCoprime` and its two removed proofs;
    `List.get!Internal._f`; `setOf` (removed) and `Set.ofPred` (new). No
    project constant is a cause.
  - `docs/V2-API.md`: 5 of 280 hashes re-written, all derived instances:
    `instDecidableEqAuth`, `instReprAuth`, `instDecidableEqSigned`,
    `instReprSigned`, `instDecidableEqEvent` (`manifest-diff.txt`). Cause:
    Lean v4.34.1 gives derived instances the new reducibility status
    `instanceReducible` (rc2: `implicitReducible`), and `V2Manifest` hashes
    the status (tag 4 → 5). With the old tag, the listing is byte-identical
    to rc2. The tag stays distinct, so that the change is visible.
  - Axiom sets: 21 of 1182 `#print axioms` lines change from `[propext,
    Quot.sound]` to `[propext, Classical.choice, Quot.sound]`
    (`print-axioms-rc2.txt`, `print-axioms-v4.34.1.txt`,
    `print-axioms-diff.txt`). The theorems: `Engine.{eventIndex_lt_of_time_lt,
    prefixEnv_execution, prefixEnv_schedule, state_interval_induction,
    tick_index_lt_delivery}`; `FGSA.{accepted_rows_decode,
    blockAccepted_facts, blockAccepted_of_wellFormed, blockAccepted_rowsOk,
    compatible_iff_eraseFG, eraseFG_ancestor_mem, eraseFG_ancestor_preceq,
    eraseFG_injOn, fgBlock_notMem, metaInv_init, parentFG_spec,
    pickPair_some_spec, preceq_of_eraseFG_preceq,
    rootInjectiveOn_of_viewRootInj, viewRootInj_of_rootInj}`;
    `SAPC.emitted_seat_unique` (prefix `AvailableChain.`). Each gains
    `Classical.choice` through Mathlib `Finset.instSetLike`, directly or
    through `ScheduleWellFormed.mk` and `FGSA.blockAccepted`, whose types
    use Finset membership (`axioms-choice-trace.txt`). No port edit adds
    choice. The allowed set {propext, Classical.choice, Quot.sound} is
    unchanged, and every axiom script passes.
  - Statement census (`scripts/StmtCensus.lean`, rc2 against v4.34.1): no
    edited declaration changed its type or value. 36 names differ for
    Mathlib and core reasons only: 27 where Finset `⊆` now elaborates as
    `≤`, 4 `Finset.partialOrder` → `Finset.instPartialOrder`, 1 test value
    (`Monoid.toPow` → `Monoid.toNPow`), and 4 removed core aliases
    `toCtorIdx`.

## 9. Changes to standing rules (approved by the user 2026-09-28)

- `AGENTS.md`: "Keep [the engine] close to that source" becomes "Engine
  v2 is the reference; changes need a lift simulation".
- `CONTRACT.md`: "one bundle every instance proves" becomes "catalog,
  instances and profiles"; Draft 4.3 stays as profile `ac-4.3`.

## 10. Open items

- Recommendation: stop paper audits here and let Phase 0 test the
  interfaces with the Lean compiler (the audits' own recommendation). The
  FG interface shapes (§7) stay DRAFT until Phase 4; the core (§0–§6)
  is ready for approval.

- User decisions (2026-09-28): core §0–§6 APPROVED; §9 rule changes
  APPROVED; core tier = floor of safety + confirmed inclusion (§4).
- Stale FG pins (2026-09-29, modular-spec study item 9; fix in the FG-SA
  spec-sync task after the I9 merge, because I9 changes `Pins.lean`):
  `fj.descent.v1` and `fj.twoChanges.core.v1` use duty-view frames (restate
  over the node store T; `fj.descent` also lacks case (2), the contested
  floor); `ap.headReachesLo.v5` keeps R ≥ 3 and θ = 4Δ, while 21 H.8 proves
  3Δ at R ≥ 2; §7.2's generic AP obligation is false (note there).
  Statuses (2026-09-29, after the I9 merge): `fj.descent.v1` and
  `fj.twoChanges.core.v1` are WITHDRAWN for current use.
  `ap.headReachesLo.v5` is also WITHDRAWN for current use (registry policy,
  FG-COMPOSITION §0: a change of statement or hypotheses gets a new id). It
  is still true in its stated scope (PROVED; R ≥ 3, 4Δ, spec bd942ca0). Its
  successor is `ap.headReachesLo.v6` (spec 4e85ff34, R ≥ 2, strict receipt,
  θ = 3Δ; §7.2). None of the three is SUPERSEDED. The Lean `Pins.lean`
  update belongs to the FG-SA re-pin commit (session fgsa-lean).
- FG research (tracked in FG-COMPOSITION.md): r149 (strengthened (S),
  (S_slow), (L), (X)); r148 (FJ root rule); "ρ once globally"; full
  healing at q_s*; the timed finality obligations.

## 11. Audit disposition

```text
┌──────┬──────────────────────────────────────────────┬──────────────────┐
│ ID   │ Fix                                          │ Where            │
├──────┼──────────────────────────────────────────────┼──────────────────┤
│ v4 B01, V08 │ protocol params and facets per       │ §3, §4, §5       │
│      │ instance; constants per certificate; Pareto  │                  │
│ v4 B02 │ exact inclusion fixed in D; persistent     │ §4               │
│      │ inclusion; Safe-premised relation lemma      │                  │
│ v4 B03, V01, V07 │ delivery outcomes; accepted-     │ E4, §5           │
│      │ dependency deliverability; run extension;    │                  │
│      │ trigger witnesses; propositions vs           │                  │
│      │ eligibility                                  │                  │
│ v4 B04–B06, V02–V06 │ exact FG statements moved to  │ §7,              │
│      │ FG-COMPOSITION.md (r147 N1/N2/Ret, HNI(m),   │ FG-COMPOSITION   │
│      │ body-level (S), separate invariants, row     │                  │
│      │ service, carrier keep, conditional finality) │                  │
│ V09  │ duty frame with Z; viable and filtered       │ §7.2             │
│      │ correspondences; R1 variant named            │                  │
│ V10  │ policy type, AP template, certificate        │ §7.3             │
│      │ families, specialization rule                │                  │
│ V11, v4 M02 │ restore law, hook projection, AP     │ E5, E6           │
│      │ label family, epochs, fold order             │                  │
│ V12, v4 N01 │ status moved to FG-COMPOSITION.md;   │ §10, FG-COMP.    │
│      │ exact versioned statements, no shorthand     │                  │
│ v4 M01, M03, M07, M08, M09, N02 │ fixed in v5      │ —                │
└──────┴──────────────────────────────────────────────┴──────────────────┘
```

## 12. What certificates do not cover

Validity of execution data; data availability or possession; conformance
of a deployed client (implementation refinement). These need their own
entries or a separate refinement project. `noFutureRead` is an
extra-tier entry.

**Known gaps after Phase 0 (status after plan 1a)**

- I1 (reasoned in Phase 0; compiled in plan 1a; open): a protocol that
  reads no input can still pass the core floor (honest
  `propose` has no input, so proposals are predictable). Fix: engine v2
  gives the proposer a run-chosen input (Phase 2).

  Status (plan 1a, 2026-09-28): compiled in
  `AvailableChainRegistry/Gaps/NoInput.lean` (Task 5, `3c76e2b`).
  `clockChain` reads no input, and `clockCandidate` shows that it passes
  the core floor at `D = 0`. Its registry rows have the status `KNOWN-GAP`
  (Task 0, `gapsPrefix`). The gap stays open until plan 2. A run input
  alone is not enough (Astra A05). Plan 2 also needs a floor claim that
  binds the proposal to the input, and a refutation of `clockChain` as its
  regression test.

- I2 (closed in plan 1a): `Claim.inhabited` accepts one early trigger for all H
  (`CounterIncluded.lean:228` always uses slot 1). Fix: require the
  trigger at a time ≥ H; changes the L3 lock and two certificates.

  Status (plan 1a, 2026-09-28): closed by Task 1 (`0e6898e`).
  `ClaimSpec.trigger` takes a time `H`, `inhabited` needs the trigger at a
  time of at least `H`, and each catalog claim with a trigger other than
  `True` proves `<claim>_trigger_late`. The Counter certificate
  `certIncluded` uses a proposal slot at a time of at least `H`.

- I9 (reasoned; a `decide` check in the async session's scratch): every
  regime has the premise `RootInjective` (`Generic/Conditions.lean:28`),
  but the honest root formula `s * (parent.root + 1)` (Grid CO
  `Model/Protocol.lean:291`; SA, SA-PC `Choice.lean:87` and L*
  `Protocol.lean:258` reuse this form) collides on forks: slot 4 on
  genesis and slot 2 on the slot-1 block both get root 4; and a faulty
  slot-7 block with root 7 gives its honest slot-8 child root 64, the
  root of the honest slot-4 block on the chain 1, 4, 15, 64. So an
  adversary can leave every regime, and the certificates give no
  guarantee against a forged collision. The theorems stay sound. Fix (a
  design decision for the user, with a proper audit; it changes the
  protocol libraries): content-coded roots checked at admission (FG-SA
  plan D4), so that `RootInjective` follows from admission. Not in plans
  1a, 1b or 2 until decided.

  Decided 2026-09-29 (user): a derived root `root(B) := H(content)` with
  `H` injective. A block carries its parent's root, and the store accepts
  a block only when it knows a parent with the carried root (dependency
  lookup). This changes the shared `Block` type, so it is a contract and
  lock break. It gets its own plan and a full audit after plan 1b.

  Point 2 of the decision (2026-09-29, user, via DC-simplify): the
  parent-root check is the store dependency lookup
  (`depsPresent`/`blockKnown`). A block claims no root of its own, and an
  unknown parent root is a temporary missing dependency. So `excludes`
  gets no clause, SA-PC keeps its `rfl`, and wire validity has no root
  check. Wire forwarding rules wait for a P2P spec discussion.

  **As implemented in plan I9 (2026-09-29).** This note does not change
  the text above. Plan: `docs/plans/2026-09-29-i9-derived-roots.md`.
  Report: `docs/I9-REPORT.md`.

  - Roots are derived. `Block.node` has a parent, a slot and a
    `body : Nat`; it has no root field. `Block.root` computes the root
    from the content: `nodeRoot pr s x := ⟨epair pr.value (epair s x) + 1⟩`
    (`AvailableChainModel/Objects/Blocks.lean`). `epair` is a
    length-delimited pairing (`Objects/Codec.lean`). Honest proposers use
    body 0, so the formula `s * (parent.root + 1)` is removed. An FG block
    uses the same `nodeRoot` with the body code `encFGBody x rows`, which
    starts with the domain tag `fgBodyTag = 1`
    (`AvailableChainSimplexFG/Objects.lean`).
  - `Block.root_injective` holds for every block. So `RootInjective` is a
    theorem for every run (`rootInjective_all`,
    `AvailableChainKit/Roots.lean`), not a run premise, and the forged
    collision above cannot occur. The FG forms are
    `FGBlock.root_injective`, `rootInjectiveOn_all` and `viewRootInj_all`.
  - The store check is the dependency lookup. `parent_mem_iff_root` and
    `parent_mem_and_iff_root` show that "the store holds the carried
    parent" is equivalent to "the store holds a block with the parent's
    root". Grid CO, SA-PC and L* prove the lookup form
    (`blockKnown_parent_slot_iff_root`) and the no-op fact for a missing
    parent (`admitProposal_missingParent`; SA-PC also
    `proposalEnters_missingParent` and `process_pc_missingPaths`). No
    `wellFormed`, handler or `excludes` got a root check (§2 E4 note).
    FG-SA proves the lookup form `parentFG_isSome_iff_root` and the
    no-op fact `admitBlock_missingParent`
    (`AvailableChainFGSA/Proofs/Admission.lean`).
  - Resolved-block model. A payload carries the resolved block, and the
    carried parent root is `b.parent.root`. The lookup lemmas show that
    the store check is equivalent to a lookup by root. They do not give a
    root-only wire. A root-only wire refinement is open. Its adapter must
    also keep authentication, dependencies, handler calls, refusals and
    proposal origin.
  - L* obligation. The L* handler does not repeat the parent-slot test of
    `wellFormed` (`AvailableChainLStar/Model/Protocol.lean:283, 300`). So
    a future root-only adapter must apply the L* parent-slot test after
    the store lookup.
  - Regime fields. The regime root fields (`rootInjective`) and the
    lemma premises of the `hroot` type stay. `rootInjective_all`,
    `rootInjectiveBelow_all`, `rootInjectiveOn_all` and `viewRootInj_all`
    fill them. Their removal is a later plan (plan I9 D6).
  - FG-SA. The base body packs the application value and the ordered
    signed rows. `rowsOk` checks this packing in `wellFormed` and in
    `blockAccepted`; it is a content check, not a root check. With it,
    `ContentAgree` becomes a theorem. Task 9 did this. `packBody`
    packs `packInner app rows` and the decoded rows into `encFGBody`.
    `fgBlock` builds the FG body from `packInner`, not from `b.root`.
    `eraseFG` maps an FG block back with `encFGBody`.
    `MetaInv.wireTree` carries `rowsOk` for every stored wire.
    `contentAgree` needs only `MetaInv` at the two stores, and
    `contentAgree_reachable` gives `ContentAgree` for any two reachable
    stores (`Proofs/CrossNode.lean`). `rootInj_all` fills
    `CStoreInv.rootInj`. The cross-node theorems keep their
    `ContentAgree` premise, which is now redundant.
  - Open: relay feasibility (plan 1c). A missing dependency is a handler
    fact, not a run fact. `PartialSynchrony` and `HealthyPrefixDelivery`
    have relay obligations with no dependency guard
    (`AvailableChainStatements/Generic/Conditions.lean`). I9 proves only
    the lookup lemmas and the no-op facts.
