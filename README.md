# The generic contract: review guide

`AvailableChainContract` states what it means for a protocol to be a correct
available chain with a finality gadget. Nothing in it depends on a concrete
protocol. If a protocol family `F` proves `Claims F C` for a literal constant
record `C`, then `F` is correct in the sense defined here. A reviewer reads
only the files below and the residual bindings at the end. The protocol's
code and its proofs need no reading: the kernel checks the proofs.

Design and history: `notes/generic-interface/plan.md` in the workbench
(rev 4), with the Astra and Opus reviews it cites.

## What to read (about 1,240 lines)

Read in this order:

| File | What it fixes |
|---|---|
| `AvailableChainContract/Objects.lean` | Blocks with computed roots (injective, no hash premise); signatures (`Auth`); messages: a proposal of a block, or protocol data; wire objects that carry objects structurally |
| `AvailableChainContract/Protocol.lean` | What an instance supplies: its types (`State`, `Label`, `Duty`, `Body`, `Durable`), `slotTicks`, a state machine (`clock`, `propose`, `act`, `gossip`, `process` with no time argument, `recordOwn`, `durable`/`restore`), three output getters, and the slashing rule `conflicts`. It knows only `n` and `Δ`. |
| `AvailableChainContract/Run.lean` | Run data (honest set, events, seats, proposers, inputs). The engine builds and signs proposals with the proposer's own input; it releases an object only if everything it carries was seen. Reads at times and at event cuts; views. |
| `AvailableChainContract/Constants.lean` | Every time bound is a coefficient of `Δ` |
| `AvailableChainContract/Conditions.lean` | Premises: schedule, sleep (a restart at every wake and only at wakes), unforgeability, delivery (flooding of released objects), participation of ready nodes, recurrence |
| `AvailableChainContract/Properties.lean` | Safety (at event cuts), provenance (`OutputValid`), inclusion of the honest proposer's own block, growth, persistence |
| `AvailableChainContract/Evidence.lean` | Generic evidence and slashing; accountable safety; honest never slashed |
| `AvailableChainContract/Regimes.lean` | The regimes. Each mentions only the environment, run data and engine facts. |
| `AvailableChainContract/Claims.lean` | `Claims F C`: every field, for every validator set, environment and run |
| `AvailableChainContractProofs/CanonicalStatement.lean` | `CanonicalRun`: the execution part of every regime is satisfiable for every protocol |
| statements in `AvailableChainContractProofs/Accountable.lean` | `finalizedSafe_of_claims` |
| `engine/AvailableChainModel/Generic/Env.lean` (22 lines), and `Time := Int` and `Slot := Nat` in `engine/AvailableChainModel/Objects/{Time,Identifiers}.lean`; `epair` in `Objects/Codec.lean` (definition only; its injectivity is proved) | the environment (`Δ`, GST, awake profile) and basic types, imported by the contract |

Not to be read (kernel-checked): the proofs of `canonical_run`
(`AvailableChainContractProofs/Canonical*`) and of
`finalizedSafe_of_claims`, and the tests (`AvailableChainContractTests`):
- `Leaks.lean` refutes the degenerate families;
- `Controls.lean` shows that every regime holds, with active guards, in one
  canonical run: `n = 4`, all honest and always awake, GST = 0, horizon 20.

`Run.View` (views by time) is defined but no claim uses it: claims use
`Run.ViewIdx`.

## Why no protocol-supplied word weakens a claim

- No premise of any claim contains a predicate that the protocol supplies.
  The protocol has no receipt hooks, no `author`, no `carries`, no block
  decoder, no schedule, no deadlines, no evidence or certificate predicates,
  and no hash premise. Execution premises do depend on what the protocol
  does (what it releases, its object types, its slot timing). They depend on
  it only through the generic engine and the generic conditions, and
  `Claims.slotTicks` pins the slot timing. `canonical_run` shows that, for every protocol, the execution
  part of every regime holds in some run. So no protocol can make a regime
  vacuous.
- The outputs are pinned on both sides:
  - from above, by safety (at every event cut), accountable safety, output
    order, and provenance (only proposed, seen blocks with increasing slots);
  - from below, by inclusion of the honest proposer's own block, which carries
    that proposer's private input, by growth, and by persistence.
- `conflicts` is pinned on both sides:
  - from above, by `honestNeverSlashed` over every valid run;
  - from below, by accountable safety together with finality liveness. That
    argument is on paper, not in Lean: a partition argument for `|V| ≥ 5`,
    or `|V| = 4` with `θrec < 3/4`.
- `AvailableChainContractTests` refutes the known degenerate families:
  - a silent protocol;
  - a protocol that proposes but outputs genesis;
  - a fabricated output chain;
  - `conflicts := true`.

## Residual bindings (read per instance)

1. **Outputs.** Are `confirmed`, `stable` and `finalized` what users read?
   Only `stable ⪯ confirmed` is promised, pointwise. No claim says that
   `finalized` lies below `stable` or `confirmed`, in any regime, `Finality`
   included (plan Q9, open).
2. **Input.** Does the run input mean what users care about (for example
   transactions)?
3. **Numbers.** `C` in full, including the premise-side constants (`catchUp`,
   `η`, `armingLag`, `fastArmingLag`, `budget`, `θ`, `θrec`, `recoveryFull`).
   They narrow the guarantee.
4. **`conflicts`.** Is it the slashing rule that the chain enforces?
5. **Implementation refinement.** Does the deployed client match the
   engine's contract?
   - Signature encoding, and the holder mapping of seats and slot keys to
     validators.
   - Structural carriage and the seen filter, with the seen log persisted.
   - What `durable` keeps is persisted across restarts. Every wake is a
     restart; claims across restarts hold only if this state survives.
   - Computed roots, and the parent/aux encoding of blocks.
   - `Body` parsing: what can be sent as protocol data. It bounds what the
     adversary can send.

Generic, read once:

6. **Model adequacy.** Clocks; delivery of released objects within `Δ`
   after GST, including to nodes that wake later; restarts only at wakes;
   unforgeable signatures; injective hashing.

## Scope limits and modelling conventions

- Reads: safety, accountability and provenance hold at every event cut;
  inclusion, growth and persistence read at the end of a time.
- Ticks: all of a tick's candidates come from the state after `clock`, before
  any `recordOwn`. A proposal cannot carry a vote of the same tick.
- Slot 0 is reserved for genesis: no other block of slot 0 can be output.

- Every committee label has all `n` seats under a run-chosen bijection.
  Protocols with small sampled committees are not expressible.
- Weights are unit.
- Recovery assumes no honest wake at or after GST (plan Q13; Francesco
  decides).
- Accountability compares two reads in one run. Accountability across two
  runs and retrievable light-client certificates are not covered.
- Application validity of inputs is not covered.
