# The generic contract: review guide

`AvailableChainContract` states what it means for a protocol to be a correct
available chain with a finality gadget. Nothing in it depends on a concrete
protocol. If a protocol family `F` proves `Claims F C` for a literal constant
record `C`, then `F` is correct in the sense defined here. A reviewer reads
only the files below and the residual bindings at the end. The protocol's
code and its proofs need no reading: the kernel checks the proofs.

Design and history: `notes/generic-interface/plan.md` in the workbench
(rev 4), with the Astra and Opus reviews it cites.

## What to read (about 1,300 lines)

Read in this order:

| File | What it fixes |
|---|---|
| `AvailableChainContract/Objects.lean` | Block headers that name their parent by digest; chains (outputs) as lists of headers, compared by prefix; signatures (`Auth`); messages: a proposal of a header, or protocol data; wire objects that carry objects structurally |
| `AvailableChainContract/Protocol.lean` | What an instance supplies: its types (`State`, `Label`, `Duty`, `Body`, `Durable`), `slotTicks`, a state machine (`clock`, `propose`, `act`, `gossip`, `process` with no time argument, `recordOwn`, `durable`/`restore`), three output getters, and the slashing rule `conflicts`. It knows only `n` and `Δ`. |
| `AvailableChainContract/Run.lean` | Run data (honest set, events, seats, proposers, inputs, hash function). The engine builds and signs proposals with the proposer's own input; it releases an object only if everything it carries was seen; it alone evaluates the hash and passes `digests` of observed signed headers to the protocol. Reads at times and at event cuts; views. |
| `AvailableChainContract/Constants.lean` | Every time bound is a coefficient of `Δ` |
| `AvailableChainContract/Conditions.lean` | Premises: schedule, sleep (a restart at every wake and only at wakes), unforgeability, delivery (flooding of released objects), participation of ready nodes, recurrence |
| `AvailableChainContract/Properties.lean` | Safety (at event cuts), provenance and linkage (`OutputValid`), inclusion of the honest proposer's own header, growth, persistence |
| `AvailableChainContract/Evidence.lean` | Generic evidence and slashing; accountable safety; honest never slashed; `HashCollision` and `InjectiveHash` |
| `AvailableChainContract/Regimes.lean` | The regimes. Each mentions only the environment, run data and engine facts. |
| `AvailableChainContract/Claims.lean` | `Claims F C`: every field, for every validator set, environment and run (hash included); most fields hold "or a hash collision was observed" |
| `AvailableChainContractProofs/CanonicalStatement.lean` | `CanonicalRun`: the execution part of every regime is satisfiable for every protocol |
| statements in `AvailableChainContractProofs/Accountable.lean` and `Lift.lean` | `finalizedSafe_of_claims`; `claims_iff_claimsInj` (`Claims ↔ ClaimsInj`: the collision escape adds nothing beyond the injective case) |
| `engine/AvailableChainModel/Generic/Env.lean` (22 lines), and `Time := Int` and `Slot := Nat` in `engine/AvailableChainModel/Objects/{Time,Identifiers}.lean` | the environment (`Δ`, GST, awake profile) and basic types, imported by the contract |

Not to be read (kernel-checked): the proofs of `canonical_run`
(`AvailableChainContractProofs/Canonical*`) and of
`finalizedSafe_of_claims`, and the tests (`AvailableChainContractTests`):
- `Leaks.lean` refutes the degenerate families;
- `Controls.lean` shows that every regime holds, with active guards, in one
  canonical run: `n = 4`, all honest and always awake, GST = 0, horizon 20.

`Run.View` (views by time) is defined but no claim uses it: claims use
`Run.ViewIdx`.

## Why no protocol-supplied word weakens a claim

- Hashes. The hash is arbitrary run data (`Run.hash`): every claim holds for
  every hash function, colliding ones included. Most claims read "X, or a hash
  collision was observed" (`HashCollision`: two distinct observed headers, or a
  header and genesis, with one digest), as accountability reads "X, or a third
  is slashable". A collision counts only if both items were observed (headers
  proposed under their own slot's key). Honest code learns the hash only
  through the digests the engine passes for such headers; changing the hash
  outside them does not change the run. For an injective hash the escape is
  false, and `claims_iff_claimsInj` proves `Claims ↔ ClaimsInj`: the escaped
  form says exactly as much as "X for every injective hash", so the escape
  adds nothing beyond genuine collisions among observed headers. Honest code
  still chooses what it proposes, so collision resistance of the deployed
  hash is an assumption (binding 5), not a theorem. Provenance, output order,
  finalized monotonicity and "honest never slashed" hold with no escape, for
  every hash.
- No premise of any claim contains a predicate that the protocol supplies.
  The protocol has no receipt hooks, no `author`, no `carries`, no block
  decoder, no schedule, no deadlines, no evidence or certificate predicates,
  and no hash function or hash premise. Execution premises do depend on what the protocol
  does (what it releases, its object types, its slot timing). They depend on
  it only through the generic engine and the generic conditions, and
  `Claims.slotTicks` pins the slot timing. `canonical_run` shows that, for every protocol, the execution
  part of every regime holds in some run. So no protocol can make a regime
  vacuous.
- The outputs are pinned on both sides:
  - from above, by safety (at every event cut), accountable safety, output
    order, and provenance (only proposed, seen headers, linked by digest, with
    increasing slots);
  - from below, by inclusion of the honest proposer's own header, which carries
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
   - The deployed hash is collision-resistant, and honest code uses digests
     only as received (it never searches for collisions); the parent/aux
     encoding of headers.
   - `Body` parsing: what can be sent as protocol data. It bounds what the
     adversary can send.

Generic, read once:

6. **Model adequacy.** Clocks; delivery of released objects within `Δ`
   after GST, including to nodes that wake later; restarts only at wakes;
   unforgeable signatures; a hash function that honest code cannot invert or
   query freely.

## Scope limits and modelling conventions

- Reads: safety, accountability and provenance hold at every event cut;
  inclusion, growth and persistence read at the end of a time.
- Ticks: all of a tick's candidates come from the state after `clock`, before
  any `recordOwn`. A proposal cannot carry a vote of the same tick.
- Slot 0 is reserved for genesis: no header of slot 0 can be output.
- The collision escape is run-wide: a collision observed anywhere in the run
  excuses the escaped claims for the whole run. Bounding it by each claim's
  cut or deadline is open (notes/generic-interface/hash-plan.md, draft 3).

- Every committee label has all `n` seats under a run-chosen bijection.
  Protocols with small sampled committees are not expressible.
- Weights are unit.
- Recovery assumes no honest wake at or after GST (plan Q13; Francesco
  decides).
- Accountability compares two reads in one run. Accountability across two
  runs and retrievable light-client certificates are not covered.
- Application validity of inputs is not covered.
