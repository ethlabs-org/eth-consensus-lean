# eth-consensus-lean

A machine-checked proof, in [Lean 4](https://lean-lang.org), that **Goldilocks** is a correct consensus protocol under stated network and adversary assumptions. Goldilocks combines an *available chain* that keeps growing while many validators are offline with a *finality gadget* that finalizes blocks when the network is healthy; its specification is in [`specs/goldilocks/tex/`](specs/goldilocks/tex/).

**The adversary grows.** The model, the generic statements and the Goldilocks claims cover an adversary whose set of compromised validators grows over the run; a constant set is the static adversary.

The proved headline theorem is `goldilocksCorrect`. It says that Goldilocks is a `CorrectProtocol` for every finite set of validators and every choice of its parameters (the lock window `k ≥ 2`, the timeout `δt` and the rest), given two assumptions on its timing: `fgSlots`, which bounds the finality gadget's attestation delay in a healthy network (see the healthy regime below), is at least 2, and the timeout is at least `3·fgSlots`. Every timing constant in the guarantees is an explicit formula in these parameters. Its proof composes two parts. The first is generic: a precise definition of a correct consensus protocol, and a theorem that any protocol written in a standard blockchain form and meeting a list of conditions on a class of runs satisfies it on that class. The second shows that Goldilocks meets those conditions.

## What "correct" means

**The setting.** There are *n* validators, each with one signing key. Some are *faulty*: the adversary controls them completely and knows everything, but cannot forge honest signatures. The set of faulty validators can grow during a run. A compromise is immediate and permanent, and from then on the adversary holds the validator's ordinary key. It can sign anything with that key, including objects that claim an earlier slot, while what the validator did while honest stays honest. A constant set is the static adversary. Honest validators can be *asleep* (offline) and wake up later. Clients submit transactions to awake honest validators. Each honest validator *reads* chains from its local view; Goldilocks gives two reads: the **confirmed** chain (from the available chain) and the **finalized** chain (from the finality gadget).

**The network.** Time is discrete. A message an honest validator sends at time *t* reaches every honest validator that stays awake, within a delay bound: `ΔAC` for ordinary messages and transactions, and `ΔFG` for finality-gadget attestations. Before the *global stabilization time* (GST) the network can be asynchronous; afterwards the bounds hold. A validator that wakes up is sent again what it missed, within the same bound.

**The regimes.** Each guarantee holds in a stated set of conditions, called a regime:

| Regime | Network | Participation |
|---|---|---|
| sleepy | synchronous from the start | at every time `t`, *ready* validators still honest at `min (t + ahead·ΔAC) horizon` outnumber the validators compromised by then (Goldilocks proof target: `ahead = 5`); under constant faults, the faulty ones (a validator is ready after a short awake catch-up period) |
| healthy | synchronous after a GST, and `ΔFG` is at most (4·`fgSlots` − 6)·`ΔAC` | fewer than *n*/3 faulty; every honest validator awake after the GST |
| outage | one bounded period of asynchrony | at every run time, η-sleepy participation (θ = ½) in the population and every nonempty committee selected in the look-back: validators ready with catch-up `max (19ΔAC) (η·ΔAC − 1)` outnumber faulty validators plus the other honest validators awake anywhere in the look-back, with faults charged at `min (t + 5ΔAC) horizon`; Goldilocks sets `η = 12k + 7`, and selection times are clamped at zero. Validators may fall asleep; readers retain catch-up `19ΔAC` |

**The guarantees.** For Goldilocks, certified on constant-fault runs only; the growing-fault statements are stated and open.

- **Always, in any network:** honest validators are never convicted by the evidence honest nodes see; the finalized chain never rolls back and is a prefix of the confirmed chain; and if two honest validators ever read conflicting finalized chains, the evidence in their views convicts at least *n*/3 validators (*accountable safety*).
- **Sleepy regime:** the confirmed chain is *safe* (ready honest readers agree; the chains they read are prefixes of one another) and *live* (every transaction submitted to an awake honest validator appears in every ready reader's confirmed chain within a bounded latency).
- **Healthy regime:** both chains are live, and the confirmed chain is safe from a bounded healing time after the GST.
- **Outage regime:** a confirmed chain read before the outage stays part of what ready readers see after recovery.

Liveness also needs honest ready proposers often enough. For Goldilocks, every window of a fixed number of slots must contain one for the confirmed chain, and for the finalized chain four, at the offsets 0, `fgSlots`, 2·`fgSlots` and 3·`fgSlots` from one slot. Every guarantee may fail on a run in which some node observes a hash collision, and only there.

The definition also rules out vacuous protocols: a protocol that never sends anything, or one whose assumptions can never be met, does not count as correct. In Lean the definition is `CorrectProtocol` ([`ConsensusLean/Spec/Problem/CorrectProtocol.lean`](ConsensusLean/Spec/Problem/CorrectProtocol.lean)); [`docs/definition.md`](docs/definition.md) gives it in full.

## How the pieces fit

```text
 Goldilocks paper spec (specs/)
        │  transcribed into Lean
        ▼
 Goldilocks node: finality gadget + available chain        ConsensusLean/Instances/Goldilocks/Spec/
        │  written as a chain shape                        .../Goldilocks/AsChainShape.lean
        ▼
 MeetsObligations: Goldilocks meets the obligations       .../Goldilocks/Statements/Obligations.lean
        │  ObligationsSufficient: every chain shape that
        │  meets the obligations is correct               ConsensusLean/Statements/Review.lean
        ▼
 goldilocksCorrect: Goldilocks is correct                  .../Goldilocks/Statements/Obligations.lean
```

| Protocol concept | Where it is in Lean |
|---|---|
| validators, keys, signatures, the adversary, every possible execution | the execution model, [`ConsensusLean/Spec/Model/`](ConsensusLean/Spec/Model/) |
| network delays `ΔAC` and `ΔFG`, GST, awake and asleep | [`ConsensusLean/Spec/Problem/Network.lean`](ConsensusLean/Spec/Problem/Network.lean) |
| the regimes and the guarantees | [`ConsensusLean/Spec/Problem/`](ConsensusLean/Spec/Problem/) (`CorrectProtocol`) |
| slots, proposers, blocks, votes, how a node handles them | a **chain shape**, [`ConsensusLean/Spec/Shape/`](ConsensusLean/Spec/Shape/) |
| the conditions a chain shape must meet: chain-level safety and liveness claims, sensible numbers, enough proposer opportunities | the **obligations**, `ShapeObligations` ([`Spec/Shape/Obligations.lean`](ConsensusLean/Spec/Shape/Obligations.lean)) |
| Goldilocks: finality gadget, available chain, attestations, finality | [`ConsensusLean/Instances/Goldilocks/Spec/`](ConsensusLean/Instances/Goldilocks/Spec/) |
| Goldilocks' timing constants (catch-up, healing time, latency) | `goldilocksContract` in [`Instances/Goldilocks/Statements/Obligations.lean`](ConsensusLean/Instances/Goldilocks/Statements/Obligations.lean) |
| the proofs | `ConsensusLean/Lemmas/`, `ConsensusLean/Proofs/`, `ConsensusLean/Instances/Goldilocks/Proofs/` |

The certified result is nine Lean statements, listed in [`Challenge.lean`](Challenge.lean). The headline is `goldilocksCorrect`: Goldilocks is correct. The others support it:

- `MeetsObligations`: Goldilocks meets the obligations;
- `GoldilocksCorrectWithExcuses`: the headline on each single run, or an explicit binding failure (forgery, credential failure, inadmissible selection);
- `PersistsWith`: Goldilocks' outage guarantee also holds when votes come from a per-slot committee rather than from all validators;
- `ObligationsSufficient`: every chain shape that meets the obligations (`ShapeObligations`) is correct;
- `ObligationsSufficientOn`: the same on a class of runs, in particular on constant faults, the static adversary at full strength;
- `RegimesRealizable`: the regimes can actually occur, so the guarantees are not vacuous;
- `LogFaithful` and `HeldIffServed`: the execution model is faithful (what a node holds in the model is exactly what the network delivered to it).

[`Solution.lean`](Solution.lean) proves them, and [`comparator.json`](comparator.json) tells Lean's comparator to check that it proves exactly these statements, using only Lean's three standard axioms.

## What you must trust, and how to check it

You must trust Lean's kernel, the pinned Mathlib, and the files that *state* the claim: the definition, the execution model, the Goldilocks specification that the headline statement reads, and the certified statements. Everything else, including every proof, is checked. [`TRUST.md`](TRUST.md) lists those files and says what each automatic check guarantees.

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get                       # Mathlib's prebuilt files
lake build && lake test                  # the library, then the tests and the statement/axiom pins
RUN_DIR="$(mktemp -d)" scripts/check.sh --fast   # the trust checks; --full adds kernel replay and the comparator
```

CI runs the fast checks on every pull request and push to `main`, and the full checks nightly ([`docs/checks.md`](docs/checks.md)).

## Scope

The generic definition covers growing faults; Goldilocks is certified for constant faults only while its dynamic endpoint and headline remain open.

Not modelled: a corruption delay or forward-secure keys, recovery from compromise, a probabilistic or computational model of adaptive corruption, validators with different weights, probabilistic protocols, proof of work, readers that are not validators, responsiveness, and transaction validity, fees or capacity. Each run has at most one GST and one outage. The full list, with the reasons, is in [`docs/definition.md`](docs/definition.md#scope).

## Repository map

```text
Challenge.lean          the certified statements (proofs left as `sorry`)
Solution.lean           their proofs
comparator.json         how the comparator checks Solution against Challenge
TRUST.md                what you must trust; what each check guarantees
ConsensusLean/          the library: the definition (Spec/), the statements, the proofs, Goldilocks (Instances/)
ConsensusLeanTest/      tests, grouped by layer and by Goldilocks component; the statement and axiom pins
specs/                  the Goldilocks specification (LaTeX)
docs/                   the definition in full, the checks, the layout, the roadmap, the Goldilocks mapping
scripts/                the check suite (scripts/check.sh) and its tools and fixtures
lakefile.toml, lean-toolchain, lake-manifest.json    Lake build configuration and pinned versions
ConsensusLean.lean, ConsensusLeanTest.lean           generated library roots (they import every module)
CONTRIBUTING.md, AGENTS.md (= CLAUDE.md)             how to contribute, for people and for agents
LICENSE                 Apache-2.0
```

## Read more

- [`docs/definition.md`](docs/definition.md): the definition of a correct protocol in full: every guarantee, the network rule, the regimes, the numbers, what the execution model fixes, and the scope.
- [`docs/goldilocks-mapping.md`](docs/goldilocks-mapping.md): from each claim of the Goldilocks paper ([`goldilocks-claims.tex`](specs/goldilocks/tex/goldilocks-claims.tex)) to its Lean statement and proof.
- [`docs/roadmap.md`](docs/roadmap.md): every milestone and its status.
- [`docs/checks.md`](docs/checks.md) and [`docs/layout.md`](docs/layout.md): the checks, CI, and how the code is organised.

Licence: Apache-2.0 ([`LICENSE`](LICENSE)).
