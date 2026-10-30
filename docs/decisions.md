# Design decisions (summary)

A summary of the design record. The full record, with the reasoning, reviews and research behind each line,
is in the team workbench (private): the [consensus-lean index][index] (decisions, plans, research, experiments
since the move to this repository) and the earlier [layers plan][layers] (iterations 1–6 of the generic
definition). Coordination decisions are in this repository's issues. Each line gives the date, the decision and
where it is recorded; "Francesco" marks the owner's decisions.

[index]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/consensus-lean/README.md
[layers]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/layers-plan.md
[plan]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/consensus-lean/plans/foundation-plan.md
[validation]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/consensus-lean/research/foundation-validation.md
[rebuild]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/consensus-lean/experiments/module-system-rebuild.md
[checkers]: https://github.com/fradamt-agent/workbench/blob/main/repos/goldilocks/notes/generic-interface/consensus-lean/research/reuse-checkers.md

## What a good protocol is

- 2026-10-28, Francesco ([layers plan][layers], "Iteration 6"). The generic layers define a good protocol as a
  fixed property table, each property with a fixed regime; an instance supplies only numbers. Precise protocol
  properties live in the instance's properties sheet. Layers: L0 problem, L1 model, L2 shape. The network is
  part of L0 (a communication log), and L1 proves once that its log is faithful (`LogFaithful`).
- 2026-10-28, Francesco (same). `stable := final` is not good: stable must be sleepy-live. The outage regime is
  η-sleepy; after an outage, every after-GST property applies (the outage end acts as GST).
- 2026-10-29, Francesco ([layers plan][layers], "Moved to consensus-lean"; README "Scope"). Healthy means full
  participation with faults below ⅓; liveness premises tolerate one bad proposer slot per window
  (`ProgressTolerant`); the sleepy stress witness keeps at most two honest validators awake; available and
  stable monotonicity stay conditional, final is unconditional; `available` may bind to `ac_confirmed`.
- 2026-10-28, Francesco ([layers plan][layers], "Iteration 6"). Goldilocks gets pinned numbers and a properties
  sheet now; the FG-SA migration comes later.
- 2026-10-29, claude-ethlabs ([#38]). That sheet (`Instances/Goldilocks/{Spec,Statements}/Baseline.lean`) is a
  pre-foundation baseline, **not approved**: no proof targets it until the first slice ([#10]) re-reviews it
  against the current Goldilocks spec (`docs/goldilocks-mapping.md`). The files of the instance semantics and
  statements (`Instances/<P>/{Spec,Statements}` as file and directory, `Instances/<P>/Refinement/Defs.lean`)
  join `trusted_paths`, and their layers are `protected` (check-boundaries requires the coverage), so every edit
  of those files is reviewed; the tag covers the sheet only as a frozen baseline. The Goldilocks import
  exception to `Main` is limited to the two `Baseline` modules. The sheet moved to
  `Instances/Goldilocks/{Spec,Statements}/Baseline.lean` (unchanged) so that milestone statements
  `Statements/<M>.lean` can sit beside it (check.sh step 4: a module with descendants owns no constants).

## Repository, toolchain and trust checks

- 2026-10-29 ([index]). Own repository (history of goldilocks `contract/` kept); Lean and Mathlib v4.35.0;
  delivery is "normal": an honest send at `t` is held at `dl a` by every honest node awake throughout
  `[a, dl a]`, for every `a ≥ t` (wakers get messages by `u + Δ`).
- 2026-10-29 ([index], [checkers]). Trust checks reuse existing tools (EthLib check-decls, leanchecker,
  `#guard_msgs` axiom pins, `lake check`, `lake comparator`, axiom-audit) with thin glue; the home-grown
  checker was abandoned. turbo-lean is optional, for per-declaration re-checks only. bubblewrap is installed on
  the shared box, so `lake check` and the comparator run locally.
- 2026-10-29 ([index]). Rules about the project's structure must rest on external precedent, not on our own
  projects ([validation]).
- 2026-10-30 ([#41]). License Apache-2.0, as the Verified-zkEVM Lean libraries (ArkLib, CompPoly, VCVio) and
  Mathlib; vendored copies keep their own licences.

## Foundation plan (adopted 2026-10-29, all recommendations)

[The plan][plan]; adoption steps §11 are issues [#4]–[#11].

- One certified library `ConsensusLean`, layers as module prefixes, a source-level boundary checker with one
  config (`scripts/boundaries.toml`) instead of Mathlib's `directoryDependency` ([#5], [#6]).
- `import all` only in tests (D1). Whole-file `@[expose]` in Spec and Statements, none in Lemmas, Proofs and
  `Main`, so a proof edit rebuilds one module ([rebuild], [#8]).
- Proof debt as in FLT and Carleson (D4): `sorry` only under `Lemmas/` and `Proofs/`, never an axiom; certified
  means the closure of `Solution`, audited per PR; leanchecker and the comparator run nightly and at milestone
  acceptance ([#7]).
- Depth, cones and critical path are reports, not gates; the one-module rebuild property is a canary; chains
  are allowed inside a milestone ([#4], [#7]).
- A light roadmap with checked names now (`docs/roadmap.md`), leanblueprint later (trigger: a second instance or
  outside contributors). The Spec package split waits for reuse outside the project.

## Goldilocks instance

- 2026-10-30, amp-orbs (architecture), under the coordinator's criterion "the smallest trusted change that keeps
  every proved milestone's proofs intact" ([#17], Refinement). **The spec block carries the engine's input**: the
  engine hashes the whole header `(parent, pos, input, info)` and `compile` writes `input := encodeTxs mempool`
  outside the shape's `Info`, so two engine blocks differing only in `input` have different hashes but, without
  the field, one spec content; `RootOk` with one digest cannot hold of both, and the refinement cannot be stated
  faithfully. Chosen: (B) a field `input : Nat` of `Common.Block`, the digest over `(parent, slot, input, FG
  payload, AC payload)`, and the node's tick event carrying the input (`Node.Event.tick x`; `mkBlock` writes it;
  the AC never reads it). Rejected: (P) the input through the AC payload via `ACInterface.proposal`, which
  changes the generic AC interface, the SA payload pair and every `Lemmas/AC` file (16 proved files) and
  `Spec/SA`; (B) leaves `Lemmas/AC` and `Lemmas/FGStore` (generic in the block type, no block literals) intact
  and touches `Spec/Common/Block`, `Spec/Node`, `Spec/Run/Model`, the `Statements/Compose` files that pattern
  the tick, five `Lemmas/Compose` files and the Goldilocks tests. The spec folds the input into the AC payload
  (composition.tex: the AC fixes the encoding of its payload); the mapping records the field as that encoding.

- 2026-10-30, amp-orbs (coordinator), on the Regimes milestone (R.3). **Baseline's heal point is not raised to the
  proved bound.** The target pins `gHeal = max(g, 0) + (29 + B_H^F(k))·Δ` (from the FG-SA analysis); the only
  healing result, claims H.4, gives `T_heal = ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G_p + T_b`, far above it. R.3 is
  stated over the run at a heal point `T ≥ T_heal` (`Statements/Regimes/Healed`), with H.4's open premises (H.3
  (c)'s bridge, `(U_all)`, `(U_B)`) as named hypotheses, and with H.4's regime premises that the target lacks
  (`Catch(2Δ)`, `Prop⁺(G_p)`, the `δ_t` bound and the genesis root of `HSShared`); Baseline's `gHeal` is unchanged.
  Raising `gHeal` to H.4's bound would weaken the review target to fit the proof we have, which AGENTS.md rules out,
  and a larger proven bound is not evidence that `gHeal` is false. **Baseline R.3 at `gHeal` remains open; what is
  proved (once the proofs land) is R.3 at `T_heal` under those premises.** `gHeal` changes only with a
  counterexample (a reachable run that heals later than `gHeal`) or the owner's explicit decision (flagged to him).
  Model evidence (workbench#8 `sa-fg-model`, measured at `528a15c`, recorded in the README at `e406004`): 9,600
  `Healthy` runs (n ∈ {4, 5, 7}, k ∈ {2, 3}, δ_t ∈ {2, 3}; random, hostile and partition adversaries) all heal
  within their horizon and none after `gHeal`; the largest available heal time is 0.049·`gHeal` and the largest
  first-finality time 0.132·`gHeal`. The adversaries are not heal-delay optimizers and the horizons (128–224Δ after
  `ḡ`) are below `gHeal`, so this is no counterexample search.

## Process

- 2026-10-29, Francesco ([#2]). Claude (claude-ethlabs) and the Amp orbs push and merge their own green,
  reviewed PRs and are responsible for them. Process speed (build, CI, iteration, review load) is part of
  quality. Reviews are local, by model instances that did not write the change. All coordination lives in
  issues and PR threads, never in the tree.
- 2026-10-29, Francesco (`docs/spec-review.md`). The trusted surface is approved by the annotated tag
  `spec-approved`, which claude-ethlabs moves only on the owner's authorization (or for a verbatim move with
  machine-checked evidence, recorded in `docs/spec-review.md`).
- 2026-10-29, claude-ethlabs within that authority ([#21], `TRUST.md`). Check infrastructure (`scripts/`,
  `.github/`, the lakefile) is agent-reviewed: a change to what a trust check checks needs two independent
  reviews linked in the PR and a pointer on [#17]; other changes one, and a pure speedup also evidence that every
  check's verdict is unchanged (the same pass/fail on the fixtures). `.github/CODEOWNERS` names the owner for
  the trusted surface, the infrastructure and the mapping docs (plan §4), but Code Owner review is not enforced
  (enforcement through a ruleset stays open to the owner).
- 2026-10-30, Francesco ([#2]). No imitation of human review process: there are no review gates between agents.
  A subagent pass is a tool inside the author's own session. This replaces the review requirements of the
  entries above; a check-infrastructure change still carries its fixture evidence.
- 2026-10-30, Francesco ([#2]). **Nothing blocks on the owner**: he gives input and asks questions, and does not
  approve PRs, statements or tag moves; agents own every decision and record it where the work is.
  `spec-approved` stays, as an **agent approval**: an agent other than the change's author (claude-ethlabs, or
  the amp-orbs coordinator) moves it after the author's fidelity read-back and a green fast check; the tag
  message names the PR, the protected files changed and the evidence. This replaces the owner's authorization
  in the entry on `spec-approved` above. First application: #49 (`f98ed97`), moved by amp-orbs.
- 2026-10-30, amp-orbs (process), under that rule ([#50]). Trunk-based: after the local checks
  (`scripts/check-changed.sh`; `--fast --selftests` for `scripts/` or build-configuration changes), rebase on
  `origin/main` and push to `main`. CI runs on every push to `main`, and whoever made it red reverts at once. A PR
  only for a trusted-surface change, since the tag must cover its head before it reaches `main`.

## Open, for the owner

- A branch ruleset enforcing owner review ([#21], option 2).

[#2]: https://github.com/fradamt-agent/consensus-lean/issues/2
[#50]: https://github.com/fradamt-agent/consensus-lean/issues/50
[#41]: https://github.com/fradamt-agent/consensus-lean/issues/41
[#4]: https://github.com/fradamt-agent/consensus-lean/issues/4
[#5]: https://github.com/fradamt-agent/consensus-lean/issues/5
[#6]: https://github.com/fradamt-agent/consensus-lean/issues/6
[#7]: https://github.com/fradamt-agent/consensus-lean/issues/7
[#8]: https://github.com/fradamt-agent/consensus-lean/issues/8
[#10]: https://github.com/fradamt-agent/consensus-lean/issues/10
[#11]: https://github.com/fradamt-agent/consensus-lean/issues/11
[#17]: https://github.com/fradamt-agent/consensus-lean/issues/17
[#21]: https://github.com/fradamt-agent/consensus-lean/issues/21
[#38]: https://github.com/fradamt-agent/consensus-lean/issues/38
