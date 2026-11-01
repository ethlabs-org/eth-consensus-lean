# Audit job: protocol framework design v4

You are an independent auditor. Audit the design document
`/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md`
(v4). It proposes a lasting Lean framework for protocol search: an engine,
conditions, facets, a claim catalog, certificates and refutations, kits, a
generated registry, and a modular composition of any available protocol
(AP) with one fixed finality gadget (our Simplex FG). Two agent sessions
agreed on it. The user will decide on it after your audit. Your job is to
find what is wrong, missing, unsound, infeasible or not future-proof. Do
not rubber-stamp. Do not edit any file. This is a read-only task.

## Sources (read what you need; cite file:line)

- The design: `lean/available-chain/docs/FRAMEWORK-DESIGN.md`.
- Current contract: `lean/available-chain/docs/CONTRACT.md`.
- Current engine and statements (v1):
  `lean/available-chain/AvailableChainModel/**`,
  `lean/available-chain/AvailableChainStatements/**`.
- Instances: `lean/available-chain/AvailableChainGridCO/`,
  `AvailableChainSA/`, `AvailableChainSAPC/`, `AvailableChainLStar/`,
  `AvailableChainWitnesses/`.
- The FG source (DC): `research/healing/rewrite/consensus.tex`
  (§ "Finality gadget in the fork-choice", the state machine with `nj`,
  the complete protocol), and the DC Lean repository
  `lean/decoupled-consensus/verified-consensus/`
  (`DecoupledConsensusStatements/Generic/*`).
- FG-SA research: `research/async-resilient-committees/tip-stability/`
  `design-space.md` (§§61–81), `codex/fg-sa-scope.md`,
  `codex/dc-recovery-map.md`, `codex/fgsa-fast.md`,
  `codex/fgsa-fast-opus.md`, `codex/reports/r143-fgsa-fast.md`,
  `codex/reports/r146-fgsa-adjudicate.md` (if present), `log.md` (tail).

All paths are relative to `/Users/francesco/ethereum`.

## What to audit

1. **Soundness of certification.** Can an instance obtain a certificate
   that is vacuous or means less than it says? Check: `HooksSound` (E4),
   instance regime witnesses (§5), facets that expose internal state
   (`Protected`, `FGTarget`; §3), record isolation (E5), the Prem/Concl
   orders and `monoPrem`/`monoConcl` (§4), and the `HavocFG` standalone
   form (§7.2). For HavocFG, check whether quantifying over the honest FG
   voting rule makes the AP-side conditions (`Static`,
   `TargetPreserving`) too strong, too weak, or ill-typed.
2. **Future-proofing.** The design claims that later needs are additions
   in L1–L3 and do not force a new engine version, except E1, E2, E5 and
   E6, which are added now. Test this claim against concrete future
   features: stake weights; finite sampled committees (ε); VRF
   self-selection with eligibility that grows with age; inclusion-list
   committees (FOCIL); multiple proposers; DAG-based or leaderless
   protocols; adaptive or mildly adaptive corruption; late joiners and
   state transfer; clock drift; protocol-driven relay instead of relay
   as a run premise; signature aggregation; a second, different FG. For
   each, say whether it is additive or needs an engine version, with a
   reason.
3. **Lift theorem feasibility (§2).** Is the v1 → v2 mapping well
   defined and sound: proposer keys to one-seat labels, per-label seat
   counts, `seatOf` as a function, event order, no self-visible labels,
   no restarts? Does every v1 claim transfer, including claims that
   quantify over `proposerOf`? Estimate its difficulty.
4. **Catalog mechanics (§4, §5).** For each current claim in
   `AvailableChainStatements/Generic/Claims.lean` and `Strong/Claims.lean`,
   check that monotonicity in each parameter is TRUE in the stated
   direction (for example: inclusion delay D, arming lag A, budget Π,
   recovery bound ρ, θ, θrec, recoveryFull, faultCap, η). Report any
   parameter that is not monotone, or whose direction is unclear. Check
   the feasibility in Lean 4 of: a freeze check that hashes the
   transitive closure of definition bodies; registry attributes; a
   reflective, kernel-checkable refutation checker without
   `native_decide`; lasso refutations.
5. **FG composition (§7).** Check that:
   - `anchorsOf` matches DC's viable set and FG root exactly, including
     the F-advance cut, frozen branches, root = J, and the F basis in
     duty views;
   - `Static` and `TargetPreserving` are the right conditions for (A)
     and (B), and that (C) can hold for them (also during Outage);
   - (D) causal cap, (E) with both arms, and (F) certified pairs are
     consistent with DC and with the FG-SA research status;
   - the composition by induction on time is not circular; list the
     prefix-closure status of each current regime (Sleepy, StableSleepy,
     Fast, Outage, FastOutage, Recovery, StrongArmed);
   - the joint recovery argument has no missing step.
6. **Internal consistency.** Contradictions between sections, stale
   references (for example to E7, `LeftAlone`, `FGDomain`), undefined
   terms, and claims in the document that the cited sources do not
   support.
7. **Missing pieces.** Anything a lasting framework needs that the
   document does not cover.

## Output

Write the report in ASD-STE100 Simplified Technical English.

1. A findings table (Unicode box-drawing, in a fenced `text` block) with
   columns: ID, severity (BLOCKING, MAJOR, MINOR), section, finding,
   evidence (file:line), proposed fix.
2. For each BLOCKING or MAJOR finding, a short paragraph with the
   argument or a counterexample sketch.
3. The future-proofing table from item 2.
4. The monotonicity table from item 4.
5. A verdict: ADOPT, ADOPT WITH FIXES, or REVISE, and why.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
