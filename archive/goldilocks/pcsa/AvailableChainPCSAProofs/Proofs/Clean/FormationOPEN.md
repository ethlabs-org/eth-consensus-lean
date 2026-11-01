# Formation (C7): inputs

This file lists the inputs of C7 `FormationClaim` and their producers. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

C7 has no open input. `Assembly/Formation.lean` proves:

- `pcsa_formationClaim : FormationClaim p`.
- `pcsa_formationSourceClaim : FormationSourceClaim p`. Assembly/Formation
  imports `Finality/Export` for `Claims.Finality`.

The F4 statement fix is part of this landing. It adds
`FormationRootReachable` and the `proposerRootReachable` fields of
`FormationPrem` and `HealedSourcePrem` (at `r * p.R`). Without this clause,
the old `FormationClaim` and `FormationSourceClaim` were false under those
premises; the old premises were satisfiable. `docs/PCSA-API.md` is
regenerated.

Proved inputs, with their producers:

- Frozen-PC origins, receipt, collection, freeze retention, stop, and
  non-equivocation: `FormationOrigins`, `FormationCollection`,
  `FormationFreeze`, `FormationTerminal`, `FormationHeads`.
- Proposal presence and metadata at `v_s` and `e_s`, resolution, support
  retention, raw-HEAD carriage, the current child:
  `FormationInputs`, from Shared body relay and honest-proposal receipt.
- Exact honest HEADs: `pcsa_formation_head_exact_of_retained`, from the
  retained inputs only.
- Early HEAD receipt: `pcsa_formation_early_heads_of_exact`
  (`FormationEarlyHeads`). Formation delivery after `z_{s-1}` is the
  strict `t + Δ` delivery of the Clean receipt proofs.
- Ack admission: `pcsa_formation_preFreeze_ack_admit`, from Clean
  `pcsa_honest_ack_admitted`.
- Late gate counts: `pcsa_formation_gate_counts`
  (`FormationGateCounts`), from the exact honest HEADs. `H` is the number
  of honest HEAD seats awake at `v_s`.
- Retained walk facts `hKeep`, `hReflect`, `hUnique`
  (`FormationRetainedTree`): equal stage-1 eligibility
  (`pcsa_formation_retained_eligible_eq`, from the two back receipts) and
  voter-tree inclusion (`pcsa_formation_retained_tree`: each voter-tree
  body is `N.erase` or a proposer-tree body). Formation body relay carries
  the frozen bodies to the proposer by `t_s`; the other bodies are
  prefixes of the unique slot-`s` body.
- Retained back receipts `hRawBack`, `hSupportBack`
  (`pcsa_formation_retained_back_of_frozen`, `FormationRetainedBack`): the
  carried arms are the proposal's own lists. A frozen support HEAD relays
  as a raw HEAD; Formation body relay gives its body at the proposer
  (`pcsa_formation_frozen_body_in_proposer`).
- Frozen raw relay `FormationFrozenRawOpen` (`pcsa_formation_frozen_raw`,
  `FormationFrozenRaw`): Formation delivery is `StrictFrom` at
  `T₀ = z_{s-1}` (`pcsa_strictFrom_of_within`). A frozen voter HEAD was
  accepted before `z_{s-1}`; the Clean windowed HEAD relay
  (`pcsa_head_relay_late_or_cap_win`) gives it, or a cap of its seat, at the
  proposer by `max t z_{s-1} + Δ = t_s`.
