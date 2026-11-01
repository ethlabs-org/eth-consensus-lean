The revision resolves the original blocking defect. Two major issues and two minor inconsistencies remain. Here, **RESOLVED** means the plan repair is sufficient; implementation is still pending.

References: P = [revised plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase1b-instances.md); CV = `CrossView.lean`, PV = `ProposalViewRelay.lean`; these and `Paths.lean` and `Proposals.lean` are under `AvailableChainGridCO/Proofs/`. L = `AvailableChainLStar/Model/Protocol.lean`.

```text
┌─────────────┬───────────┬───────────────────────────────────────────────┬───────────────────────────────────┐
│ Item        │ Status    │ Evidence                                      │ Fix if needed                     │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-01      │ RESOLVED  │ P:270–271 adds the missing L* proposal clause  │ None for the clause; see N3.       │
│             │           │ and requires permanence and disjointness      │                                   │
│             │           │ proofs.                                       │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-02      │ PARTLY    │ P:347 fixes G = 1, but P:379 still promotes    │ Replace the family rule; see N1.   │
│             │           │ hidden assumptions to LEAN (family).          │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-03      │ RESOLVED  │ P:381 gates result cells by status and         │ None; N1 concerns the input       │
│             │           │ separates cond, gap and unsound.              │ status.                           │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-04      │ RESOLVED  │ P:380 resolves the base projection and tests   │ None.                             │
│             │           │ both SA-PC profiles on one instance line.     │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-05      │ PARTLY    │ P:224 assumes an o parameter, but Paths:288    │ Quantify over accepted proposal   │
│             │           │ has none; its proof obtains o at :308.        │ wires; include the caller at      │
│             │           │                                               │ Paths:357.                        │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-06      │ RESOLVED  │ P:145,164 preserves Framework.Kit and keeps    │ None.                             │
│             │           │ both existing transitivity lemmas.            │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-07      │ RESOLVED  │ P:388 leaves the Counter run/step helper work  │ None.                             │
│             │           │ open for plan 1c.                             │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-08      │ RESOLVED  │ P:47,52 lists the other relay uses and states  │ None.                             │
│             │           │ that a general run construction is not        │                                   │
│             │           │ proved.                                       │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ P1b-09      │ RESOLVED  │ P:60 states that the import boundary is a      │ None.                             │
│             │           │ choice made by this plan.                     │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ M1          │ RESOLVED  │ P:245–256 gives the case split; CV:72–74 and   │ None; preserve strict receipt     │
│             │           │ PV:73–75 already allow equivocation.          │ stamps.                           │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ M2          │ RESOLVED  │ P:224–228 covers both deadlines at CV:28–35    │ None for M2; Paths needs the      │
│             │           │ and Proposals:114–120 without stability.      │ P1b-05 repair.                    │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ M3          │ RESOLVED  │ P:270 matches L:283,315; a stored block        │ None for the clause; see N3.       │
│             │           │ prevents that missing wire from ever entering │                                   │
│             │           │ proposals.                                    │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ Family / N1 │ NOT       │ The scratch check gives isProp = false for    │ Use the exact family rule below.  │
│             │           │ HiddenAssumption and Nat → HiddenAssumption;  │                                   │
│             │           │ all axioms pass.                              │                                   │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ N2          │ NEW MINOR │ P:367 says only G = 1 forms are rows, but      │ Say only G = 1 forms are result   │
│             │           │ P:383 includes the conditional *_of_pos rows. │ rows.                             │
├─────────────┼───────────┼───────────────────────────────────────────────┼───────────────────────────────────┤
│ N3          │ NEW MINOR │ P:391 still tells Task 7 to document only the │ Include the stored-block proposal │
│             │           │ L* equivocation refusal.                      │ refusal.                          │
└─────────────┴───────────┴───────────────────────────────────────────────┴───────────────────────────────────┘
```

M1’s fix is sound and sufficient. Split **before** applying `accepted_head_receipt_before`. In the excluded branch, the time bound rules out old-label exclusion. For CrossView, events in `stateBeforeTime X` are strictly before `X`; their receipt stamps remain below `X ≤ cut` in the later state. Thus the existing stamped-equivocation conclusion applies. For ProposalViewRelay, vote monotonicity gives its existing equivocation conclusion.

M2’s fix is sound and sufficient for the two identified lemmas. Apply `hx` at `max t E.t_GST + E.Δ` or `t + E.Δ`, using the branch’s existing cutoff bound. No exclusion-stability or schedule premise is needed.

M3’s fix is sound and sufficient. The membership test keeps exclusion disjoint from `processed`. Stored blocks remain stored, and the admission guard prevents every later insertion of the missing proposal wire. The scratch proof also confirms that `process` leaves any proposal for a stored block unchanged.

**Remaining P1b-05 — MAJOR.** The repair covers proposal relays in principle, but its literal interface does not fit [Paths.lean:288](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/Paths.lean:288). Require non-exclusion for **every accepted proposal wire for `B`**, at every `u ≤ earlyTime p r`. Instantiate that premise with the witness obtained at line 308. Add the caller at line 357 to Task 1’s list. An unrelated implicit `o` would not supply the required fact.

**New N1 — MAJOR; counted with P1b-02.** A data binder can contain an unproved assumption:

```lean
structure HiddenAssumption : Type where
  proof : False

def boxedCert (h : HiddenAssumption) :
    Cert includedConfirmed Registry.Sanity.sanity :=
  False.elim h.proof
```

This [checked example](/private/tmp/phase1b-recheck-w6tgz4ty/FamilyCheck.lean:6) has a data binder and only allowed axioms. The proposed rule would give it `LEAN (family)` and a MATRIX `cert` result, although Sanity inclusion is already refuted. The universal function is valid but has no argument. The same defect occurs with `h : Nat → HiddenAssumption`.

The function distinction matters: `Nat → False` is a Prop and must be detected as such. `Nat → Prop` is a type of predicates; that binder alone supplies no proof that a predicate holds.

Use this exact, conservative rule for plan 1b:

1. Open the complete binder telescope and use `Lean.Meta.isProp` on each binder type. Include implicit and instance binders.
2. Keep every open row `CONDITIONAL` by default. A non-Prop binder is insufficient for promotion.
3. Permit `LEAN (family)` only for the approved Task 5 `profile-holds` templates: exactly one parameter of type `GridCO.Params` or `SA.Params`, the corresponding instance application, the specified catalog profile, and `G = 1`. Permit no extra binders or narrower parameter subtypes.
4. Require a closed, axiom-checked `Nonempty` proof for each approved parameter domain. Show the exact domain and retain its documented constraints. Check the row theorem’s axioms and preserve `KNOWN-GAP` handling.
5. Any additional family shape needs an explicit domain and a checked proof over that whole domain. Any remaining assumptions must be discharged for every domain value before promotion.

Do not ban all Prop fields: the real parameter records contain such fields. The rule must expose the domain and check its use. A parameter-domain witness does **not** establish execution-regime inhabitation.

**New N2 — MINOR.** Align Task 5’s row wording with Task 6’s explicit inclusion of conditional rows.

**New N3 — MINOR.** Correct Task 7’s L* summary so the handoff records both permanent refusals.

No repository file was changed by this review. The scratch file passed `lake env lean`; no full build ran. Counts below treat N1/P1b-02 as one issue.

VERDICT: REVISE  
RECHECK COMPLETE: 0 blocking, 2 major, 2 minor