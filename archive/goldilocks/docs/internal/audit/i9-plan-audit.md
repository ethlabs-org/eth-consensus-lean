# Astra audit: I9 derived block roots plan

You are an auditor. Work read-only in `lean/available-chain` (paths below are
relative to it). Write prose in ASD-STE100 Simplified Technical English and
tables in Unicode box drawing inside fenced `text` blocks.

## Object

The plan `docs/plans/2026-09-29-i9-derived-roots.md` (main, after d0d913a).
It implements the user's I9 decision (design `docs/FRAMEWORK-DESIGN.md` §12,
the I9 note with both points of 2026-09-29) in the **store-only** variant.
Inputs: r203 `../../research/async-resilient-committees/tip-stability/codex/derived-root.md`
and `codex/scratch/r203-followups.md` (with its evidence in `codex/scratch/r203/`),
the survey `claude-files/i9/survey.md`, and `docs/PHASE1B-REPORT.md`.

This change is "really major" under the user's rule: it breaks the catalog
lock (about 101 CHANGED lines) and changes the shared `Block` type under every
protocol and FG-SA. Audit it fully.

## Questions

1. **Faithfulness to the user's decision.** Does the store-only variant
   (payloads keep resolved blocks; the store check is `blockKnown st b.parent`
   with the lemma `b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root`;
   no wire root check; `excludes` unchanged) implement "the block's root
   cannot go in the block itself; the block carries its parent's root; the
   store check is 'do I have a parent with that root'; no wire check"? Name
   any place where it does not.
2. **Codec (D4, Task 0).** Is the proposed linear self-delimiting `lpair`
   (trailing-ones length code, then `b`, then `a`) injective as defined? Is
   the size bound right? Is kernel evaluation of these operations accelerated
   in Lean 4 v4.30 (check which `Nat` operations the kernel accelerates)? Is
   there a simpler injective linear-size codec with an easier proof? Check the
   survey's claim that `Nat.pair` roots of the G02 FG chain reach about 10^13
   bits (`claude-files/i9/pairsize.py`).
3. **Universal injectivity (Task 1).** Is the induction sound as specified,
   including slot-0 nodes and genesis separation? Does anything in the tree use
   `Block` in a way that needs a root that is not a function of content?
4. **The three-case lemma (Task 1 Step 4).** Is it statable and true as
   written for the four state-free `wellFormed` parent-slot tests
   (GridCO:337, SAPC Handlers:65, L*:300, FGSA Handlers:96)? Is "outside
   ExecutionValid" equivalent to "delivered but waits forever" for the relay
   obligations of `PartialSynchrony` and `HealthyPrefixDelivery`
   (`AvailableChainStatements/Generic/Conditions.lean:104-151`)? That is: does
   a delivery of a deps-missing wire leave the state unchanged in every
   protocol's `process`?
5. **FG-SA (Task 9).** Is the packing (`packBody`, `rowsOk`, `fgBlock` from
   decoded content) enough for `eraseFG (fgBlock P b rows) = b`, the erasure
   law, `MetaInv.wireTree` preservation, and `ContentAgree` across two stores?
   Does adding `rowsOk` to `wellFormed` and `blockAccepted` create a permanent
   refusal that needs an `excludes` clause when FG-SA gets a `ProtocolSpec`
   (T7)?
6. **Task order and build states.** The type change breaks every downstream
   library. Is the per-library order (Model → Statements → Kit/EngineV2/
   Framework → GridCO/SA → SA-PC → L* → Registry/Witnesses → SimplexFG → KitFG
   → FG-SA → docs → lock/merge) consistent with the import graph
   (`lakefile.toml`, imports)? Is any library missing from the order?
7. **Lock break.** Is the predicted CHANGED set (`codex/scratch/r203/lock-impact.tsv`)
   right for the store-only variant? Would any Framework declaration change
   its text? Is the stop rule of Task 11 adequate?
8. **Statements.** List any theorem whose statement must change beyond the
   plan's allowance (old root field, old formula, numeric root value), and any
   protected statement (Global Constraints) that the change would force to
   change.
9. **Fixtures.** For each fixture in the survey's §4 table, is the plan's
   instruction enough to keep its intent? Name any whose intent cannot be kept
   under derived roots, besides the two the plan names (SimplexFG Frame
   collision, FG-SA DQ2).
10. **Missing sites.** Using r203's inventory and the survey, name any site
    that the plan's task file lists omit.

## Output

`VERDICT: ADOPT | ADOPT WITH FIXES | REVISE | REJECT`, a findings table (id,
severity BLOCKING/MAJOR/MINOR, evidence file:line, fix), then the answers to
questions 1–10. End with `AUDIT COMPLETE: <b> blocking, <m> major, <n> minor`.
