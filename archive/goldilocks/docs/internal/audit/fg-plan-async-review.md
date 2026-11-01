# Async-session review of the FG-module plan (455cf4a), 2026-09-28

Verbatim from the async-resilience session (cross-session message). 1 BLOCKING, 6 MAJOR, 7 MINOR, and answers to the plan's 4 questions. The async session did not edit the plan.

NJ scope: nothing in the plan ports DC's NJ recovery. The NJ-only list and "Out of scope" are correct. fjFrame (Task 6) matches r148 FJ_FRAME and the spec fg_frame line by line (H, lex pair with F ⪯ J, the contest test, Z/lo table, viable, D).

## BLOCKING

B1. Review Focus 1 (line 103) and Task 6 Step 1 (line 524) test the inverse of the rule. In a contest lo = H. The rule is: a child of a block with state height < lo is eligible WITHOUT a majority (spec lines 520–523; r148 `eligible(B) := h(B.parent)<frame.lo or ...`). So a child of a height-(H−1) block is eligible (TRUE) in a contest. It is not eligible (FALSE) in the uncontested or gap frame of the same tree, where lo = H−1. The purpose of the contest is exactly this: the walk must be able to leave H−1 without a majority (N12). The fjEligible definition is correct, so the written example fails, and an implementer can "fix" the definition to match the test. Fix: in the contested view, expect fjEligible = true for a child of a height-(H−1) block (majority false, slot not current). Add the same block in an uncontested view with the expectation false.

## MAJOR

M1. Task 7: liveFrame is not a spec object. The spec computes fg_frame(Σ,V) from the view. Σ.hmax is "archival; only finality acceptance reads it; no duty frame reads it" (spec lines 358–360). r148 §2 says "Do not calculate the contest from a live cache while calculating its height from a frozen view." Review Focus 2 and the Task 7 intro say "DC-fj reads the stored Σ.J, Σ.h_j and Σ.h_max". That is DC §7's structure, and no FJ proof covers it. Keep the lemma, but rename liveFrame to cacheFrame. Document it as a comparison object that the spec does not use. The spec reads the cache in one place only: update_finality tests σ.F ⪯ Σ.J. CacheInv.pair gives exactly that: Σ.J = the full-view lexMax. State that this is the purpose of the lemma.

M2. Task 8, line 730: "The finality pair uses finality_pair Λ h_j J h_F of the full-view pair" is wrong or ambiguous. In the spec (get_fg_vote, lines 1147–1170, "finality stays head-derived"), (h_j, J, h_F) = σ[H] of the full-view HEAD block H. They are not the frame's lexMax pair. createRow already takes them as parameters, so fix only the text: "the head block's state fields; the AP supplies the head".

M3. Task 12, inBandLock: the statement covers only the Λ.lock case. The pinned text also says "A same-action finality pair has the same property": in height_pair, `if h_c = h_f then lock ← T_f` (spec line ~1197). The contradiction does not use Λ; it uses only the carrier K. Fix: remove Λ, hlock and hne. State the positive form: under hC, hband, hsrc, hcar (K ∈ Vw with h_j(K) = h(C) and J.root = J'), hFJ' and uniqueness AT HEIGHT h(C) only (not huniq over all heights), conclude (derive C).T_h.root = J'. Both lock sources then follow: a past finality pair's carrier is kept in the full store; the same-action pair comes from the head.

M4. Task 13: monotone phase rank does not by itself prove "at most two EFFECTIVE changes". An effective change is a change of (Z, lo), and so of D. Add the corollary frame_of_phase: for k ≤ k′ with the same phase, fjFrame gives the same Z and lo. Proof: gap → (F, m−1); uncontested → (J, m−1) with the same J, because the carrier in Vs k is in Vs k′ and uniqueness holds; contested → (F, m). Only with this corollary do the two phase changes bound the frame changes.

M5. Task 9, provenance_entry: the pinned fact is "T is a prefix of the source C" (T ⪯ C). fj.descent and comp.provenance use this form. The Lean statement takes σ : ChainState, so it cannot state T ⪯ C. Fix: source : Option (FGBlock V) with σ = derive C. Conclude h = (derive C).h, T = (derive C).T_h.root, and (derive C).T_h ⪯ C. DC has the entry-ancestry lemma (NamedEntryHeight or StoreRoots).

M6. Q4 content: see answer 4 below. The duty-view lemma for the F basis is missing.

## MINOR

m1. Review Focus 4 (line 106) says "two justified entries at height 1". The construction in Task 6 (childA and childB target their parents at height 2) gives two entries at height 2 (B1a, B1b). B1a and B1b both justify genesis at 1: that is one pair. Fix the text.

m2. Task 11, crossingNoFinal: the E1 intersection needs the finality quorum at height j. Add the entry-height helper (a justified pair (h, J) has (derive J).h = h; DC NamedEntryHeight), or add the hypothesis (derive D).h_F = (derive B).h_j. The conclusion can be the stronger HasSlashableWeightBetween (chainRows W) (chainRows D). B is used only to identify J.

m3. Task 2, process_row: "a finality pair (h_j, J) with h_j > h_F sets the finality bit" must say "equal to the chain's own (σ.h_j, σ.J.root), with σ.h_j > σ.h_F" (exact entry, as in DC and the spec).

m4. Task 6, lexMax fallback (0, genesis): if F ≠ genesis and no pair in the view extends F, J = genesis and F ⪯ J fails. With the F basis in the view this cannot occur (answer 4). Document it, or make the fallback (h_F, F), but only if the spec says so. Otherwise keep it and prove the lemma of answer 4.

m5. Task 6, ghost: port the spec's ghost(anchor, tree, score, eligible) with anchor as a parameter. The walk starts at the live root (the deepest live lease in D, else Z), not at Z. The lease is AP data. The pin fj.frame.v1 includes fgsa_head, so either take the anchor as a parameter with the hypothesis anchor ∈ D ∪ {Z}, or mark the fjFrame pin partial ("walk start is AP data").

m6. Task 5: fg.accountable.v1 pins two sources. The r143 part also says "F advances only to a proper descendant; local F never retreats". update_finality_F_mono (old F ⪯ new F) is a one-line lemma. Add it, or record the r143 part as partial.

m7. The spec hash will change. After r154 (spec red-team, running now) the async session will fix spec wording, at least line 357 ("compatible" → F ⪯ J). The plan's Task 14 check will report CHANGED for the spec only if the spec is pinned. The spec is not a registry source, so this is only a note: re-read Fig. alg:fc-full and alg:client after the async spec commit. Also, fin-live-opus is checking whether FG-SA needs δ_t = 2R at all. Keep FGConfig.timeoutDelay a free parameter (δ_t = 0 allowed), and make no statement depend on δ_t > 0. The plan already does this; keep it so.

## ANSWERS

1. When the pending entries land, the statements match, with the fixes above:
   - Task 5: uniqueJust and finalLock are the pure disjunctive (slashable-or) forms of the a≤f facts. They are correct.
   - Task 9: needs M5 for "T ⪯ C". provenance_honestRow and provenance_finality match.
   - Task 10: matches the core. Its hypothesis hrows is weaker than "all rows pre-cut", which is good. The part "honest row height ≤ the signer's archival maximum" is provenance_entry (row height = the source state height) plus comp.cut. Mark coverage partial with that reason.
   - Task 11: needs m2.
   - Task 13: needs M4, and answer 3.
2. The split is acceptable in principle, with M3. hFJ′ is derivable in pure form: with no slashable weight between F's finality carrier and K, fg.finalLock gives F ⪯ K. Then the height order of the entries gives F ⪯ J′, or h_F > m, which contradicts F ⪯ C with h(C) = m. That form needs an F carrier in the view (the F basis). If you keep hFJ′ as a hypothesis, the coverage is partial, as you wrote. Replace global uniqueness by uniqueness at h(C).
3. A fixed F is not enough for the pinned text. fj-redteam.md:785–789 treats F moves: below m−1 → "below every band witness"; at m−1 → the same top J. Add a pure lemma (no run facts): for F ⪯ F′ with h(F′) ≤ m−1, if every W ∈ V with h(W) ≥ m−1 extends F′ and every pair at m−1 extends F′ (both follow from fg.finalLock), then phaseOf, Z (up to F → F′ in the F cases, where D is the same set) and D are unchanged. Otherwise record partial "F fixed" and list the F-move lemma as open work, not as out of scope.
4. The full-view equality under CacheInv is correct, but it is not the R1 content (see M1). R1 means that the frame is a function of the view. So for duty views V ⊊ Σ.T no equality with the store is intended; it is false by design. The Lean content that the duty views need is:
   (a) F-basis lemma (Lean form of fg.frameCompat (ii)): if V contains a block K with F ⪯ (derive K).J, then F ⪯ (fjFrame F V).J and the lexMax is at least (derive K).h_j, so the fallback is never used. Keep an fBasis field in Store and prove that update_finality keeps "the J carrier in fBasis has F ⪯ J" (spec line 749: at acceptance σ.F ⪯ Σ.J).
   (b) Monotonicity in the view: V ⊆ V′ ⇒ frontier V ≤ frontier V′, and lexMax V ≤ lexMax V′. Task 13 needs these, so state them as lemmas.
   Add (a) and (b) to Task 7 and remove "a duty view is not compared with the store" as a reason. The correct reason: the spec gives each duty its own frame, and the only store reading of the cache is the acceptance test (M1).

## Follow-up notes (registry commits 3ed676c, 0ff5a6c)

- The registry edits are committed: 3ed676c (the splits: 13 new ids, 5 SUPERSEDED) and 0ff5a6c (a "Lean plan" column; DC-fj marks for the 9 pinned ids; "not planned for Lean now" on 16 NJ entries).
- The finalized-crossing law is at fj-redteam.md:226, not :236.
- DC paths at verified-consensus b97b902: Engine.lean:243 justification_unique_per_height (the _slashable form is at :261); FinalityComparison.lean:50; WeakHeightBounds.lean:42.
- DC Lean has only the certificate form of fg.uniqueJust.v1 (two target quorums for different entries give 2q−W E2 weight); "a≤f, so one entry" is on paper. Task 5's disjunctive form is exactly the Lean part (full coverage of what is in Lean).
- fg.frameCompat.v1 is marked "Lean plan: none". If the plan adds the F-basis lemma (answer 4a), pin it to fg.frameCompat.v1 with partial coverage "(ii) only, F ⪯ J form"; the async session then changes the mark.
- AP-side gap (not this module): ap.S.v2, ap.Sslow.v1 and comp.theoremN.v1 use fg.N2.v2, which is in the NJ frame. An FJ Kept/N2 form (with lo) will be a new fj entry for the later Kit.Compose work.
