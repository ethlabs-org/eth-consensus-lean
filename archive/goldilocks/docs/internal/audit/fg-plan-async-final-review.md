# Async-session final review of the FG-module plan (2b080ef), 2026-09-28

Verbatim from the async-resilience session (cross-session message). Scope: diff 897fe6e..2b080ef (ALFS restructure, fj.frame.v2 pins, Astra K01/K02). The async session did not edit the plan.

Final review of the FG plan at 2b080ef (diff 897fe6e..2b080ef): ADOPT WITH FIXES. 0 BLOCKING, 0 MAJOR, 3 MINOR.

(1) The Lean definitions against the ALFS archive 183f2c40, line by line:
- Store.init = spec 429–437 (T = TF = {genesis}, hmax = 1, F = J = genesis, h_j = 0). OK.
- update_finality = spec 809–822: hmax first, then J by lex with F ⪯ σ.J, then F with strict F ≺ σ.F, σ.F ⪯ Σ.J and viable_tree read after both writes. OK. acceptViable = viable_tree 936–942 (TF, hmax−1, also in a contest). OK.
- on_block = spec 747–779: raw T first, admission iff F ⪯ B, update_finality only for admitted blocks. OK. StoreInv.admits/closedF follow because F only moves up.
- storeControls = fg_contest/band_floor/get_fg_root (910–926, 944–951). OK. Controls.Z/lo match the table. filteredFrom = viable_tree_from + root cut (928–934, 953–960). OK. storeFrame = get_filtered_block_tree(_from). OK.
- I also checked that the chain-state and client functions (state_transition, process_attestation, process_height_events, advance_height, finality_pair, height_pair, create_attestation, record_attestation) are the same in ae4497ab and 183f2c40, apart from \Comment text. So the ports from ae4497ab are correct.

(2) The pins state their math. The partial markers are right (fj.frame.v1: frame only; the view vs store forms are labelled on each lemma). storeControls_eq_fjControls under StoreInv is the right central statement. filteredFrom_Z_mem (K02) is exactly clause 3 of ap.headReachesLo.v2.

(3) The SA handoff text (Out of scope and Later work) matches ap.headReachesLo.v2 clauses 1–4 as registered in 250db63, including the anchor fallback and "before the boundary, part of ρ".

(4) r158 (the Astra red-team of the ALFS spec) is DONE: codex/alfs-redteam.md. No critical or high finding. P1, clean, FG safety, uniform healing 1004Δ and first finality 1049Δ are PROVED (paper). The H12 transfer gives 996Δ and 1041Δ. NJ clean/P1/local healing are PROVED (NJ uniform healing is SKETCH). Nothing changes the text of the fj.frame.v2 functions. Its medium findings concern proofs and the SA vote merge: M1, a witness repair (supplied, and consistent with the conditional form of ap.headReachesLo.v2); M2, the raw-proposal vote merge (an AP/spec point); M3, δ_t < 2R is outside the port. I will move fj.frame.v2's status from "red-team pending" to "def; r158 found no issue in the frame functions" and send you the commit id.

MINOR
m1. Global Constraints (line 55) and Task 6 (line 739) still take ae4497ab as the executable reference for everything except Tasks 6–7, and they cite its fg_frame (852–876) for the view form. The ported functions are the same (see (1)), but ae4497ab also contains the removed R1/F-basis and raw-only-row rules. Make 183f2c40 the single executable reference, and cite r148 FJ_FRAME (the fj.frame.v1 pin) for the view form fjControls/fjFrame. That removes the mixed reference.
m2. on_block's docstring says "the slot, signature and round checks … are the AP's". The row-round check (spec 757–760, "no row from the block's future") is DC §7's FG rule, not an AP rule. Keep it outside the Lean on_block if you want, but call it an admission precondition from the FG spec (a hypothesis of storeInv_on_block, or a documented input contract), not AP data.
m3. storeInv_on_block assumes ViewRootInj (insert B st.TF) even when B is not admitted. This is harmless but stronger than needed; ViewRootInj st.TF suffices in the non-admitted branch. Optional.
