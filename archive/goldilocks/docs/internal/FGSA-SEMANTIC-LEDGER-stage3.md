# FG5c stage-3 semantic ledger

Authority: FG5 lead rulings 1, 2, 4, 6, and 7 (2026-10-02), plan section 3.5,
and spec fgsa-protocol.tex at 59bb0dda. This candidate implements the approved
window fold and R6W. The full build and local proof guards pass. Reviewed by J5
(Astra + Opus, 2026-10-02: LAND WITH FIXES; lead ruling in fg5-rulings.md).

1. **Reachable and epochs.** `admitBlock` now uses `Window.on_block p p.K_W`.
   The concrete protocol, epochs, and run claims therefore describe W execution.
   Evidence: `fg_on_block_accepts`, `admitBlock_accepted_eq`, `fg_step_cases`,
   and the admission tests in `AvailableChainFGSA/Tests/WindowAdmission.lean`.
2. **CStoreInv.fg and Inv0.** Their generic store invariant now uses W finality.
   Evidence: `fgStoreSafety` uses `Window.windowStoreSafety`; the initial and
   step proofs use the restated FG3 invariant. The structure gains no field.
3. **RFrame.** Its step and row-selection clauses use the W updater and R6W.
   Every row is tested against the same pre-fold parent. Evidence:
   `rowsValidForParent_iff`, `Window.rowValidW_fold`, `mem_proposalRowsFor_iff`,
   and the common-parent admission test.
4. **RCert, RQCOrigin, finality observations, and accountability.** Finality
   fields in `RCert` (conjuncts 3 and 4), `certified`, `RQCOrigin`, `RXing`,
   `FGFinalizedAt`, cap/lag, crossing premises, and composition carrier
   premises read `finalityView`. Height-only clauses keep their text.
   Evidence: `fgCertificateLaws` uses `Window.windowCertificateLaws`;
   `fgsa_rCert` uses those laws; source proofs use `Window.window_final_birth`
   followed by the birth's target certificate. No complete-fold equality is used.
5. **Client h_F.** `fgInputs` reads `Window.headFields`; the shared
   `createRowOnce` action remains. Evidence: `fgInputs_headFields`,
   `emitted_finality_pair_of_headFields`, and the window head-field test.
6. **Stale-row validity and exclusion.** `parentFoldState` is the W parent;
   admission and selection use `Window.rowValidW`. Useful stale rows can pass.
   R6W alone does not imply HeightMatch. Evidence: the replacement
   `validForParent_currentHeightMatch` excludes the stale arm using the current
   height bound; admission tests cover useful, unmatched, future, and wrong-entry rows.

The latest-only finality bit interface is retired by ruling 4.
`row_bit_persist` now covers only target and progress over H. The Run
`fgsa_rowBitPersist` form is equivalent to its earlier height-only form by Boolean
cases and the height bridge. The decoded-row form also supplies batch coverage.
`rowValidFor_finality_persist`, `rowValidFor_finality_irrel`,
`rowValidFor_progress_first`, `validForParent_heightMatch`, and
`finalityView_eq_simplex` are removed. None is in the frozen API file.
The old `rowValidFor` definition, its `rowValidFor_iff` and `rowValidFor_fold`
proofs, and `fgStoreInvariant_on_block` also leave active use. The window
validity proofs and store-safety instance supply the replacement interfaces.
The removal of the Claims guard tuple entry is recorded in
`scripts/guard-lists-allow.txt`; all removed check-fgsa.sh expectations must be
listed in the writer report, since guard-lists does not check them.

Ruling 7 defers the height-only Claims text to J6. Unchanged manifest hashes
do not establish unchanged meaning: controls and store readers can hide a
changed public definition from the generated/private dependency hash.


## Named Claims whose meaning changes only through a model body (J5 X2)

Their source text is unchanged; their meaning moves with W. Route in brackets.

- Through `fgInputs` (client head fields now read W, including W h_F): `actionTriple`,
  `fgClientEvent`, `fgClientEvents`, `EmittedRowsNoSlash`, `ClientSafeAll` /
  `ClientSafetyClaim`.
- Through `rowsValidForParent` / `ValidForParent` (now R6W): `excludesFixed`,
  `invalidForParent`, `TRowsSelect`, `TRowsSync`, `BatchPrem.valid`. `TRowsSelect`
  and `TRowsSync` now oblige the proposer to carry useful STALE rows as well
  (spec :798–812); both are proved (`RowService.lean:224`, `:297`).
- Through the store F (now the W F): `F_at`, `FAdvanceAt`, `AcceptsFinalBefore`,
  `finalizedOut`.
- `RXing`: a composition premise (`ComposeStmt.lean:459`) with no producer; it
  now speaks about the W h_F.
- `J_mem` and `store_accountable` read finality only through `finalityView`. This
  is safe after J4 only because `finalityView` then reads W (lead condition for the
  J4 landing; the old-read audit lists `finalityView`, not these two).
- Through W reachability, W stores and W outputs (Claims families, Astra J5
  table): `StoreAt` / `StoreClaim`, `ActiveViewAt` / `ActiveViewClaim` (W accepted
  F), `ChainCertificatesAt` / `ChainCertificatesClaim` (RCert supplies W f),
  `SourceDisciplineAt` / `SourceDisciplineClaim` (W run, RQCOrigin, certified),
  `ReconcileClaim`, `OutputNestingAt` / `OutputNestingClaim`, `FrameAt` /
  `FrameClaim` (W update and R6W channels), `CleanHistoryAt` and its claim
  wrappers, `CleanTruncAt` / `CleanPrefixTruncationClaim`, `CleanSafetyAt` /
  `CleanSafetyClaim`, `SameLabelAt` / `SameLabelClaim`, `HeadReachesLoClaim`,
  `ReleaseAt` / `ReleaseClaim`.
- Bridge-equal readers, no per-block meaning change: `HeightMatch` (through
  `parentFoldState`), and `frameR`, `domainR`, `jointSource`, `proposerHead`,
  `FrameAt`, `HeadReachesLoAt` (through `controls`); the ruling-7 height readers
  (`RGeo`, `SourceDisciplineBaseAt`, `EntryBelow`, Fold / Witness / ComposeStmt
  heights) until J6.
- `certified`: its F arm is a subset of its J arm before and after J4 (the W F is
  `(derive C).J` for some C ⪯ W, by `window_final_birth`), so the set content does
  not change (J5 Opus N1; RCert conjunct 4 states the same fact).

"the unproven regime Props (FinalitySet, Recurrence, Regimes) now nominally describe W runs with old bounds: not re-validated until stage 4"

J6 / FG5d: height-only readers now read heightView; bridge-equal; no meaning change

S4.6: G-F0b W surface integrated; dropped exports removed; no meaning change of kept claims
