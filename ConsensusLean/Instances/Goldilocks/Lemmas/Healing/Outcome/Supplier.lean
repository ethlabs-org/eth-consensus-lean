module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction

public section

/-! # Goldilocks Healing: the post-reset duty supplier (run level)

The objects of fradamt-agent/workbench `producer-reset-continuation.md` §22–§23 and
`phase-service.md` §10 (HS.2) after the reset `a = a_z`, stated over the run, for every consumer
(C1.2 here, H.3 (c)'s `reset_inv` through workbench#21), not specialized to C1.2's entries.
With `b = slot(a) + 3` (`cleanLabel`) and `R = t_{b+2k+2}` (`drainTime`, the `R_z` of C1.2):

* **RN, stored ancestry is irreversible** (§22): every lock stored at a later cut sits below a
  stored lock of its slot at an earlier cut, or below a fresh write between them
  (`stored_lock_below`, `SA.lock_provenance_from` on the AC projection). **RU** (§22) is
  `SA.unlock_compatible`: unlocking against a view with at least `n/2` validators whose slot-`s`
  support votes extend `B`, or that equivocate, moves every lock of a slot below `s` to a block
  compatible with `B`.
* **The drain** (§23, HS.2 (3)): from `R` on, every live lock has a label at least `b + k + 2`, so
  every lock with a label before `b` or a slow window straddling `b` has expired
  (`drain_live_locks`).
* **Clean fast transfer** (`clean_fast_transfer`, HS.2 (1)): the stored block of a fast lock of
  label `≥ b` written by an honest joined node is extended by every honest vote of a later slot,
  and is in the voter's viable voter block tree or at or below its `fc_root` there (HR.4 (R3)
  when it is high; inherited from a high seed when it is a low ancestor of one).
* **Clean slow transfer** (`clean_slow_transfer`, phase-service §10, HS.2 (2)): the raw slow
  selection `S` of an honest update of label `j` (`SA.SlowLockAt`) whose slow window is clean
  (`b + k − 1 ≤ j`) is extended by every honest vote of a later slot, and is in the voter's
  viable voter block tree or at or below its `fc_root` there.
* **The joined duty at honest ready proposals** (§23 "Joined duty conclusion", phase-service §10
  "Join with RN/RU"): for an honest ready proposal `P` of slot `u` with `t_u ≥ R`, every honest
  slot-`u` vote is `P` (`ready_unanimous`), and at every honest update of slot `u` (at
  `t_u + 6Δ`) the result is `P`, not vetoed, with fast selection `P`, and the FG source the tick
  returns extends `P`; or an honest accepted block has justified `P`'s entry by then
  (`ready_update`); and **report coverage** (`report_cover`, workbench#30 §2): by `t_u + 6Δ`
  every honest node has an actual report extending `P`, or one honest node has an actual higher
  report extending `P` (the supplier `entry_rows` consumes).

Interfaces: every theorem but `stored_lock_below`, `drain_live_locks` and `clean_fast_transfer`
(workbench#29 §9, over HR.4) is open; their paper proofs are workbench#6 §22–§23 and #7 §10,
conditional on HR.4. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The first clean evidence label `b = slot(a) + 3` after the reset `a`. -/
def cleanLabel (sp : SAParams) (a : Time) : Nat := sp.slot a + 3

/-- The drain time `R = t_{b+2k+2} = t_{slot(a)+2k+5}` (C1.2's `R_z`). -/
def drainTime (sp : SAParams) (a : Time) : Time := sp.ts (sp.slot a + 2 * sp.k + 5 : Nat)

theorem cleanLabel_eq (a : Time) : cleanLabel sp a = sp.slot a + 3 := by rfl

theorem drainTime_eq (a : Time) : drainTime sp a = sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) := by
  rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **RN, stored ancestry is irreversible** (§22): a lock that an honest node stores before cut
`b` sits below a stored lock of its slot before an earlier cut `a'`, or below the block of a
fresh fast write (an optimistic selection) or an update of its slot at a cut in `[a', b)`. -/
theorem stored_lock_below (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {a' b : Nat} (hab : a' ≤ b) :
    ∀ l ∈ (tr.projAC.state x b).locks,
      (∃ l' ∈ (tr.projAC.state x a').locks, l'.slot = l.slot ∧
        (l' = l ∨ ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧
          ∃ L' ∈ tr.HonestBlocks H, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L')) ∨
      ∃ j, a' ≤ j ∧ j < b ∧ ∃ B,
        ((∃ CV, SA.OptimisticLockAt tr.projAC x j l.slot B CV) ∨
          ∃ ℓ, SA.UpdateAt tr.projAC x j l.slot ℓ) ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Anc (tr.HonestBlocks H) L B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  exact SA.lock_provenance_from hr hx hab

/-- **The drain** (§23, HS.2 (3)): at a time `t ≥ R`, every live lock of an honest node has a
label at least `b + k + 2`; every lock of a label before `b`, and every slow lock whose window
straddles `b`, has expired. -/
theorem drain_live_locks {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {L : Set SA.Lock} {t : Time}
    (ht : drainTime sp a ≤ t) :
    ∀ l ∈ SA.liveLocks sp L Φ t, cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  rintro _ ⟨l, -, B, -, -, hk, rfl⟩
  have h0 : 0 ≤ t := le_trans (by
    simp only [drainTime, SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  have := (SA.ts_le_iff_le_slot sp h0 _).1 ht
  simp only [cleanLabel]
  omega

/-! ### The clean fast transfer -/

/-- `f < n/2` under `Healthy(g)`. -/
private theorem faulty_lt_half (hp : ResetPremises tr H dg g ΔF a) (x : Fin sp.n) :
    2 * Hᶜ.ncard < sp.n := by
  have := hp.healthy.2.2
  have := Fin.pos x
  have hn : sp.n = sp.toParams.n := rfl
  omega

/-- A fast lock of label `s` is written at or after `t_s` (the update of `s` runs at `t_s + 6Δ`,
an optimistic confirmation of `s` in slot `s`). -/
private theorem ts_le_of_fastLock (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time i = sp.ts s + 6 * sp.Δ := ht
    rw [ht']
    linarith
  · have hsl' : sp.slot (tr.time i) = s := hsl
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by omega)

/-- **The reset seed** (workbench#29 §9): a high origin `(O, l)` with `l ≤ slot(a)`. An honest
row of height `H_z + 1` is signed at `a` (`IsReset`); its source is below a high origin written
by the signer before the row (`high_row_source`), and a fast lock written by `a` has a label
`≤ slot(a)`. -/
private theorem reset_seed (hp : ResetPremises tr H dg g ΔF a) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ l ≤ sp.slot a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, rfl⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := high_row_source hp hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have h₁ : sp.ts l ≤ tr.time k := (ts_le_of_fastLock hp hfl).trans (hr.time_mono hrk.le)
  exact ⟨y, r, l, O, ho, by exact_mod_cast (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) l).1 h₁⟩

/-- In a coherent `U` containing the frame tree, a block `B` between a tree block `X` and a tree
block `O` above it (`X ⪯ B ⪯ O` in `U`, `X ⪯ O` in the tree) is below `O` in the tree. -/
private theorem frame_anc_of_between {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦU : Φ.tree ⊆ U)
    {X B O : SA.Blk sp.n (List (FG.Att sp.n))} (hXO : Φ.Anc X O) (hXB : Anc U X B)
    (hBO : Anc U B O) : Φ.Anc B O := by
  induction hXO generalizing B with
  | refl =>
    obtain rfl := Anc.antisymm hU hXB hBO
    exact .refl
  | tail _ hcd ih =>
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBO with rfl | ⟨c', hBc', hc'd⟩
    · exact .refl
    obtain rfl := hU.1 hc'd.1 (hΦU hcd.1)
      (Option.some_injective _ (hc'd.2.2.symm.trans hcd.2.2))
    exact (ih hXB hBc').tail hcd

/-- **Clean fast transfer** (§23, HS.2 (1), across phases): a fast lock of label `j ≥ b` that an
honest node joined at its write stores (after the move back) on `B` is extended by every honest
vote of a slot after `j`, and at that vote `B` is in the voter's viable voter block tree or at or
below its `fc_root` (inside the honest blocks). (A high `B` is an HR.4 high origin, (R3); a low
`B` can be an ancestor of a high seed, and then inherits the seed's transfer and witness.) -/
theorem clean_fast_transfer (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H)
    (hj : tr.JoinedAt x (tr.time i)) (hw : Compose.StoredFastLockAt tr x i j B CV)
    (hb : cleanLabel sp a ≤ j) :
    ∀ y ∈ H, ∀ k ℓ' e, SA.CastAt tr.projAC y k ℓ' e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ'.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ'.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ'.frame.fcRoot) := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hret := height_scoped_retention sp ro dg H tr g ΔF hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨hBt, D, hfl, hBD⟩ := storedFastLock_mem hp.run hp.noColl hx hw
  -- a high `B` is a high origin: (R3)
  by_cases hhigh : HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h
  · exact hret.votes x i j B ⟨hx, hj, ⟨CV, hw⟩, hhigh⟩
  -- a low `B` is below the reset seed `O`: the honest slot-`j` votes counted by the write extend
  -- `O` (R3, `l < j`), so `B ⪯ D` is comparable with `O`, and `O ⪯ B` would make `B` high
  obtain ⟨v, r, l, O, ho, hl⟩ := reset_seed hp
  rw [cleanLabel_eq] at hb
  have hDO : Compatible (tr.HonestBlocks H) D O :=
    SA.fastLock_compatible_of_votes hrun' hx (Nat.lt_succ_self i) hfl (faulty_lt_half hp x)
      fun z hz c _ e ⟨ℓ, hcl, he⟩ hsl =>
        (hret.votes v r l O ho z hz c ℓ e ⟨hcl, he⟩ (by omega)).1
  have hBO : Anc (tr.HonestBlocks H) B O := by
    have hc : Compatible (tr.HonestBlocks H) B O := by
      rcases hDO with h | h
      · exact Or.inl (hBD.trans h)
      · exact SA.anc_total hU hBD h
    rcases hc with h | h
    · exact h
    · exact absurd (high_of_anc hp ho hx hBt h) hhigh
  -- later votes inherit `O`'s transfer and witness
  intro y hy k ℓ' e hc hje
  obtain ⟨⟨Hd, hHd, hHdr, hOHd⟩, hO⟩ := hret.votes v r l O ho y hy k ℓ' e hc (by omega)
  refine ⟨⟨Hd, hHd, hHdr, hBO.trans hOHd⟩, ?_⟩
  rcases hO with ⟨hOS, hrO, W, hWS, hWv, hOW⟩ | hO
  swap
  · exact Or.inr (hBO.trans hO)
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  rcases SA.anc_total hU hBO (hrO.mono hΦU) with h | h
  · exact Or.inr h
  have hBOΦ := frame_anc_of_between hU hΦU hrO h hBO
  exact Or.inl ⟨SA.voterBlockTree_anc hr hy hc O hOS B hBOΦ,
    SA.anc_tree_of_anc_U hU hΦ hΦU (SA.mem_of_anc hrO hOS.1) h (SA.mem_of_anc hBOΦ hOS.1),
    W, hWS, hWv, hBOΦ.trans hOW⟩

/-- **Clean slow transfer** (phase-service §10, HS.2 (2), across phases): let an honest node `x`
write at cut `i` a slow lock of label `j` on the raw selected block `S` (`SA.SlowLockAt`, before
the move back), with a clean slow window (`b + k − 1 ≤ j`). Then every honest vote of a slot after
`j` extends `S`, and at that vote `S` is in the voter's viable voter block tree or at or below its
`fc_root` (inside the honest blocks). Every stored image of the lock is an ancestor of `S` (RN). -/
theorem clean_slow_transfer (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {S : SA.Blk sp.n (List (FG.Att sp.n))} (hx : x ∈ H) (hS : SA.SlowLockAt tr.projAC x i j S)
    (hb : cleanLabel sp a + sp.k ≤ j + 1) :
    ∀ y ∈ H, ∀ k ℓ' e, SA.CastAt tr.projAC y k ℓ' e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg S ∧
      (S ∈ ℓ'.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ'.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) S ℓ'.frame.fcRoot) := by
  sorry

/-- **The joined duty, unanimity** (§23; phase-service §10, "Join with RN/RU"): under the reset
premises and `Catch(2Δ)`, every honest vote of the slot `u` of an honest ready proposal `P` with
`t_u ≥ R` is `P`. -/
theorem ready_unanimous (hp : ResetPremises tr H dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u P)
    (hR : drainTime sp a ≤ sp.ts u) : Unanimous tr H u P := by
  sorry

/-- **The joined duty at the update** (§23, §17 "Exact remaining premise"; phase-service §10):
under the reset premises and `Catch(2Δ)`, for an honest ready proposal `P` of slot `u` with
`t_u ≥ R` and every honest node `z` running its update of slot `u` (at `t_u + 6Δ`, joined):
either the result is `P`, not vetoed, its fast test selects `P`, and every FG source `z` returns
at that time extends `P`; or an honest node has accepted, by then, a block `X` that justifies
`P`'s entry at `P`'s height (a retained justified crossing). -/
theorem ready_update (hp : ResetPremises tr H dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u P)
    (hR : drainTime sp a ≤ sp.ts u) {z : Fin sp.n} (hz : z ∈ H) {kz : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC z kz u ℓ) :
    (SA.getConfirmation sp (tr.projAC.state z kz) ℓ.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state z kz).locks ℓ.frame (tr.time kz) P ∧
      SA.fastSelect sp (tr.projAC.state z kz) ℓ.frame u P = some P ∧
      ∀ k' ℓ' C, SA.ToFGAt tr.projAC z k' ℓ' C → tr.time k' = tr.time kz →
        Anc (tr.HonestBlocks H) P C) ∨
    ∃ y ∈ H, ∃ k' X, tr.AcceptAt y k' X ∧ tr.time k' ≤ tr.time kz ∧
      Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k').fg P
        ((tr.post k').fg.σ P.root).h X := by
  sorry

/-- **Report coverage** (workbench#30 `entry-rows-exact.md` §2, the exact acquisition supplier
of `entry_rows`): for an honest ready proposal `P` of slot `u` with `t_u ≥ R`, by
`d = t_u + 6Δ` either every honest node has an actual `ac_to_fg` report `C` extending `P` (a
report that suppresses a later one counts at its own cut), or some honest node has an actual
report `C` extending `P` of a greater state height than `P` (a higher source). (`ready_update`'s
returned-source clause is vacuous when nothing is returned, and its crossing arm carries no
source; this supplier is the sharpened form.) -/
theorem report_cover (hp : ResetPremises tr H dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u P)
    (hR : drainTime sp a ≤ sp.ts u) :
    (∀ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  sorry

end Consensus.Goldilocks.Healing

end
