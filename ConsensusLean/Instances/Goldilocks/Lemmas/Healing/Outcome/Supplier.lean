module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service

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
* **Clean fast origins are high** (`clean_fast_high`): a stored fast lock of label `≥ b` written
  by an honest joined node is a high origin of HR.4, so HR.4 (R3) transfers it.
* **Clean slow transfer** (`clean_slow_transfer`, phase-service §10, HS.2 (2)): a raw slow
  selection `S` of an honest result of label `j` whose slow window is clean (`b + k − 1 ≤ j`)
  is extended by every honest vote of a later slot, and is in the voter's viable voter block
  tree or at or below its `fc_root` there.
* **The joined duty at honest ready proposals** (§23 "Joined duty conclusion", phase-service §10
  "Join with RN/RU"): for an honest ready proposal `P` of slot `u` with `t_u ≥ R`, every honest
  slot-`u` vote is `P` (`ready_unanimous`), and at every honest update of slot `u` (at
  `t_u + 6Δ`) the result is `P`, not vetoed, with fast selection `P`, and the FG source the tick
  returns extends `P`; or an honest accepted block has justified `P`'s entry by then
  (`ready_update`).

Interfaces: every theorem but `stored_lock_below` and `drain_live_locks` is open; their paper
proofs are workbench#6 §22–§23 and #7 §10, conditional on HR.4. -/

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

/-- **Clean fast origins are high**: under the reset premises, a fast lock of label `j ≥ b` that
an honest node joined at its write stores (after the move back) is a high origin of HR.4, so
(R1)–(R3) of `height_scoped_retention` apply to it. -/
theorem clean_fast_high (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H)
    (hj : tr.JoinedAt x (tr.time i)) (hw : Compose.StoredFastLockAt tr x i j B CV)
    (hb : cleanLabel sp a ≤ j) : HighOrigin tr H g x i j B := by
  sorry

/-- **Clean slow transfer** (phase-service §10, HS.2 (2)): let an honest node `x` get the result
`C` of its update of slot `j` at cut `i`, whose slow window is clean (`b + k − 1 ≤ j`), and let
`S` be a block of `C`'s confirmation path that passes the slow test there (each saved result of
the `k − 1` previous slots is a block of the frame extending `S`). Then every honest vote of a
slot after `j` extends `S`, and at that vote `S` is in the voter's viable voter block tree or at
or below its `fc_root` (inside the honest blocks). -/
theorem clean_slow_transfer (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {C S : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksNode sp ro)}
    (hx : x ∈ H) (hR : SA.ResultAt tr.projAC x i j C CV) (hu : SA.UpdateAt tr.projAC x i j ℓ)
    (hb : cleanLabel sp a + sp.k ≤ j + 1)
    (hS : S ∈ SA.confirmationPath sp ℓ.frame C)
    (hslow : ∀ j' : Int, (j : Int) - sp.k < j' → j' < j →
      ∃ S' ∈ ℓ.frame.tree, (tr.state x i).ac.saved j' = some S'.root ∧ ℓ.frame.Anc S S') :
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

end Consensus.Goldilocks.Healing

end
