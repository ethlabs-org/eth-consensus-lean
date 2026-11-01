module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

public section

/-! # Goldilocks Healing: post-reset source and transport foundations

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

`Outcome.Pivot` consumes these source facts. The downstream `Outcome.Supplier` retains
`ready_unanimous`, `ready_update` and `report_cover`; this separation lets those suppliers
use the pivot without an import cycle. `clean_result_next_votes` remains open here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

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
theorem stored_lock_below (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {a' b : Nat} (hab : a' ≤ b) :
    ∀ l ∈ (tr.projAC.state x b).locks,
      (∃ l' ∈ (tr.projAC.state x a').locks, l'.slot = l.slot ∧
        (l' = l ∨ ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧
          ∃ L' ∈ tr.HonestBlocks H, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L')) ∨
      ∃ j, a' ≤ j ∧ j < b ∧ ∃ B,
        ((∃ CV, SA.OptimisticLockAt tr.projAC x j l.slot B CV) ∨
          ∃ ℓ, SA.UpdateAt tr.projAC x j l.slot ℓ) ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Anc (tr.HonestBlocks H) L B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
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
private theorem faulty_lt_half (hp : ResetPremises tr H proposer dg g ΔF a) (x : Fin sp.n) :
    2 * Hᶜ.ncard < sp.n := by
  have := hp.healthy.2.2
  have := Fin.pos x
  have hn : sp.n = sp.toParams.n := rfl
  omega

/-- A fast lock of label `s` is written at or after `t_s` (the update of `s` runs at `t_s + 6Δ`,
an optimistic confirmation of `s` in slot `s`). -/
private theorem ts_le_of_fastLock (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
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
private theorem reset_seed (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ l ≤ sp.slot a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
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
theorem clean_fast_transfer (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H)
    (hj : tr.JoinedAt x (tr.time i)) (hw : Compose.StoredFastLockAt tr x i j B CV)
    (hb : cleanLabel sp a ≤ j) :
    ∀ y ∈ H, ∀ k ℓ' e, SA.CastAt tr.projAC y k ℓ' e → j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ'.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ'.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ'.frame.fcRoot) := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
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

/-! ### The clean slow transfer -/

/-- **Clean regular-result transfer to the next slot** (open; the T3 paper orb's target): under the
reset premises, every honest vote of slot `j + 1` extends the result `R` of an honest joined update
of a clean label `j ≥ b` (fast, sub-fast or vetoed). -/
theorem clean_result_next_votes (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {i j : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H)
    (hR : SA.ResultAt tr.projAC x i j R CV) (hb : cleanLabel sp a ≤ j) :
    ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → e.msg.slot = j + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg R := by
  sorry

/-- A deepest block of a set is the one `deepest` returns. -/
private theorem deepest_eq_of_isDeepest {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.IsDeepest Φ S D) : SA.deepest Φ S = some D := by
  have hex : ∃ B, SA.IsDeepest Φ S B := ⟨D, h⟩
  cases hd : SA.deepest Φ S with
  | none =>
    unfold SA.deepest at hd
    simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := SA.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- An honest validator is not an equivocator in an honest node's pool of a slot. -/
private theorem honest_not_equivocator_pool (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n}
    (hy : y ∈ H) (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ SA.equivocators {v | v ∈ (tr.projAC.state y c).pool s} := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  rintro ⟨v, hv, w, hw, hvw, rfl, hwv⟩
  obtain ⟨jv, -, ev, hev, rfl⟩ := hrun.honest.pool_vote y hy c s _ hv hu
  obtain ⟨jw, -, ew, hew, rfl⟩ := hrun.honest.pool_vote y hy c s _ hw (hwv ▸ hu)
  rw [hwv] at hew
  obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ _ hr _ hu jv jw ev ew hev hew
    ((SA.state_pool_slot sp hr hy c s _ hv).trans (SA.state_pool_slot sp hr hy c s _ hw).symm)
  exact hvw rfl

/-- The existing node premises supply all four fields of the healthy AC projection. -/
theorem healthy_base_of_reset_catch (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g :=
  ⟨Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl,
    projection_driven hp.run hp.noColl hp.run.genesis_root_ok hp.healthy,
    projection_healthy hp.run hp.noColl hp.healthy,
    projection_catch hp.run hp.noColl hp.healthy hc⟩

/-- Catch uses its actual source boundary `gbar g`, not the later high-origin cut. -/
theorem catch_window_of_reset_catch (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (Q : Time) :
    CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) (SA.gbar g) (2 * sp.Δ) Q :=
  ⟨fun x hx i B ha hi y hy j ell hj ht _ hF =>
    projection_catch hp.run hp.noColl hp.healthy hc x hx i B ha hi y hy j ell hj ht hF⟩

/-- The raw-target service window starts at the same boundary as Catch. -/
theorem reset_raw_sync_window_before (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time) :
    SyncACWindowBefore H (tr.HonestBlocks H) (SA.gbar g) Q tr.projAC := by
  have hs := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (SA.gbar g) Q hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 (SA.le_gbar g))
  have hsource : ∀ y j (t : Time), t ≤ tr.projAC.deadline y j t := by
    intro y j t
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases tr.projAC.lastWake y j with
    | bot => change t ≤ t + sp.Δ; linarith
    | coe w =>
      change t ≤ max t w + sp.Δ
      have := le_max_left t w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj hQ hd
    exact hs.1 x hx i m hm hi ((hsource y j _).trans hQ) y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj hQ hd hF
    exact hs.2 x hx i B hB hi ((hsource y j _).trans hQ) y hy j ell hj hd hF

/-- Clean labels start after the high seed and leave the whole slow window after GST. -/
private theorem clean_source_timing (hp : ResetPremises tr H proposer dg g ΔF a)
    {s : Nat} (hs : cleanLabel sp a + sp.k + 2 ≤ s) :
    cutZ sp.toParams g ≤ sp.ts s ∧
      SA.gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1) := by
  obtain ⟨v, r, l, O, ho, hl⟩ := reset_seed hp
  have ht := cutZ_le_ts_of_highOrigin hp ho
  have hz := lt_cutZ sp g
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rw [cleanLabel_eq] at hs
  constructor
  · exact ht.trans ((SA.ts_le_iff sp).mpr (by omega))
  · have hle : sp.ts ((l : Int) + 1) ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (SA.ts_le_iff sp).mpr (by omega)
    have he : sp.ts ((l : Int) + 1) = sp.ts l + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; ring
    rw [he] at hle
    linarith

/-- Current raw-target keep/root/floor step. Actual source heldness and honest counted
support feed the domain reduction; earlier support is strictly cut-bounded. -/
private theorem clean_source_vote_domain_step
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r s i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrQ : tr.time r ≤ Q)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hiQ : tr.time i ≤ Q)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  rcases horig with hfast | hslow
  · obtain ⟨CV, hfast⟩ := hfast
    have hS := healthy_base_of_reset_catch hp hc
    have hr := hS.run.localRun
    have hf := faulty_lt_half hp x
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    have hgs : SA.gbar g ≤ sp.ts s := by
      have := (clean_source_timing hp hs).1
      have := lt_cutZ sp g
      linarith
    have evidence : B ∈ (tr.state x r).fg.tree ∧
        ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = s ∧
          SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rcases hfast with ⟨ellX, C, ⟨hcall, -⟩, -, -, hD, -⟩ |
          ⟨ellX, A, hpt, hslot, hsel, -⟩
      · have hΦU := (SA.frameIn_of_callAt hr hx hcall).2
        refine ⟨frame_tree_subset hp hx hcall (SA.deepest_mem hD).1.1.1, ?_⟩
        have htest := (SA.deepest_mem hD).1.2
        unfold SA.FastTest SA.confirmationScore at htest
        dsimp only at htest
        have hlt := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hf htest)
        obtain ⟨z, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hBR⟩, hz⟩ :=
          Set.exists_mem_notMem_of_ncard_lt_ncard hlt
        obtain ⟨q, _, e', hv, rfl⟩ := hS.run.honest.pool_vote x hx r s _ hvp (not_not.mp hz)
        exact ⟨_, not_not.mp hz, q, e', hv, SA.state_pool_slot sp hr hx r s _ hvp,
          R, hΦU hR, hRr, hBR.mono hΦU⟩
      · have hΦU := (SA.frameIn_of_callAt hr hx hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        refine ⟨frame_tree_subset hp hx hpt.1 (SA.deepest_mem hsel).1.1, ?_⟩
        have h34 := (SA.deepest_mem hsel).1.2.1
        obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
          Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
            (t := SA.optimisticVoters sp A ellX.frame (sp.slot (tr.projAC.time r)) B) (by omega)
        obtain ⟨hvs, q, _, e', he, rfl⟩ :=
          SA.optimisticPoint_pool_vote hS.run hx hpt hv (not_not.mp hz)
        exact ⟨_, not_not.mp hz, q, e', he, hvs.trans hslot,
          R, hΦU hR, hRr, hBR.mono hΦU⟩
    obtain ⟨hBx, z, hz, q, e', hv, hvs, hVB⟩ := evidence
    refine held_target_vote_domain_before hp hx hy hBx hcast ?_ ?_ ?_
    · intro hF
      exact raw_writer_voterBlockTree_window_before hr (reset_raw_sync_window_before hp Q)
        (catch_window_of_reset_catch hp hc Q) hx hy (Or.inr hfast) .refl hcast (by omega) hiQ
        (by
          have hm := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
          linarith) hF
    · obtain ⟨v, r₀, m, S, hS, hm⟩ := reset_seed hp
      have hms : m < s := by rw [cleanLabel_eq] at hs; omega
      exact ⟨v, r₀, m, S, hS, by omega,
        target_compatible_older_origin hp hS hz hv hvs hms hVB⟩
    · intro v r₀ m O hri ho
      rcases lt_trichotomy m s with hm | rfl | hm
      · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
      · obtain ⟨CV', hst⟩ := ho.2.2.1
        obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
        rcases SA.fastLock_fastLock_compatible hS hx hfast ho.1 hfl hgs with h | h
        · exact SA.anc_total hr.coherent h hOD
        · exact Or.inr (hOD.trans h)
      · exact target_compatible_later_origin_before hp ho hri hm hprior
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hts, hwindow⟩ := clean_source_timing hp hs
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith
  have hgs : SA.gbar g ≤ sp.ts s := by linarith
  obtain ⟨ellX, C, hupd, hconf, -, hdeep, -⟩ := id hslow
  have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hupd.1).2
  have hres : SA.ResultAt tr.projAC x r s C
      (SA.fastCounted sp (tr.projAC.state x r) ellX.frame s C) := ⟨ellX, hupd, hconf, rfl⟩
  have hslot : sp.slot (sp.ts s + sp.Δ) = s := SA.slot_of_mem sp s (by linarith)
    (by simp only [SA.SAParams.ts]; push_cast; linarith)
  have hprev : SA.gbar g ≤ sp.ts ((s : Int) - 1) := by
    have he : sp.ts ((s : Int) - 1) = sp.ts s - 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; ring
    rw [he]; linarith
  have hparts := Compose.honest_participants_window_before hp.run hp.noColl
    (SA.serviceWindowBefore_of_sync (reset_raw_sync_window_before hp Q)) hgs hx hupd hrQ
    (fun z hz => ⟨hp.healthy.2.1 z hz _ (by change SA.gbar g ≤ sp.ts s + sp.Δ; linarith),
      (Compose.joined_projection sp ro dg H tr proposer hp.run z hz _).1.mpr
        (hS.joinedAt hz (by rw [hslot]; exact hprev))⟩)
    (by have := hp.healthy.2.2; have := Fin.pos x
        have hn : sp.n = sp.toParams.n := rfl
        omega)
  obtain ⟨z, hz, q, _, e', hv, _, hvs, hVB⟩ :=
    SA.result_honest_supporter_of_participants sp hS.run hx hres hBC hparts.le
  have hjoined : SA.JoinedAt tr.projAC x (tr.time r) := by
    have ht : tr.time r = sp.ts s + 6 * sp.Δ := hupd.2.2.1
    have hsr : sp.slot (tr.time r) = s + 1 := by
      rw [ht]
      apply SA.slot_of_mem sp (s + 1) <;>
        simp only [SA.SAParams.ts] <;> push_cast <;> linarith
    exact hS.joinedAt hx (by rw [hsr]; convert hgs using 1; congr 1; omega)
  refine slow_target_vote_domain_of_support_before hp hc Q hx hy hslow hjoined
    ((SA.ts_le_iff sp).mpr (by rw [cleanLabel_eq] at hs; omega)) hrQ
    hcast hsi hiQ ?_ ?_ ⟨z, hz, q, e', hv, hvs, hVB⟩ ?_ hprior
  · intro hF
    exact raw_writer_voterBlockTree_window_before hr (reset_raw_sync_window_before hp Q)
      (catch_window_of_reset_catch hp hc Q) hx hy (Or.inl hres) hBC hcast (by omega) hiQ
      (by
        have hm := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
        linarith) hF
  · obtain ⟨v, q, m, S, hS, hm⟩ := reset_seed hp
    exact ⟨v, q, m, S, hS, by rw [cleanLabel_eq] at hs; omega⟩
  · intro v q O _ ho
    obtain ⟨CV, hst⟩ := ho.2.2.1
    obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hCD : Compatible (tr.HonestBlocks H) C D := by
      rcases hfl with ⟨ellD, R, huD, hR, _, hfast, _⟩ | hop
      · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
          (SA.frameIn_of_callAt hr ho.1 huD.1).2
        have hRR := SA.result_result_compatible hS hx hres ho.1 ⟨ellD, huD, hR, rfl⟩ hgs4
        rcases hRR with h | h
        · exact SA.anc_total hr.coherent h hDR
        · exact Or.inr (hDR.trans h)
      · exact SA.result_optimistic_compatible hS hx hres ho.1 hop hgs4
    rcases hCD with h | h
    · exact SA.anc_total hr.coherent (hBC.trans h) hOD
    · exact SA.anc_total hr.coherent hBC (hOD.trans h)

/-- Prospective clean-source support: strong induction is on the receiving cut, never
on the source gate. Current domain, transfer and service use only strictly earlier support. -/
theorem clean_source_votes_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrQ : tr.time r ≤ Q) :
    ∀ i, tr.time i ≤ Q → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch hp hcatch
  have hr := hS.run.localRun
  have hsync := reset_raw_sync_window_before hp Q
  have hcatch' := catch_window_of_reset_catch hp hcatch Q
  obtain ⟨hts, hwindow⟩ := clean_source_timing hp hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiQ y hy ell e hcast hsi
    have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rintro z hz q hqi e' ⟨ell', hc'⟩ hse
      exact ih q hqi ((hp.run.time_mono hqi.le).trans hiQ) z hz ell' e' hc' hse
    obtain ⟨hroot, hkeep⟩ := clean_source_vote_domain_step hp hcatch Q hx hy horig hs hrQ
      hcast hsi hiQ hprior
    have hvi := vote_viable_of_root hp.run hp.noColl hy hcast hroot hkeep
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    by_cases hBF : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hv := hvi.resolve_right hBF
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    have htsRead : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr
        (by rw [(SA.castAt_spec hr hy hcast).2.1])
    have hfault : SA.FaultBound tr.projAC H (tr.time i) := hS.faultBound (hr.time_nonneg i)
      (hgs.trans ((SA.ts_le_iff sp).mpr (by
        have hslot : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hcast).2.1
        omega)))
    have sync : ∀ m, s ≤ m → SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)
        H (tr.HonestBlocks H) (sp.ts m) (tr.time i) tr.projAC := by
      intro m hm
      exact Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
        tr proposer ΔF (sp.ts m) (tr.time i) hp.run.toLocalRun
        (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by omega)))))
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : ∀ CV, (∀ v ∈ CV, v.slot = s ∧
          (∃ k, tr.projAC.SendOrAdmit x k v ∧ sp.ts s ≤ tr.projAC.time k ∧
            tr.projAC.time k < sp.ts s + 2 * sp.Δ) ∧
          ∃ Hv ∈ tr.HonestBlocks H, Hv.root = v.head ∧ Anc (tr.HonestBlocks H) B Hv ∧
            (Hv.root = sp.genesisRoot ∨ ∃ k, tr.projAC.AcceptAt x k Hv ∧
              tr.projAC.time k < sp.ts s + 2 * sp.Δ)) →
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        intro CV hW
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgs hcatch' (by linarith [sp.toParams.hΔ]) hx hy hcast hfirst hiQ
        intro v hv
        obtain ⟨hvs, hw, H, hH, hHr, hBH, ha⟩ := hW v hv
        exact ⟨hvs, hw, H, hH, hHr, hFB.trans hBH, ha⟩
      have earlier : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B :=
        fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)
      have viab : SA.ViableAtVote ell e (s + 1) B := by rw [← hfirst]; exact Or.inl hv
      rcases horig with ⟨CV, hfast⟩ | hslow
      · exact SA.first_transfer_stored sp hS.run hx hfast .refl hy hcast hfirst
          (sync s le_rfl) (carry CV (fastLock_writer hr hx hfast)) hfault viab earlier
      · obtain ⟨ellX, C, hupd, hconf, -, hdeep, -⟩ := id hslow
        have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono
          (SA.frameIn_of_callAt hr hx hupd.1).2
        have hres : SA.ResultAt tr.projAC x r s C
            (SA.fastCounted sp (tr.projAC.state x r) ellX.frame s C) :=
          ⟨ellX, hupd, hconf, rfl⟩
        refine SA.result_prefix_vote_extends_of_stored hS.run (faulty_lt_half hp x)
          hx hy hres hBC hcast hfirst (carry _ ?_) viab
          (SA.slow_stored_locks hS hx hslow hwindow hy (by
            rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst])) earlier
          (SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hsync)
            hx hgs hupd hrQ hy hcast hfirst)
        intro v hv
        obtain ⟨hvs, hw, H, hH, hHr, hCH, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, H, hH, hHr, hBC.trans hCH, ha⟩
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hsm : s < m := by omega
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hslot⟩
        have hqi : q < i := by
          by_contra hn
          have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (SA.castAt_spec hr hz hc').2.1
          have := (SA.castAt_spec hr hy hcast).2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgm hcatch' (by linarith [sp.toParams.hΔ]) hz hy hcast hm hiQ
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt
          linarith [sp.toParams.hΔ]
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by rcases hslot with h | h <;> omega))
        (half_committee hp (hts.trans ((SA.ts_le_iff sp).mpr (by omega))))
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault (sync m hsm.le) ?_
      rw [← hm]
      exact Or.inl hv

/-- A raw result prefix has a prospective frozen vote domain. Only support at strictly
earlier receiving cuts is assumed; the result writer need not precede the cast. -/
theorem result_prefix_vote_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hiQ : tr.time i ≤ Q)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := (clean_source_timing hp hs).2
    exact this.trans ((SA.ts_le_iff sp).mpr (by have := sp.two_le_k; omega))
  obtain ⟨ellX, hupd, hconf, -⟩ := id hres
  have hCx := frame_tree_subset hp hx hupd.1 (SA.deepest_mem hconf).1.1
  have hBx := mem_tree_of_anc hp hx hBC hCx
  obtain ⟨z, hz, q, e', hv, hvs, D, hD, hDr, hCD⟩ :=
    SA.result_extended hS hgs4 hx hupd.1
      (by rw [hupd.2.2.1]; linarith) hconf
  have hVB : SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    ⟨D, hD, hDr, hBC.trans hCD⟩
  refine held_target_vote_domain_before hp hx hy hBx hcast ?_ ?_ ?_
  · intro hF
    exact raw_writer_voterBlockTree_window_before hr (reset_raw_sync_window_before hp Q)
      (catch_window_of_reset_catch hp hc Q) hx hy (Or.inl hres) hBC hcast (by omega) hiQ
      (by
        have := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
        linarith) hF
  · obtain ⟨v, r₀, m, S, hseed, hm⟩ := reset_seed hp
    have hms : m < s := by rw [cleanLabel_eq] at hs; omega
    exact ⟨v, r₀, m, S, hseed, by omega,
      target_compatible_older_origin hp hseed hz hv hvs hms hVB⟩
  · intro v r₀ m O hri ho
    rcases lt_trichotomy m s with hm | rfl | hm
    · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hcomp : Compatible (tr.HonestBlocks H) C D := by
        rcases hfl with ⟨ellD, R, huD, hR, _, hfast, _⟩ | hop
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            (SA.frameIn_of_callAt hr ho.1 huD.1).2
          rcases SA.result_result_compatible hS hx hres ho.1 ⟨ellD, huD, hR, rfl⟩ hgs4
            with h | h
          · exact SA.anc_total hr.coherent h hDR
          · exact Or.inr (hDR.trans h)
        · exact SA.result_optimistic_compatible hS hx hres ho.1 hop hgs4
      rcases hcomp with h | h
      · exact SA.anc_total hr.coherent (hBC.trans h) hOD
      · exact SA.anc_total hr.coherent hBC (hOD.trans h)
    · exact target_compatible_later_origin_before hp ho hri hm hprior

/-- At the first slot after a late raw result, every still-live older stored lock is
compatible with each prefix of that result. The late bound drains pre-clean sources. -/
theorem result_prefix_stored_locks
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := (clean_source_timing hp (show cleanLabel sp a + sp.k + 2 ≤ s by
      have := sp.two_le_k; omega)).2
    exact ht.trans ((SA.ts_le_iff sp).mpr (by have := sp.two_le_k; omega))
  have down : ∀ {L D}, Anc (tr.HonestBlocks H) L D →
      Compatible (tr.HonestBlocks H) C D → Compatible (tr.HonestBlocks H) L B := by
    intro L D hLD hCD
    rcases hCD with h | h
    · exact SA.anc_total hr.coherent hLD (hBC.trans h)
    · exact SA.anc_total hr.coherent (hLD.trans h) hBC
  intro l hl hlive hle Y hY hYr
  rcases hle.lt_or_eq with hls | hls
  · have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by omega
    have compare : ∀ {q D},
        ((∃ CV, SA.FastLockAt tr.projAC y q l.slot D CV) ∨
          SA.SlowLockAt tr.projAC y q l.slot D) → Compatible (tr.HonestBlocks H) C D := by
      intro q D hsource
      obtain ⟨ell, hu, hC, -⟩ := hres
      obtain ⟨z, hz, j, e, hv, hes, Hd, hHd, he, hCH⟩ :=
        SA.result_extended hS hgs4 hx hu.1 (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
      obtain ⟨ell', hcast⟩ := hv
      obtain ⟨Hd', hHd', he', hDH⟩ := clean_source_votes_before hp hc
        (max (tr.time q) (tr.time j)) hy hsource hclean (le_max_left _ _)
        j (le_max_right _ _) z hz ell' e hcast (by omega)
      obtain rfl : Hd' = Hd := hr.coherent.1 hHd' hHd (he'.trans he.symm)
      exact SA.anc_total hr.coherent hCH hDH
    cases hf : l.fast
    · obtain ⟨q, -, D, hsl, L, hL, hLr, hLD⟩ := SA.slow_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare (Or.inr hsl))
    · obtain ⟨q, -, D, CV', hfl, L, hL, hLr, hLD⟩ := SA.fast_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare (Or.inl ⟨CV', hfl⟩))
  · obtain ⟨L, hL, hLr, D, hLD, q, -, CV', hD⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
    rw [hls] at hD
    apply down hLD
    rcases hD with hD | hD
    · exact SA.result_result_compatible hS hx hres hy hD hgs4
    · exact SA.result_optimistic_compatible hS hx hres hy hD hgs4

/-- Every honest cast after a late raw result extends each prefix of that result.
The induction is over receiving cuts for all later labels, not over the writer cut. -/
theorem late_result_prefix_votes_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrQ : tr.time r ≤ Q) :
    ∀ i, tr.time i ≤ Q → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hsync := reset_raw_sync_window_before hp Q
  have hcatch := catch_window_of_reset_catch hp hc Q
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
  have hts := (clean_source_timing hp hclean).1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiQ y hy ell e hcast hsi
    have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rintro z hz q hqi e' ⟨ell', hc'⟩ hse
      exact ih q hqi ((hp.run.time_mono hqi.le).trans hiQ) z hz ell' e' hc' hse
    obtain ⟨hroot, hkeep⟩ := result_prefix_vote_domain_before hp hc Q hx hy hres hBC hclean
      hcast hsi hiQ hprior
    have hvi := vote_viable_of_root hp.run hp.noColl hy hcast hroot hkeep
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    by_cases hBF : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hv := hvi.resolve_right hBF
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    have hfault : SA.FaultBound tr.projAC H (tr.time i) := hS.faultBound (hr.time_nonneg i)
      (hgs.trans ((SA.ts_le_iff sp).mpr (by
        have hslot : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hcast).2.1
        omega)))
    have sync : ∀ m, s ≤ m → SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)
        H (tr.HonestBlocks H) (sp.ts m) (tr.time i) tr.projAC := by
      intro m hm
      exact Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
        tr proposer ΔF (sp.ts m) (tr.time i) hp.run.toLocalRun
        (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by omega)))))
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgs hcatch (by linarith) hx hy hcast hfirst hiQ
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hCD, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans (hBC.trans hCD), ha⟩
      refine SA.result_prefix_vote_extends_of_stored hS.run (faulty_lt_half hp x)
        hx hy hres hBC hcast hfirst carry ?_
        (result_prefix_stored_locks hp hc hx hy hres hBC hs (by
          change s + 1 ≤ sp.slot (tr.projAC.time i)
          rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst]))
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)) ?_
      · rw [← hfirst]; exact Or.inl hv
      · obtain ⟨ellX, hupd, -⟩ := hres
        exact SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hsync)
          hx hgs hupd hrQ hy hcast hfirst
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hsm : s < m := by omega
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hslot⟩
        have hqi : q < i := by
          by_contra hn
          have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (SA.castAt_spec hr hz hc').2.1
          have := (SA.castAt_spec hr hy hcast).2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgm hcatch (by linarith) hz hy hcast hm hiQ
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt
          linarith
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by rcases hslot with h | h <;> omega))
        (half_committee hp (hts.trans ((SA.ts_le_iff sp).mpr (by omega))))
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault (sync m hsm.le) ?_
      rw [← hm]
      exact Or.inl hv

/-- Late raw-result prefixes are extended by every later honest cast, without a
source-cut ordering, high-origin, no-veto, or slow-lock premise. -/
theorem late_result_prefix_votes
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) :
    ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  intro y hy i ell e hcast hsi
  exact late_result_prefix_votes_before hp hc (max (tr.time r) (tr.time i)) hx hres hBC hs
    (le_max_left _ _) i (le_max_right _ _) y hy ell e hcast hsi

/-- Compare using an already-cast honest vote within `Q`, rather than manufacturing a
future vote. Whole-run reset premises remain in the transfer dependencies. -/
theorem clean_source_compatible_high_origin_of_vote_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrQ : tr.time r ≤ Q)
    {v : Fin sp.n} {q m : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v q m O)
    {z : Fin sp.n} (hz : z ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC z j ell e)
    (hjQ : tr.time j ≤ Q) (hsl : s < e.msg.slot) (hml : m < e.msg.slot) :
    Compatible (tr.HonestBlocks H) B O := by
  have hB := clean_source_votes_before hp hc Q hx hsource hs hrQ j hjQ z hz ell e hv hsl
  exact target_compatible_older_origin hp ho hz ⟨ell, hv⟩ rfl hml hB

/-- A clean raw source and any high origin share a later honest vote head. This uses
the already proved clean-source transfer, rather than assuming support at a source gate. -/
theorem clean_source_compatible_high_origin
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {v : Fin sp.n} {q m : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v q m O) : Compatible (tr.HonestBlocks H) B O := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  let n := max s m + 1
  have htime : SA.gbar g + 4 * sp.Δ ≤ sp.ts n := by
    have ht := (clean_source_timing hp hs).2
    exact ht.trans ((SA.ts_le_iff sp).mpr (by dsimp [n]; omega))
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hS htime x hx
  obtain ⟨ell, hcast⟩ := hv
  have hB := clean_source_votes_before hp hc (max (tr.time r) (tr.time j)) hx hsource hs
    (le_max_left _ _) j (le_max_right _ _) x hx ell e hcast (by dsimp [n] at hes; omega)
  exact target_compatible_older_origin hp ho hx ⟨ell, hcast⟩ hes
    (by dsimp [n]; omega) hB

/-- A raw writer's target is frame-held at a later slot start once finalization is below it.
Old acceptances use Catch; fresh acceptances use Sync and the healthy restart bound. -/
theorem raw_writer_held_at_slot_start
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [SA.SAParams.ts] at ht ⊢
    nlinarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hr hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : SA.gbar g ≤ tr.time q
      · have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.time q) < sp.ts s + 3 * sp.Δ := by
          intro k hk
          have hd := deadline_le_restarts
            (T := tr.projAC) (c := k) (fun k' _ hr' => hS.restart_le hpH hr') (tr.time q)
          have ht : max (tr.time q) (SA.gbar g) < sp.ts s + 2 * sp.Δ := by
            apply max_lt hqt
            linarith
          change _ ≤ max (tr.time q) (SA.gbar g) + sp.Δ at hd
          linarith
        obtain ⟨k, hki, hak, _⟩ := (hS.syncAC le_rfl (tr.time q)).2 x hx q D hq hg le_rfl
          p hpH i ell hci (by
            have := hdl i le_rfl
            change tr.projAC.deadline p i (tr.time q) ≤ tr.time i
            linarith) hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := hS.catchUp x hx q D hq (not_le.mp hg) p hpH i ell hci
          (by change _ ≤ tr.time i; linarith) hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

/-- Guarded receipt of an actual acceptance: old sources use Catch, newer ones use Sync.
The receiver's finalization bound is required; archival heldness alone is not frame membership. -/
theorem reset_accept_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  by_cases hnew : SA.gbar g ≤ tr.time q
  · have hd := deadline_le_restarts
      (T := tr.projAC) (c := j) (fun k _ hk => hS.restart_le hy hk) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      change _ ≤ max (tr.time q) (SA.gbar g) + sp.Δ at hd
      rw [max_eq_left hnew] at hd
      exact hd.trans hq
    obtain ⟨k, hkj, hak, _⟩ := (hS.syncAC le_rfl (tr.time q)).2 x hx q B ha hnew le_rfl
      y hy j ell hcall hdl hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF
  · obtain ⟨k, hkj, hak, _⟩ := hS.catchUp x hx q B ha (not_le.mp hnew)
      y hy j ell hcall hg hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF

/-- A frame-held block reaches a later frame only under that receiver's finalization guard. -/
theorem reset_frame_relay
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  rcases Compose.frame_anc_accepted hr hx q ellx hcx B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · exact reset_accept_frame hp hc hx hy ha hcy hg
      (by have := hp.run.time_mono hk; change tr.time k ≤ tr.time q at this; linarith) hF

/-- A held target above a high seed is either a candidate at the actual call or
covered by a strictly earlier high origin. No frozen-tree transport is required. -/
theorem held_target_candidate_or_high_origin_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y i ell)
    {P S : SA.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r b B, r < i → HighOrigin tr H g x r b B →
      Compatible (tr.HonestBlocks H) P B) :
    ell.frame.AncestorCandidate P ∨
      ∃ x r b B, r < i ∧ HighOrigin tr H g x r b B ∧ Anc (tr.HonestBlocks H) P B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  have hPy := frame_tree_subset hp hy hcall hPt
  have hSy := mem_tree_of_anc hp hy hSP hPy
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact low_root_of_held_seed_at_call hp hy hPy hy hseed hcall hSy hlow
        (Or.inr hSP) (fun _ => hPt)
    · exact high_J_root_of_held_at_call_before hp hy hPy hy hcall (by omega) hcompare
  by_cases hPF : Anc (tr.HonestBlocks H) P ell.frame.fcRoot
  · exact Or.inl (Or.inl (SA.anc_tree_of_anc_U hU hPhi hPhiU hPt hPF hPhi.fcRoot_mem))
  have hFP := hroot.resolve_right hPF
  have hFPf := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hFP hPt
  by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
  · have hPv : P ∈ ell.frame.viableHeads := by
      have hfr := Compose.frame_of_projAC hp.run hy hcall
      have hPt' := hPt
      rw [hfr] at hPt' hFPf ⊢
      exact ⟨hPy, hPt'.2, hFPf.mono (fun X hX => hX.1), hfloor⟩
    exact Or.inl (Or.inr ⟨hPt, hFPf, P, hPt, hPv, .refl⟩)
  obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := highOrigin_mem hp hseed
  have hSh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
    rw [σ_eq_run hp hseed.1 hy hSs hSy]
    omega
  obtain ⟨x, r, b, B, E, hri, ho, -, hE, hEB, -, hEf⟩ :=
    high_floor_source_of_row_bound hp hseed hy (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
        obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
        have ht : sp.ts l ≤ tr.time i :=
          (ts_le_of_fastLock hp hfl).trans (hp.run.time_mono (by omega))
        have hlabel : (l : Int) ≤ sp.slot (tr.time i) :=
          (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).mp ht
        omega)
      (fun x r b B _ ho x' r' b' B' _ ho' => hret.comparable x r b B x' r' b' B' ho ho')
      (fun x r b B _ ho => hret.comparable v q m S x r b B hseed ho) hSf
  refine Or.inr ⟨x, r, b, B, hri, ho, ?_⟩
  rcases hcompare x r b B hri ho with h | h
  · exact h
  · have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy (hEB.trans h) hPy)
    omega

/-- A floor above a held target above a high seed has an actual earlier honest report
extending the target with strictly greater height at the reporter's cut. -/
theorem held_target_high_floor_report_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {P S : SA.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ (tr.state y i).fg.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r b B, r < i → HighOrigin tr H g x r b B →
      Compatible (tr.HonestBlocks H) P B)
    (hfloor : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor) :
    ∃ x ∈ H, ∃ r ell C, r < i ∧ SA.ToFGAt tr.projAC x r ell C ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hU := honest_coherent hp
  have hSy := mem_tree_of_anc hp hy hSP hPy
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := highOrigin_mem hp hseed
  have hSh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
    rw [σ_eq_run hp hseed.1 hy hSs hSy]
    omega
  obtain ⟨x, r, b, B, E, hri, ho, -, hE, hEB, -, hEf, d, att, hrd, hdi, hsign, haT⟩ :=
    high_floor_signed_source_of_row_bound hp hseed hy (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
        obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
        have ht : sp.ts l ≤ tr.time i :=
          (ts_le_of_fastLock hp hfl).trans (hp.run.time_mono (by omega))
        have hlabel : (l : Int) ≤ sp.slot (tr.time i) :=
          (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).mp ht
        omega)
      (fun x r b B _ ho x' r' b' B' _ ho' => hret.comparable x r b B x' r' b' B' ho ho')
      (fun x r b B _ ho => hret.comparable v q m S x r b B hseed ho) hSf
  have hPE : Anc (tr.HonestBlocks H) P E := by
    have hcomp : Compatible (tr.HonestBlocks H) P E := by
      rcases hcompare x r b B hri ho with h | h
      · exact SA.anc_total hU h hEB
      · exact Or.inr (hEB.trans h)
    rcases hcomp with h | h
    · exact h
    · have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy h hPy)
      omega
  obtain ⟨j, hdj, -, ell, C, E', hreport, hC, hE', hEr, hEC, -, -, hEh, -⟩ :=
    signAt_report_entry hp.run ho.1 hsign
  obtain rfl : E' = E := hU.1 ⟨x, ho.1, j, hE'⟩ ⟨y, hy, i, hE⟩ (hEr.trans haT)
  have hPC := hPE.trans (hEC.mono (fun X hX => ⟨x, ho.1, j, hX⟩))
  have hPx := mem_tree_of_anc hp ho.1 hPC hC
  refine ⟨x, ho.1, j, ell, C, by omega, hreport, hPC, ?_⟩
  rw [← hEh, σ_eq_run hp ho.1 hy hPx hPy, σ_eq_run hp ho.1 hy hE' hE]
  omega

/-- A late raw-result prefix and any high origin share a later honest vote head. -/
theorem late_result_prefix_compatible_high_origin
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s)
    {v : Fin sp.n} {q m : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v q m O) : Compatible (tr.HonestBlocks H) B O := by
  have hS := healthy_base_of_reset_catch hp hc
  let n := max s m + 1
  have htime : SA.gbar g + 4 * sp.Δ ≤ sp.ts n := by
    have ht := (clean_source_timing hp (show cleanLabel sp a + sp.k + 2 ≤ s by
      have := sp.two_le_k; omega)).2
    exact ht.trans ((SA.ts_le_iff sp).mpr (by dsimp [n]; omega))
  obtain ⟨j, e, ⟨ell, hcast⟩, hes⟩ := SA.honest_votes_in_slot hS htime x hx
  have hB := late_result_prefix_votes hp hc hx hres hBC hs x hx j ell e hcast
    (by dsimp [n] at hes; omega)
  exact target_compatible_older_origin hp ho hx ⟨ell, hcast⟩ hes
    (by dsimp [n]; omega) hB

/-- A unanimous late vote head extends a high reset seed. -/
theorem high_seed_below_unanimous
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    (hun : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s → e.msg.head = P.root) :
    ∃ v q m S, HighOrigin tr H g v q m S ∧ Anc (tr.HonestBlocks H) S P := by
  have hS := healthy_base_of_reset_catch hp hc
  obtain ⟨v, q, m, S, ho, hm⟩ := reset_seed hp
  have hms : m < s := by rw [cleanLabel_eq] at hs; omega
  have htime : SA.gbar g + 4 * sp.Δ ≤ sp.ts s :=
    (clean_source_timing hp hs).2.trans ((SA.ts_le_iff sp).mpr (by have := sp.two_le_k; omega))
  obtain ⟨i, e, ⟨ell, hcast⟩, hes⟩ := SA.honest_votes_in_slot hS htime x hx
  obtain ⟨⟨D, hD, hDr, hSD⟩, -⟩ := (height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset).votes v q m S ho x hx i ell e hcast (by omega)
  obtain rfl : D = P := hS.run.localRun.coherent.1 hD hP
    (hDr.trans (hun x hx i e ⟨ell, hcast⟩ hes))
  exact ⟨v, q, m, S, ho, hSD⟩

/-- A late unanimous result is a candidate at its own update or has a covering high origin. -/
theorem unanimous_result_candidate_or_high_origin
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hu : SA.UpdateAt tr.projAC x i s ell)
    (hconf : SA.getConfirmation sp (tr.projAC.state x i) ell.frame s = some P)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = s → e.msg.head = P.root) :
    ell.frame.AncestorCandidate P ∨
      ∃ v q m S, q < i ∧ HighOrigin tr H g v q m S ∧ Anc (tr.HonestBlocks H) P S := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  have hPt : P ∈ ell.frame.tree := (SA.deepest_mem hconf).1.1
  have hPU := (SA.frameIn_of_callAt hr hx hu.1).2 hPt
  have hres : SA.ResultAt tr.projAC x i s P
      (SA.fastCounted sp (tr.projAC.state x i) ell.frame s P) := ⟨ell, hu, hconf, rfl⟩
  obtain ⟨v, q, m, S, ho, hSP⟩ := high_seed_below_unanimous hp hc hx hPU
    (by have := sp.two_le_k; omega) hun
  exact held_target_candidate_or_high_origin_before hp hx hu.1 hPt ho hSP
    (fun v q m S _ ho => late_result_prefix_compatible_high_origin hp hc hx hres .refl hs ho)

end Consensus.Goldilocks.Healing

end
