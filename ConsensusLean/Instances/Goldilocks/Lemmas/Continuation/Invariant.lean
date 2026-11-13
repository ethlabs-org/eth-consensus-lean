module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Frontier
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.SeedHeld
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The seeded invariant after a hand-over

The fields of `SleepyInvariantUpTo` relative to the healed family at the floors `(rL, rO)`, for
the states read at times `t ∈ [t₁, b]`:

* `origins_compatible`, `vote_extends`: the healed frontier at every label (`healed_frontier_at`);
* `record`: the record at a read point is `Σ.F` or below an origin of label `≥ rO` written before
  the read (`HealedRecordCoverAt`);
* `caches`: `Σ.F` is on the healed chain (ancestor form), and `fc_root` is compatible with every
  member held in the frame;
* `locks`: every live lock block is on the healed chain, below its holder's own lock write, whose
  label is `≥ rL` after the drain (`lock_write_at`, `drain_live_locks`);
* `sources`: every FG source from `t₁` on is on the healed chain, below the lock write of the live
  fast lock it is the viable ancestor of;
* `viable`: S3 at full reads for every block on the healed chain;
* `seedHeld`: the reset seed is in the frame of every honest call from `t_{rL−k−3}` through `b`
  whose `Σ.F` it extends.

`caches` and `viable` are read at states whose node has called from `t_{rL−k−3}` on before the
read: a stale state from before the reset need not hold the reset seed, and its pre-reset `Σ.J`
is then not compared with the family. A reader honest at a read point from `t_{r+k}` on, or at a
vote cut after the split slot, has such a call (`seeded_reader_called_at`).
`seeded_chain_candidate_at` reads `viable` as a viable-ancestor candidate.

`seeded_invariant_at` assembles them from the seed, the reset service and the counts through
`b ≥ T`, and conviction below a third, with `t₁ ≥ t_{r+k}` the later of the seed's cover start and
the drain `t_{r+k}`. Every field is proved: the record cover after `T` (`Continuation/Record`), the
held seed after `T` (`Continuation/SeedHeld`), and the cache facts and the full-read viability
(`Continuation/Rows`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The seeded invariant through `b`**: the `SleepyInvariantUpTo` fields relative to the healed
family at the floors `rL`, `rO`, for the states read at times `t ∈ [t₁, b]`. -/
structure SeededInvariant (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g : Time)
    (rL rO : Nat) (t₁ b : Time) : Prop where
  /-- S1: any two members of the healed family within `b` are compatible. -/
  origins_compatible : ∀ C s C' s', HealedOrigin tr H g rL rO C s b →
    HealedOrigin tr H g rL rO C' s' b → Compatible (tr.HonestBlocksAt H) C C'
  /-- S2: every honest vote at a time `≤ b` of a slot after a member's label extends it. -/
  vote_extends : ∀ C s, HealedOrigin tr H g rL rO C s b → ∀ y i e, HVoteAt tr H y i e →
    tr.time i ≤ b → s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg C
  /-- The record of a reader honest at a read point `t ∈ [t₁, b]` is its `Σ.F` or below an origin
  of label `≥ rO` written before the read. -/
  record : ∀ y i t, t₁ ≤ t → t ≤ b → y ∈ H t → Regimes.ReadPoint tr i t →
    HealedRecordCoverAt tr H rO y i t
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (tr.state y i).fg.F)
  /-- `Σ.F` is on the healed chain, and `fc_root` is compatible with every member held in the
  frame (state read at `t ∈ [t₁, b]`, of a node that has called from `t_{rL−k−3}` on before the
  read). -/
  caches : ∀ y i t, t₁ ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    (∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c) →
    OnHealedChain tr H g rL rO (tr.state y i).fg.F b ∧
      ∀ C s, HealedOrigin tr H g rL rO C s b → C ∈ (Node.frame (tr.state y i)).tree →
        Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot C
  /-- Every live lock block is on the healed chain (state read at `t ∈ [t₁, b]`). -/
  locks : ∀ y i t, t₁ ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    ∀ L ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t,
      OnHealedChain tr H g rL rO L b
  /-- Every FG source of a node honest at its cut, at a time in `[t₁, b]`, is on the healed
  chain. -/
  sources : ∀ y i ℓ C, y ∈ H (tr.time i) → t₁ ≤ tr.time i → tr.time i ≤ b →
    SA.ToFGAt tr.projAC y i ℓ C → OnHealedChain tr H g rL rO C b
  /-- S3 (full reads): a block on the healed chain held in the frame (state read at
  `t ∈ [t₁, b]`, of a node that has called from `t_{rL−k−3}` on before the read) is at or below
  `fc_root` or in the full viable tree. -/
  viable : ∀ y i t, t₁ ≤ t → (∀ k < i, tr.time k ≤ t) → t ≤ b → y ∈ H t →
    (∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c) →
    ∀ C, OnHealedChain tr H g rL rO C b → C ∈ (Node.frame (tr.state y i)).tree →
      (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
        C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree
  /-- The reset seed: a high origin written by `b`, in the frame of every honest call at a time in
  `[t_{rL−k−3}, b]` whose `Σ.F` it extends. -/
  seedHeld : ∃ x i j B, Healing.Growing.HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧
    ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) →
      tr.projAC.CallAt y c ell → sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c → tr.time c ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree

/-- **A block on the healed chain held in the frame is a viable-ancestor candidate**: at or below
`fc_root`, or in the full viable tree (`SeededInvariant.viable`), for a reader honest at
`t ∈ [t₁, b]` that has called from `t_{rL−k−3}` on before the read. -/
theorem seeded_chain_candidate_at {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {g : Time} {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y : Fin sp.n} {i : Nat} {t : Time}
    (ht₁ : t₁ ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : OnHealedChain tr H g rL rO C b)
    (hCm : C ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).AncestorCandidate C :=
  hinv.viable y i t ht₁ hi htb hy hcall C hC hCm

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-! ### Locks and sources: through the holder's lock write, after the drain -/

/-- The drain of the seed's reset is at `t_{r+k}`. -/
private theorem HandoverSeed.drainTime_eq {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) :
    ∃ a, Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T ∧
      r = Healing.cleanLabel sp a + sp.k + 2 ∧ Healing.drainTime sp a = sp.ts (r + sp.k : Nat) := by
  obtain ⟨a, hp, hr⟩ := hseed.reset
  refine ⟨a, hp, hr, ?_⟩
  rw [Healing.drainTime_eq, hr, Healing.cleanLabel_eq]
  congr 2
  omega

/-- **Live locks from the drain on are on the healed chain**: a live lock block of a node honest
at `t ≥ t_{r+k}` is the viable ancestor of a stored lock block, which is below its holder's own
lock write of the lock's slot (`lock_write_at`); after the drain that slot is `≥ r`
(`drain_live_locks`), so the write is a member. -/
theorem seeded_locks_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time}
    {y : Fin sp.n} {i : Nat} {t : Time} (hdt : sp.ts (r + sp.k : Nat) ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b) (hy : y ∈ H t) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t,
      OnHealedChain tr H g r (r + sp.k - 1) L b := by
  obtain ⟨a, -, hr, hdrain⟩ := hseed.drainTime_eq
  have ht0 : 0 ≤ t := (ts_natCast_nonneg _).trans hdt
  have hst := Trace.upTo_state tr y (d := t) hi
  have hU := honestBlocksAt_coherent hrun hnc
  have hwf : SA.LocksWF sp (tr.state y i).ac.locks := by
    have h := Compose.locksWF_state (hrun.upTo ht0) (hnc.upTo _) hy i
    rwa [hst] at h
  have hreach := Compose.fg_reachable (hrun.upTo ht0).toLocalRun hy i
  rw [hst] at hreach
  have hΦ : FrameOK (Node.frame (tr.state y i)) := (Store.frame_realization _ _ _ _ hreach).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, i, t, ht0, hi, hy, hX.1⟩
  rintro L ⟨hL, l, hlm, hlL⟩
  have hlab : r ≤ l.slot := by
    rw [hr]
    exact Healing.drain_live_locks (a := a) hwf (hdrain ▸ hdt) l hlm
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hlm
  obtain rfl : L = (Node.frame (tr.state y i)).viableAncestor B₀ :=
    hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB₀).1 hlL.symm
  obtain ⟨L₀, hL₀, hL₀r, D, hD, hL₀D⟩ := lock_write_at hrun hnc ht0 hi hy l₀ hl₀
  obtain rfl : B₀ = L₀ := hU.1 (hΦU hB₀) ⟨y, i, t, ht0, hi, hy, hL₀⟩ (hB₀r.trans hL₀r.symm)
  exact onHealedChain_iff.2 ⟨D, l₀.slot, .of_lock hlab (hD.mono htb),
    ((SA.anc_viableAncestor _ B₀).mono hΦU).trans hL₀D⟩

/-- **FG sources from the drain on are on the healed chain**: a source is the viable ancestor of
the block of a live fast lock, below its holder's lock write of a label `≥ r`. -/
theorem seeded_sources_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time}
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hdt : sp.ts (r + sp.k : Nat) ≤ tr.time i)
    (hib : tr.time i ≤ b) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.ToFGAt tr.projAC y i ℓ C) :
    OnHealedChain tr H g r (r + sp.k - 1) C b := by
  obtain ⟨a, -, hr, hdrain⟩ := hseed.drainTime_eq
  have hd := hrun.time_nonneg i
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hpc
  rw [projAC_state_at hrun hy] at hC
  have hwf : SA.LocksWF sp (tr.state y i).ac.locks := by
    have h := Compose.locksWF_state (hrun.upTo hd) (hnc.upTo _) hy i
    rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  obtain ⟨hCv, l, hlm, hlC, -, -⟩ := Compose.toFG_candidate hC
  have hlab : r ≤ l.slot := by
    rw [hr]
    exact Healing.drain_live_locks (a := a) hwf (hdrain ▸ hdt) l hlm
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hlm
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : C = ℓ.frame.viableAncestor B := hΦ.coherent.1 hCv.1 hvt hlC.symm
  obtain ⟨L, hL, hLr, D, hD, hLD⟩ :=
    lock_write_at hrun hnc hd (fun _ hk => hrun.time_mono hk.le) hy l₀ hl₀
  obtain rfl : B = L := hU.1 (hΦU hB) (mem_honestBlocksAt hrun hy hL) (hBr.trans hLr.symm)
  exact onHealedChain_iff.2 ⟨D, l₀.slot, .of_lock hlab (hD.mono hib), (hva.mono hΦU).trans hLD⟩

/-! ### Open frame facts -/

/-- **The record cover from `t₁` through `b`**. From the seed's cover through `T`, the record of a
reader honest at a read point `t ∈ [t₁, b]` is its `Σ.F` or below an origin of label `≥ r + k − 1`
written before the read: after `T` a kept root keeps its block or follows `Σ.F`, and a new root
is the reader's own result or selection, of label `≥ σ` (`seeded_record_cover_at`). -/
theorem seeded_record_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hTb : T ≤ b) (hsvc : Healing.Growing.ResetService tr H g ΔF b)
    (hB : SleepyBoundsFrom tr H r b) (hcv : ChainConvictedBelow tr H)
    (hdt : sp.ts (r + sp.k : Nat) ≤ t₁)
    (hcov : ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F)) :
    ∀ y n t, t₁ ≤ t → t ≤ b → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F) := by
  exact seeded_record_cover_at hrun hnc hseed hTb hsvc hB hcv hdt hcov

/-- Any two members of the healed family within `b ≥ T` are compatible (`healed_frontier_at`). -/
private theorem seeded_members_compatible (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) (hstock : sp.committeeSize = sp.n) :
    ∀ C s C' s', HealedOrigin tr H g r (r + sp.k - 1) C s b →
      HealedOrigin tr H g r (r + sp.k - 1) C' s' b → Compatible (tr.HonestBlocksAt H) C C' :=
  fun C s C' s' h h' => healedOriginsBelow_iff.1
    (healed_frontier_at hrun hnc hseed hTb hsvc hB hcv hstock (max s s' + 1)).1 C s C' s'
      (by omega) (by omega) h h'

/-- **The seeded cache facts.** For a reader honest at `t ∈ [t₁, b]` that has called from
`t_{r−k−3}` on before its read, `Σ.F` is on the healed chain, and `fc_root` is compatible with
every family member held in the frame (`seeded_caches_of`: a low reader holds the reset seed, with
`Σ.F` and `fc_root` below it; a high `Σ.J` is the entry of an honest source below a member). -/
theorem seeded_caches_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hTb : T ≤ b) (hsvc : Healing.Growing.ResetService tr H g ΔF b)
    (hB : SleepyBoundsFrom tr H r b) (hcv : ChainConvictedBelow tr H)
    (hdt : sp.ts (r + sp.k : Nat) ≤ t₁) {y : Fin sp.n} {i : Nat} {t : Time} (ht₁ : t₁ ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c) (hstock : sp.committeeSize = sp.n) :
    OnHealedChain tr H g r (r + sp.k - 1) (tr.state y i).fg.F b ∧
      ∀ C s, HealedOrigin tr H g r (r + sp.k - 1) C s b →
        C ∈ (Node.frame (tr.state y i)).tree →
        Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot C :=
  have ht0 : 0 ≤ t := (ts_natCast_nonneg _).trans (hdt.trans ht₁)
  seeded_caches_of hrun hnc hcv hseed hTb
    (seeded_members_compatible hrun hnc hseed hTb hsvc hB hcv hstock) ht0 hi htb hy
    (hB.two t ht0 htb) hcall

/-- **S3 at full reads for the healed chain.** A block on the healed chain held in the frame of a
reader honest at `t ∈ [t₁, b]` that has called from `t_{r−k−3}` on before its read is at or below
`fc_root` or in the full viable tree (`seeded_viable_of`: above `fc_root`, the block is viable, or
below the crossing of the floor, a high row, or below the low reader's held seed). -/
theorem seeded_viable_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hTb : T ≤ b) (hsvc : Healing.Growing.ResetService tr H g ΔF b)
    (hB : SleepyBoundsFrom tr H r b) (hcv : ChainConvictedBelow tr H)
    (hdt : sp.ts (r + sp.k : Nat) ≤ t₁) {y : Fin sp.n} {i : Nat} {t : Time} (ht₁ : t₁ ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c) (hstock : sp.committeeSize = sp.n) :
    ∀ C, OnHealedChain tr H g r (r + sp.k - 1) C b → C ∈ (Node.frame (tr.state y i)).tree →
      (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
        C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  have ht0 : 0 ≤ t := (ts_natCast_nonneg _).trans (hdt.trans ht₁)
  fun _ hC hCt => seeded_viable_of hrun hnc hcv hseed hTb
    (seeded_members_compatible hrun hnc hseed hTb hsvc hB hcv hstock) ht0 hi htb hy
    (hB.two t ht0 htb) hcall hC hCt

/-- **The held seed past `T`**. The seed's high origin `S` is in the frame of every honest call at
a time in `[t_{r−k−3}, b]` whose `Σ.F` it extends: after `T`, through the caller's tick at
`t_{r−k−3}` and the growth of its FG tree (`seed_held_through_at`). -/
theorem seed_held_past_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time}
    (hTb : T ≤ b) :
    ∃ x i j B, Healing.Growing.HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧
      ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) →
        tr.projAC.CallAt y c ell → sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c → tr.time c ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree := by
  exact seed_held_through_at hrun hnc hseed hTb

/-! ### The seeded invariant -/

/-- **The seeded invariant through `b` from a cover start `t_c`**: from the hand-over seed, the
reset service and the slot counts from `r` through `b ≥ T`, conviction below a third, and the record
cover through `T` from `t_c` on, the seeded invariant at the floors `(r, r + k − 1)` holds from
`t₁ = max t_c t_{r+k}`. The frontier is `healed_frontier_at`; locks and sources go through the
holder's lock write (`seeded_locks_at`, `seeded_sources_at`). -/
theorem seeded_invariant_of_cover_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) {tc : Time}
    (hcov : ∀ y n t, tc ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F)) (hstock : sp.committeeSize = sp.n) :
    SeededInvariant tr H g r (r + sp.k - 1) (max tc (sp.ts (r + sp.k : Nat))) b := by
  have hdt : sp.ts (r + sp.k : Nat) ≤ max tc (sp.ts (r + sp.k : Nat)) := le_max_right _ _
  have hF := healed_frontier_at hrun hnc hseed hTb hsvc hB hcv hstock
  exact ⟨seeded_members_compatible hrun hnc hseed hTb hsvc hB hcv hstock,
    fun C s hC y i e he hib hs =>
      healedVotesBelow_iff.1 (hF e.msg.slot).2 C s hC y i e he hib hs le_rfl,
    seeded_record_at hrun hnc hseed hTb hsvc hB hcv hdt
      (fun y n t ht htT hy hrp => hcov y n t ((le_max_left _ _).trans ht) htT hy hrp),
    fun y i t ht₁ hi htb hy hcall =>
      seeded_caches_at hrun hnc hseed hTb hsvc hB hcv hdt ht₁ hi htb hy hcall hstock,
    fun y i t ht₁ hi htb hy => seeded_locks_at hrun hnc hseed (hdt.trans ht₁) hi htb hy,
    fun y i ℓ C hy hi hib h => seeded_sources_at hrun hnc hseed hy (hdt.trans hi) hib h,
    fun y i t ht₁ hi htb hy hcall =>
      seeded_viable_at hrun hnc hseed hTb hsvc hB hcv hdt ht₁ hi htb hy hcall hstock,
    seed_held_past_at hrun hnc hseed hTb⟩

/-- **The seeded invariant through `b`**: from the hand-over seed, the reset service and the slot
counts from `r` through `b ≥ T`, and conviction below a third, the seeded invariant at the floors
`(r, r + k − 1)` holds from a time `t₁ ∈ [t_{r+k}, T]`: the later of the seed's cover start and
the drain `t_{r+k}` (`seeded_invariant_of_cover_at`). -/
theorem seeded_invariant_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) (hstock : sp.committeeSize = sp.n) :
    ∃ t₁, t₁ ≤ T ∧ sp.ts (r + sp.k : Nat) ≤ t₁ ∧ SeededInvariant tr H g r (r + sp.k - 1) t₁ b := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨hσT, hrσ, -⟩ := hseed.timing
  obtain ⟨tc, htcT, hcov⟩ := hseed.covered
  have hDT : sp.ts (r + sp.k : Nat) ≤ T := by
    have := ts_le_ts (sp := sp) (show r + sp.k ≤ σ + 1 by omega)
    have hts : sp.ts ((σ + 1 : Nat) : Int) = sp.ts σ + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  exact ⟨_, max_le htcT hDT, le_max_right _ _,
    seeded_invariant_of_cover_at hrun hnc hseed hTb hsvc hB hcv hcov hstock⟩

end Consensus.Goldilocks.Compose.Growing

end
