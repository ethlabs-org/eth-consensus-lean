module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.TopFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # The honest rows of a reader after a hand-over

After a hand-over the trees of honest readers still hold FG rows signed before the reset, whose
sources sit on branches that the healed family does not compare. The rows that matter are the
**high** ones, naming an entry of height `≥ H_z + 1`. Each has an honest source below a member of
the healed family written by its own signer before the signing: before `T` the reset cluster puts
the named entry on the chain of a high origin of the signer (`high_row_source_at`); after `T`,
past the drain, the source is the viable ancestor of a live fast lock, below the signer's own lock
write of a label `≥ r`. The **low** reader (`h_j ≤ H_z`) is handled through the reset seed `S`:
its `Σ.F` is below `S` (G1.2 at strict height under `ChainConvictedBelow`); once `S` is held,
`fc_root` is below `S` too (`Σ.J` is an entry of height `H_z` in the active case, and no contest
puts it below the held block `S` of height `h_max = H_z + 1`). A reader holds `S` once it has
called from `t_{r−k−3}` on: the healthy prefix keeps every reader honest after it awake on
`[ḡ, T]`, so its tick at `t_{r−k−3}` is such a call, and the seed's holding at calls carries `S`
into every later state.

* `sleepyServiceFrom_of_reset`: the reset service with the catch-up is the sleepy service from `ḡ`.
* `seeded_reader_called_at`: a reader honest at `t ≥ t_{r+k}`, read at or before cut `i` with
  `t ≤ time i`, has an AC call before `i` at or after `t_{r−k−3}`.
* `seeded_rows_above_at`: the high rows of a reader read after `c_z` are sourced below members
  (`RowsAbove` at `H_z + 1` on the prefix through the read).
* `seeded_reader_on_chain_at`: `Σ.F` and `fc_root` of a reader with such a call are on the healed
  chain.
* `seeded_caches_of`, `seeded_viable_of`: the cache facts and the full-read viability of the seeded
  invariant, for a reader with such a call.
* `seeded_vote_frame_of`: the frozen witness at a vote after the split slot. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

variable {sp : ACParams}
variable {hold : Time}

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}

/-! ### The service after GST -/

/-- **The catch-up at the node**: a block accepted before `ḡ` by a node honest then is accepted,
before `ḡ + κ`, by a node honest at a call from `ḡ + κ` on whose `Σ.F` it extends. -/
private theorem catch_old_at (hrun : Growing.GoldilocksRun proposer dg H tr ini) {κ : Time}
    (hc : Healing.Growing.CatchRun tr H g κ) {x : Fin sp.n} {i : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hx : x ∈ H (tr.time i)) (hB : tr.AcceptAt x i B)
    (hi : tr.time i < AC.gbar g) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    (hj : AC.gbar g + κ ≤ tr.time j) (hF : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ := by
  exact hrun.toLocalRun.fgCatchAt hc hx hB hi hy hj hF

/-- **The reset service with the catch-up is the sleepy service from `ḡ`**: sends and acceptances
from `ḡ ≥ g` are served with the deadline from their own time (`ACResetService.ac_service_at`,
`ACResetService.relay`); a block accepted before `ḡ` is caught up before `ḡ + κ` (`CatchRun`), at
the node and, through the AC block call that follows each acceptance, at its AC projection. -/
theorem sleepyServiceFrom_of_reset (hrun : Growing.GoldilocksRun proposer dg H tr ini) {κ b : Time}
    (hsvc : Healing.Growing.ACResetService tr H g ΔF) (hc : Healing.Growing.CatchRun tr H g κ)
    (hκ : 0 ≤ κ) : SleepyServiceFrom tr H ΔF (AC.gbar g) κ b := by
  have hac := hsvc.ac_service_at hrun (lo := AC.gbar g) (hi := b) (AC.le_gbar g)
  refine ⟨hsvc.deltaF, hκ, hac.message, hac.relay, ?_, ?_, ?_⟩
  · intro x i B hx hB hai y j hy hj _ hdl hF
    have he : max (tr.time i) g = tr.time i := max_eq_left ((AC.le_gbar g).trans hai)
    have h := hsvc.relay x i B hx hB ((AC.le_gbar g).trans hai) y j hy hj (by rw [he]; exact hdl)
      hF
    rwa [he] at h
  · intro x i B hx hB hi y j hy _ hj hF
    exact catch_old_at hrun hc hx hB hi hy hj hF
  · intro x i B hx hB hi y j ℓ hy hcj hj hF
    obtain ⟨k, _, hk, hkt⟩ := hrun.toLocalRun.acCatchAt hc hx hB hi hy hcj hj hF
    exact ⟨k, lt_of_not_ge (fun h => (not_le_of_gt hkt) (hj.trans (hrun.time_mono h))), hk, hkt⟩

/-! ### Timing -/

/-- `t_{s+j} = t_s + 4jΔ`. -/
private theorem ts_add (s j : Nat) : sp.ts (s + j : Nat) = sp.ts s + 4 * sp.Δ * j := by
  simp only [ACParams.ts]; push_cast; ring

/-- A fast lock of label `l` is written at a time in `[t_l, t_l + 6Δ]`. -/
private theorem fastLockAt_time (hrun : Growing.GoldilocksRun proposer dg H tr ini) {x : Fin sp.n}
    {i l : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (h : AC.FastLockAt tr.projAC x i l C CV) :
    sp.ts l ≤ tr.time i ∧ tr.time i ≤ sp.ts l + 6 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  rcases h with ⟨ℓ, C', hu, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht : tr.time i = sp.ts l + 6 * sp.Δ := hu.2.2.1
    exact ⟨by linarith, ht.le⟩
  · change sp.slot (tr.time i) = l at hsl
    have h1 := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) (l : Int)).2 (by omega)
    have h2 : tr.time i < sp.ts (l + 1 : Nat) := lt_of_not_ge fun hge => by
      have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hge
      push_cast at this
      omega
    rw [ts_add] at h2
    push_cast at h2
    exact ⟨h1, by linarith⟩

/-- An honest vote of slot `m` is cast in `[t_m, t_{m+1})`. -/
private theorem vote_time (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H y i e) :
    sp.ts e.msg.slot ≤ tr.time i ∧ tr.time i < sp.ts (e.msg.slot + 1 : Nat) := by
  obtain ⟨hy, ℓ, hc⟩ := hVoteAt_iff.1 hv
  have h := (castAt_spec_at hrun hnc hy hc).2.1
  refine ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [h]), lt_of_not_ge ?_⟩
  intro hge
  have := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hge
  push_cast at this
  omega

/-- The seed's reset, with its lock floor, the seed's call time `t_{r−k−3} = t_{slot a + 2}`
after GST and before `T`, and the drain `t_{r+k}` before `T`. -/
private theorem HandoverCore.reset_timing {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) :
    ∃ a hold, Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold ∧
      r = Healing.cleanLabel sp a + sp.k + 2 ∧ r - sp.k - 3 = sp.slot a + 2 ∧
      a + sp.Δ < sp.ts (r - sp.k - 3 : Nat) ∧ AC.gbar g < a ∧
      sp.ts (r - sp.k - 3 : Nat) < sp.ts (r + sp.k : Nat) ∧ sp.ts (r + sp.k : Nat) ≤ T ∧
      Healing.drainTime sp a = sp.ts (r + sp.k : Nat) := by
  obtain ⟨a, _, hp, hr⟩ := hseed.reset
  obtain ⟨hσT, hrσ, -⟩ := hseed.timing
  have hΔ := sp.toParams.hΔ
  have hca := hp.cutZ_lt_reset_at
  have hgz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [AC.gbar_nonneg g]
  have hsa : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hq : r - sp.k - 3 = sp.slot a + 2 := by rw [hr, Healing.cleanLabel_eq]; omega
  have hk := sp.two_le_k
  refine ⟨a, _, hp, hr, hq, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [hq]
    have : sp.ts ((sp.slot a + 2 : Nat) : Int) = sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    rw [this]
    linarith
  · exact (AC.ts_lt_iff sp).mpr (by push_cast; omega)
  · have h1 := ts_le_ts (sp := sp) (show r + sp.k ≤ σ + 1 by omega)
    have h2 : sp.ts ((σ + 1 : Nat) : Int) = sp.ts σ + 4 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    linarith
  · rw [Healing.drainTime_eq, hr, Healing.cleanLabel_eq]
    congr 2
    omega

/-! ### The reader's call from the seed's call time -/

/-- **A node honest at `t_{r−k−3}` has an AC call at exactly that time**: it is awake there
(the healthy prefix through `T`), so it ticks, and a tick's first cut is `ac_on_tick`. -/
private theorem seed_time_call (hrun : Growing.GoldilocksRun proposer dg H tr ini) {T : Time}
    {r σ : Nat} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {y : Fin sp.n}
    (hy : y ∈ H (sp.ts (r - sp.k - 3 : Nat))) :
    ∃ c, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      tr.time c = sp.ts (r - sp.k - 3 : Nat) := by
  obtain ⟨a, _, hp, -, -, hqa, hga, hqd, hdT, -⟩ := hseed.reset_timing
  have hΔ := sp.toParams.hΔ
  set q := sp.ts (r - sp.k - 3 : Nat) with hq
  have hq0 : 0 ≤ q := ts_natCast_nonneg _
  have hpub : sp.toParams.IsPublic q :=
    ⟨4 * ((r - sp.k - 3 : Nat) : Int), by rw [hq]; simp only [ACParams.ts]; ring⟩
  have hawake := hp.awake y q hy (by linarith) (by linarith)
  obtain ⟨j₀, xt, fgDue, hj₀⟩ := hrun.tick_of_awake y q hy hq0 hpub hawake
  obtain ⟨ℓt, pc, uc, hlt, hcs, -, -⟩ :=
    @tick_order sp.toParams (goldilocksNode sp) proposer dg y (tr.state y j₀) q xt fgDue
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j₀) q (.tick xt fgDue)).2.length := by
    change 0 < (Node.onTick proposer dg y (tr.state y j₀) q xt fgDue).2.length
    rw [hcs]; simp
  obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hj₀.2.1 0 hlen
  have hct : tr.CallAt y j₀ (.ac ℓt) := by
    refine ⟨hn₀, ?_⟩
    simp only [Nat.add_zero] at hl₀
    rw [hl₀]
    change some (Node.onTick proposer dg y (tr.state y j₀) q xt fgDue).2[0] = _
    simp [hcs]
  simp only [Nat.add_zero] at ht₀
  exact ⟨j₀, ℓt, Compose.projAC_callAt.mpr hct, ht₀⟩

/-- **A reader honest at a time `t ≥ t_{r+k}`, read at or before cut `i` with `t ≤ time i`, has an
AC call before `i` from `t_{r−k−3}` on.** The healthy prefix keeps the reader, honest at `t` and
so at every earlier time, awake on `[ḡ, T]`; its tick at `t_{r−k−3} < t_{r+k} ≤ t` is a call, at a
cut before `i`. This covers a read point at `t ≥ t₁` and a vote cut of a slot after the split
slot. -/
theorem seeded_reader_called_at (hrun : Growing.GoldilocksRun proposer dg H tr ini) {T : Time}
    {r σ : Nat} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {y : Fin sp.n}
      {i : Nat}
    {t : Time} (hy : y ∈ H t) (ht : sp.ts (r + sp.k : Nat) ≤ t) (hti : t ≤ tr.time i) :
    ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c := by
  obtain ⟨-, _, -, -, -, -, -, hqd, -, -⟩ := hseed.reset_timing
  obtain ⟨c, ell, hc, hct⟩ := seed_time_call hrun hseed (hrun.antitone (hqd.le.trans ht) hy)
  refine ⟨c, ?_, ell, hc, hct.ge⟩
  by_contra h
  have := hrun.time_mono (not_lt.mp h)
  linarith

/-! ### The low reader and the reset seed -/

/-- The block of a high origin is in its writer's tree at the write. -/
theorem HighOrigin.mem_tree (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {q l : Nat} {S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hS : Healing.Growing.HighOrigin tr H g x q l S) : S ∈ (tr.state x q).fg.tree := by
  have hx := hrun.antitone (le_max_right _ _) hS.1
  obtain ⟨CV, ell, D, hcall, hfl, rfl⟩ := hS.2.2.1
  obtain ⟨ell', hcall', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hcall'.2)
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hx hcall
  have h := (AC.viableAncestor_anc hΦ hD).1
  have hfr := frame_of_projAC_at hrun hx hcall
  rw [hfr] at h ⊢
  exact h.1

/-- **A low `Σ.F` is below every high origin** (G1.2 at strict height under
`ChainConvictedBelow`): `Σ.F` is finalized at a height `≤ h_j ≤ H_z`, below the high origin's
height. -/
private theorem low_finalized_below (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hcv : ChainConvictedBelowUpTo tr H b) {y : Fin sp.n}
    {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (htb : t ≤ b)
    (hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g) {x : Fin sp.n} {q l : Nat}
    {S : AC.Blk sp.n (List (FG.Att sp.n))} (hS : Healing.Growing.HighOrigin tr H g x q l S)
    (hqb : tr.time q ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S := by
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  have hU := honestBlocksAt_coherent hrun hnc
  have hx := hrun.antitone (le_max_right _ _) hS.1
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H := fun X hX => ⟨y, i, t, ht0, hi, hy, hX⟩
  have hcoh : Coherent (tr.state y i).fg.tree := hU.mono hsub
  have hg := Healing.Store.genesis_mem hreach
  have hSt := HighOrigin.mem_tree hrun hnc hS
  have hgS : Anc (tr.HonestBlocksAt H)
      (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload) S :=
    ((Goldilocks.Store.accepted_tree _ _ _ _
      (Healing.Growing.fg_reachable_at hrun (hrun.time_nonneg q) (fun _ h => hrun.time_mono h.le)
        hx)).2.2.2 S hSt).mono
        (fun X hX => ⟨x, q, tr.time q, hrun.time_nonneg q, fun _ h => hrun.time_mono h.le, hx,
          hX⟩)
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hgF : (tr.state y i).fg.Anc (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload)
      (tr.state y i).fg.F := (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 _ hFm
  have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S := fun he => by
    rw [hcoh.1 hFm hg he]
    exact hgS
  rcases Healing.Store.fin_pair_entry hreach hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgen (hBfF.symm.trans he)
  obtain rfl : W = (tr.state y i).fg.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := Healing.Store.J_entry_of_reachable hreach hBj
  obtain rfl : E = (tr.state y i).fg.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := Healing.h_le_of_store_anc hreach hFJ
  have hSh := hS.2.2.2
  exact Growing.GoldilocksRun.finalized_anc_of_lt_conv_upTo hrun hnc hcv ht0 hi hy htb
    (hrun.time_nonneg q) (fun _ h => hrun.time_mono h.le) hx hqb hBf hFm hBfF.symm hSt (by omega)

/-- **A low reader with a call from `t_{r−k−3}` on holds the reset seed `S`**, a high origin of a
label `< r` written by `T`, with `Σ.F ⪯ S`: at the call at `t_{r−k−3}` before the read, `Σ.F` is
below `S` (finality only grows, and the current `Σ.F` is below `S`), so the seed's holding at
calls puts `S` in the frame there; the tree only grows. -/
theorem low_seed_held_upTo (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
    (hcv : ChainConvictedBelowUpTo tr H b) (hTb : T ≤ b) {y : Fin sp.n}
      {i : Nat} {t : Time}
    (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    (hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g) :
    ∃ x q l S, Healing.Growing.HighOrigin tr H g x q l S ∧ tr.time q ≤ T ∧ l < r ∧
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S ∧ S ∈ (tr.state y i).fg.tree ∧
      ∃ c < i, tr.time c = sp.ts (r - sp.k - 3 : Nat) ∧ S ∈ (tr.state y c).fg.tree := by
  obtain ⟨a, _, hp, hr, hq, hqa, hga, hqd, hdT, -⟩ := hseed.reset_timing
  have hΔ := sp.toParams.hΔ
  obtain ⟨x, q, l, S, hS, hqa', hqT, hheld⟩ := hp.reset_seed_held_at_call_at
  have hlr : l < r := by
    obtain ⟨CV, -, D, -, hfl, -⟩ := hS.2.2.1
    have h1 := (fastLockAt_time hrun hfl).1
    have h2 : a < sp.ts r := by
      have := ts_le_ts (sp := sp) (show r - sp.k - 3 ≤ r by omega)
      linarith
    by_contra hge
    have := ts_le_ts (sp := sp) (show r ≤ l by omega)
    linarith
  have hFS := low_finalized_below hrun hnc hcv ht0 hi hy htb hlow hS (hqT.trans hTb)
  -- the call at `t_{r−k−3}` before the read
  obtain ⟨c₀, hc₀i, ell₀, hc₀, hc₀t⟩ := hcall
  obtain ⟨c, hci, ell, hc, hct⟩ : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp),
      tr.projAC.CallAt y c ell ∧ tr.time c = sp.ts (r - sp.k - 3 : Nat) := by
    rcases hc₀t.eq_or_lt with h | h
    · exact ⟨c₀, hc₀i, ell₀, hc₀, h.symm⟩
    · obtain ⟨c, ell, hc, hct⟩ := seed_time_call hrun hseed
        (hrun.antitone (h.le.trans (hi c₀ hc₀i)) hy)
      refine ⟨c, ?_, ell, hc, hct⟩
      by_contra hge
      have := hrun.time_mono (show c₀ ≤ c by omega)
      linarith
  have hct' : tr.time c ≤ t := hi c hci
  have hyc : y ∈ H (tr.time c) := hrun.antitone hct' hy
  have hfr := frame_of_projAC_at hrun hyc hc
  have hFc : Anc (tr.HonestBlocksAt H) ell.frame.F S := by
    rw [hfr]
    exact (F_mono_at hrun ht0 hy hi hci.le).trans hFS
  have hSc := hheld y c ell hyc hc (by rw [hct]; linarith) (by rw [hct]; linarith) hFc
  rw [hfr] at hSc
  exact ⟨x, q, l, S, hS, hqT, hlr, hFS, tree_mono_at hrun ht0 hy hi hci.le hSc.1, c, hci, hct,
    hSc.1⟩

/-- `low_seed_held_upTo` under conviction below a third at every time. -/
theorem low_seed_held (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hcv : ChainConvictedBelow tr H) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {y : Fin sp.n}
      {i : Nat} {t : Time}
    (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    (hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g) :
    ∃ x q l S, Healing.Growing.HighOrigin tr H g x q l S ∧ tr.time q ≤ T ∧ l < r ∧
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S ∧ S ∈ (tr.state y i).fg.tree ∧
      ∃ c < i, tr.time c = sp.ts (r - sp.k - 3 : Nat) ∧ S ∈ (tr.state y c).fg.tree :=
  low_seed_held_upTo hrun hnc hseed (hcv.upTo (max T t)) (le_max_left _ _) ht0 hi hy
    (le_max_right _ _) hcall hlow

/-- **A low reader's `fc_root` is below a held high block `S` above its `Σ.F`**: if `fc_root` is
`Σ.J`, then `h_max = h_j + 1 ≤ H_z + 1 ≤ h(S) ≤ h_max`, so `S` has the top height and, with no
contest, extends `Σ.J`. -/
theorem low_fcRoot_below (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g) {x : Fin sp.n} {q l : Nat}
    {S : AC.Blk sp.n (List (FG.Att sp.n))} (hS : Healing.Growing.HighOrigin tr H g x q l S)
    (hSy : S ∈ (tr.state y i).fg.tree) (hFS : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot S := by
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧ ¬ (tr.state y i).fg.Contest
  · rw [Goldilocks.Store.fcRoot_of_not_contest _ hk.1 hk.2]
    have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
      rw [Healing.Growing.σ_eq_honest_at hrun hnc ht0 hi hy (hrun.time_nonneg q)
        (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hS.1) hSy
        (HighOrigin.mem_tree hrun hnc hS)]
      exact hS.2.2.2
    obtain ⟨-, -, -, -, hZm, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
    have hSm := hZm S hSy
    by_contra hJS
    refine hk.2 ⟨hk.1, S, hSy, held_anc_at hrun hnc ht0 hy hi hFS hSy, by omega,
      fun h => hJS (Healing.Growing.honest_anc_of_store_anc_at ht0 hi hy h)⟩
  · rw [Goldilocks.Store.fcRoot]
    simp only [hk, ↓reduceIte]
    exact hFS

/-! ### The high rows -/

/-- **After the drain, a signing's source is below the signer's own lock write of a label `≥ r`.**
The source is at or below the viable ancestor of the block of a live lock, fast or slow
(`AC.toFG_source_below_lock`: a fast-lock candidate is itself such a block, and a deep candidate
is below the deep anchor, one of them); the stored lock sits below the signer's lock write of its
slot at an earlier cut (`AC.fast_lock_provenance`, `AC.slow_lock_provenance`), and after
`t_{r+k}` a live lock has slot `≥ r` (`drain_live_locks`). -/
private theorem signed_source_lock (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {v : Fin sp.n}
      {k : Nat}
    {a : FG.Att sp.n} (hv : v ∈ H (tr.time k)) (hs : tr.SignAt v k a)
    (hk : sp.ts (r + sp.k : Nat) ≤ tr.time k) :
    ∃ D, D ∈ (tr.state v k).fg.tree ∧ ((tr.state v k).fg.σ D.root).Th = a.T ∧
      ∃ c < k, ∃ l C, r ≤ l ∧
        ((∃ CV, AC.FastLockAt tr.projAC v c l C CV) ∨ AC.SlowLockAt tr.projAC v c l C) ∧
        Anc (tr.HonestBlocksAt H) D C := by
  obtain ⟨a₀, _, -, hr, -, -, -, -, -, hdrain⟩ := hseed.reset_timing
  obtain ⟨src, hcall⟩ := hs
  obtain ⟨j, rfl, ℓ, hcj, -, htj, hC, hfg⟩ := attest_source hrun hv hcall
  have hvj : v ∈ H (tr.time j) := htj ▸ hv
  have hd := hrun.time_nonneg j
  have hpc : tr.projAC.CallAt v j ℓ := Compose.projAC_callAt.mpr hcj
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hvj hpc
  have hfr := frame_of_projAC_at hrun hvj hpc
  rw [hfr] at hC hΦ hΦU
  have hC' : (AC.acToFG sp (tr.state v j).ac (Node.frame (tr.state v j)) (tr.time j)).2 =
      some src := hC
  obtain ⟨hsv, A, ⟨hAt, l, hlm, hlA⟩, hsA⟩ := AC.toFG_source_below_lock hC'
  have hwf : AC.LocksWF sp (tr.state v j).ac.locks := by
    have h := Compose.locksWF_state (hrun.upTo hd) (hnc.upTo _) hvj j
    rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  have hlab : r ≤ l.slot := by
    rw [hr]
    exact Healing.drain_live_locks (a := a₀) hwf (hdrain ▸ (htj ▸ hk)) l hlm
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hlm
  obtain ⟨hVt, hVB⟩ := AC.viableAncestor_anc hΦ hB
  obtain rfl : A = (Node.frame (tr.state v j)).viableAncestor B :=
    hΦ.coherent.1 hAt hVt hlA.symm
  -- the holder's lock write, fast or slow, on the prefix through `time j`
  have hst := Trace.upTo_state tr v (d := tr.time j) fun _ hk' => hrun.time_mono hk'.le
  have hrA := (acRun_upTo hrun hnc hd).localRun
  have hsA' : (tr.projAC.upTo (tr.time j)).state v j = (tr.state v j).ac := by
    rw [← RunTrace.upTo_projAC, projAC_state (hrun.upTo hd).toLocalRun hvj j, hst]
  have hl₀' : l₀ ∈ ((tr.projAC.upTo (tr.time j)).state v j).locks := by rw [hsA']; exact hl₀
  have hBU : B ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) :=
    ⟨v, hvj, j, by rw [hst]; exact hB.1⟩
  have hw : ∃ c < j, ∃ B', ((∃ CV, AC.FastLockAt tr.projAC v c l₀.slot B' CV) ∨
      AC.SlowLockAt tr.projAC v c l₀.slot B') ∧
      Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) B B' := by
    cases hf : l₀.fast
    · obtain ⟨c, hcj', B', hsl, L', hL', hL'r, hL'B'⟩ :=
        AC.slow_lock_provenance hrA hrun.vstart hvj j l₀ hl₀' hf
      obtain rfl : L' = B := hrA.coherent.1 hL' hBU (hL'r.trans hBr.symm)
      obtain ⟨ℓ', C', hu, hconf, hdeep⟩ := hsl
      obtain ⟨hid, hu⟩ := (ac_updateAt_upTo hrun.time_mono).mp hu
      have hst' := projAC_upTo_state hrun (y := v) hid
      exact ⟨c, hcj', B', Or.inr ⟨ℓ', C', hu, by rwa [hst'] at hconf,
        by simpa only [hst', Trace.upTo_time] using hdeep⟩, hL'B'⟩
    · obtain ⟨c, hcj', B', CV, hfl, L', hL', hL'r, hL'B'⟩ :=
        AC.fast_lock_provenance hrA hrun.vstart hvj j l₀ hl₀' hf
      obtain rfl : L' = B := hrA.coherent.1 hL' hBU (hL'r.trans hBr.symm)
      obtain ⟨-, hfl⟩ := (AC.upTo_fastLockAt hrun.time_mono).mp hfl
      exact ⟨c, hcj', B', Or.inl ⟨CV, hfl⟩, hL'B'⟩
  obtain ⟨c, hcj', B', hfl, hBB'⟩ := hw
  -- the signed target is the source's entry
  have hatt := (hrun.cutLaw v (j + 1) _ hcall hv).1
  have hT := Compose.createAtt_T hatt
  have hsk : src ∈ (tr.state v (j + 1)).fg.tree := by
    rw [hfg]; exact hsv.1.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ := Goldilocks.Store.entry_state_of_source _ _ _ _
    (Healing.Growing.fg_reachable_at hrun (hrun.time_nonneg (j + 1))
      (fun _ h => hrun.time_mono h.le) hv) _ hsk
  rw [← hEr, hET] at hT
  exact ⟨_, hsk, hT.symm, c, by omega, l₀.slot, B', hlab, hfl,
    (hsA.mono hΦU).trans ((hVB.mono hΦU).trans (hBB'.mono (upTo_subset hrun hd)))⟩

/-- **The source of a high honest row** of a reader `y` honest at `d ≥ c_z`, read before cut `i`:
the row names a held entry of height `≥ H_z + 1` and its signer is honest at `d`, hence at `c_z`.
It was signed at a cut `k` before `y` accepted its block at `m < i`, and its honest source `D`
(held by the signer at a cut `≤ k`) is below a member `C` of the healed family of label `l`,
written by the signer at a cut `c < k` and below the signer's origin `O` of label `l` at that
cut. Up to `T` this is the reset cluster's high row (`high_row_source_at`: the entry is on the
chain of the signer's high origin); after `T` it is the signer's lock write
(`signed_source_lock`). -/
private theorem high_row_member (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {d : Time} (hd : 0 ≤ d)
    (hzd : Healing.cutZ sp.toParams g ≤ d) {y : Fin sp.n}
    {i : Nat} (hi : ∀ k < i, tr.time k ≤ d) (hy : y ∈ H d)
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree) {a : FG.Att sp.n}
    (ha : a ∈ X.fgPayload) (hav : a.val ∈ H d) {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y i).fg.tree) (hEr : E.root = a.T)
    (hEh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ a.T).h) :
    ∃ m < i, tr.AcceptAt y m X ∧ ∃ k < m, tr.SignAt a.val k a ∧
      ∃ D, (∃ k' ≤ k, D ∈ (tr.state a.val k').fg.tree ∧
        ((tr.state a.val k').fg.σ D.root).Th = a.T) ∧
      ∃ c < k, ∃ C l O OV, HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) ∧
        (AC.ResultAt tr.projAC a.val c l O OV ∨ AC.OptimisticLockAt tr.projAC a.val c l O OV) ∧
        Anc (tr.HonestBlocksAt H) D C ∧ Anc (tr.HonestBlocksAt H) C O := by
  obtain ⟨a₀, _, hp, -, -, -, -, -, hdT, hdrain⟩ := hseed.reset_timing
  have hst := Trace.upTo_state tr y hi
  obtain ⟨m, hmi, hA, k, hkm, hS⟩ := Compose.honest_row_signed_before (hrun.upTo hd) (hnc.upTo _)
    hy (by rw [hst]; exact hX) ha hav
  obtain ⟨-, hA⟩ := (RunTrace.upTo_acceptAt tr).mp hA
  obtain ⟨hkd, hS⟩ := (RunTrace.upTo_signAt tr).mp hS
  have hv : a.val ∈ H (tr.time k) := hrun.antitone hkd hav
  have hk0 := hrun.time_nonneg k
  have hkle : ∀ q < k, tr.time q ≤ tr.time k := fun _ h => hrun.time_mono h.le
  -- the signed height is the reader's height of the named entry
  have hah : Healing.Growing.HZ tr H g + 1 ≤ a.h := by
    obtain ⟨E₀, hE₀, hE₀r, hE₀h⟩ : ∃ E₀ ∈ (tr.state a.val k).fg.tree, E₀.root = a.T ∧
        ((tr.state a.val k).fg.σ E₀.root).h = a.h := by
      have h := Healing.signAt_entry (hrun.upTo hk0) hv ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hS⟩)
      rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
    obtain rfl : E₀ = E := (honestBlocksAt_coherent hrun hnc).1
      ⟨a.val, k, tr.time k, hk0, hkle, hv, hE₀⟩ ⟨y, i, d, hd, hi, hy, hE⟩ (hE₀r.trans hEr.symm)
    rw [← hEr, Healing.Growing.σ_eq_honest_at hrun hnc hd hi hy hk0 hkle hv hE hE₀] at hEh
    omega
  -- inside `T` and the deep quarantine: the reset cluster's high row; otherwise the signing is
  -- after the drain (past `T`, or past the quarantine, which the cover ends after the drain)
  by_cases hpre : tr.time k ≤ T ∧
      ∀ D, sp.deepDepth = some D → tr.time k ≤ Healing.cutZ sp.toParams g + 4 * D * sp.Δ
  · obtain ⟨q, hqk, l, O', ho, E', hE', hE'O', hE'r, -, hE'T⟩ :=
      hp.high_row_source_at (hrun.antitone (max_le hzd hkd) hav) hS hah hpre.2
    have hx := hrun.antitone (le_max_right _ _) ho.1
    obtain ⟨CV, ℓw, D', hcw, hfl, rfl⟩ := ho.2.2.1
    obtain ⟨O, OV, hO, hD'O⟩ := lock_below_origin_at hrun hnc hx (Or.inl ⟨CV, hfl⟩)
    have hq0 := hrun.time_nonneg q
    refine ⟨m, hmi, hA, k, hkm, hS, E', ⟨q, hqk.le, hE', hE'T.trans hE'r⟩, q, hqk, _, l, O, OV,
      .of_high le_rfl ho, hO, hE'O'.mono fun _ h => ⟨a.val, q, tr.time q, hq0,
        fun _ h' => hrun.time_mono h'.le, hx, h⟩, ?_⟩
    exact (Anc.mono (frameIn_at hrun hnc hx hcw).2 (AC.anc_viableAncestor _ D')).trans hD'O
  · have hkdr : sp.ts (r + sp.k : Nat) ≤ tr.time k := by
      by_cases hkT : tr.time k ≤ T
      · have hq : ¬ ∀ D, sp.deepDepth = some D →
            tr.time k ≤ Healing.cutZ sp.toParams g + 4 * D * sp.Δ := fun h => hpre ⟨hkT, h⟩
        push Not at hq
        obtain ⟨D, hD, hlt⟩ := hq
        rcases hp.deepCover D hD with hbq | hc
        · exact absurd (hkT.trans hbq) (not_le.2 hlt)
        · have := hc.drain_le D hD
          rw [← hdrain]
          linarith [sp.toParams.hΔ]
      · exact hdT.trans (not_le.1 hkT).le
    obtain ⟨D, hD, hDT, c, hck, l, C, hrl, hfl, hDC⟩ :=
      signed_source_lock hrun hnc hseed hv hS hkdr
    have hvc := hrun.antitone (hrun.time_mono hck.le) hv
    obtain ⟨O, OV, hO, hCO⟩ := lock_below_origin_at hrun hnc hvc hfl
    exact ⟨m, hmi, hA, k, hkm, hS, D, ⟨k, le_rfl, hD, hDT⟩, c, hck, C, l, O, OV,
      .of_lock hrl (lockWithin_iff.2 ⟨a.val, c, hvc, le_rfl, hfl⟩), hO, hDC, hCO⟩

/-- **The high rows on the prefix through `d ≥ c_z`**, sourced below members satisfying `Q`: the
`RowsAbove` premise of the store geometry at height `H_z + 1`, for every property `Q` of the
members that the classification of each high row supplies. The signers, honest at `d`, are then
honest at `c_z`, which `H_z` bounds. -/
theorem rowsAbove_of (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {d : Time} (hd : 0 ≤ d)
    (hzd : Healing.cutZ sp.toParams g ≤ d) {y : Fin sp.n}
    {i : Nat} (hi : ∀ k < i, tr.time k ≤ d) (hy : y ∈ H d)
    {Q : AC.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hQ : ∀ m < i, ∀ X, tr.AcceptAt y m X → ∀ a ∈ X.fgPayload, a.val ∈ H d →
      ∀ k < m, tr.SignAt a.val k a → ∀ c < k, ∀ C l O OV,
        HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) →
        (AC.ResultAt tr.projAC a.val c l O OV ∨ AC.OptimisticLockAt tr.projAC a.val c l O OV) →
        Q C l) :
    Compose.RowsAbove (tr.upTo d) (H d)
      (fun D => ∃ C l, Q C l ∧ C ∈ (tr.upTo d).HonestBlocks (H d) ∧
        Anc ((tr.upTo d).HonestBlocks (H d)) D C) y i (Healing.Growing.HZ tr H g + 1) := by
  have hst := Trace.upTo_state tr y hi
  refine Compose.rowsAbove_iff.2 fun X hX a ha hav ⟨E, hE, hEr⟩ hh => ?_
  rw [hst] at hX hE hh
  obtain ⟨m, hmi, hA, k, hkm, hS, D, ⟨k', hk'k, hD, hDT⟩, c, hck, C, l, O, OV, hC, hO, hDC, hCO⟩ :=
    high_row_member hrun hnc hseed hd hzd hi hy hX ha hav hE hEr hh
  have hmd : tr.time m ≤ d := hi m hmi
  have hcd : tr.time c ≤ d := (hrun.time_mono (by omega : c ≤ m)).trans hmd
  have hk'le : ∀ q < k', tr.time q ≤ d := fun q hq => (hrun.time_mono (by omega)).trans hmd
  have hOP := origin_mem_upTo hrun hav hcd hO
  have hCOP := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hOP hCO
  have hCP := Compose.anc_mem hCOP hOP
  have hDP : D ∈ (tr.upTo d).HonestBlocks (H d) :=
    ⟨a.val, hav, k', by rw [Trace.upTo_state tr a.val hk'le]; exact hD⟩
  refine ⟨D, ⟨C, l, hQ m hmi X hA a ha hav k hkm hS c hck C l O OV hC hO, hCP,
    RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hCP hDC⟩, ?_⟩
  have hk'st := Trace.upTo_state tr a.val hk'le
  exact Compose.isHonestSource_iff.2 ⟨a.val, hav, k', by rw [hk'st]; exact hD,
    by rw [hk'st]; exact hDT⟩

/-- `RowsAbove` at a height passes to every greater height. -/
private theorem rowsAbove_mono {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop} {Hs : Set (Fin sp.n)}
    {y : Fin sp.n} {i h₀ h₁ : Nat} (h : Compose.RowsAbove tr Hs G y i h₀) (hle : h₀ ≤ h₁) :
    Compose.RowsAbove tr Hs G y i h₁ :=
  Compose.rowsAbove_iff.2 fun X hX a ha hav hE hh =>
    Compose.rowsAbove_iff.1 h X hX a ha hav hE (hle.trans hh)

/-! ### Reads: the caches and full-read viability -/

/-- A block held below a source's entry height is below the entry (on a static run): the entry is
below the source, which is compatible with the block. -/
theorem held_below_entry {Hs : Set (Fin sp.n)} {tr₀ : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State} (hrun : GoldilocksRun proposer dg Hs tr₀ ini)
    (hnc : NoCollRun dg tr₀) {y : Fin sp.n}
    (hy : y ∈ Hs) {i : Nat} {B D E : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr₀.state y i).fg.tree) (hE : E ∈ (tr₀.state y i).fg.tree)
    (hD : Compose.IsHonestSource tr₀ Hs D E.root) (hDB : Compatible (tr₀.HonestBlocks Hs) D B)
    (hlt : ((tr₀.state y i).fg.σ B.root).h < ((tr₀.state y i).fg.σ E.root).h) :
    (tr₀.state y i).fg.Anc B E := by
  have hU := (Compose.projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := Compose.honest_source_entry hrun hnc hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr₀.HonestBlocks Hs) E D := hED.mono (Compose.fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr₀.HonestBlocks Hs) E B := fun h => by
    have := (Compose.honest_held_height hrun hnc hy (Compose.honest_held_anc hrun hnc hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hU h hEDU with h' | h'
    · exact Compose.honest_held_anc hrun hnc hy h' hE
    · exact absurd h' no

/-- P-U viability from the head height floor and the analysis root `Store.fcRoot` below the
block: `Σ.J` is that root exactly when the lower viable arm needs it. -/
private theorem isViable_of_floor_root {P : Goldilocks.Params} {ACP : Type}
    {st : Goldilocks.Store P ACP} {C : Goldilocks.NodeBlock P ACP} (hjm : st.hj < st.hmax)
    (hfl : st.headHeightFloor ≤ (st.σ C.root).h) (hroot : st.Anc st.fcRoot C) :
    st.IsViable C := by
  classical
  by_cases hc : st.Contest
  · have hf : st.headHeightFloor = st.hmax := by
      simp only [Goldilocks.Store.headHeightFloor, hc, ↓reduceIte]
    exact Or.inl (by omega)
  · have hf : st.headHeightFloor = st.hmax - 1 := by
      simp only [Goldilocks.Store.headHeightFloor, hc, ↓reduceIte]
    by_cases hm : st.hmax ≤ (st.σ C.root).h
    · exact Or.inl hm
    refine Or.inr ⟨by omega, ?_⟩
    by_cases hgap : st.hj + 1 < st.hmax
    · exact Or.inl hgap
    · rw [Goldilocks.Store.fcRoot_of_not_contest _ (by omega) hc] at hroot
      exact Or.inr hroot

/-- P-U viability of a block at height at least `h_max − 1` above `Σ.J`, or under a gap. -/
private theorem isViable_of_J_or_gap {P : Goldilocks.Params} {ACP : Type}
    {st : Goldilocks.Store P ACP} {C : Goldilocks.NodeBlock P ACP}
    (hh : st.hmax - 1 ≤ (st.σ C.root).h) (hJ : st.hj + 1 < st.hmax ∨ st.Anc st.J C) :
    st.IsViable C := by
  by_cases hm : st.hmax ≤ (st.σ C.root).h
  · exact Or.inl hm
  · exact Or.inr ⟨by omega, hJ⟩

/-- Two blocks on the healed chain are compatible once the members are. -/
private theorem onHealedChain_compatible (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {b : Time}
    (hP : ∀ C s C' s', HealedOrigin tr H g rL rO C s b → HealedOrigin tr H g rL rO C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {X Y : AC.Blk sp.n (List (FG.Att sp.n))} (hX : OnHealedChain tr H g rL rO X b)
    (hY : OnHealedChain tr H g rL rO Y b) : Compatible (tr.HonestBlocksAt H) X Y := by
  obtain ⟨C, s, hC, hXC⟩ := onHealedChain_iff.1 hX
  obtain ⟨C', s', hC', hYC'⟩ := onHealedChain_iff.1 hY
  exact compatible_of_anc_both (honestBlocksAt_coherent hrun hnc) hXC hYC' (hP C s C' s' hC hC')

/-- **The high rows of a seeded reader**, read at `t ≥ c_z` (earlier cuts at times `≤ t`, the
reader honest at `t`): on the prefix through `t`, every row of its tree naming a held entry of
height `≥ H_z + 1`, by a signer honest at `t`, has an honest source below a member of the healed
family within `t` held in the prefix (`RowsAbove` at height `H_z + 1`). -/
theorem seeded_rows_above_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {y : Fin sp.n}
      {i : Nat} {t : Time}
    (ht0 : 0 ≤ t) (hzt : Healing.cutZ sp.toParams g ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) :
    Compose.RowsAbove (tr.upTo t) (H t)
      (fun D => ∃ C l, HealedOrigin tr H g r (r + sp.k - 1) C l t ∧
        C ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D C) y i
      (Healing.Growing.HZ tr H g + 1) :=
  rowsAbove_of hrun hnc hseed ht0 hzt hi hy fun m hmi _ _ _ _ _ _ _ _ c _ _ _ _ _ hC _ =>
    hC.mono ((hrun.time_mono (by omega : c ≤ m)).trans (hi m hmi))

/-- **`Σ.J` of a high seeded reader is on the healed chain**: `Σ.J` is the entry of an honest
member of its target quorum (`f_t < n/2 < q`), whose source is below a member (the high rows). -/
private theorem seeded_reader_J_on_chain_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (htb : t ≤ b) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    (hhigh : ¬ (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g) :
    OnHealedChain tr H g r (r + sp.k - 1) (tr.state y i).fg.J b := by
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  obtain ⟨-, hJm, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hst := Trace.upTo_state tr y hi
  have hzt : Healing.cutZ sp.toParams g ≤ t := by
    obtain ⟨c, hci, -, -, hc⟩ := hcall
    obtain ⟨a₀, _, hp₀, -, -, hlo, -⟩ := hseed.reset_timing
    linarith [hp₀.cutZ_lt_reset_at, hi c hci, sp.toParams.hΔ]
  have hsrc := rowsAbove_mono (seeded_rows_above_at hrun hnc hseed ht0 hzt hi hy)
    (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo t).state y i).fg.hj by rw [hst]; omega)
  obtain ⟨-, -, D, ⟨C, l, hC, -, hDC⟩, hDs⟩ := Compose.justified_honest_source_of
    (hrun.upTo ht0) (hnc.upTo _) hf hy hsrc (by rw [hst]; omega)
  rw [hst] at hDs
  have hJP : (tr.state y i).fg.J ∈ (tr.upTo t).HonestBlocks (H t) :=
    ⟨y, hy, i, by rw [hst]; exact hJm⟩
  obtain ⟨x', hx', k', -, -, hJD, -, -⟩ :=
    Compose.honest_source_entry (hrun.upTo ht0) (hnc.upTo _) hDs hJP rfl
  exact onHealedChain_iff.2 ⟨C, l, hC.mono htb, Anc.mono (upTo_subset hrun ht0)
    ((Anc.mono (Compose.fg_tree_subset_honest hx' k') hJD).trans hDC)⟩

/-- **`Σ.F` and the analysis root `Store.fcRoot` of a seeded reader are on the healed chain.**
Low (`h_j ≤ H_z`): both are below the held reset seed. High: `Σ.J` is on the chain
(`seeded_reader_J_on_chain_at`) and `Σ.F ⪯ Σ.J`. -/
theorem seeded_reader_on_chain_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
    (hcv : ChainConvictedBelowUpTo tr H b)
      (hTb : T ≤ b) {y : Fin sp.n}
    {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c) :
    OnHealedChain tr H g r (r + sp.k - 1) (tr.state y i).fg.F b ∧
      OnHealedChain tr H g r (r + sp.k - 1) (tr.state y i).fg.fcRoot b := by
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  obtain ⟨-, -, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hFJ' := Healing.Growing.honest_anc_of_store_anc_at ht0 hi hy hFJ
  have below : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      OnHealedChain tr H g r (r + sp.k - 1) Y b → OnHealedChain tr H g r (r + sp.k - 1) X b :=
    fun hXY hY => let ⟨C, s, hC, hYC⟩ := onHealedChain_iff.1 hY
      onHealedChain_iff.2 ⟨C, s, hC, hXY.trans hYC⟩
  by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
  · obtain ⟨x, q, l, S, hS, hqT, -, hFS, hSy, -⟩ :=
      low_seed_held_upTo hrun hnc hseed hcv hTb ht0 hi hy htb hcall hlow
    have hSc : OnHealedChain tr H g r (r + sp.k - 1) S b :=
      onHealedChain_iff.2 ⟨S, l, .of_high (hqT.trans hTb) hS, .refl⟩
    exact ⟨below hFS hSc, below (low_fcRoot_below hrun hnc ht0 hi hy hlow hS hSy hFS) hSc⟩
  have hJ := seeded_reader_J_on_chain_at hrun hnc hseed ht0 hi htb hy hf hcall hlow
  refine ⟨below hFJ' hJ, ?_⟩
  rw [Goldilocks.Store.fcRoot]
  split_ifs
  · exact hJ
  · exact below hFJ' hJ

/-- **The seeded cache facts**, for a reader honest at `t ≥ 0` with a call from `t_{r−k−3}` before
its read: `Σ.F` is on the healed chain, and `fc_root` is compatible with every member held in the
frame (both are below members, which are pairwise compatible). -/
theorem seeded_caches_of (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
    (hcv : ChainConvictedBelowUpTo tr H b)
      (hTb : T ≤ b)
    (hP : ∀ C s C' s', HealedOrigin tr H g r (r + sp.k - 1) C s b →
      HealedOrigin tr H g r (r + sp.k - 1) C' s' b → Compatible (tr.HonestBlocksAt H) C C')
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (htb : t ≤ b) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c) :
    OnHealedChain tr H g r (r + sp.k - 1) (tr.state y i).fg.F b ∧
      ∀ C s, HealedOrigin tr H g r (r + sp.k - 1) C s b →
        C ∈ (Node.frame (tr.state y i)).tree →
        Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot C := by
  obtain ⟨hF, -⟩ := seeded_reader_on_chain_at hrun hnc hseed hcv hTb ht0 hi htb hy hf hcall
  exact ⟨hF, fun C s hC _ => onHealedChain_compatible hrun hnc hP hF
    (onHealedChain_iff.2 ⟨C, s, hC, .refl⟩)⟩

/-- **Full-read viability for the healed chain** (S3 at full reads), for a reader honest at `t ≥ 0`
with a call from `t_{r−k−3}` before its read: a block on the healed chain held in the frame is at
or below `fc_root` or in the full viable tree. `fc_root` is on the healed chain, so it is
compatible with the block; above `fc_root`, the block is viable itself, or below a viable block of
the tree. High reader: the floor crossing of the store geometry (`floor_or_crossing_of`) over the
high rows. Low reader: below the held seed `S` when the floor is at most `h(S)`; otherwise there is
no contest (a contest puts the floor at `h_max = h_j + 1 ≤ H_z + 1`), and the crossing of the
floor `h_max − 1 ≥ H_z + 1` is a high row whose entry is above the block. -/
theorem seeded_viable_of (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
    (hcv : ChainConvictedBelowUpTo tr H b)
      (hTb : T ≤ b)
    (hP : ∀ C s C' s', HealedOrigin tr H g r (r + sp.k - 1) C s b →
      HealedOrigin tr H g r (r + sp.k - 1) C' s' b → Compatible (tr.HonestBlocksAt H) C C')
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (htb : t ≤ b) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp), tr.projAC.CallAt y c ell ∧
      sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} (hC : OnHealedChain tr H g r (r + sp.k - 1) C b)
    (hCt : C ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc C (Node.frame (tr.state y i)).fcRoot ∨
      C ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hreach := Healing.Growing.fg_reachable_at hrun ht0 hi hy
  have hst := Trace.upTo_state tr y hi
  have hrun' := hrun.upTo ht0
  have hnc' := hnc.upTo t
  have hUP := (Compose.projFG_localRun hrun' hnc').coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) := frameOK_at hrun ht0 hy hi
  have hsU : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H := fun X hX => ⟨y, i, t, ht0, hi, hy, hX⟩
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H := fun X hX => hsU hX.1
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  obtain ⟨hF, hfc⟩ := seeded_reader_on_chain_at hrun hnc hseed hcv hTb ht0 hi htb hy hf hcall
  rcases onHealedChain_compatible hrun hnc hP hF hC with hfB | hBf
  swap
  · exact Or.inl (AC.anc_tree_of_anc_U hU hΦ hΦU hCt hBf hΦ.fcRoot_mem)
  have hΦfB := AC.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hCt
  right
  suffices h : ∃ X ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc C X ∧
      (tr.state y i).fg.IsViable X by
    obtain ⟨X, hX, hCX, hXv⟩ := h
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hCt.2.trans hCX⟩
    exact ⟨hCt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, hXv⟩,
      AC.anc_tree_of_anc_U hU hΦ hΦU hCt (Anc.mono hsU hCX) hXΦ⟩
  have hjm := Healing.Store.hj_lt_hmax_of_reachable hreach
  obtain ⟨hFm, hJm, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  -- the analysis root `Store.fcRoot` against `C`, in the store
  by_cases hfl : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ C.root).h
  · have hfcm : (tr.state y i).fg.fcRoot ∈ (tr.state y i).fg.tree := by
      rw [Goldilocks.Store.fcRoot]
      split_ifs
      · exact hJm
      · exact hFm
    rcases onHealedChain_compatible hrun hnc hP hfc hC with h | h
    · exact ⟨C, hCt.1, .refl,
        isViable_of_floor_root hjm hfl (held_anc_at hrun hnc ht0 hy hi h hCt.1)⟩
    · have h' := held_anc_at hrun hnc ht0 hy hi h hfcm
      exact ⟨_, hfcm, h', isViable_of_floor_root hjm
        (hfl.trans (Healing.h_le_of_store_anc hreach h')) .refl⟩
  -- the sources of the high rows compare with `C`, inside the prefix
  have hCP : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, by rw [hst]; exact hCt.1⟩
  have hzt : Healing.cutZ sp.toParams g ≤ t := by
    obtain ⟨c, hci, -, -, hc⟩ := hcall
    obtain ⟨a₀, _, hp₀, -, -, hlo, -⟩ := hseed.reset_timing
    linarith [hp₀.cutZ_lt_reset_at, hi c hci, sp.toParams.hΔ]
  have hsrc := seeded_rows_above_at hrun hnc hseed ht0 hzt hi hy
  have hmem : ∀ {C'} {l : Nat}, HealedOrigin tr H g r (r + sp.k - 1) C' l t →
      OnHealedChain tr H g r (r + sp.k - 1) C' b :=
    fun hC' => onHealedChain_iff.2 ⟨_, _, hC'.mono htb, .refl⟩
  have hGB : ∀ D, (∃ C' l, HealedOrigin tr H g r (r + sp.k - 1) C' l t ∧
      C' ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D C') →
      Compatible ((tr.upTo t).HonestBlocks (H t)) D C := by
    rintro D ⟨C', l, hC', hC'P, hDC'⟩
    exact compatible_of_anc_left hUP hDC' (compatible_upTo hrun hnc ht0 hC'P hCP
      (onHealedChain_compatible hrun hnc hP (hmem hC') hC))
  by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
  · obtain ⟨x, q, l, S, hS, hqT, -, hFS, hSy, -⟩ :=
      low_seed_held_upTo hrun hnc hseed hcv hTb ht0 hi hy htb hcall hlow
    have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
      rw [Healing.Growing.σ_eq_honest_at hrun hnc ht0 hi hy (hrun.time_nonneg q)
        (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hS.1) hSy
        (HighOrigin.mem_tree hrun hnc hS)]
      exact hS.2.2.2
    by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h
    · have hCS : Anc (tr.HonestBlocksAt H) C S := by
        rcases onHealedChain_compatible hrun hnc hP hC
          (onHealedChain_iff.2 ⟨S, l, .of_high (hqT.trans hTb) hS, .refl⟩) with h | h
        · exact h
        · have := Healing.h_le_of_store_anc hreach (held_anc_at hrun hnc ht0 hy hi h hCt.1)
          omega
      exact ⟨S, hSy, held_anc_at hrun hnc ht0 hy hi hCS hSy, isViable_of_floor_root hjm hSf
        (held_anc_at hrun hnc ht0 hy hi (low_fcRoot_below hrun hnc ht0 hi hy hlow hS hSy hFS) hSy)⟩
    have hcon : ¬ (tr.state y i).fg.Contest := fun hc => hSf (by
      simp only [Goldilocks.Store.headHeightFloor, hc, ↓reduceIte]
      have := hc.1
      omega)
    have hfl' : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
      simp only [Goldilocks.Store.headHeightFloor, hcon, ↓reduceIte]
    obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ := Compose.frame_crossing_source_of hrun' hnc' hf hy
      hsrc (W := X) (j := (tr.state y i).fg.hmax - 1) (by rw [hst]; exact hX) (by omega) (by omega)
      (by rw [hst, hXh]; omega)
    rw [hst] at hE hEX hEh
    have hCE := held_below_entry hrun' hnc' hy (by rw [hst]; exact hCt.1) (by rw [hst]; exact hE)
      hDs (hGB D hD) (by rw [hst, hEh]; omega)
    rw [hst] at hCE
    exact ⟨X, hX, hCE.trans hEX, Or.inl hXh.ge⟩
  · have hGG : ∀ D D', (∃ C' l, HealedOrigin tr H g r (r + sp.k - 1) C' l t ∧
        C' ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D C') →
        (∃ C' l, HealedOrigin tr H g r (r + sp.k - 1) C' l t ∧
        C' ∈ (tr.upTo t).HonestBlocks (H t) ∧ Anc ((tr.upTo t).HonestBlocks (H t)) D' C') →
        Compatible ((tr.upTo t).HonestBlocks (H t)) D D' := by
      rintro D D' ⟨C₁, l₁, hC₁, hC₁P, hDC₁⟩ ⟨C₂, l₂, hC₂, hC₂P, hDC₂⟩
      exact compatible_of_anc_both hUP hDC₁ hDC₂ (compatible_upTo hrun hnc ht0 hC₁P hC₂P
        (onHealedChain_compatible hrun hnc hP (hmem hC₁) (hmem hC₂)))
    have h := Compose.floor_or_crossing_of hrun' hnc' hf hy
      (rowsAbove_mono hsrc (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo t).state y i).fg.hj by
        rw [hst]; omega)) hGG hGB (by rw [hst]; exact hCt.1)
    rw [hst] at h
    rcases h with h | ⟨-, E, X, -, -, -, hCE, -, hX, hEX, hXv⟩
    · -- `h_max − 1 ≤ h(C)` below the floor: a contest, so `h_max = h_j + 1`; compare with `Σ.J`
      have hcon : (tr.state y i).fg.Contest := by
        by_contra hcn
        apply hfl
        simp only [Goldilocks.Store.headHeightFloor, hcn, ↓reduceIte]
        exact h
      have hJc := seeded_reader_J_on_chain_at hrun hnc hseed ht0 hi htb hy hf hcall hlow
      rcases onHealedChain_compatible hrun hnc hP hJc hC with hJC | hCJ
      · exact ⟨C, hCt.1, .refl, isViable_of_J_or_gap h
          (Or.inr (held_anc_at hrun hnc ht0 hy hi hJC hCt.1))⟩
      · have hCJ' := held_anc_at hrun hnc ht0 hy hi hCJ hJm
        exact ⟨_, hJm, hCJ', isViable_of_J_or_gap
          (h.trans (Healing.h_le_of_store_anc hreach hCJ')) (Or.inr .refl)⟩
    · exact ⟨X, hX, hCE.trans hEX, hXv⟩

/-! ### Votes: the frozen witness after the split slot -/

private theorem add_mul_delta_le {x a c : Time} (h : a ≤ c) : x + a * sp.Δ ≤ x + c * sp.Δ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right h sp.toParams.hΔ.le)

/-- A block held by a node at a call `c`, honest then, was accepted by it (or is genesis) at an
AC block call no later than `time c`. -/
private theorem acceptedBefore_of_tree (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {c i : Nat} (hyc : y ∈ H (tr.time c))
    (hy : y ∈ H (tr.time i)) (hci : tr.time c ≤ tr.time i) {Z : AC.Blk sp.n (List (FG.Att sp.n))}
    (hZ : Z ∈ (tr.state y c).fg.tree) {τ : Time} (hτ : tr.time c < τ) :
    AC.AcceptedBefore tr.projAC y Z τ := by
  have hdc := hrun.time_nonneg c
  have hstc : (tr.upTo (tr.time c)).state y c = tr.state y c :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  rw [← hstc, ← Compose.store_eq (hrun.upTo hdc) hyc c] at hZ
  rcases Store.tree_accepted (Compose.projFG_localRun (hrun.upTo hdc) (hnc.upTo _)) hyc hZ with
    hg | ⟨m, -, hA⟩
  · exact Or.inl (by rw [hg]; rfl)
  obtain ⟨hmd, hA⟩ := (RunTrace.upTo_acceptAt tr).mp (Compose.projFG_callAt.1 hA)
  obtain ⟨ℓy, hcy, hby, hty⟩ := Compose.accept_next (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
    ((RunTrace.upTo_acceptAt tr).mpr ⟨hmd.trans hci, hA⟩)
  obtain ⟨-, hcy⟩ := (Trace.upTo_callAt tr).mp hcy
  have hty' : tr.time (m + 1) = tr.time m := hty
  exact Or.inr ⟨m + 1, ⟨ℓy, Compose.projAC_callAt.2 hcy, hby⟩, by
    change tr.time (m + 1) < _; rw [hty']; exact hmd.trans_lt hτ⟩

/-- **A block accepted before the freeze is in the voter block tree** of a slot-`(s+1)` vote of a
node honest at its cut, when it extends the voter's `Σ.F` (`accepted_voter_tree` on the prefix
through the vote). -/
private theorem frozen_of_accepted (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {Z : AC.Blk sp.n (List (FG.Att sp.n))} (hZ : Z ∈ tr.HonestBlocksAt H)
    (hacc : AC.AcceptedBefore tr.projAC y Z (sp.ts s + 3 * sp.Δ))
    (hFZ : Anc (tr.HonestBlocksAt H) ℓ.frame.F Z) :
    Z ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1) := by
  have hd := hrun.time_nonneg i
  have hU := honestBlocksAt_coherent hrun hnc
  have hT : sp.ts s + 3 * sp.Δ ≤ tr.time i := by
    linarith [(honest_vote_restarts_at hrun hnc hy hc hs).2, sp.toParams.hΔ]
  have hΦ := (frameIn_at hrun hnc hy hc.1).1
  have hZp : Z ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := by
    rcases hacc with hg | ⟨k', hk', hk't⟩
    · have hFp := frame_upTo_at hrun hnc hy hc.1 hΦ.rooted.1
      have hG := (Compose.honest_genesis_anc (hrun.upTo hd) hFp).1
      rwa [honestAt_eq_genesis hrun hU hZ hg]
    · have hk'd : tr.time k' ≤ tr.time i := hk't.le.trans hT
      have hk'' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k' Z :=
        (ac_acceptAt_upTo _).mpr ⟨hk'd, hk'⟩
      obtain ⟨ℓk, hck, -⟩ := hk'
      exact mem_upTo_of_frame hrun hy hk'd hck
        ((AC.accept_new sp (acRun_upTo hrun hnc hd).localRun hy hk'').1 ℓk
          ((Trace.upTo_callAt_of_le tr.projAC hk'd).mpr hck))
  exact Compose.accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy
    (by rw [RunTrace.upTo_projAC]; exact ac_castAt_upTo.mpr ⟨le_rfl, hc⟩) hs hZp
    (by
      rw [RunTrace.upTo_projAC]
      exact hacc.imp_right fun ⟨k', hk', hk't⟩ =>
        ⟨k', (ac_acceptAt_upTo _).mpr ⟨hk't.le.trans hT, hk'⟩, hk't⟩)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hZp hFZ)

/-- **A head of a slot `≤ s`, of a vote of a node honest at it, is accepted before the freeze** by a
slot-`(s+1)` voter honest at its cut whose `Σ.F` it extends, under the sleepy service from `ḡ`
(`ḡ + 2Δ ≤ t_s`): its voter accepted it (or it is genesis) while honest, by `t_s + Δ`; an acceptance
from `ḡ` on is relayed to the voter by `t_s + 2Δ`, an earlier one is caught up before `ḡ + 2Δ`. -/
private theorem head_accepted_from (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time}
    (hsync : SleepyServiceFrom tr H ΔF (AC.gbar g) (2 * sp.Δ) b) {s : Nat}
    (hgs : AC.gbar g + 2 * sp.Δ ≤ sp.ts s) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {x : Fin sp.n} {k : Nat} {e' : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e') (hs' : e'.msg.slot ≤ s) {Hd : AC.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocksAt H) (hHdr : Hd.root = e'.msg.head)
    (hFHd : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    AC.AcceptedBefore tr.projAC y Hd (sp.ts s + 3 * sp.Δ) := by
  have hm := hrun.time_mono
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hx, ℓ', hcx, hex⟩ := hVoteAt_iff.1 hv
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩
  rw [frame_of_projAC_at hrun hx hcx] at hHd't
  obtain rfl : Hd = Hd' :=
    (hU.1 (mem_honestBlocksAt hrun hx hHd't.1) hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts s + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 : sp.ts (e'.msg.slot : Int) ≤ sp.ts (s : Int) := (AC.ts_le_iff sp).2 (by omega)
    exact h1.trans (add_le_add h2 le_rfl)
  obtain ⟨hrs, hti⟩ := honest_vote_restarts_at hrun hnc hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s := fun c hc' ⟨ℓr, hcr, hrr⟩ =>
    hrs c hc' ⟨ℓr, Compose.projAC_callAt.2 hcr, hrr⟩
  -- its voter accepted it while honest (or it is genesis), on the prefix through `tr.time k`
  have hdk := hrun.time_nonneg k
  have hstk : (tr.upTo (tr.time k)).state x k = tr.state x k := RunTrace.upTo_state_of_le hm le_rfl
  have hHdx := hHd't.1
  rw [← hstk, ← Compose.store_eq (hrun.upTo hdk) hx k] at hHdx
  rcases Store.tree_accepted (Compose.projFG_localRun (hrun.upTo hdk) (hnc.upTo _)) hx hHdx with
    hg | ⟨m, -, hA⟩
  · exact Or.inl (by rw [hg]; rfl)
  obtain ⟨hmd, hA⟩ := (RunTrace.upTo_acceptAt tr).mp (Compose.projFG_callAt.1 hA)
  have hxm : x ∈ H (tr.time m) := hrun.antitone hmd hx
  have hmt : tr.time m ≤ sp.ts s + sp.Δ := hmd.trans hkt'
  have hFy : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Hd := by
    rw [frame_of_projAC_at hrun hy hc.1] at hFHd; exact hFHd
  have hcall : tr.IsCall y i := ⟨_, Compose.projAC_callAt.1 hc.1⟩
  -- the voter accepts it before `t_s + 2Δ`
  obtain ⟨k', hk'i, hAy, hk't⟩ : ∃ k' ≤ i, tr.AcceptAt y k' Hd ∧
      tr.time k' < sp.ts s + 2 * sp.Δ := by
    by_cases hgm : AC.gbar g ≤ tr.time m
    · have hdl : ∀ c ≤ i, tr.deadline y c (tr.time m) sp.Δ ≤ sp.ts s + 2 * sp.Δ := fun c hc' => by
        have := Compose.deadline_le_of_restarts (fun k hk hr' => hrs' k (hk.trans hc') hr')
          (tr.time m) sp.Δ
        refine this.trans ?_
        rw [two_mul, ← add_assoc]
        exact add_le_add (max_le hmt (le_add_of_nonneg_right hΔ.le)) le_rfl
      have hdi : tr.deadline y i (tr.time m) sp.Δ ≤ tr.time i :=
        (hdl i le_rfl).trans ((add_mul_delta_le (by norm_num)).trans hti)
      obtain ⟨k', hk'i, hAy, hk't⟩ := hsync.relay x m Hd hxm hA hgm y i hy hcall (hdi.trans hib)
        hdi hFy
      exact ⟨k', hk'i, hAy, hk't.trans_le (hdl k' hk'i)⟩
    · obtain ⟨k', hk'i, hAy, hk't⟩ := hsync.old x m Hd hxm hA (lt_of_not_ge hgm) y i hy hcall
        (by linarith) hFy
      exact ⟨k', hk'i.le, hAy, by linarith⟩
  have hk'd : tr.time k' ≤ tr.time i := hm hk'i
  obtain ⟨ℓy, hcy, hby, hty⟩ := Compose.accept_next (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
    ((RunTrace.upTo_acceptAt tr).mpr ⟨hk'd, hAy⟩)
  obtain ⟨-, hcy⟩ := (Trace.upTo_callAt tr).mp hcy
  have hty' : tr.time (k' + 1) = tr.time k' := hty
  exact Or.inr ⟨k' + 1, ⟨ℓy, Compose.projAC_callAt.2 hcy, hby⟩, by
    change tr.time (k' + 1) < _; rw [hty']; linarith⟩

/-- **A head of a slot `≤ s`, of a vote of a node honest at it, is in the voter block tree** of a
slot-`(s+1)` vote of a node honest at its cut, under the sleepy service from `ḡ`, once it extends
the voter's `Σ.F`. -/
private theorem head_frozen_from (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time}
    (hsync : SleepyServiceFrom tr H ΔF (AC.gbar g) (2 * sp.Δ) b) {s : Nat}
    (hgs : AC.gbar g + 2 * sp.Δ ≤ sp.ts s) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {x : Fin sp.n} {k : Nat} {e' : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e') (hs' : e'.msg.slot ≤ s) {Z : AC.Blk sp.n (List (FG.Att sp.n))}
    (hZ : AC.VoteExtends (tr.HonestBlocksAt H) e'.msg Z)
    (hFZ : Anc (tr.HonestBlocksAt H) ℓ.frame.F Z) :
    ∃ W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocksAt H) Z W := by
  obtain ⟨Hd, hHd, hHdr, hZHd⟩ := hZ
  have hFHd := hFZ.trans hZHd
  exact ⟨Hd, frozen_of_accepted hrun hnc hy hc hs hHd
    (head_accepted_from hrun hnc hsync hgs hy hc hs hib hv hs' hHd hHdr hFHd) hFHd, hZHd⟩

/-- **Every member of label `l` is extended by an honest vote of a slot `≤ max l (σ + 1)`**: from
the lock floor on, the honest supporter of the member's origin (`honest_supporter_at`, the slot
count of label `l ≥ r` and the service from `ḡ ≤ t_l`); below it the member is a high origin
written by `t_l + 6Δ ≤ T`, extended by every honest vote up to `T` of a slot in `(l, σ + 1]`
(the seed's `V` row), and there is such a vote of slot `σ + 1` (its slot count). -/
private theorem member_supported (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
      (hTb : T ≤ b)
    (hsync : SleepyServiceFrom tr H ΔF (AC.gbar g) (2 * sp.Δ) b)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {l : Nat}
    (hC : HealedOrigin tr H g r (r + sp.k - 1) C l b)
    {K : AC.CommitteeDict sp.n} (hK : CommitteeFacts tr H K)
    (hKB : CommitteeBoundsFrom tr H K r b) :
    ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot ≤ max l (σ + 1) ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e'.msg C := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  obtain ⟨hσT, hrσ, hgr⟩ := hseed.timing
  have hσ1 : sp.ts ((σ + 1 : Nat) : Int) = sp.ts σ + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hσ2 : sp.ts ((σ + 1 + 1 : Nat) : Int) = sp.ts σ + 8 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  rcases Nat.lt_or_ge l r with hlr | hlr
  · obtain ⟨x, q, -, ho⟩ : ∃ x q, tr.time q ≤ b ∧ Healing.Growing.HighOrigin tr H g x q l C := by
      rcases healedOrigin_iff.1 hC with ⟨h, -⟩ | ⟨h, -⟩ | h
      · omega
      · omega
      · exact h
    obtain ⟨CV, -, D, -, hfl, -⟩ := ho.2.2.1
    have hqT : tr.time q ≤ T := by
      have := (fastLockAt_time hrun hfl).2
      have := ts_le_ts (sp := sp) (show l ≤ σ by omega)
      linarith
    have hcount := faults_lt_voters hrun hnc hK hKB (s := σ + 1) (d := sp.ts (σ + 1 : Nat) + sp.Δ)
      (by omega) le_rfl (by linarith) (by linarith)
    obtain ⟨x', hx'⟩ : (VotersAt tr H (σ + 1) (sp.ts (σ + 1 : Nat) + sp.Δ)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      rw [h, Set.ncard_empty] at hcount
      omega
    obtain ⟨-, k, e', hv, hvs⟩ := votersAt_iff.1 hx'
    have hkT : tr.time k ≤ T := by
      have h1 := (vote_time hrun hnc hv).2
      rw [hvs] at h1
      linarith
    exact ⟨x', k, e', hv, by omega, healedVotesBelow_iff.1 hseed.frontier.2 C l
      (.of_high hqT ho) x' k e' hv hkT (by omega) (by omega)⟩
  · obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
    obtain ⟨x, k, e', hv, -, hes, hext⟩ := honest_supporter_at hrun hnc
        hK hsync hKB hlr
      (by have := ts_le_ts (sp := sp) hlr; linarith) hO
    exact ⟨x, k, e', hv, by omega, voteExtends_of_anc hext hCO⟩

/-- **The label of a high row's member at a vote is at most `s`**: the member's origin, written by
the signer before the signing and so before the slot-`(s+1)` vote at `≤ t_{s+1} + Δ`, is a result
at `t_l + 6Δ` (so `l < s`), or an optimistic selection in slot `l` (so `l ≤ s + 1`, and label
`s + 1` is `no_optimistic_before_held_row_at`). -/
private theorem member_label_le (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i s : Nat} {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {m : Nat} (hmi : m < i)
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hA : tr.AcceptAt y m X) {a : FG.Att sp.n}
    (hav : a.val ∈ H (tr.time m)) {k : Nat} (hkm : k < m) (hS : tr.SignAt a.val k a) {c : Nat}
    (hck : c < k) {l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))} {OV : Set (Vote sp.n)}
    (hO : AC.ResultAt tr.projAC a.val c l O OV ∨ AC.OptimisticLockAt tr.projAC a.val c l O OV)
    {K : AC.CommitteeDict sp.n} (hK : CommitteeFacts tr H K)
    (hfK : sp.ts (s + 1 : Nat) ≤ tr.time c → tr.time c < sp.ts (s + 2 : Nat) →
      2 * (K.committee (s + 1) ∩ (H (tr.time c))ᶜ).ncard < sp.committeeSize) :
    l ≤ s := by
  have hΔ := sp.toParams.hΔ
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot_at hrun hnc hy hc).2
    rw [hs] at h
    simp only [ACParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hci : tr.time c ≤ tr.time i := hrun.time_mono (by omega)
  rcases hO with ⟨ℓR, ⟨-, -, htR, -⟩, -⟩ | hO
  · have htR' : tr.time c = sp.ts (l : Int) + 6 * sp.Δ := htR
    have : sp.ts (l : Int) < sp.ts (s : Int) := by linarith
    have := (AC.ts_lt_iff sp).1 this
    omega
  · obtain ⟨-, -, -, hslot, -⟩ := id hO
    change sp.slot (tr.time c) = l at hslot
    have h1 := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg c) (l : Int)).2 (by omega)
    by_contra hl
    rcases (show l = s + 1 ∨ s + 2 ≤ l by omega) with rfl | hl2
    · have hcm := hrun.time_mono (show c ≤ m by omega)
      exact no_optimistic_before_held_row_at hrun hnc hK
        hy hc hs hA hmi hav hkm hS (hrun.antitone hcm hav) hck hO (hfK h1 (by
          have h2 := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg c) ((s + 2 : Nat) : Int)).not.2
            (by omega)
          exact lt_of_not_ge h2))
    · have h2 := (AC.ts_le_iff sp).2 (show ((s + 2 : Nat) : Int) ≤ (l : Int) by exact_mod_cast hl2)
      have h3 := ts_add (sp := sp) s 2
      push_cast at h2 h3
      linarith

/-- **The seeded frozen witness** (S3 at a vote after the split slot). At an honest vote of slot
`s + 1 > σ + 1`, a block `B` compatible with every member of label `≤ s` and extended by an honest
slot-`s` vote is in the viable voter block tree or at or below `fc_root`, given `P_{s+1}`. The
high rows of the voter's tree are sourced below members of labels `≤ s`, each extended by an
honest vote of a slot `≤ s` and so frozen at the vote. `fc_root` is compatible with `B`: a high
`Σ.J` is the entry of such a source, and a low reader's `fc_root` is below the held reset seed.
Above `fc_root`, `B` is in the frame (between `Σ.F` and its frozen supporter) and has a viable
frozen descendant: its supporter's head when the floor is at most its height; otherwise the
frozen head above the crossing of the floor, which is a high row (the floor is at least
`H_z + 1`, or the low reader's held seed is viable). -/
theorem seeded_vote_frame_of (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hseed : HandoverCore tr H proposer dg g ΔF T r σ (cm := cm) (βK := βK)) {b : Time}
      (hTb : T ≤ b)
    (hsvc : Healing.Growing.ACResetService tr H g ΔF) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelowUpTo tr H b) {s : Nat} (hs : σ + 1 ≤ s)
    (hP : HealedOriginsBelow tr H g r (r + sp.k - 1) (s + 1) b) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ℓ e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C l, HealedOrigin tr H g r (r + sp.k - 1) C l b → l ≤ s →
      Compatible (tr.HonestBlocksAt H) B C)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    {K : AC.CommitteeDict sp.n} (hK : CommitteeFacts tr H K)
    (hKB : CommitteeBoundsFrom tr H K r b) :
    B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  have hΔ := sp.toParams.hΔ
  have hCB : ∀ C l, HealedOrigin tr H g r (r + sp.k - 1) C l b → l ≤ s →
      Compatible (tr.HonestBlocksAt H) C B := fun C l hC hl => Or.symm (hBc C l hC hl)
  obtain ⟨hσT, hrσ, hgr⟩ := hseed.timing
  have hd := hrun.time_nonneg i
  have hi : ∀ k < i, tr.time k ≤ tr.time i := fun _ h => hrun.time_mono h.le
  have hf := hB.two (tr.time i) hd hib
  have hU := honestBlocksAt_coherent hrun hnc
  have hst := Trace.upTo_state tr y hi
  have hrun' := hrun.upTo hd
  have hnc' := hnc.upTo (tr.time i)
  have hUP := (Compose.projFG_localRun hrun' hnc').coherent
  have hsub := upTo_subset hrun hd
  have hreach := Healing.Growing.fg_reachable_at hrun hd hi hy
  have hsync := sleepyServiceFrom_of_reset hrun hsvc hseed.catchRun (κ := 2 * sp.Δ) (b := b)
    (by linarith)
  have hgs : AC.gbar g + 2 * sp.Δ ≤ sp.ts s := by
    have := ts_le_ts (sp := sp) (show r ≤ s by omega)
    linarith
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  have hfr := frame_of_projAC_at hrun hy hc.1
  have hsU : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H := fun X hX =>
    mem_honestBlocksAt hrun hy hX
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hes] at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by rw [← h])
  have hrk : sp.ts (r + sp.k : Nat) ≤ tr.time i :=
    (ts_le_ts (sp := sp) (show r + sp.k ≤ s + 1 by omega)).trans hti
  -- members of labels `≤ s` compare
  have hPc : ∀ C l C' l', HealedOrigin tr H g r (r + sp.k - 1) C l b → l ≤ s →
      HealedOrigin tr H g r (r + sp.k - 1) C' l' b → l' ≤ s →
      Compatible (tr.HonestBlocksAt H) C C' := fun C l C' l' h hl h' hl' =>
    healedOriginsBelow_iff.1 hP C l C' l' (by omega) (by omega) h h'
  -- frozen witnesses
  have frozen : ∀ {Z : AC.Blk sp.n (List (FG.Att sp.n))} {x k e'}, HVoteAt tr H x k e' →
      e'.msg.slot ≤ s → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg Z →
      Anc (tr.HonestBlocksAt H) ℓ.frame.F Z →
      ∃ W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocksAt H) Z W :=
    fun hv hs' hZ hFZ => head_frozen_from hrun hnc hsync hgs hy hc hes hib hv hs' hZ hFZ
  -- the high rows, sourced below supported members of labels `≤ s`
  let Q : AC.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop := fun C l =>
    HealedOrigin tr H g r (r + sp.k - 1) C l b ∧ l ≤ s ∧ ∃ x k e', HVoteAt tr H x k e' ∧
      e'.msg.slot ≤ s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e'.msg C
  have hzd : Healing.cutZ sp.toParams g ≤ tr.time i := by
    obtain ⟨a₀, _, hp₀, -, -, hlo, -, hlt, -⟩ := hseed.reset_timing
    linarith [hp₀.cutZ_lt_reset_at, sp.toParams.hΔ]
  have hsrc := rowsAbove_of hrun hnc hseed hd hzd hi hy (Q := Q)
    fun m hmi X hA a ha hav k hkm hS c hck C l O OV hC hO => by
      have hl := member_label_le hrun hnc hy hc hes hmi hA
        (hrun.antitone (hrun.time_mono hmi.le) hav) hkm hS hck hO hK (fun h1 h2 => by
          rw [← hK.hsize (s + 1)]
          exact hKB.two_in_slot (by omega) h1 h2
            ((hrun.time_mono (show c ≤ i by omega)).trans hib))
      have hCb : HealedOrigin tr H g r (r + sp.k - 1) C l b :=
        hC.mono ((hrun.time_mono (by omega : c ≤ i)).trans hib)
      obtain ⟨x, k', e', hv, hvs, hext⟩ := member_supported hrun hnc hseed hTb hsync hCb hK hKB
      exact ⟨hCb, hl, x, k', e', hv, by omega, hext⟩
  have hGB : ∀ D, (∃ C l, Q C l ∧ C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) ∧
      Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D C) →
      Compatible (tr.HonestBlocksAt H) D B := by
    rintro D ⟨C, l, ⟨hC, hl, -⟩, -, hDC⟩
    exact compatible_of_anc_left hU (hDC.mono hsub) (hCB C l hC hl)
  -- a crossing source above `B` gives a viable frozen witness
  have cross : ∀ D E, (∃ C l, Q C l ∧ C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) ∧
      Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D C) →
      Compose.IsHonestSource (tr.upTo (tr.time i)) (H (tr.time i)) D E.root →
      E ∈ (tr.state y i).fg.tree → Anc (tr.HonestBlocksAt H) ℓ.frame.F E →
      ∃ W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocksAt H) E W ∧
        ((tr.state y i).fg.σ E.root).h ≤ ((tr.state y i).fg.σ W.root).h := by
    rintro D E ⟨C, l, ⟨-, -, x, k, e', hv, hvs, hext⟩, -, hDC⟩ hDs hE hFE
    have hEP : E ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
      ⟨y, hy, i, by rw [hst]; exact hE⟩
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := Compose.honest_source_entry hrun' hnc' hDs hEP rfl
    have hEC : Anc (tr.HonestBlocksAt H) E C :=
      Anc.mono hsub ((Anc.mono (Compose.fg_tree_subset_honest hx₀ k₀) hED).trans hDC)
    obtain ⟨W, hW, hCW⟩ := frozen hv hvs hext (hFE.trans hEC)
    have hWt : W ∈ (tr.state y i).fg.tree := by have := hW.1; rw [hfr] at this; exact this.1
    exact ⟨W, hW, hEC.trans hCW, Healing.h_le_of_store_anc hreach
      (held_anc_at hrun hnc hd hy hi (hEC.trans hCW) hWt)⟩
  have hvbt : ∀ {W}, W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1) →
      W ∈ (tr.state y i).fg.tree := fun hW => by
    have := hW.1
    rw [hfr] at this
    exact this.1
  have hjm := Healing.Store.hj_lt_hmax_of_reachable hreach
  -- the analysis root `Store.fcRoot` against `B`; a viable frozen witness above `B` once `B` is
  -- above that root; and, without a contest at `h_max = h_j + 1`, one above `Σ.J`
  have key : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot B ∧
      (B ∈ (tr.state y i).fg.tree → Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
        Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot B →
        (∃ W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocksAt H) B W) →
        ¬ (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h →
        ∃ D ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1),
          Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) ∧
      ((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 → ¬ (tr.state y i).fg.Contest →
        ∃ D ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1),
          Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D ∧ (tr.state y i).fg.IsViable D) := by
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.Growing.HZ tr H g
    · obtain ⟨x, q, l, S, hS, hqT, hlr, hFS, hSy, c, hci, hct, hSc⟩ :=
        low_seed_held_upTo hrun hnc hseed hcv hTb hd hi hy hib
          (seeded_reader_called_at hrun hseed hy hrk le_rfl) hlow
      have hSm : HealedOrigin tr H g r (r + sp.k - 1) S l b := .of_high (hqT.trans hTb) hS
      have hSB := hCB S l hSm (by omega)
      have hfcS := low_fcRoot_below hrun hnc hd hi hy hlow hS hSy hFS
      have hSh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ S.root).h := by
        rw [Healing.Growing.σ_eq_honest_at hrun hnc hd hi hy (hrun.time_nonneg q)
          (fun _ h => hrun.time_mono h.le) (hrun.antitone (le_max_right _ _) hS.1) hSy
          (HighOrigin.mem_tree hrun hnc hS)]
        exact hS.2.2.2
      have hct' : tr.time c < sp.ts s + 3 * sp.Δ := by
        have := ts_le_ts (sp := sp) (show r - sp.k - 3 ≤ s by omega)
        linarith
      have hSv : S ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1) :=
        frozen_of_accepted hrun hnc hy hc hes (hsU hSy)
          (acceptedBefore_of_tree hrun hnc (hrun.antitone (hi c hci) hy) hy (hi c hci) hSc hct')
          (by rw [hfr]; exact hFS)
      refine ⟨compatible_of_anc_left hU hfcS hSB, fun hBt hFB hfcB _ hfl => ?_,
        fun htop hcn => ⟨S, hSv, by rwa [← Goldilocks.Store.fcRoot_of_not_contest _ htop hcn],
          Or.inl (by omega)⟩⟩
      by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h
      · have hBS : Anc (tr.HonestBlocksAt H) B S := by
          rcases hSB with h | h
          · have := Healing.h_le_of_store_anc hreach (held_anc_at hrun hnc hd hy hi h hBt)
            omega
          · exact h
        exact ⟨S, hSv, hBS,
          isViable_of_floor_root hjm hSf (held_anc_at hrun hnc hd hy hi hfcS hSy)⟩
      have hcon : ¬ (tr.state y i).fg.Contest := fun hcn => hSf (by
        simp only [Goldilocks.Store.headHeightFloor, hcn, ↓reduceIte]
        have := hcn.1
        omega)
      have hfl' : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
        simp only [Goldilocks.Store.headHeightFloor, hcon, ↓reduceIte]
      obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
      obtain ⟨E, hE, -, hEh, -, D, hD, hDs⟩ := Compose.frame_crossing_source_of hrun' hnc' hf hy
        hsrc (W := X) (j := (tr.state y i).fg.hmax - 1) (by rw [hst]; exact hX) (by omega)
        (by omega) (by rw [hst, hXh]; omega)
      rw [hst] at hE hEh
      have hBP : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
        ⟨y, hy, i, by rw [hst]; exact hBt⟩
      have hDP : D ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := by
        obtain ⟨C, l, -, hCP, hDC⟩ := hD
        exact Compose.anc_mem hDC hCP
      have hBE := held_below_entry hrun' hnc' hy (by rw [hst]; exact hBt)
        (by rw [hst]; exact hE) hDs (compatible_upTo hrun hnc hd hDP hBP (hGB D hD))
        (by rw [hst, hEh]; omega)
      rw [hst] at hBE
      have hBE' := Healing.Growing.honest_anc_of_store_anc_at hd hi hy hBE
      obtain ⟨W, hW, hEW, hhW⟩ := cross D E hD hDs hE (hFB.trans hBE')
      exact ⟨W, hW, hBE'.trans hEW, isViable_of_floor_root hjm (by omega)
        (held_anc_at hrun hnc hd hy hi (hfcB.trans (hBE'.trans hEW)) (hvbt hW))⟩
    · have hsrc' := rowsAbove_mono hsrc
        (show Healing.Growing.HZ tr H g + 1 ≤ ((tr.upTo (tr.time i)).state y i).fg.hj by
          rw [hst]; omega)
      obtain ⟨-, hJm, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
      have hFJ' := Healing.Growing.honest_anc_of_store_anc_at hd hi hy hFJ
      -- `Σ.J` is below a supported member, so below a frozen witness of height `≥ h_j`
      obtain ⟨hJh, -, D, hD, hDs⟩ := Compose.justified_honest_source_of hrun' hnc' hf hy hsrc'
        (by rw [hst]; omega)
      rw [hst] at hDs hJh
      have hJP : (tr.state y i).fg.J ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
        ⟨y, hy, i, by rw [hst]; exact hJm⟩
      obtain ⟨x₀, hx₀, k₀, -, -, hJD, -, -⟩ := Compose.honest_source_entry hrun' hnc' hDs hJP rfl
      have hJD' : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D :=
        (hJD.mono (Compose.fg_tree_subset_honest hx₀ k₀)).mono hsub
      have hJ : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B :=
        compatible_of_anc_left hU hJD' (hGB D hD)
      obtain ⟨C, l, ⟨-, -, x, k, e', hv, hvs, hext⟩, -, hDC⟩ := hD
      have hJC := hJD'.trans (hDC.mono hsub)
      obtain ⟨WJ, hWJ, hCWJ⟩ := frozen hv hvs hext (by rw [hfr]; exact hFJ'.trans hJC)
      have hJWJ := held_anc_at hrun hnc hd hy hi (hJC.trans hCWJ) (hvbt hWJ)
      have hWJv : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
          (tr.state y i).fg.IsViable WJ := fun htop => isViable_of_J_or_gap
        (by have := Healing.h_le_of_store_anc hreach hJWJ; omega) (Or.inr hJWJ)
      refine ⟨?_, fun hBt hFB _ hW₀ _ => ?_, fun htop _ => ⟨WJ, hWJ, hJC.trans hCWJ, hWJv htop⟩⟩
      · rw [Goldilocks.Store.fcRoot]
        split_ifs
        · exact hJ
        · exact compatible_of_anc_left hU hFJ' hJ
      have hBP : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
        ⟨y, hy, i, by rw [hst]; exact hBt⟩
      have hGG : ∀ D D', (∃ C l, Q C l ∧ C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) ∧
          Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D C) →
          (∃ C l, Q C l ∧ C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) ∧
          Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D' C) →
          Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D D' := by
        rintro D D' ⟨C₁, l₁, ⟨hC₁, hl₁, -⟩, hC₁P, hDC₁⟩ ⟨C₂, l₂, ⟨hC₂, hl₂, -⟩, hC₂P, hDC₂⟩
        exact compatible_of_anc_both hUP hDC₁ hDC₂
          (compatible_upTo hrun hnc hd hC₁P hC₂P (hPc C₁ l₁ C₂ l₂ hC₁ hl₁ hC₂ hl₂))
      have hGBP : ∀ D, (∃ C l, Q C l ∧ C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) ∧
          Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D C) →
          Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D B := by
        rintro D ⟨C, l, hQ, hCP, hDC⟩
        exact compatible_upTo hrun hnc hd (Compose.anc_mem hDC hCP) hBP (hGB D ⟨C, l, hQ, hCP, hDC⟩)
      -- a frozen witness above `B` of height `≥ h_max − 1`: `B` itself, or the crossing
      obtain ⟨W, hW, hBW, hWh⟩ : ∃ W ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1),
          Anc (tr.HonestBlocksAt H) B W ∧
            (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ W.root).h := by
        have h := Compose.floor_or_crossing_of hrun' hnc' hf hy hsrc' hGG hGBP
          (by rw [hst]; exact hBt)
        rw [hst] at h
        rcases h with h | ⟨D, E, -, hD, hDs, hE, hBE, hEh, -⟩
        · obtain ⟨W, hW, hBW⟩ := hW₀
          exact ⟨W, hW, hBW, h.trans (Healing.h_le_of_store_anc hreach
            (held_anc_at hrun hnc hd hy hi hBW (hvbt hW)))⟩
        have hBE' := Healing.Growing.honest_anc_of_store_anc_at hd hi hy hBE
        obtain ⟨W, hW, hEW, hhW⟩ := cross D E hD hDs hE (hFB.trans hBE')
        exact ⟨W, hW, hBE'.trans hEW, by omega⟩
      by_cases hgap : (tr.state y i).fg.hj + 1 < (tr.state y i).fg.hmax
      · exact ⟨W, hW, hBW, isViable_of_J_or_gap hWh (Or.inl hgap)⟩
      rcases hJ with hJB | hBJ
      · exact ⟨W, hW, hBW, isViable_of_J_or_gap hWh
          (Or.inr (held_anc_at hrun hnc hd hy hi (hJB.trans hBW) (hvbt hW)))⟩
      · exact ⟨WJ, hWJ, hBJ.trans (hJC.trans hCWJ), hWJv (by omega)⟩
  obtain ⟨hroot, hviab, htopJ⟩ := key
  obtain ⟨-, -, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hFJ' := Healing.Growing.honest_anc_of_store_anc_at hd hi hy hFJ
  have hfin : Compatible (tr.HonestBlocksAt H) ℓ.frame.fcRoot B →
      (∃ D ∈ AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1),
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) →
      B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
        Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := fun hcomp hK => by
    obtain ⟨D, hD, hBD, hDv⟩ := hK
    have h := Healing.Growing.KernelProof.vote_viable_of_root_at hrun hnc hy hc hcomp
      (Or.inl ⟨D, by rw [hes]; exact hD, hBD, hDv⟩)
    rw [hes] at h
    exact h
  rcases hroot with hfB | hBf
  · -- above the analysis root, so above the frame root `Σ.F`
    have hFfc : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y i).fg.fcRoot := by
      rw [Goldilocks.Store.fcRoot]
      split_ifs
      · exact hFJ'
      · exact .refl
    have hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B := by rw [hfr]; exact hFfc.trans hfB
    obtain ⟨x, k, e', hv, hs', hext⟩ := hw
    obtain ⟨W, hW, hBW⟩ := frozen hv hs'.le hext hFB
    have hBt := AC.frame_mem_of_between sp hU hΦ hΦU hW.1 hBW hFB
    rw [hfr] at hBt
    refine hfin (Or.inl (by rw [hfr]; exact hFfc.trans hfB)) ?_
    by_cases hfl : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
    · have hBW' := held_anc_at hrun hnc hd hy hi hBW (hvbt hW)
      exact ⟨W, hW, hBW, isViable_of_floor_root hjm
        (hfl.trans (Healing.h_le_of_store_anc hreach hBW'))
        (held_anc_at hrun hnc hd hy hi (hfB.trans hBW) (hvbt hW))⟩
    · exact hviab hBt.1 hFB hfB ⟨W, hW, hBW⟩ hfl
  · -- below the analysis root: below `Σ.F`, or strictly between `Σ.F` and a clean top `Σ.J`
    by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
        ¬ (tr.state y i).fg.Contest
    · rw [Goldilocks.Store.fcRoot_of_not_contest _ hk.1 hk.2] at hBf
      obtain ⟨D, hD, hJD, hDv⟩ := htopJ hk.1 hk.2
      exact hfin (by rw [hfr]; exact compatible_of_anc_both hU hFJ' hBf (Or.inl .refl))
        ⟨D, hD, hBf.trans hJD, hDv⟩
    · rw [Goldilocks.Store.fcRoot, ite_eq_right hk] at hBf
      exact Or.inr (by rw [hfr]; exact hBf)

end Consensus.Goldilocks.Compose.Growing

end
