module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedSteps
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the served head (S4) and the record step (G3)

The facts the Service milestone reads (`ServedFacts`, in
`Lemmas/Compose/Service/Sleepy`), from `SleepyInvariant`:

* **The record step** (`record_step`, G3, at every honest cut): a record write takes an origin
  `C` of the frame, compatible with the old record (genesis or an origin, in the node's tree);
  it keeps the record when `C` is below it in the frame, and otherwise the old record is below
  `C` (below `Σ.F ⪯ C` when it left the frame). Restarts keep the record.
* **The served head** (`served_head_support`, G1, G2, at a cut after the update of slot
  `slot(t) − 2` or `slot(t) − 1` with no restart since, awake and joined): the anchor (the
  deepest of the live lock blocks and `fc_root`, all on the origin chain) is compatible with the
  record `R`. If `R` was
  written by an optimistic check of the current slot, or of the previous one before its
  `t_s + 2Δ`, its fast lock is still live at `R` (full viability keeps it there), so `R ⪯` the
  anchor. Otherwise `R`'s label is below the latest view's slot: every honest vote of that slot
  extends `R` (S2), the more than `f` cast by the validators awake and joined at its `t + Δ`
  reach the served node by its tick at `t_l + 2Δ` and are resolved (their heads are relayed,
  extending `Σ.F ⪯ R`), and the node keeps them (joined at `t`, it has not restarted since
  `t_{σ−1}`; the update clause is not needed), and only faulty seats remain, so the supporters
  are a strict majority of the voters; `R` is fully viable (S3). Which case holds is read off
  how the record was last written (`record_writer`: genesis, a result, or an optimistic
  selection whose fast lock every later call keeps while `R` stays viable and the slot at most
  one later).
* **The head at a read** (`read_head_support`, for R.1): the same, for the state before a cut `i`
  read at a time `t` with every earlier cut at or before `t` and cut `i` at or after it, the node
  awake and joined at `t`. The votes and heads the latest view at `t` needs arrive before
  `t_l + 2Δ ≤ t`, so at cuts before `i`; when the node's tick at `t` is at a cut `≥ i`, the node
  makes no call before it at `t`, and the read is the one before the tick's cut.

The record step and the head at a read hold up to a horizon `b` too (`record_step_upTo`,
`read_head_support_upTo`), from `SleepyInvariantUpTo` under the prefix premises up to `b`: a read
at `t ≤ b` needs `Sync` for the sends up to `t − Δ` and `f < h_t` at `t_l + Δ ≤ t`.

The chain-generic steps are in `Compose/Sleepy/ServedSteps`, imported privately, which the
growing-fault forms share; the facts on the latest view's votes are in `Compose/Sleepy/ServedBase`,
imported publicly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **G3, the record step**: at every cut of an honest node, the record moves to a descendant
(inside the honest blocks). -/
theorem record_step (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
  record_step_of hrun hnc hy i
    (fun _ _ hX hY hXc hYc =>
      OnOriginChain.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc)
    ⟨C, hC, hCr, onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i).1 fun C s _ hO => onOriginChain_iff.2 (Or.inr
      ⟨C, s, hO.elim (Origin.of_result hy) (Origin.of_optimistic hy), .refl⟩)

/-- **G3 up to `b`, the record step**: at every cut of an honest node at a time `≤ b` (with the
earlier ones), the record moves to a descendant (inside the honest blocks). -/
theorem record_step_upTo {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hi : ∀ k ≤ i, tr.time k ≤ b) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' :=
  have hi' : ∀ k < i, tr.time k ≤ b := fun k hk => hi k hk.le
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i hi'
  record_step_of hrun hnc hy i
    (fun _ _ hX hY hXc hYc =>
      OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc)
    ⟨C, hC, hCr, onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i hi').1 fun C s CV hO => onOriginChainWithin_iff.2 (Or.inr
      ⟨C, s, originWithin_iff.2 ⟨y, hy, i, CV, hi i le_rfl, hO⟩, .refl⟩)

/-- A cut of an honest node awake and joined at its time is read at its time. -/
private theorem readAt_self (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hc : tr.IsCall y i) (hw : tr.awake y (tr.time i)) (hj : tr.JoinedAt y (tr.time i)) :
    ReadAtCut proposer dg tr y i (tr.time i) :=
  ⟨hrun.time_nonneg i, fun _ hk => hrun.time_mono hk.le, le_rfl,
    fun _ hk => not_lt.1 fun hik => not_before_tick hrun hy hc hj hk hik, hw, hj⟩

private abbrev ReadInv (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop)
    (O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (y : Fin sp.n) (i : Nat) (t : Time) :=
  ReadInvWith tr H Ch O y i t
    (SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) 0 (t - sp.Δ) tr.projAC)

private theorem ReadInv.service {Ch O y i t} (h : ReadInv tr H Ch O y i t) :
    ReadInvWith tr H Ch O y i t (ReadSyncOrService tr H t) :=
  { h with sync := Or.inl h.sync }

/-- `ReadInv` from the full invariant under `Sleepy`. -/
private theorem ReadInv.of_full (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (t : Time) : ReadInv tr H (OnOriginChain tr H) (Origin tr H) y i t :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
  { compat := fun _ _ hX hY hXc hYc =>
      OnOriginChain.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc
    anc := fun _ _ hA hAB h => OnOriginChain.of_anc hrun hnc hA hAB h
    record := ⟨C, hC, hCr, onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    locks := hinv.locks y hy i
    caches := hinv.caches y hy i
    origin := fun _ _ h => h.origin
    viable := fun m _ C s hO hC => hinv.viable y hy m C s hO hC
    vote_extends := fun C s hO x hx k _ e hv hs => hinv.vote_extends C s hO x hx k e hv hs
    sync := syncAC_of_sleepy hrun hsl le_rfl
    awake := fun s _ _ => faults_lt_awake_joined hsl s }

private theorem ReadInvWith.of_before {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hi : ∀ k < i, tr.time k ≤ b) {t : Time}
    (ht : t ≤ b) (hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ t → tr.FaultBound H (sp.ts s + sp.Δ)) :
    ReadInvWith tr H (fun B => OnOriginChainWithin tr H B b)
      (fun C s => OriginWithin tr H C s b) y i t (ReadSyncOrService tr H t) :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i hi
  { compat := fun _ _ hX hY hXc hYc =>
      OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc
    anc := fun _ _ hA hAB h => OnOriginChainWithin.of_anc hrun hnc hA hAB h
    record := ⟨C, hC, hCr,
      onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    locks := hinv.locks y hy i hi
    caches := hinv.caches y hy i hi
    origin := fun _ _ h => h.within hi
    viable := fun m hm C s hO hC => hinv.viable y hy m (fun k hk => hi k (by omega)) C s hO hC
    vote_extends := fun C s hO x hx k hk e hv hs =>
      hinv.vote_extends C s hO x hx k e hv (hi k hk) hs
    sync := Or.inr {
      message := fun x hx k m hm h0 z hz j ℓ hc hd hj =>
        hsync.message x hx k m hm h0 z hz j ℓ hc (hd.trans ht) hj
      relay := fun x hx k B hB h0 z hz j ℓ hc hd hj ha =>
        hsync.relay x hx k B hB h0 z hz j ℓ hc (hd.trans ht) hj ha }
    awake := fun s h _ => hfb s h }

private theorem latest_majority_of_target_votes_at_read
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    (hrd : ReadAtCut proposer dg tr y i t)
    {a : Time} (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac
      (Node.frame (tr.state y i)) t).2) (ha : a ≤ sp.ts L)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
          t).2 R).ncard := by
  set Vt := SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
    t).1.votes
  set Sp := SA.supporters (Node.frame (tr.state y i))
    (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
    (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R
  have hHV : Vt ∩ H ⊆ Sp := by
    intro w hw
    apply latest_honest_supporter_of_target_votes hrun hnc hy hR hL hvotes ?_ w hw.1 hw.2
    intro z hz q e hv hs Hd hHd hHdr hF
    exact honest_head_in_frame_at_read hrun hnc (Or.inr ⟨a, hsync, hcatch, by rw [← hL]; exact ha⟩)
      hy hrd hL hz hv hs hHd hHdr hF
  have hSX : {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)} ⊆
      Vt ∩ H := fun x hx =>
    ⟨latest_awake_voter hrun hnc (Or.inr ⟨a, hsync, by rw [← hL]; exact ha⟩)
      hy hrd hL hx.1 hx.2.1 hx.2.2, hx.1⟩
  have h₁ := Set.ncard_le_ncard (hSX.trans hHV) (Set.toFinite _)
  have h₂ := Set.ncard_le_ncard hHV (Set.toFinite _)
  have h₃ : Vt.ncard ≤ (Vt ∩ H).ncard + Hᶜ.ncard := by
    refine (Set.ncard_le_ncard (fun w hw => ?_) (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    by_cases hwH : w ∈ H
    · exact Or.inl ⟨hw, hwH⟩
    · exact Or.inr hwH
  change Vt.ncard < 2 * Sp.ncard
  omega

/-- Scoped target support at an arbitrary read, including a read before the node's tick
at the same clock. Direct votes are required through that clock, not just the initial cut. -/
theorem read_majority_of_target_votes
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    {a : Time} (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e,
      SA.VoteAt tr.projAC z q e → e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard := by
  by_cases hT : ∃ j, i ≤ j ∧ tr.TickAt proposer dg y j t
  · obtain ⟨j, hij, hT⟩ := hT
    obtain ⟨-, -, -, htj⟩ := tickAt_acCall hT
    have hst : ∀ m, i ≤ m → m ≤ j → tr.state y m = tr.state y i := by
      intro m him
      induction m, him using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ m him ih =>
        intro hm
        have htm : tr.time m = t := le_antisymm
          (by rw [← htj]; exact hrun.time_mono (by omega)) (hti.trans (hrun.time_mono him))
        rw [tr.state_succ_of_not fun c hc => not_before_tick hrun hy ⟨c, hc⟩
          (by rw [htm]; exact hj) (by rw [htm]; exact hT) (by omega), ih (by omega)]
    have hs := hst j hij le_rfl
    have hlej : ∀ q < j, tr.time q ≤ t := fun q hq => htj ▸ hrun.time_mono hq.le
    have hrd : ReadAtCut proposer dg tr y j t :=
      ⟨ht0, hlej, htj.ge, fun q hq => (hrun.tick_unique y hy q j t hq hT).le, hw, hj⟩
    have h := latest_majority_of_target_votes_at_read hrun hnc hy hrd hsync hcatch
      (by rw [hs]; exact hL) ha (by rw [hs]; exact hR)
      (fun z hz q hq => hvotes z hz q (hlej q hq)) hfault
    rwa [hs] at h
  · exact latest_majority_of_target_votes_at_read hrun hnc hy
      ⟨ht0, hle, hti, fun q hq => not_lt.1 fun hiq => hT ⟨q, hiq.le, hq⟩, hw, hj⟩
      hsync hcatch hL ha hR (fun z hz q hq => hvotes z hz q (hle q hq)) hfault

/-- Post-GST head support for the actual record. Only the current view's votes and
participation are needed; historical record recency and anchor compatibility are supplied
separately. The live-lock arm requires no majority or service before GST. -/
theorem anchor_compatible_of_live_candidates
    {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    {t : Time} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcomp : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}, Compatible Φ.tree X R) :
    Compatible Φ.tree (SA.getAnchor sp A Φ t) R := by
  have hsub : SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.mp hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hsub ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : SA.getAnchor sp A Φ t = D := by simp only [SA.getAnchor, hD, Option.getD_some]
  rw [ha]
  exact hcomp D (SA.deepest_mem hD).1

/-- **G1, G2 at a read** (for R.1): the state of an honest node before cut `i`, read at a time
`t` at or after every cut before `i` and at or before cut `i`, the node awake and joined at `t`
(when `t ≥ 0`): the anchor at `t` is compatible with the record's block `R`, and `R` is at or
below it, or viable with a strict majority of the latest view's voters at `t` as supporters. When
the node's tick at `t` is at a cut `≥ i`, it makes no call in between (the tick is its first event
at `t`), so the read is the one before the tick's cut. -/
theorem read_head_support (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {t : Time} (hle : ∀ k < i, tr.time k ≤ t) (hti : t ≤ tr.time i)
    (hwj : 0 ≤ t → tr.awake y t ∧ tr.JoinedAt y t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : RecordAt tr y i R) :
    Compatible (Node.frame (tr.state y i)).tree
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
              t).1.votes).ncard <
            2 * (SA.supporters (Node.frame (tr.state y i))
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
              R).ncard)) :=
  read_head_support_of hrun hnc hy
    (fun m _ _ => (ReadInv.of_full hinv hrun hnc hsl hy m t).service) hle hti hwj hR

/-- G1, G2 with recipient service bounded by the read time, not the next cut's time.
Only the fault bounds at `t_s + Δ ≤ t` are needed for the latest-view majority. -/
theorem read_head_support_before {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (htb : t ≤ b)
    (hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ t → tr.FaultBound H (sp.ts s + sp.Δ))
    (hle : ∀ k < i, tr.time k ≤ t) (hti : t ≤ tr.time i)
    (hwj : 0 ≤ t → tr.awake y t ∧ tr.JoinedAt y t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : RecordAt tr y i R) :
    Compatible (Node.frame (tr.state y i)).tree
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
              t).1.votes).ncard <
            2 * (SA.supporters (Node.frame (tr.state y i))
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
              R).ncard)) :=
  read_head_support_of hrun hnc hy
    (fun _ hm _ => ReadInvWith.of_before hinv hrun hnc hsync hy
      (fun k hk => (hm k hk).trans htb) htb hfb) hle hti hwj hR

/-- **G1, G2 at a served cut**: at a cut of an honest node awake and joined at its time that has
run the update of slot `slot(t) − 2` or `slot(t) − 1` with no restart since (A1.6's condition,
and A1.7's in the slot after the proposal's), the record's block has `HeadSupport`. -/
theorem served_head_support (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hc : tr.IsCall y i) (hw : tr.awake y (tr.time i)) (hj : tr.JoinedAt y (tr.time i))
    {s' : Nat} (_hs' : sp.slot (tr.time i) ≤ s' + 2) (_hu : UpdatedNoRestart tr y i s')
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R) :
    HeadSupport tr y i R :=
  -- the update clause is not needed here: joining at `t` already excludes the restarts after the
  -- latest view's slot started, which would clear the pools
  have h := head_support_at hrun hnc hy (ReadInv.of_full hinv hrun hnc hsl hy i (tr.time i)).service
    (fun _ hk => hrun.time_mono hk.le) (fun _ => readAt_self hrun hy hc hw hj) hR
  ⟨h.1, h.2⟩

/-- **The served-cut facts under `Sleepy`** (`ServedFacts`, the target of the Service
milestone's served-cut facts). -/
theorem sleepy_served_facts (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hs : ServedAt tr y i)
    (hstock : sp.committeeSize = sp.n) :
    ServedFacts tr H y i :=
  have hinv := sleepy_invariant hrun hnc hsl hstock
  have ⟨hc, hj, _, hs', hu⟩ := hs
  have hw := hrun.awake_of_call y hy i hc
  ⟨fun _ hR => served_head_support hinv hrun hnc hsl hy hc hw hj hs'.ge hu hR,
    record_step hinv hrun hnc hy i⟩

end Consensus.Goldilocks.Compose

end
