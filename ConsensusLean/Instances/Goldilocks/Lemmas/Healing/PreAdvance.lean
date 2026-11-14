module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Pre-advance frame windows

`FrameWindow` fixes explicit F-independent frame data on a finite interval: the honest
head-height floor and the kind of the justified block `J`. From it and finite service, without
any reset premise: the window's `fc_root` monotonicity, floor ancestors in the frame, persistence
of viable heads, root and old-lock witnesses from earlier calls, the classification of honest vote
heads, and the fault bound from the service. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- An update of label `l` at `t_l + 6Δ` precedes the vote freeze of every slot `s ≥ l + 2`. -/
private theorem ts_add_six_lt_freeze {l : Int} {s : Nat} (h : l + 2 ≤ (s : Int)) :
    sp.ts l + 6 * sp.Δ < SA.freeze sp s := by
  have hΔ := sp.toParams.hΔ
  have := (SA.ts_le_iff sp).mpr (show l + 1 ≤ (s : Int) - 1 by omega)
  unfold SA.freeze
  simp only [SA.SAParams.ts] at this ⊢
  linarith

/-- Explicit F-independent frame data on a finite interval. F itself need not agree. -/
structure FrameWindow (lo hi : Time) (floor : Nat) (kindJ : Prop)
    (J : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  floor_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.headHeightFloor = floor
  kind_iff : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest) ↔ kindJ)
  root_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi → kindJ →
    (tr.state y i).fg.J = J

/-- On a `FrameWindow` the fork-choice root is constant in kind J and follows finalized
monotonicity otherwise (including Contest). -/
theorem FrameWindow.fcRoot_mono {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {a i : Nat} (hai : a ≤ i) (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi) :
    Anc (tr.HonestBlocks H) (tr.state y a).fg.fcRoot (tr.state y i).fg.fcRoot := by
  classical
  have htime := hrun.time_mono hai
  by_cases hk : kindJ
  · have hka := (hframe.kind_iff y hy a halo (htime.trans hihi)).mpr hk
    have hki := (hframe.kind_iff y hy i (halo.trans htime) hihi).mpr hk
    change Anc _ (if _ then _ else _) (if _ then _ else _)
    rw [ite_eq_left hka, ite_eq_left hki]
    rw [hframe.root_eq y hy a halo (htime.trans hihi) hk,
      hframe.root_eq y hy i (halo.trans htime) hihi hk]
    exact .refl
  · have hka := (hframe.kind_iff y hy a halo (htime.trans hihi)).not.mpr hk
    have hki := (hframe.kind_iff y hy i (halo.trans htime) hihi).not.mpr hk
    change Anc _ (if _ then _ else _) (if _ then _ else _)
    rw [ite_eq_right hka, ite_eq_right hki]
    exact run_F_mono hrun.toLocalRun hy hai

/-- An accepted descendant puts a floor-viable source in the receiver's frame, even when
the source was originally witnessed at a later cut. -/
theorem floor_ancestor_mem_frame (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {j c : Nat}
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : (tr.state y j).fg.headHeightFloor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 →
      ¬(tr.state y j).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y j).fg.J X)
    (hW : W ∈ (tr.state y j).fg.tree) (hXW : Anc (tr.HonestBlocks H) X W) :
    X ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).Anc (Node.frame (tr.state y j)).fcRoot X ∧
      X ∈ (Node.frame (tr.state y j)).viableHeads := by
  have hXt := mem_of_honest_anc hrun hnc hy hXW hW
  have hh' : (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ X.root).h := by
    rw [← σ_eq_honest hrun hnc hz hy hX hXt]
    exact hh
  obtain ⟨-, hframe, hroot, -, hv⟩ := viable_head_of_floor hrun hnc hf hy hXt hh'
    (fun hm hc => Compose.honest_held_anc hrun hnc hy (hJ hm hc) hXt)
  have hΦ := (Goldilocks.Store.frame_realization _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy j)).1
  have hsub : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H :=
    fun B hB => ⟨y, hy, j, hB.1⟩
  refine ⟨hframe, SA.anc_tree_of_anc_U
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hΦ hsub hΦ.fcRoot_mem
    (hroot.mono (fun B hB => ⟨y, hy, j, hB⟩)) hframe, hv⟩

/-- A write-frame viable head remains a viable head at every later cut in the `FrameWindow`.
This is the writer-local persistence needed by `FrameWindow.vote_head_classification`, not
cross-node delivery. -/
theorem FrameWindow.viableHead_persists {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y a ell)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    Q ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  have htime := hrun.time_mono hai
  rw [Compose.frame_of_projAC hrun hy hc] at hv
  have hQa : Q ∈ (tr.state y a).fg.tree := hv.1
  apply floor_ancestor_mem_frame hrun hnc hf hy hy hQa
  · rw [hframe.floor_eq y hy i (halo.trans htime) hihi,
      ← hframe.floor_eq y hy a halo (htime.trans hihi)]
    exact hv.2.2.2
  · intro hm hcont
    have hk := (hframe.kind_iff y hy i (halo.trans htime) hihi).mp ⟨hm, hcont⟩
    have hka := (hframe.kind_iff y hy a halo (htime.trans hihi)).mpr hk
    have hroot : (tr.state y a).fg.fcRoot = (tr.state y a).fg.J := ite_eq_left hka
    rw [hframe.root_eq y hy i (halo.trans htime) hihi hk,
      ← hframe.root_eq y hy a halo (htime.trans hihi) hk, ← hroot]
    exact hv.2.2.1.mono (fun B hB => ⟨y, hy, a, hB⟩)
  · exact Compose.tree_mono hrun.toLocalRun hy hai hQa
  · exact Relation.ReflTransGen.refl

/-- H-wit: an earlier action frame supplies a frozen viable descendant of the
kind-F root. The earlier head is not assumed viable: use the store's hmax witness. -/
theorem FrameWindow.root_witness_of_earlier_call {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) (hnk : ¬kindJ)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode sp ro)}
    (ha : tr.projAC.CallAt y a ell₀) {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < SA.freeze sp e.msg.slot)
    (hgf : gbar g < SA.freeze sp e.msg.slot) :
    ∃ Q ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have htime := hrun.time_mono hai
  obtain ⟨-, -, -, -, -, ⟨Q, hQ, hQh⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy a)
  obtain ⟨hQt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hQ
    ((Goldilocks.Store.headHeightFloor_bounds (tr.state y a).fg).2.trans_eq hQh.symm)
    (fun hm hcon => (hnk ((hframe.kind_iff y hy a halo (htime.trans hihi)).mp
      ⟨hm, hcon⟩)).elim) hQ Relation.ReflTransGen.refl
  rw [← Compose.frame_of_projAC hrun hy ha] at hQt hv
  obtain ⟨hQi, hrooti, hvi⟩ :=
    hframe.viableHead_persists hrun hnc hf hy hai halo hihi ha hv
  rw [← Compose.frame_of_projAC hrun hy hc.1] at hQi hrooti hvi
  refine ⟨Q, ⟨hQi, Or.inl ?_⟩, hvi, hrooti⟩
  apply SA.readPoint_blockStamp_lt_of_earlier_frame hr hy ha hc hQt hQi hat
  intro r _ hrs
  exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf

/-- The strict-above-root stored-lock core of `FrameWindow.vote_head_classification`. Old
labels force the write into the `FrameWindow`
and before the vote freeze. The below-write-root alternative is impossible by root
monotonicity; the viable witness remains viable and frozen at the writer's vote.
Current-slot optimistic locks and the root itself are deliberately outside this core. -/
theorem FrameWindow.old_lock_witness {s₀ floor : Nat} {hi : Time}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hgf : gbar g < SA.freeze sp e.msg.slot)
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hlabel : s₀ ≤ l.slot) (hold : l.slot < e.msg.slot)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    ∃ a < i, ∃ ell₀ D Q,
      tr.projAC.CallAt y a ell₀ ∧ sp.ts s₀ ≤ tr.time a ∧
      tr.time a < SA.freeze sp e.msg.slot ∧
      ((∃ CV, SA.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        ∃ ell', SA.UpdateAt tr.projAC y a l.slot ell') ∧
      Q ∈ ell₀.frame.viableHeads ∧ Anc (tr.HonestBlocks H) L Q ∧
      Q ∈ ell.frame.viableHeads ∧
      Q ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have htvote := SA.vote_time_le hr hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at htvote
  have hslot : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hc).2.1
  rw [← hslot] at htvote
  obtain ⟨a, hai, ell₀, D, A, ha, hD, hAeq, ho, ⟨M, hM, hMr, hMA⟩, hcase⟩ :=
    SA.lock_write_witness hr hy hl
  have hPhiU := (SA.frameIn_of_callAt hr hy hc.1).2
  have hPhi₀ := SA.frameIn_of_callAt hr hy ha
  obtain rfl : M = L := hr.coherent.1 hM (hPhiU hL) (hMr.trans hLr.symm)
  have htime : sp.ts s₀ ≤ tr.time a ∧ tr.time a < SA.freeze sp e.msg.slot := by
    rcases ho with ⟨CV, ell', B, hp, hs, hsel, -⟩ | ⟨ell', hu⟩
    · have hlo := (SA.ts_le_iff_le_slot sp (hr.time_nonneg a) (s₀ : Int)).mpr
        (by rw [hs]; exact_mod_cast hlabel)
      have hlt : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel with hn
        exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (hs ▸ ht))))
      have hts := (SA.ts_le_iff sp).mpr (show (l.slot : Int) ≤ (e.msg.slot : Int) - 1 by omega)
      refine ⟨hlo, ?_⟩
      unfold SA.freeze
      exact hlt.trans_le
        (add_le_add hts (mul_le_mul_of_nonneg_right (by norm_num) sp.toParams.hΔ.le))
    · have ht := hu.2.2.1
      change tr.time a = _ at ht
      have hts₀ := (SA.ts_le_iff sp).mpr (show (s₀ : Int) ≤ l.slot by exact_mod_cast hlabel)
      have hlabel' : l.slot + 2 ≤ e.msg.slot :=
        Compose.ts_add_two_le ((ht.symm.trans_le (hrun.time_mono hai.le)).trans htvote)
      exact ⟨hts₀.trans ((le_add_of_nonneg_right
          (mul_nonneg (by norm_num) sp.toParams.hΔ.le)).trans_eq ht.symm),
        ht.trans_lt (ts_add_six_lt_freeze (by exact_mod_cast hlabel'))⟩
  rcases hcase with hbelow | ⟨Q, hQ, hv, hAQ⟩
  · exfalso
    apply hstrict
    have hroot := hframe.fcRoot_mono hrun hy hai.le htime.1 hihi
    change Anc _ (Node.frame (tr.state y a)).fcRoot (Node.frame (tr.state y i)).fcRoot at hroot
    rw [← Compose.frame_of_projAC hrun hy ha,
      ← Compose.frame_of_projAC hrun hy hc.1] at hroot
    exact hMA.trans ((hbelow.mono hPhi₀.2).trans hroot)
  · obtain ⟨hQt, -, hvQ⟩ := hframe.viableHead_persists hrun hnc hf hy hai.le htime.1 hihi ha hv
    rw [← Compose.frame_of_projAC hrun hy hc.1] at hQt hvQ
    refine ⟨a, hai, ell₀, D, Q, ha, htime.1, htime.2, ho, hv,
      hMA.trans (hAQ.mono hPhi₀.2), hvQ, hQt, Or.inl ?_⟩
    apply SA.readPoint_blockStamp_lt_of_earlier_frame hr hy ha hc hQ hQt htime.2
    intro r _ hrs
    exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf

/-- The vote-head classification for an older live read-point lock strictly above the current
root. Liveness and the warmup bound derive the label lower bound; no write-cut or witness premise
is supplied by the caller. The result is directly consumable by
`FrameWindow.vote_head_classification`. -/
theorem FrameWindow.live_old_lock_witness {s₀ floor : Nat} {hi : Time}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hgf : gbar g < SA.freeze sp e.msg.slot)
    {l : SA.Lock} (hl : l ∈ SA.liveLocks sp e.readPoint.locks ell.frame (tr.time i))
    (hold : l.slot < e.msg.slot)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    ∃ Q ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc L Q := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hs := (SA.castAt_spec hr hy hc).2.1
  change e.msg.slot = sp.slot (tr.time i) at hs
  obtain ⟨l₀, hl₀, B, hB, hBr, hlive, heq⟩ := hl
  -- live ⇒ recent: the read point's locks expire by `slot + k`
  have hrecent : sp.slot (tr.time i) ≤ l₀.slot + sp.k :=
    hlive.trans ((SA.castAt_readPoint_locksWF hr hy hc).cap hl₀)
  have hsl : l.slot = l₀.slot := by simpa only using congrArg SA.Lock.slot heq
  have hne : l₀.slot ≠ sp.slot (tr.time i) := by rw [← hs]; omega
  obtain ⟨l₁, hl₁, hs₁, C, hC, hCr, B', hB', hB'r, hBC⟩ :=
    SA.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time i); rwa [← hs]) l₀ hl₀ hne
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hBB : B' = B := hPhi.1.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [hBB] at hBC
  have hLB : ell.frame.Anc L B := by
    have he : L = ell.frame.viableAncestor B := hPhi.1.coherent.1 hL
      (SA.viableAncestor_anc hPhi.1 hB).1 (hLr.trans (congrArg SA.Lock.block heq))
    rw [he]; exact (SA.viableAncestor_anc hPhi.1 hB).2
  have hlabel : s₀ ≤ l₁.slot := by rw [← hs₁, ← hsl]; rw [← hs] at hrecent; omega
  have hstrictC : ¬ Anc (tr.HonestBlocks H) C ell.frame.fcRoot := by
    intro h
    exact hstrict ((Anc.mono hPhi.2 (hLB.trans hBC)).trans h)
  obtain ⟨a, hai, ell₀, D, Q, -, -, -, -, -, hCQ, hvQ, hQv⟩ :=
    hframe.old_lock_witness hrun hnc hf hnr hy hc hihi hgf hl₁ hlabel
      (by rw [← hs₁, ← hsl]; exact hold) hC hCr hstrictC
  refine ⟨Q, hQv, hvQ, ?_⟩
  exact hLB.trans (hBC.trans (SA.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hC hCQ hQv.1))

/-- Finite service supplies H-wit's earlier action cut from the writer's actual
prior-slot vote, without assuming anything about that vote's head. -/
theorem prior_vote_call_before_freeze
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hpos : 0 < e.msg.slot)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((e.msg.slot - 1 : Nat) : Int))
    (hmb : sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ ≤ b)
    {s₀ : Nat} (hs₀ : s₀ ≤ e.msg.slot - 1) :
    ∃ a ≤ i, ∃ ell₀, tr.projAC.CallAt y a ell₀ ∧
      sp.ts s₀ ≤ tr.time a ∧ tr.time a < SA.freeze sp e.msg.slot := by
  have hr := hS.run.localRun
  have hcast : ((e.msg.slot - 1 : Nat) : Int) = (e.msg.slot : Int) - 1 := by omega
  obtain ⟨a, e₀, ⟨ell₀, ha, he⟩, hs, ht⟩ :=
    SA.honest_votes_in_slot_before hS (m := e.msg.slot - 1) hm hmb (fun x hx r _ hrs => by
      have hb := hnr x hx r (Compose.projAC_restartAt.mp hrs)
      rw [hcast, SA.ts_sub_one]
      exact hb.trans (le_sub_iff_add_le.mpr (hcast ▸ hm))) y hy
  have hslot := (SA.castAt_spec hr hy ⟨ha, he⟩).2.1
  have hislot := (SA.castAt_spec hr hy hc).2.1
  have hti := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) (e.msg.slot : Int)).mpr
    (by rw [hislot])
  change sp.ts (e.msg.slot : Int) ≤ tr.time i at hti
  have hDelta := sp.toParams.hΔ
  have hlt : tr.time a < tr.time i := by
    change tr.time a ≤ _ at ht
    simp only [SA.SAParams.ts] at ht hti
    rw [hcast] at ht
    linarith
  refine ⟨a, (le_of_not_gt fun h => hlt.not_ge (hr.time_mono h.le)), ell₀, ha, ?_, ?_⟩
  · apply (SA.ts_le_iff_le_slot sp (hr.time_nonneg a) _).mpr
    rw [← hslot, hs]
    exact_mod_cast hs₀
  · change tr.time a ≤ _ at ht
    unfold SA.freeze
    have heq : (e.msg.slot : Int) - 1 = ((e.msg.slot - 1 : Nat) : Int) := by omega
    rw [heq]
    exact ht.trans_lt (add_lt_add_of_le_of_lt le_rfl (lt_mul_of_one_lt_left hDelta (by norm_num)))

/-- Writer-local vote-head classification at a vote, with an explicit earlier action cut for
H-wit.
The head is viable in its walked domain (the vote domain), the common kind-J root, or the anchor
of a current-slot optimistic lock. No viability of a counted vote head is assumed. -/
theorem FrameWindow.vote_head_classification {s₀ floor : Nat} {hi : Time}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i a : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode sp ro)}
    (ha : tr.projAC.CallAt y a ell₀) {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    (halo : sp.ts s₀ ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < SA.freeze sp e.msg.slot)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hgf : gbar g < SA.freeze sp e.msg.slot) :
    ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      ((Hd ∈ SA.voteDomain sp e.readPoint ell.frame e.msg.slot ∧
        Hd ∈ ell.frame.viableHeads) ∨
      (kindJ ∧ Hd = J) ∨
      (Hd = SA.getAnchor sp e.readPoint ell.frame (tr.time i) ∧
        ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
        ∃ a ≤ i, ∃ D CV, SA.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
          sp.ts e.msg.slot ≤ tr.time a ∧
          ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧
            ell.frame.Anc Hd L ∧ Anc (tr.HonestBlocks H) L D)) := by
  classical
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  let A := SA.getAnchor sp e.readPoint ell.frame (tr.time i)
  let S := SA.voteDomain sp e.readPoint ell.frame e.msg.slot
  let Hd := SA.getHead sp e.readPoint ell.frame (tr.time i) (ell.frame.viableTree S)
    (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)
  obtain ⟨hAt, hanc⟩ := SA.anc_getAnchor hPhi.1
    (SA.castAt_liveLockBlocks_chain hr (fun _ => SA.voteStart_initial _) hy hc _)
  have hroot := hanc _ (Or.inr rfl)
  have hwalk := SA.getHead_viable_dichotomy hPhi.1 (fun _ h => SA.voteDomain_subset_tree h)
    (SA.voteDomain_anc hr hy hc) e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) hAt hroot
  refine ⟨Hd, SA.getHead_mem hPhi.1 (fun _ h => SA.voteDomain_subset_tree h.1) _ _ _ _,
    (SA.castAt_spec hr hy hc).2.2.2.symm, ?_⟩
  by_cases hd : ∃ Q ∈ S, Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc A Q
  · exact Or.inl (hwalk.1 hd)
  have hHd : Hd = A := hwalk.2 hd
  apply Or.inr
  by_cases heq : A = ell.frame.fcRoot
  · by_cases hk : kindJ
    · apply Or.inl
      refine ⟨hk, hHd.trans (heq.trans ?_)⟩
      rw [Compose.frame_of_projAC hrun hy hc.1]
      have hlo := halo.trans (hrun.time_mono hai)
      have hki := (hframe.kind_iff y hy i hlo hihi).mpr hk
      change (if _ then _ else _) = J
      rw [ite_eq_left hki, hframe.root_eq y hy i hlo hihi hk]
    · exfalso
      obtain ⟨Q, hQ, hv, hrQ⟩ :=
        hframe.root_witness_of_earlier_call hrun hnc hf hk hnr hy hai ha hc halo hihi hat hgf
      exact hd ⟨Q, SA.voterBlockTree_subset_voteDomain hQ, hv, heq ▸ hrQ⟩
  have hAm : A ∈ SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) := by
    unfold A SA.getAnchor
    cases hh : SA.deepest ell.frame
        (SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) ∪ {ell.frame.fcRoot}) with
    | none => exact (heq (by unfold A SA.getAnchor; rw [hh]; rfl)).elim
    | some B =>
      rcases (SA.deepest_mem hh).1 with h | h
      · exact h
      · exact (heq (by unfold A SA.getAnchor; rw [hh]; exact h)).elim
  obtain ⟨hA, l, hl, hlr⟩ := hAm
  have hstrict : ¬ Anc (tr.HonestBlocks H) A ell.frame.fcRoot := by
    intro h
    apply heq
    exact Anc.antisymm hr.coherent h (hroot.mono hPhi.2)
  by_cases hold : l.slot < e.msg.slot
  · exfalso
    obtain ⟨Q, hQ, hv, hAQ⟩ := hframe.live_old_lock_witness hrun hnc hf hnr hy hc hihi
      hwarm hpos hgf hl hold hA hlr.symm hstrict
    exact hd ⟨Q, SA.voterBlockTree_subset_voteDomain hQ, hv, hAQ⟩
  obtain ⟨l₀, hl₀, B, hB, hBr, -, hleq⟩ := hl
  have hsl : l.slot = l₀.slot := by simpa only using congrArg SA.Lock.slot hleq
  obtain ⟨hs, c, hci, D, CV, ho, ht, L, hL, hLr, hLD⟩ :=
    SA.current_lock_write_readPoint hr hy hc hpos hl₀ (by omega)
  have hBL : B = L := hr.coherent.1 (hPhi.2 hB) hL (hBr.trans hLr.symm)
  refine Or.inr ⟨hHd, l₀, hl₀, hs, c, hci, D, CV, ho, ht, L, hL, hLr, ?_, hLD⟩
  have hAB : A = ell.frame.viableAncestor B := hPhi.1.coherent.1 hA
    (SA.viableAncestor_anc hPhi.1 hB).1 (hlr.symm.trans (congrArg SA.Lock.block hleq))
  rw [hHd, hAB, ← hBL]
  exact (SA.viableAncestor_anc hPhi.1 hB).2

/-- Full writer-local vote-head classification, with finite service supplying the prior-slot
H-wit cut.
The optimistic residue exports the actual counted pool through `OptimisticLockAt`;
`SA.optimisticLockAt_spec` gives its threshold and honest-vote provenance. -/
theorem FrameWindow.vote_head_classification_of_service {s₀ floor : Nat} {hi : Time}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hs₀ : s₀ ≤ e.msg.slot - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((e.msg.slot - 1 : Nat) : Int))
    (hmb : sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ ≤ b)
    (hgf : gbar g < SA.freeze sp e.msg.slot) :
    ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      ((Hd ∈ SA.voteDomain sp e.readPoint ell.frame e.msg.slot ∧
        Hd ∈ ell.frame.viableHeads) ∨
      (kindJ ∧ Hd = J) ∨
      (Hd = SA.getAnchor sp e.readPoint ell.frame (tr.time i) ∧
        ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
        ∃ a ≤ i, ∃ D CV, SA.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
          sp.ts e.msg.slot ≤ tr.time a ∧ tr.time a < sp.ts e.msg.slot + 2 * sp.Δ ∧
          3 * sp.n ≤ 4 * (SA.voters CV).ncard ∧
          ell.frame.Anc Hd D)) := by
  obtain ⟨a, hai, ell₀, ha, halo, hat⟩ :=
    prior_vote_call_before_freeze hS hnr hy hc hpos hm hmb hs₀
  obtain ⟨Hd, hHd, hHDr, hv | hj | ⟨hA, l, hl, hs, c, hci, D, CV, ho, ht,
      L, hL, hLr, hHL, hLD⟩⟩ :=
    hframe.vote_head_classification hrun hnc hf hnr hy hai ha hc halo hihi hat hwarm hpos hgf
  · exact ⟨Hd, hHd, hHDr, Or.inl hv⟩
  · exact ⟨Hd, hHd, hHDr, Or.inr (Or.inl hj)⟩
  have hAC := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨htop, hcount, -⟩ := SA.optimisticLockAt_spec hAC hy ho (SA.CommitteeDict.full sp.n)
    (fun _ _ _ => SA.mem_full _ _)
  rw [hS.stock] at hcount
  have hD : D ∈ ell.frame.tree := by
    obtain ⟨ellw, Aw, hp, hslot, hsel, -⟩ := ho
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have hDw := (SA.deepest_mem hsel).1.1
    rw [Compose.frame_of_projAC hrun hy hp.1] at hDw
    have hDi := Compose.tree_mono hrun.toLocalRun hy hci hDw.1
    have hPhi := SA.frameIn_of_callAt hAC.localRun hy hc.1
    have hHD := (hHL.mono hPhi.2).trans hLD
    have hHdi := hHd
    rw [Compose.frame_of_projAC hrun hy hc.1] at hHdi
    have hFD : Anc (tr.HonestBlocks H) (tr.state y i).fg.F D :=
      (Anc.mono (show (tr.state y i).fg.tree ⊆ tr.HonestBlocks H from
        fun B hB => ⟨y, hy, i, hB⟩) hHdi.2).trans hHD
    rw [Compose.frame_of_projAC hrun hy hc.1]
    exact ⟨hDi, Compose.honest_held_anc hrun hnc hy hFD hDi⟩
  have hPhi := SA.frameIn_of_callAt hAC.localRun hy hc.1
  have hLt : L ∈ ell.frame.tree := by
    by_cases he : Hd = L
    · exact he ▸ hHd
    · exact (Anc.mem hHL he).2
  exact ⟨Hd, hHd, hHDr, Or.inr (Or.inr ⟨hA, l, hl, hs, c, hci, D, CV, ho,
    ht, htop, hcount, hHL.trans (SA.anc_tree_of_anc_U hAC.localRun.coherent
      hPhi.1 hPhi.2 hLt hLD hD)⟩)⟩

/-- Finite awake service and no late restarts give the actual-run fault bound at a
next-slot action. No post-reset premise is used. -/
theorem faultBound_of_service
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hnr : NoRestartAfter tr H (gbar g))
    {t : Time} (ht0 : 0 ≤ t) (hprev : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) (htb : t ≤ b) :
    SA.FaultBound tr.projAC H t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (SA.ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : H ⊆ {y | y ∈ H ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t} := by
    intro y hy
    refine ⟨hy, hawake y hy t (hprev.trans hts) htb, ?_⟩
    intro k hk _
    exact (hnr y hy k (Compose.projAC_restartAt.mp hk)).trans hprev
  have hle := Set.ncard_le_ncard hsub
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := sp.toParams.hn
  change Hᶜ.ncard < {y | y ∈ H ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t}.ncard
  change 0 < sp.n at this
  omega

end Consensus.Goldilocks.Healing

end
