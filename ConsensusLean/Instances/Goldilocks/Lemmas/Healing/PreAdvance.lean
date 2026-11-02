module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore

public section

/-! # Pre-advance unanimous-slot propagation

Finite service and explicit frame equalities propagate unanimous vote ancestry to the
next slot's honest votes and proposal heads, without any reset premise. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- Explicit F-independent frame data on a finite interval. F itself need not agree. -/
structure FrameWindow (lo hi : Time) (floor : Nat) (contest kindJ : Prop)
    (J : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  floor_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.headHeightFloor = floor
  contest_iff : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    ((tr.state y i).fg.Contest ↔ contest)
  kind_iff : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest) ↔ kindJ)
  root_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi → kindJ →
    (tr.state y i).fg.J = J

/-- The floor bound of a source block passes to every honest-held descendant, with no
ordering requirement on the source and descendant cuts. -/
theorem floor_le_of_honest_ancestor (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H)
    {i c : Nat} {X W : SA.Blk sp.n (List (FG.Att sp.n))} {floor : Nat}
    (hX : X ∈ (tr.state z c).fg.tree) (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocks H) X W) :
    floor ≤ ((tr.state x i).fg.σ W.root).h := by
  have hXt := mem_of_honest_anc hrun hnc hx hXW hW
  have hle := (Compose.honest_held_height hrun hnc hx
    (Compose.honest_held_anc hrun hnc hx hXW hW)).1
  rw [← σ_eq_honest hrun hnc hz hx hX hXt] at hle
  exact hh.trans hle

/-- V_U for an honest-held descendant of a floor-viable source. All three cuts are
arbitrary; in particular the source cut need not precede either of the others. -/
theorem finalized_below_floor_descendant (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y x z : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) (hz : z ∈ H)
    {j i c : Nat} {X W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state z c).fg.tree)
    (hh : (tr.state y j).fg.headHeightFloor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 →
      ¬(tr.state y j).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y j).fg.J X)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocks H) X W) :
    Anc (tr.HonestBlocks H) (tr.state y j).fg.F W :=
  finalized_below_floor_held hrun hnc hf hy hx hW
    (floor_le_of_honest_ancestor hrun hnc hx hz hX hh hW hXW)
    (fun hm hc => (hJ hm hc).trans hXW)

/-- The interval's common floor and J condition give the relay ancestry at its own cut. -/
theorem FrameWindow.finalized_below_descendant {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y x z : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) (hz : z ∈ H)
    {j i c : Nat} (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocks H) X W) :
    Anc (tr.HonestBlocks H) (tr.state y j).fg.F W := by
  refine finalized_below_floor_descendant hrun hnc hf hy hx hz hX ?_ ?_ hW hXW
  · rwa [hframe.floor_eq y hy j hjlo hjhi]
  · intro hm hc
    have hk := (hframe.kind_iff y hy j hjlo hjhi).mp ⟨hm, hc⟩
    rw [hframe.root_eq y hy j hjlo hjhi hk]
    exact hJ hk

/-- An actual early FG acceptance survives to a later action frame when the common-floor
witness extends that action's finalized tip. Retention includes restart replay: finalized
tips at intervening restarts lie below the target tip, hence below Q. -/
theorem FrameWindow.early_accepted_mem_frame {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i c : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J Q)
    {T : Time} (hacc : ∃ k, tr.AcceptAt y k Q ∧ tr.time k < T)
    (hTi : T ≤ tr.time i) : Q ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨k, hk, hkt⟩ := hacc
  obtain ⟨ha, ht, -⟩ := ac_block_after hrun.toLocalRun hy hk
  have hki : k + 1 ≤ i := by
    by_contra hn
    have htime := hr.time_mono (show i ≤ k + 1 by omega)
    change tr.time i ≤ tr.time (k + 1) at htime
    rw [ht] at htime
    linarith
  apply SA.mem_tree_of_acceptAt sp hr hy ha hki hc
  rw [Compose.frame_of_projAC hrun hy hc]
  exact hframe.finalized_below_descendant hrun hnc hf hy hz hz hlo hhi hQ hh hJ hQ
    Relation.ReflTransGen.refl

/-- Producer form of U-W's vote binder. Actual acceptance before the freeze supplies
both FG heldness and the strict emission-read-point stamp. The common-floor/J geometry
is used for retention, rather than assuming arbitrary early blocks survive a restart. -/
theorem FrameWindow.early_accepted_vote_witness {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (gbar g))
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i c : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC y i e)
    (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J Q)
    (hacc : ∃ k, tr.AcceptAt y k Q ∧ tr.time k < SA.freeze sp e.msg.slot)
    (hgf : gbar g < SA.freeze sp e.msg.slot)
    (hti : SA.freeze sp e.msg.slot ≤ tr.time i) :
    Q ∈ (tr.state y i).fg.tree ∧
      e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp e.msg.slot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨ell, hc, he⟩ := hv
  have hQt := hframe.early_accepted_mem_frame hrun hnc hf hy hz hc hlo hhi hQ hh hJ hacc hti
  refine ⟨mem_tree_of_frame hrun hy hc hQt, ?_⟩
  apply SA.readPoint_blockStamp_lt_of_acceptedBefore hr hy ⟨hc, he⟩ hQt
  · obtain ⟨k, hk, hkt⟩ := hacc
    obtain ⟨ha, ht, -⟩ := ac_block_after hrun.toLocalRun hy hk
    exact Or.inr ⟨k + 1, ha, by change tr.time (k + 1) < _; rwa [ht]⟩
  · intro k _ hrs
    exact (hnr y hy k (Compose.projAC_restartAt.mp hrs)).trans_lt hgf
  · exact hti

/-- A common-floor witness above X makes X comparable with the target's finalized tip.
The witness's source cut is arbitrary. -/
theorem FrameWindow.finalized_comparable_of_witness {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {j c : Nat}
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J Q)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    Compatible (tr.HonestBlocks H) (tr.state y j).fg.F X := by
  exact SA.anc_total (Compose.honest_blocks_coherent hrun.toLocalRun hnc)
    (hframe.finalized_below_descendant hrun hnc hf hy hz hz hjlo hjhi hQ hh hJ hQ
      Relation.ReflTransGen.refl) hXQ

/-- An actual honest vote extending the common-floor source satisfies the receiving
cut's relay ancestry, even before its head has reached the receiver. -/
theorem FrameWindow.finalized_below_vote {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y x z : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) (hz : z ∈ H)
    {j i c : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x i e)
    (hG : SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ B ∈ tr.HonestBlocks H, B.root = e.msg.head →
      Anc (tr.HonestBlocks H) ell.frame.F B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨ellx, hcx, hex⟩ := hv
  obtain ⟨W, hW, hWr, -⟩ := SA.honest_head_frame hr hx ⟨hcx, hex⟩
  obtain ⟨W', hW', hW'r, hXW⟩ := hG
  have hWU : W ∈ tr.HonestBlocks H :=
    ⟨x, hx, i, mem_tree_of_frame hrun hx hcx hW⟩
  have heq : W' = W := hr.coherent.1 hW' hWU (hW'r.trans hWr.symm)
  subst W'
  intro B hB hBr
  have heq : B = W := hr.coherent.1 hB hWU (hBr.trans hWr.symm)
  subst B
  rw [Compose.frame_of_projAC hrun hy hc]
  exact hframe.finalized_below_descendant hrun hnc hf hy hx hz hjlo hjhi hX hh hJ
    (mem_tree_of_frame hrun hx hcx hW) hXW

/-- The common-floor relay condition suffices for CarryAt of the actual honest batch.
The source block's honest cut is unrestricted. -/
theorem FrameWindow.honest_batch_carry {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {j c s : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e') (hs' : e'.msg.slot = s + 1)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    (hdl : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrs : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.time k < sp.ts s)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y j e' s
      {v | ∃ x ∈ H, ∃ i e, SA.VoteAt tr.projAC x i e ∧ e.msg = v ∧ v.slot = s} :=
  SA.honest_batch_carry_before hS hy hc hs' hs ht hjb hdl hrs
    (fun x hx i e hv hes => hframe.finalized_below_vote hrun hnc hf hy hx hz hc.1 hjlo hjhi
      hX hh hJ hv (hG x hx i e hv hes))

/-- No-restart and the initial slot margin supply the bounded actual honest vote batch. -/
theorem honest_votes_before_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsync : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hc : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b) :
    ∀ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ := by
  apply SA.honest_votes_in_slot_before
    (healthy_base_of_service_catch_before hrun hnc hsync hawake hf hc) hm hmb
  intro x hx r _ hrs
  have hr := hnr x hx r (Compose.projAC_restartAt.mp hrs)
  rw [SA.ts_sub_one]
  change tr.time r ≤ _
  linarith

/-- Finite reset-free service resolves an honest initial-slot vote and its head strictly
before the next slot's freeze. The caller supplies the receiver's finality ancestry. -/
theorem late_vote_held_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsync : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (ht : sp.ts m + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x i e) (hes : e.msg.slot = m)
    (hF : ∀ B ∈ tr.HonestBlocks H, B.root = e.msg.head →
      Anc (tr.HonestBlocks H) ell.frame.F B) :
    ∃ B ∈ ell.frame.tree, B.root = e.msg.head ∧ B.slot ≤ m ∧
      e.msg ∈ (tr.projAC.state y j).pool m ∧
      (tr.projAC.state y j).voteStamp e.msg < SA.ETime.of (sp.ts m + 2 * sp.Δ) ∧
      (tr.projAC.state y j).blockStamp e.msg.head < SA.ETime.of (sp.ts m + 2 * sp.Δ) := by
  refine SA.late_vote_held_of_frame_before
    (healthy_base_of_service_catch_before hrun hnc hsync hawake hf hcatch)
    hy hc hm ht hjb ?_ ?_ hx hv hes hF
  · intro k _ t _
    apply deadline_le_restarts (a := sp.ts m)
    intro r _ hrs
    have hr := hnr y hy r (Compose.projAC_restartAt.mp hrs)
    change tr.time r ≤ _
    have := sp.toParams.hΔ
    linarith
  · intro k _ hrs
    have hr := hnr y hy k (Compose.projAC_restartAt.mp hrs)
    change tr.time k < _
    have := sp.toParams.hΔ
    linarith

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

/-- A carried honest head extending a floor-viable X makes X frozen-viable at the
receiving vote. This does not assume that arbitrary honest heads are viable. -/
theorem viable_at_vote_of_carried_head (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {j c s : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hs : e.msg.slot = s + 1)
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : (tr.state y j).fg.headHeightFloor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 →
      ¬(tr.state y j).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y j).fg.J X)
    (hW : W ∈ ell.frame.tree) (hXW : Anc (tr.HonestBlocks H) X W)
    (hacc : SA.AcceptedBefore tr.projAC y X (SA.freeze sp e.msg.slot))
    (hrs : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.time k < SA.freeze sp e.msg.slot)
    (ht : SA.freeze sp e.msg.slot ≤ tr.time j) : SA.ViableAtVote ell e (s + 1) X := by
  obtain ⟨hXt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hz hX hh hJ
    (mem_tree_of_frame hrun hy hc.1 hW) hXW
  rw [← Compose.frame_of_projAC hrun hy hc.1] at hXt hroot hv
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hdom := SA.voterBlockTree_of_acceptedBefore hr hy hc hXt hacc hrs ht
  rw [hs] at hdom
  exact Or.inl ⟨hdom, hroot, X, hdom, hv, Relation.ReflTransGen.refl⟩

/-- The honest preceding-slot batch is at least half the committee. -/
theorem honest_voters_half_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b) :
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ i e, SA.VoteAt tr.projAC x i e ∧ e.msg.slot = m}.ncard := by
  have hall := honest_votes_before_of_service hrun hnc hsvc hawake hf hcatch hnr hm hmb
  have hle := Set.ncard_le_ncard (s := H)
    (t := {x | x ∈ H ∧ ∃ i e, SA.VoteAt tr.projAC x i e ∧ e.msg.slot = m}) (by
      intro x hx
      obtain ⟨i, e, hv, hs, -⟩ := hall x hx
      exact ⟨hx, i, e, hv, hs⟩)
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := sp.toParams.hn
  omega

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

/-- The shared U induction separates delivery/path geometry from the finite-run inputs. -/
private theorem unanimous_next_votes_of_geometry (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X)
    (hgeom : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      e.msg.slot = m + 1 →
      Anc (tr.HonestBlocks H) X ell.frame.F ∨
        (SA.ViableAtVote ell e (m + 1) X ∧
          ∀ x ∈ H, ∀ k ev, SA.VoteAt tr.projAC x k ev → ev.msg.slot = m →
            ∀ B ∈ tr.HonestBlocks H, B.root = ev.msg.head →
              Anc (tr.HonestBlocks H) ell.frame.F B)) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hhalf := honest_voters_half_of_service hrun hnc hsvc hawake hf hcatch hnr hm
    (show sp.ts m + sp.Δ ≤ b by linarith)
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X by
    exact fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e hv hs
    obtain ⟨ell, hc, he⟩ := hv
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hslot : sp.slot (tr.time i) = m + 1 := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
    have hlo : sp.ts (m + 1 : Nat) ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
        change ((m + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
        rw [hslot])
    have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
      have ht := SA.vote_time_le hr hy ⟨ell, hcast⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      simpa only [hslot] using ht
    have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
        tr.projAC.deadline y k t ≤ max t (sp.ts m) + sp.Δ := by
      intro k _ t _
      apply deadline_le_restarts (a := sp.ts m)
      intro r _ hrs
      have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ _
      linarith
    have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < sp.ts m := by
      intro k _ hk
      have := hnr y hy k (Compose.projAC_restartAt.mp hk)
      change tr.time k < _
      linarith
    rcases hgeom y hy i ell e hcast hs with hbelow | ⟨hviab, hrelay⟩
    · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
      obtain ⟨W, hW, hWr, hXW⟩ := SA.castAt_head_anc hr hy hcast (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      exact ⟨W, hPhiU hW, hWr, hbelow.trans (hXW.mono hPhiU)⟩
    have hcarry := SA.honest_batch_carry_before hS hy hcast hs hm
      (by change sp.ts m + 2 * sp.Δ ≤ tr.time i; linarith) (hhi.trans hmb) hdl hrs hrelay
    exact SA.next_transfer_of_carry sp hS.run hy hcast hs hG hhalf hcarry
      (faultBound_of_service hawake hf hnr (hr.time_nonneg i)
        (by
          change gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
          rw [hslot]
          have heq : ((m + 1 : Nat) : Int) - 1 = m := by omega
          rw [heq]; linarith) (hhi.trans hmb)) hviab
      (fun x hx k hki ev hv hsx => ih k hki x hx ev hv hsx)

/-- Local V for a witness also places every ancestor above F and the common J in the frame. -/
private theorem FrameWindow.witness_path {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i c : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    {X Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) (hQy : Q ∈ (tr.state y i).fg.tree)
    (hFX : Anc (tr.HonestBlocks H) (tr.state y i).fg.F X) :
    X ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot X ∧
      Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc X Q := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hQt, -, hvQ⟩ := floor_ancestor_mem_frame hrun hnc hf hy hz hQ
    (by rw [hframe.floor_eq y hy i hlo hhi]; exact hh)
    (fun hm' hc' => by
      have hk := (hframe.kind_iff y hy i hlo hhi).mp ⟨hm', hc'⟩
      rw [hframe.root_eq y hy i hlo hhi hk]
      exact (hJ hk).trans hXQ) hQy Relation.ReflTransGen.refl
  rw [← Compose.frame_of_projAC hrun hy hc] at hQt hvQ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  have hXt : X ∈ ell.frame.tree := by
    have hXy := mem_of_honest_anc hrun hnc hy hXQ hQy
    rw [Compose.frame_of_projAC hrun hy hc]
    exact ⟨hXy, Compose.honest_held_anc hrun hnc hy hFX hXy⟩
  refine ⟨hXt, ?_, hQt, hvQ, SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hXt hXQ hQt⟩
  apply SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem _ hXt
  rw [Compose.frame_of_projAC hrun hy hc]
  change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot X
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · have h := hJ ((hframe.kind_iff y hy i hlo hhi).mp hk)
    rw [← hframe.root_eq y hy i hlo hhi ((hframe.kind_iff y hy i hlo hhi).mp hk)] at h
    have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J := by
      simp [Goldilocks.Store.fcRoot, hk]
    exact he ▸ h
  · have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.F := by
      simp [Goldilocks.Store.fcRoot, hk]
    exact he ▸ hFX

/-- U-W's vote conclusion uses a common-floor witness above X in each target frozen domain.
`floor` and `J` are the FS′ values supplied by `hframe`; the source cut is arbitrary.
The kind-J condition is on X, not merely on its witness, and the stamp is read from
the vote emission's read point, not its pre-call state. -/
theorem unanimous_next_votes_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m floor : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hheld : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
      Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp (m + 1)))
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  apply unanimous_next_votes_of_geometry hrun hnc hsvc hawake hf hcatch hnr hm hmb hG
  intro y hy i ell e hc hs
  have hslot : sp.slot (tr.time i) = m + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hs
  have hlo : sp.ts m ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
      change (m : Int) ≤ sp.slot (tr.time i)
      rw [hslot]; omega)
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
    have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    simpa only [hslot] using ht
  have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := fun hk => (hJ hk).trans hXQ
  rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hz hlo hhi hQ hh hJQ hXQ
    with hFX | hXF
  swap
  · exact Or.inl (by rwa [Compose.frame_of_projAC hrun hy hc.1])
  obtain ⟨hQy, hstamp⟩ := hheld y hy i e ⟨ell, hc⟩ hs
  obtain ⟨hXt, hrootX, hQt, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hz
    hc.1 hlo hhi hQ hh hJ hXQ hQy hFX
  have hQdom : Q ∈ SA.voterBlockTree sp e.readPoint ell.frame (m + 1) := by
    exact ⟨hQt, Or.inl hstamp⟩
  have hdomA := SA.voterBlockTree_anc hr hy hc
  rw [hs] at hdomA
  refine Or.inr ⟨Or.inl ⟨hdomA Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩, ?_⟩
  intro x hx k ev hv hes B hB hBr
  obtain ⟨W, hW, hWr, hXW⟩ := hG x hx k ev hv hes
  obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
  rw [Compose.frame_of_projAC hrun hy hc.1]
  exact hFX.trans hXW

/-- U's vote conclusion, with explicit common frame data and an arbitrary honest
source cut for X. -/
theorem unanimous_next_votes (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m floor : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  apply unanimous_next_votes_of_geometry hrun hnc hsvc hawake hf hcatch hnr hm hmb hG
  intro y hy i ell e hc hs
  have hslot : sp.slot (tr.time i) = m + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hs
  have hlo : sp.ts m ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
      change (m : Int) ≤ sp.slot (tr.time i)
      rw [hslot]; omega)
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
    have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    simpa only [hslot] using ht
  have hrelay := fun x hx k ev hv hes => hframe.finalized_below_vote hrun hnc hmf
    hy hx hz hc.1 hlo hhi hX hh hJ hv (hG x hx k ev hv hes)
  refine Or.inr ⟨?_, hrelay⟩
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      tr.projAC.deadline y k t ≤ max t (sp.ts m) + sp.Δ := by
    intro k _ t _
    apply deadline_le_restarts (a := sp.ts m)
    intro r _ hrs
    have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
    change tr.time r ≤ _
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < sp.ts m := by
    intro k _ hk
    have := hnr y hy k (Compose.projAC_restartAt.mp hk)
    change tr.time k < _
    linarith
  obtain ⟨k, ev, hvx, hsx, -⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
    hcatch hnr hm (show sp.ts m + sp.Δ ≤ b by linarith) y hy
  have hnext : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
      change ((m + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
      rw [hslot])
  obtain ⟨W, hW, hWr, -, -, -, -, hacc⟩ := SA.late_vote_accepted_of_frame_before hS hy hc.1
    hm (by change sp.ts m + 2 * sp.Δ ≤ tr.time i; linarith) (hhi.trans hmb) hdl hrs hy hvx hsx
    (hrelay y hy k ev hvx hsx)
  obtain ⟨W', hW', hW'r, hXW⟩ := hG y hy k ev hvx hsx
  obtain ⟨_, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain rfl : W' = W := hr.coherent.1 hW' (hPhiU hW) (hW'r.trans hWr.symm)
  have haccX := SA.acceptedBefore_ancestor hr hy hc.1 (hPhiU hW) hacc hXW
  have hfreeze : SA.freeze sp e.msg.slot = sp.ts m + 3 * sp.Δ := by
    rw [hs]; simp only [SA.freeze]; congr 1; congr 1; omega
  apply viable_at_vote_of_carried_head hrun hnc hmf hy hz hc hs hX
    (by rw [hframe.floor_eq y hy i hlo hhi]; exact hh)
    (fun hm' hc' => by
      have hk := (hframe.kind_iff y hy i hlo hhi).mp ⟨hm', hc'⟩
      rw [hframe.root_eq y hy i hlo hhi hk]
      exact hJ hk) hW hXW
  · rcases haccX with hg | ⟨a, ha, hat⟩
    · exact Or.inl hg
    · exact Or.inr ⟨a, ha, by rw [hfreeze]; linarith⟩
  · intro k hk hrk
    rw [hfreeze]
    have := hrs k hk hrk
    linarith
  · rw [hfreeze]; linarith

/-- The shared proposal argument consumes local path geometry and relay ancestry. -/
private theorem unanimous_next_proposal_of_geometry (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hgeom : Anc (tr.HonestBlocks H) X ell.frame.F ∨
      ((X ∈ ell.frame.tree ∧
        (X ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc X ell.frame.fcRoot)) ∧
        ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = m →
          ∀ B ∈ tr.HonestBlocks H, B.root = e.msg.head → Anc (tr.HonestBlocks H) ell.frame.F B)) :
    Anc (tr.HonestBlocks H) X d.head := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hf2 : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  have hhalf := honest_voters_half_of_service hrun hnc hsvc hawake hf hcatch hnr hm
    (show sp.ts m + sp.Δ ≤ b by linarith)
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  rcases hgeom with hbelow | ⟨hV, hrelay⟩
  · have he := (SA.acProposal_head hd).2
    rw [he]
    exact hbelow.trans ((SA.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      tr.projAC.deadline y k t ≤ max t (sp.ts m) + sp.Δ := by
    intro k _ t _
    apply deadline_le_restarts (a := sp.ts m)
    intro r _ hrs
    have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
    change tr.time r ≤ _
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < sp.ts m := by
    intro k _ hk
    have := hnr y hy k (Compose.projAC_restartAt.mp hk)
    change tr.time k < _
    linarith
  have hdel : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = m →
      ∃ W ∈ ell.frame.tree, W.root = e.msg.head ∧ W.slot ≤ m ∧
        e.msg ∈ (tr.projAC.state y i).pool m ∧
        (tr.projAC.state y i).voteStamp e.msg < SA.ETime.of (sp.ts m + 2 * sp.Δ) ∧
        (tr.projAC.state y i).blockStamp e.msg.head < SA.ETime.of (sp.ts m + 2 * sp.Δ) := by
    intro x hx k e hv hs
    exact SA.late_vote_held_of_frame_before hS hy hc hm
      (by change sp.ts m + 2 * sp.Δ ≤ tr.time i; linarith) (hhi.trans hmb) hdl hrs hx hv hs
      (hrelay x hx k e hv hs)
  refine SA.batch_proposal hS.run hf2 hhalf hG hy hc (SA.proposal_slot hti) hd
    hV ?_ ?_
  · intro x hx k e hv hs
    obtain ⟨W, hW, hWr, -, hp, -, hb⟩ := hdel x hx k e hv hs
    apply SA.heldAtProposal_iff.mpr
    exact ⟨Or.inl hp, W, hW, hWr, hWr ▸ lt_trans hb
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩
  · apply SA.highLocksCompatible_iff.mpr
    intro l hl _ hlm L hL hLr
    have hl' : l ∈ (tr.state y i).ac.locks := by
      rwa [Compose.projAC_state hrun.toLocalRun hy i] at hl
    have hls := Compose.proposal_locks_slot_of hrun hnc hf2 hy hc hcall hd hti l hl'
    have heq : l.slot = m := by omega
    obtain ⟨O, hLO, a, CV, hopt⟩ := SA.proposal_high_lock hr hy hti hl hlm hL hLr
    rw [heq] at hopt
    rcases SA.optimisticLock_compatible hS.run hf2 hy hopt hG with hOX | hXO
    · exact Or.inl (hLO.trans hOX)
    · exact SA.anc_total hr.coherent hLO hXO

/-- U-W at an actual next-slot proposal needs heldness of Q, not a frozen stamp.
`floor` and `J` are the FS′ values supplied by `hframe`; the source cut is arbitrary. -/
theorem unanimous_next_proposal_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m floor : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) : Anc (tr.HonestBlocks H) X d.head := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hlo : sp.ts m ≤ tr.time i := by linarith
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  apply unanimous_next_proposal_of_geometry hrun hnc hsvc hawake hf hcatch hnr hm hmb hG
    hy hc hcall hti hd
  rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hz hlo hhi hQ hh
      (fun hk => (hJ hk).trans hXQ) hXQ with hFX | hXF
  swap
  · exact Or.inl (by rwa [Compose.frame_of_projAC hrun hy hc])
  obtain ⟨hXt, hroot, hQt, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hz hc
    hlo hhi hQ hh hJ hXQ hQy hFX
  refine Or.inr ⟨⟨hXt, Or.inl ⟨hXt, hroot, Q, hQt, hvQ, hXQf⟩⟩, ?_⟩
  intro x hx k e hv hs B hB hBr
  obtain ⟨W, hW, hWr, hXW⟩ := hG x hx k e hv hs
  obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
  rw [Compose.frame_of_projAC hrun hy hc]
  exact hFX.trans hXW

/-- U's proposal conclusion retains its original floor-viable source contract. -/
theorem unanimous_next_proposal (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {m floor : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hG : ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay)) :
    Anc (tr.HonestBlocks H) X d.head := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hlo : sp.ts m ≤ tr.time i := by linarith
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      tr.projAC.deadline y k t ≤ max t (sp.ts m) + sp.Δ := by
    intro k _ t _
    apply deadline_le_restarts (a := sp.ts m)
    intro r _ hrs
    have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
    change tr.time r ≤ _
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < sp.ts m := by
    intro k _ hk
    have := hnr y hy k (Compose.projAC_restartAt.mp hk)
    change tr.time k < _
    linarith
  obtain ⟨k, e, hv, hs, -⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf hcatch
    hnr hm (show sp.ts m + sp.Δ ≤ b by linarith) y hy
  obtain ⟨W, hW, hWr, -, -, -, -⟩ := SA.late_vote_held_of_frame_before hS hy hc hm
    (by change sp.ts m + 2 * sp.Δ ≤ tr.time i; linarith) (hhi.trans hmb) hdl hrs hy hv hs
    (hframe.finalized_below_vote hrun hnc hmf hy hy hz hc hlo hhi hX hh hJ hv
      (hG y hy k e hv hs))
  obtain ⟨W', hW', hW'r, hXW⟩ := hG y hy k e hv hs
  obtain ⟨_, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  obtain rfl : W' = W := hr.coherent.1 hW' (hPhiU hW) (hW'r.trans hWr.symm)
  exact unanimous_next_proposal_of_witness hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hframe hz hX hh hJ Relation.ReflTransGen.refl hG hy hc hcall hti hd
    (mem_of_honest_anc hrun hnc hy hXW (mem_tree_of_frame hrun hy hc hW))

end Consensus.Goldilocks.Healing

end
