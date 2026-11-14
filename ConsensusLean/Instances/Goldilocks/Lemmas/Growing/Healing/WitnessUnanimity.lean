module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Arbitrary-prefix unanimity through a held witness, under growing faults

Next-slot votes and proposals extend a prefix with a held witness. The prefix `X` need not be a
proposal or have slot `m`; prior votes need only extend it. Each reader (a next-slot voter or
proposer) is honest at its own cut, and the witness `Q` is held by it there. Its replay height
is the one the source `z` saw at its own cut (replay is the same at independently honest
observations), so the replay quorum is charged only at the reader's cut, never at the source's.

The frame geometry is read at the reader's cut (`witness_frame_at`). The vote and proposal steps
are the static ones on the prefix through the reader's cut, over the validators honest there
(`healthy_base_of_service_catch_before_at`): the batch carry and the next transfer for a vote,
the batch proposal for a proposal. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    SA.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) := by
  have h := Compose.goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer
    (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- Fewer than a third faulty is below the replay quorum excess. -/
private theorem quorum_excess {t : Time} (h : 3 * (H t)ᶜ.ncard ≤ sp.n - 1) :
    (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
  have hn := sp.toParams.hn
  have he : sp.n = sp.toParams.n := rfl
  change (H t)ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.n
  omega

/-- A vote of the prefix through `d` by a node honest at `d` extends `B` in the prefix's honest
blocks when it does in the run's. -/
private theorem narrow_vote (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d)
    {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (tr.projAC.upTo d) x k e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    SA.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg B := by
  have hr := (acRun_prefix hrun hnc hd).localRun
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hd
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hx hc
  have hHdU := (SA.frameIn_of_callAt hr hx hc.1).2 hHd
  obtain ⟨W, hW, hWr, hBW⟩ := hext
  obtain rfl : W = Hd := hU.1 hW (subU hHdU) (hWr.trans hHdr.symm)
  exact ⟨W, hHdU, hWr, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdU hBW⟩

/-- **The frame geometry of a held witness at a reader's cut**: for a reader honest at its call
in the `FrameWindow`, holding a floor-viable descendant `Q` of `X`, either `X` is below its
finalized tip, or `X` and `Q` are on its frame's viable path above the fork-choice root and its
finalized tip is below `X`. -/
theorem witness_frame_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))} (hframe : FrameWindow tr H lo hi floor kindJ J)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQy : Q ∈ (tr.state y i).fg.tree)
    (hh : floor ≤ ((tr.state y i).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X) (hXQ : Anc (tr.HonestBlocksAt H) X Q) :
    Anc (tr.HonestBlocksAt H) X ell.frame.F ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F X ∧ X ∈ ell.frame.tree ∧
        ell.frame.Anc ell.frame.fcRoot X ∧ Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧
        ell.frame.Anc X Q) := by
  have hm := hrun.time_mono
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hpy := hrun.upTo ht
  have hfr : ell.frame = Node.frame (tr.state y i) := by
    have h := Compose.frame_of_projAC hpy hy
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩)
    rwa [RunTrace.upTo_state_of_le hm le_rfl] at h
  have hJQ : kindJ → Anc (tr.HonestBlocksAt H) J Q := fun hk => (hJ hk).trans hXQ
  rw [hfr]
  rcases SA.anc_total hU (hframe.finalized_below_descendant_at hrun hnc hy hy hy
      (by rwa [max_self]) hlo hhi hQy hh hJQ hQy .refl) hXQ with hFX | hXF
  swap
  · exact Or.inl hXF
  refine Or.inr ⟨hFX, ?_⟩
  obtain ⟨hQt, -, hvQ⟩ := floor_ancestor_mem_frame_at hrun hnc hy hy hf hQy
    (by rw [hframe.floor_eq y i hy hlo hhi]; exact hh)
    (fun hm' hc' => by
      have hk := (hframe.kind_iff y i hy hlo hhi).mp ⟨hm', hc'⟩
      rw [hframe.root_eq y i hy hlo hhi hk]
      exact hJQ hk) hQy .refl
  have hΦ := (Store.frame_realization _ _ _ _ (fg_reachable_at hrun ht hb hy)).1
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, i, tr.time i, ht, hb, hy, h.1⟩
  have hXy := mem_of_honest_anc_at hrun hnc ht hb hy hXQ hQy
  have hXt : X ∈ (Node.frame (tr.state y i)).tree :=
    ⟨hXy, store_anc_of_honest_anc_at hrun hnc ht hb hy hFX hXy⟩
  refine ⟨hXt, ?_, hQt, hvQ, SA.anc_tree_of_anc_U hU hΦ hsub hXt hXQ hQt⟩
  apply SA.anc_tree_of_anc_U hU hΦ hsub hΦ.fcRoot_mem _ hXt
  change Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot X
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · have hkJ := (hframe.kind_iff y i hy hlo hhi).mp hk
    have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J := by
      simp [Goldilocks.Store.fcRoot, hk]
    rw [he, hframe.root_eq y i hy hlo hhi hkJ]
    exact hJ hkJ
  · have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.F := by
      simp [Goldilocks.Store.fcRoot, hk]
    exact he ▸ hFX

/-- The witness's replay height, seen by an independently honest source, is the reader's. -/
private theorem witness_height (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z y : Fin sp.n} {c i : Nat} (hz : z ∈ H (tr.time c))
    (hy : y ∈ H (tr.time i)) {Q : SA.Blk sp.n (List (FG.Att sp.n))} {floor : Nat}
    (hQ : Q ∈ (tr.state z c).fg.tree) (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hQy : Q ∈ (tr.state y i).fg.tree) : floor ≤ ((tr.state y i).fg.σ Q.root).h := by
  rwa [← σ_eq_honest_at hrun hnc (hrun.time_nonneg c) (fun _ hq => hrun.time_mono hq.le) hz
    (hrun.time_nonneg i) (fun _ hq => hrun.time_mono hq.le) hy hQ hQy]

/-- **Prior votes extending an arbitrary prefix propagate through a frozen viable witness**,
under growing faults. -/
theorem unanimous_next_votes_of_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hgm : gbar g ≤ sp.ts m := by linarith
  suffices hall : ∀ i, ∀ y e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X from
    fun y i e => hall i y e
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro y e hy hv hs
  obtain ⟨ell, hcast⟩ := hv
  have ht0 := hrun.time_nonneg i
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hrun' := acRun_prefix hrun hnc ht0
  have hr := hrun'.localRun
  have hcast' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e :=
    SA.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hslot : sp.slot (tr.time i) = m + 1 := (SA.castAt_spec hr hy hcast').2.1.symm.trans hs
  have hlo1 : sp.ts (m + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp ht0 _).mpr (by rw [hslot])
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
    have h := SA.vote_time_le hr hy ⟨ell, hcast'⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
    simpa only [hslot] using h
  have hib : tr.time i ≤ b := hhi.trans hmb
  have hlo : sp.ts m ≤ tr.time i := by linarith
  obtain ⟨hQy, hstamp⟩ := hheld y i e hy ⟨ell, hcast⟩ hs
  have hhy := witness_height hrun hnc hz hy hQ hh hQy
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch ht0 hib
    hstock
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcast'.1
  rcases witness_frame_at hrun hnc hframe hy hcast.1 hlo hhi
      (quorum_excess (hf _ ht0 hib)) hQy hhy hJ hXQ with hXF | ⟨hFX, hXt, hrootX, hQt, hvQ, hXQf⟩
  · obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast' (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
    exact ⟨W, subU (hPhiU hW), hWr, hXF.trans ((hFW.mono hPhiU).mono subU)⟩
  -- the voter's vote domain holds `Q`, hence `X`, viable above its fork-choice root
  have hQdom : Q ∈ SA.voterBlockTree sp e.readPoint ell.frame (m + 1) := ⟨hQt, Or.inl hstamp⟩
  have hdomA := SA.voterBlockTree_anc hr hy hcast'
  rw [hs] at hdomA
  have hviab : SA.ViableAtVote ell e (m + 1) X :=
    Or.inl ⟨hdomA Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩
  -- slot-`m` votes of nodes honest at the voter's cut extend `X` above its `Σ.F`
  have hG' : ∀ x ∈ H (tr.time i), ∀ j e', SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      e'.msg.slot = m → SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e'.msg X := by
    intro x hx j e' hv' hs'
    obtain ⟨hjd, hv''⟩ := SA.upTo_voteAt.mp hv'
    exact narrow_vote hrun hnc ht0 hx hv' (hG x j e' (hrun.antitone hjd hx) hv'' hs')
  have hrelay : ∀ x ∈ H (tr.time i), ∀ k ev, SA.VoteAt (tr.projAC.upTo (tr.time i)) x k ev →
      ev.msg.slot = m → ∀ B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)),
        B.root = ev.msg.head →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ell.frame.F B := by
    intro x hx k ev hv' hs' B hB hBr
    obtain ⟨W, hW, hWr, hXW⟩ := hG' x hx k ev hv' hs'
    obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hB (hFX.trans (hXW.mono subU))
  have hrestart : ∀ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ gbar g := by
    intro k hk
    obtain ⟨hkd, hk⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hk
    exact hnr y k (hrun.antitone hkd hy) (Compose.projAC_restartAt.mp hk)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := SA.goldilocksSA sp _ ro) (tr.projAC.upTo (tr.time i)) y k t ≤
        max t (sp.ts m) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts m)
      (fun r _ hrs => (hrestart r hrs).trans hgm) t
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k < sp.ts m :=
    fun k _ hk => (hrestart k hk).trans_lt (by linarith)
  have hcarry := SA.honest_batch_carry_before hS hy hcast' hs hm
    (show sp.ts m + 2 * sp.Δ ≤ tr.time i by linarith) le_rfl hdl hrs hrelay
  have hhalf := SA.honest_voters_half_before hS hm (show sp.ts m + sp.Δ ≤ tr.time i by linarith)
    (fun x hx r _ hrest => by
      obtain ⟨hrd, hrest⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hrest
      rw [SA.ts_sub_one]
      exact (hnr x r (hrun.antitone hrd hx) (Compose.projAC_restartAt.mp hrest)).trans
        (by linarith))
  have hhalf' : sp.n ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ j e',
      SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m}.ncard := by
    have hle := Set.ncard_le_ncard (s := {x | x ∈ H (tr.time i) ∧ ∃ j e',
      SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m ∧
        (tr.projAC.upTo (tr.time i)).time j ≤ sp.ts m + sp.Δ})
      (t := {x | x ∈ H (tr.time i) ∧ ∃ j e',
        SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m})
      (by rintro x ⟨hx, j, e', hv', hs', _⟩; exact ⟨hx, j, e', hv', hs'⟩)
    omega
  have hfault : SA.FaultBound (tr.projAC.upTo (tr.time i)) (H (tr.time i)) (tr.time i) := by
    have h := Healing.faultBound_of_service (tr := tr.upTo (tr.time i)) (H := H (tr.time i))
      (b := tr.time i)
      (fun y' hy' t hgt htd => (Trace.upTo_awake _ y' t).mpr
        ⟨hawake y' t (hrun.antitone htd hy') hgt (htd.trans hib), htd⟩)
      (hf _ ht0 hib)
      (fun y' hy' k hk => by
        obtain ⟨hkd, hk⟩ := (RunTrace.upTo_restartAt tr).mp hk
        exact hnr y' k (hrun.antitone hkd hy') hk)
      ht0 (by
        rw [hslot]
        have heq : ((m + 1 : Nat) : Int) - 1 = m := by omega
        rw [heq]; exact hgm) le_rfl
    rwa [RunTrace.upTo_projAC] at h
  have hext := SA.next_transfer_of_carry sp hrun' _ SA.CommitteeP.full SA.CommitteeT.full
    (SA.size_binding_full hS.stock) hy hcast' hs hG' (by rw [hS.stock]; exact hhalf') hcarry
    ((SA.faultBoundK_full_iff _ _).2 hfault) (SA.cs2_full_of_faultBound sp hS.stock hfault) hviab
    (fun x hx k hki ev hv' hsx => by
      obtain ⟨hkd, hv''⟩ := SA.upTo_voteAt.mp hv'
      exact narrow_vote hrun hnc ht0 hx hv'
        (ih k hki x ev (hrun.antitone hkd hx) hv'' hsx))
  obtain ⟨W, hW, hWr, hXW⟩ := hext
  exact ⟨W, subU hW, hWr, hXW.mono subU⟩

/-- **The same arbitrary prefix reaches an actual next-slot proposal head**, under growing
faults. -/
theorem unanimous_next_proposal_of_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → SA.VoteAt tr.projAC x j e →
      e.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hgm : gbar g ≤ sp.ts m := by linarith
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := by linarith
  have hlo : sp.ts m ≤ tr.time i := by linarith
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch ht0 hib
    hstock
  have hr := hS.run.localRun
  have hf3 := hf _ ht0 hib
  have hf2 : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := Fin.pos y
    omega
  have hcp : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hdp : (SA.acProposal sp ((tr.projAC.upTo (tr.time i)).state y i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcp
  have hhy := witness_height hrun hnc hz hy hQ hh hQy
  rcases witness_frame_at hrun hnc hframe hy hc hlo hhi (quorum_excess hf3) hQy hhy hJ hXQ
    with hXF | ⟨hFX, hXt, hrootX, hQt, hvQ, hXQf⟩
  · have he := (SA.acProposal_head hdp).2
    rw [he]
    exact hXF.trans (((SA.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU).mono subU)
  have hG' : ∀ x ∈ H (tr.time i), ∀ j e', SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      e'.msg.slot = m → SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e'.msg X := by
    intro x hx j e' hv' hs'
    obtain ⟨hjd, hv''⟩ := SA.upTo_voteAt.mp hv'
    exact narrow_vote hrun hnc ht0 hx hv' (hG x j e' (hrun.antitone hjd hx) hv'' hs')
  have hrelay : ∀ x ∈ H (tr.time i), ∀ k ev, SA.VoteAt (tr.projAC.upTo (tr.time i)) x k ev →
      ev.msg.slot = m → ∀ B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)),
        B.root = ev.msg.head →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ell.frame.F B := by
    intro x hx k ev hv' hs' B hB hBr
    obtain ⟨W, hW, hWr, hXW⟩ := hG' x hx k ev hv' hs'
    obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hB (hFX.trans (hXW.mono subU))
  have hrestart : ∀ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ gbar g := by
    intro k hk
    obtain ⟨hkd, hk⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hk
    exact hnr y k (hrun.antitone hkd hy) (Compose.projAC_restartAt.mp hk)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := SA.goldilocksSA sp _ ro) (tr.projAC.upTo (tr.time i)) y k t ≤
        max t (sp.ts m) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts m)
      (fun r _ hrs => (hrestart r hrs).trans hgm) t
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k < sp.ts m :=
    fun k _ hk => (hrestart k hk).trans_lt (by linarith)
  have hhalf := SA.honest_voters_half_before hS hm (show sp.ts m + sp.Δ ≤ tr.time i by linarith)
    (fun x hx r _ hrest => by
      obtain ⟨hrd, hrest⟩ := (ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hrest
      rw [SA.ts_sub_one]
      exact (hnr x r (hrun.antitone hrd hx) (Compose.projAC_restartAt.mp hrest)).trans
        (by linarith))
  have hhalf' : sp.n ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ j e',
      SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m}.ncard := by
    have hle := Set.ncard_le_ncard (s := {x | x ∈ H (tr.time i) ∧ ∃ j e',
      SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m ∧
        (tr.projAC.upTo (tr.time i)).time j ≤ sp.ts m + sp.Δ})
      (t := {x | x ∈ H (tr.time i) ∧ ∃ j e',
        SA.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m})
      (by rintro x ⟨hx, j, e', hv', hs', _⟩; exact ⟨hx, j, e', hv', hs'⟩)
    omega
  have hpre := hrun.upTo ht0
  refine (SA.batch_proposal hS.run hf2 hhalf' hG' hy hcp (SA.proposal_slot hti) hdp
    ⟨hXt, Or.inl ⟨hXt, hrootX, Q, hQt, hvQ, hXQf⟩⟩ ?_ ?_ hstock).mono subU
  · intro x hx k e hv hs
    obtain ⟨W, hW, hWr, -, hp, -, hb⟩ := SA.late_vote_held_of_frame_before hS hy hcp hm
      (show sp.ts m + 2 * sp.Δ ≤ tr.time i by linarith) le_rfl hdl hrs hx hv hs
      (hrelay x hx k e hv hs)
    exact SA.heldAtProposal_iff.mpr ⟨Or.inl hp, W, hW, hWr, hWr ▸ lt_trans hb
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩
  · apply SA.highLocksCompatible_iff.mpr
    intro l hl _ hlm L hL hLr
    have hl' : l ∈ ((tr.upTo (tr.time i)).state y i).ac.locks := by
      have h := Compose.projAC_state hpre.toLocalRun hy i
      rw [RunTrace.upTo_projAC] at h
      rwa [h] at hl
    have hls := Compose.proposal_locks_slot_of hpre (hnc.upTo _) hf2 hy
      (by rw [RunTrace.upTo_projAC]; exact hcp) hcall
      (by rw [RunTrace.upTo_projAC]; exact hdp) hti hstock l hl'
    have heq : l.slot = m := by omega
    obtain ⟨O, hLO, a, CV, hopt⟩ := SA.proposal_high_lock hr hy hti hl hlm hL hLr
    rw [heq] at hopt
    rcases SA.optimisticLock_compatible hS.run hf2 hy hopt hG' hstock with hOX | hXO
    · exact Or.inl (hLO.trans hOX)
    · exact SA.anc_total hr.coherent hLO hXO

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
