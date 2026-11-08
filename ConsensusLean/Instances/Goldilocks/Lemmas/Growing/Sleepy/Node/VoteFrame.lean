module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the frozen witness at a vote

`vote_frame_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, a block `B` held
while honest, compatible with every origin within `b` of label at most `s` and extended by a
slot-`s` vote of a node honest at it, is in the viable tree of the voter block tree or at or below
`fc_root`. The honest rows of the voter's tree are classified at `i` (`2 f < n` at `tr.time i`);
each witnessing head is relayed from its voter, honest at its acceptance, to the voter, honest at
`i`, before the freeze (`honest_head_frozen_at`).

The store geometry runs on the prefix through `tr.time i` for the validators honest then
(`vote_frame_core`, the static `vote_frame_of` with the frozen witnesses as premises), once `B` is
known to be in the voter's frame: `Σ.J` and `Σ.F` are compared with `B` among the blocks held while
honest, and `B` lies between `Σ.F` and a frozen witness. -/

/-! ### Static pieces (copied from `Compose/Sleepy/FrameLabels`, private) -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}


/-- **Sources at a vote have labels at most `s`** (R4):
at an honest slot-`(s+1)` vote, every honest attestation on a block the voter holds has
a source below an origin of label at most `s`. A regular origin of label `l` is written at
`t_l + 6Δ`, after the vote unless `l < s`; an optimistic one of label `l ≥ s + 2` after
`t_{s+2}`; label `s + 1` is `no_optimistic_before_held_row`. -/
private theorem vote_row_source (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C j, OriginBefore tr H C j i ∧ j ≤ s ∧ Anc (tr.HonestBlocks H) D C := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨m, hmi, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, hDU, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  obtain ⟨z, hz, c, hck, CV, hRO⟩ := originBefore_iff.1 hC
  refine ⟨D, hDU, hDs, C, l, originBefore_iff.2 ⟨z, hz, c, by omega, CV, hRO⟩, ?_, hDC⟩
  -- the vote is cast by `t_{s+1} + Δ`, after the origin's event
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hci : tr.time c ≤ tr.time i := hrun.time_mono (by omega)
  by_contra hl
  have hl' : (s : Int) + 1 ≤ (l : Int) := by exact_mod_cast Nat.lt_of_not_le hl
  rcases hRO with ⟨ℓR, ⟨-, -, htR, -⟩, -⟩ | hO
  · -- a regular origin of label `l > s` is written at `t_l + 6Δ ≥ t_{s+1} + 6Δ`
    have htR' : tr.time c = sp.ts (l : Int) + 6 * sp.Δ := htR
    simp only [SAParams.ts] at htR' hti
    linarith only [htR', hti, hci, hΔ, mul_le_mul_of_nonneg_left hl' hΔ.le]
  · rcases Nat.lt_or_ge l (s + 2) with hl2 | hl2
    · obtain rfl : l = s + 1 := by omega
      exact no_optimistic_before_held_row_of hrun hnc hf hy hc hs hm hmi hav hkm hsg hz hck hO
    · -- an optimistic origin of label `l ≥ s + 2` is selected from `t_l ≥ t_s + 8Δ` on
      obtain ⟨ℓO, A, -, hslot, -⟩ := hO
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) (l : Int)).2
        (le_of_eq (by rw [hslot]))
      have h' : sp.ts (l : Int) ≤ tr.time c := h
      have hl2' : (s : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl2
      simp only [SAParams.ts] at h' hti
      linarith only [h', hti, hci, hΔ, mul_le_mul_of_nonneg_left hl2' hΔ.le]

/-- **S3 at votes, over sources `G`, with the frozen witnesses given**: `vote_frame_of` with the
relays of the honest heads (`honest_head_frozen`) replaced by their conclusions, for `B` and for
the crossing sources. -/
private theorem vote_frame_core (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    (hGW : ∀ D, G D → Anc (tr.HonestBlocks H) ℓ.frame.F D →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) D W)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : Anc (tr.HonestBlocks H) ℓ.frame.F B →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) B W) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hfr := frame_of_projAC hrun hy hc.1
  have hΦ : FrameOK ℓ.frame := by
    rw [hfr]; exact (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rw [hfr]; exact fun X hX => ⟨y, hy, i, hX.1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `Σ.J`, `Σ.F` and `fc_root` are compatible with `B`
  have hJ := J_compatible hrun hnc hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.2.1).mono
      hsU
    rcases hJ with h | h
    · exact Or.inl (hFJ.trans h)
    · exact Anc.total hU hFJ h
  have hfc : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  have hv := vote_viable hrun hnc hy hc (B := B) ⟨hF, hJ⟩
  rw [hs] at hv
  apply hv
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  left
  have hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
  -- the relayed honest slot-`s` head extending `B`
  obtain ⟨W, hW, hBW⟩ := hw hFB
  have hWt : W ∈ (tr.state y i).fg.tree := by
    have := hW.1; rw [hfr] at this; exact this.1
  have hBW' := honest_held_anc hrun hnc hy hBW hWt
  have hBt := anc_mem hBW' hWt
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt with hle | ⟨D, E, X, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact ⟨W, hW, hBW, hle.trans (honest_held_height hrun hnc hy hBW').1⟩
  · -- the honest head of a vote extending the crossing source
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    have hFD : Anc (tr.HonestBlocks H) ℓ.frame.F D := hFB.trans ((hBE.mono hsU).trans hEDU)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD hFD
    have hW't : W' ∈ (tr.state y i).fg.tree := by
      have := hW'.1; rw [hfr] at this; exact this.1
    have hEW' := honest_held_anc hrun hnc hy (hEDU.trans hDW') hW't
    refine ⟨W', hW', (hBE.mono hsU).trans (hEDU.trans hDW'), ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    rw [← hEh]
    exact (honest_held_height hrun hnc hy hEW').1

end Consensus.Goldilocks.Compose

/-! ### Under growing faults -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem add_mul_delta_le {x a b : Time} (h : a ≤ b) : x + a * sp.Δ ≤ x + b * sp.Δ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right h sp.toParams.hΔ.le)

/-- At a slot-`(s+1)` vote of a node honest at its cut `i`, the voter's restarts up to the vote were
at or before `t_s`, and the vote is cast from `t_s + 4Δ` on (`honest_vote_restarts` on the prefix
through `tr.time i`). -/
theorem honest_vote_restarts_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat} {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.projAC.RestartAt y c → tr.time c ≤ sp.ts s) ∧
      sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  obtain ⟨h1, h2⟩ := honest_vote_restarts (hrun.upTo (hrun.time_nonneg i)) (hnc.upTo _) hy
    (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hc⟩) hs
  refine ⟨fun c hci hr => h1 c hci ?_, h2⟩
  rw [RunTrace.upTo_projAC]
  exact (ac_restartAt_upTo _).mpr ⟨hrun.time_mono hci, hr⟩

/-- **A head of a slot at most `s`, of a vote of a node honest at it, is accepted before the
freeze** by a slot-`(s+1)` voter honest at its cut whose `Σ.F` it extends: its voter accepted it
(or it is genesis) while honest, by `t_s + Δ`, and the service relays the acceptance to the voter
by `t_s + 2Δ`. -/
private theorem honest_head_accepted_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {s : Nat}
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e')
    (hs' : e'.msg.slot ≤ s) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocksAt H) (hHdr : Hd.root = e'.msg.head)
    (hFHd : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    SA.AcceptedBefore tr.projAC y Hd (sp.ts s + 3 * sp.Δ) := by
  have hm := hrun.time_mono
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hx, ℓ', hcx, hex⟩ := hVoteAt_iff.1 hv
  -- the head is in its voter's tree, and the vote is cast by `t_m + Δ ≤ t_s + Δ`
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩
  rw [frame_of_projAC_at hrun hx hcx] at hHd't
  obtain rfl : Hd = Hd' :=
    (hU.1 (mem_honestBlocksAt hrun hx hHd't.1) hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts s + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 : sp.ts (e'.msg.slot : Int) ≤ sp.ts (s : Int) := by
      unfold SAParams.ts
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs') (mul_nonneg (by norm_num) hΔ.le)
    exact h1.trans (add_le_add h2 le_rfl)
  obtain ⟨hrs, hti⟩ := honest_vote_restarts_at hrun hnc hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s := fun c hc' ⟨ℓr, hcr, hrr⟩ =>
    hrs c hc' ⟨ℓr, projAC_callAt.2 hcr, hrr⟩
  -- its voter accepted it while honest (or it is genesis), on the prefix through `tr.time k`
  have hdk := hrun.time_nonneg k
  have hstk : (tr.upTo (tr.time k)).state x k = tr.state x k := RunTrace.upTo_state_of_le hm le_rfl
  have hHdx := hHd't.1
  rw [← hstk, ← store_eq (hrun.upTo hdk) hx k] at hHdx
  rcases Store.tree_accepted (projFG_localRun (hrun.upTo hdk) (hnc.upTo _)) hx hHdx with
    hg | ⟨m, -, hA⟩
  · exact Or.inl (by rw [hg]; rfl)
  obtain ⟨hmd, hA⟩ := (RunTrace.upTo_acceptAt tr).mp (projFG_callAt.1 hA)
  have hxm : x ∈ H (tr.time m) := hrun.antitone hmd hx
  have hmt : tr.time m ≤ sp.ts s + sp.Δ := hmd.trans hkt'
  have hFy : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Hd := by
    rw [frame_of_projAC_at hrun hy hc.1] at hFHd; exact hFHd
  have hdl : ∀ c ≤ i, tr.deadline y c (tr.time m) sp.Δ ≤ sp.ts s + 2 * sp.Δ := fun c hc' => by
    have := deadline_le_of_restarts (fun k hk hr' => hrs' k (hk.trans hc') hr') (tr.time m) sp.Δ
    refine this.trans ?_
    rw [two_mul, ← add_assoc]
    exact add_le_add (max_le hmt (le_add_of_nonneg_right hΔ.le)) le_rfl
  have hdi : tr.deadline y i (tr.time m) sp.Δ ≤ tr.time i :=
    (hdl i le_rfl).trans ((add_mul_delta_le (by norm_num)).trans hti)
  -- the service relays the acceptance to `y` before `t_s + 2Δ`
  obtain ⟨k', hk'i, hAy, hk't⟩ := hsync.relay x m Hd hxm hA (hrun.time_nonneg m) y i hy
    ⟨_, projAC_callAt.1 hc.1⟩ (hdi.trans hib) hdi hFy
  have hk'd : tr.time k' ≤ tr.time i := hm hk'i
  obtain ⟨ℓy, hcy, hby, hty⟩ := accept_next (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
    ((RunTrace.upTo_acceptAt tr).mpr ⟨hk'd, hAy⟩)
  obtain ⟨-, hcy⟩ := (Trace.upTo_callAt tr).mp hcy
  have hty' : tr.time (k' + 1) = tr.time k' := hty
  have hk't' : tr.time k' < tr.deadline y k' (tr.time m) sp.Δ := hk't
  have := hdl k' hk'i
  exact Or.inr ⟨k' + 1, ⟨ℓy, projAC_callAt.2 hcy, hby⟩, by
    change tr.time (k' + 1) < _; rw [hty']
    exact hk't'.trans_le (this.trans (add_mul_delta_le (by norm_num)))⟩

/-- **A head of a slot at most `s`, of a vote of a node honest at it, is in the voter block tree**
of a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, when it extends the voter's `Σ.F`
(`honest_head_frozen` with each node honest at its own events: the head's voter at its acceptance,
the voter at `i`). -/
theorem honest_head_frozen_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {s : Nat}
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e')
    (hs' : e'.msg.slot ≤ s) {Z : SA.Blk sp.n (List (FG.Att sp.n))}
    (hZ : SA.VoteExtends (tr.HonestBlocksAt H) e'.msg Z)
    (hFZ : Anc (tr.HonestBlocksAt H) ℓ.frame.F Z) :
    ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocksAt H) Z W := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨Hd, hHd, hHdr, hZHd⟩ := hZ
  have hFHd := hFZ.trans hZHd
  have hacc := honest_head_accepted_at hrun hnc hsync hy hc hs hib hv hs' hHd hHdr hFHd
  have hT : sp.ts s + 3 * sp.Δ ≤ tr.time i := by
    linarith [(honest_vote_restarts_at hrun hnc hy hc hs).2]
  have hΦ := (frameIn_at hrun hnc hy hc.1).1
  -- the head is in the prefix's honest blocks through `tr.time i`
  have hHdp : Hd ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := by
    rcases hacc with hg | ⟨k', hk', hk't⟩
    · have hFp := frame_upTo_at hrun hnc hy hc.1 hΦ.rooted.1
      have hG := (honest_genesis_anc (hrun.upTo hd) hFp).1
      rwa [honestAt_eq_genesis hrun hU hHd hg]
    · have hk'd : tr.time k' ≤ tr.time i := hk't.le.trans hT
      have hk'' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k' Hd :=
        (ac_acceptAt_upTo _).mpr ⟨hk'd, hk'⟩
      obtain ⟨ℓk, hck, -⟩ := hk'
      exact mem_upTo_of_frame hrun hy hk'd hck
        ((SA.accept_new sp (acRun_upTo hrun hnc hd).localRun hy hk'').1 ℓk
          ((Trace.upTo_callAt_of_le tr.projAC hk'd).mpr hck))
  have h := accepted_voter_tree (hrun.upTo hd) (hnc.upTo _) hy
    (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hc⟩) hs hHdp
    (by
      rw [RunTrace.upTo_projAC]
      exact hacc.imp_right fun ⟨k', hk', hk't⟩ =>
        ⟨k', (ac_acceptAt_upTo _).mpr ⟨hk't.le.trans hT, hk'⟩, hk't⟩)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdp hFHd)
  exact ⟨Hd, h, hZHd⟩

/-- **S3 at votes under growing faults (the frozen witness)**. -/
theorem vote_frame_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (_hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b)
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hf := hB.two (tr.time i) hd hib
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hrun' := hrun.upTo hd
  have hnc' := hnc.upTo (tr.time i)
  have hUp := (projFG_localRun hrun' hnc').coherent
  have hst : (tr.upTo (tr.time i)).state y i = tr.state y i := RunTrace.upTo_state_of_le hm le_rfl
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e := by
    rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hΦ := frameIn_at hrun hnc hy hc.1
  have hfr := frame_of_projAC_at hrun hy hc.1
  -- the origins of the prefix of labels at most `s`, and the sources below them
  let Q : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun C =>
    ∃ j, Compose.OriginWithin (tr.upTo (tr.time i)) (H (tr.time i)) C j (tr.time i) ∧ j ≤ s
  have hQ : ∀ C, Q C → OriginWithin tr H C s b ∨ ∃ j, OriginWithin tr H C j b ∧ j ≤ s :=
    fun C ⟨j, hC, hj⟩ => Or.inr ⟨j, (originWithin_of_upTo hrun hC).mono hib, hj⟩
  have hQU : ∀ C, Q C → C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    fun C ⟨_, hC, _⟩ => originWithin_upTo_mem hrun hnc hd hC
  have hQQ : ∀ C C', Q C → Q C' →
      Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) C C' := by
    intro C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩
    exact compatible_upTo hrun hnc hd (originWithin_upTo_mem hrun hnc hd hC)
      (originWithin_upTo_mem hrun hnc hd hC')
      (originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega)
        ((originWithin_of_upTo hrun hC).mono hib) ((originWithin_of_upTo hrun hC').mono hib))
  have hQB : ∀ C, Q C → Compatible (tr.HonestBlocksAt H) B C := fun C ⟨j, hC, hj⟩ =>
    hBc C j ((originWithin_of_upTo hrun hC).mono hib) hj
  let G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D =>
    ∃ C, Q C ∧ Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D C
  have hsrc : Compose.HonestRowsSourced (tr.upTo (tr.time i)) (H (tr.time i)) G y i := by
    rw [Compose.honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun' hnc' hf hy hc' hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within fun k hk => hm hk.le, hj⟩, hDC⟩, hDs⟩
  -- `Σ.J` and `Σ.F` are compatible with `B` among the blocks held while honest
  have hR := fg_reachable hrun'.toLocalRun hy i
  have hJp : ((tr.upTo (tr.time i)).state y i).fg.J ∈
      (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨y, hy, i, (Store.cache_invariants _ _ _ _ hR).2.1⟩
  rw [hst] at hJp
  have hJ : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J B := by
    by_cases h0 : (tr.state y i).fg.hj = 0
    · have hg := justified_genesis hrun' (i := i) (by rw [hst]; exact h0) hy
      rw [hst] at hg
      rw [hg]
      exact Or.inl (honestAt_genesis_anc hrun hBU).2
    obtain ⟨-, -, D, ⟨C, hCQ, hDC⟩, hDs⟩ :=
      justified_honest_source_before hrun' hnc' hf hy hsrc (by rw [hst]; omega)
    rw [hst] at hDs
    obtain ⟨x₀, hx₀, k₀, -, -, hJD, -, -⟩ := honest_source_entry hrun' hnc' hDs hJp rfl
    have hJC : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J C :=
      Anc.mono hsub ((hJD.mono (fg_tree_subset_honest hx₀ k₀)).trans hDC)
    rcases hQB C hCQ with h | h
    · exact Anc.total hU hJC h
    · exact Or.inl (hJC.trans h)
  have hF : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ hR).2.2.1).mono
      (fg_tree_subset_honest (tr := tr.upTo (tr.time i)) hy i)
    rw [hst] at hFJ
    rcases hJ with h | h
    · exact Or.inl ((hFJ.mono hsub).trans h)
    · exact Anc.total hU (hFJ.mono hsub) h
  have hfc : Compatible (tr.HonestBlocksAt H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  -- `B` lies between `Σ.F` and a frozen witness, so it is in the voter's frame
  have hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B :=
    (Anc.mono hΦ.2 hΦ.1.F_anc_fcRoot).trans hfB
  obtain ⟨x, k, e', hv, hs', hext⟩ := hw
  obtain ⟨W, hW, hBW⟩ := honest_head_frozen_at hrun hnc hsync hy hc hs hib hv hs'.le hext hFB
  have hBt := SA.frame_mem_of_between sp hU hΦ.1 hΦ.2 hW.1 hBW hFB
  have hBp := frame_upTo_at hrun hnc hy hc.1 hBt
  -- the store geometry on the prefix
  have hGG : ∀ D D', G D → G D' →
      Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D D' := by
    rintro D D' ⟨C, hC, hDC⟩ ⟨C', hC', hDC'⟩
    rcases hQQ C C' hC hC' with h | h
    · exact Anc.total hUp (hDC.trans h) hDC'
    · exact Anc.total hUp hDC (hDC'.trans h)
  have hGB : ∀ D, G D → Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) D B := by
    rintro D ⟨C, hC, hDC⟩
    rcases compatible_upTo hrun hnc hd hBp (hQU C hC) (hQB C hC) with h | h
    · exact Anc.total hUp hDC h
    · exact Or.inl (hDC.trans h)
  have h := vote_frame_core hrun' hnc' hf hy hc' hs (by rw [hst]; exact hsrc.above _) hGG
    (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ hFD => by
      obtain ⟨x', k', e'', hv', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
        honest_supporter_at hrun hnc (hsync.toFrom hrun) hB (Nat.zero_le _)
          (ts_natCast_nonneg _) ((originWithin_of_upTo hrun hC).mono hib)
      obtain ⟨W', hW', hDW'⟩ := honest_head_frozen_at hrun hnc hsync hy hc hs hib hv'
        (by omega) ⟨Hd, hHd, hHdr, (hDC.mono hsub).trans hCHd⟩ (hFD.mono hsub)
      exact ⟨W', hW', RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd
        (frame_upTo_at hrun hnc hy hc.1 hW'.1) hDW'⟩)
    hBp hGB
    (fun _ => ⟨W, hW, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd
      (frame_upTo_at hrun hnc hy hc.1 hW.1) hBW⟩)
  exact h.imp_right (·.mono hsub)

end Consensus.Goldilocks.Compose.Growing

end
