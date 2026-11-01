module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Goldilocks under `Sleepy`: the suffix of the proposal walk

workbench#12 §3: on the proposal walk from the pivot `D` to `Q = P.parent`, at every block below
`Q` at or above a voter's anchor, the proposer's best child is the voter's best child. Its pieces:

* `winner_on_path` (proved): the proposer's best child `C` at a block `X ≠ Q` of the walk is on
  the walk, below `Q`;
* `winner_voter_tree` (proved): `C`, an ancestor of `P`, is in the voter's viable voter block
  tree (the voter holds `P`, a viable head there: the floor at the vote is at most the height of
  every block above the old origins, which are below `Q`);
* `competitor_reflect` (proved): for `X ≠ Q`, every child of `X` in the voter's viable voter block
  tree is in the proposer's viable tree (frozen before the vote freeze, so relayed to the proposer
  by `t_s`, or below `Q`; and viable there: heights do not decrease along ancestry and `X` is a
  proposer viable head); at `X = Q` it fails (`P` is not in the proposal's frame);
* `views_agree` (proved): the two views have the same equivocators and voters, and the same
  supporters for every block of both trees (`view_agree`, with the Sleepy relay), once the voter
  holds `P` (`voter_holds`: its anchor is below the block `X ⪯ Q`).

With `X` a proposer viable head (`hviab`) and `C` of a slot below `s`, the best child carries over
(`SA.isBest_transfer`, Lemmas/AC/BestChild): `C` is proposer-eligible only by a strict majority,
so voter-eligible by the same majority (`views_agree`), and a competitor the proposer does not
count has no majority, so its score is below `C`'s. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-! ### Blocks and walks -/

section Walk

variable {FGP : Type}

/-- A descendant inside the tree of a block of the tree is in the tree. -/
private theorem mem_of_anc_left {Φ : SA.Frm sp.n FGP} {A B : SA.Blk sp.n FGP} (h : Φ.Anc A B)
    (hA : A ∈ Φ.tree) : B ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hA
  · exact (Anc.mem h hAB).2

/-- A proper ancestor of a block is an ancestor of its parent. -/
private theorem anc_parent {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {A B Q : SA.Blk sp.n FGP} (h : Anc U A B) (hne : A ≠ B) (hBQ : B.parent = some Q.root)
    (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

end Walk


/-! ### Ancestry in a set -/

section Store

variable {P : Params} {ACP : Type}

/-- An ancestor of a member is a member. -/
private theorem anc_mem {S : Set (NodeBlock P ACP)} {A W : NodeBlock P ACP} (h : Anc S A W)
    (hW : W ∈ S) : A ∈ S := by
  by_cases hne : A = W
  · exact hne ▸ hW
  · exact (Goldilocks.Anc.mem h hne).1

end Store

/-! ### Over a run -/

section Run

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9). -/
private theorem requirements (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- **An honest node accepts its own proposal** (C0.3, under `NoColl`). -/
theorem proposal_accepted (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : tr.AcceptAt p k P := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcall⟩, hpos⟩, -, -⟩ := hP
  rcases blockCall_cases h hp hcall with hg | ⟨j, x, rfl, hg, hpr, d, pay, hdp, hB, hacc, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hp hg
  have hC03 := honest_block_accepted proposer dg p (requirements sp ro) hrun.genesis_root_ok cfg _
    (tr.time (j + 2)) x hreach hstep hpr d pay (by rw [hst]; exact hdp)
  simp only [hst] at hC03
  have key : NoCollOn dg (insert P (tr.state p j).fg.tree) →
      (tr.state p j).fg.blocks P.root = none ∧ ∃ fg', (tr.state p j).fg.onBlock P = some fg' := by
    rw [hB]
    exact hC03.2.2.2.2.2.2
  obtain ⟨-, fg', hon⟩ := key <| hnc.mono <| Set.insert_subset_iff.2
    ⟨Or.inr ⟨p, j + 2, acc, hcall⟩, tree_subset_run h hp j⟩
  obtain rfl : acc = true := hacc.2 ⟨fg', hon⟩
  exact hcall

/-- An accepted block is an honest block. -/
private theorem accepted_honest (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) :
    B ∈ tr.HonestBlocks H := by
  have h := hrun.toLocalRun
  refine ⟨y, hy, k + 1, ?_⟩
  rw [tr.state_succ_of_call hk,
    (Store.tree_grows _ _ _ _ (fg_reachable h hy _)).1 B _ (h.cutLaw y hy _ _ hk).2.1]
  exact Set.mem_insert _ _

/-- **The honest proposal is the only honest block of its slot.** -/
private theorem eq_of_slot (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ tr.HonestBlocks H) (hRs : R.slot = P.slot) :
    R = P := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, rfl, hg, hPr, d, pay, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hpr : P.proposer = proposer P.slot := by
    rw [hpp, hB]
    exact hPr.2.2.symm
  have hs0 : 0 < P.slot := by rw [hB]; exact hPr.1
  obtain ⟨y, hy, i, hRt⟩ := hR
  rcases tree_cases h hy hRt with rfl | ⟨k', -, hk'⟩
  · simp [Params.genesisBlock] at hRs
    omega
  obtain ⟨-, hRpr, -⟩ := accept_facts h hy hk'
  have hRp : R.proposer = p := by rw [hRpr, hRs, ← hpr, hpp]
  obtain ⟨j', -, ⟨acc', hc'⟩, hpos'⟩ := hrun.block_unforgeable y hy k' R ⟨true, hk'⟩ (hRp ▸ hp)
  rw [hRp] at hc'
  rcases blockCall_cases h hp hc' with hg' | ⟨j₀, x', rfl, hg', hPr', d₀, pay₀, -, hB', -⟩
  · exact absurd (by simpa using (hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).2.2.2.1) hpos'
  have ht' : tr.time (j₀ + 2) = sp.toParams.slotTime R.slot := by
    have hs : R.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB']; rfl
    exact hs ▸ hPr'.2.1
  have htt : tr.time (j₀ + 2) = tr.time (j + 2) := by rw [ht', htk, hRs]
  rw [htt] at hg'
  obtain rfl := hrun.tick_unique p hp j₀ j _ ⟨x', hg'⟩ ⟨x, hg⟩
  have := hc'.2.symm.trans hcB.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at this
  exact this.1

private theorem etime_lt {t t' : Time} : SA.ETime.of t < SA.ETime.of t' ↔ t < t' := by
  simp [SA.ETime.of]

private theorem etime_le {t t' : Time} : SA.ETime.of t ≤ SA.ETime.of t' ↔ t ≤ t' := by
  simp [SA.ETime.of]

/-- **A stamp is not earlier than the acceptance** (as `Sleepy/Transport`'s
`stamp_ge_of_accept`). -/
private theorem stamp_ge_of_accept {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {T : SA.SATrace sp (List (FG.Att sp.n)) ro}
    (hr : ACLocalRun (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hk : T.AcceptAt y k B) (hB : B.root ≠ sp.genesisRoot) :
    ∀ c, k + 1 ≤ c → SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root := by
  have hpost : ∀ c (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)), T.CallAt y c ℓ →
      k ≤ c → (ℓ.call = .block B ∨ SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root) →
      SA.ETime.of (T.time k) ≤ (T.post c).blockStamp B.root := by
    intro c ℓ hc hkc hpre
    have hΦ : FrameOK ℓ.frame := by
      rcases hr.frameLaw y hy c ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp : T.post c = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (T.state y c)
        ℓ.frame (T.time c) ℓ.call).1 := by
      rw [he]
    have htk : SA.ETime.of (T.time k) ≤ SA.ETime.of (T.time c) := etime_le.2 (hr.time_mono hkc)
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro y (T.state y c) hΦ (hr.time_nonneg c) ℓ.call
    rw [hp]
    generalize ℓ.call = cl at hpre hblk hoth ⊢
    cases cl with
    | block B' =>
      rw [hblk B' rfl, Function.update_apply]
      split_ifs with h
      · exact htk
      · rcases hpre with hpre | hpre
        · cases hpre
          exact absurd rfl h
        · exact hpre
    | restart =>
      change _ ≤ (SA.acRestart sp ro y (T.state y c) ℓ.frame (T.time c)).1.blockStamp B.root
      rcases ((SA.restart_state sp) (List (FG.Att sp.n)) ro y (T.state y c) ℓ.frame (T.time c) hΦ
        (hr.time_nonneg c)).2.2.2.2.2.2.2.2.2.2 B.root with h | ⟨h, -⟩
      · rw [h]; simp [SA.SAState.initial, hB]
      · rw [h]; exact htk
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    obtain ⟨ℓ, hcl, hcall⟩ := hk
    rw [Trace.state_succ_of_call T hcl]
    exact hpost k ℓ hcl le_rfl (Or.inl hcall)
  | succ c hkc ih =>
    by_cases hn : ∃ ℓ, T.CallAt y c ℓ
    · obtain ⟨ℓ, hcl⟩ := hn
      rw [Trace.state_succ_of_call T hcl]
      exact hpost c ℓ hcl (by omega) (Or.inr ih)
    · rw [Trace.state_succ_of_not T fun ℓ hcl => hn ⟨ℓ, hcl⟩]
      exact ih

/-- **The acceptance relay into a frame**: a block of the honest blocks that is genesis, or that
an honest node accepted at a time `τ` with `max(τ, a) + Δ` at most the time of a call of an
honest `z` whose restarts up to it are at or before `a`, is in that call's frame when it extends
its `Σ.F`. -/
theorem relay_mem_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SyncACBefore H (tr.HonestBlocks H) b tr.projAC)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H) {jz : Nat}
    {ℓz : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z jz ℓz)
    (hb : tr.time jz ≤ b) {a : Time}
    (hrs : ∀ c ≤ jz, tr.projAC.RestartAt z c → tr.projAC.time c ≤ a)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx B ∧
      max (tr.projAC.time kx) a + sp.Δ ≤ tr.projAC.time jz)
    (hF : Anc (tr.HonestBlocks H) ℓz.frame.F B) : B ∈ ℓz.frame.tree := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hz hcz
  rcases hacc with hg | ⟨kx, hkx, hdl⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hz _ _ hcz
    obtain rfl : B = G := hU.1 hBU hGU (hg.trans hGr.symm)
    obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF
    · exact h ▸ hΦ.rooted.1
    · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
  have hd := (ac_deadline_le_of_restarts hrs _).trans hdl
  obtain ⟨k', hk', hAz, -⟩ := hsync.relay x hx kx B hkx (hr.time_nonneg kx)
    z hz jz ℓz hcz (hd.trans hb) hd hF
  exact SA.mem_tree_of_acceptAt sp hr hz hAz hk' hcz hF

/-- Whole-run service specializes the bounded acceptance relay. -/
theorem relay_mem (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H) {jz : Nat}
    {ℓz : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z jz ℓz) {a : Time}
    (hrs : ∀ c ≤ jz, tr.projAC.RestartAt z c → tr.projAC.time c ≤ a)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx B ∧
      max (tr.projAC.time kx) a + sp.Δ ≤ tr.projAC.time jz)
    (hF : Anc (tr.HonestBlocks H) ℓz.frame.F B) : B ∈ ℓz.frame.tree := by
  have hs : tr.SyncBefore H ΔF (tr.time jz) :=
    ⟨hsl.1.deltaF, fun x hx i m hm h0 y hy j hc _ hd =>
      hsl.1.message x hx i m hm h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.block x hx i B hB h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.relay x hx i B hB h0 y hy j hc hd,
      fun x hx i a ha h0 y hy j hc _ hd => hsl.1.attestation x hx i a ha h0 y hy j hc hd⟩
  exact relay_mem_before hrun hnc (syncBefore_projection hrun.toLocalRun hs)
    hx hz hBU hcz le_rfl hrs hacc hF

/-- **The honest rows at a vote have old sources** (as `Pivot`'s `vote_fcRoot_old`): every
honest row an honest slot-`s` voter holds was signed before the vote, with a source below an
origin before the signing (`attestation_source`); a regular one of label `l` is written at
`t_l + 6Δ ≤ t_s + Δ`, so `l ≤ s − 2`; an optimistic one has label at most `s`, and not `s`
(`no_optimistic_before_held_row`). -/
private theorem vote_rows_old (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s) :
    HonestRowsSourced tr H
      (fun D => ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) y j := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ := sp.toParams.hΔ
  have htj : tr.time j ≤ sp.ts ((s' + 1 : Nat) : Int) + sp.Δ :=
    hes ▸ (cast_head_fcRoot hr hy hc).2
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmj, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ⟨C, ?_, hDC⟩, hDs⟩
  have hjj : tr.projAC.time j = tr.time j := rfl
  obtain ⟨z, hz, c, hck, CV, hR | hOp⟩ := originBefore_iff.1 hC
  · refine oldOrigin_iff.2 ⟨z, hz, c, l, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
    obtain ⟨-, ⟨-, -, htc, -⟩, -⟩ := hR
    have := hr.time_mono (show c ≤ j by omega)
    linarith
  · refine oldOrigin_iff.2 ⟨z, hz, c, l, CV, Or.inr ⟨hOp, ?_⟩⟩
    obtain ⟨-, -, -, hsc, -⟩ := id hOp
    have hle := SA.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ j by omega))
    have hsj : sp.slot (tr.projAC.time j) = s' + 1 :=
      (SA.castAt_spec hr hy hc).2.1.symm.trans hes
    rcases Nat.lt_or_ge l (s' + 1) with h | h
    · omega
    obtain rfl : l = s' + 1 := by omega
    exact (no_optimistic_before_held_row_of hrun hnc hf hy hc hes hm hmj hav
      hkm hsg hz hck hOp).elim

/-- **The head height floor at an honest vote is at most the height of a held block above every
old origin** (workbench#12 §2,
`floor ≤ ht(D_s)` at the vote reads): the sources of the voter's honest rows are below old
origins (`vote_rows_old`), so below the block; so there is no contest, and the carrier of `h_max`
crossed `h_max − 1` with such a source, whose entry, below the block, has height `h_max − 1`. -/
private theorem vote_floor_le_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.tree)
    (hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hsrc := vote_rows_old hrun hnc hf hs0 hy hc hes
  have hU := (projFG_localRun hrun hnc).coherent
  have hGB : ∀ D, (∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) →
      Anc (tr.HonestBlocks H) D B := fun D ⟨O, hO, hDO⟩ => hDO.trans (hold O hO)
  rcases floor_or_crossing_scoped hrun hnc hf hy
      (fun X hX a ha hav _ => honestRowsSourced_iff.1 hsrc X hX a ha hav)
      (fun D D' hD hD' => Anc.total hU (hGB D hD) (hGB D' hD'))
      (fun D hD => Or.inl (hGB D hD)) hB with hle | ⟨D, E, -, hD, hDs, hE, -, hEh, -⟩
  · exact hle
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, j, hE⟩ rfl
  have hEB :=
    honest_held_anc hrun hnc hy ((hED.mono (fg_tree_subset_honest hx k)).trans (hGB D hD)) hB
  have := (honest_held_height hrun hnc hy hEB).1
  omega

private theorem vote_floor_le (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.tree)
    (hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h :=
  vote_floor_le_of hrun hnc (two_faults_lt_of_sleepy hsl) hs0 hy hc hes hB hold

/-- **The voter holds the proposal**: an early vote is ready, with a block of slot `s` in its
frame (`SA.cast_ready`), which is `P` (`eq_of_slot`); a vote at `t_s + Δ` follows the relay of
`P`, accepted by its proposer at `t_s`, to the voter (restarted at or before `t_{s−1}`), when `P`
extends the voter's `Σ.F`. -/
private theorem voter_holds_proposal_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time}
    (hsync : SyncACBefore H (tr.HonestBlocks H) b tr.projAC)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hb : tr.time j ≤ b)
    (hFP : Anc (tr.HonestBlocks H) ℓy.frame.F P) : P ∈ ℓy.frame.tree := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  by_cases ht : tr.projAC.time j < sp.ts e.msg.slot + sp.Δ
  · obtain ⟨P', hP't, hP's, -⟩ := SA.cast_ready hr hy hcy ht
    rwa [eq_of_slot hrun hp hP (hΦU hP't) (hP's.trans (hes.trans hPs.symm))] at hP't
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hacc := proposal_accepted hrun hnc hp hP
  obtain ⟨ℓ, hcl, hbl, htl⟩ := accept_next hrun.toLocalRun hp hacc
  have htk : tr.time k = sp.ts ((s' + 1 : Nat) : Int) := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  refine relay_mem_before hrun hnc hsync hp hy (accepted_honest hrun hp hacc) hcy.1 hb
    (honest_vote_restarts hrun hnc hy hcy hes).1
    (Or.inr ⟨k + 1, ⟨ℓ, projAC_callAt.2 hcl, hbl⟩, ?_⟩) hFP
  change max (tr.time (k + 1)) (sp.ts (s' : Int)) + sp.Δ ≤ tr.time j
  rw [hes] at ht
  have ht' : sp.ts ((s' + 1 : Nat) : Int) + sp.Δ ≤ tr.time j := not_lt.1 ht
  rw [htl, htk, max_eq_left (by rw [hts]; linarith)]
  exact ht'

private theorem voter_holds_proposal (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hs0 : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hFP : Anc (tr.HonestBlocks H) ℓy.frame.F P) : P ∈ ℓy.frame.tree := by
  have hs : tr.SyncBefore H ΔF (tr.time j) :=
    ⟨hsl.1.deltaF, fun x hx i m hm h0 y hy j hc _ hd =>
      hsl.1.message x hx i m hm h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.block x hx i B hB h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.relay x hx i B hB h0 y hy j hc hd,
      fun x hx i a ha h0 y hy j hc _ hd => hsl.1.attestation x hx i a ha h0 y hy j hc hd⟩
  exact voter_holds_proposal_before hrun hnc (syncBefore_projection hrun.toLocalRun hs)
    hp hP hPs hs0 hy hcy hes le_rfl hFP

end Run

/-! ### The proposal's cut and payload (for `views_agree`) -/

section Proposal

/-- The duty head of a proposal is in the frame's tree. -/
private theorem head_mem {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {t : Time}
    (hΦ : FrameOK Φ) {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) : d.head ∈ Φ.tree := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact SA.getHead_mem hΦ (fun _ h => h.1) _ _ _ _

/-- The payload of a proposal is the proposer's view of the previous slot's pool. -/
private theorem payload_eq {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    pay = SA.voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- In a tick, the `ac_proposal` cut is at position `1` (C0.4). -/
private theorem tick_proposal_pos {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {x c : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : (Node.exec proposer dg y st t (.tick x)).2[c]? = some (Cut.ac ℓ))
    (hm : ℓ.call = .proposal) :
    c = 1 := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y st t x
  have huc' : ∀ ℓ', Cut.ac ℓ' ∈ uc → ℓ'.call = .toFG := by
    intro ℓ' hm
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp at hm <;> (rw [hm]; exact hlu)
  change (Node.onTick proposer dg y st t x).2[c]? = _ at h
  rw [hcs] at h
  rcases c with _ | c
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    rw [← h, hlt] at hm
    cases hm
  rw [List.getElem?_cons_succ] at h
  rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓ₀, -, hpc⟩
  · rw [huc' ℓ (by simpa using List.mem_of_getElem? h)] at hm
    cases hm
  obtain ⟨rest, rfl, hrest⟩ : ∃ rest, pc = Cut.ac ℓ₀ :: rest ∧
      ∀ ℓ', Cut.ac ℓ' ∈ rest → ℓ'.call ≠ .proposal := by
    rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩
    · exact ⟨[], rfl, by simp⟩
    · exact ⟨_, rfl, by simp⟩
    · refine ⟨_, rfl, fun ℓ'' hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, Cut.ac.injEq, reduceCtorEq, false_or,
        or_false] at hm
      rw [hm, hℓ']
      simp
  rcases c with _ | c
  · rfl
  rw [List.cons_append, List.getElem?_cons_succ] at h
  rcases List.mem_append.1 (List.mem_of_getElem? h) with hm' | hm'
  · exact absurd hm (hrest ℓ hm')
  · rw [huc' ℓ hm'] at hm
    cases hm

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- Two `ac_proposal` cuts of an honest node at one time are one cut (one tick per time). -/
private theorem proposal_cut_unique (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H)
    {i i' : Nat} {ℓ ℓ' : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓ)
    (hc' : tr.projAC.CallAt p i' ℓ') (hm : ℓ.call = .proposal) (hm' : ℓ'.call = .proposal)
    (ht : tr.time i = tr.time i') : i = i' := by
  have hl := hrun.toLocalRun
  obtain ⟨g, e, k, hg, rfl, hk⟩ := call_in_group hl hp (projAC_callAt.1 hc)
  obtain ⟨g', e', k', hg', rfl, hk'⟩ := call_in_group hl hp (projAC_callAt.1 hc')
  obtain ⟨x, rfl⟩ := acProposal_in_tick (List.mem_of_getElem? hk) hm
  obtain ⟨x', rfl⟩ := acProposal_in_tick (List.mem_of_getElem? hk') hm'
  rw [ht] at hg
  obtain rfl := hl.tick_unique p hp g g' _ ⟨x, hg⟩ ⟨x', hg'⟩
  rw [ht] at hk
  rw [tick_proposal_pos hk hm, tick_proposal_pos hk' hm']

/-- **The run's proposal of `P` is `ac_proposal`'s** at `t_s` (as `Service/Agree`'s
`proposal_data`). -/
private theorem proposal_data (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, rfl, hg, hPr, d, pay, hr, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  set t := tr.time (j + 2)
  set st := tr.state p j
  set st1 := (Node.tickStep proposer dg p st t x .acTick).1
  have hcuts : (Node.exec proposer dg p st t (.tick x)).2 =
      (Node.tickStep proposer dg p st t x .acTick).2 ++
      (Node.tickStep proposer dg p st1 t x .proposal).2 ++
      (Node.tickStep proposer dg p
        (Node.tickStep proposer dg p st1 t x .proposal).1 t x .fgUpdate).2 := by
    simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, st1]
  have h0 : (Node.exec proposer dg p st t (.tick x)).2[0]? = some (Node.acCall p st t .tick).2 := by
    rw [hcuts]; simp [Node.tickStep]
  have h1 : (Node.exec proposer dg p st t (.tick x)).2[1]? = some (Node.acProposal st1 t).2.1 := by
    rw [hcuts]
    simp only [Node.tickStep, hPr, ↓reduceIte]
    split <;> simp [Node.acProposal, Node.acCall]
  obtain ⟨hk0, hc0⟩ := List.getElem?_eq_some_iff.1 h0
  obtain ⟨hk1, hc1⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hg.2.1 0 hk0
  obtain ⟨hn1, ht1, -, -, hl1⟩ := hg.2.1 1 hk1
  rw [hc0] at hl0
  rw [hc1] at hl1
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall0 : tr.CallAt p j (Node.acCall p st t .tick).2 := ⟨hn0, hl0⟩
  have hst1 : (tr.state p (j + 1)).ac = st1.ac := by
    rw [tr.state_succ_of_call hcall0]
    obtain ⟨-, hstep, -, -⟩ := hrun.cutLaw p hp j _ hcall0
    rw [ht0] at hstep
    exact (congrArg Prod.fst hstep).symm
  have hts : t = sp.ts s := by
    rw [htk, sp.slotTime_eq, hPs]; rfl
  refine ⟨j + 1, ⟨.proposal, Node.frame st1, []⟩, d, pay, projAC_callAt.2 ⟨hn1, hl1⟩, rfl, ?_,
    ht1.trans hts, by rw [hB]; rfl, by rw [hB]; rfl⟩
  rw [projAC_state h hp, hst1, show tr.time (j + 1) = t from ht1]
  exact hr

/-- The payload of the honest proposal `P` is the payload of any `ac_proposal` call of its
proposer at `t_s`. -/
private theorem proposal_payload_eq (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H)
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) : P.acPayload = pay := by
  obtain ⟨i', ℓ', d', pay', hc', hcall', hd', hti', -, hpay'⟩ := proposal_data hrun hp hP hPs
  obtain rfl := proposal_cut_unique hrun hp hc hc' hcall hcall' (hti.trans hti'.symm)
  obtain rfl : ℓp = ℓ' := by
    have := (projAC_callAt.1 hc).2.symm.trans (projAC_callAt.1 hc').2
    simpa using this
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  rw [hpay', hd'.2]

end Proposal

/-- The duty head of the proposal is below slot `s` (`P`, of slot `s`, is its child). -/
private theorem head_slot_lt {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hPQ : P.parent = some d.head.root) : d.head.slot < s := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  have hPU := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have := hr.coherent.2 d.head (hΦU (head_mem hΦ hd)) P hPU hPQ
  omega

section Leaves

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
  (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
  (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
  {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
  {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
  {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
  (hDQ : ℓp.frame.Anc D d.head)
  (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)

include hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy hcy hes

omit hpj hsD hDQ hviab in
/-- **The winner is in the voter's tree**: a child `C` of a block `X` of the suffix that is an
ancestor of `Q` (so of `P`) is in the voter's viable voter block tree. The voter holds `P`
(`voter_holds_proposal`), and `C ⪯ P` extends `fc_root` (below the voter's anchor, below `X`), so
`C` is in the voter block tree as an ancestor of the slot-`s` block `P`; and `P` is a viable head
of the voter: every old origin is below `Q` (`proposal_passes_old`), so the floor at the vote is
at most the height of `P` (`vote_floor_le`). -/
private theorem winner_voter_tree {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXQ : ℓp.frame.Anc X d.head)
    (hanc : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X)
    (hCX : C.parent = some X.root) (hCp : C ∈ ℓp.frame.tree) (hCQ : ℓp.frame.Anc C d.head) :
    C ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨-, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hCQ hCp
  have hPU : P ∈ tr.HonestBlocks H := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have hQP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hΦpU hQt, hPU, hPQ⟩
  have hs0 : 0 < s := by
    have := hU.2 d.head (hΦpU hQt) P hPU hPQ
    omega
  have hXC : Anc (tr.HonestBlocks H) X C := .single ⟨hΦpU (anc_mem hXQ hQt), hΦpU hCp, hCX⟩
  have hCP : Anc (tr.HonestBlocks H) C P := (hCQ.mono hΦpU).trans hQP
  have hfC : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot C :=
    ((SA.fcRoot_anc_getAnchor hΦy e.readPoint (tr.time j)).mono hΦyU).trans (hanc.trans hXC)
  have hFC : Anc (tr.HonestBlocks H) ℓy.frame.F C := (hΦy.F_anc_fcRoot.mono hΦyU).trans hfC
  have hPt := voter_holds_proposal hrun hnc hsl hp hP hPs hs0 hy hcy hes (hFC.trans hCP)
  have hCt : C ∈ ℓy.frame.tree := SA.frame_mem_of_between sp hU hΦy hΦyU hPt hCP hFC
  have hCPy : ℓy.frame.Anc C P := SA.anc_tree_of_anc_U hU hΦy hΦyU hCt hCP hPt
  have hfP : ℓy.frame.Anc ℓy.frame.fcRoot P :=
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem (hfC.trans hCP) hPt
  refine ⟨⟨hCt, Or.inr ⟨P, hPt, hPs, hCPy⟩⟩,
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfC hCt,
    P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, ?_, hCPy⟩
  -- `P` is a viable head of the voter
  have hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O P := fun O hO =>
    (proposal_walk_passes_old hrun hnc hsl hp hc hcall hd hti O hO).trans hQP
  rw [frame_of_projAC hrun hy hcy.1] at hPt hfP ⊢
  exact ⟨hPt.1, hPt.2, Anc.mono (fun X hX => hX.1) hfP,
    vote_floor_le hrun hnc hsl hs0 hy hcy hes hPt.1 hold⟩

omit hpj hsD hDQ in
/-- **Competitors reflect**: a child `B` of a block `X ≠ Q` of the suffix in the voter's viable
voter block tree is in the proposer's tree, stamped before the freeze (so accepted then, and
relayed to the proposer by `t_s`) or an ancestor of the voter's slot-`s` block `P`, other than
`P` (its parent is not `Q`), so below `Q`; and it is a viable head of the proposer (its height is
at least that of `X`). -/
private theorem competitor_reflect {X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDX : ℓp.frame.Anc D X) (hXQ : ℓp.frame.Anc X d.head) (hne : X ≠ d.head)
    (hBX : B.parent = some X.root)
    (hB : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)) :
    B ∈ ℓp.frame.viableTree ℓp.frame.tree := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨-, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hst, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hst
  have hXt : X ∈ ℓp.frame.tree := SA.mem_of_anc hXQ hQt
  have hPU : P ∈ tr.HonestBlocks H := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have hBU : B ∈ tr.HonestBlocks H := hΦyU hB.1.1
  have hXB : Anc (tr.HonestBlocks H) X B := .single ⟨hΦpU hXt, hBU, hBX⟩
  have hFB : Anc (tr.HonestBlocks H) ℓp.frame.F B := ((hΦp.rooted.2 X hXt).mono hΦpU).trans hXB
  have hBt : B ∈ ℓp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · -- stamped before the freeze: accepted then, and relayed to the proposer by `t_s`
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by
        have := hU.2 d.head (hΦpU hQt) P hPU hPQ
        omega⟩
      have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      have hsi : sp.slot (tr.time i) = s' + 1 := by
        rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
      have hcast : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
      have hrsp := proposal_call_restarts hrun hnc hp hc hcall hd
      rw [hsi, hcast] at hrsp
      refine relay_mem hrun hnc hsl hy hp hBU hc hrsp ?_ hFB
      rcases frame_anc_accepted hr hy j ℓy hcy.1 B hB.1.1 B .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      by_cases hg : B.root = sp.genesisRoot
      · exact Or.inl hg
      refine Or.inr ⟨kx, hA, ?_⟩
      have hge := stamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
      rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
      have hlt := etime_lt.1 (lt_of_le_of_lt hge hfz)
      have hfr : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
        simp only [SA.freeze, hcast]
      rw [hfr] at hlt
      change _ ≤ tr.time i
      rw [hti, hts]
      have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ by linarith)
      linarith
    · -- an ancestor of `P` other than `P`, so of `Q`
      obtain rfl := eq_of_slot hrun hp hP (hΦyU hP't) (hP's.trans hPs.symm)
      have hBP : B ≠ P' := by
        rintro rfl
        exact hne (hU.1 (hΦpU hXt) (hΦpU hQt) (Option.some_injective _ (hBX.symm.trans hPQ)))
      exact SA.frame_mem_of_between sp hU hΦp hΦpU hQt
        (anc_parent hU (hBP'.mono hΦyU) hBP hPQ (hΦpU hQt)) hFB
  -- `B` is a viable head of the proposer: its height is at least that of `X`
  have hXv := hviab X hDX hXQ
  have hfB : ℓp.frame.Anc ℓp.frame.fcRoot B := SA.anc_tree_of_anc_U hU hΦp hΦpU hΦp.fcRoot_mem
    (((hΦp.fcRoot_anc_viableHeads X hXv).mono hΦpU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  rw [frame_of_projAC hrun hp hc] at hXv hBt ⊢
  have hXBs := honest_held_anc hrun hnc hp hXB hBt.1
  exact ⟨hBt.1, hBt.2, hXv.2.2.1.trans hXBs,
    le_trans hXv.2.2.2 (honest_held_height hrun hnc hp hXBs).1⟩

omit hsl hP hPs hpj hcall hy hcy hes in
/-- **The winner is on the walk**: the proposer's best child at a block `X ≠ Q` of the suffix
is an ancestor of `Q`. -/
private theorem winner_on_path {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDX : ℓp.frame.Anc D X) (hXQ : ℓp.frame.Anc X d.head) (hne : X ≠ d.head)
    (hC : SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B} C) :
    ℓp.frame.Anc C d.head := by
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt
    (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hp hc
  have hslot : sp.slot (tr.time i) = s := by
    rw [hti]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  set T := ℓp.frame.viableTree ℓp.frame.tree
  have hT : T ⊆ ℓp.frame.tree := fun B hB => hB.1
  have hhead : d.head = SA.ghost sp T
      (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
      ℓp.frame.tree.ncard d.start := by
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot]
    rfl
  have hw := SA.walkEnd_ghost (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay)
      ((s : Int) - 1)) (el := SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
      ((s : Int) - 1)) hΦ.coherent hT (hΦ.finite.subset hT) (Set.ncard_le_ncard hT hΦ.finite)
    d.start
  rw [← hhead] at hw
  obtain ⟨f, hf, -⟩ := SA.walkEnd_iff.1 (hw.of_anc hΦ.coherent hT (hsD.trans hDX) hXQ)
  cases f with
  | zero => exact absurd hf hne
  | succ f =>
    have h1 : SA.ghost sp T (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1)) 1
        X = C := SA.ghost_succ_of_best 0 X hC
    rw [show f + 1 = 1 + f by omega, SA.ghost_add, h1] at hf
    exact hf ▸ SA.anc_ghost hT f (hT hC.1.1)

omit hpj hcall hti hsD hDQ hviab in
/-- **The voter holds `P`** when its anchor is below a block `X ⪯ Q` of the proposer's tree: then
`Σ.F ⪯ fc_root ⪯ anchor ⪯ X ⪯ P` (`voter_holds_proposal`). -/
private theorem voter_holds {X : SA.Blk sp.n (List (FG.Att sp.n))} (hXQ : ℓp.frame.Anc X d.head)
    (hanc : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X) :
    P ∈ ℓy.frame.tree := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hst, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hst
  have hPU : P ∈ tr.HonestBlocks H := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have hQP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hΦpU hQt, hPU, hPQ⟩
  have hs0 : 0 < s := by
    have := hU.2 d.head (hΦpU hQt) P hPU hPQ
    omega
  have hfX : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot X :=
    ((SA.fcRoot_anc_getAnchor hΦy e.readPoint (tr.time j)).mono hΦyU).trans hanc
  exact voter_holds_proposal hrun hnc hsl hp hP hPs hs0 hy hcy hes
    (((hΦy.F_anc_fcRoot.mono hΦyU).trans hfX).trans ((hXQ.mono hΦpU).trans hQP))

omit hpj hsD hDQ hviab in
/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees (`SA.view_agree`,
with the Sleepy relay: a block the voter stamped before the vote freeze reaches the proposer by
`t_s`, and `P`'s support heads reach the voter by its vote, ready or relayed). -/
private theorem views_agree (hPy : P ∈ ℓy.frame.tree) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        SA.supporters ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) X =
          SA.supporters ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)
            X := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hslt := head_slot_lt hrun hnc hp hP hPs hc hd hPQ
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hacc := proposal_accepted hrun hnc hp hP
  have hPU := accepted_honest hrun hp hacc
  have hpp : p = proposer (s' + 1) := by
    rw [← hPs, ← (accept_facts hrun.toLocalRun hp hacc).2.1, hP.2.1]
  have hpay := proposal_payload_eq hrun hp hP hPs hc hcall hd hti
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsi : sp.slot (tr.time i) = s' + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
  have hcast : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
  obtain ⟨hrsy, -⟩ := honest_vote_restarts hrun hnc hy hcy hes
  have hrsp := proposal_call_restarts hrun hnc hp hc hcall hd
  rw [hsi, hcast] at hrsp
  have hjj : tr.projAC.time j = tr.time j := rfl
  have hii : tr.projAC.time i = tr.time i := rfl
  -- the early votes are ready
  have hready : tr.time j < sp.ts ((s' + 1 : Nat) : Int) + sp.Δ →
      SA.voteReady sp ℓy.frame (s' + 1) := fun h =>
    hes ▸ SA.cast_ready hr hy hcy (by rw [hes]; exact h)
  refine hcast ▸ SA.view_agree hrun' hp hy hpp ⟨hc, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hPs, hpay⟩ (syncAC_of_sleepy hrun hsl ?_) ?_ ?_
  · simp only [SAParams.ts]
    exact mul_nonneg (by linarith) (Int.natCast_nonneg s')
  · -- a voter block stamped before the freeze reaches the proposer by `t_s`
    intro Hd hHd hHds hst hFHd
    have hHdU := hΦyU hHd
    refine relay_mem hrun hnc hsl hy hp hHdU hc hrsp ?_ hFHd
    rcases frame_anc_accepted hr hy j ℓy hcy.1 Hd hHd Hd .refl with hg | ⟨kx, hkx, hA⟩
    · exact Or.inl hg
    by_cases hg : Hd.root = sp.genesisRoot
    · exact Or.inl hg
    right
    refine ⟨kx, hA, ?_⟩
    have hge := stamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
    rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
    have hlt := etime_lt.1 (lt_of_le_of_lt hge hst)
    have hfz : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
      simp only [SA.freeze, hcast]
    rw [hfz] at hlt
    rw [hii, hti, hts]
    have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ by linarith)
    linarith
  · -- a support head of `P` reaches the voter by its vote
    intro x hx Hd hHd hHdr hFHd
    by_cases hE : tr.time j < sp.ts ((s' + 1 : Nat) : Int) + sp.Δ
    · obtain ⟨P', hP't, hP's, hsup⟩ := hready hE
      obtain rfl := eq_of_slot hrun hp hP (hΦyU hP't) (hP's.trans hPs.symm)
      have hxs : x.slot + 1 = s' + 1 := by
        rw [payload_eq hd, hsi, hcast] at hx
        simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hx
        rw [SA.state_pool_slot sp hr hp i s' x hx.1]
      obtain ⟨H', hH't, hH'r, -⟩ := hsup x (by rw [SA.blockSupport, hpay]; exact hx) hxs
      rwa [hU.1 (hΦpU hHd) (hΦyU hH't) (hHdr.trans hH'r.symm)]
    · refine relay_mem hrun hnc hsl hp hy (hΦpU hHd) hcy.1 hrsy ?_ hFHd
      rcases frame_anc_accepted hr hp i ℓp hc Hd hHd Hd .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      right
      refine ⟨kx, hA, ?_⟩
      have h1 : tr.projAC.time kx ≤ sp.ts ((s' + 1 : Nat) : Int) := by
        rw [← hti]; exact hr.time_mono hkx
      have h2 := max_le h1
        (show sp.ts (s' : Int) ≤ sp.ts ((s' + 1 : Nat) : Int) by rw [hts]; linarith)
      rw [hjj]
      linarith [not_lt.1 hE]


omit hpj hsD in
/-- **No old child of `Q` is eligible at the voter** (workbench#12 §3, the `X = Q` case of the
leaves): a child `B ≠ P` of `Q` (of a slot below `s`) in the voter's viable voter block tree is
stamped before the vote freeze (it is not an ancestor of the slot-`s` block `P`), so it is in the
proposer's tree, and a viable head there (its height is at least `Q`'s, a proposer viable head);
the proposal walk stopped at `Q`, so `B` has no strict majority in the proposal's view; the views
agree on `B` (`views_agree`), and `Q` is a viable head of the voter (`vote_floor_le`), so `B` is
ineligible at the voter too. -/
theorem old_child_ineligible {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s) :
    ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hst, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hst
  have hPU : P ∈ tr.HonestBlocks H := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have hBU : B ∈ tr.HonestBlocks H := hΦyU hB.1.1
  have hQB : Anc (tr.HonestBlocks H) d.head B := .single ⟨hΦpU hQt, hBU, hBQ⟩
  have hQP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hΦpU hQt, hPU, hPQ⟩
  have hQBs := hU.2 d.head (hΦpU hQt) B hBU hBQ
  have hs0 : 0 < s := by omega
  have hBP : B ≠ P := by rintro rfl; omega
  -- `B` is not an ancestor of `P`; a common ancestor of `B` and `P` is one of `Q`
  have hnBP : ¬ Anc (tr.HonestBlocks H) B P := fun h => by
    have := (Anc.slot_le hU (anc_parent hU h hBP hPQ (hΦpU hQt))).1
    omega
  have below : ∀ X, Anc (tr.HonestBlocks H) X B → Anc (tr.HonestBlocks H) X P →
      Anc (tr.HonestBlocks H) X d.head := by
    intro X hXB hXP
    by_cases hXe : X = B
    · subst hXe; exact absurd hXP hnBP
    · exact anc_parent hU hXB hXe hBQ (hΦpU hQt)
  -- `B` is in the proposer's tree
  have hFB : Anc (tr.HonestBlocks H) ℓp.frame.F B :=
    ((hΦp.rooted.2 _ hQt).mono hΦpU).trans hQB
  have hBt : B ∈ ℓp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · -- stamped before the freeze: accepted then, and relayed to the proposer by `t_s`
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      have hsi : sp.slot (tr.time i) = s' + 1 := by
        rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
      have hcast : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
      have hrsp := proposal_call_restarts hrun hnc hp hc hcall hd
      rw [hsi, hcast] at hrsp
      refine relay_mem hrun hnc hsl hy hp hBU hc hrsp ?_ hFB
      rcases frame_anc_accepted hr hy j ℓy hcy.1 B hB.1.1 B .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      by_cases hg : B.root = sp.genesisRoot
      · exact Or.inl hg
      refine Or.inr ⟨kx, hA, ?_⟩
      have hge := stamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
      rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
      have hlt := etime_lt.1 (lt_of_le_of_lt hge hfz)
      have hfr : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
        simp only [SA.freeze, hcast]
      rw [hfr] at hlt
      change _ ≤ tr.time i
      rw [hti, hts]
      have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ by linarith)
      linarith
    · -- an ancestor of the slot-`s` block `P`: impossible
      obtain rfl := eq_of_slot hrun hp hP (hΦyU hP't) (hP's.trans hPs.symm)
      exact absurd (hBP'.mono hΦyU) hnBP
  -- `B` is in the proposer's viable tree: its height is at least that of `Q`
  have hQv := hviab d.head hDQ .refl
  have hfB : ℓp.frame.Anc ℓp.frame.fcRoot B := SA.anc_tree_of_anc_U hU hΦp hΦpU hΦp.fcRoot_mem
    (((hΦp.fcRoot_anc_viableHeads _ hQv).mono hΦpU).trans hQB) hBt
  have hBv : B ∈ ℓp.frame.viableTree ℓp.frame.tree := by
    refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
    have hQv' := hQv
    have hBt' := hBt
    rw [frame_of_projAC hrun hp hc] at hQv' hBt' ⊢
    have hQBs' := honest_held_anc hrun hnc hp hQB hBt'.1
    exact ⟨hBt'.1, hBt'.2, hQv'.2.2.1.trans hQBs',
      le_trans hQv'.2.2.2 (honest_held_height hrun hnc hp hQBs').1⟩
  -- the proposal walk stopped at `Q`, so `B` has no majority in the proposal's view
  have hslot : sp.slot (tr.time i) = s := by
    rw [hti]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  set T := ℓp.frame.viableTree ℓp.frame.tree
  have hT : T ⊆ ℓp.frame.tree := fun X hX => hX.1
  have hhead : d.head = SA.ghost sp T
      (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
      ℓp.frame.tree.ncard d.start := by
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot]
    rfl
  have hstop := SA.ghost_stopped hΦp.coherent hT (hΦp.finite.subset hT)
    (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
    (el := SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
    (Set.ncard_le_ncard hT hΦp.finite) d.start
  rw [← hhead] at hstop
  have hnp : ¬ (SA.voters (SA.View.ofLists pay).votes).ncard <
      2 * SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B := fun h =>
    hstop (SA.exists_isBest hΦp (S := {X | X ∈ T ∧ X.parent = some d.head.root ∧
      SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) X})
      (fun X hX => hT hX.1) ⟨B, hBv, hBQ, Or.inr (Or.inr h)⟩ _)
  -- `Q` is a viable head of the voter
  have hold := proposal_walk_passes_old hrun hnc hsl hp hc hcall hd hti
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := by
    rcases vote_fcRoot_old hrun hnc hsl hs0 hy hcy hes with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦyU hΦy.fcRoot_mem) hg hPU
    · exact (hfO.trans (hold O hO)).trans hQP
  have hPt := voter_holds_proposal hrun hnc hsl hp hP hPs hs0 hy hcy hes
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfP)
  have hFQ : Anc (tr.HonestBlocks H) ℓy.frame.F d.head :=
    below _ ((hΦy.rooted.2 B hB.1.1).mono hΦyU) ((hΦy.rooted.2 P hPt).mono hΦyU)
  have hQty : d.head ∈ ℓy.frame.tree := SA.frame_mem_of_between sp hU hΦy hΦyU hPt hQP hFQ
  have hfQy : ℓy.frame.Anc ℓy.frame.fcRoot d.head := SA.anc_tree_of_anc_U hU hΦy hΦyU
    hΦy.fcRoot_mem (below _ (hB.2.1.mono hΦyU) hfP) hQty
  have hQvy : d.head ∈ ℓy.frame.viableHeads := by
    rw [frame_of_projAC hrun hy hcy.1] at hQty hfQy ⊢
    exact ⟨hQty.1, hQty.2, Anc.mono (fun X hX => hX.1) hfQy,
      vote_floor_le hrun hnc hsl hs0 hy hcy hes hQty.1 hold⟩
  -- the views agree on `B`
  obtain ⟨heq, hvot, hsup⟩ :=
    views_agree hrun hnc hsl hp hP hPs hc hcall hd hti hPQ hy hcy hes hPt
  have hsj : sp.slot (tr.time j) = s := ((SA.castAt_spec hr hy hcy).2.1).symm.trans hes
  rintro (h | h | h)
  · exact h ⟨d.head, hQvy, hBQ⟩
  · omega
  · apply hnp
    simp only [SA.goldfishScore] at h ⊢
    rw [hvot, heq, hsup B hBt hB.1.1]
    exact h

end Leaves

/-- **The suffix** (workbench#12 §3; over the leaves above): at every block `X` from the pivot `D`
to `Q` (in the proposer's tree) at or above the voter's anchor, the proposer's best child is the
voter's best child. Only the winner is compared: in reachable runs (sa-fg-model 7f7e660) a
voter-eligible competitor need not be proposer-eligible (the frame moves between the proposal read
and the vote, e.g. `Σ.F` rises to `X` when the node accepts `P`, and every child of `X` becomes
eligible), and competitor scores differ between the views; below the voter's anchor the proposer's
best child can be outside the voter's viable tree. The model finds the voter's winner score strictly
above every competitor's in all of these cases. -/
theorem suffix_agree {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
      X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        SA.IsBest sp (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1))
          {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  intro X hDX hXQ hanc hne C hC
  obtain ⟨heq, hvot, hsup⟩ :=
    views_agree hrun hnc hsl hp hP hPs hc hcall hd hti hPQ hy hcy hes
      (voter_holds hrun hnc hsl hp hP hPs hc hd hPQ hy hcy hes hXQ hanc)
  have hCQ := winner_on_path hrun hnc hp hc hd hti hPQ hsD hDQ hviab hDX hXQ hne hC
  obtain ⟨⟨hCp, -⟩, hCX, -⟩ := hC.1
  have hCy := winner_voter_tree hrun hnc hsl hp hP hPs hc hcall hd hti hPQ hy hcy hes hXQ hanc
    hCX hCp hCQ
  have hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓy.frame.tree →
      SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
          ((s : Int) - 1) B =
        SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B := by
    intro B hBp hBy
    simp only [SA.goldfishScore, heq, hsup B hBp hBy]
  have hCs : C.slot < s := by
    have hle := (Anc.slot_le (SA.frameIn_of_callAt
      (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hp hc).1.coherent hCQ).1
    have := head_slot_lt hrun hnc hp hP hPs hc hd hPQ
    omega
  have hslot : sp.slot (tr.time i) = s := by
    rw [hti]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  exact SA.isBest_transfer (hviab X hDX hXQ) (by omega) hvot hsc (fun B hB => hB.1)
    (fun B hB => hB.1.1) hCy (fun B hB hBX => competitor_reflect hrun hnc hsl hp hP hPs hc hcall hd
      hti hPQ hviab hy hcy hes hDX hXQ hne hBX hB) hC

/-- **`P` is in the voter's viable voter block tree** (workbench#12 §3: `P` extends every
receiving `Σ.F`, so it is accepted by the joined voter before its vote, which waits for a ready
proposal or `t_s + Δ`; it is viable, as an allowed witness above both floors). -/
theorem proposal_at_voter {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hQt : d.head ∈ ℓp.frame.tree := (acProposal_start_anc_head hΦp hd).2 |> fun h =>
    mem_of_anc_left h (acProposal_start_anc_head hΦp hd).1
  have hPU : P ∈ tr.HonestBlocks H := accepted_honest hrun hp (proposal_accepted hrun hnc hp hP)
  have hQP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hΦpU hQt, hPU, hPQ⟩
  have hs0 : 0 < s := by
    have := hU.2 d.head (hΦpU hQt) P hPU hPQ
    omega
  have hold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O P := fun O hO =>
    (proposal_walk_passes_old hrun hnc hsl hp hc hcall hd hti O hO).trans hQP
  -- `fc_root` of the voter is genesis or below an old origin, so below `P`
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := by
    rcases vote_fcRoot_old hrun hnc hsl hs0 hy hcy hes with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦyU hΦy.fcRoot_mem) hg hPU
    · exact hfO.trans (hold O hO)
  have hPt := voter_holds_proposal hrun hnc hsl hp hP hPs hs0 hy hcy hes
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfP)
  have hfPy : ℓy.frame.Anc ℓy.frame.fcRoot P :=
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfP hPt
  refine ⟨⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hfPy, P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, ?_,
    .refl⟩
  rw [frame_of_projAC hrun hy hcy.1] at hPt hfPy ⊢
  exact ⟨hPt.1, hPt.2, Anc.mono (fun X hX => hX.1) hfPy,
    vote_floor_le hrun hnc hsl hs0 hy hcy hes hPt.1 hold⟩

end Consensus.Goldilocks.Compose

end
