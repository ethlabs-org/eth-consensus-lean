module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
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
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the suffix of the proposal walk under windowed service

The core of `Compose/Service/Suffix`, generic in the service start. The leaves read the service as
`SuffixService` (the AC service window from a start `a₀` with the catch-up of older acceptances
before `a₀ + κ ≤ t_{s−1}`), and the voter's facts at `Q` (its `fc_root` below `Q`, its head height
floor at most the height of every block of its tree above `Q`) as premises:

* `relay_mem_window_before`: the acceptance relay into a frame under the window and its catch-up;
* `suffix_agree_of`: on the suffix from the pivot, the proposer's best child is the voter's;
* `old_child_ineligible_of`: no old child of `Q` is eligible at the voter;
* `proposal_at_voter_of`: `P` is in the voter's viable voter block tree;
* `head_slot_lt`, `vote_floor_le_of`: the duty head is below slot `s`, and the head height floor at
  an honest vote is at most the height of every block above the old origins.

`Compose/Service/Suffix` derives its whole-history forms from these at `a₀ = κ = 0`, and the
growing-fault forms apply them on a prefix. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

section Run

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- An accepted block is an honest block. -/
private theorem accepted_honest (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (hk : tr.AcceptAt y k B) :
    B ∈ tr.HonestBlocks H := by
  have h := hrun.toLocalRun
  refine ⟨y, hy, k + 1, ?_⟩
  rw [tr.state_succ_of_call hk,
    (Store.tree_grows _ _ _ _ (fg_reachable h hy _)).1 B _ (h.cutLaw y hy _ _ hk).2.1]
  exact Set.mem_insert _ _
/-- **The acceptance relay into a frame**: a block of the honest blocks that is genesis, or that
an honest node accepted at a time `τ` with `max(τ, a) + Δ` at most the time of a call of an
honest `z` whose restarts up to it are at or before `a`, is in that call's frame when it extends
its `Σ.F`. -/
theorem relay_mem_window_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a₀ κ b : Time} (hsync : SA.ServiceWindowBefore H (tr.HonestBlocks H) a₀ b tr.projAC)
    (hcat : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a₀ κ b)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocks H) {jz : Nat}
    {ℓz : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z jz ℓz)
    (hb : tr.time jz ≤ b) (hκz : a₀ + κ ≤ tr.time jz) {a : Time}
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
  by_cases hka : a₀ ≤ tr.projAC.time kx
  · obtain ⟨k', hk', hAz, -⟩ := hsync.relay x hx kx B hkx hka z hz jz ℓz hcz (hd.trans hb) hd hF
    exact SA.mem_tree_of_acceptAt sp hr hz hAz hk' hcz hF
  · obtain ⟨k', hk', hAz, -⟩ :=
      hcat.relay x hx kx B hkx (lt_of_not_ge hka) z hz jz ℓz hcz hκz hb hF
    exact SA.mem_tree_of_acceptAt sp hr hz hAz hk' hcz hF
/-- **The service of the suffix lemmas** for slot `s`: the AC service window from `a` through `b`,
with the catch-up of older acceptances before `a + κ ≤ t_{s−1}` at calls through `b`. -/
structure SuffixService (H : Set (Fin sp.n)) (tr : GoldilocksTrace sp ro)
    (a κ b : Time) (s : Nat) : Prop where
  window : SA.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC
  caught : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a κ b
  kappa : 0 ≤ κ
  start : a + κ ≤ sp.ts ((s : Int) - 1)

/-- The catch-up is over by every call at or after `t_s`. -/
theorem SuffixService.le_time {a κ b : Time} {s j : Nat}
    (h : SuffixService H tr a κ b s) (hj : sp.ts s ≤ tr.time j) : a + κ ≤ tr.time j :=
  h.start.trans (((SA.ts_le_iff sp).2 (by omega)).trans hj)

/-- **The honest attestations at a vote have old sources** (as `Pivot`'s `vote_fcRoot_old_of`):
every honest attestation an honest slot-`s` voter holds was signed before the vote, with a source
below an origin before the signing (`attestation_source`); a regular one of label `l` is written at
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
    linarith only [htc, this, hjj, htj]
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

/-- **The head height floor at an honest vote is at most the height of a held block above every old
origin** (`floor ≤ ht(D_s)` at the vote reads): the sources of the voter's honest attestations are
below old origins (`vote_rows_old`), so below the block; so there is no contest, and the carrier of
`h_max` crossed `h_max − 1` with such a source, whose entry, below the block, has height
`h_max − 1`. -/
theorem vote_floor_le_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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

/-- **The voter holds the proposal**: an early vote is ready, with a block of slot `s` in its
frame (`SA.cast_ready`), which is `P` (`eq_of_slot`); a vote at `t_s + Δ` follows the relay of
`P`, accepted by its proposer at `t_s`, to the voter (restarted at or before `t_{s−1}`), when `P`
extends the voter's `Σ.F`. -/
private theorem voter_holds_proposal_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a₀ κ b : Time} {s : Nat} (hsync : SuffixService H tr a₀ κ b s)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P)
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
  rw [hes] at ht
  have ht' : sp.ts ((s' + 1 : Nat) : Int) + sp.Δ ≤ tr.time j := not_lt.1 ht
  refine relay_mem_window_before hrun hnc hsync.window hsync.caught hp hy
    (accepted_honest hrun hp hacc) hcy.1 hb (hsync.le_time (by linarith only [ht', hΔ]))
    (honest_vote_restarts hrun hnc hy hcy hes).1
    (Or.inr ⟨k + 1, ⟨ℓ, projAC_callAt.2 hcl, hbl⟩, ?_⟩) hFP
  change max (tr.time (k + 1)) (sp.ts (s' : Int)) + sp.Δ ≤ tr.time j
  rw [htl, htk, max_eq_left (by rw [hts]; linarith only [hΔ])]
  exact ht'
end Run

/-! ### The proposal's cut and payload (for `views_agree_before`) -/

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
theorem head_slot_lt {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
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

omit hsl hpj hcall hd hti hsD hDQ hviab in
/-- **The winner is in the voter's tree**: a child `C` of a block `X` of the suffix that is an
ancestor of `Q` (so of `P`) is in the voter's viable voter block tree. The voter holds `P`
(`voter_holds_proposal_before`), and `C ⪯ P` extends `fc_root` (below the voter's anchor, below
`X`), so `C` is in the voter block tree as an ancestor of the slot-`s` block `P`; and `P` is a
viable head of the voter: every old origin is below `Q` (`proposal_walk_passes_old_before`), so the
floor at the vote is at most the height of `P` (`vote_floor_le_of`). -/
private theorem winner_voter_tree_before {a₀ κ b : Time}
    (hsync : SuffixService H tr a₀ κ b s) (hjb : tr.time j ≤ b)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocks H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h)
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
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
  have hPt := voter_holds_proposal_before hrun hnc hsync hp hP hPs hs0 hy hcy hes hjb
    (hFC.trans hCP)
  have hCt : C ∈ ℓy.frame.tree := SA.frame_mem_of_between sp hU hΦy hΦyU hPt hCP hFC
  have hCPy : ℓy.frame.Anc C P := SA.anc_tree_of_anc_U hU hΦy hΦyU hCt hCP hPt
  have hfP : ℓy.frame.Anc ℓy.frame.fcRoot P :=
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem (hfC.trans hCP) hPt
  refine ⟨⟨hCt, Or.inr ⟨P, hPt, hPs, hCPy⟩⟩,
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfC hCt,
    P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, ?_, hCPy⟩
  -- `P` is a viable head of the voter
  rw [frame_of_projAC hrun hy hcy.1] at hPt hfP ⊢
  exact ⟨hPt.1, hPt.2, Anc.mono (fun X hX => hX.1) hfP, hflQ P hPt.1 hQP⟩

omit hsl hpj hsD hDQ in
/-- **Competitors reflect**: a child `B` of a block `X ≠ Q` of the suffix in the voter's viable
voter block tree is in the proposer's tree, stamped before the freeze (so accepted then, and
relayed to the proposer by `t_s`) or an ancestor of the voter's slot-`s` block `P`, other than
`P` (its parent is not `Q`), so below `Q`; and it is a viable head of the proposer (its height is
at least that of `X`). -/
private theorem competitor_reflect_before {a₀ κ b : Time}
    (hsync : SuffixService H tr a₀ κ b s) (hib : tr.time i ≤ b)
    {X B : SA.Blk sp.n (List (FG.Att sp.n))}
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
      refine relay_mem_window_before hrun hnc hsync.window hsync.caught hy hp hBU hc hib
        (hsync.le_time hti.ge) hrsp ?_ hFB
      rcases frame_anc_accepted hr hy j ℓy hcy.1 B hB.1.1 B .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      by_cases hg : B.root = sp.genesisRoot
      · exact Or.inl hg
      refine Or.inr ⟨kx, hA, ?_⟩
      have hge := blockStamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
      rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
      have hlt := SA.etime_of_lt_of.1 (lt_of_le_of_lt hge hfz)
      have hfr : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
        simp only [SA.freeze, hcast]
      rw [hfr] at hlt
      change _ ≤ tr.time i
      rw [hti, hts]
      have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ from
        le_add_of_nonneg_right (mul_nonneg zero_le_three hΔ.le))
      linarith only [this]
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

omit hsl hpj hcall hti hsD hDQ hviab in
/-- **The voter holds `P`** when its anchor is below a block `X ⪯ Q` of the proposer's tree: then
`Σ.F ⪯ fc_root ⪯ anchor ⪯ X ⪯ P` (`voter_holds_proposal_before`). -/
private theorem voter_holds_before {a₀ κ b : Time}
    (hsync : SuffixService H tr a₀ κ b s) (hjb : tr.time j ≤ b)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hXQ : ℓp.frame.Anc X d.head)
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
  exact voter_holds_proposal_before hrun hnc hsync hp hP hPs hs0 hy hcy hes hjb
    (((hΦy.F_anc_fcRoot.mono hΦyU).trans hfX).trans ((hXQ.mono hΦpU).trans hQP))

omit hsl hpj hsD hDQ hviab in
/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees (`SA.view_agree`,
with the Sleepy relay: a block the voter stamped before the vote freeze reaches the proposer by
`t_s`, and `P`'s support heads reach the voter by its vote, ready or relayed). -/
private theorem views_agree_before {a₀ κ b : Time}
    (hsync : SuffixService H tr a₀ κ b s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hPy : P ∈ ℓy.frame.tree) :
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
  have hj1 : sp.ts ((s' + 1 : Nat) : Int) ≤ tr.time j := by
    have h := (SA.castAt_spec hr hy hcy).2.1
    rw [hes] at h
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [h])
  refine hcast ▸ SA.view_agree_window_before hrun' hp hy hpp ⟨hc, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hPs, hpay⟩ hsync.window (by
      have h := hsync.start
      rw [hcast] at h
      linarith only [h, hsync.kappa]) hib ?_ ?_
  · -- a voter block stamped before the freeze reaches the proposer by `t_s`
    intro Hd hHd hHds hst hFHd
    have hHdU := hΦyU hHd
    refine relay_mem_window_before hrun hnc hsync.window hsync.caught hy hp hHdU hc hib
      (hsync.le_time hti.ge) hrsp ?_ hFHd
    rcases frame_anc_accepted hr hy j ℓy hcy.1 Hd hHd Hd .refl with hg | ⟨kx, hkx, hA⟩
    · exact Or.inl hg
    by_cases hg : Hd.root = sp.genesisRoot
    · exact Or.inl hg
    right
    refine ⟨kx, hA, ?_⟩
    have hge := blockStamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
    rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
    have hlt := SA.etime_of_lt_of.1 (lt_of_le_of_lt hge hst)
    have hfz : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
      simp only [SA.freeze, hcast]
    rw [hfz] at hlt
    rw [hii, hti, hts]
    have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ from
      le_add_of_nonneg_right (mul_nonneg zero_le_three hΔ.le))
    linarith only [this]
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
    · refine relay_mem_window_before hrun hnc hsync.window hsync.caught hp hy (hΦpU hHd) hcy.1 hjb
        (hsync.le_time hj1) hrsy ?_ hFHd
      rcases frame_anc_accepted hr hp i ℓp hc Hd hHd Hd .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      right
      refine ⟨kx, hA, ?_⟩
      have h1 : tr.projAC.time kx ≤ sp.ts ((s' + 1 : Nat) : Int) := by
        rw [← hti]; exact hr.time_mono hkx
      have h2 := max_le h1
        (show sp.ts (s' : Int) ≤ sp.ts ((s' + 1 : Nat) : Int) by rw [hts]; linarith only [hΔ])
      rw [hjj]
      linarith only [h2, not_lt.1 hE]

omit hsl hpj hsD in
/-- **No old child of `Q` is eligible at the voter** (the `X = Q` case of the
leaves): a child `B ≠ P` of `Q` (of a slot below `s`) in the voter's viable voter block tree is
stamped before the vote freeze (it is not an ancestor of the slot-`s` block `P`), so it is in the
proposer's tree, and a viable head there (its height is at least `Q`'s, a proposer viable head);
the proposal walk stopped at `Q`, so `B` has no strict majority in the proposal's view; the views
agree on `B` (`views_agree_before`), and `Q` is a viable head of the voter (`vote_floor_le_of`), so
`B` is ineligible at the voter too. Under the suffix service from `a₀` with its catch-up
(`SuffixService`), given the voter's `fc_root` below `Q` and its head height floor at most the
height of every block of its tree above `Q`. -/
theorem old_child_ineligible_of {a₀ κ b : Time}
    (hsync : SuffixService H tr a₀ κ b s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hfcQ : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocks H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
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
      refine relay_mem_window_before hrun hnc hsync.window hsync.caught hy hp hBU hc hib
        (hsync.le_time hti.ge) hrsp ?_ hFB
      rcases frame_anc_accepted hr hy j ℓy hcy.1 B hB.1.1 B .refl with hg | ⟨kx, hkx, hA⟩
      · exact Or.inl hg
      by_cases hg : B.root = sp.genesisRoot
      · exact Or.inl hg
      refine Or.inr ⟨kx, hA, ?_⟩
      have hge := blockStamp_ge_of_accept hr hy hA hg (j + 1) (by omega)
      rw [Trace.state_succ_of_call _ hcy.1, ← SA.readPoint_blockStamp_eq hr hy hcy] at hge
      have hlt := SA.etime_of_lt_of.1 (lt_of_le_of_lt hge hfz)
      have hfr : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
        simp only [SA.freeze, hcast]
      rw [hfr] at hlt
      change _ ≤ tr.time i
      rw [hti, hts]
      have := max_le hlt.le (show sp.ts (s' : Int) ≤ sp.ts (s' : Int) + 3 * sp.Δ from
        le_add_of_nonneg_right (mul_nonneg zero_le_three hΔ.le))
      linarith only [this]
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
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := hfcQ.trans hQP
  have hPt := voter_holds_proposal_before hrun hnc hsync hp hP hPs hs0 hy hcy hes hjb
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfP)
  have hFQ : Anc (tr.HonestBlocks H) ℓy.frame.F d.head :=
    below _ ((hΦy.rooted.2 B hB.1.1).mono hΦyU) ((hΦy.rooted.2 P hPt).mono hΦyU)
  have hQty : d.head ∈ ℓy.frame.tree := SA.frame_mem_of_between sp hU hΦy hΦyU hPt hQP hFQ
  have hfQy : ℓy.frame.Anc ℓy.frame.fcRoot d.head := SA.anc_tree_of_anc_U hU hΦy hΦyU
    hΦy.fcRoot_mem (below _ (hB.2.1.mono hΦyU) hfP) hQty
  have hQvy : d.head ∈ ℓy.frame.viableHeads := by
    rw [frame_of_projAC hrun hy hcy.1] at hQty hfQy ⊢
    exact ⟨hQty.1, hQty.2, Anc.mono (fun X hX => hX.1) hfQy, hflQ _ hQty.1 .refl⟩
  -- the views agree on `B`
  obtain ⟨heq, hvot, hsup⟩ :=
    views_agree_before hrun hnc hp hP hPs hc hcall hd hti hPQ hy hcy hes hsync hib hjb hPt
  have hsj : sp.slot (tr.time j) = s := ((SA.castAt_spec hr hy hcy).2.1).symm.trans hes
  rintro (h | h | h)
  · exact h ⟨d.head, hQvy, hBQ⟩
  · omega
  · apply hnp
    simp only [SA.goldfishScore] at h ⊢
    rw [hvot, heq, hsup B hBt hB.1.1]
    exact h
end Leaves

/-- **The suffix** under the suffix service from `a₀` with its catch-up (`SuffixService`), given
the voter's head height floor at most the height of every block of its tree above `Q`
(`suffix_agree_before` is the form from `0`). -/
theorem suffix_agree_of {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a₀ κ b : Time} {s : Nat} (hs : SuffixService H tr a₀ κ b s)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) {i : Nat}
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
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocks H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h) :
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
    views_agree_before hrun hnc hp hP hPs hc hcall hd hti hPQ hy hcy hes hs hib hjb
      (voter_holds_before hrun hnc hp hP hPs hc hd hPQ hy hcy hes hs hjb hXQ hanc)
  have hCQ := winner_on_path hrun hnc hp hc hd hti hPQ hsD hDQ hviab hDX hXQ hne hC
  obtain ⟨⟨hCp, -⟩, hCX, -⟩ := hC.1
  have hCy := winner_voter_tree_before hrun hnc hp hP hPs hc hPQ hy hcy hes
    hs hjb hflQ hXQ hanc hCX hCp hCQ
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
    (fun B hB => hB.1.1) hCy (fun B hB hBX =>
      competitor_reflect_before hrun hnc hp hP hPs hc hcall hd hti hPQ hviab hy hcy hes
        hs hib hDX hXQ hne hBX hB) hC

/-- **`P` is in the voter's viable voter block tree** under the suffix service from `a₀` with its
catch-up (`SuffixService`), given the voter's `fc_root` below `Q` and its head height floor at most
the height of every block of its tree above `Q` (`proposal_at_voter_before` is the form from
`0`). -/
theorem proposal_at_voter_of {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a₀ κ b : Time} {s : Nat} (hs : SuffixService H tr a₀ κ b s)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hPQ : P.parent = some d.head.root) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (hjb : tr.time j ≤ b)
    (hfcQ : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocks H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h) :
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
  -- `fc_root` of the voter is below `Q`, so below `P`
  have hfP : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := hfcQ.trans hQP
  have hPt := voter_holds_proposal_before hrun hnc hs
    hp hP hPs hs0 hy hcy hes hjb
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfP)
  have hfPy : ℓy.frame.Anc ℓy.frame.fcRoot P :=
    SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfP hPt
  refine ⟨⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hfPy, P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, ?_,
    .refl⟩
  rw [frame_of_projAC hrun hy hcy.1] at hPt hfPy ⊢
  exact ⟨hPt.1, hPt.2, Anc.mono (fun X hX => hX.1) hfPy, hflQ P hPt.1 hQP⟩
end Consensus.Goldilocks.Compose

end
