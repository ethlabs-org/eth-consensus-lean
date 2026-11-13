module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.PivotWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the suffix of the proposal walk

The growing-fault forms of `Compose/Service/Suffix`: at a slot-`s` vote of a node honest then,
with the proposer honest at `t_s + Δ` (the hold, so at the vote, which is cast by `t_s + Δ`), the
proposer's best child on the suffix from the pivot is the voter's (`suffix_agree_at`), no old
child of `Q` is eligible at the voter (`old_child_ineligible_at`), and `P` is in the voter's
viable voter block tree (`proposal_at_voter_at`).

The forms of `Compose/Service/Suffix` under the suffix service (`suffix_agree_of`,
`old_child_ineligible_of`, `proposal_at_voter_of`) name only the proposer and the voter, at cuts up
to the vote. They are applied to the prefix through the vote's time `d`, with the service through
`min b d` and `2 f_d < n`; the genesis forms (`*_at`) and the seeded forms (`*_from`) share them. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The premises of the suffix lemmas, read in the prefix through the time `d` of a slot-`s` vote
(the proposer honest at `t_s + Δ`, the voter at its vote), under the service from `a` with its
catch-up before `a + κ ≤ t_{s−1}`: the proposer and the voter are honest at `d`, the proposal and
the vote are calls of the prefix, the service runs through `min b d`, and the voter's `fc_root`
and head height floor are bounded by `Q` inside the prefix's honest blocks. -/
private theorem suffix_lift_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hs : a + κ ≤ sp.ts ((s : Int) - 1))
    (hfcQ : Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h) :
    0 ≤ tr.time j ∧ tr.time i ≤ tr.time j ∧ p ∈ H (tr.time j) ∧
      (tr.upTo (tr.time j)).ProposesAt p k P ∧
      (tr.upTo (tr.time j)).projAC.CallAt p i ℓp ∧
      (SA.acProposal sp ((tr.upTo (tr.time j)).projAC.state p i) ℓp.frame (tr.time i)).2 =
        some (d, pay) ∧
      SA.CastAt (tr.upTo (tr.time j)).projAC y j ℓy e ∧
      Compose.SuffixService (H (tr.time j)) (tr.upTo (tr.time j)) a κ (min b (tr.time j)) s ∧
      Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) ℓy.frame.fcRoot d.head ∧
      ∀ B ∈ ((tr.upTo (tr.time j)).state y j).fg.tree,
        Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) d.head B →
        ((tr.upTo (tr.time j)).state y j).fg.headHeightFloor ≤
          (((tr.upTo (tr.time j)).state y j).fg.σ B.root).h := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have h0 := hrun.time_nonneg j
  have hsub := upTo_subset hrun h0
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hj1 : sp.ts s ≤ tr.time j := by
    have h := (castAt_spec_at hrun hnc hy hcy).2.1
    rw [hes] at h
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← h])
  have hij : tr.time i ≤ tr.time j := hti ▸ hj1
  have hpj : p ∈ H (tr.time j) := hrun.antitone hjt hp
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  have hkt : tr.time k = sp.ts s := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  obtain ⟨hΦp, -⟩ := frameIn_at hrun hnc hpi hc
  have hQt : d.head ∈ ℓp.frame.tree := (acProposal_start_anc_head hΦp hd).2 |> fun h =>
    mem_of_anc_left h (acProposal_start_anc_head hΦp hd).1
  have hQP := mem_upTo_of_frame hrun hpj hij hc hQt
  have hst : (tr.upTo (tr.time j)).state y j = tr.state y j :=
    Trace.upTo_state tr y fun k hk => hm hk.le
  refine ⟨h0, hij, hpj,
    ⟨(RunTrace.upTo_ownBlockAt tr).mpr ⟨hkt.trans_le hj1, hP.1⟩, hP.2.1, hP.2.2⟩,
    ?_, ?_, ?_, ⟨hsync.acWindow_upTo hrun h0,
      ⟨fun x hx i' B hB hia z hz j' ℓ hc' hj' hjd' hF => ?_⟩, hsync.kappa, hs⟩,
    RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hQP hfcQ, fun B hB hQB => ?_⟩
  · rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le tr.projAC hij).mpr hc
  · rw [RunTrace.upTo_projAC, projAC_upTo_state hrun hij]; exact hd
  · rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩
  · rw [RunTrace.upTo_projAC] at hB hc' ⊢
    obtain ⟨hid, hB⟩ := (ac_acceptAt_upTo _).mp hB
    obtain ⟨hjd, hc'⟩ := (Trace.upTo_callAt _).mp hc'
    obtain ⟨k', hkj, hk, hkt'⟩ := hsync.acOld x i' B (hrun.antitone hid hx) hB hia z j' ℓ
      (hrun.antitone hjd hz) hc' hj' (hF.mono hsub)
    exact ⟨k', hkj.le, (ac_acceptAt_upTo _).mpr ⟨(hm hkj.le).trans hjd, hk⟩, hkt'⟩
  · rw [hst] at hB ⊢
    exact hflQ B hB (hQB.mono hsub)

/-- The voter's `fc_root` and head height floor are bounded by `Q`, and `0 < s`, from the old
origins (the genesis case): every old origin of the prefix through the vote is below `Q`
(`proposal_walk_passes_old_at`), so `fc_root` is genesis or below `Q` (`vote_fcRoot_old_of`) and
the floor is at most the height of every block above `Q` (`vote_floor_le_of`). -/
private theorem genesis_voter_facts (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hstock : sp.committeeSize = sp.n) :
    0 < s ∧ Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot d.head ∧
      ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) d.head B →
        (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have h0 := hrun.time_nonneg j
  have hsub := upTo_subset hrun h0
  have hU := honestBlocksAt_coherent hrun hnc
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hj1 : sp.ts s ≤ tr.time j := by
    have h := (castAt_spec_at hrun hnc hy hcy).2.1
    rw [hes] at h
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← h])
  have hij : tr.time i ≤ tr.time j := hti ▸ hj1
  have hpj : p ∈ H (tr.time j) := hrun.antitone hjt hp
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  have hkt : tr.time k = sp.ts s := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  obtain ⟨hΦy, hΦyU⟩ := frameIn_at hrun hnc hy hcy.1
  have hQt : d.head ∈ ℓp.frame.tree := (acProposal_start_anc_head hΦp hd).2 |> fun h =>
    mem_of_anc_left h (acProposal_start_anc_head hΦp hd).1
  have hQP := mem_upTo_of_frame hrun hpj hij hc hQt
  have hst : (tr.upTo (tr.time j)).state y j = tr.state y j :=
    Trace.upTo_state tr y fun k hk => hm hk.le
  have hf := hB.two _ h0 hjb
  have hold := proposal_walk_passes_old_at hrun hnc hsync hB hinv hpi hc hcall hd hti hib hstock
  have hold' : ∀ O, Compose.OldOrigin (tr.upTo (tr.time j)) (H (tr.time j)) s O →
      Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) O d.head := fun O hO =>
    RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hQP (hold O (oldOrigin_of_upTo hrun hO))
  have hP' : (tr.upTo (tr.time j)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).mpr ⟨hkt.trans_le hj1, hP.1⟩, hP.2.1, hP.2.2⟩
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt p i ℓp := by
    rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le tr.projAC hij).mpr hc
  have hd' : (SA.acProposal sp ((tr.upTo (tr.time j)).projAC.state p i) ℓp.frame
      (tr.time i)).2 = some (d, pay) := by
    rw [RunTrace.upTo_projAC, projAC_upTo_state hrun hij]; exact hd
  have hcy' : SA.CastAt (tr.upTo (tr.time j)).projAC y j ℓy e := by
    rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩
  have hs0 : 0 < s := by
    have := Compose.head_slot_lt (hrun.upTo h0) (hnc.upTo _) hpj hP' hPs hc' hd' hPQ
    omega
  refine ⟨hs0, ?_, fun B hB hQB => ?_⟩
  · rcases Compose.vote_fcRoot_old_of (hrun.upTo h0) (hnc.upTo _) hf hs0 hy hcy' hes hstock
      with hg | ⟨O, hO, hfO⟩
    · exact honestAt_genesis_root_anc hrun hU (hΦyU hΦy.fcRoot_mem) hg (hΦpU hQt)
    · exact Anc.mono hsub (hfO.trans (hold' O hO))
  · have hBP : B ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) :=
      ⟨y, hy, j, by rw [hst]; exact hB⟩
    have h := Compose.vote_floor_le_of (hrun.upTo h0) (hnc.upTo _) hf hs0 hy hcy' hes
      (by rw [hst]; exact hB) (fun O hO =>
        (hold' O hO).trans (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hBP hQB))
      hstock
    rwa [hst] at h

/-- The genesis start of the catch-up: `0 + 0 ≤ t_{s−1}` for `s > 0`. -/
private theorem genesis_start {s : Nat} (hs0 : 0 < s) : (0 : Time) + 0 ≤ sp.ts ((s : Int) - 1) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [add_zero, show ((s' + 1 : Nat) : Int) - 1 = (s' : Int) by push_cast; ring]
  exact ts_natCast_nonneg _

/-- **The suffix** under growing faults, under the service from `a` with its catch-up before
`a + κ ≤ t_{s−1}`, given that the voter's head height floor is at most the height of every block
of its tree above `Q`: at every block `X` from the pivot `D` to `Q` at or above the voter's anchor,
the proposer's best child is the voter's best child. The proposer is honest at `t_s + Δ` (the
hold), the voter at its vote. -/
theorem suffix_agree_from (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hs : a + κ ≤ sp.ts ((s : Int) - 1))
    (hfcQ : Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
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
  obtain ⟨h0, hij, hpj, hP', hc', hd', hcy', hsv, -, hflQ'⟩ :=
    suffix_lift_from hrun hnc hsync hp hP hPs hc hd hti hy hcy hes hs hfcQ hflQ
  intro X hDX hXQ hanc
  have hpi : p ∈ H (tr.time i) := hrun.antitone hij hpj
  have hXU := mem_upTo_of_frame hrun hpj hij hc (Compose.mem_of_anc_left hDX
    (Compose.mem_of_anc_left hsD (acProposal_start_anc_head (frameIn_at hrun hnc hpi hc).1 hd).1))
  exact Compose.suffix_agree_of (hrun.upTo h0) (hnc.upTo _) hsv hpj hP' hPs hc' hcall hd' hti hPQ
    hsD hDQ hviab hy hcy' hes (le_min hib hij) (le_min hjb le_rfl) hflQ' X hDX hXQ
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hXU hanc)

/-- **The suffix** under growing faults (the form from `a = κ = 0`, with the old origins): at
every block `X` from the pivot `D` to `Q` at or above the voter's anchor, the proposer's best child
is the voter's best child. The proposer is honest at `t_s + Δ` (the hold), the voter at its
vote. -/
theorem suffix_agree_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hstock : sp.committeeSize = sp.n) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
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
  obtain ⟨hs0, hfcQ, hflQ⟩ := genesis_voter_facts hrun hnc hsync hB hinv hp hP hPs hc hcall hd
    hti hPQ hy hcy hes hib hjb hstock
  exact suffix_agree_from hrun hnc (hsync.toFrom hrun) hp hP hPs hc hcall hd hti hPQ hsD hDQ hviab
    hy hcy hes hib hjb (genesis_start hs0) hfcQ hflQ

/-- **No old child of `Q` is eligible at the voter** under growing faults, under the service from
`a` with its catch-up before `a + κ ≤ t_{s−1}`, given that the voter's `fc_root` is below `Q` and
its head height floor is at most the height of every block of its tree above `Q` (the proposer
honest at `t_s + Δ`, the voter at its vote). -/
theorem old_child_ineligible_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hs : a + κ ≤ sp.ts ((s : Int) - 1))
    (hfcQ : Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBv : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s) :
    ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B := by
  obtain ⟨h0, hij, hpj, hP', hc', hd', hcy', hsv, hfcQ', hflQ'⟩ :=
    suffix_lift_from hrun hnc hsync hp hP hPs hc hd hti hy hcy hes hs hfcQ hflQ
  exact Compose.old_child_ineligible_of (hrun.upTo h0) (hnc.upTo _) hpj hP' hPs hc' hcall
    hd' hti hPQ hDQ hviab hy hcy' hes hsv (le_min hib hij) (le_min hjb le_rfl) hfcQ' hflQ' hBv
    hBQ hBs

/-- **No old child of `Q` is eligible at the voter** under growing faults (the form from
`a = κ = 0`, with the old origins; the proposer honest at `t_s + Δ`, the voter at its vote). -/
theorem old_child_ineligible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBv : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s) (hstock : sp.committeeSize = sp.n) :
    ¬ SA.goldfishEligible sp ℓy.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B := by
  obtain ⟨hs0, hfcQ, hflQ⟩ := genesis_voter_facts hrun hnc hsync hB hinv hp hP hPs hc hcall hd
    hti hPQ hy hcy hes hib hjb hstock
  exact old_child_ineligible_from hrun hnc (hsync.toFrom hrun) hp hP hPs hc hcall hd hti hPQ hDQ
    hviab hy hcy hes hib hjb (genesis_start hs0) hfcQ hflQ hBv hBQ hBs

/-- **`P` is in the voter's viable voter block tree** under growing faults, under the service from
`a` with its catch-up before `a + κ ≤ t_{s−1}`, given that the voter's `fc_root` is below `Q` and
its head height floor is at most the height of every block of its tree above `Q` (the proposer
honest at `t_s + Δ`, the voter at its vote). -/
theorem proposal_at_voter_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) (hjb : tr.time j ≤ b)
    (hs : a + κ ≤ sp.ts ((s : Int) - 1))
    (hfcQ : Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot d.head)
    (hflQ : ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) d.head B →
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  obtain ⟨h0, -, hpj, hP', hc', hd', hcy', hsv, hfcQ', hflQ'⟩ :=
    suffix_lift_from hrun hnc hsync hp hP hPs hc hd hti hy hcy hes hs hfcQ hflQ
  exact Compose.proposal_at_voter_of (hrun.upTo h0) (hnc.upTo _) hsv hpj hP' hPs hc' hd' hPQ
    hy hcy' hes (le_min hjb le_rfl) hfcQ' hflQ'

/-- **`P` is in the voter's viable voter block tree** under growing faults (the form from
`a = κ = 0`, with the old origins; the proposer honest at `t_s + Δ`, the voter at its vote). -/
theorem proposal_at_voter_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    (hPQ : P.parent = some d.head.root) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b) (hstock : sp.committeeSize = sp.n) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  obtain ⟨hs0, hfcQ, hflQ⟩ := genesis_voter_facts hrun hnc hsync hB hinv hp hP hPs hc hcall hd
    hti hPQ hy hcy hes hib hjb hstock
  exact proposal_at_voter_from hrun hnc (hsync.toFrom hrun) hp hP hPs hc hd hti hPQ hy hcy hes
    hjb (genesis_start hs0) hfcQ hflQ

end Consensus.Goldilocks.Compose.Growing

end
