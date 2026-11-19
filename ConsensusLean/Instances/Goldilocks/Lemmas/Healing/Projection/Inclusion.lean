module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Goldilocks Healing: the AC projection of a run

The AC projection of a Goldilocks run is a driven AC trace (clause (a) from the FG's acceptance
tests, C0.5 (b), read on the projection's frames, `Compose.GoldilocksACProjection`; clause (b)
from C0.4 and C0.3: the tick's cuts, and the own block accepted at once), and `Healthy(g)` and
`Catch(2Δ)` read on it (from `GST(g)` over the run, read directly: its message clause and
acceptance relay, each FG acceptance followed by its `ac_on_block` at the next cut; and the run's
`Catch`, with `Σ.F` monotone), inside the honest blocks of the run
(`Compose.GoldilocksACProjection`). The run facts are in `Healing/Projection/Run`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- Every block of an honest node's frame at a call is genesis (by root), or the node accepted
it at that call or an earlier one. -/
private theorem frame_root_or_accepted {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}
    {ini} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ Φ : SA.Frm sp.n FGP,
        (SA.goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame →
        (∀ B ∈ Φ.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B) →
        ∀ B ∈ ℓ.frame.tree, B.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
      intro Φ hok hv X hX
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm
      cases c with
      | block B =>
        rw [hm.1.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact Or.inr ⟨i, le_rfl, ℓ, hc, hcall⟩
        · exact hv X hX
      | message m => exact hv X (hm.1 ▸ hX)
      | tick => exact hv X (hm ▸ hX)
      | proposal => exact hv X (hm ▸ hX)
      | toFG => exact hv X (hm ▸ hX)
      | restart => exact hv X (hm ▸ hX)
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      exact Or.inl hroot
    · exact step _ hok fun B hB =>
        (ih j hj hc' B hB).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF : Time}

/-- The finalized tip of the frame of an honest AC cut is the node's `Σ.F`. -/
private theorem frame_F (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ℓ) :
    ℓ.frame.F = (tr.state y j).fg.F := by
  rw [(hrun.cutLaw y hy j _ (Compose.projAC_callAt.1 hc)).1]; rfl

/-- **The proposal of an honest proposer's tick is its honest proposal** in the AC projection:
the `ac_proposal` cut after the tick's `ac_on_tick` returns the payload, and the own block is
accepted at once (C0.3), at `t_s`. -/
private theorem honest_proposal_of_tick {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    {p : Fin sp.n} (hp : p ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg p j t (.tick x))
    (hP : Node.Proposes proposer p t) {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n}
    (hr : (Node.acProposal (Node.tickStep proposer dg p (tr.state p j) t x .acTick).1 t).2.2 =
      some (d, pay)) :
    SA.HonestProposal tr.projAC p (sp.slot t)
      (Node.mkBlock dg p (tr.state p j).fg t x d.head pay) := by
  have h := hrun.toLocalRun
  obtain ⟨hc1, ht1, hst1⟩ := tick_proposal_call h hp hg hP
  obtain ⟨hacc, ht2⟩ := own_block_accepted h (Compose.requirements_from sp ro (hrun.vstart p)) hroot
    hnc hp hg hP hr
  obtain ⟨hacc3, ht3, -⟩ := ac_block_after h hp hacc
  have hts : t = sp.ts (sp.slot t) := hP.2.1.trans (sp.slotTime_eq _)
  refine ⟨j + 1,
    ⟨.proposal, Node.frame (Node.tickStep proposer dg p (tr.state p j) t x .acTick).1, []⟩,
    d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, rfl, rfl, rfl, j + 3,
    by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = t := ht1
  rw [Compose.projAC_state h hp, hst1, ht1']
  exact hr

/-- The AC projection of a Goldilocks run is driven (H.2 (run): clause (a) from the FG's
acceptance tests, clause (b) from C0.4). -/
theorem projection_driven_of_run {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg) :
    SA.Driven proposer tr.projAC H := by
  have h := hrun.toLocalRun
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hac.localRun
  have blocks : ∀ y ∈ H, ∀ i B, tr.projAC.AcceptAt y i B → B.root ≠ sp.genesisRoot →
      B.proposer = proposer B.slot ∧ B.slot ≤ sp.slot (tr.projAC.time i) ∧
      ∃ Pb : SA.Blk sp.n (List (FG.Att sp.n)), B.parent = some Pb.root ∧ Pb.slot < B.slot ∧
        (Pb.root = sp.genesisRoot ∨ ∃ k < i, tr.projAC.AcceptAt y k Pb) := by
    intro y hy i B ha hB
    obtain ⟨ℓ, hc, hcall⟩ := ha
    obtain ⟨Φ, hok, hΦU, hprev⟩ : ∃ Φ, (goldilocksNode sp ro).CallOK (tr.HonestBlocks H) Φ
        (tr.projAC.time i) ℓ.call ℓ.frame ∧ Φ.tree ⊆ tr.HonestBlocks H ∧
        ∀ X ∈ Φ.tree, X.root = sp.genesisRoot ∨ ∃ k < i, tr.projAC.AcceptAt y k X := by
      rcases hr.frameLaw y hy i ℓ hc with
        ⟨-, Φ₀, ⟨htree, hroot₀, -⟩, hin, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
      · refine ⟨Φ₀, hok, hin.2, fun X hX => ?_⟩
        rw [htree, Set.mem_singleton_iff] at hX
        subst hX
        exact Or.inl hroot₀
      · have hin : (goldilocksNode sp ro).FrameIn (tr.HonestBlocks H) ℓ'.frame := by
          rcases hr.frameLaw y hy j ℓ' hc' with ⟨_, _, _, _, hok'⟩ | ⟨_, _, _, _, _, hok'⟩ <;>
            exact hok'.1
        exact ⟨ℓ'.frame, hok, hin.2, fun X hX => (frame_root_or_accepted hr hy hc' X hX).imp_right
          fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩⟩
    obtain ⟨⟨-, hΦ'U⟩, hm⟩ := hok
    rw [hcall] at hm
    obtain ⟨hs, -, hslot⟩ := hm
    have hBt : B ∈ ℓ.frame.tree := by rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
    obtain ⟨Pb, hPb, hpar⟩ := hs.parent_mem
    exact ⟨hac.honest.proposer B ⟨y, hy, i, ℓ, hc, hBt⟩ hB, hslot, Pb, hpar,
      hr.coherent.2 Pb (hΦU hPb) B (hΦ'U hBt) hpar, hprev Pb hPb⟩
  refine ⟨blocks, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) a block of an honest proposer's slot is its proposal
    intro y hy i B ha hB hpH
    have hprop := (blocks y hy i B ha hB).1
    obtain ⟨k, rfl, hk, -⟩ := fg_accept_before h hy ha
    obtain ⟨j', -, ⟨acc, ho⟩, hpos⟩ := h.block_unforgeable y hy k B ⟨true, hk⟩ (hprop ▸ hpH)
    generalize hpB : B.proposer = p at ho hpos
    have hp : p ∈ H := hpB ▸ hprop ▸ hpH
    rcases Compose.blockCall_cases h hp ho with hd | ⟨j, x, rfl, hg, hP, d, pay, hr', rfl, -⟩
    · exact absurd (by simpa using (hd.2.1 0 (List.length_pos_iff.2 hd.1)).2.2.2.1) hpos
    have hps : proposer (sp.slot (tr.time (j + 2))) = p := hP.2.2
    change SA.HonestProposal tr.projAC (proposer (sp.slot (tr.time (j + 2))))
      (sp.slot (tr.time (j + 2))) _
    rw [hps]
    exact honest_proposal_of_tick hrun hnc hroot hp hg hP hr'
  · -- (b) the tick at every public time
    intro y hy t ht hpub haw
    obtain ⟨j, x, hg⟩ := h.tick_of_awake y hy t ht hpub haw
    obtain ⟨hc, htj⟩ := tick_first_cut hg
    exact ⟨j, ⟨.tick, Node.frame (tr.state y j), _⟩, Compose.projAC_callAt.2 hc, rfl, htj⟩
  · -- (b) the proposal at `t_s`
    intro s hs p hp hps haw _
    have hΔ := sp.toParams.hΔ
    have hts0 : 0 ≤ sp.ts s := by unfold SAParams.ts; positivity
    have hpub : sp.toParams.IsPublic (sp.ts s) := ⟨4 * (s : Int), by unfold SAParams.ts; ring⟩
    obtain ⟨j, x, hg⟩ := h.tick_of_awake p hp _ hts0 hpub haw
    have hslot : sp.toParams.slotOf (sp.ts s) = s :=
      SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by omega))
    have hP : Node.Proposes proposer p (sp.ts s) :=
      ⟨by rw [hslot]; exact hs, by rw [hslot, sp.slotTime_eq]; rfl, by rw [hslot, hps]⟩
    obtain ⟨hc1, ht1, hst1⟩ := tick_proposal_call h hp hg hP
    refine ⟨j + 1, ⟨.proposal, Node.frame (Node.tickStep proposer dg p (tr.state p j) (sp.ts s)
      x .acTick).1, []⟩, Compose.projAC_callAt.2 hc1, rfl, ht1, ?_⟩
    rintro ⟨pay, -, -, d, hd⟩
    have ht1' : tr.projAC.time (j + 1) = sp.ts s := ht1
    rw [Compose.projAC_state h hp, hst1, ht1'] at hd
    have := honest_proposal_of_tick hrun hnc hroot hp hg hP hd
    rw [show sp.slot (sp.ts s) = s from hslot] at this
    exact ⟨_, this⟩
  · -- (b) no object of a public time before its tick
    rintro y hy i j ℓ ℓ' hci hcj htick htime ⟨m, hm⟩
    obtain ⟨ji, ei, qi, hgi, rfl, hqi⟩ := Compose.call_in_group h hy (Compose.projAC_callAt.1 hci)
    obtain ⟨jj, ej, qj, hgj, rfl, hqj⟩ := Compose.call_in_group h hy (Compose.projAC_callAt.1 hcj)
    have hei := (exec_ac_call _ _ _ _ (List.mem_of_getElem? hqi)).2 m hm
    obtain ⟨x, hej⟩ := (exec_ac_call _ _ _ _ (List.mem_of_getElem? hqj)).1 htick
    subst hei hej
    have htime' : tr.time (ji + qi) = tr.time (jj + qj) := htime
    rw [htime'] at hgi
    have hlt : jj < ji := by
      rcases lt_trichotomy jj ji with h1 | rfl | h1
      · exact h1
      · exfalso
        have h1 := (hgj.2.1 0 (List.length_pos_iff.2 hgj.1)).2.2.2.2
        have h2 := (hgi.2.1 0 (List.length_pos_iff.2 hgi.1)).2.2.2.2
        rw [h1] at h2
        simp [Node.exec, Node.onMessage, Node.acCall, onTick_eq, Node.tickStep] at h2
      · exact absurd (h.phase_order y hy y hy ji jj _ _ _ hgi hgj h1)
          (by simp [Node.Event.phase])
    by_contra hle
    have hqjlen := (List.getElem?_eq_some_iff.1 hqj).1
    have hev := (hgj.2.1 (ji - jj) (by omega)).2.2.1
    rw [Nat.add_sub_cancel' hlt.le] at hev
    have := (hgi.2.2 jj hev.symm).1
    omega
  · -- (b) no object of the proposal's time before the proposal
    rintro y hy i j ℓ ℓ' hci hcj hprop htime hobj
    obtain ⟨ji, ei, qi, hgi, rfl, hqi⟩ := Compose.call_in_group h hy (Compose.projAC_callAt.1 hci)
    obtain ⟨jj, ej, qj, hgj, rfl, hqj⟩ := Compose.call_in_group h hy (Compose.projAC_callAt.1 hcj)
    obtain ⟨x, rfl⟩ := exec_ac_proposal _ _ _ _ (List.mem_of_getElem? hqj) hprop
    have hqj1 : qj = 1 := (onTick_ac_index _ _ _ _
      (show (Node.onTick proposer dg y (tr.state y jj)
        (tr.time (jj + qj)) x).2[qj]? = _ from hqj)).1 hprop
    have htime' : tr.time (ji + qi) = tr.time (jj + qj) := htime
    rw [htime'] at hgi hqi
    -- a delivery's group at that time starts after the tick's
    have later : ei.phase = 2 → jj + qj < ji + qi := by
      intro hph
      have hlt : jj < ji := by
        rcases lt_trichotomy jj ji with h1 | rfl | h1
        · exact h1
        · have := Compose.group_phase hgi hgj
          rw [hph] at this
          simp [Node.Event.phase] at this
        · have := h.phase_order y hy y hy ji jj _ _ _ hgi hgj h1
          rw [hph] at this
          simp [Node.Event.phase] at this
      by_contra hle
      have hqjlen := (List.getElem?_eq_some_iff.1 hqj).1
      have hev := (hgj.2.1 (ji - jj) (by omega)).2.2.1
      rw [Nat.add_sub_cancel' hlt.le] at hev
      have := (hgi.2.2 jj hev.symm).1
      omega
    cases ei with
    | tick x' =>
      have hji : ji = jj := h.tick_unique y hy ji jj _ ⟨x', hgi⟩ ⟨x, hgj⟩
      subst hji
      have hidx := (onTick_ac_index _ _ _ _
        (show (Node.onTick proposer dg y (tr.state y ji)
          (tr.time (ji + qj)) x').2[qi]? = _ from hqi)).2
      rcases hobj with ⟨m, hm⟩ | ⟨B, hB⟩
      · exact absurd ((exec_ac_call _ _ _ _ (List.mem_of_getElem? hqi)).2 m hm) (by simp)
      · have : ¬ qi ≤ 1 := fun hle => hidx hle B hB
        omega
    | block B => exact later rfl
    | message m => exact later rfl
    | attestation a =>
      have := List.mem_of_getElem? hqi
      simp [Node.exec, Node.onAttestation] at this
    | restart =>
      exfalso
      have hm := List.mem_of_getElem? hqi
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hm
      subst hm
      rcases hobj with ⟨m, hm⟩ | ⟨B, hB⟩
      · cases hm
      · cases hB

/-- `Catch(κ)` over a run gives `Catch(κ)` on its AC projection (`Φ.F` is `Σ.F`). -/
theorem projection_catch_of_run (hrun : GoldilocksRun proposer dg H tr ini)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.CatchAC tr.projAC H (tr.HonestBlocks H) g (2 * sp.Δ) := by
  classical
  have h := hrun.toLocalRun
  intro x hx i B ha hi y hy j ℓ hcj hj hanc
  obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before h hx ha
  have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨j, hj⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀j : Nat.find hex ≤ j := Nat.find_min' hex hj
  have hanc₀ : Anc (tr.HonestBlocks H) (tr.state y (Nat.find hex)).fg.F B :=
    (run_F_mono h hy hj₀j).trans (frame_F hrun hy hcj ▸ hanc)
  obtain ⟨k, hk, hak⟩ := hc x hx i' B ha' (by rw [hti]; exact hi) y hy _ hj₀ hanc₀
  obtain ⟨hak', htk, -⟩ := ac_block_after h hy hak
  have htk' : tr.projAC.time (k + 1) = tr.time k := htk
  refine ⟨k + 1, by omega, hak', ?_⟩
  rw [htk']
  exact hj₀.2 k hk

end Consensus.Goldilocks.Healing

end
