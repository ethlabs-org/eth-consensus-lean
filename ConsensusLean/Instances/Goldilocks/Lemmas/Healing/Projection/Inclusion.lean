module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Goldilocks Healing: H.2 (run), AC inclusion in runs

The AC projection of a Goldilocks run is a driven AC trace (clause (a) from the FG's acceptance
tests, C0.5 (b), read on the projection's frames, `Compose.GoldilocksACProjection`; clause (b)
from C0.4 and C0.3: the tick's cuts, and the own block accepted at once), and `Healthy(g)` and
`Catch(2Δ)` read on it (from `GST(g)` over the run, read directly: its message clause and
acceptance relay, each FG acceptance followed by its `ac_on_block` at the next cut; and the run's
`Catch`, with `Σ.F` monotone); then H.2 applies to the projection (`SA.ac_inclusion`), inside the
honest blocks of the run (`Compose.GoldilocksACProjection`). The claims mark H.2 (run) S:
definitional in the node. The run facts are in `Healing/Projection/Run`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- Every block of an honest node's frame at a call is genesis (by root), or the node accepted
it at that call or an earlier one. -/
private theorem frame_root_or_accepted {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
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
  {tr : GoldilocksTrace sp ro} {g ΔF : Time}

/-- The Goldilocks node's AC meets requirements 1–5. -/
private theorem node_requirements : (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- The deadline does not change at a cut that is not a restart. -/
private theorem deadline_succ {y : Fin sp.n} {k : Nat} (hn : ¬ tr.RestartAt y (k + 1))
    (τ Δ' : Time) : tr.deadline y (k + 1) τ Δ' = tr.deadline y k τ Δ' := by
  simp only [RunTrace.deadline, lastWake_succ hn]

/-- The finalized tip of the frame of an honest AC cut is the node's `Σ.F`. -/
private theorem frame_F (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ℓ) :
    ℓ.frame.F = (tr.state y j).fg.F := by
  rw [(hrun.cutLaw y hy j _ (Compose.projAC_callAt.1 hc)).1]; rfl

/-- **The proposal of an honest proposer's tick is its honest proposal** in the AC projection:
the `ac_proposal` cut after the tick's `ac_on_tick` returns the payload, and the own block is
accepted at once (C0.3), at `t_s`. -/
private theorem honest_proposal_of_tick (hrun : GoldilocksRun proposer dg H tr)
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
  obtain ⟨hacc, ht2⟩ := own_block_accepted h node_requirements hroot hnc hp hg hP hr
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
theorem projection_driven_of_run (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg) :
    SA.Driven proposer tr.projAC H := by
  have h := hrun.toLocalRun
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
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

/-- Compatibility wrapper; driven duties require actual awake witnesses, not
an unbounded health premise. -/
theorem projection_driven (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    (_hh : tr.HealthyRun H ΔF g) : SA.Driven proposer tr.projAC H :=
  projection_driven_of_run hrun hnc hroot

/-- `Healthy(g)` over a run gives `Healthy(g)` on its AC projection. -/
theorem projection_healthy (hrun : GoldilocksRun proposer dg H tr) (_hnc : Compose.NoCollRun dg tr)
    (hh : tr.HealthyRun H ΔF g) : SA.HealthyAC tr.projAC H (tr.HonestBlocks H) g := by
  have h := hrun.toLocalRun
  obtain ⟨hgst, hawake, hf⟩ := hh
  refine ⟨?_, ?_, fun y hy t ht => hawake y hy t ht, hf⟩
  · intro x hx i m hsa y hy j ℓ hc hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ℓ, hc, hm⟩ := hsa
      refine ⟨ℓ, Compose.projAC_callAt.1 hc, ?_⟩
      rwa [Compose.projAC_state h hx] at hm
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ :=
      hgst.message x hx i m hsa' trivial y hy j ⟨_, Compose.projAC_callAt.1 hc⟩ hdl
    refine ⟨k, hk, h1, ?_, by rw [Compose.projAC_deadline]; exact h3⟩
    rcases h2 with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', e, he, hem⟩
    · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
    · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he, hem⟩⟩
  · intro x hx i B ha hgi y hy j ℓ hc hdl hanc
    obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before h hx ha
    have hmax : max (tr.time i') g = tr.projAC.time (i' + 1) := by
      rw [show tr.projAC.time (i' + 1) = tr.time (i' + 1) from rfl, hti]; exact max_eq_left hgi
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, hak, hkt⟩ := hgst.relay x hx i' B ha' (by rw [hti]; exact hgi) y hy j
      ⟨_, Compose.projAC_callAt.1 hc⟩ (by rw [hmax]; exact hdl) (frame_F hrun hy hc ▸ hanc)
    obtain ⟨hak', htk, hnr⟩ := ac_block_after h hy hak
    have hkj : k < j := by
      rcases hk.lt_or_eq with hk | rfl
      · exact hk
      · exact absurd (hak.2.symm.trans (Compose.projAC_callAt.1 hc).2) (by simp)
    refine ⟨k + 1, hkj, hak', ?_⟩
    have htk' : tr.projAC.time (k + 1) = tr.time k := htk
    rw [Compose.projAC_deadline, deadline_succ hnr, htk', ← hmax]
    exact hkt

/-- `Catch(κ)` over a run gives `Catch(κ)` on its AC projection (`Φ.F` is `Σ.F`). -/
theorem projection_catch_of_run (hrun : GoldilocksRun proposer dg H tr)
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

/-- Compatibility wrapper; Catch projection uses actual calls only. -/
theorem projection_catch (hrun : GoldilocksRun proposer dg H tr) (_hnc : Compose.NoCollRun dg tr)
    (_hh : tr.HealthyRun H ΔF g) (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.CatchAC tr.projAC H (tr.HonestBlocks H) g (2 * sp.Δ) :=
  projection_catch_of_run hrun hc

/-- **H.2 (run), AC inclusion in runs.** -/
theorem run_inclusion : RunInclusion := by
  intro sp ro proposer dg H tr g ΔF hrun hnc hroot hh hc
  have hd := projection_driven hrun hnc hroot hh
  have hhe := projection_healthy hrun hnc hh
  have hca := projection_catch hrun hnc hh hc
  refine ⟨⟨hd, hhe, hca⟩, fun t₀ ht₀ hinv p P hP htp => ?_⟩
  have := SA.ac_inclusion sp _ ro H _ tr.projAC proposer g t₀
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc)
    hd hhe hca ht₀ hinv p P hP.1 hP.2 htp
  exact ⟨this.1, fun hu y hy j ℓ hj ht hk => this.2 hu y hy j ℓ hj ht hk⟩

end Consensus.Goldilocks.Healing

end
