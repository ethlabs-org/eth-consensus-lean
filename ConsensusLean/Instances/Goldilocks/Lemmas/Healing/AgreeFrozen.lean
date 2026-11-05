module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.3: the ready proposal is frozen-viable at every slot-`s` vote

With `P` itself as frozen witness for every ancestor: at every
honest slot-`s` vote, `P` is held, allowed in the effective geometry, a viable head of the voter
and in its viable voter block tree (`proposal_frozen_viable`). As `Geo.geo_of_settled`: the
proposal's parent is a viable head of the proposer (its walk starts in the viable tree), so `P`
is allowed wherever it is held; the voter holds it (ready at an early vote, relayed by `t_s + Δ`
otherwise); HS.1 (`viableHead_of_allowed`) makes it a viable head of the voter. The proposal's
cut precedes every slot-`s` vote (an early voter holds `P`, accepted
after its proposer's own block call, the tick of the proposal), so the phase holds at it.

The aligned-reader facts are `Geo`'s (`viableHeads_iff`, `proposal_head_viable`,
`proposal_call_tick`, `effAllowed_transfer`, `effAllowed_of_anc`) and `SA.cast_ready`. The same
proof gives that `Q` is a viable head of the proposer (`proposal_head_viableHead`) and the phase
facts at a vote (`phase_at_vote`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Main

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-- **The proposal's cut precedes every honest holder of `P`**: an honest node holding `P` at a
cut `k` accepted it at an earlier cut, after its proposer's own block call (unforgeable blocks),
which is the cut after the proposal's `ac_proposal` cut (one tick per node and time). -/
private theorem proposal_before_holder
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) (hs1 : 1 ≤ s)
    (hPprop : P.proposer = p) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    (hPz : P ∈ (tr.state z k).fg.tree) : iP < k := by
  have hl := hS.run.toLocalRun
  have hpH : p ∈ H := hS.ready.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  rcases Compose.tree_cases hl hz hPz with hg | ⟨a, hak, ha⟩
  · have := congrArg (·.slot) hg
    simp only [Params.genesisBlock] at this
    omega
  obtain ⟨j', hj'a, hown⟩ := hl.block_unforgeable z hz a P ⟨true, ha⟩ (hPprop ▸ hpH)
  rw [hPprop] at hown
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  rcases Compose.blockCall_cases hl hpH hc with hg |
    ⟨j'', x, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hS.call)
    hS.call_proposal
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [hS.time, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by rw [← ht]; exact ⟨x, hg⟩)
  omega

/-- **The slot-`s` block of an honest frame is `P`**: the honest proposer has one block per slot
in the honest frames (`HonestObjects.one_block`), and a slot-`s` block (`s ≥ 1`) is not genesis,
so it has the slot's proposer. -/
theorem frame_slot_eq_proposal
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ℓy) : ∀ P' ∈ ℓy.frame.tree, P'.slot = s → P' = P := by
  have hrun := hS.run
  have hl := hrun.toLocalRun
  have hnc := hS.shared.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hpH : p ∈ H := hS.ready.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  have hs1 := hS.one_le_slot
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hPprop, -, ja, -, hacc, -⟩ :=
    honestProposalRun_of_ready hrun hnc hS.ready
  rw [← hS.ready.2.1] at hPprop hacc
  obtain ⟨jℓ, hcj, hcallj⟩ := hacc
  have hPj : P ∈ jℓ.frame.tree := (SA.accept_new sp hr hpH ⟨jℓ, hcj, hcallj⟩).1 jℓ hcj
  have hfU : ℓy.frame.tree ⊆ tr.HonestBlocks H := (SA.frameIn_of_callAt hr hy hc).2
  intro P' hP' hP's
  have hfb : SA.HonestFrameBlock tr.projAC H P' := ⟨y, hy, j, ℓy, hc, hP'⟩
  have hroot : P'.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hl hy j)
    obtain rfl := hU.1 (hfU hP') ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hP's
    omega
  exact (hac.honest.one_block P P' ⟨_, hpH, ja, jℓ, hcj, hPj⟩ hfb (hPprop ▸ hpH)
    (by rw [hPprop, hac.honest.proposer P' hfb hroot, hP's, hS.ready.2.1])
    (by rw [hPs, hP's])).symm

/-- **The frozen facts at a vote**: `P` is frozen-viable (`proposal_frozen_viable`, whose
docstring has the argument), `Q` is a viable head of the proposer, and the phase and evidence
hold from `i₀` through the vote. -/
private theorem frozen_core
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    (P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
      d.head ∈ ℓp.frame.viableHeads) ∧
    (i₀ ≤ iP ∧ iP < j ∧ PhaseOn tr.projFG H i₀ j m c ∧
      ∀ z ∈ H, ∀ k', i₀ ≤ k' → HoldsEvidence (tr.state z k').fg m c) := by
  have hrun := hS.run
  have hs := hS.shared
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  have hpar := hS.parent
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hPprop, -, ja, -, hacc, htja⟩ :=
    honestProposalRun_of_ready hrun hnc hS.ready
  rw [← hS.ready.2.1] at hPprop hacc
  -- times: the settled time and the vote are around `t_s`
  have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
  have hvt : sp.ts s ≤ tr.time j := by
    obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hcy
    exact (SA.ts_le_iff_le_slot sp (hl.time_nonneg j) s).2
      (by have := hys.le; rw [hes] at this; exact_mod_cast this)
  have hwi : w ≤ tr.time i := hS.settled.2.1.1.trans (hl.time_mono hS.settled_le)
  have hws : w < sp.ts s := by linarith [hS.start_time]
  have hs1 : 1 ≤ s := by
    by_contra h0
    obtain rfl : s = 0 := by omega
    have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    have := gbar_nonneg g
    have := (le_max_right _ _).trans hS.settled.1.late
    linarith
  have hiP0 : i₀ ≤ iP := le_of_settledIn hS.settled (by rw [hS.time]; exact hws.le)
  -- the slot-`s` block of the voter's frame is `P`
  obtain ⟨jℓ, hcj, hcallj⟩ := hacc
  have hPj : P ∈ jℓ.frame.tree := (SA.accept_new sp hr hpH ⟨jℓ, hcj, hcallj⟩).1 jℓ hcj
  have hslotP := frame_slot_eq_proposal hS hy hcy.1
  -- an early voter holds `P`; the proposal's cut precedes the vote
  have hiPj : iP < j := by
    by_cases hlate : tr.time iP < tr.time j
    · by_contra hn
      exact absurd (hl.time_mono (not_lt.1 hn)) (not_le.2 hlate)
    · have hearly : tr.time j < sp.ts e.msg.slot + sp.Δ := by
        rw [hes]; rw [hS.time] at hlate; linarith
      obtain ⟨P', hP', hP's, -⟩ := SA.cast_ready hr hy hcy hearly
      rw [hes] at hP's
      exact proposal_before_holder hS hs1 hPprop hy
        (mem_tree_of_frame hrun hy hcy.1 (hslotP P' hP' hP's ▸ hP'))
  -- the phase on `[i₀, j]`, and the evidence held from `i₀` on
  have hwin : PhaseOn tr.projFG H i₀ j m c :=
    phaseOn_voter hrun hs hS.settled (start_le_voter hrun hnc hS.start_time hy hcy hes)
      (hS.phase y hy j ℓy e hcy hes)
  have hev : ∀ z ∈ H, ∀ k', i₀ ≤ k' → HoldsEvidence (tr.state z k').fg m c := by
    intro z hz k' hk'
    have := hS.settled.1.evidence i₀ hS.settled.2.1 m c hS.settled.2.2 z hz
    rw [projFG_store_eq hrun hz] at this
    exact holdsEvidence_mono hrun hnc hz hk' this
  have hphP := hwin iP hiP0 hiPj.le
  -- the proposal's parent is a viable head of the proposer, so allowed
  have hfr₀ : ℓp.frame = Node.frame (tr.state p iP) := Compose.frame_of_projAC hrun hpH hS.call
  have hΦ₀ := (SA.frameIn_of_callAt hr hpH hS.call).1
  have hfc₀ : ℓp.frame.fcRoot ∈ ℓp.frame.viableTree ℓp.frame.tree := by
    have hevk := hev p hpH iP hiP0
    obtain ⟨Bm, hBm, hBmh⟩ : ∃ B ∈ (tr.state p iP).fg.tree,
        ((tr.state p iP).fg.σ B.root).h = m := by
      cases c with
      | gap => exact hevk
      | top J => exact hevk.1
      | contest J => exact hevk.1
    have hBe : EffAllowed (tr.state p iP).fg m c Bm := by
      refine ⟨hBm, ?_, fun J hJ => ?_⟩
      · cases c <;> (simp only [phaseFloor]; omega)
      · subst hJ
        by_contra hn
        exact hphP.2.2 ⟨_, hpH, Bm, by rw [projFG_store_eq hrun hpH]; exact hBm,
          by rw [projFG_store_eq hrun hpH]; exact hBmh, by rw [projFG_store_eq hrun hpH]; exact hn⟩
    have hBv : Bm ∈ ℓp.frame.viableHeads := by
      rw [hfr₀]
      exact viableHead_of_allowed hrun hs (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hphP) hpH
        hBe hpH le_rfl le_rfl hBm
    exact ⟨hΦ₀.fcRoot_mem, .refl, Bm, hΦ₀.viableHeads_subset hBv, hBv,
      hΦ₀.fcRoot_anc_viableHeads Bm hBv⟩
  have hPrv : d.head ∈ ℓp.frame.viableHeads := proposal_head_viable hr hpH hS.call
    hS.call_proposal (σ := s) (by rw [sp.slotTime_eq]; exact hS.time) hS.payload hfc₀
  have hQv := hPrv
  rw [hfr₀] at hPrv
  have hPrt : d.head ∈ (tr.state p iP).fg.tree := hPrv.1
  obtain ⟨-, hPrE⟩ :=
    (viableHeads_iff hrun hs hS.catchUp hpH hphP (hev p hpH iP hiP0) hPrt).1 hPrv
  -- `P` is allowed wherever it is held
  have hPallow : ∀ z ∈ H, ∀ k', P ∈ (tr.state z k').fg.tree →
      EffAllowed (tr.state z k').fg m c P := by
    intro z hz k' hPz
    have hR := Compose.fg_reachable hl hz k'
    obtain ⟨Y, hY, hYr, -⟩ := Store.step_σ hR hPz hpar
    obtain rfl : Y = d.head := hU.1 ⟨z, hz, k', hY⟩ ⟨_, hpH, iP, hPrt⟩ hYr
    exact effAllowed_of_anc hR (effAllowed_transfer hrun hnc hpH hz hPrE hY) hPz
      (Relation.ReflTransGen.single ⟨hY, hPz, hpar⟩)
  -- the voter holds `P`
  have hPy : P ∈ (tr.state y j).fg.tree := by
    by_cases hearly : tr.time j < sp.ts s + sp.Δ
    · obtain ⟨P', hP', hP's, -⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
      rw [hes] at hP's
      exact mem_tree_of_frame hrun hy hcy.1 (hslotP P' hP' hP's ▸ hP')
    · push Not at hearly
      obtain ⟨kf, rfl, hkf, hkft⟩ := fg_accept_before hl hpH ⟨jℓ, hcj, hcallj⟩
      have htj' : tr.time (kf + 1) = sp.ts s := htja
      have hPk := mem_tree_of_frame hrun hpH hcj hPj
      obtain ⟨jv, hjv, hjvj⟩ := exists_firstCutFrom_le (tr := tr) hearly
      have hj0 : i₀ ≤ kf + 1 := le_of_settledIn hS.settled (by rw [htj']; exact hws.le)
      have hjjv : kf + 1 ≤ jv := by
        by_contra hn
        have := hl.time_mono (not_le.1 hn).le
        linarith [hjv.1]
      have hF := finalized_anc_of_allowed hrun hs (fun k' h1 h2 => hwin k' (hj0.trans h1) h2)
        hpH (hPallow _ hpH _ hPk) hy hjjv hjvj
      exact Compose.tree_mono hl hy hjvj (relay_held hl hs.healthy hs.noRestart hS.catchUp hpH hy
        hkf (by linarith [hS.gbar_le]) (by rw [hkft, htj']) hjv hF)
  have hPv := viableHead_of_allowed hrun hs (fun k' h1 h2 => hwin k' (hiP0.trans
    (hiPj.le.trans h1)) h2) hy (hPallow y hy j hPy) hy le_rfl le_rfl hPy
  have hfrv : ℓy.frame = Node.frame (tr.state y j) := Compose.frame_of_projAC hrun hy hcy.1
  have hΦy := (SA.frameIn_of_callAt hr hy hcy.1).1
  refine ⟨⟨?_, hQv⟩, hiP0, hiPj, hwin, hev⟩
  rw [hfrv] at hΦy ⊢
  have hPt : P ∈ (Node.frame (tr.state y j)).tree := hΦy.viableHeads_subset hPv
  have hPV : P ∈ SA.voterBlockTree sp e.readPoint (Node.frame (tr.state y j)) s :=
    ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩
  exact ⟨hPV, hΦy.fcRoot_anc_viableHeads P hPv, P, hPV, hPv, .refl⟩

/-- **`P` is frozen-viable at every honest slot-`s` vote** (with
`P` itself as frozen witness): `P` is held by the voter (ready at an early vote, `cast_ready`;
relayed by `t_s + Δ` otherwise, `relay_held`), allowed (its parent is a viable head of the
proposer, whose walk starts in the viable tree, `proposal_head_viable`, read with the aligned
readers at the proposal cut, which precedes the vote), so a viable head of the voter (HS.1,
`viableHead_of_allowed`), and in the voter block tree as the slot-`s` block. -/
theorem proposal_frozen_viable
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    P ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) :=
  (frozen_core hS hy hcy hes).1.1

/-- **`Q` is a viable head of the proposer** (`proposal_head_viable`: the proposal walk starts in
the viable tree, `fc_root` being below the evidence block of height `m`, allowed and so a viable
head, HS.1), read at the proposal cut, which precedes an honest slot-`s` vote. -/
theorem proposal_head_viableHead
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) : d.head ∈ ℓp.frame.viableHeads :=
  (frozen_core hS hy hcy hes).1.2

/-- **The phase at a vote**: the proposal's cut is between the settled cut `i₀` and an honest
slot-`s` vote, the phase `(m, c)` holds from `i₀` through the vote, and every honest node holds
the evidence from `i₀` on (the phase from the vote's `PhaseOn` and the sandwich; the proposal's
cut precedes every holder of `P`). -/
theorem phase_at_vote
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    i₀ ≤ iP ∧ iP < j ∧ PhaseOn tr.projFG H i₀ j m c ∧
      ∀ z ∈ H, ∀ k', i₀ ≤ k' → HoldsEvidence (tr.state z k').fg m c :=
  (frozen_core hS hy hcy hes).2

end Main

end Consensus.Goldilocks.Healing

end
