module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeFrozen
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.3: the proposal's view and a voter's merged view agree

`hs234-exact-interface.md` §4 (workbench#12 §3, first paragraph; as A1.7's view agreement in
`Compose/Service/Suffix`): in the settled phase of `AgreeSetting`, the proposal's view
(`View.ofLists pay`, the proposer's slot-`(s−1)` pool) and an honest slot-`s` voter's merged view
have the same equivocators and voters, and the same supporters for every block of both trees
(`SA.view_agree`: the voter's pre-freeze votes and blocks reach the proposer by `t_s`, the support
heads of `P` reach the voter by its vote). Used by `AgreeSuffix`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-- A block held at an honest call's cut that extends the call's `Σ.F` is in its frame. -/
theorem mem_frame_of_held (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y k).fg.tree) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    B ∈ ℓ.frame.tree := by
  rw [Compose.frame_of_projAC hrun hy hc] at hF ⊢
  exact ⟨hB, store_anc_of_honest_anc hrun hnc hy hF hB⟩

/-- **The relay into a frame** (`relay_held`): a block an honest `x` holds at a cut of time
`τ` with `τ + Δ ≤ u` and `ḡ + 2Δ ≤ u` is in the frame of every honest call at a time `≥ u`
whose `Σ.F` it extends. -/
theorem mem_frame_of_relay
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {k₀ : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x k₀).fg.tree) {u : Time}
    (hu : gbar g + 2 * sp.Δ ≤ u) (hk₀ : tr.time k₀ + sp.Δ ≤ u) {jz : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z jz ℓ) (hjz : u ≤ tr.time jz)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) : B ∈ ℓ.frame.tree := by
  have hl := hS.run.toLocalRun
  have hFz : ℓ.frame.F = (tr.state z jz).fg.F := by
    rw [Compose.frame_of_projAC hS.run hz hc]; rfl
  refine mem_frame_of_held hS.run hS.shared.noColl hz hc ?_ hF
  rcases Compose.tree_cases hl hx hB with rfl | ⟨a, hak, ha⟩
  · exact Store.genesis_mem (Compose.fg_reachable hl hz jz)
  obtain ⟨j₁, hj₁, hle⟩ := exists_firstCutFrom_le hjz
  have hta := hl.time_mono hak.le
  exact Compose.tree_mono hl hz hle (relay_held hl hS.shared.healthy hS.shared.noRestart
    hS.catchUp hx hz ha hu (by linarith) hj₁ ((run_F_mono hl hz hle).trans (hFz ▸ hF)))

/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees
(`SA.view_agree`, with the HS relay: a block the voter stamped before the vote freeze was
accepted by then, so it reaches the proposer by `t_s` (`relay_held`); a support head of `P` is in
the voter's ready frame at an early vote, and relayed from the proposer by `t_s + Δ` otherwise;
`Sync` on `[t_{s−1}, t_s]` from `GST(g)`, `g ≤ ḡ ≤ t_{s−1}`). -/
theorem proposal_views_agree
    (hS : AgreeSetting proposer dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        SA.supporters ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) X =
          SA.supporters ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)
            X := by
  have hrun := hS.run
  have hl := hrun.toLocalRun
  have hnc := hS.shared.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hpH : p ∈ H := hS.ready.1
  have hs1 := hS.one_le_slot
  have hPy : P ∈ ℓy.frame.tree := (proposal_frozen_viable hS hy hcy hes).1.1
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hcast : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hwi : w ≤ tr.time i := hS.settled.2.1.1.trans (hl.time_mono hS.settled_le)
  have hgw : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hS.settled.1.late
  have hti0 := hS.start_time
  rw [hcast] at hti0
  have hsi : sp.slot (tr.time iP) = s' + 1 := by
    rw [hS.time]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
  -- the proposal's payload
  obtain ⟨-, k, ℓk, d', pay', hck, hcallk, hdk, htk, -, hPs, hPprop, hpayk, ja, -, hacc, -⟩ :=
    honestProposalRun_of_ready hrun hnc hS.ready
  rw [← hS.ready.2.1] at hck hdk hPprop hacc
  obtain rfl := proposal_call_unique hl hpH (Compose.projAC_callAt.1 hS.call)
    (Compose.projAC_callAt.1 hck) hS.call_proposal hcallk (hS.time.trans htk.symm)
  obtain rfl : ℓp = ℓk := by
    have := (Compose.projAC_callAt.1 hS.call).2.symm.trans (Compose.projAC_callAt.1 hck).2
    simpa using this
  have hpay : P.acPayload = pay := by
    have := hS.payload.symm.trans hdk
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    rw [hpayk, ← this.2]
  obtain ⟨-, hΦpU⟩ := SA.frameIn_of_callAt hr hpH hS.call
  obtain ⟨-, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hslotP : ∀ P' ∈ ℓy.frame.tree, P'.slot = s' + 1 → P' = P :=
    frame_slot_eq_proposal hS hy hcy.1
  -- `Sync` on `[t_{s−1}, t_s]` from `GST(g)`
  have hga : g ≤ sp.ts (s' : Int) := by have := le_gbar g; linarith
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (sp.ts (s' : Int)) (sp.ts ((s' + 1 : Nat) : Int)) hl
    (syncRun_of_gst hS.shared.healthy.1 hga)
  refine hcast ▸ SA.view_agree hac hpH hy hS.ready.2.1 ⟨hS.call, hS.call_proposal, d, hS.payload⟩
    hS.time hcy ⟨P, hPy, hPs, hpay⟩ hsync ?_ ?_
  · -- a voter block stamped before the freeze reaches the proposer by `t_s`
    intro Hd hHd _ hst hFHd
    rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
    rcases stamp_origin hr hy j ℓy hcy.1 Hd hHd with hg | ⟨k', -, ℓk', hck', hHdk', hsk⟩
    · have hG := Store.genesis_mem (Compose.fg_reachable hl hpH iP)
      obtain rfl := hU.1 (hΦyU hHd) ⟨p, hpH, iP, hG⟩ hg
      exact mem_frame_of_held hrun hnc hpH hS.call hG hFHd
    have hfz : SA.freeze sp (s' + 1) = sp.ts (s' : Int) + 3 * sp.Δ := by
      simp only [SA.freeze, hcast]
    rw [hsk, hfz] at hst
    have hlt : tr.time k' < sp.ts (s' : Int) + 3 * sp.Δ :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    exact mem_frame_of_relay hS hy hpH (mem_tree_of_frame hrun hy hck' hHdk')
      (u := sp.ts ((s' + 1 : Nat) : Int)) (by linarith) (by linarith) hS.call hS.time.ge hFHd
  · -- a support head of `P` reaches the voter by its vote
    intro x hx Hd hHd hHdr hFHd
    by_cases hE : tr.time j < sp.ts ((s' + 1 : Nat) : Int) + sp.Δ
    · obtain ⟨P', hP't, hP's, hsup⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hE)
      rw [hes] at hP's hsup
      obtain rfl := hslotP P' hP't hP's
      have hxs : x.slot + 1 = s' + 1 := by
        rw [Compose.payload_eq hS.payload, hsi, hcast] at hx
        simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hx
        rw [SA.state_pool_slot sp hr hpH iP s' x hx.1]
      obtain ⟨H', hH't, hH'r, -⟩ := hsup x (by rw [SA.blockSupport, hpay]; exact hx) hxs
      rwa [hU.1 (hΦpU hHd) (hΦyU hH't) (hHdr.trans hH'r.symm)]
    · exact mem_frame_of_relay hS hpH hy (mem_tree_of_frame hrun hpH hS.call hHd)
        (u := sp.ts ((s' + 1 : Nat) : Int) + sp.Δ) (by linarith) (by rw [hS.time]) hcy.1
        (not_lt.1 hE) hFHd

end Consensus.Goldilocks.Healing

end
