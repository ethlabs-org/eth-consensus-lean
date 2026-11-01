module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree

public section

/-! # Goldilocks Healing: post-reset duty suppliers

The source and transport facts are in `Outcome.Foundation`; the proposal pivot is in
`Outcome.Pivot`. The duty conclusions here may use both without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Actual honest proposals are unique in honest frames at their positive slot.
This uses no payload-support clause of `ReadyProposal`. -/
theorem reset_proposal_frame_unique
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hPprop, -, ja, -, hacc, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hPprop hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hr hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hQf : SA.HonestFrameBlock tr.projAC H Q := ⟨y, hy, j, ell, hcall, hQ⟩
  have hroot : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
    obtain rfl := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcall).2 hQ)
      ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block P Q ⟨p, hP.1, ja, ellp, hcp, hPm⟩ hQf (hPprop ▸ hP.1)
    (by rw [hPprop, hac.honest.proposer Q hQf hroot, hQu, hP.2.1])
    (by rw [hP.2.2.2.2.1, hQu])).symm

/-- Payload support is transported only above the receiver's `F`. Early votes use their
actual readiness witness; deadline votes use guarded relay, not ready-proposal support. -/
theorem reset_support_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    {v : SA.Vote sp.n} (hv : v ∈ pay.2) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs hsup
    obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact SA.slot_of_mem sp _ le_rfl ((SA.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = SA.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold SA.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [SA.state_pool_slot sp hr hP.1 i s v hv.1]
    obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((SA.frameIn_of_callAt hr hP.1 hci).2 hB)
      ((SA.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact reset_frame_relay hp hc hP.1 hy hci hcy.1 hB hg
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A pre-freeze voter block reaches the proposal frame under the proposer's `F` guard. -/
theorem reset_frozen_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, -, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < SA.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply reset_frame_relay hp hc hy hpH hcq hci hBq hg ?_ hF
    rw [hti]
    simp only [SA.freeze, SA.SAParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith

/-- Guarded incidence gives view agreement on common held targets. Proposal heldness at the
voter remains explicit; this lemma does not supply viable-tree membership. -/
theorem reset_views_agree
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (sp.ts s) (sp.ts (s + 1 : Nat)) hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans hg))
  apply SA.view_agree hac hP.1 hy hP.2.1 ⟨hci, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hP.2.2.2.2.1, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hgi hB hstamp hF
  · intro v hv B hB hBr hF
    exact reset_support_frame hp hc hP hci hd hti hpay hy hcy hes hgj hv hB hBr hF

/-- **The joined duty, unanimity** (§23; phase-service §10, "Join with RN/RU"): under the reset
premises and `Catch(2Δ)`, every honest vote of the slot `u` of an honest ready proposal `P` with
`t_u ≥ R` is `P`. -/
theorem ready_unanimous (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) : Unanimous tr H u P := by
  sorry

/-- **The joined duty at the update** (§23, §17 "Exact remaining premise"; phase-service §10;
restated with the healing orb, workbench#30-style): under the reset premises and `Catch(2Δ)`, for
an honest ready proposal `P` of slot `u` with `t_u ≥ R` and every honest node `z` running its
update of slot `u` (at `t_u + 6Δ`, joined, cut `kz`): either the result is `P`, not vetoed, its
fast test selects `P`, and every FG source `z` returns at a cut at or after the update, at its
time, extends `P`; or some honest node has an actual `ac_to_fg` report `C` by then that extends
`P` with a greater state height than `P` in the reporter's state (a higher source; `P` need not
be an entry). -/
theorem ready_update (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) {z : Fin sp.n} (hz : z ∈ H) {kz : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC z kz u ℓ) :
    (SA.getConfirmation sp (tr.projAC.state z kz) ℓ.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state z kz).locks ℓ.frame (tr.time kz) P ∧
      SA.fastSelect sp (tr.projAC.state z kz) ℓ.frame u P = some P ∧
      ∀ k' ℓ' C, kz ≤ k' → SA.ToFGAt tr.projAC z k' ℓ' C → tr.time k' = tr.time kz →
        Anc (tr.HonestBlocks H) P C) ∨
    ∃ z' ∈ H, ∃ r ℓ' C, SA.ToFGAt tr.projAC z' r ℓ' C ∧ tr.time r ≤ tr.time kz ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z' r).fg.σ P.root).h < ((tr.state z' r).fg.σ C.root).h := by
  sorry

/-- **Report coverage** (workbench#30 `entry-rows-exact.md` §2, the exact acquisition supplier
of `entry_rows`): for an honest ready proposal `P` of slot `u` with `t_u ≥ R`, by
`d = t_u + 6Δ` either every honest node has an actual `ac_to_fg` report `C` extending `P` (a
report that suppresses a later one counts at its own cut), or some honest node has an actual
report `C` extending `P` of a greater state height than `P` (a higher source). (`ready_update`'s
returned-source clause is vacuous when nothing is returned; this supplier quantifies over every
honest node's actual reports.) -/
theorem report_cover (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) :
    (∀ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  sorry

end Consensus.Goldilocks.Healing

end
