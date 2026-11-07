module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CorePending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Unanimity of the post-drain slot under growing faults

The growing form of `Healing.ResetPremisesUpTo.operational_unanimous` (Outcome/Supplier): every
vote of slot `u` by a node honest at its cast, by `b`, is for the actual post-drain proposal. The
proposer's frame is read at its call, and each voter's frame at its cast, on the prefix through
that cut over the validators honest there; the ghost walk is the static one. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Every vote of slot `u` by a node honest at its cut, by `b`, is for the post-drain operational
proposal `P` of slot `u`, whose proposer is honest through `t_u + hold`. -/
theorem operational_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hub : sp.ts u ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      tr.time j ≤ b → e.msg.head = P.root := by
  have hDelta := sp.toParams.hΔ
  have hca := hp.cutZ_lt_reset_at
  have hcut := lt_cutZ (sp := sp) g
  have hga0 := SA.gbar_nonneg g
  have ha0 : 0 ≤ a := by linarith
  have hu : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hg : SA.gbar g ≤ sp.ts s := by
    have hle : sp.ts (sp.slot a) + 4 * sp.Δ ≤ sp.ts s := by
      have hs : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts s :=
        (SA.ts_le_iff sp).2 (by omega)
      simpa only [SAParams.ts, mul_add, mul_one] using hs
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have he : sp.ts ((sp.slot a : Int) + 1) = sp.ts (sp.slot a) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    rw [he] at ha'
    linarith
  have hgu : SA.gbar g + 2 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by
    have hs : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  have hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ sp.ts (s + 1 : Nat) := by
    rw [cutZ_eq] at hca
    have hqa := (SA.ts_le_iff_le_slot sp ha0 _).1 hca.le
    have hqs : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s :=
      (SA.ts_le_iff sp).2 (by push_cast at hqa ⊢; omega)
    have hs : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  obtain ⟨_, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, _, _, hpay, _⟩ :=
    honestProposalRun_of_proposesAt_at hp.run hp.noColl hpH hdesignated hactual hPs
  rw [← hdesignated] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  have hib : tr.time i ≤ b := hti ▸ hub
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ :=
    hp.reset_pivot_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ
  have hi0 := hp.run.time_nonneg i
  have hpi : p ∈ H (tr.time i) := hp.run.antitone (by rw [hti, hold]; linarith) hpH
  have hrp := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hp.run.upTo hi0) (hp.noColl.upTo _)).localRun
  have hci' : (tr.upTo (tr.time i)).projAC.CallAt p i ellp := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  obtain ⟨hPhi, hPhiU₀⟩ := SA.frameIn_of_callAt hrp hpi hci'
  have hPhiU : ellp.frame.tree ⊆ tr.HonestBlocksAt H :=
    hPhiU₀.trans (RunTrace.honestBlocks_upTo_subset hp.run.time_mono hi0)
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set W₁ := SA.ghost sp (ellp.frame.viableTree ellp.frame.tree)
    (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s) with hW₁
  have hTp : ellp.frame.viableTree ellp.frame.tree ⊆ ellp.frame.tree := fun _ h => h.1
  have hQ : d.head = W₁ ellp.frame.tree.ncard d.start := by
    rw [hW₁]
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop₀ := SA.ghost_stopped hPhi.coherent hTp (hPhi.finite.subset hTp)
    (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
    (Set.ncard_le_ncard hTp hPhi.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m)
      (by rw [h0]; exact hstop₁)).trans h0
  have hXQend : ∀ {X}, ellp.frame.Anc D X → ellp.frame.Anc X d.head →
      W₁ ellp.frame.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, _, hkx⟩ := SA.ghost_visits hPhi.coherent hTp _ (hsD.trans hDX) (hQ ▸ hXQ)
    rw [← hW₁] at hkx
    have hadd := hW₁add kx ellp.frame.tree.ncard d.start
    rw [hkx] at hadd
    rw [← hadd, add_comm, hW₁add, ← hQ, hstopQ]
  intro y j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hy hv hes hjb
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : SA.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x j' e' hx hj' hv' hs' => ih j' hj' x e' hx hv' hs'
        ((hp.run.time_mono hj'.le).trans hjb)
    have hj0 := hp.run.time_nonneg j
    have hry := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
      (tr.upTo (tr.time j)) proposer (hp.run.upTo hj0) (hp.noColl.upTo _)).localRun
    have hcy' : SA.CastAt (tr.upTo (tr.time j)).projAC y j elly e := by
      rw [RunTrace.upTo_projAC]
      exact SA.upTo_castAt.mpr ⟨le_rfl, hcy⟩
    obtain ⟨hPsi, hPsiU₀⟩ := SA.frameIn_of_callAt hry hy hcy'.1
    have hPsiU : elly.frame.tree ⊆ tr.HonestBlocksAt H :=
      hPsiU₀.trans (RunTrace.honestBlocks_upTo_subset hp.run.time_mono hj0)
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (SA.ts_le_iff_le_slot sp hj0 _).2
      have := (SA.castAt_spec hry hy hcy').2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hroot := hp.reset_vote_root_below_proposal_at hc hpH hactual hPs hR hci hcall hd hti hib
      hPQ hy hcy hes hjb
    have hPy := hp.reset_proposal_frame_at hc hpH hdesignated hactual hPs (by omega) hy hcy hes
      hjb hgj (hjoin.trans hjt) ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := hp.reset_proposal_viable_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ
      hy hcy hes hjb hPy
    obtain ⟨hstep₀, hP₀⟩ := hp.reset_stop_at_parent_at hc hpH hdesignated hactual hPs hR
      hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu) hgj
      (hti ▸ hjoin) (hjoin.trans hjt) hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y j elly e hy hcy hes hjb hE
    rw [hcast] at hXend
    rw [SA.viableTree_voteDomain_eq_of_viable ⟨P, hPv⟩] at hXend
    set W₂ := SA.ghost sp
      (elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
      (SA.goldfishScore sp elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (SA.goldfishEligible sp elly.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s) with hW₂
    have hTy : elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ⊆
        elly.frame.tree := fun _ h => h.1.1
    have hXP : ∃ fX, W₂ fX X = P := by
      rcases hXc with rfl | ⟨hDX, hXQ⟩
      · exact ⟨0, rfl⟩
      refine ⟨ellp.frame.tree.ncard + 1, SA.ghost_follow _ X (hXQend hDX hXQ) hstop₁ ?_
        hstep₀ hP₀⟩
      intro m hm hne C hC
      by_cases hXe : X = d.head
      · exact absurd (by rw [hXe]; exact hstopQ m) hne
      have hXt := (Anc.mem hXQ hXe).1
      have hXm : ellp.frame.Anc X (W₁ m X) := SA.anc_ghost hTp m hXt
      have hmem : W₁ m X ∈ ellp.frame.tree := by
        rcases eq_or_ne (W₁ m X) X with he | he
        · rw [he]; exact hXt
        · exact (Anc.mem hXm (Ne.symm he)).2
      have hend : W₁ (ellp.frame.tree.ncard - m) (W₁ m X) = d.head := by
        rw [← hW₁add, Nat.add_sub_cancel' hm.le]
        exact hXQend hDX hXQ
      have hQm : ellp.frame.Anc (W₁ m X) d.head :=
        hend ▸ SA.anc_ghost hTp _ hmem
      have hCQ : ellp.frame.Anc C d.head := by
        have hw := SA.walkEnd_ghost
          (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
          (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
          hPhi.coherent hTp (hPhi.finite.subset hTp)
          (Set.ncard_le_ncard hTp hPhi.finite) d.start
        rw [← hW₁, ← hQ] at hw
        obtain ⟨f, hf, _⟩ := SA.walkEnd_iff.1
          (hw.of_anc hPhi.coherent hTp (hsD.trans (hDX.trans hXm)) hQm)
        cases f with
        | zero => exact absurd hf hne
        | succ f =>
          have h1 : W₁ 1 (W₁ m X) = C := SA.ghost_succ_of_best 0 _ hC
          rw [hW₁] at h1
          rw [show f + 1 = 1 + f by omega, SA.ghost_add, h1] at hf
          exact hf ▸ SA.anc_ghost hTp f (hTp hC.1.1)
      exact hp.reset_suffix_best_at hc hpH hdesignated hactual hPs hci hcall hd hti hpay hPQ
        hy hcy hes hib hjb hPv hg (hti ▸ hgu) hgj (hti ▸ hjoin) (hjoin.trans hjt)
        hQt hQm hne (hviab _ (hDX.trans hXm) hQm) hCQ
        ((haX.mono hPsiU).trans (hXm.mono hPhiU)) hC
    obtain ⟨fX, hfX⟩ := hXP
    have hspec := SA.castAt_head_of_viable hry hy hcy' (hes ▸ ⟨P, hPv⟩)
    rw [hes, hcast] at hspec
    rw [hspec]
    congr 1
    change W₂ elly.frame.tree.ncard (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) = P
    obtain ⟨ky, _, hky⟩ := SA.ghost_visits hPsi.coherent hTy _ haX hXend
    have hP₂ : W₂ (ky + fX) (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) = P := by
      rw [hW₂, SA.ghost_add, ← hW₂]
      rw [← hW₂] at hky
      rw [hky]; exact hfX
    have hstop₂ := SA.ghost_stopped hPsi.coherent hTy (hPsi.finite.subset hTy)
      (sc := SA.goldfishScore sp elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (el := SA.goldfishEligible sp elly.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (Set.ncard_le_ncard hTy hPsi.finite) (SA.getAnchor sp e.readPoint elly.frame (tr.time j))
    rw [← hW₂] at hstop₂
    have hmax₁ := SA.ghost_fuel_stable (le_max_left elly.frame.tree.ncard (ky + fX)) hstop₂
    have hmax₂ := SA.ghost_fuel_stable (le_max_right elly.frame.tree.ncard (ky + fX)) (hP₂ ▸ hP₀)
    rw [← hW₂] at hmax₁ hmax₂
    rw [← hmax₁, hmax₂, hP₂]

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
