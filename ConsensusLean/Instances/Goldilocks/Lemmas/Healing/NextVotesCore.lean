module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shared finite-window next-vote propagation

Witness transport and causal induction do not depend on the kind of lock that supplies
the transfer step. Later-label propagation needs only a next-vote base. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The common witness/relay induction, with the lock-specific transfer left to the caller. -/
theorem next_votes_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) hi floor kindJ J)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (htransfer : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F X →
      SA.ViableAtVote ell e (s + 1) X →
      (∀ z ∈ H, ∀ k < i, ∀ ev, SA.VoteAt tr.projAC z k ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg X) →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hw hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨w, hw, a, hQ⟩
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X from fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e ⟨ell, hc, he⟩ hs
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
    change sp.slot (tr.time i) = s + 1 at hslot
    have hlo : sp.ts s ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
        change (s : Int) ≤ sp.slot (tr.time i); rw [hslot]; omega)
    have hhi : tr.time i ≤ hi := by
      have ht := SA.vote_time_le hr hy ⟨ell, hcast⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      rw [hslot] at ht
      exact ht.trans hnext
    rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hw hlo hhi hQ hh
      (fun hk => (hJ hk).trans hXQ) hXQ with hFX | hXF
    swap
    · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      refine ⟨W, hPhiU hW, hWr, ?_⟩
      have hFW := hFW.mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hc] at hFW
      exact hXF.trans hFW
    have hFQ : Anc (tr.HonestBlocks H) ell.frame.F Q := by
      rw [Compose.frame_of_projAC hrun hy hc]; exact hFX.trans hXQ
    have hQdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hw hy hQU
      (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
      (by omega) (hhi.trans hmb) (by
        rw [hs, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]
        linarith only [sp.toParams.hΔ, hm]) hFQ
    obtain ⟨-, hroot, -, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hw hc
      hlo hhi hQ hh hJ hXQ (mem_tree_of_frame hrun hy hc hQdom.1) hFX
    have hviab : SA.ViableAtVote ell e (s + 1) X := by
      have hdomA := SA.voterBlockTree_anc hr hy hcast
      rw [hs] at hdomA hQdom
      exact Or.inl ⟨hdomA Q hQdom X hXQf, hroot, Q, hQdom, hvQ, hXQf⟩
    exact htransfer y hy i ell e hcast hs hhi hFX hviab
      (fun z hz k hki ev hv hes => ih k hki z hz ev hv hes)

/-- An early writer-held block reaches a proposal through window relay or old-block
Catch. The finite deadline is strictly before the next slot begins. -/
theorem relay_source_at_proposal
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hib : tr.time i ≤ b)
    (hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocks H)
    (hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ)
    (hFQ : Anc (tr.HonestBlocks H) ell.frame.F Q) :
    Q ∈ ell.frame.tree ∧ (tr.projAC.state y i).blockStamp Q.root < ⊤ := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hi : tr.projAC.time i = sp.ts s + 4 * sp.Δ := hti.trans hts
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := deadline_le_restarts (fun r hri hr => hrs r (hri.trans hk) hr) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  have ha : SA.AcceptedBefore tr.projAC y Q (sp.ts s + 3 * sp.Δ) := by
    rcases hsource with hg | ⟨q, hq, hqt⟩
    · exact Or.inl hg
    by_cases hqg : gbar g ≤ tr.projAC.time q
    · obtain ⟨k, hki, hk, hkt⟩ := hS.sync.relay x hx q Q hq hqg y hy i ell hc
        (by
            have := hdl i le_rfl _ hqt; change tr.projAC.time i ≤ b at hib; linarith only [hΔ, hi,
                this, hib])
        (by have := hdl i le_rfl _ hqt; linarith only [hΔ, hi, this]) hFQ
      exact Or.inr ⟨k, hk, hkt.trans (hdl k hki _ hqt)⟩
    · obtain ⟨k, -, hk, hkt⟩ := hS.catchUp.relay x hx q Q hq (lt_of_not_ge hqg) y hy i ell hc
        (by linarith only [hm, hΔ, hi]) hib hFQ
      exact Or.inr ⟨k, hk, by linarith only [hm, hΔ, hkt]⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ell hc
      obtain rfl : Q = G := hr.coherent.1 hQU hGU (hg.trans hGr.symm)
      obtain ⟨hPhi, -⟩ := SA.frameIn_of_callAt hr hy hc
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hki : k ≤ i := by
        by_contra hn
        have ht := hr.time_mono (show i ≤ k by omega)
        linarith only [hΔ, hi, hkt, ht]
      exact SA.mem_tree_of_acceptAt sp hr hy hk hki hc hFQ
  refine ⟨hQt, lt_trans (SA.blockStamp_lt_of_acceptedBefore sp hr hy hc hQt ha
    (fun k hk hrk => by
      change tr.time k < _
      have := hrs k hk hrk
      linarith only [hΔ, this]) (Or.inl (by linarith only [hΔ, hi]))) ?_⟩
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- Unanimity propagation (as `unanimous_next_votes_of_witness`) from a next-vote base; boundary
proposals need a separate base. -/
theorem later_heads_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s N floor : Nat}
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor kindJ J)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hbase : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
          some (d, pay) → Anc (tr.HonestBlocks H) X d.head) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hw hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨w, hw, a, hQ⟩
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro r hrlo
  induction r, hrlo using Nat.le_induction with
  | base => exact fun _ => ⟨hbase, fun h => by omega⟩
  | succ m hsm ih =>
    intro hrN
    have hmN : m ≤ N := by omega
    have hprior := (ih hmN).1
    have ht := hts hrN
    have hms := hts hsm
    have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by rw [hstep] at hms; linarith only [hm, hms]
    have hwin : FrameWindow (tr := tr) (H := H) (sp.ts m)
        (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht])),
       fun y hy i hlo hhi => hframe.kind_iff y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht])),
       fun y hy i hlo hhi => hframe.root_eq y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith only [ht]))⟩
    have hheld : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
        Q ∈ (tr.state y i).fg.tree ∧
          e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp (m + 1)) := by
      intro y hy i e hv hs
      obtain ⟨ell, hc, he⟩ := hv
      have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
      have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
      change sp.slot (tr.time i) = m + 1 at hslot
      have hlo : sp.ts s ≤ tr.time i :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
          change (s : Int) ≤ sp.slot (tr.time i); rw [hslot]; omega)
      have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
        have h := SA.vote_time_le hr hy ⟨ell, hcast⟩
        change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
        rwa [hslot] at h
      have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hw hw hlo
        (hhi.trans (by linarith only [ht])) hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
      change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
      rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
      have hct : gbar g + 2 * sp.Δ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
        rw [hs, show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]; linarith only [hΔ, hwarm]
      have hdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hw hy hQU
        (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
        (by omega) (hhi.trans (by linarith only [hmb, ht])) hct hFQ
      refine ⟨mem_tree_of_frame hrun hy hc hdom.1, ?_⟩
      rw [← hs]
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · apply SA.readPoint_blockStamp_lt_of_acceptedBefore hr hy hcast hdom.1 (Or.inl hg)
        · intro k hk hrs
          have h := hnr y hy k (Compose.projAC_restartAt.mp hrs)
          change tr.time k < _
          rw [hs]; unfold SA.freeze; rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]
          linarith only [hΔ, hwarm, h]
        · have h : sp.ts (m + 1 : Nat) ≤ tr.time i :=
            (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
              change ((m + 1 : Nat) : Int) ≤ sp.slot (tr.time i); rw [hslot])
          change SA.freeze sp e.msg.slot ≤ tr.time i
          rw [hs]; unfold SA.freeze
          rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega, hstep] at *
          linarith only [hhi, h]
      · exact (relay_readPoint_stamp_window_before hr hS.sync hS.catchUp hw hy hq hqt
          hcast (by omega) (hhi.trans (by linarith only [hmb, ht])) hct hFQ).2
    refine ⟨unanimous_next_votes_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith only [hmb, ht]) hwin hw hQ hh hJ hXQ hheld hprior, ?_⟩
    intro _ y hy i ell hc hcall hti d pay hd
    have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
    have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith only [hΔ, ht]
    have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hw hw hlo hhi
      hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
    change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
    rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
    have hsource' : Q.root = sp.genesisRoot ∨
        ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · exact Or.inl hg
      · exact Or.inr ⟨q, hq, by linarith only [hts (show s ≤ m by omega), hqt]⟩
    have hQt := (relay_source_at_proposal hS (hm.trans (hts (by omega))) hw hy hc hti
      (hhi.trans hmb) (fun k hk hrs => (hnr y hy k (Compose.projAC_restartAt.mp hrs)).trans
        (hm.trans (hts (by omega)))) hQU hsource' hFQ).1
    exact unanimous_next_proposal_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith only [hmb, ht]) hwin hw hQ hh hJ hXQ hprior hy hc hcall hti hd
      (mem_tree_of_frame hrun hy hc hQt)

/-- The viable, common-J and optimistic-supporter branches of
`FrameWindow.vote_head_classification`, independent of lock kind. -/
theorem FrameWindow.next_votes_of_supporter {s₀ s floor : Nat}
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts s + 6 * sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) {q : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocks H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hbase : Q ∈ ell.frame.tree → floor ≤ ((tr.state z q).fg.σ Q.root).h →
      (kindJ → Anc (tr.HonestBlocks H) J X) →
      ∀ y ∈ H, ∀ i ev, SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg X)
    (hoptimistic : Q = SA.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, SA.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocks H) Q D →
      ∀ y ∈ H, ∀ i ev, SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg Q) :
    ∀ y ∈ H, ∀ i ev, SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) ev.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega : 1 ≤ s)]; ring
  have htq := SA.vote_time_le hr hz ⟨ell, hc⟩
  have hslot := (SA.castAt_spec hr hz hc).2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hqt : sp.ts s₀ ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) _).2 (by
      change (s₀ : Int) ≤ sp.slot (tr.time q); rw [hslot]; omega)
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hrootVotes : kindJ → Anc (tr.HonestBlocks H) X J →
      ∀ y ∈ H, ∀ i ev, SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg X := by
    intro hk hXJ y hy i ev ⟨elly, hcy, hey⟩ hev
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcy
    have hsl := (SA.castAt_spec hr hy ⟨hcy, hey⟩).2.1.symm.trans hev
    change sp.slot (tr.time i) = s + 1 at hsl
    have hlo : sp.ts s₀ ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
        change (s₀ : Int) ≤ sp.slot (tr.time i); rw [hsl]; omega)
    have hhi := SA.vote_time_le hr hy ⟨elly, hcy, hey⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
    rw [hsl] at hhi
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hhi' : tr.time i ≤ sp.ts s + 6 * sp.Δ := by linarith only [sp.toParams.hΔ, hhi, hts]
    obtain ⟨W, hW, hWr, hRW⟩ := SA.castAt_head_anc hr hy ⟨hcy, hey⟩ (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
    have hRW := hRW.mono hPhiU
    rw [Compose.frame_of_projAC hrun hy hcy] at hRW
    have hkind := (hframe.kind_iff y hy i hlo hhi').mpr hk
    have hroot : (tr.state y i).fg.fcRoot = J :=
      (ite_eq_left hkind).trans (hframe.root_eq y hy i hlo hhi' hk)
    change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot W at hRW
    rw [hroot] at hRW
    exact ⟨W, hPhiU hW, hWr, hXJ.trans hRW⟩
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hframe.vote_head_classification_of_service
    hrun hnc hmf hS hnr hz hc (by linarith only [sp.toParams.hΔ, htq])
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by simpa only [hes] using hm)
    (by rw [hes]; linarith only [sp.toParams.hΔ, hmb, hprev]) (by
      rw [hes]; simp only [SA.freeze]
      have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      rw [← hcast]; linarith only [sp.toParams.hΔ, hm])
  have hPhi := SA.frameIn_of_callAt hr hz hc.1
  have hEQ : Hd = Q := hr.coherent.1 (hPhi.2 hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · have hvQ := hv.2
    rw [Compose.frame_of_projAC hrun hz hc.1] at hvQ
    have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := by
      intro hk
      have hkind := (hframe.kind_iff z hz q hqt (by linarith only [sp.toParams.hΔ, htq])).mpr hk
      have hroot := (hPhi.1.fcRoot_anc_viableHeads Q hv.2).mono hPhi.2
      rw [Compose.frame_of_projAC hrun hz hc.1] at hroot
      change Anc (tr.HonestBlocks H) (tr.state z q).fg.fcRoot Q at hroot
      rwa [show (tr.state z q).fg.fcRoot = (tr.state z q).fg.J from ite_eq_left hkind,
        hframe.root_eq z hz q hqt (by linarith only [sp.toParams.hΔ, htq]) hk] at hroot
    by_cases hJX : kindJ → Anc (tr.HonestBlocks H) J X
    · apply hbase hHd ?_ hJX
      rw [← hframe.floor_eq z hz q hqt (by linarith only [sp.toParams.hΔ, htq])]
      exact hvQ.2.2.2
    · push Not at hJX
      obtain ⟨hk, hn⟩ := hJX
      exact hrootVotes hk ((SA.anc_total hr.coherent hXQ (hJQ hk)).resolve_right hn)
  · exact hrootVotes hj.1 (hj.2 ▸ hXQ)
  · obtain ⟨hA, l, hl, hls, a, hai, D, CV, hop, -, -, -, hQD⟩ := ho
    have hheads := hoptimistic hA a D CV (hes ▸ hop) (hQD.mono hPhi.2)
    intro y hy i ev hv hesv
    obtain ⟨W, hW, hWr, hQW⟩ := hheads y hy i ev hv hesv
    exact ⟨W, hW, hWr, hXQ.trans hQW⟩

end Consensus.Goldilocks.Healing
