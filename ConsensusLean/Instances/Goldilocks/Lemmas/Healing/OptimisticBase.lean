module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance

public section

/-! # Optimistic-lock next-slot propagation

An actual optimistic selection supplies the counted votes, including forwarded faulty
votes. A write-time viable witness supplies the frozen path, not assumed vote-head viability.
The vote and proposal bases are proved separately; later-slot U-W and drain composition
are separate. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The optimistic base G(s+1,X), including below-floor X with a viable descendant Q.
The actual write and its counted set are retained. Q is held in the write frame; its
floor and J are the explicit FS′ values. Service/Catch ends at the next-slot horizon,
and no premise asserts viability of arbitrary honest vote heads. -/
theorem optimistic_next_votes_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt x c ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hh : floor ≤ ((tr.state x c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hx hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨x, hx, c, hQ⟩
  have htw := (SA.optimisticLockAt_spec hS.run hx hopt).1
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hx c ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt htw⟩
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X by
    exact fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e hv hs
    obtain ⟨ell, hc, he⟩ := hv
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hslot : sp.slot (tr.time i) = s + 1 := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
    have hlo : sp.ts s ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
        change (s : Int) ≤ sp.slot (tr.time i)
        rw [hslot]; omega)
    have hhi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
      have ht := SA.vote_time_le hr hy ⟨ell, hcast⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      simpa only [hslot] using ht
    have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := fun hk => (hJ hk).trans hXQ
    rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hx hlo hhi hQ hh hJQ hXQ
      with hFX | hXF
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
      rw [Compose.frame_of_projAC hrun hy hc]
      exact hFX.trans hXQ
    have hcatchTime : gbar g + 2 * sp.Δ ≤
        sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
      rw [hs, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]
      linarith
    have hQdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hx hy hQU
      (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
      (by omega) (hhi.trans hmb) hcatchTime hFQ
    obtain ⟨hXt, hrootX, -, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hx
      hc hlo hhi hQ hh hJ hXQ (mem_tree_of_frame hrun hy hc hQdom.1) hFX
    have hviab : SA.ViableAtVote ell e (s + 1) X := by
      have hdomA := SA.voterBlockTree_anc hr hy hcast
      rw [hs] at hdomA hQdom
      exact Or.inl ⟨hdomA Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩
    have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
      apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
        hm hS.catchUp (by linarith) hx hy hcast hs (hhi.trans hmb)
      intro v hv
      obtain ⟨hvs, hw, Hv, hHv, hHvr, hDHv, ha⟩ := Compose.optimistic_writer_votes hr hx hopt v hv
      refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
      rw [Compose.frame_of_projAC hrun hy hc]
      exact hFX.trans (hXD.trans hDHv)
    exact SA.optimistic_transfer_stored sp hS.run hx hopt hXD (by
      have hn := sp.toParams.hn
      change 0 < sp.n at hn
      omega) hy hcast hs hcarry hviab
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
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith)
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith
  have ha : SA.AcceptedBefore tr.projAC y Q (sp.ts s + 3 * sp.Δ) := by
    rcases hsource with hg | ⟨q, hq, hqt⟩
    · exact Or.inl hg
    by_cases hqg : gbar g ≤ tr.projAC.time q
    · obtain ⟨k, hki, hk, hkt⟩ := hS.sync.relay x hx q Q hq hqg y hy i ell hc
        (by have := hdl i le_rfl _ hqt; change tr.projAC.time i ≤ b at hib; linarith)
        (by have := hdl i le_rfl _ hqt; linarith) hFQ
      exact Or.inr ⟨k, hk, hkt.trans (hdl k hki _ hqt)⟩
    · obtain ⟨k, -, hk, hkt⟩ := hS.catchUp.relay x hx q Q hq (lt_of_not_ge hqg) y hy i ell hc
        (by linarith) hib hFQ
      exact Or.inr ⟨k, hk, by linarith⟩
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
        linarith
      exact SA.mem_tree_of_acceptAt sp hr hy hk hki hc hFQ
  refine ⟨hQt, lt_trans (SA.blockStamp_lt_of_acceptedBefore sp hr hy hc hQt ha
    (fun k hk hrk => by
      change tr.time k < _
      have := hrs k hk hrk
      linarith) (Or.inl (by linarith))) ?_⟩
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- The same-slot proposal base needed by L1.5 Step 4 at label s = s_p−1.
An actual optimistic write and its write-held common-floor witness suffice; recipient
heldness, counted-vote delivery and lock compatibility are derived, not assumed. -/
theorem optimistic_next_proposal_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {contest kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts (s + 1 : Nat))
      floor contest kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt x c ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state x c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay)) :
    Anc (tr.HonestBlocks H) X d.head := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot := SA.proposal_slot (tr := tr.projAC) hti
  have hib : tr.time i ≤ b := hti ▸ hmb
  have hlo : sp.ts s ≤ tr.time i := by rw [hti, hts]; linarith
  have hf2 : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hx hcw hQw
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hj := (SA.acProposal_head hd).1
    have hpost : SA.joined sp (tr.projAC.post i) (tr.time i) := by
      have he := hr.exec i ell hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have heq : (tr.projAC.post i).restartTime = (tr.projAC.state y i).restartTime := by
        have hp := congrArg Prod.fst he
        dsimp only at hp
        rw [← hp]
        exact SA.step_restartTime y _ _ _ _ (by rw [hcall]; simp)
      unfold SA.joined at hj ⊢
      rwa [heq]
    intro k hk hrk
    have ht := ((SA.joined_awake sp) _ ro H (tr.HonestBlocks H) tr.projAC hr y hy i ell hc
      hpost).2 k hk hrk
    rwa [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at ht
  rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hx hlo hti.le hQ hh
    (fun hk => (hJ hk).trans hXQ) hXQ with hFX | hXF
  swap
  · rw [(SA.acProposal_head hd).2]
    have hXF' : Anc (tr.HonestBlocks H) X ell.frame.F := by
      rwa [Compose.frame_of_projAC hrun hy hc]
    exact hXF'.trans ((SA.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU)
  have hFX' : Anc (tr.HonestBlocks H) ell.frame.F X := by
    rwa [Compose.frame_of_projAC hrun hy hc]
  have htw := (SA.optimisticLockAt_spec hS.run hx hopt).1
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hx c ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt htw⟩
  have hQt := (relay_source_at_proposal hS hm hx hy hc hti hib hrs
    (show Q ∈ tr.HonestBlocks H from ⟨x, hx, c, hQ⟩) hsource (hFX'.trans hXQ)).1
  obtain ⟨hXt, hroot, -, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hx hc
    hlo hti.le hQ hh hJ hXQ (mem_tree_of_frame hrun hy hc hQt) hFX
  apply SA.optimistic_first_proposal_stored hS.run hf2 hx hopt hXD hy hc hslot hd
    ⟨hXt, Or.inl ⟨hXt, hroot, Q, hQt, hvQ, hXQf⟩⟩
  · intro v hv
    obtain ⟨hvs, ⟨k, hsend, hklo, hkhi⟩, Hv, hHv, hHvr, hDHv, ha⟩ :=
      Compose.optimistic_writer_votes hr hx hopt v hv
    have hvheld := SA.sync_window_before_forward hr (SA.serviceWindowBefore_of_sync hS.sync)
      hx hsend (hm.trans hklo) (by rw [hti, hts] at hib; linarith) hy hc
      (fun k' hk' hrk => (hrs k' hk' hrk).trans hklo)
      (by change tr.projAC.time k + sp.Δ ≤ tr.time i; rw [hti, hts]; linarith)
      (fun t htlo hthi => by
        have hslt := SA.slot_of_mem sp s (hklo.trans htlo) (by rw [hts]; linarith)
        rw [hslt, hvs]; omega)
    obtain ⟨hHvt, hstamp⟩ := relay_source_at_proposal hS hm hx hy hc hti hib hrs hHv ha
      (hFX'.trans (hXD.trans hDHv))
    exact SA.heldAtProposal_iff.mpr ⟨by rwa [hvs] at hvheld, Hv, hHvt, hHvr, hstamp⟩
  · apply SA.highLocksCompatible_iff.mpr
    intro l hl _ hls L hL hLr
    have hl' : l ∈ (tr.state y i).ac.locks := by
      rwa [Compose.projAC_state hrun.toLocalRun hy i] at hl
    have hbound := Compose.proposal_locks_slot_of hrun hnc hf2 hy hc hcall hd hti l hl'
    have heq : l.slot = s := by omega
    obtain ⟨O, hLO, a, CW, ho⟩ := SA.proposal_high_lock hr hy hti hl hls hL hLr
    rw [heq] at ho
    rcases SA.optimisticLock_pair_compatible hS.run hf2 hy hx ho hopt with hOD | hDO
    · exact SA.anc_total hr.coherent (hLO.trans hOD) hXD
    · exact SA.anc_total hr.coherent hLO (hXD.trans hDO)

/-- MI-opt's bounded later-label propagation: every honest vote and actual proposal
from s+1 through N extends X. The boundary proposal uses the optimistic base directly;
later labels use U-W. This does not prove unlock passage, regular BASE, DESC or drain.
The archived capped H.2 induction (`frontier_heads_transfer`) uses leases rather than
the current FS′ frame and emission-read-point stamps; only its label-induction pattern
is reused here. All witness transport is derived from the actual optimistic write. -/
theorem optimistic_later_heads_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s N floor : Nat}
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor contest kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt x c ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state x c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X) ∧
      (∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
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
  have hQ := mem_tree_of_frame hrun hx hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨x, hx, c, hQ⟩
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hx c ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt
        (SA.optimisticLockAt_spec hS.run hx hopt).1⟩
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsub {lo hi : Time} (hl : sp.ts s ≤ lo) (hh' : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i (hl.trans hlo) (hhi.trans hh'),
      fun y hy i hlo hhi => hframe.contest_iff y hy i (hl.trans hlo) (hhi.trans hh'),
      fun y hy i hlo hhi => hframe.kind_iff y hy i (hl.trans hlo) (hhi.trans hh'),
      fun y hy i hlo hhi => hframe.root_eq y hy i (hl.trans hlo) (hhi.trans hh')⟩
  intro r hrlo
  induction r, hrlo using Nat.le_induction with
  | base =>
    intro hrN
    have ht := hts hrN
    refine ⟨optimistic_next_votes_of_witness hrun hnc hsvc hawake hf hcatch hm
      (by linarith) (hsub le_rfl (by linarith)) hx hopt hXD hcw hQw hh hJ hXQ, ?_⟩
    intro y hy i ell hc hcall hti d pay hd
    exact optimistic_next_proposal_of_witness hrun hnc hsvc hawake hf hcatch hm
      (by linarith) (hsub le_rfl (by linarith)) hx hopt hXD hcw hQw hh hJ hXQ
      hy hc hcall hti hd
  | succ m hsm ih =>
    intro hrN
    have hmN : m ≤ N := by omega
    have hprior := (ih hmN).1
    have ht := hts hrN
    have hms := hts hsm
    have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by rw [hstep] at hms; linarith
    have hwin := hsub (hts (show s ≤ m by omega))
      (show sp.ts (m + 1 : Nat) + sp.Δ ≤ sp.ts N + sp.Δ by linarith)
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
          change (s : Int) ≤ sp.slot (tr.time i)
          rw [hslot]; omega)
      have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
        have h := SA.vote_time_le hr hy ⟨ell, hcast⟩
        change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
        rw [hslot] at h
        exact h
      have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hx hx hlo
        (hhi.trans (by linarith)) hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
      change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
      rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
      have hct : gbar g + 2 * sp.Δ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
        rw [hs, show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]; linarith
      have hdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hx hy hQU
        (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
        (by omega) (hhi.trans (by linarith)) hct hFQ
      refine ⟨mem_tree_of_frame hrun hy hc hdom.1, ?_⟩
      rw [← hs]
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · apply SA.readPoint_blockStamp_lt_of_acceptedBefore hr hy hcast hdom.1 (Or.inl hg)
        · intro k hk hrs
          have h := hnr y hy k (Compose.projAC_restartAt.mp hrs)
          change tr.time k < _
          rw [hs]; unfold SA.freeze; rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]
          linarith
        · have h : sp.ts (m + 1 : Nat) ≤ tr.time i :=
            (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
              change ((m + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
              rw [hslot])
          change SA.freeze sp e.msg.slot ≤ tr.time i
          rw [hs]; unfold SA.freeze
          rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega, hstep] at *
          linarith
      · exact (relay_readPoint_stamp_window_before hr hS.sync hS.catchUp hx hy hq hqt
          hcast (by omega) (hhi.trans (by linarith)) hct hFQ).2
    refine ⟨unanimous_next_votes_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith) hwin hx hQ hh hJ hXQ hheld hprior, ?_⟩
    intro y hy i ell hc hcall hti d pay hd
    have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
    have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith
    have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hx hx hlo hhi
      hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
    change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
    rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
    have hsource' : Q.root = sp.genesisRoot ∨
        ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · exact Or.inl hg
      · exact Or.inr ⟨q, hq, by linarith [hts (show s ≤ m by omega)]⟩
    have hQt := (relay_source_at_proposal hS (hm.trans (hts (by omega))) hx hy hc hti
      (hhi.trans hmb) (fun k hk hrs => (hnr y hy k (Compose.projAC_restartAt.mp hrs)).trans
        (hm.trans (hts (by omega)))) hQU hsource' hFQ).1
    exact unanimous_next_proposal_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith) hwin hx hQ hh hJ hXQ hprior hy hc hcall hti hd
      (mem_tree_of_frame hrun hy hc hQt)

/-- L1.5 Steps 3–4, the witnessed optimistic unlock consumer. `l₀,B` is the
actual live-lock preimage of `l` at the proposer's unlock, not an arbitrary block.
The proposal extends its image, including the boundary s=p−1; for s≤p−2 the
prior-slot honest votes do too. The origin-to-preimage producer remains separate.
Unlike the archived `healing_unanimous_release_compat` lease deletion argument,
current unlock moves to an ancestor (also in the F fallback), so no MI-F is needed. -/
theorem optimistic_unlock_proposal_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s p floor : Nat}
    (hsp : s + 1 ≤ p) (hm : gbar g ≤ sp.ts s) (hpb : sp.ts p + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts p + sp.Δ)
      floor contest kindJ J)
    {y : Fin sp.n} (hy : y ∈ H) {c i : Nat}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC y c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {ellw ell : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt y c ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state y c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hc : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    {l₀ l : SA.Lock} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hl₀ : l₀ ∈ SA.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i))
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l₀.block)
    (hBX : Anc (tr.HonestBlocks H) B X)
    (hl : l = if (l₀.slot : Int) < (p : Int) - 1 then
      ⟨(SA.unlockTarget sp ell.frame
        (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤))
        ((p : Int) - 1) B).root, l₀.slot, l₀.fast⟩ else l₀) :
    l ∈ SA.unlock sp (tr.projAC.state y i).locks ell.frame (tr.time i) ((p : Int) - 1)
      (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤)) ∧
    ∃ B' ∈ ell.frame.tree, B'.root = l.block ∧
      Anc (tr.HonestBlocks H) B' d.head ∧
      (s + 2 ≤ p → ∀ z ∈ H, ∀ k e, SA.VoteAt tr.projAC z k e → e.msg.slot = p - 1 →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B') := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  have hmem : l ∈ SA.unlock sp (tr.projAC.state y i).locks ell.frame (tr.time i)
      ((p : Int) - 1)
      (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤)) :=
    ⟨l₀, hl₀, B, hB, hBr, hl⟩
  have himage : ∃ B' ∈ ell.frame.tree, B'.root = l.block ∧ ell.frame.Anc B' B := by
    subst l
    split_ifs with hlt
    · obtain ⟨hT, hTB⟩ := SA.unlockTarget_anc sp hPhi
        (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤))
        ((p : Int) - 1) hB
      exact ⟨_, hT, rfl, hTB⟩
    · exact ⟨B, hB, hBr, .refl⟩
  obtain ⟨B', hB', hB'r, hB'B⟩ := himage
  have hB'X := (hB'B.mono hPhiU).trans hBX
  have hall := optimistic_later_heads_of_witness hrun hnc hsvc hawake hf hcatch hnr hm hpb
    hframe hy hopt hXD hcw hQw hh hJ hXQ
  refine ⟨hmem, B', hB', hB'r,
    hB'X.trans ((hall p hsp le_rfl).2 y hy i ell hc hcall hti d pay hd), ?_⟩
  intro hgap z hz k e hv hs
  obtain ⟨W, hW, hWr, hXW⟩ := (hall (p - 1) (by omega) (by omega)).1 z hz k e hv hs
  exact ⟨W, hW, hWr, hB'X.trans hXW⟩

/-- The separate writer-local below-root branch of L1.5's optimistic unlock
consumer. An input below the write-time root remains below the same actor's
proposal head under FS′ root monotonicity. No cross-node root or MI-F premise is
used. Transport to another actor's slot-p vote is a separate composition. -/
theorem FrameWindow.unlock_proposal_of_below_write_root {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {c i p : Nat} (hci : c ≤ i)
    {ellw ell : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt y c ellw)
    (hc : tr.projAC.CallAt y i ell) (_hcall : ell.call = .proposal)
    (_hti : tr.time i = sp.ts p) (hclo : lo ≤ tr.time c) (hihi : tr.time i ≤ hi)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    {l₀ l : SA.Lock} {B A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hl₀ : l₀ ∈ SA.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i))
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l₀.block)
    (hBA : Anc (tr.HonestBlocks H) B A) (hroot : ellw.frame.Anc A ellw.frame.fcRoot)
    (hl : l = if (l₀.slot : Int) < (p : Int) - 1 then
      ⟨(SA.unlockTarget sp ell.frame
        (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤))
        ((p : Int) - 1) B).root, l₀.slot, l₀.fast⟩ else l₀) :
    l ∈ SA.unlock sp (tr.projAC.state y i).locks ell.frame (tr.time i) ((p : Int) - 1)
      (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤)) ∧
    ∃ B' ∈ ell.frame.tree, B'.root = l.block ∧ Anc (tr.HonestBlocks H) B' d.head := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  have hAw := hroot.mono (SA.frameIn_of_callAt hr hy hcw).2
  have hmono := hframe.fcRoot_mono hrun hy hci hclo hihi
  have hBc : Anc (tr.HonestBlocks H) B ell.frame.fcRoot := by
    rw [Compose.frame_of_projAC hrun hy hcw] at hAw
    rw [Compose.frame_of_projAC hrun hy hc]
    exact hBA.trans (hAw.trans hmono)
  have hfc : Anc (tr.HonestBlocks H) ell.frame.fcRoot d.head := by
    rw [(SA.acProposal_head hd).2]
    exact (SA.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ (Relation.ReflTransGen.refl : ell.frame.Anc ell.frame.fcRoot ell.frame.fcRoot)).mono hPhiU
  refine ⟨⟨l₀, hl₀, B, hB, hBr, hl⟩, ?_⟩
  subst l
  split_ifs with hlt
  · obtain ⟨hT, hTB⟩ := SA.unlockTarget_anc sp hPhi
      (SA.View.ofLists (SA.voteViewList (tr.projAC.state y i) ell.frame ((p : Int) - 1) ⊤))
      ((p : Int) - 1) hB
    exact ⟨_, hT, rfl, (hTB.mono hPhiU).trans (hBc.trans hfc)⟩
  · exact ⟨B, hB, hBr, hBc.trans hfc⟩

end Consensus.Goldilocks.Healing

end
