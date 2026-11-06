module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.NextVotesCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CarryPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic-lock next-slot propagation

An actual optimistic selection supplies the counted votes, including forwarded faulty
votes. A write-time viable witness supplies the frozen path, not assumed vote-head viability.
The vote and proposal bases are proved separately; later-slot unanimity propagation and drain
composition are separate. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The optimistic base G(s+1,X), including below-floor X with a viable descendant Q.
The actual write and its counted set are retained. Q is held at any honest early cut; its
floor and J are the explicit `FrameWindow` values. Service/Catch ends at the next-slot horizon,
and no premise asserts viability of arbitrary honest vote heads. -/
theorem optimistic_next_votes_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  apply next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hm le_rfl hmb
    hframe hw hat hcw hQw hh hJ hXQ
  intro y hy i ell e hcast hs hhi hFX hviab ih
  have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
    apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
      hm hS.catchUp (by linarith only [hm, sp.toParams.hΔ]) hx hy hcast hs (hhi.trans hmb)
    intro v hv
    obtain ⟨hvs, hw, Hv, hHv, hHvr, hDHv, ha⟩ := Compose.optimistic_writer_votes hr hx hopt v hv
    refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
    rw [Compose.frame_of_projAC hrun hy hcast.1]
    exact hFX.trans (hXD.trans hDHv)
  exact SA.optimistic_transfer_stored sp hS.run hx hopt hXD (by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega) hy hcast hs hcarry hviab ih

/-- The same-slot proposal base at label s = s_p−1.
An actual optimistic write and an early-held common-floor witness suffice; recipient
heldness, counted-vote delivery and lock compatibility are derived, not assumed. -/
theorem optimistic_next_proposal_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts (s + 1 : Nat))
      floor kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
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
  have hlo : sp.ts s ≤ tr.time i := by rw [hti, hts]; linarith only [hΔ]
  have hf2 : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hw hcw hQw
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
  rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hw hlo hti.le hQ hh
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
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  have hQt := (relay_source_at_proposal hS hm hw hy hc hti hib hrs
    (show Q ∈ tr.HonestBlocks H from ⟨w, hw, a, hQ⟩) hsource (hFX'.trans hXQ)).1
  obtain ⟨hXt, hroot, -, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hw hc
    hlo hti.le hQ hh hJ hXQ (mem_tree_of_frame hrun hy hc hQt) hFX
  apply SA.optimistic_first_proposal_stored hS.run hf2 hx hopt hXD hy hc hslot hd
    ⟨hXt, Or.inl ⟨hXt, hroot, Q, hQt, hvQ, hXQf⟩⟩
  · intro v hv
    obtain ⟨hvs, ⟨k, hsend, hklo, hkhi⟩, Hv, hHv, hHvr, hDHv, ha⟩ :=
      Compose.optimistic_writer_votes hr hx hopt v hv
    have hvheld := SA.sync_window_before_forward hr (SA.serviceWindowBefore_of_sync hS.sync)
      hx hsend (hm.trans hklo) (by rw [hti, hts] at hib; linarith only [hib, hklo, hkhi]) hy hc
      (fun k' hk' hrk => (hrs k' hk' hrk).trans hklo)
      (by change tr.projAC.time k + sp.Δ ≤ tr.time i; rw [hti, hts]; linarith only [hklo, hkhi])
      (fun t htlo hthi => by
        have hslt := SA.slot_of_mem sp s (hklo.trans htlo)
          (by rw [hts]; linarith only [hkhi, htlo, hthi])
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

/-- Bounded later-label propagation from an optimistic origin: every honest vote and actual proposal
from s+1 through N extends X. The boundary proposal uses the optimistic base directly;
later labels use unanimity propagation. This does not prove unlock passage, the regular next-vote
base or drain.
The archived capped H.2 induction (`frontier_heads_transfer`) uses leases rather than
the current `FrameWindow` frame and emission-read-point stamps; only its label-induction pattern
is reused here. All witness transport is derived from the actual optimistic write. -/
theorem optimistic_later_heads_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s N floor : Nat}
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X) ∧
      (∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
          some (d, pay) → Anc (tr.HonestBlocks H) X d.head) := by
  intro r hrlo hrN
  have ht : sp.ts (s + 1 : Nat) ≤ sp.ts N :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast (show s + 1 ≤ N from hrlo.trans hrN))
  have hsub {lo hi : Time} (hl : sp.ts s ≤ lo) (hh' : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow (tr := tr) (H := H) lo hi floor kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i (hl.trans hlo) (hhi.trans hh'),
      fun y hy i hlo hhi => hframe.kind_iff y hy i (hl.trans hlo) (hhi.trans hh'),
      fun y hy i hlo hhi => hframe.root_eq y hy i (hl.trans hlo) (hhi.trans hh')⟩
  have hbase := optimistic_next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hm
    (by linarith only [hmb, ht]) (hsub le_rfl (by linarith only [ht])) hx hopt hXD hw hat hcw hQw
    hh hJ hXQ
  obtain ⟨hvote, hproposal⟩ := later_heads_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
    hm hmb hframe hw hat hcw hQw hh hJ hXQ hbase r hrlo hrN
  refine ⟨hvote, ?_⟩
  by_cases heq : r = s + 1
  · subst r
    intro y hy i ell hc hcall hti d pay hd
    exact optimistic_next_proposal_of_early_witness hrun hnc hsvc hawake hf hcatch hm
      (by linarith only [hmb, ht, sp.toParams.hΔ])
      (hsub le_rfl (by linarith only [ht, sp.toParams.hΔ]))
      hx hopt hXD hw hat hcw hQw hh hJ hXQ hy hc hcall hti hd
  · exact hproposal (by omega)

/-- Write-held specialization of optimistic later-label propagation. -/
theorem optimistic_later_heads_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s N floor : Nat}
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor kindJ J)
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
  exact optimistic_later_heads_of_early_witness hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hframe hx hopt hXD hx (SA.optimisticLockAt_spec hS.run hx hopt).1 hcw hQw hh hJ hXQ

/- The full proposal domain needs no frozen stamp. In kind J use J itself;
otherwise the cache's hmax block supplies the root's viable descendant. -/
private theorem proposal_root_viable (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell) :
    ell.frame.fcRoot ∈ ell.frame.viableTree ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, -⟩ := SA.frameIn_of_callAt hr hy hc
  have hR := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, hJ, -, ⟨B, hB, hBJ, hBh⟩, -, ⟨Q, hQ, hQh⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  suffices ∃ W ∈ (Node.frame (tr.state y i)).tree,
      W ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot W by
    rw [← Compose.frame_of_projAC hrun hy hc] at this
    obtain ⟨W, hW, hv, ha⟩ := this
    exact ⟨hPhi.fcRoot_mem, .refl, W, hW, hv, ha⟩
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · obtain ⟨E, hE, hEr, hh⟩ := J_entry_h hR hB
    have hcoh := (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1
    obtain rfl : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hBJ)
    obtain ⟨ht, ha, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hJ
      (by simp only [Goldilocks.Store.headHeightFloor, hk.2, ↓reduceIte, hk.1]
          omega) (fun _ _ => .refl) hJ Relation.ReflTransGen.refl
    exact ⟨_, ht, hv, ha⟩
  · obtain ⟨ht, ha, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hQ
      ((Goldilocks.Store.headHeightFloor_bounds _).2.trans_eq hQh.symm)
      (fun hm hn => (hk ⟨hm, hn⟩).elim) hQ Relation.ReflTransGen.refl
    exact ⟨Q, ht, hv, ha⟩

/-- The optimistic-supporter branch of the regular next-vote base. The early viable witness
is produced at the actual supporter vote, not assumed at its optimistic write.
The regular count/saved-result branches, vote agreement and current-slot optimistic induction
remain separate. -/
theorem FrameWindow.optimistic_supporter_later_heads {s₀ s N floor : Nat}
    {kindJ : Prop} {J L D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {i a : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = SA.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (SA.Vote sp.n)} (hop : SA.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocks H) L D) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ j ev, SA.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg L) ∧
      (∀ y ∈ H, ∀ j ell', tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 =
          some (d, pay) → Anc (tr.HonestBlocks H) L d.head) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hx hc.1
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hroot : ell.frame.Anc ell.frame.fcRoot L := by
    rw [hanchor]; exact SA.fcRoot_anc_getAnchor hPhi _ _
  have hvL : L ∈ ell.frame.viableTree ell.frame.tree := by
    have hR := proposal_root_viable hrun hnc hmf hx hc.1
    have he : L = ell.frame.fcRoot ∨
        L ∈ SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) := by
      rw [hanchor]
      unfold SA.getAnchor
      cases hd : SA.deepest ell.frame _ with
      | none => exact Or.inl rfl
      | some B =>
        rcases (SA.deepest_mem hd).1 with h | h
        · exact Or.inr h
        · exact Or.inl (Set.mem_singleton_iff.mp h)
    rcases he with he | h
    · exact he ▸ hR
    rcases SA.liveLockBlock_candidate hPhi h with hv | hb
    · exact hv
    · have he := Anc.antisymm hPhi.coherent hb hroot
      exact he ▸ hR
  obtain ⟨Q, hQ, hvQ, hLQ⟩ := hvL.2.2
  have hslot := (SA.castAt_spec hr hx hc).2.1.symm.trans hes
  change sp.slot (tr.time i) = s at hslot
  have hlo : sp.ts s ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change (s : Int) ≤ sp.slot (tr.time i)
      rw [hslot])
  have hhi : tr.time i ≤ sp.ts s + sp.Δ := by
    have ht := SA.vote_time_le hr hx ⟨ell, hc⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot] at ht
  have hts : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have htN : sp.ts s ≤ sp.ts N :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast (show s ≤ N by omega))
  have hh : floor ≤ ((tr.state x i).fg.σ Q.root).h := by
    rw [← hframe.floor_eq x hx i (hts.trans hlo) (by linarith only [hhi, htN])]
    rw [Compose.frame_of_projAC hrun hx hc.1] at hvQ
    exact hvQ.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocks H) J L := by
    intro hk
    have hki := (hframe.kind_iff x hx i (hts.trans hlo) (by linarith only [hhi, htN])).mpr hk
    have hroot' := hroot.mono hPhiU
    rw [Compose.frame_of_projAC hrun hx hc.1] at hroot'
    change Anc (tr.HonestBlocks H) (tr.state x i).fg.fcRoot L at hroot'
    have he : (tr.state x i).fg.fcRoot = (tr.state x i).fg.J := ite_eq_left hki
    rw [he, hframe.root_eq x hx i (hts.trans hlo) (by linarith only [hhi, htN]) hk] at hroot'
    exact hroot'
  have hsub : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor kindJ J :=
    ⟨fun y hy j hl hh => hframe.floor_eq y hy j (hts.trans hl) hh,
      fun y hy j hl hh => hframe.kind_iff y hy j (hts.trans hl) hh,
      fun y hy j hl hh => hframe.root_eq y hy j (hts.trans hl) hh⟩
  exact optimistic_later_heads_of_early_witness hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hsub hx hop hLD hx (by linarith only [hhi, sp.toParams.hΔ]) hc.1 hQ hh hJ
    (hLQ.mono hPhiU)

/-- The actual heal proposal is a viable head in every honest slot-p vote's
read domain. Heldness is derived from early readiness or finite relay; the slot-p
proposal arm of voterBlockTree needs no frozen stamp. This is not vote agreement
or current-slot optimistic induction.
The archived repair_h6_frame uses phase/RX-ing store frames, not read points. -/
theorem FrameWindow.proposal_viable_at_cast {s₀ p floor : Nat}
    {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts p + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hm : gbar g ≤ sp.ts s₀)
    (hsp : s₀ ≤ p) (hp0 : 0 < p) (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer p)
    {k : Nat} (hactual : tr.ProposesAt z k P) (hPs : P.slot = p)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, hta⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hcp hd hacc
  have hhead := proposal_head_viable hr hz hcp hcall
    (show tr.projAC.time ip = sp.toParams.slotTime p by rwa [sp.slotTime_eq]) hd
    (proposal_root_viable hrun hnc hmf hz hcp)
  change tr.time ip = sp.ts p at hti
  change tr.time ja = sp.ts p at hta
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hacc : tr.projAC.AcceptAt z ja P := ⟨ella, hca, hblock⟩
  have hPt := (SA.accept_new sp hr hz hacc).1 _ hca
  have hPU := (SA.frameIn_of_callAt hr hz hca).2 hPt
  have hHU := (SA.frameIn_of_callAt hr hz hcp).2
    ((SA.frameIn_of_callAt hr hz hcp).1.viableHeads_subset hhead)
  have hHP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hHU, hPU, hparent⟩
  have hts : sp.ts s₀ ≤ sp.ts p := (SA.ts_le_iff sp).2 (by exact_mod_cast hsp)
  have hslot : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hc).2.1
  have hslot' : sp.slot (tr.time i) = p := hslot.symm.trans hes
  have hlow : sp.ts s₀ ≤ tr.time i := by
    have ht := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) (p : Int)).2
      (by change (p : Int) ≤ (sp.slot (tr.time i) : Int); rw [hslot'])
    exact hts.trans ht
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot'] at ht
  have hH := hhead
  rw [Compose.frame_of_projAC hrun hz hcp] at hH
  have hheldP := mem_tree_of_frame hrun hz hca hPt
  have hh : floor ≤ ((tr.state z ja).fg.σ P.root).h :=
    floor_le_of_honest_ancestor hrun hnc hz hz hH.1
      (by rw [← hframe.floor_eq z hz ip (hti ▸ hts) (by rw [hti]; linarith only [hΔ])]
          exact hH.2.2.2) hheldP hHP
  have hJ : kindJ → Anc (tr.HonestBlocks H) J P := by
    intro hk
    have hroot : Anc (tr.HonestBlocks H) (tr.state z ip).fg.fcRoot d.head :=
      hH.2.2.1.mono (fun B hB => ⟨z, hz, ip, hB⟩)
    have hk' := (hframe.kind_iff z hz ip (hti ▸ hts) (by rw [hti]; linarith only [hΔ])).mpr hk
    change Anc _ (tr.state z ip).fg.fcRoot d.head at hroot
    have he : (tr.state z ip).fg.fcRoot = (tr.state z ip).fg.J := ite_eq_left hk'
    rw [he, hframe.root_eq z hz ip (hti ▸ hts) (by rw [hti]; linarith only [hΔ]) hk] at hroot
    exact hroot.trans hHP
  have hFP : Anc (tr.HonestBlocks H) ell.frame.F P := by
    rw [Compose.frame_of_projAC hrun hy hc.1]
    exact hframe.finalized_below_descendant hrun hnc hmf hy hz hz hlow hhigh
      hheldP hh hJ hheldP Relation.ReflTransGen.refl
  have hPy : P ∈ ell.frame.tree := by
    by_cases hearly : tr.time i < sp.ts p + sp.Δ
    · obtain ⟨Q, hQ, hQs, _⟩ := SA.cast_ready hr hy hc (by rw [hes]; exact hearly)
      rw [hes] at hQs
      exact (proposal_frame_unique hrun hnc hz hdesignated hactual hPs hp0 hy hc.1 hQ hQs) ▸ hQ
    · have hdl : tr.projAC.deadline y i (tr.time ja) ≤ tr.time i := by
        apply (deadline_le_restarts (a := gbar g) (fun r _ hrs =>
          hnr y hy r (Compose.projAC_restartAt.mp hrs)) _).trans
        change max (tr.time ja) (gbar g) + sp.Δ ≤ tr.time i
        rw [hta, max_eq_left (hm.trans hts)]
        exact not_lt.mp hearly
      obtain ⟨q, hqi, haq, _⟩ := hS.sync.relay z hz ja P hacc
        (by change gbar g ≤ tr.time ja; rw [hta]; exact hm.trans hts)
        y hy i ell hc.1 (hdl.trans (hhigh.trans hpb)) hdl hFP
      exact SA.mem_tree_of_acceptAt sp hr hy haq hqi hc.1 hFP
  obtain ⟨_, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hmf hy hz hheldP
    (by rw [hframe.floor_eq y hy i hlow hhigh]; exact hh)
    (fun hm' hn => by
      have hk := (hframe.kind_iff y hy i hlow hhigh).mp ⟨hm', hn⟩
      rw [hframe.root_eq y hy i hlow hhigh hk]
      exact hJ hk) (mem_tree_of_frame hrun hy hc.1 hPy) Relation.ReflTransGen.refl
  rw [← Compose.frame_of_projAC hrun hy hc.1] at hroot hv
  have hdom : P ∈ SA.voterBlockTree sp e.readPoint ell.frame p :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  exact ⟨hv, hdom, hroot, P, hdom, hv, .refl⟩

/-- The viable-supporter branch of the regular fast next-vote base, through the writer's actual
finite update cutoff. The early witness is above the strict-majority result C,
not merely the half-committee fast selection D. -/
theorem regular_fast_next_votes_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts s + 6 * sp.Δ)
      floor kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hfast : SA.FastUpdateAt tr.projAC x c s D CV)
    (hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c)
        (Node.frame (tr.state x c)) s C))
    (hXD : Anc (tr.HonestBlocks H) X D)
    (hCQ : Anc (tr.HonestBlocks H) C Q)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  obtain ⟨ellx, C', hu, hconf, hsel, hCV⟩ := hfast
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hXQ := hXD.trans (hDC.trans hCQ)
  have hfl : SA.FastLockAt tr.projAC x c s D CV :=
    Or.inl ⟨ellx, C, hu, hconf, hsel, hCV⟩
  apply next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hm (by
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith [sp.toParams.hΔ]) hmb hframe hw hat hcw hQw hh hJ hXQ
  intro y hy i ell e hcast hs hhigh hFX hviab ih
  have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
  change sp.slot (tr.time i) = s + 1 at hslot
  have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
    apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
      hm hS.catchUp (by linarith only [hm, sp.toParams.hΔ]) hx hy hcast hs (hhigh.trans hmb)
    intro v hv
    obtain ⟨hvs, hw, Hv, hHv, hHvr, hDHv, ha⟩ := fastLock_writer hr hx hfl v hv
    refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
    rw [Compose.frame_of_projAC hrun hy hcast.1]; exact hFX.trans (hXD.trans hDHv)
  exact SA.first_transfer_stored_window_before sp hS.run
    (SA.serviceWindowBefore_of_sync hS.sync) hm hx hfl (hu.2.2.1.trans_le hmb)
    hXD hy hcast hs hcarry
    (faultBound_of_service hawake hf hnr (hr.time_nonneg i) (by
      change gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
      rw [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]; exact hm)
      (hhigh.trans hmb)) hviab ih

/-- A finite-window result has an actual earlier honest supporter. Participation
is derived from the two actual voting deadlines, not assumed of the update. -/
theorem result_honest_supporter_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x c s C CV) (hcb : tr.time c ≤ b) :
    ∃ z ∈ H, ∃ q < c, ∃ e, SA.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  obtain ⟨ell, hu, hconf, hCV⟩ := hres
  have hHV : H ⊆ SA.voters {v | v ∈ (tr.projAC.state x c).pool s} := fun z hz =>
    SA.honest_voter_at_update_before hS
      (fun y hy r hrs => hnr y hy r (Compose.projAC_restartAt.mp hrs)) hx hu hm hcb hz
  apply SA.result_honest_supporter_of_participants sp hS.run hx
    ⟨ell, hu, hconf, hCV⟩ .refl
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hnpos := sp.toParams.hn
  change 0 < sp.n at hnpos
  have := Set.ncard_le_ncard hHV
  omega

/-- The regular fast next-vote base: actual update provenance supplies the result and its honest
supporter; the viable, common-J and optimistic-stuck cases of
`FrameWindow.vote_head_classification` are all discharged.
No supporter viability or write-time witness is assumed. This is the next-vote
base only, not the slow base, later-label `FrameWindow.regular_later_heads`, vote agreement,
current-slot optimistic induction or drain. -/
theorem FrameWindow.regular_fast_next_votes {s₀ s floor : Nat}
    {kindJ : Prop} {J X D : SA.Blk sp.n (List (FG.Att sp.n))}
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
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hfast : SA.FastUpdateAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  obtain ⟨ellx, C, hu, hconf, hsel, hCV⟩ := hfast
  have hfast : SA.FastUpdateAt tr.projAC x c s D CV :=
    ⟨ellx, C, hu, hconf, hsel, hCV⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega : 1 ≤ s)]; ring
  have hms : gbar g + 4 * sp.Δ ≤ sp.ts s := by linarith [sp.toParams.hΔ]
  obtain ⟨z, hz, q, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before hrun hnc hsvc hawake hf hcatch hnr hms hx hres
      (hu.2.2.1.trans_le hmb)
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hXQ := hXD.trans (hDC.trans hCQ)
  have htq := SA.vote_time_le hr hz ⟨ell, hc, he⟩
  have hslot := (SA.castAt_spec hr hz ⟨hc, he⟩).2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  apply hframe.next_votes_of_supporter hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr hXQ
  · intro hQ hh hJX
    apply regular_fast_next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [hms, sp.toParams.hΔ]) hmb
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi,
       fun y hy i hlo hhi => hframe.kind_iff y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi,
       fun y hy i hlo hhi => hframe.root_eq y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi⟩
      hx hfast ?_ hXD hCQ hz (by linarith only [htq, sp.toParams.hΔ]) hc hQ hh hJX
    simpa only [Compose.frame_of_projAC hrun hx hu.1] using hres
  · intro hA a D' CV' hop hQD
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hnext : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
        (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i hlo
          (by linarith only [hts, hhi, sp.toParams.hΔ]),
       fun y hy i hlo hhi => hframe.kind_iff y hy i hlo
          (by linarith only [hts, hhi, sp.toParams.hΔ]),
       fun y hy i hlo hhi => hframe.root_eq y hy i hlo
          (by linarith only [hts, hhi, sp.toParams.hΔ])⟩
    exact (hnext.optimistic_supporter_later_heads hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [hms, sp.toParams.hΔ]) (by omega) (by omega)
      (by linarith only [hmb, hts, sp.toParams.hΔ])
      hz ⟨hc, he⟩ hes hA hop hQD (s + 1) le_rfl le_rfl).1

/-- The boundary optimistic anchor prefix, with actual CV delivery supplied
from its honest writer. No next-slot unanimity or earlier-vote IH is used. -/
theorem optimistic_prefix_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {c i : Nat}
    {D B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocks H) B D)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b)
    (hFD : Anc (tr.HonestBlocks H) ell.frame.F D)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
    apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
      hm hS.catchUp (by linarith only [hm, sp.toParams.hΔ]) hx hy hc hes hib
    intro v hv
    obtain ⟨hvs, hw, Hv, hHv, hHvr, hDHv, ha⟩ := Compose.optimistic_writer_votes hr hx hopt v hv
    exact ⟨hvs, hw, Hv, hHv, hHvr, hFD.trans hDHv, ha⟩
  have hhalf : 2 * Hᶜ.ncard < sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  rw [← SA.viableTree_voteDomain_eq_of_viable ⟨B, hB⟩]
  exact SA.optimistic_prefix_of_carry sp hS.run hx hopt hBD hhalf hy hc hes hcarry
    (SA.viableTree_voterBlockTree_subset_voteDomain hB) haB

end Consensus.Goldilocks.Healing

end
