module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticFirstProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.WitnessUnanimity
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The optimistic first-proposal base under growing faults

The growing form of `Healing.optimistic_next_proposal_of_early_witness`
(`Healing/OptimisticBase`): an actual optimistic write of slot `s` by a node honest at its write,
with an early-held floor witness of the prefix `X`, puts `X` below the duty head of every honest
proposal of slot `s + 1`. The writer, the witness holder and the proposer are honest at their own
cuts only, and the proposer's restarts are bounded by its proposal's joinedness, not by a
whole-run premise.

The proposer's finalized tip is compared with `X` through the witness (the common floor); in the
`Σ.F ⪯ X` case the witness and the writer's counted votes and heads reach the proposal
(`relay_source_at_proposal_at`, `SA.Growing.sync_window_before_forward`), the frame geometry is
`witness_frame_at`, and the proposal is `SA.Growing.optimistic_first_proposal_stored_at`. The
proposer's high locks are its own optimistic locks of slot `s`, compatible with the write
(`optimisticLock_pair_compatible_at`, faults counted at the later write). -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    SA.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) := by
  have h := Compose.goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer
    (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- **Two optimistic locks of one slot are compatible**, their writers honest at their own
writes, with fewer than half faulty at the later write. -/
theorem optimisticLock_pair_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {i j s : Nat}
    (hx : x ∈ H (tr.time i)) (hy : y ∈ H (tr.time j))
    (hf : 2 * (H (max (tr.time i) (tr.time j)))ᶜ.ncard < sp.n)
    {D E : SA.Blk sp.n (List (FG.Att sp.n))} {CV CW : Set (Vote sp.n)}
    (hd : SA.OptimisticLockAt tr.projAC x i s D CV)
    (he : SA.OptimisticLockAt tr.projAC y j s E CW) :
    Compatible (tr.HonestBlocksAt H) D E := by
  have hmono := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hj0 := hrun.time_nonneg j
  have hrx := acRun_prefix' hrun hnc hi0
  have hry := acRun_prefix' hrun hnc hj0
  have hd' : SA.OptimisticLockAt (tr.projAC.upTo (tr.time i)) x i s D CV :=
    (SA.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, hd⟩
  have he' : SA.OptimisticLockAt (tr.projAC.upTo (tr.time j)) y j s E CW :=
    (SA.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, he⟩
  obtain ⟨-, hnD, ellD, A, hpD, -, hvD, hhD⟩ := SA.optimisticLockAt_spec hrx hx hd'
  obtain ⟨-, hnE, ellE, A', hpE, -, hvE, hhE⟩ := SA.optimisticLockAt_spec hry hy he'
  have hint := Set.ncard_inter_add_ncard_union (SA.voters CV) (SA.voters CW)
  have hu := Set.ncard_le_ncard (Set.subset_univ (SA.voters CV ∪ SA.voters CW))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hu
  obtain ⟨w, ⟨⟨v, hv, hvw⟩, v', hv', hv'w⟩, hw⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (max (tr.time i) (tr.time j)))ᶜ)
      (t := SA.voters CV ∩ SA.voters CW) (by omega)
  have hw : w ∈ H (max (tr.time i) (tr.time j)) := not_not.mp hw
  have hwi : w ∈ H (tr.time i) := hrun.antitone (le_max_left _ _) hw
  have hwj : w ∈ H (tr.time j) := hrun.antitone (le_max_right _ _) hw
  obtain ⟨a, hai, ev, hev, hevv⟩ := hhD v hv (hvw ▸ hwi)
  obtain ⟨c, hcj, ev', hev', hevv'⟩ := hhE v' hv' (hv'w ▸ hwj)
  obtain ⟨hat, hev⟩ := SA.upTo_voteAt.mp hev
  obtain ⟨hct, hev'⟩ := SA.upTo_voteAt.mp hev'
  have heqv : v = v' := by
    have hvval : v.val = v'.val := hvw.trans hv'w.symm
    have heq := Compose.Growing.one_vote_per_slot_at hrun hnc
      (Compose.Growing.hVoteAt_iff.mpr ⟨hrun.antitone hat (hvw ▸ hwi), hev⟩)
      (Compose.Growing.hVoteAt_iff.mpr
        ⟨hrun.antitone hct (hvval ▸ hv'w ▸ hwj), by simpa only [hvval] using hev'⟩)
      (by simp only [hevv, hevv', (hvD v hv).2.1, (hvE v' hv').2.1])
    exact hevv.symm.trans ((congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      heq.2).trans hevv')
  obtain ⟨R, hR, hRr, hDR⟩ := (hvD v hv).2.2
  obtain ⟨R', hR', hR'r, hER'⟩ := (hvE v' hv').2.2
  have hDU := (SA.frameIn_of_callAt hrx.localRun hx hpD.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hi0)
  have hEU := (SA.frameIn_of_callAt hry.localRun hy hpE.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hj0)
  obtain rfl : R' = R := hU.1 (hEU hR') (hDU hR)
    (hR'r.trans ((congrArg SA.Vote.head heqv).symm.trans hRr.symm))
  exact SA.anc_total hU (hDR.mono hDU) (hER'.mono hEU)

/-- The first next-slot proposal follows the same prefix, before unanimity induction starts. -/
theorem optimistic_next_proposal_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat)) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay)) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hti ▸ hmb
  have hlo : sp.ts s ≤ tr.time i := by rw [hti, hts]; linarith only [hΔ]
  have hslot := SA.proposal_slot (tr := tr.projAC) hti
  have hf3 := hf _ ht0 hib
  have hf2 : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := Fin.pos y
    omega
  have hfq : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    have he : sp.n = sp.toParams.n := rfl
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.n
    omega
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hacG := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hacP := acRun_prefix' hrun hnc ht0
  have hr := hacP.localRun
  have hpre := hrun.upTo ht0
  have hcp : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hdp : (SA.acProposal sp ((tr.projAC.upTo (tr.time i)).state y i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcp
  have hfr : ell.frame = Node.frame (tr.state y i) := by
    have h := Compose.frame_of_projAC hpre hy
      (by rw [RunTrace.upTo_projAC]; exact hcp)
    rwa [RunTrace.upTo_state_of_le hmono le_rfl] at h
  have hFF : ell.frame.F = (tr.state y i).fg.F := by rw [hfr]; rfl
  -- the proposer's restarts are before `t_s`, by the proposal's joinedness
  have hrsP : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k ≤ sp.ts s := by
    have hj := (SA.acProposal_head hdp).1
    have hpost : SA.joined sp ((tr.projAC.upTo (tr.time i)).post i)
        ((tr.projAC.upTo (tr.time i)).time i) := by
      have he := hr.exec i ell hcp.2 (hcp.1 ▸ hy)
      rw [hcp.1] at he
      have heq : ((tr.projAC.upTo (tr.time i)).post i).restartTime =
          ((tr.projAC.upTo (tr.time i)).state y i).restartTime := by
        have hp := congrArg Prod.fst he
        dsimp only at hp
        rw [← hp]
        exact SA.step_restartTime y _ _ _ _ (by rw [hcall]; simp)
      unfold SA.joined at hj ⊢
      rwa [heq]
    intro k hk hrk
    have ht := ((SA.joined_awake sp) _ ro (H (tr.time i))
      ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) (tr.projAC.upTo (tr.time i)) hr y hy i
      ell hcp hpost).2 k hk hrk
    have hslot' : sp.slot (tr.time i) = s + 1 := hslot
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at ht
    change tr.time k ≤ sp.ts s
    rwa [hslot', show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at ht
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := fun k hk hrk =>
    hrsP k hk (ACTrace.upTo_restartAt.mpr ⟨hmono hk, hrk⟩)
  -- the witness and its finalized-tip comparison
  have hfrw : ellw.frame = Node.frame (tr.state w a) := by
    have h := Compose.frame_of_projAC (hrun.upTo (hrun.time_nonneg a)) hw
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hcw⟩)
    rwa [RunTrace.upTo_state_of_le hmono le_rfl] at h
  have hQ : Q ∈ (tr.state w a).fg.tree := by rw [hfrw] at hQw; exact hQw.1
  have hQU : Q ∈ tr.HonestBlocksAt H :=
    ⟨w, a, tr.time a, hrun.time_nonneg a, fun _ hq => hmono hq.le, hw, hQ⟩
  have hai : tr.time a ≤ tr.time i := by linarith only [hat, hlo, hti, hts, hΔ]
  have hFQ0 := hframe.finalized_below_descendant_at hrun hnc hy hw hw
    (by rw [max_eq_left hai]; exact hfq) hlo hti.le hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
  have hXF_case : Anc (tr.HonestBlocksAt H) X ell.frame.F → Anc (tr.HonestBlocksAt H) X d.head := by
    intro hXF
    rw [(SA.acProposal_head hdp).2]
    exact hXF.trans (((SA.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU).mono subU)
  rcases SA.anc_total hU hFQ0 hXQ with hFX | hXF
  swap
  · exact hXF_case (hFF ▸ hXF)
  have hFX' : Anc (tr.HonestBlocksAt H) ell.frame.F X := hFF ▸ hFX
  -- the witness reaches the proposal
  have hsrcQ : Q.root = sp.genesisRoot ∨ ∃ z q, z ∈ H (tr.time q) ∧
      tr.projAC.AcceptAt z q Q ∧ tr.time q < sp.ts s + 2 * sp.Δ := by
    rcases frame_block_acceptance_at hrun hw hcw hQw with hg | ⟨k, hka, hwk, hacc⟩
    · exact Or.inl (by rw [hg]; rfl)
    · obtain ⟨hacc', htk, -⟩ := Healing.ac_block_after
        (hrun.upTo (hrun.time_nonneg k)).toLocalRun hwk
        ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, hacc⟩)
      rw [RunTrace.upTo_projAC] at hacc'
      change tr.time (k + 1) = tr.time k at htk
      refine Or.inr ⟨w, k + 1, by rw [htk]; exact hwk, (ACTrace.upTo_acceptAt.mp hacc').2, ?_⟩
      rw [htk]
      exact (hmono hka.le).trans_lt hat
  obtain ⟨hQt, -⟩ := relay_source_at_proposal_at hrun hnc hsvc hcatch hm hy hc hti hrs hQU hsrcQ
    (hFX'.trans hXQ)
  have hQy : Q ∈ (tr.state y i).fg.tree := by rw [hfr] at hQt; exact hQt.1
  have hhy : floor ≤ ((tr.state y i).fg.σ Q.root).h := by
    rwa [← σ_eq_honest_at hrun hnc (hrun.time_nonneg a) (fun _ hq => hmono hq.le) hw
      ht0 (fun _ hq => hmono hq.le) hy hQ hQy]
  rcases witness_frame_at hrun hnc hframe hy hc hlo hti.le hfq hQy hhy hJ hXQ with
    hXF | ⟨-, hXt, hrootX, hQt', hvQ, hXQf⟩
  · exact hXF_case hXF
  -- the counted votes of the write and their heads are held at the proposal
  have hgg := SA.le_gbar g
  have hsw : SA.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) g (tr.time i) tr.projAC :=
    { message := fun z q v hz hsend hgq y' j ℓ hy' hcj _ hdl =>
        (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          ((service_syncACAt hrun hsvc (lo := g) (hi := tr.time q) le_rfl).1 z q v hz hsend hgq
            le_rfl y' j ℓ hy' hcj hdl))
      relay := fun z q B hz hacc hgq y' j ℓ hy' hcj _ hdl hanc =>
        (service_syncACAt hrun hsvc (lo := g) (hi := tr.time q) le_rfl).2 z q B hz hacc hgq
          le_rfl y' j ℓ hy' hcj hdl hanc }
  have hP : ∀ v ∈ CV, SA.HeldAtProposal (tr.projAC.state y i) ell.frame s v := by
    intro v hv
    obtain ⟨hvs, ⟨k, hk, hsend, hklo, hkhi⟩, Hv, hHvU, hHvr, hDHv, hacc⟩ :=
      Compose.Growing.optimistic_writer_votes_at hrun hnc hx hopt v hv
    have hvheld := SA.Growing.sync_window_before_forward hacG.localRun hsw hk hsend
      (hgg.trans (hm.trans hklo))
      (by change tr.time k + sp.Δ ≤ tr.time i; rw [hti, hts]; linarith only [hkhi, hΔ]) hy hc
      (fun k' hk' hrk => (hrs k' hk' hrk).trans hklo)
      (by change tr.time k + sp.Δ ≤ tr.time i; rw [hti, hts]; linarith only [hkhi, hΔ])
      (fun t htlo hthi => by
        change tr.time k ≤ t at htlo
        change t < tr.time k + sp.Δ at hthi
        have hslt := SA.slot_of_mem sp s (hklo.trans htlo)
          (by rw [hts]; linarith only [hkhi, htlo, hthi])
        rw [hslt, hvs]; omega)
    obtain ⟨hHvt, hstamp⟩ := relay_source_at_proposal_at hrun hnc hsvc hcatch hm hy hc hti hrs
      hHvU (hacc.imp_right fun ⟨k', hk', hacc', ht'⟩ => ⟨x, k', hk', hacc', ht'⟩)
      (hFX'.trans (hXD.trans hDHv))
    exact SA.heldAtProposal_iff.mpr ⟨by rwa [hvs] at hvheld, Hv, hHvt, hHvr, hstamp⟩
  -- the proposer's high locks are its own optimistic locks of slot `s`
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state y i) (tr.time i) s
      X := by
    apply SA.highLocksCompatible_iff.mpr
    intro l hl _ hls L hL hLr
    rw [← hst] at hl
    have hl' : l ∈ ((tr.upTo (tr.time i)).state y i).ac.locks := by
      have h := Compose.projAC_state hpre.toLocalRun hy i
      rw [RunTrace.upTo_projAC] at h
      rwa [h] at hl
    have hlsb := Compose.proposal_locks_slot_of hpre (hnc.upTo _) hf2 hy
      (by rw [RunTrace.upTo_projAC]; exact hcp) hcall
      (by rw [RunTrace.upTo_projAC]; exact hdp) hti l hl'
    have heq : l.slot = s := by omega
    obtain ⟨L', hL', hL'r, -⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : L = L' := hU.1 hL (subU hL') (hLr.trans hL'r.symm)
    obtain ⟨O, hLO, a', CW, ho⟩ := SA.proposal_high_lock hr hy hti hl hls hL' hLr
    rw [heq] at ho
    obtain ⟨ha't, ho⟩ := (SA.upTo_optimisticLockAt hmono).mp ho
    have hya' : y ∈ H (tr.time a') := hrun.antitone ha't hy
    have hmax : max (tr.time a') (tr.time c) ≤ tr.time i := by
      refine max_le ha't ?_
      obtain ⟨hct, -⟩ := SA.optimisticLockAt_spec (acRun_prefix' hrun hnc (hrun.time_nonneg c)) hx
        ((SA.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, hopt⟩)
      change tr.time c < _ at hct
      linarith only [hct, hlo, hti, hts, hΔ]
    have hf' : 2 * (H (max (tr.time a') (tr.time c)))ᶜ.ncard < sp.n := by
      have := hf _ ((hrun.time_nonneg a').trans (le_max_left _ _)) (hmax.trans hib)
      have := Fin.pos y
      omega
    have hLO' := hLO.mono subU
    rcases optimisticLock_pair_compatible_at hrun hnc hya' hx hf' ho hopt with hOD | hDO
    · exact SA.anc_total hU (hLO'.trans hOD) hXD
    · exact SA.anc_total hU hLO' (hXD.trans hDO)
  exact SA.Growing.optimistic_first_proposal_stored_at hacG hx hopt hXD hy hf2 hc hslot hd
    ⟨hXt, Or.inl ⟨hXt, hrootX, Q, hQt', hvQ, hXQf⟩⟩ hP hhigh

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
