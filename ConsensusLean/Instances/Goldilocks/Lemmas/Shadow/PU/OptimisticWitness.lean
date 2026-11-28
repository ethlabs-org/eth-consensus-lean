module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LaterHead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.PivotOld
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticFirstProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic early-witness propagation over the shadow P-U run

The stock optimistic transfer reads the proved AC projection. Historical sends and acceptances
are transported from the writer's honest prefix to independently honest readers.
-/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State} {hold : Time}

/-! ## Optimistic proposal and lock facts -/

private theorem relay_source_at_proposal_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocksAt H)
    (hsource : Q.root = sp.genesisRoot ∨ ∃ z q, z ∈ H (tr.time q) ∧
      tr.projAC.AcceptAt z q Q ∧ tr.time q < sp.ts s + 2 * sp.Δ)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ ell.frame.tree ∧ (tr.projAC.state y i).blockStamp Q.root < ⊤ := by
  have hΔ := sp.toParams.hΔ
  have hi : tr.time i = sp.ts s + 4 * sp.Δ := hti.trans (AC.ts_succ s)
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hri hrr => hrs r (hri.trans hk) hrr) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith)
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith
  have ha : Q.root = sp.genesisRoot ∨
      ∃ k ≤ i, tr.projAC.AcceptAt y k Q ∧ tr.time k < sp.ts s + 3 * sp.Δ := by
    rcases hsource with hg | ⟨z, q, hz, hq, hqt⟩
    · exact Or.inl hg
    right
    by_cases hqg : gbar g ≤ tr.time q
    · obtain ⟨k, hki, hk, hkt⟩ := (Healing.Growing.KernelProof.service_syncACAt hrun hsvc
        (lo := g) (hi := tr.time q) le_rfl).2 z q Q hz hq
        ((AC.le_gbar g).trans hqg) le_rfl y i ell hy hc
        (by have := hdl i le_rfl _ hqt
            change tr.projAC.deadline y i (tr.time q) ≤ tr.time i
            linarith) hFQ
      exact ⟨k, hki, hk, hkt.trans (hdl k hki _ hqt)⟩
    · obtain ⟨k, hki, hk, hkt⟩ := hrun.toLocalRun.acCatchAt hcatch hz hq
        (lt_of_not_ge hqg) hy hc (by linarith) hFQ
      exact ⟨k, hki, hk, by linarith⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hki, hk, -⟩
    · obtain ⟨hPhi, hPhiU⟩ := Compose.Growing.frameIn_at hrun hnc hy hc
      have hQF := Compose.Growing.honestAt_genesis_root_anc hrun hU hQU hg
        (hPhiU hPhi.rooted.1)
      exact (Anc.antisymm hU hFQ hQF) ▸ hPhi.rooted.1
    · exact Compose.Growing.mem_tree_of_acceptAt_at hrun hnc hy hk hki hc hFQ
  have hbs := Compose.Growing.blockStamp_lt_of_acceptedBefore_at hrun hnc hy hc hQt
    (ha.imp_right fun ⟨k, _, hk, hkt⟩ => ⟨k, hk, hkt⟩)
    (fun k hk hrk => by linarith only [hrs k hk hrk, hΔ])
    (by linarith only [hi, hΔ])
  exact ⟨hQt, lt_trans hbs (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩

private theorem optimisticLock_pair_compatible_at
    {K : AC.CommitteeDict sp.n} {g b : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {i j s : Nat}
    (hx : x ∈ H (tr.time i)) (hy : y ∈ H (tr.time j))
    (hf : 2 * (K.committee s ∩ (H (max (tr.time i) (tr.time j)))ᶜ).ncard < sp.committeeSize)
    {D E : AC.Blk sp.n (List (FG.Att sp.n))} {CV CW : Set (AC.Vote sp.n)}
    (hd : AC.OptimisticLockAt tr.projAC x i s D CV)
    (he : AC.OptimisticLockAt tr.projAC y j s E CW) (hK : CommitteeHalfUpTo tr H K g b) :
    Compatible (tr.HonestBlocksAt H) D E := by
  have hmono := hrun.time_mono
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hj0 := hrun.time_nonneg j
  have hrx := Compose.goldilocks_ac_projection_from (hrun.upTo hi0) (hnc.upTo _)
  have hry := Compose.goldilocks_ac_projection_from (hrun.upTo hj0) (hnc.upTo _)
  rw [RunTrace.upTo_projAC] at hrx hry
  have hd' := (AC.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, hd⟩
  have he' := (AC.upTo_optimisticLockAt hmono).mpr ⟨le_rfl, he⟩
  obtain ⟨-, hnD, ellD, A, hpD, -, hvD, hhD, hKD⟩ := AC.optimisticLockAt_spec hrx hx hd' K
    (fun σ v hv => (AC.CommitteePAt.upTo hmono hrun.antitone hK.facts.hP _).1 x hx _ σ v hv)
  obtain ⟨-, hnE, ellE, A', hpE, -, hvE, hhE, hKE⟩ := AC.optimisticLockAt_spec hry hy he' K
    (fun σ v hv => (AC.CommitteePAt.upTo hmono hrun.antitone hK.facts.hP _).1 y hy _ σ v hv)
  have hint := Set.ncard_inter_add_ncard_union (AC.voters CV) (AC.voters CW)
  have hu := Set.ncard_le_ncard (Set.union_subset hKD hKE)
  rw [hK.facts.hsize s] at hu
  obtain ⟨w, ⟨⟨v, hv, hvw⟩, v', hv', hv'w⟩, hw⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (s := K.committee s ∩ (H (max (tr.time i) (tr.time j)))ᶜ)
      (t := AC.voters CV ∩ AC.voters CW) (by omega)
  have hw : w ∈ H (max (tr.time i) (tr.time j)) := by
    by_contra hn
    exact hw ⟨hKD ⟨v, hv, hvw⟩, hn⟩
  have hwi : w ∈ H (tr.time i) := hrun.antitone (le_max_left _ _) hw
  have hwj : w ∈ H (tr.time j) := hrun.antitone (le_max_right _ _) hw
  obtain ⟨a, hai, ev, hev, hevv⟩ := hhD v hv (hvw ▸ hwi)
  obtain ⟨c, hcj, ev', hev', hevv'⟩ := hhE v' hv' (hv'w ▸ hwj)
  obtain ⟨hat, hev⟩ := AC.upTo_voteAt.mp hev
  obtain ⟨hct, hev'⟩ := AC.upTo_voteAt.mp hev'
  have heqv : v = v' := by
    have hvval : v.val = v'.val := hvw.trans hv'w.symm
    have heq := Compose.Growing.one_vote_per_slot_at hrun hnc
      (Compose.Growing.hVoteAt_iff.mpr ⟨hrun.antitone hat (hvw ▸ hwi), hev⟩)
      (Compose.Growing.hVoteAt_iff.mpr
        ⟨hrun.antitone hct (hvval ▸ hv'w ▸ hwj), by simpa only [hvval] using hev'⟩)
      (by simp only [hevv, hevv', (hvD v hv).2.1, (hvE v' hv').2.1])
    exact hevv.symm.trans ((congrArg (fun e : AC.Em sp (List (FG.Att sp.n)) => e.msg)
      heq.2).trans hevv')
  obtain ⟨R, hR, hRr, hDR⟩ := (hvD v hv).2.2
  obtain ⟨R', hR', hR'r, hER'⟩ := (hvE v' hv').2.2
  have hDU := (AC.frameIn_of_callAt hrx.localRun hx hpD.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hi0)
  have hEU := (AC.frameIn_of_callAt hry.localRun hy hpE.1).2.trans
    (RunTrace.honestBlocks_upTo_subset hmono hj0)
  obtain rfl : R' = R := hU.1 (hEU hR') (hDU hR)
    (hR'r.trans ((congrArg AC.Vote.head heqv).symm.trans hRr.symm))
  exact AC.anc_total hU (hDR.mono hDU) (hER'.mono hEU)

private theorem proposal_root_viable_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell) :
    ell.frame.fcRoot ∈ ell.frame.viableTree ell.frame.tree := by
  have ht := hrun.time_nonneg i
  have hb : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hrun.time_mono hk.le
  have hr := Compose.Growing.reachable_at hrun ht hy hb
  obtain ⟨_, _, _, _, _, ⟨Q, hQ, hheight⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
  have hFQ := Goldilocks.Store.F_anc_of_hmax_le_of_safe hr hr
    (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.1 subset_rfl subset_rfl hf
    (Healing.Growing.held_atts_safe_at hrun ht hb hy ht hb hy le_rfl le_rfl)
    hQ hheight.ge
  rw [Compose.Growing.frame_of_projAC_at hrun hy hc, Node.frame_eq]
  have hPhi := (Store.frame_realization _ _ _ _ hr).1
  refine ⟨hPhi.fcRoot_mem, Relation.ReflTransGen.refl, Q, ?_, ?_, ?_⟩
  · rw [Store.toFrame_tree]; exact ⟨hQ, hFQ⟩
  · rw [Store.toFrame_viableHeads]
    exact ⟨hQ, hFQ, Store.isViable_of_hmax_le hheight.ge⟩
  · rw [Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict Relation.ReflTransGen.refl hFQ

/-! ## Optimistic next-vote base -/

/-- An optimistic write supplies the vote transfer for the first slot after the write. -/
theorem optimistic_next_votes_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hW : Healing.WindowWitness tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) Q)
    (hfin : ∀ y i, y ∈ H (tr.time i) → sp.ts s ≤ tr.time i →
      tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  apply next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hm le_rfl hmb
    hw hat hcw hQw hW hfin hXQ
  intro y i ell e hy hcast hs hhi hFX hviab ih
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hhi.trans hmb
  have hFX' : Anc (tr.HonestBlocksAt H) ell.frame.F X := by
    rwa [Compose.Growing.frame_of_projAC_at hrun hy hcast.1]
  have hcarry := Healing.Growing.KernelProof.carry_of_service_senders hrun hnc hsvc hcatch hm hy
    hcast hs
    (CV := CV) fun v hv => by
      obtain ⟨hvs, ⟨k, hk, hsend, hlo, hhi'⟩, Hv, -, hroot, hanc, hacc⟩ :=
        Compose.Growing.optimistic_writer_votes_at hrun hnc hx hopt v hv
      refine ⟨hvs, ⟨x, k, hk, hsend, hlo, hhi'⟩, Hv, hroot,
        (hFX'.trans hXD).trans hanc, ?_⟩
      exact hacc.imp_right fun ⟨k', hk', hacc', htime⟩ => ⟨x, k', hk', hacc', htime⟩
  have hss : sp.ts s ≤ sp.ts (s + 1 : Nat) := (AC.ts_le_iff sp).2 (by omega)
  have hΔ := sp.toParams.hΔ
  exact AC.Growing.optimistic_transfer_stored
    (Compose.Growing.goldilocks_ac_projection_from hrun hnc) K
    (AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP)
    (AC.CommitteeTAt.upTo hrun.antitone (hK.facts.committeeTAt' hrun hnc)) hK.facts.hsize
    hx hopt hXD (hK.cs2 s hm (by linarith) _ ht0 hib)
    (hK.cs2 (s + 1) (hm.trans hss) (by linarith) _ ht0 hib) hy hcast hs hcarry
    hviab (fun z k hki hz ev hv hes => ih z k ev hki hz hv hes)

/-- The first next-slot proposal follows an optimistic prefix through a window witness. -/
theorem optimistic_next_proposal_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hW : Healing.WindowWitness tr H (sp.ts s) (sp.ts (s + 1 : Nat)) Q)
    (hfin : ∀ y i, y ∈ H (tr.time i) → sp.ts s ≤ tr.time i → tr.time i ≤ sp.ts (s + 1 : Nat) →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts := AC.ts_succ s (sp := sp)
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hti ▸ hmb
  have hlo : sp.ts s ≤ tr.time i := by rw [hti, hts]; linarith
  have hfq := sp.toParams.fg.faults_lt_quorum_margin (hf _ ht0 hib)
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hacG := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hacP := Compose.goldilocks_ac_projection_from (hrun.upTo ht0) (hnc.upTo _)
  rw [RunTrace.upTo_projAC] at hacP
  have hr := hacP.localRun
  have hcp := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hdp : (AC.acProposal sp ((tr.projAC.upTo (tr.time i)).state y i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcp
  have hfr := Compose.Growing.frame_of_projAC_at hrun hy hc
  have hFF : ell.frame.F = (tr.state y i).fg.F := by
    rw [hfr, Node.frame_eq, Store.toFrame_F]
  have hslot : sp.slot (tr.time i) = s + 1 := AC.proposal_slot (tr := tr.projAC) hti
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    intro k hk hrk
    have ht := Compose.Growing.proposal_call_restarts_at hrun hnc hy hc hcall hd k hk hrk
    rw [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at ht
    exact ht
  have hfrw := Compose.Growing.frame_of_projAC_at hrun hw hcw
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    rw [hfrw, Node.frame_eq, Store.toFrame_tree] at hQw
    exact hQw.1
  have hQU : Q ∈ tr.HonestBlocksAt H :=
    ⟨w, a, tr.time a, hrun.time_nonneg a, fun _ hq => hmono hq.le, hw, hQ⟩
  have hai : tr.time a ≤ tr.time i := by linarith
  have hFQ0 := hfin y i hy hlo hti.le
  have hXF_case : Anc (tr.HonestBlocksAt H) X ell.frame.F →
      Anc (tr.HonestBlocksAt H) X d.head := by
    intro hXF
    rw [(AC.acProposal_head hdp).2]
    exact hXF.trans (((AC.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU).mono subU)
  rcases AC.anc_total hU hFQ0 hXQ with hFX | hXF
  swap
  · exact hXF_case (hFF ▸ hXF)
  have hFX' : Anc (tr.HonestBlocksAt H) ell.frame.F X := hFF ▸ hFX
  have hsrcQ : Q.root = sp.genesisRoot ∨ ∃ z q, z ∈ H (tr.time q) ∧
      tr.projAC.AcceptAt z q Q ∧ tr.time q < sp.ts s + 2 * sp.Δ := by
    rcases Healing.Growing.frame_block_acceptance_at hrun hw hcw hQw with hg | ⟨k, hka, hwk, hacc⟩
    · exact Or.inl (congrArg Block.root hg)
    · obtain ⟨hacc', htk, -⟩ := Healing.ac_block_after
        (hrun.upTo (hrun.time_nonneg k)).toLocalRun hwk
        ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, hacc⟩)
      rw [RunTrace.upTo_projAC] at hacc'
      change tr.time (k + 1) = tr.time k at htk
      refine Or.inr ⟨w, k + 1, by rwa [htk], (ACTrace.upTo_acceptAt.mp hacc').2, ?_⟩
      rw [htk]
      exact (hmono hka.le).trans_lt hat
  obtain ⟨hQt, -⟩ := relay_source_at_proposal_at hrun hnc hsvc hcatch hm hy hc hti hrs hQU hsrcQ
    (hFX'.trans hXQ)
  have hQy : Q ∈ (tr.state y i).fg.tree := by
    rw [hfr, Node.frame_eq, Store.toFrame_tree] at hQt
    exact hQt.1
  obtain ⟨hFQy, hvy⟩ := hW.held y i hy hlo hti.le hfq hQy
  rcases Healing.witness_frame_of_held hrun hnc hy hc hQy hFQy hvy hXQ with
    hXF | ⟨-, hXt, hrootX, hQt', hvQ', hXQf⟩
  · exact hXF_case hXF
  have hsw : AC.Growing.ServiceWindowBefore H (tr.HonestBlocksAt H) g (tr.time i) tr.projAC :=
    { message := fun z q v hz hsend hgq y' j ℓ hy' hcj _ hdl =>
        (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          ((Healing.Growing.KernelProof.service_syncACAt hrun hsvc (lo := g) (hi := tr.time q)
              le_rfl).1
            z q v hz hsend hgq le_rfl y' j ℓ hy' hcj hdl))
      relay := fun z q B hz hacc hgq y' j ℓ hy' hcj _ hdl hanc =>
        (Healing.Growing.KernelProof.service_syncACAt hrun hsvc (lo := g) (hi := tr.time q)
            le_rfl).2
          z q B hz hacc hgq le_rfl y' j ℓ hy' hcj hdl hanc }
  have hP : ∀ v ∈ CV, AC.HeldAtProposal (tr.projAC.state y i) ell.frame s v := by
    intro v hv
    obtain ⟨hvs, ⟨k, hk, hsend, hklo, hkhi⟩, Hv, hHvU, hHvr, hDHv, hacc⟩ :=
      Compose.Growing.optimistic_writer_votes_at hrun hnc hx hopt v hv
    have hvheld := AC.Growing.sync_window_before_forward hacG.localRun hsw hk hsend
      ((AC.le_gbar g).trans (hm.trans hklo))
      (by change tr.time k + sp.Δ ≤ tr.time i; linarith) hy hc
      (fun k' hk' hrk => (hrs k' hk' hrk).trans hklo)
      (by change tr.time k + sp.Δ ≤ tr.time i; linarith)
      (fun t htlo hthi => by
        change tr.time k ≤ t at htlo
        change t < tr.time k + sp.Δ at hthi
        have hslt := AC.slot_of_mem sp s (hklo.trans htlo)
          (by rw [hts]; linarith)
        rw [hslt, hvs]; omega)
    obtain ⟨hHvt, hstamp⟩ := relay_source_at_proposal_at hrun hnc hsvc hcatch hm hy hc hti hrs
      hHvU (hacc.imp_right fun ⟨k', hk', hacc', ht'⟩ => ⟨x, k', hk', hacc', ht'⟩)
      (hFX'.trans (hXD.trans hDHv))
    exact AC.heldAtProposal_iff.mpr ⟨by rwa [hvs] at hvheld, Hv, hHvt, hHvr, hstamp⟩
  have hhigh : AC.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state y i)
      (tr.time i) s X := by
    apply AC.highLocksCompatible_iff.mpr
    intro l hl _ hls L hL hLr
    rw [← hst] at hl
    have hl' : l ∈ ((tr.upTo (tr.time i)).state y i).ac.locks := by
      have h := Compose.projAC_state (hrun.upTo ht0).toLocalRun hy i
      rw [RunTrace.upTo_projAC] at h
      rwa [h] at hl
    have hlsb := Compose.proposal_locks_slot_of (hrun.upTo ht0) (hnc.upTo _) hy
      (by rw [RunTrace.upTo_projAC]; exact hcp) hcall
      (by rw [RunTrace.upTo_projAC]; exact hdp) hti
      (by rw [RunTrace.upTo_projAC];
          exact AC.CommitteePAt.upTo hmono hrun.antitone hK.facts.hP _)
      (hK.cs2 (s + 1) (hm.trans (by linarith)) hmb _ ht0 hib) l hl'
    have heq : l.slot = s := by omega
    obtain ⟨L', hL', hL'r, -⟩ := AC.lock_below_origin hr hacP.vstart hy i l hl
    obtain rfl : L = L' := hU.1 hL (subU hL') (hLr.trans hL'r.symm)
    obtain ⟨O, hLO, a', CW, ho⟩ := AC.proposal_high_lockU hr.toU hacP.vstart hy hti hl hls hL' hLr
    rw [heq] at ho
    obtain ⟨ha't, ho⟩ := (AC.upTo_optimisticLockAt hmono).mp ho
    have hya' : y ∈ H (tr.time a') := hrun.antitone ha't hy
    have hmax : max (tr.time a') (tr.time c) ≤ tr.time i := by
      exact max_le ha't (by linarith only [(Compose.Growing.optimistic_time_at hrun hopt).2,
        hti, hts, hΔ])
    have hf' := hK.cs2 s hm (by linarith) _
      ((hrun.time_nonneg a').trans (le_max_left _ _)) (hmax.trans hib)
    have hLO' := hLO.mono subU
    rcases optimisticLock_pair_compatible_at hrun hnc hya' hx hf' ho hopt hK with hOD | hDO
    · exact AC.anc_total hU (hLO'.trans hOD) hXD
    · exact AC.anc_total hU hLO' (hXD.trans hDO)
  exact AC.Growing.optimistic_first_proposal_stored_at hacG K hK.facts.hP
    hK.facts.hsize hx hopt hXD hy (hK.cs2 s hm (by linarith) _ ht0 hib)
    hc (AC.proposal_slot hti) hd
    ⟨hXt, Or.inl ⟨hXt, hrootX, Q, hQt', hvQ', hXQf⟩⟩ hP hhigh

/-- An optimistic prefix reaches later honest calls through a window witness: the window-free
core of `optimistic_later_heads_of_early_witness_at`. -/
theorem optimistic_later_heads_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hW : Healing.WindowWitness tr H (sp.ts s) (sp.ts N + sp.Δ) Q)
    (hfin : ∀ y i, y ∈ H (tr.time i) → sp.ts s ≤ tr.time i → tr.time i ≤ sp.ts N + sp.Δ →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have ht : sp.ts (s + 1 : Nat) ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hbase := optimistic_next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hm
    (by linarith) hx hopt hXD hw hat hcw hQw (hW.mono le_rfl (by linarith))
    (fun y i hy hlo hhi => hfin y i hy hlo (by linarith)) hXQ hK
  obtain ⟨hvote, hproposal⟩ := later_heads_of_windowWitness_at hrun hnc hsvc hawake hf hcatch
    hnr hm hmb hw hat hcw hQw hW hfin hXQ hbase hK r hrlo hrN
  refine ⟨hvote, ?_⟩
  by_cases heq : r = s + 1
  · subst r
    intro y i ell hy hc hcall hti d pay hd
    exact optimistic_next_proposal_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hm
      (by linarith [sp.toParams.hΔ]) hx hopt hXD hw hat hcw hQw
      (hW.mono le_rfl (by linarith [sp.toParams.hΔ]))
      (fun y i hy hlo hhi => hfin y i hy hlo (by linarith [sp.toParams.hΔ])) hXQ hy hc hcall
      hti hd hK
  · exact hproposal (by omega)

/-- An early P-U viable witness propagates an optimistic prefix to later honest calls. -/
theorem optimistic_later_heads_of_early_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {isTop : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have hsN : sp.ts (s + 1 : Nat) ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by
    linarith only [hat, AC.ts_succ s (sp := sp), hsN, sp.toParams.hΔ]
  have hwit := early_witness_viable hrun hframe hw halo hahi hcw hvQ
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [Compose.Growing.frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact optimistic_later_heads_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hx hopt hXD hw hat hcw hQw (Healing.windowWitness_of_frameWindow hrun hnc hframe hw hQ hwit)
    (fun y i hy hlo hhi => hframe.finalized_below_descendant_at hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ hwit hQ .refl) hXQ hK r hrlo hrN

/-- **The viable head above a supporter's anchor**: a cast of slot `s` of a node honest at it
is in slot `s` before its vote deadline, and its anchor `L` is below a P-U viable head of the
cast's frame. The window-free extraction step of `optimistic_supporter_later_heads_at'` and its
stock form. -/
theorem supporter_anchor_viable_head_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    {s : Nat} (hsb : sp.ts s + sp.Δ ≤ b) {L : AC.Blk sp.n (List (FG.Att sp.n))}
    {x : Fin sp.n} {i : Nat} (hx : x ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = AC.getAnchor sp e.readPoint ell.frame (tr.time i)) :
    sp.ts s ≤ tr.time i ∧ tr.time i ≤ sp.ts s + sp.Δ ∧
      ∃ Q ∈ ell.frame.tree, Q ∈ ell.frame.viableHeads ∧ Anc (tr.HonestBlocksAt H) L Q := by
  have ht0 := hrun.time_nonneg i
  have hac := Compose.goldilocks_ac_projection_from (hrun.upTo ht0) (hnc.upTo _)
  rw [RunTrace.upTo_projAC] at hac
  have hr := hac.localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have subU := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) ht0
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hx hc'.1
  obtain ⟨hlo, hhi⟩ := hes ▸ Compose.Growing.cast_time_at hrun hnc hx hc
  have hib : tr.time i ≤ b := hhi.trans hsb
  have hroot : ell.frame.Anc ell.frame.fcRoot L := by
    rw [hanchor]; exact AC.fcRoot_anc_getAnchor hPhi _ _
  have hvL : L ∈ ell.frame.viableTree ell.frame.tree := by
    have hR := proposal_root_viable_at hrun hx
      (sp.toParams.fg.faults_lt_quorum_margin (hf _ ht0 hib)) hc.1
    have he : L = ell.frame.fcRoot ∨
        L ∈ AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) := by
      rw [hanchor]
      rw [AC.getAnchor_eq_deepest_union hPhi]
      cases hd : AC.deepest ell.frame _ with
      | none => exact Or.inl rfl
      | some B =>
        rcases (AC.deepest_mem hd).1 with h | h
        · exact Or.inr h
        · exact Or.inl (Set.mem_singleton_iff.mp h)
    rcases he with he | h
    · exact he ▸ hR
    rcases AC.liveLockBlock_candidate hPhi h with hv | hb
    · exact hv
    · exact Anc.antisymm hPhi.coherent hb hroot ▸ hR
  obtain ⟨Q, hQ, hvQ, hLQ⟩ := hvL.2.2
  exact ⟨hlo, hhi, Q, hQ, hvQ, hLQ.mono (hPhiU.trans subU)⟩

/-- An optimistic supporter's anchor propagates to independently honest later calls. -/
theorem optimistic_supporter_later_heads_at {s₀ s N M : Nat}
    {isTop : Prop} {J L D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = AC.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (AC.Vote sp.n)} (hop : AC.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  have hts : sp.ts s₀ ≤ sp.ts s := (AC.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have htN : sp.ts s ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast (show s ≤ N by omega))
  obtain ⟨hlo, hhi, Q, hQ, hvQ, hLQ⟩ := supporter_anchor_viable_head_at hrun hnc hf
    (by linarith only [htN, hmb]) hx hc hes hanchor
  exact optimistic_later_heads_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    (hframe.mono hts le_rfl) hxa hop hLD hx hlo
    (by linarith [sp.toParams.hΔ]) hc.1 hQ hvQ hLQ hK

end Consensus.Goldilocks.Shadow.PU.Growing

end
