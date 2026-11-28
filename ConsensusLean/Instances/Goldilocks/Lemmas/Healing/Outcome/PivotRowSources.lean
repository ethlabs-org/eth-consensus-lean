module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotOldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: sources of the proposal attestations

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-! ### Sources of the proposer's attestations -/

/-- Finite high-origin labels preceding an actual proposal are strictly older. -/
theorem ResetPremisesUpTo.origin_label_lt_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (AC.ts_lt_iff sp).mp (show sp.ts l < sp.ts u by linarith only [ht', hrt, hΔ])
  · obtain ⟨_, _, _, hsl, _⟩ := id hop
    have hle : l ≤ u := by
      have hts : sp.ts l ≤ tr.time r :=
        (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
      exact_mod_cast (AC.ts_le_iff sp).mp (hts.trans hrt)
    have hl1 := slot_gbar_lt_of_cutZ_le (hp.cutZ_le_ts_of_highOrigin ho)
    have hne : l ≠ u := fun he => Compose.proposal_no_optimistic_of hp.run hp.noColl hp.hP
      (hp.cs2 (he ▸ hl1)) hpH hci hcall hti v ho.1 r hri D CV (he ▸ hop)
    clear * - hle hne; omega

/-- An origin already preceding an honest signature before a proposal has an older label.
This bound does not require the origin to precede a later receiving cast. -/
theorem origin_label_lt_at_proposal (hp : ResetPremises tr H K proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u :=
  (hp.toUpTo tr H le_rfl).origin_label_lt_at_proposal hpH hci hcall hti hri ho

/-- Finite receipt of a raw writer's ancestor at a later slot start. -/
theorem ResetPremisesUpTo.raw_writer_held_at_slot_start {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hwriter : AC.ResultAt tr.projAC x r s C CV ∨ AC.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : AC.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (AC.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [AC.ACParams.ts] at ht ⊢
    linarith only [ht]
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hp.committee_pos hr hp.run.vstart hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : AC.gbar g ≤ tr.time q
      · have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := i)
          (fun k hki hr' => restart_le_before hp hpH (Compose.projAC_restartAt.mp hr')
            ((hp.run.time_mono hki).trans hib)) (tr.time q)
        have hdl : tr.projAC.deadline p i (tr.time q) ≤ tr.time i := by
          have ht : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts s := by
            have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
              (sp.slot (AC.gbar g))).mpr (by clear * -; omega)
            simp only [ACParams.ts] at hbase hs ⊢
            push_cast at hbase hs ⊢
            linarith only [hbase, hs]
          change _ ≤ max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ at hd
          have hm : max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) ≤
              sp.ts s + 2 * sp.Δ := max_le hqt.le (by linarith only [ht, hΔ])
          linarith only [hd, hm, hstep, hΔ]
        obtain ⟨k, hki, hak, _⟩ := (sync_window_of_service hp.run hp.sync).relay x hx q D hq hg
          p hpH i ell hci
          (hdl.trans hib) hdl hFD
        exact AC.mem_tree_of_acceptAtU sp hr.toU hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := (catch_window_of_run hp.run hc).relay x hx q D hq
          (not_le.mp hg) p hpH i ell hci (by change _ ≤ tr.time i; linarith only [hs, hstep, hΔ])
          hib hFD
        exact AC.mem_tree_of_acceptAtU sp hr.toU hpH hak hki hci hFD
    exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

end Consensus.Goldilocks.Healing
