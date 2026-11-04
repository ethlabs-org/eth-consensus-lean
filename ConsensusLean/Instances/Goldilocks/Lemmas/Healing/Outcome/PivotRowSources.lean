module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotOldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: sources of the proposal rows

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### Sources of the proposer's rows -/

/-- A high row signed before a proposal has a strictly earlier source cut and label.
The entry remains explicit so a crossing proof can identify it by root coherence. -/
theorem proposal_high_row_source_before (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} (hv : v ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hki : k < i) (hs : tr.SignAt v k att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ r l O E, r < k ∧ l < u ∧ HighOrigin tr H g v r l O ∧
      tr.time r < sp.ts u ∧ E ∈ (tr.state v r).fg.tree ∧ E.root = att.T ∧
      Compose.IsHonestSource tr H E att.T ∧ Anc (tr.HonestBlocks H) E O := by
  obtain ⟨r, hrk, l, O, ho, E, hE, hEO, hEr, -, hET⟩ := high_row_source hp hv hs hh
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono (by omega)
  have hlu : l < u := by
    have hle : l ≤ u := by
      have := (SA.ts_le_iff sp).1 ((ts_le_of_fastLock hp hfl).trans hrt)
      exact_mod_cast this
    by_contra hn
    have hlu : l = u := by omega
    rw [hlu] at hfl
    rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | hop
    · have ht' : tr.time r = sp.ts u + 6 * sp.Δ := ht
      have := sp.toParams.hΔ
      linarith
    · exact proposal_no_optimistic hp hpH hci hcall hti v hv r (by omega) D CV hop
  exact ⟨r, l, O, E, hrk, hlu, ho,
    fastLock_time_lt hp hfl hlu (by have := sp.toParams.hΔ; linarith), hE, hEr,
    Compose.isHonestSource_iff.2 ⟨v, hv, r, hE, hET.trans hEr⟩,
    hEO.mono (fun X hX => ⟨v, hv, r, hX⟩)⟩

/-- Finite high-origin labels preceding an actual proposal are strictly older. -/
theorem ResetPremisesUpTo.origin_label_lt_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (SA.ts_lt_iff sp).mp (show sp.ts l < sp.ts u by linarith)
  · obtain ⟨_, _, _, hsl, _⟩ := id hop
    have hle : l ≤ u := by
      have hts : sp.ts l ≤ tr.time r :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
      exact_mod_cast (SA.ts_le_iff sp).mp (hts.trans hrt)
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
    have hne : l ≠ u := fun he => proposal_no_optimistic_of_run hp.run hp.noColl hf hpH
      hci hcall hti v ho.1 r hri D CV (he ▸ hop)
    omega

/-- An origin already preceding an honest signature before a proposal has an older label.
This bound does not require the origin to precede a later receiving cast. -/
theorem origin_label_lt_at_proposal (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u :=
  (hp.toUpTo tr H le_rfl).origin_label_lt_at_proposal hpH hci hcall hti hri ho

/-- A bounded high floor at an actual proposal has a strictly older signed-row source. -/
theorem ResetPremisesUpTo.high_floor_source_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  obtain ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hfloor, _⟩ :=
    hp.high_floor_signed_source_of_row_bound ho hpH (u := u)
      (fun W hW att ha v hv d hsign hdi q m O hqd hO =>
        hp.origin_label_lt_at_proposal hpH hci hcall hti (by omega) hO)
      (fun v q m O hqi hO v' q' m' O' hqi' hO' =>
        hp.origins_compatible hO ((hp.run.time_mono hqi.le).trans hib)
          hO' ((hp.run.time_mono hqi'.le).trans hib))
      (fun v q m O hqi hO => hp.origins_compatible ho hrb hO
        ((hp.run.time_mono hqi.le).trans hib)) hfloor
  exact ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hfloor⟩

set_option linter.unusedVariables false in
/-- Floor crossing at a proposal uses the full held tree and the actual proposal cut. -/
theorem high_floor_source_at_proposal
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u)
    (hpair : ∀ v r l O, r < i → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < i → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < i → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v r l O E, r < i ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  have hbr : tr.time r ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbi : tr.time i ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (hp.toUpTo tr H (le_max_left _ _)).high_floor_source_at_proposal ho hpH hci hcall hti
    hbr hbi hfloor

/-- Finite proposal domain for a held target compared with earlier high sources. -/
theorem ResetPremisesUpTo.held_target_proposal_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hroot := hp.held_target_proposal_root_before hx hpH hBx hci hcall hd hti hib
    hheld hseed hcompare
  by_cases hcovered : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hrootB := hroot.resolve_right hcovered
  have hFB := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootB
  have hBt := hheld hFB
  have hBy := mem_tree_of_frame hp.run hpH hci hBt
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have held : ∀ {z q m O}, HighOrigin tr H g z q m O → tr.time q < sp.ts u →
      Anc (tr.HonestBlocks H) B O → O ∈ ell.frame.tree := by
    intro z q m O ho hqt hBO
    rcases hp.proposal_holds_old hpH hci hcall hd hti hib ho hqt with h | h
    · exact h
    · have he := Anc.antisymm hr.coherent h (hFB.trans hBO)
      rw [he]
      exact hPhi.rooted.1
  have hdesc : ∃ C ∈ ell.frame.tree, Anc (tr.HonestBlocks H) B C ∧
      (tr.state p i).fg.IsViable C := by
    by_cases hfloor : (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    obtain ⟨v, q, m, S, hS, hqt, hBS⟩ := hseed
    obtain ⟨_, _, _, _, _, _, _, _, _, hSsrc⟩ := hp.highOrigin_mem hS
    by_cases hSf : (tr.state p i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocks H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := hp.mem_tree_of_anc hpH h hBy
          have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH h hBy)
          rw [← hp.σ_eq_run hS.1 hpH hSsrc hSy] at hh
          omega
      have hSt := held hS hqt hBS'
      refine ⟨S, hSt, hBS', ?_⟩
      change (tr.state p i).fg.headHeightFloor ≤ _
      rw [← hp.σ_eq_run hS.1 hpH hSsrc (mem_tree_of_frame hp.run hpH hci hSt)]
      exact hSf
    · obtain ⟨z, q', n, O, E, hqi, ho, hn, hE, hEO, _, hEf⟩ :=
        hp.high_floor_source_at_proposal hS hpH hci hcall hti
          (hqt.le.trans (hti ▸ hib)) hib (lt_of_not_ge hSf)
      have hBO : Anc (tr.HonestBlocks H) B O := by
        rcases hcompare z q' n O hqi ho with h | h
        · exact h
        · have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH (hEO.trans h) hBy)
          omega
      obtain ⟨_, D, CV, _, hf, _⟩ := hp.highOrigin_mem ho
      have htime : tr.time q' < sp.ts u := by
        rcases hf with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
        · have ht' : tr.time q' = sp.ts n + 6 * sp.Δ := ht
          have hle := hp.run.time_mono hqi.le
          rw [hti, ht'] at hle
          rw [ht']
          simp only [SAParams.ts] at hle ⊢
          have hΔ := sp.toParams.hΔ
          have hn2 : (n : Int) + 2 ≤ u := by
            by_contra h
            have : (u : Int) ≤ n + 1 := by omega
            linarith [mul_le_mul_of_nonneg_left this hΔ.le]
          linarith [mul_le_mul_of_nonneg_left hn2 hΔ.le]
        · by_contra h
          have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q') u).mp (not_lt.mp h)
          change sp.slot (tr.time q') = n at hsl
          omega
      have hOt := held ho htime hBO
      have hh := σ_h_le_of_anc hreach
        (hp.anc_tree_of_anc hpH hEO (mem_tree_of_frame hp.run hpH hci hOt))
      exact ⟨O, hOt, hBO, hEf.trans hh⟩
  obtain ⟨C, hCt, hBC, hCv⟩ := hdesc
  have hrootB' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hrootB hBt
  have hBC' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBC hCt
  refine Or.inr ⟨hBt, hrootB', C, hCt, ?_, hBC'⟩
  have hCf : C ∈ (Node.frame (tr.state p i)).tree := hfr ▸ hCt
  have hrootC := hrootB'.trans hBC'
  rw [hfr] at hrootC ⊢
  exact ⟨hCf.1, hCf.2, Anc.mono (fun _ h => h.1) hrootC, hCv⟩

/-- Arbitrary-target proposal domain from actual receipt and bounded source comparisons. -/
theorem held_target_proposal_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    (hai : a ≤ tr.time i) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree :=
  (hp.toUpTo tr H hai).held_target_proposal_domain_before hx hpH hBx hci hcall hd hti le_rfl
    hheld hseed hcompare

/-- Finite receipt of a raw writer's ancestor at a later slot start. -/
theorem ResetPremisesUpTo.raw_writer_held_at_slot_start {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [SA.SAParams.ts] at ht ⊢
    linarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hr hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : SA.gbar g ≤ tr.time q
      · have hd := deadline_le_restarts (T := tr.projAC) (c := i)
          (fun k hki hr' => restart_le_before hp hpH (Compose.projAC_restartAt.mp hr')
            ((hp.run.time_mono hki).trans hib)) (tr.time q)
        have hdl : tr.projAC.deadline p i (tr.time q) ≤ tr.time i := by
          have ht : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s := by
            have hbase := (SA.ts_le_iff_le_slot sp (gbar_nonneg g)
              (sp.slot (SA.gbar g))).mpr (by omega)
            simp only [SAParams.ts] at hbase hs ⊢
            push_cast at *
            linarith
          change _ ≤ max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) + sp.Δ at hd
          have hm : max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) ≤
              sp.ts s + 2 * sp.Δ := max_le hqt.le (by linarith)
          linarith
        obtain ⟨k, hki, hak, _⟩ := hS.sync.relay x hx q D hq hg p hpH i ell hci
          (hdl.trans hib) hdl hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := hS.catchUp.relay x hx q D hq (not_le.mp hg)
          p hpH i ell hci (by change _ ≤ tr.time i; linarith) hib hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

/-- A clean protected source compares with every high origin inside the horizon. -/
theorem ResetPremisesUpTo.protected_source_compatible_high_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocks H) B D := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hts := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
  have evidence : ∃ C CV,
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocks H) B C := by
    rcases hsource with ⟨CV, ⟨ell, C, hu, hR, hfast, _⟩ | hop⟩ | ⟨ell, C, hu, hR, hslow⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hfast).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
    · exact ⟨B, CV, Or.inr hop, .refl⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hslow).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
  obtain ⟨C, CV, hC, hBC⟩ := evidence
  rcases lt_trichotomy t s with h | rfl | h
  · have supporter : ∃ z ∈ H, ∃ j ≤ r, ∃ e, SA.VoteAt tr.projAC z j e ∧
        e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
      rcases hC with hC | hC
      · obtain ⟨z, hz, j, hjr, e, hv, _, hes, hCH⟩ :=
          hp.result_supporter hc hx hC (.refl : Anc (tr.HonestBlocks H) C C) hrb hts
        exact ⟨z, hz, j, hjr.le, e, hv, hes, hCH⟩
      · exact (hp.optimistic_supporter hx hC).2
    obtain ⟨z, hz, j, hjr, e, hv, hes, W, hW, hWr, hCW⟩ := supporter
    exact hp.target_compatible_older_origin ho hqb hz hv
      ((hp.run.time_mono hjr).trans hrb) hes h ⟨W, hW, hWr, hBC.trans hCW⟩
  · obtain ⟨DV, hst⟩ := ho.2.2.1
    obtain ⟨_, E, hfl, hDE⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hcomp : Compatible (tr.HonestBlocks H) C E := by
      rcases hfl with ⟨ell, R, hu, hR, hfast, _⟩ | hop
      · have hER := ((SA.deepest_mem hfast).1.1.2.2).mono
          (SA.frameIn_of_callAt hr ho.1 hu.1).2
        rcases hp.result_source_compatible hc ho.1 hx
          ⟨ell, hu, hR, rfl⟩ hC hqb hrb hts with h | h
        · exact Or.inr (hER.trans h)
        · exact SA.anc_total hr.coherent h hER
      · exact hp.sources_same_label_compatible hc hx ho.1 hC (Or.inr hop) hrb hqb hts
    rcases hcomp with h | h
    · exact SA.anc_total hr.coherent (hBC.trans h) hDE
    · exact SA.anc_total hr.coherent hBC (hDE.trans h)
  · obtain ⟨DV, hst⟩ := ho.2.2.1
    obtain ⟨_, E, hfl, hDE⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos x; omega
    have hEB : Compatible (tr.HonestBlocks H) E B :=
      SA.fastLock_compatible_of_votes hrun ho.1 (Nat.lt_succ_self q) hfl hf (by
        intro z hz j hj e ⟨ell, hcast⟩ hes
        have hjb := (hp.run.time_mono (Nat.lt_succ_iff.mp hj)).trans hqb
        rcases hsource with ⟨CV, hfast⟩ | hslow
        · exact hp.fast_source_votes_before hc hx hfast hs hrb j hjb z hz ell e hcast (by omega)
        · exact hp.slow_source_votes_before hc hx hslow hs hrb j hjb z hz ell e hcast (by omega))
    rcases hEB with h | h
    · exact Or.inr (hDE.trans h)
    · exact SA.anc_total hr.coherent h hDE

/-- A clean protected source has the actual finite proposal domain, without cut ordering. -/
theorem ResetPremisesUpTo.clean_source_proposal_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have evidence : ∃ C CV, (SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocks H) B C ∧ B ∈ (tr.state x r).fg.tree := by
    rcases hsource with ⟨CV, hf⟩ | hsl
    · refine ⟨B, CV, Or.inr hf, .refl, ?_⟩
      rcases hf with ⟨ellX, C, hupd, _, hdeep, _⟩ | ⟨ellX, A, hpt, _, hsel, _⟩
      · exact hp.frame_tree_subset hx hupd.1 (SA.deepest_mem hdeep).1.1.1
      · unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact hp.frame_tree_subset hx hpt.1 (SA.deepest_mem hsel).1.1
    · obtain ⟨ellX, C, hupd, hconf, hdeep⟩ := hsl
      have hB := (SA.deepest_mem hdeep).1.1
      exact ⟨C, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩,
        hB.2.2.mono (SA.frameIn_of_callAt hr hx hupd.1).2,
        hp.frame_tree_subset hx hupd.1 hB.1⟩
  obtain ⟨C, CV, hw, hBC, hBx⟩ := evidence
  obtain ⟨v, q, m, S, hS, hqa, hm⟩ := hp.reset_seed
  have htiming : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := hp.cutZ_le_ts_of_highOrigin hS
    have hz := lt_cutZ sp g
    have hsm : sp.ts (m + 1 : Nat) ≤ sp.ts s := (SA.ts_le_iff sp).mpr
      (by rw [cleanLabel_eq] at hs; omega)
    have he : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [he] at hsm
    have := sp.toParams.hΔ
    linarith
  have hqt : tr.time q < sp.ts u := by
    obtain ⟨_, D, DV, _, hf, _⟩ := hp.highOrigin_mem hS
    have hmu : m + 2 ≤ u := by
      rw [drainTime_eq] at hR
      have := (SA.ts_le_iff sp).mp hR
      omega
    rcases hf with ⟨ellX, R, ⟨_, _, ht, _⟩, _⟩ | ⟨ellX, A, _, hsl, _⟩
    · have ht' : tr.time q = sp.ts m + 6 * sp.Δ := ht
      have htu := (SA.ts_le_iff sp).mpr (show (m : Int) + 2 ≤ u by omega)
      simp only [SAParams.ts] at ht' htu ⊢
      have := sp.toParams.hΔ
      linarith
    · by_contra h
      have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) u).mp (not_lt.mp h)
      change sp.slot (tr.time q) = m at hsl
      omega
  refine hp.held_target_proposal_domain_before hx hpH hBx hci hcall hd hti hib ?_ ?_ ?_
  · exact hp.raw_writer_held_at_slot_start hc hx hpH hw hBC htiming hsu hci hti hib
  · exact ⟨v, q, m, S, hS, hqt,
      hp.protected_source_compatible_high_origin hc hx hsource hs hrb hS
        (hqa.trans hp.reset_le)⟩
  · intro v q m O hqi ho
    exact hp.protected_source_compatible_high_origin hc hx hsource hs hrb ho
      ((hp.run.time_mono hqi.le).trans hib)

/-- Clean raw sources have the actual proposal domain, without a source-before-proposal
cut assumption. Writer service is driven by the source label, including old acceptances. -/
theorem clean_source_proposal_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hbr : tr.time r ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbi : tr.time i ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (hp.toUpTo tr H (le_max_left _ _)).clean_source_proposal_domain_before hc hx hpH hsource hs
    hsu hbr hR hci hcall hd hti hbi

/-- The finite predecessor batch extends every clean source at least two labels earlier. -/
theorem ResetPremisesUpTo.clean_source_proposal_parent_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s + 2 ≤ u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) : Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos x; omega
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  rcases hp.clean_source_proposal_domain_before hc hx hpH hsource hs (by omega) hrb hR
      hci hcall hd hti hib with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  obtain ⟨σ, rfl⟩ : ∃ σ, u = σ + 1 := ⟨u - 1, by omega⟩
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hσb : sp.ts σ + sp.Δ ≤ b := by rw [hti, hσ] at hib; linarith
  have votes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = σ →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
    rintro z hz q e ⟨ell', hc'⟩ hslot
    have hqb : tr.time q ≤ b := by
      have ht := SA.vote_time_le hr hz ⟨ell', hc'⟩
      have hsl := (SA.castAt_spec hr hz hc').2.1
      rw [← hsl, hslot] at ht
      exact ht.trans hσb
    rcases hsource with ⟨CV, hfast⟩ | hslow
    · exact hp.fast_source_votes_before hc hx hfast hs hrb q hqb z hz ell' e hc' (by omega)
    · exact hp.slow_source_votes_before hc hx hslow hs hrb q hqb z hz ell' e hc' (by omega)
  have hcut := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
  have hσg : SA.gbar g + 4 * sp.Δ ≤ sp.ts σ := by
    have hz := lt_cutZ sp g
    have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ σ by omega)
    linarith
  have hrestart : ∀ z ∈ H, ∀ q, tr.time q ≤ b → tr.projAC.RestartAt z q →
      tr.time q ≤ sp.ts ((σ : Int) - 1) := by
    intro z hz q hqb hrest
    apply (restart_le_before hp hz (Compose.projAC_restartAt.mp hrest) hqb).trans
    rw [cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hrs : ∀ q ≤ i, tr.projAC.RestartAt p q → tr.time q < sp.ts σ := by
    intro q hqi hrest
    exact (hrestart p hpH q ((hp.run.time_mono hqi).trans hib) hrest).trans_lt
      ((SA.ts_lt_iff sp).mpr (by omega))
  have hhalf := SA.honest_voters_half_before hS hσg hσb
    (fun z hz q hqt hrest => hrestart z hz q (hqt.trans hσb) hrest)
  have hhalf' : sp.n ≤ 2 *
      {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = σ}.ncard := by
    change sp.n ≤ 2 * {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = σ ∧ tr.time q ≤ sp.ts σ + sp.Δ}.ncard at hhalf
    have hle := Set.ncard_le_ncard (s := {z | z ∈ H ∧ ∃ q e,
      SA.VoteAt tr.projAC z q e ∧ e.msg.slot = σ ∧ tr.time q ≤ sp.ts σ + sp.Δ})
      (t := {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = σ})
      (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
    omega
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) σ B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, q, hqi, CV, hO⟩ := SA.lock_below_origin hr hpH i l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hcomp : Compatible (tr.HonestBlocks H) O B := by
      rcases hO with ⟨ell', ⟨_, _, ht, _⟩, _⟩ | ⟨ellO, A, hpt, hsl, hsel, hCV⟩
      · have htime := hr.time_mono hqi.le
        have hle := (SA.ts_le_iff sp).mpr (show (σ : Int) ≤ l.slot by omega)
        change tr.time q ≤ tr.time i at htime
        change tr.time q = sp.ts l.slot + 6 * sp.Δ at ht
        rw [hti, hσ] at htime
        exfalso
        linarith
      · have hle : l.slot ≤ σ := by
          have htime := hp.run.time_mono hqi.le
          have hne : l.slot ≠ σ + 1 := fun he =>
            proposal_no_optimistic_of_run hp.run hp.noColl hf hpH hci hcall hti
              p hpH q hqi O CV (he ▸ ⟨ellO, A, hpt, hsl, hsel, hCV⟩)
          have hstart := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr
            (by change sp.slot (tr.time q) = l.slot at hsl; omega)
          rw [hti] at htime
          have := (SA.ts_le_iff sp).mp (hstart.trans htime)
          omega
        have hΦU := (SA.frameIn_of_callAt hr hpH hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦU h34 hf fun v hv hvH => ?_
        obtain ⟨hvs, q', _, e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hS.run hpH hpt hv hvH
        exact votes _ hvH q' e' hv' (by rw [hvs]; omega)
    rcases hcomp with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  refine SA.batch_proposal hS.run hf hhalf' votes hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro z hz q e hv he
  obtain ⟨H', hH', hHr', hBH⟩ := votes z hz q e hv he
  obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hpH hci hσg
    (by change _ ≤ tr.time i; rw [hti, hσ]; linarith) hib
    (fun k hki t _ => deadline_le_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv he
    (fun Hd hHd hHdr => by
      rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
      exact hFB.trans hBH)
  exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

/-- The completed predecessor batch makes a proposal extend every clean raw source
whose label is at least two slots earlier. -/
theorem clean_source_proposal_parent_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s + 2 ≤ u)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) : Anc (tr.HonestBlocks H) B d.head := by
  have hbr : tr.time r ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbi : tr.time i ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (hp.toUpTo tr H (le_max_left _ _)).clean_source_proposal_parent_before hc hx hpH hsource hs
    hsu hbr hR hci hcall hd hti hbi

/-- A clean optimistic source extends the next actual proposal within the finite horizon. -/
theorem ResetPremisesUpTo.clean_optimistic_proposal_parent {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos x; omega
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
    have hz := lt_cutZ sp g
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt p k → tr.time k < sp.ts s := by
    intro k hki hk
    have ht := restart_le_before hp hpH (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hki).trans hib)
    have hs0 := (SA.ts_le_iff_le_slot sp (gbar_nonneg g)
      (sp.slot (SA.gbar g))).mpr (by omega)
    have hclean := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
    rw [cutZ_eq] at hclean
    have hlt : sp.slot (SA.gbar g) + 1 < s := by
      have := (SA.ts_le_iff sp).mp hclean
      omega
    exact ht.trans_lt ((SA.ts_lt_iff sp).mpr (by exact_mod_cast hlt))
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  rcases hp.clean_source_proposal_domain_before hc hx hpH (Or.inl ⟨CV, Or.inr hop⟩) hs
      (by omega) hrb hR hci hcall hd hti hib with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) s B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hls X hX hXr => ?_
    obtain ⟨q, hqi, D, hw, L, hL, hLr, hLD⟩ := SA.lock_provenance hr hpH i l hl
    obtain rfl : L = X := hr.coherent.1 hL hX (hLr.trans hXr.symm)
    have hqt : tr.time q ≤ sp.ts (s + 1 : Nat) := hti ▸ hp.run.time_mono hqi.le
    rcases hw with ⟨CV', hop'⟩ | ⟨ell', hupd⟩
    · have hle : l.slot ≤ s + 1 := by
        obtain ⟨ell', A, _, hsl, _⟩ := hop'
        change sp.slot (tr.time q) = l.slot at hsl
        have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr (by omega)
        exact_mod_cast (SA.ts_le_iff sp).mp (this.trans hqt)
      have hne : l.slot ≠ s + 1 := by
        intro he
        exact proposal_no_optimistic_of_run hp.run hp.noColl hf hpH hci hcall hti
          p hpH q hqi D CV' (he ▸ hop')
      have he : l.slot = s := by omega
      rw [he] at hop'
      rcases hp.optimistic_sources_compatible hpH hx hop' hop with h | h
      · exact Or.inl (hLD.trans h)
      · exact SA.anc_total hr.coherent hLD h
    · have ht : tr.time q = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ l.slot by omega)
      rw [hts] at hqt
      exfalso
      linarith
  refine optimistic_first_proposal_anc hS.run hf hx hop .refl hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro v hv
  obtain ⟨hvs, hsend, D, hD, hDr, hBD, hacc⟩ := fastLock_writer hr hx (Or.inr hop) v hv
  have hFD := hFB.trans hBD
  refine SA.heldAtProposal_of_writer hr (hp.sync.syncAC hp.run (le_gbar g))
    (by linarith) le_rfl hx hpH hci hti hrs hvs hsend ⟨D, hD, hDr, hFD, ?_⟩
  rcases hacc with hg | ⟨q, hq, hqt⟩
  · exact Or.inl hg
  by_cases hg : SA.gbar g ≤ tr.time q
  · exact Or.inr (Or.inl ⟨q, hq, hg, hqt⟩)
  · obtain ⟨k, hki, hak, hkt⟩ := hS.catchUp.relay x hx q D hq (not_le.mp hg) p hpH i ell hci
      (by change _ ≤ tr.time i; rw [hti, hts]; linarith) hib hFD
    exact Or.inr (Or.inr ⟨k, hki, hak, by change tr.time k < _ at hkt ⊢; linarith⟩)

/-- The immediately preceding optimistic source reaches and constrains the proposal. -/
theorem clean_optimistic_proposal_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) : Anc (tr.HonestBlocks H) B d.head := by
  have hbr : tr.time r ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbi : tr.time i ≤ max a (max (tr.time r) (tr.time i)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (hp.toUpTo tr H (le_max_left _ _)).clean_optimistic_proposal_parent hc hx hpH hop hs hbr
    hR hci hcall hd hti hbi

/-- The packed old-source interface of the proposal row ordering lemma. -/
theorem proposal_high_row (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} (hv : v ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hki : k < i) (hs : tr.SignAt v k att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E O, Compose.IsHonestSource tr H E att.T ∧ OldSrc tr H g u O ∧
      Anc (tr.HonestBlocks H) E O := by
  obtain ⟨r, l, O, E, _, _, ho, ht, _, _, hE, hEO⟩ :=
    proposal_high_row_source_before hp hpH hci hcall hti hv hki hs hh
  exact ⟨E, O, hE, oldSrc_iff.2 ⟨v, r, l, ho, ht⟩, hEO⟩

/-- Earlier bounded origins rule out a high contest at a completed-prefix observation. -/
theorem ResetPremisesUpTo.no_high_contest {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) (i : Nat) (hib : ∀ q < i, tr.time q ≤ b) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
  have hU := hp.honest_coherent
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  rintro ⟨⟨hmj, C, hC, _, hCh, hJC⟩, hmax⟩
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
  have hJlt := Store.hj_lt_h hreach hBj
  obtain ⟨_, _, _, _, v₂, _, d₂, hd₂, _, _, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
    hp.left_entry_origin hpH hJm hJT (by omega) hEJB (by omega)
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ :=
    entry_at_height hreach hC (h := (tr.state p i).fg.hj) (by omega) (by omega)
  obtain ⟨_, _, _, _, v₁, _, d₁, hd₁, _, _, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
    hp.left_entry_origin hpH hEC hECT (by omega) hECC (by omega)
  have upper : ∃ z ∈ H, ∃ m W, W ∈ (tr.state z m).fg.tree ∧
      Anc (tr.HonestBlocks H) O₁ W ∧ Anc (tr.HonestBlocks H) O₂ W := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hO₁⟩ := hp.highOrigin_mem ho₁
    obtain ⟨_, _, _, _, _, _, _, _, _, hO₂⟩ := hp.highOrigin_mem ho₂
    rcases hp.origins_compatible ho₁ (hib r₁ (by omega)) ho₂ (hib r₂ (by omega)) with h | h
    · exact ⟨v₂, ho₂.1, r₂, O₂, hO₂, h, .refl⟩
    · exact ⟨v₁, ho₁.1, r₁, O₁, hO₁, .refl, h⟩
  obtain ⟨z, hz, m, W, hW, hO₁W, hO₂W⟩ := upper
  have h₁ := hECO.trans hO₁W
  have h₂ := hJO.trans hO₂W
  have hσ₁ := hp.σ_eq_run hpH hz hEC (hp.mem_tree_of_anc hz h₁ hW)
  have hσ₂ := hp.σ_eq_run hpH hz hJm (hp.mem_tree_of_anc hz h₂ hW)
  have he := hp.entry_root_eq hz hW h₁ h₂
    (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
    (by rw [← hσ₂]; exact hJT)
  obtain rfl : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hJm) he
  exact hJC hECC

/-- Global high-origin comparability excludes contests at high justification heights. -/
theorem no_high_contest (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) (i : Nat) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) :=
  (hp.toUpTo tr H (le_max_left a (tr.time i))).no_high_contest hpH i
    (fun _ hq => (hp.run.time_mono hq.le).trans (le_max_right _ _))

/-- A bounded held high origin lies below the root or in the actual viable tree. -/
theorem ResetPremisesUpTo.held_high_origin_viable {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {c : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p c ell) (hcb : tr.time c ≤ b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (ht : sp.ts (j + 1 : Nat) ≤ tr.time c) (hBt : B ∈ ell.frame.tree) :
    B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot := by
  have hU := hp.honest_coherent
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH c
  have hsub : (tr.state p c).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, c, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hpH hc
  have hBf : B ∈ (Node.frame (tr.state p c)).tree := hfr ▸ hBt
  have hBh := hp.high_of_anc ho hpH hBf.1 .refl
  have hcache := hp.vote_state_caches
    (fun ho₀ hi₀ z hz q _ hqb e ⟨ell, hv⟩ hs =>
      hp.high_origin_votes_before q hqb _ _ _ _ ho₀ hi₀ z hz ell e hv hs)
    hcb ho hib hpH ht
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun hpH hc
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state p c).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs with hchoose
    · by_cases hhigh : HZ tr H g + 1 ≤ (tr.state p c).fg.hj
      · exact hcache.2 hhigh
      · have hmax := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 B hBf.1
        have hJB : (tr.state p c).fg.Anc (tr.state p c).fg.J B := by
          by_contra hn
          exact hchoose.2 ⟨hchoose.1, B, hBf.1, hBf.2, by omega, hn⟩
        exact Or.inl (hJB.mono hsub)
    · exact hcache.1
  rcases hroot with hfB | hBfroot
  swap
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hPhiU hBt hBfroot hPhi.fcRoot_mem)
  have hfB' := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hfB hBt
  have hfBs : (tr.state p c).fg.Anc (tr.state p c).fg.fcRoot B := by
    rw [hfr] at hfB'
    exact hfB'.mono (fun _ h => h.1)
  have hdesc : ∃ C ∈ (tr.state p c).fg.tree, (tr.state p c).fg.Anc B C ∧
      (tr.state p c).fg.IsViable C := by
    by_cases hle : (tr.state p c).fg.headHeightFloor ≤ ((tr.state p c).fg.σ B.root).h
    · exact ⟨B, hBf.1, .refl, hle⟩
    have hfloor := lt_of_not_ge hle
    have hcon : ¬ (tr.state p c).fg.Contest := fun h => by
      unfold Store.headHeightFloor at hfloor
      simp only [h, ↓reduceIte] at hfloor
      exact hp.no_high_contest hpH c
        (fun q hqc => (hp.run.time_mono hqc.le).trans hcb) ⟨h, by omega⟩
    have hfl : (tr.state p c).fg.headHeightFloor = (tr.state p c).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [hcon, ↓reduceIte]
    rw [hfl] at hfloor
    obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, hEC, hEh, hET⟩ :=
      entry_at_height hreach hC (h := (tr.state p c).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨_, _, _, _, v, _, d, hdc, _, _, r, hrd, l, O, hoO, hEO⟩ :=
      hp.left_entry_origin hpH hE hET (by omega) hEC (by omega)
    have hcmp : Compatible (tr.HonestBlocks H) E B := by
      rcases hp.origins_compatible hoO ((hp.run.time_mono (by omega : r ≤ c)).trans hcb)
          ho hib with h | h
      · exact Or.inl (hEO.trans h)
      · exact Anc.total hU hEO h
    have hBE : Anc (tr.HonestBlocks H) B E := by
      rcases hcmp with h | h
      · have := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH h hBf.1)
        omega
      · exact h
    refine ⟨C, hC, (hp.anc_tree_of_anc hpH hBE hE).trans hEC, ?_⟩
    change (tr.state p c).fg.headHeightFloor ≤ _
    omega
  obtain ⟨C, hC, hBC, hvC⟩ := hdesc
  have hCf : C ∈ (Node.frame (tr.state p c)).tree := ⟨hC, hBf.2.trans hBC⟩
  have hCt : C ∈ ell.frame.tree := hfr ▸ hCf
  have hCv : C ∈ ell.frame.viableHeads := by
    rw [hfr]
    exact ⟨hC, hCf.2, hfBs.trans hBC, hvC⟩
  exact Or.inl ⟨hBt, hfB', C, hCt, hCv,
    SA.anc_tree_of_anc_U hU hPhi hPhiU hBt (hBC.mono hsub) hCt⟩

/-- A held high origin is below the root or in the full viable tree at an active cut. -/
theorem held_high_origin_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p c ℓ)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ℓ.frame.tree) :
    B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot := by
  have hbc : tr.time c ≤ max a (max (tr.time c) (tr.time i)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbi : tr.time i ≤ max a (max (tr.time c) (tr.time i)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (hp.toUpTo tr H (le_max_left _ _)).held_high_origin_viable hpH hc hbc ho hbi ht hBt

end Consensus.Goldilocks.Healing
