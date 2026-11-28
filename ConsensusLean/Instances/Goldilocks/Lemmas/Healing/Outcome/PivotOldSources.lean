module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: old sources at proposals

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-! ### Old sources -/

/-- **The old sources of slot `u`**: the HR.4 high origins written before `t_u` (the post-reset
counterpart of the old origins of the A1.7 pivot; their labels are below `u`). -/
def OldSrc (tr : GoldilocksTrace sp) (H : Set (Fin sp.n)) (g : Time) (u : Nat)
    (O : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u

/-- An old source is a high origin written before the slot starts. -/
theorem oldSrc_iff {u : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))} :
    OldSrc tr H g u O ↔
      ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u := Iff.rfl

/-- Actual-call relay of a high supporting head to the proposal frame. -/
theorem ResetPremisesUpTo.proposal_relay_high {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ell : ACLabel (goldilocksNode sp)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    {x : Fin sp.n} {r l : Nat} {O B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hOB : Anc (tr.HonestBlocks H) O B)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hacc : tr.projAC.AcceptAt z c B)
    (hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) :
    B ∈ ell.frame.tree ∧ AC.AcceptedBefore tr.projAC p B (sp.ts ((u : Int) - 1) + 3 * sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hgc : g ≤ tr.time c := by
    have := (hp.cutZ_lt_of_anc ho hz (hp.acceptAt_mem hz hacc) hOB).1
    have := lt_cutZ sp g
    have := AC.le_gbar g
    linarith
  have hsi : sp.slot (tr.time i) = u := by
    rw [hti]; simpa using (AC.slot_arithmetic sp u).1 0 (by clear * -; omega)
  have hts : sp.ts (u : Int) = sp.ts ((u : Int) - 1) + 4 * sp.Δ := by
    simp only [ACParams.ts]; ring
  have hrs := Compose.proposal_call_restarts hp.run hp.noColl hpH hci hcall hd
  rw [hsi] at hrs
  have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.projAC.time c) ≤
      sp.ts ((u : Int) - 1) + 3 * sp.Δ := fun k hk => by
    have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
      (fun c' hc' hr' => hrs c' (hc'.trans hk) hr') (tr.projAC.time c)
    have := max_le hct.le (show sp.ts ((u : Int) - 1) ≤ sp.ts ((u : Int) - 1) + 2 * sp.Δ by
      linarith only [hΔ])
    change _ ≤ max (tr.time c) (sp.ts ((u : Int) - 1)) + sp.Δ at hd
    linarith only [this, hd]
  obtain ⟨k, hki, hak, hkt⟩ := (hp.sync.syncAC hp.run le_rfl).2 z hz c B hacc hgc le_rfl
    p hpH i ell hci (by
        have := hdl i le_rfl; change _ ≤ tr.time i; linarith only [hti, hΔ, hts, this]) hFB
  exact ⟨AC.mem_tree_of_acceptAtU sp hr.toU hpH hak hki hci hFB,
    Or.inr ⟨k, hak, lt_of_lt_of_le hkt (hdl k hki)⟩⟩

/-- The label of an old source is below `u`. -/
theorem label_lt_of_old (hp : ResetPremises tr H K proposer dg g ΔF a)
    {u : Nat} {x : Fin sp.n}
    {i j : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j O)
    (ht : tr.time i < sp.ts u) : j < u := by
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  by_contra hcon
  have h1 : sp.ts u ≤ sp.ts j := (AC.ts_le_iff sp).2 (by omega)
  linarith [ts_le_of_fastLock hp hfl]

end Consensus.Goldilocks.Healing
