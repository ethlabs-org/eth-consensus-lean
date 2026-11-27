module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Full-frame viability through an honest observation

Persistence is local to the receiver. The retained frame window ends at the actual
observation, rather than extending the receiver's honesty beyond that cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- A call-local viability witness fixes its viable ancestor for every run core. -/
theorem Core.proposal_viable_after_votes_at
    {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hroot : ell.frame.Anc ell.frame.fcRoot P)
    (hv : P ∈ ell.frame.viableHeads) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hr := (hrun.acRun_upTo hnc (hrun.time_nonneg k)).localRun
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hv, .refl⟩
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  exact ⟨hvi, AC.viableAncestor_self (AC.frameIn_of_callAt hr hy hc').1 hPt (Or.inl hvi), hv⟩

/-- At an actual update the warm unanimous pool forces confirmation and fast
selection, at the slot committees `K` of a run from `K`'s committee start. No
lock-compatibility premise is used to select the raw result. -/
theorem Core.unanimous_update_selection_at
    {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
    {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b)
    (hvi : P ∈ ell.frame.viableTree ell.frame.tree)
    (hva : ell.frame.viableAncestor P = P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have _ := hdes
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hlate : sp.ts u + 2 * sp.Δ ≤ tr.time k := by rw [hkt]; linarith
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith) hz
  have hp := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hacc := (hp.accept_of_proposesAt (hnc.upTo _) hzk hP').1
  obtain ⟨ha', hta', _⟩ := hp.ac_block_after z hzk hacc
  have ha : tr.projAC.AcceptAt z (kP + 1) P := by
    rw [RunTrace.upTo_projAC] at ha'
    obtain ⟨ella, hca, hea⟩ := ha'
    exact ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
  have hta : tr.time (kP + 1) = sp.ts u := hta'.trans htime
  have hza : z ∈ H (tr.time (kP + 1)) := hta' ▸ hzk
  have hpool := Core.unanimous_early_pool_of_acceptance_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hPs hun hza ha hta hy hu.1 hlate hkb hvi.1 hK
  have hr := (hrun.acRun_upTo hnc (hrun.time_nonneg k)).localRun
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hPg : P.root ≠ sp.genesisRoot := by
    have hra := (hrun.acRun_upTo hnc (hrun.time_nonneg (kP + 1))).localRun
    apply AC.accept_ne_genesisU sp hra.toU hza
    obtain ⟨ella, hca, hea⟩ := ha
    exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
  have hslots : ∀ v ∈ (tr.projAC.state y k).pool u, v.slot = u := by
    intro v hv
    apply AC.state_pool_slotU sp hr.toU hrun.vstart hy k u v
    rwa [hs]
  obtain ⟨hconf, hfast⟩ := AC.confirmation_of_unanimous_early_pool
    (AC.frameIn_of_callAt hr hy hc').1 hvi.1 hPg K (hK.facts.hsize u)
    (fun v hv => hK.facts.hP.1 (tr.time k) y hy k (fun q hq => hrun.time_mono hq.le) u v hv)
    (hK.cs2 u hgu (by linarith) _ (hrun.time_nonneg k) hkb) hslots hpool
  exact ⟨hvi, hconf, hfast, hva⟩

end Consensus.Goldilocks.Healing.Growing

end
