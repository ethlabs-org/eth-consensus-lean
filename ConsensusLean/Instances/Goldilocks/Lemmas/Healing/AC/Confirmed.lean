module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ConfirmedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the confirmed tip after an honest proposal (H.1 (ii))

For an honest proposal `P` of slot `p`:

* `anc_acConfirmed_of_frame` (frame-only): when the head extends `P`, the confirmed tip extends
  `P`;
* `unanimous_pool_before`: the finite stamped honest batch of the slot committee, from actual
  unanimous casts. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## The record after the first update -/

/-! ## The head and the confirmed tip -/

/-- **The confirmed tip from the frame**: in a well-formed frame inside a
coherent `U`, a block `P` below both the effective record (`latest_confirmed` if in the tree, else
`Φ.F`) and the head is below the confirmed tip, the deepest common ancestor of the two (when `P` is
not in the tree it is below `Φ.F`, which every block of the tree extends). -/
theorem anc_acConfirmed_of_frame (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : ACState sp.n} {t : Time} {P : Blk sp.n FGP}
    (hPC : Anc U P ((lookup Φ A.latestConfirmed).getD Φ.F))
    (hPH : Anc U P (acHead sp A Φ t)) : Anc U P (acConfirmed sp A Φ t) := by
  have hCt : (lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
    cases h : lookup Φ A.latestConfirmed with
    | none => exact hΦ.rooted.1
    | some R => exact (lookup_eq_some h).1
  have hHt : acHead sp A Φ t ∈ Φ.tree :=
    getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ hX => hX.1) _ _ _ _
  unfold acConfirmed
  dsimp only
  have hFS : Φ.F ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)} :=
    ⟨hΦ.rooted.1, hΦ.rooted.2 _ hCt, hΦ.rooted.2 _ hHt⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X h => h.1) ⟨Φ.F, hFS⟩
  have hch : ∀ B ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)}, ∀ C ∈ {X | X ∈ Φ.tree ∧
      Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧ Φ.Anc X (acHead sp A Φ t)},
      Compatible Φ.tree B C := fun B hB C hC => anc_total hΦ.coherent hB.2.1 hC.2.1
  rw [hD, Option.getD_some]
  by_cases hPt : P ∈ Φ.tree
  · exact (anc_deepest hΦ (fun X h => h.1) hch hD P
      ⟨hPt, anc_tree_of_anc_U hU hΦ hΦU hPt hPC hCt,
        anc_tree_of_anc_U hU hΦ hΦU hPt hPH hHt⟩).mono hΦU
  · rcases anc_total hU hPC ((hΦ.rooted.2 _ hCt).mono hΦU) with h | h
    · exact h.trans ((anc_deepest hΦ (fun X h => h.1) hch hD Φ.F hFS).mono hΦU)
    · exact absurd (frame_mem_of_between sp hU hΦ hΦU hCt hPC h) hPt

/-- Finite stamped honest batch of the slot committee from actual unanimous casts. The
actual-vote existence input is separate from agreement; no ready-proposal support clause is
needed. -/
theorem unanimous_pool_before {K : AC.CommitteeDict sp.n}
    {b : Time} (hS : HealthyBaseUpTo K tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {P : Blk sp.n FGP} (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x ∈ H, x ∈ K.committee s →
      ∃ i e, VoteAt tr x i e ∧ e.msg.slot = s ∧ e.msg.head = P.root) :
    ∀ x ∈ H, x ∈ K.committee s → ∃ v ∈ (tr.state y j).pool s, v.val = x ∧ v.head = P.root ∧
      resolutionTime (tr.state y j) ell.frame v < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.state y j).pool s, v'.val = x → v' = v := by
  have hr := hS.run.localRun
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  intro x hx hxK
  obtain ⟨i, e, hv, hes, heP⟩ := hvotes x hx hxK
  obtain ⟨B, hB, hBr, hBs, hmem, hvs, hbs⟩ :=
    late_vote_held_of_frame_before hS hy hc hs ht hjb hdeadline hrestart hx hv hes
      (fun B hBU hBr => by
        rw [hr.coherent.1 hBU (hPhiU hPt) (hBr.trans heP)]
        exact (hPhi.rooted.2 P hPt).mono hPhiU)
  obtain ⟨hval, -⟩ := castAt_specU hr.toU hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, hmem, hval, heP,
    resolutionTime_lt_of hPhi hB hBr (hes ▸ hBs) hvs hbs, ?_⟩
  intro v' hv' hv'x
  obtain ⟨q, -, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j s v' hv' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr.toU x hx q i e' e he' hv
    ((state_pool_slotU sp hr.toU hS.run.vstart hy j s _ hv').trans hes.symm)
  rfl

end Consensus.Goldilocks.AC

end
