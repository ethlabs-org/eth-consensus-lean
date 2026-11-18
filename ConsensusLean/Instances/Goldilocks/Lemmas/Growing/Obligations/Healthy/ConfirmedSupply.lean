module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UpdateReadAfter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # The operational proposal's fresh locks and reads under growing faults

After the drain, the operational proposal of a slot reaches every honest reader's confirmed read:

* `operational_update_fresh_lock_at`: every update of the post-drain operational proposal `P` of
  slot `u`, by a node honest at it, writes the fresh fast lock `(P, u, true, e)`, `e ≥ u + 2`;
* `operational_proposal_read_after_at`: with those locks, every reader honest at `t_u + 6Δ` holds
  `P` under its confirmed read at the first cut after it (`operational_update_read_after_at`).

Each node is honest at its own cut or read; ancestry is in the blocks held while honest. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The frame of a node honest at a cut is well formed. -/
private theorem frameOK_state_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) : FrameOK (Node.frame (tr.state y i)) := by
  have h := Compose.frameOK_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A fast update writes its fast lock with an expiry of at least `u + 2` (`s + k` or
`fastExpiry`), so it is live at every `t` of slot at most `u + 2`. -/
private theorem fastLock_mem_updateConfirmation_floor {FGP : Type} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n FGP} {t : Time} {u : Nat} {P : SA.Blk sp.n FGP} (hPt : P ∈ Φ.tree)
    (hva : Φ.viableAncestor P = P) (hconf : SA.getConfirmation sp A Φ u = some P)
    (hnv : ¬ SA.conflictsWithLock sp A.locks Φ t P) (hfast : SA.fastSelect sp A Φ u P = some P)
    (hage : sp.slot t ≤ u + 2) :
    ∃ e, u + 2 ≤ e ∧
      (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (SA.updateConfirmation sp A Φ t u).locks := by
  have hD := Obligations.UpTo.deepest_of_subset (S := {B | B ∈ {B | B ∈
      SA.confirmationPath sp Φ P ∧ ¬ SA.conflictsWithLock sp A.locks Φ t B} ∧
      SA.FastTest sp A Φ u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(SA.deepest_mem hfast).1.1, hnv⟩, (SA.deepest_mem hfast).1.2⟩
  unfold SA.updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  exact ⟨_, SA.le_fastExpiry sp _ _ _ _, ⟨P.root, u, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPt, rfl,
    hage.trans (SA.le_fastExpiry sp _ _ _ _), by rw [hva]⟩

/-- **The fresh fast lock at an actual update.** Every update of slot `u` after the drain, by a
node honest at it, writes `(P, u, true, e)` for the actual designated proposal `P` of slot `u`,
whose proposer is honest through `t_u + Δ`, with an expiry `e ≥ u + 2`. -/
theorem operational_update_fresh_lock_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks := by
  have hΔ := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  obtain ⟨hPt, hconf, hnv, hfast, hpost, -⟩ :=
    operational_update_selection_at hp hhold hdesignated hactual hPs hR hgu hTb hy hup
  have hframe := Compose.Growing.frame_of_projAC_at hp.run hy hup.1
  have hPj : P ∈ (Node.frame (tr.state y j)).tree := hframe ▸ hPt
  have hPU : P ∈ tr.HonestBlocksAt H :=
    ⟨y, j, tr.time j, hp.run.time_nonneg j, fun q hq => hp.run.time_mono hq.le, hy, hPj.1⟩
  have hun0 := hp.operational_unanimous_at hhold hdesignated hactual hPs hR
    (show sp.ts u ≤ b by linarith only [hTb, hΔ])
  have hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root :=
    fun z q e hz hv hqb hs => hun0 z q e hz hv hs hqb
  have hRnext := hR.trans ((SA.ts_le_iff sp).mpr
    (show (u : Int) ≤ (u + 1 : Nat) by exact_mod_cast Nat.le_succ u))
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    exact (Nat.succ_pos _).trans_le (by exact_mod_cast this)
  obtain ⟨v, r, m, S, hseed, hrb, -, hrt⟩ := hp.reset_seed_before_slot_at hRnext
  have hSP := high_origins_before_next_slot_below_at hp hPU hun hgu hRnext
    (by linarith only [hTb, hΔ]) hseed hrt hrb
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hva : (Node.frame (tr.state y j)).viableAncestor P = P := by
    apply SA.viableAncestor_self (frameOK_state_at hp.run hy) hPj
    exact (hp.held_target_ancestor_candidate_at_state_at (hp.run.time_nonneg j)
      (fun q hq => hp.run.time_mono hq.le) hy hjb hPj hseed hrb hSP
      (fun x q l B hqe ho => (high_origin_compatible_before_update_at hp hPU hPs hu hun
        hgu hRnext hTb ho ((hp.run.time_mono hqe.le).trans ht.le)).symm)).symm
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
  rw [hpost]
  exact fastLock_mem_updateConfirmation_floor hPt (hframe ▸ hva) hconf hnv hfast
    (by rw [hslot]; exact Nat.le_succ _)

/-- **Every reader honest at `t_u + 6Δ` holds the operational proposal** under its confirmed read
at the first cut after `t_u + 6Δ`, when every update of slot `u` by a node honest at it writes the
fresh fast lock. -/
theorem operational_proposal_read_after_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    (hlocks : ∀ y j (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time j) →
      SA.UpdateAt tr.projAC y j u ell →
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks) :
    ∀ y J, y ∈ H (sp.ts u + 6 * sp.Δ) → Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ) →
      Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  intro y J hy hJ
  have hstart : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hg := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr le_rfl
    have hbound : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) =
        sp.ts (sp.slot (SA.gbar g)) + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hbound]
    linarith
  obtain ⟨j, ell, -, hup, -⟩ := hp.update_toFG_calls_at hy hstart hTb
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  exact operational_update_read_after_at hp hhold hdesignated hactual hPs hR hgu hTb hy hup
    (hlocks y j ell (ht ▸ hy) hup) hJ

end Consensus.Goldilocks.Healing.Growing

end
