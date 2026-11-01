module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OperationalPersistence

public section

/-! # Goldilocks Refinement: C4 of the Healed bundle from the reset (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` L4.6 (C4,
no reorg of honest blocks). Under `Healing.ResetPremises` and Catch(2Δ), an honest operational
proposal of a post-drain slot `s` is an ancestor of every honest proposal of a slot `s' ≥ s + 2`
(`honest_proposal_below_later`, from `UpTo.operational_proposal_below_later_parent`). C4 then
needs only the adjacent pairs `s' = s + 1` and the operational form (`ProposesAt`) of the earlier
proposal; both are explicit premises of `c4_of_reset` and `healed_of_reset_c4`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- **No reorg two slots on.** Under the reset and Catch(2Δ), the honest proposal `P` of a
post-drain slot `s`, made operationally (`ProposesAt`), is an ancestor of the honest proposal
`P'` of every slot `s' ≥ s + 2`. -/
theorem honest_proposal_below_later (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hk : ∃ k, tr.ProposesAt (proposer s) k P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.HonestProposalRun tr H proposer s' P') (hss : s + 2 ≤ s') :
    Anc (tr.HonestBlocks H) P P' := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  obtain ⟨hy, i, ell, d, pay, hci, hcall, hd, hti, hpar, -, -, -, j, -, hacc, -⟩ := hP'
  set b : Time := max (max (sp.ts s') (sp.ts s + 6 * sp.Δ)) a
  have hpu := Healing.ResetPremises.toUpTo tr H hp (b := b) (le_max_right _ _)
  have hib : tr.time i ≤ b := hti ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := (le_max_right _ _).trans (le_max_left _ _)
  have hPd := UpTo.operational_proposal_below_later_parent hpu hc hP.1 rfl hk hPs hR hTb hy hss
    hci hcall hd hti hib
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ell.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hBU : P' ∈ tr.HonestBlocks H := ⟨_, hy, j, Healing.acceptAt_mem hp hy hacc⟩
  exact hPd.trans (.single ⟨hPhiU hQt, hBU, hpar⟩)

/-- **C4 from the reset, the adjacent pairs and the operational proposals.** Under the reset and
Catch(2Δ) with the drain over by `t_{slot(tH)+1}`, C4 of `Healed` holds when (i) each honest
proposal of a slot `s > slot(tH)` is made operationally (`hown`) and (ii) C4 holds for adjacent
slots `s, s + 1` (`hadj`). The pairs `s' ≥ s + 2` are `honest_proposal_below_later`. -/
theorem c4_of_reset (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time}
    (hR : Healing.drainTime sp a ≤ sp.ts (sp.slot tH + 1))
    (hown : ∀ s P, Healing.HonestProposalRun tr H proposer s P → sp.slot tH < s →
      ∃ k, tr.ProposesAt (proposer s) k P)
    (hadj : ∀ s P P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer (s + 1) P' → sp.slot tH < s →
        Anc (tr.HonestBlocks H) P P') :
    ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
        Anc (tr.HonestBlocks H) P P' := by
  intro s P s' P' hP hP' hs hss
  rcases Nat.lt_or_ge (s + 1) s' with h2 | h1
  · have hRs : Healing.drainTime sp a ≤ sp.ts s := hR.trans ((SA.ts_le_iff sp).2 (by omega))
    exact honest_proposal_below_later hp hc hP (hown s P hP hs) hRs hP' (by omega)
  · obtain rfl : s' = s + 1 := by omega
    exact hadj s P P' hP hP' hs

/-- **Healed from the reset, C3, and the reduced C4 premises** (`c4_of_reset`). -/
theorem healed_of_reset_c4 (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}
    (hrh : Healing.HZ tr H g + 1 ≤ h₀) (hE : ∀ h, h₀ ≤ h → Healing.HighEntry tr H g h (E h))
    (hc3 : ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
      ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr)
    (hR : Healing.drainTime sp a ≤ sp.ts (sp.slot tH + 1))
    (hown : ∀ s P, Healing.HonestProposalRun tr H proposer s P → sp.slot tH < s →
      ∃ k, tr.ProposesAt (proposer s) k P)
    (hadj : ∀ s P P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer (s + 1) P' → sp.slot tH < s →
        Anc (tr.HonestBlocks H) P P') :
    Healed tr H proposer g tH h₀ E :=
  healed_of_reset hp hrh hE hc3 (c4_of_reset hp hc hR hown hadj)

end Consensus.Goldilocks.Refinement

end
