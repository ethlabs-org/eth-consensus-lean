module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks Refinement: C3 of the Healed bundle from the reset (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` L4.5/L4.6
(C3, A-safe). A live fast lock on `X` at an honest call at a time `≥ tH` comes from a stored
fast lock of label `m` with `slot(t) ≤ m + k`; that lock was written by a fast confirmation
(`Healing.stored_fast_lock_provenance`) on a block `D` with `X ⪯ D`. With the drain over by
`tH`, the label `m` is clean (`m ≥ cleanLabel + k + 2`), and a proposal of slot `s` with
`t + Δ ≤ t_s` has `m < s`. For `m + 2 ≤ s` the predecessor batch puts `D` below the duty head
(`Healing.clean_source_proposal_parent_before`); for `s = m + 1` the lock is optimistic (an
update of `m` runs at `t_m + 6Δ`) and `Healing.clean_optimistic_proposal_parent` applies. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- **C3 from the reset.** Under the reset and Catch(2Δ) with the drain over by the heal time
(`drainTime ≤ tH`), C3 (A-safe) of `Healed` holds. -/
theorem c3_of_reset (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time}
    (hR : Healing.drainTime sp a ≤ tH) :
    ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
      ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr := by
  intro y hy k ℓ hck htk l hl hlf X hX hXr s P hP hks
  obtain ⟨l₀, hl₀, B, hB, hBr, hlive, rfl⟩ := hl
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hck
  have hvB := SA.viableAncestor_anc hPhi hB
  obtain rfl : X = ℓ.frame.viableAncestor B := hU.1 (hPhiU hX) (hPhiU hvB.1) hXr
  obtain ⟨r, hrk, CV, ℓ', D, hcr, hfl, L, hL, hLr, hLD⟩ :=
    Healing.stored_fast_lock_provenance hr hy k l₀ hl₀ hlf
  rw [hU.1 hL (hPhiU hB) (hLr.trans hBr.symm)] at hLD
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell' = ℓ' := Option.some.inj (hc'.2.symm.trans hcr.2)
  obtain ⟨hPhi', hPhiU'⟩ := SA.frameIn_of_callAt hr hy hc'
  have hXD : Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B) D :=
    (hvB.2.mono hPhiU).trans (hLD.trans ((SA.viableAncestor_anc hPhi' hD).2.mono hPhiU'))
  obtain ⟨hpH, i, ell, d, pay, hci, hcall, hd, hti, hpar, -⟩ := hP
  -- the slot bounds
  have hk0 := hp.run.time_nonneg k
  have hrt : tr.time r ≤ tr.time k := hp.run.time_mono hrk.le
  have hRk : Healing.drainTime sp a ≤ tr.time k := hR.trans htk
  rw [Healing.drainTime_eq] at hRk
  have hsk := (SA.ts_le_iff_le_slot sp hk0 _).1 hRk
  have hks' : ¬ sp.ts s ≤ tr.time k := by linarith
  rw [SA.ts_le_iff_le_slot sp hk0] at hks'
  have hlab : Healing.cleanLabel sp a + sp.k + 2 ≤ l₀.slot := by
    rw [Healing.cleanLabel_eq]; omega
  have hRs : Healing.drainTime sp a ≤ sp.ts s := by
    rw [Healing.drainTime_eq]; exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hQ : Anc (tr.HonestBlocks H) D d.head → ∃ Pr ∈ tr.HonestBlocks H,
      P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B) Pr := by
    intro hDQ
    obtain ⟨hPhiP, hPhiPU⟩ := SA.frameIn_of_callAt hr hpH hci
    obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhiP hd
    have hQt : d.head ∈ ell.frame.tree := by
      rcases eq_or_ne d.start d.head with he | he
      · exact he ▸ hst
      · exact (Anc.mem hsQ he).2
    exact ⟨d.head, hPhiPU hQt, hpar, hXD.trans hDQ⟩
  have hclean : l₀.slot + 2 ≤ s → Anc (tr.HonestBlocks H) D d.head := fun h2 =>
    Healing.clean_source_proposal_parent_before hp hc hy hpH (Or.inl ⟨CV, hfl⟩) hlab h2 hRs
      hci hcall hd hti
  rcases hfl with hup | hop
  · obtain ⟨-, -, ⟨-, -, ht, -⟩, -⟩ := hup
    have ht' : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := ht
    have h2 : l₀.slot + 2 ≤ s := by
      have hlt : sp.ts (l₀.slot + 1 : Nat) < sp.ts s := by
        have : sp.ts (l₀.slot + 1 : Nat) = sp.ts l₀.slot + 4 * sp.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        linarith
      have := (SA.ts_lt_iff sp).1 hlt
      omega
    exact hQ (hclean h2)
  · have hsl : sp.slot (tr.time r) = l₀.slot := hop.choose_spec.choose_spec.2.1
    have hsm := SA.slot_mono sp (hp.run.time_nonneg r) hrt
    rcases Nat.lt_or_ge (l₀.slot + 1) s with h2 | h1
    · exact hQ (hclean (by omega))
    · obtain rfl : s = l₀.slot + 1 := by omega
      exact hQ (Healing.clean_optimistic_proposal_parent hp hc hy hpH hop hlab hRs hci hcall hd
        hti)

/-- **Healed from the reset, canonical form, C3 and C4 discharged.** Under the reset and
Catch(2Δ) with the drain over by the heal time, `Healed` holds for the canonical entries. -/
theorem healed_of_reset_canonical_full (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time} {h₀ : Nat}
    (hrh : Healing.HZ tr H g + 1 ≤ h₀) (Z₀ : SA.Blk sp.n (List (FG.Att sp.n)))
    (hR : Healing.drainTime sp a ≤ tH) :
    Healed tr H proposer g tH h₀ (Healing.canonicalEntry tr H g Z₀) := by
  have h0 : 0 ≤ tH := by
    refine le_trans ?_ hR
    rw [Healing.drainTime_eq]; simp only [SA.SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by positivity)
  have hR' : Healing.drainTime sp a ≤ sp.ts (sp.slot tH + 1) := by
    refine hR.trans (le_of_lt (not_le.1 fun h => ?_))
    have := (SA.ts_le_iff_le_slot sp h0 _).1 h
    omega
  exact healed_of_reset_canonical_c4 hp hc hrh Z₀ (c3_of_reset hp hc hR) hR'

end Consensus.Goldilocks.Refinement

end
