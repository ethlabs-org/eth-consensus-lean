module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Viable proposal suffixes under growing faults -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A held block above every pre-slot high origin reaches the proposal reader's floor. -/
theorem proposal_floor_above_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h := by
  have ht := hp.run.time_nonneg i
  have hj : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hj hpH
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hBh := Outcome.high_of_anc_at hp.run hp.noColl ho₀ ht hj hpH hB
    (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := Outcome.no_high_contest_at hp hpH hib
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state p i).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state p i).fg.headHeightFloor = (tr.state p i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hmax - 1) (by omega) (by omega)
  have hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults (tr.time i) ht hib
    have hn := sp.toParams.hn
    change 3 * (H (tr.time i))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change (H (tr.time i))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  obtain ⟨_, _, _, _, v, _, d, hdj, _, _, r, hrd, l, O, ho, hEO⟩ :=
    Outcome.left_entry_origin_at (g := g) hp.run hp.noColl ht hj hpH hq hE hET
      (by omega) hEC (by omega)
  have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib (by omega : r < i) ho
  obtain ⟨CV, ellw, D, _, hf, _⟩ := ho.2.2.1
  have hrt := Outcome.fastLock_time_lt_at hp.run hf hlu (by
    rw [← hti]
    have := hp.run.time_mono (show r ≤ i by omega)
    have := sp.toParams.hΔ
    linarith)
  have hEB := hEO.trans (hBold v r l O ho hrt
    ((hp.run.time_mono (show r ≤ i by omega)).trans hib))
  have hh := Healing.h_le_of_store_anc hreach
    (store_anc_of_honest_anc_at hp.run hp.noColl ht hj hpH hEB hB)
  omega

/-- The proposal suffix above all pre-slot high origins consists of viable heads. -/
theorem reset_suffix_viable_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ell.frame.tree)
    (hsD : ell.frame.Anc d.start D)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D) :
    ∀ X, ell.frame.Anc D X → ell.frame.Anc X d.head → X ∈ ell.frame.viableHeads := by
  intro X hDX _
  have hPhi := Outcome.frame_realized hp.run hpH hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpH hci
  have hXt : X ∈ ell.frame.tree := Compose.mem_of_anc_left hDX hDt
  have hDXU := hDX.mono hPhiU
  obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
  have hfX : ell.frame.Anc ell.frame.fcRoot X := by
    rw [hstart] at hsD
    exact ((SA.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hsD).trans hDX
  rw [Outcome.frame_of_call hp.run hpH hci] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  exact ⟨hXs, hFX, hfX.mono (fun _ h => h.1),
    hp.proposal_floor_above_old_at hpH hR hci hcall hti hib hXs
      (fun x r l O ho hrt hrb => (hDold x r l O ho hrt hrb).trans hDXU)⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
