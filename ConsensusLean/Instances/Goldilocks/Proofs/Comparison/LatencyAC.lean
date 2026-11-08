module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.LatencyAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SettledGenesis
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks comparison instances at Tier A: proposal latency (Slice 0)

* `proposalLatencyAC0_sync`: `6Δ` from slot `2` at every width-`k` write mode and unlock oracle,
  from inclusion from a synchronous start (`ac_healing_of_sync_startU`).
* `proposalLatencyAC0_bridge`: with `Prop(G_p)`, from the corollary at threshold `t₂ = 8Δ` and
  the same inclusion; `corollary_memU` is upstream's `corollary_atU` keeping the proposer's
  membership in `H`. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

/-- A slot whose start is at or after `t₂` is at least `2`. -/
private theorem two_le_of_ts {sp : SAParams} {p : Nat} (h : sp.ts 2 ≤ sp.ts p) : 2 ≤ p := by
  have hΔ := sp.toParams.hΔ
  simp only [SAParams.ts] at h
  have : (2 : Int) ≤ p := le_of_mul_le_mul_left (by linarith) (by linarith : (0 : Int) < 4 * sp.Δ)
  omega

theorem proposalLatencyAC0_sync : ProposalLatencyAC0Sync := by
  intro sp
  refine ⟨fun f f' hf => ?_, ?_⟩
  · unfold acLat0
    by_cases h' : 2 * f' < sp.n
    · simp [h', lt_of_le_of_lt (by omega : 2 * f ≤ 2 * f') h']
    · simp [h']
  · intro m hw u FGP ro H U tr proposer f c g hc hI p P hp hpH hP
    unfold acLat0 at hc
    split_ifs at hc
    · obtain rfl : c = 6 := (WithTop.coe_injective hc).symm
      have := (ac_healing_of_sync_startU hw hI.1 hI.2.1 hp hpH hP).2
      push_cast
      exact this
    · exact absurd hc WithTop.top_ne_coe

/-- `corollary_atU` keeping the proposer's membership in `H`: `Prop(G_p)` gives a slot `p` with an
honest proposer and `t ≤ t_p ≤ t + G_p`; the proposer is awake and joined at `t_p`, so
`ac_proposal` returns a payload and `DrivenU (b)` gives the honest proposal `P`; the inclusion at
`P` holds from `t_p + 6Δ ≤ t + G_p + 6Δ`. -/
private theorem corollary_memU {m : WriteMode} {u : Nat → Set Lock} {FGP : Type} {sp : SAParams}
    {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n} {g Gp c : Time} (hc : 4 * sp.Δ ≤ c)
    (hS : StandaloneRunU m u tr H U proposer g) (hprop : PropAC proposer H g Gp)
    (h : ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposalU u tr (proposer p) p P →
      gbar g + c ≤ sp.ts p →
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))
    (t : Time) (ht : gbar g + c ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧ proposer p ∈ H ∧
      HonestProposalU u tr (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hdr := hS.driven
  have hΔ := sp.toParams.hΔ
  obtain ⟨p, hp1, htp, htpG, hpH⟩ := hprop t (by linarith [gbar_nonneg g])
  have hgp : gbar g + c ≤ sp.ts p := ht.trans htp
  have hslot : sp.slot (sp.ts p) = p :=
    slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  have hj : gbar g ≤ sp.ts ((sp.slot (sp.ts p) : Int) - 1) := by
    rw [hslot, ts_sub_one]; linarith
  obtain ⟨k, ℓ, hc, hcall, htk, himp⟩ := hdr.proposal p (by omega) _ hpH rfl
    (hS.awake hpH (by linarith)) (hS.joinedAt hpH hj)
  have hjs := hS.joined_state hpH k (by rw [htk]; exact hj)
  obtain ⟨d, pay, hdp⟩ : ∃ d pay,
      (acProposal sp (tr.state (proposer p) k) ℓ.frame (tr.time k)).2 =
        some (d, pay) := by
    unfold acProposal
    simp only [hjs, not_true_eq_false, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  obtain ⟨P, hP⟩ := himp ⟨pay, hc, hcall, d, hdp⟩
  exact ⟨p, P, htp, htpG, hpH, hP, fun y hy j ℓ' hc' htj htick =>
    h p P hpH hP hgp y hy j ℓ' hc' (by linarith) fun heq => htick (by linarith)⟩

theorem proposalLatencyAC0_bridge : ProposalLatencyAC0Bridge := by
  intro sp m hw u FGP ro H U tr proposer f g Gp hI hprop t ht
  have hΔ := sp.toParams.hΔ
  have hg0 : gbar g = 0 := max_eq_right hI.2.1
  have ht2 : sp.ts 2 = 8 * sp.Δ := by simp only [SAParams.ts]; ring
  refine corollary_memU (c := 8 * sp.Δ) (by linarith) hI.1 hprop
    (fun p P hpH hP hp => (ac_healing_of_sync_startU hw hI.1 hI.2.1
      (two_le_of_ts (by rw [ht2]; rw [hg0] at hp; linarith)) hpH hP).2) t
    (by rw [hg0]; linarith)

end Consensus.Goldilocks.Comparison

end
