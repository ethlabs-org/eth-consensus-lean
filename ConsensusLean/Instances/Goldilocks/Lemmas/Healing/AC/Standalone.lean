module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: standalone proposal-block inclusion with the unlock given

Over a `StandaloneRunU` (driven AC traces of the SA with trivial frames, the frame of every honest
call being the tree of the blocks the node has accepted, rooted at genesis, under `Healthy(g)`,
`Catch(2Δ)`, `NoColl` and unforgeable signatures), `ac_healing_standalone_tight_corollaryU` is
proposal-block inclusion from `ḡ + (8k + 10)Δ + G_p` under `Prop(G_p)`. Its per-proposal step is
`ac_healing_standalone_of_parent_tightU` (`Steps.lean`). `Prop(G_p)` gives an honest proposer in
`[t, t + G_p]`, joined there (no restart after `ḡ`), so its `ac_proposal` returns a payload and
`Driven (b)` gives its proposal (`corollary_atU`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

/-- `corollary_at` with the unlock given. -/
theorem corollary_atU
    {u : Nat → Set Lock} {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} {g Gp c : Time} (hc : 4 * sp.Δ ≤ c)
    (hS : StandaloneRunU wm u tr H U proposer g) (hprop : PropAC proposer H g Gp)
    (h : ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposalU u tr (proposer p) p P →
      gbar g + c ≤ sp.ts p →
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))
    (t : Time) (ht : gbar g + c ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
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
  refine ⟨p, P, htp, htpG, hP, fun y hy j ℓ' hc' htj htick =>
    h p P hpH hP hgp y hy j ℓ' hc' (by linarith) fun heq => htick (by linarith)⟩

/-- **The corollary from H.1's inclusion at a threshold `ḡ + c`** (`c ≥ 4Δ`): `Prop(G_p)` gives a
slot `p` with an honest proposer and `t ≤ t_p ≤ t + G_p`; the proposer is awake and joined at
`t_p` (no restart after `ḡ`), so `ac_proposal` returns a payload and `Driven (b)` gives the
honest proposal `P`; the inclusion at `P` holds from `t_p + 6Δ ≤ t + G_p + 6Δ`. -/
private theorem corollary_at {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} {g Gp c : Time} (hc : 4 * sp.Δ ≤ c)
    (hS : StandaloneRun tr H U proposer g) (hprop : PropAC proposer H g Gp)
    (h : ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposal tr (proposer p) p P →
      gbar g + c ≤ sp.ts p →
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))
    (t : Time) (ht : gbar g + c ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposal tr (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨p, P, h1, h2, hP, h3⟩ := corollary_atU hc hS.toU hprop
    (fun p P hpH hP hp => h p P hpH ((honestProposalU_parent_iff _ _ _ _).1 hP) hp) t ht
  exact ⟨p, P, h1, h2, (honestProposalU_parent_iff _ _ _ _).1 hP, h3⟩

/-- **Proposal-block inclusion at `ḡ + (8k + 4)Δ` with the unlock given** (for every lock rule
related to the parent's unlock, at every write mode of width `k`): the conclusions of
`ac_healing_standalone_of_parent_tightU` at an honest proposal of `Prop(G_p)`. -/
theorem ac_healing_standalone_tight_corollaryU {u : Nat → Set Lock} {FGP : Type} {sp : SAParams}
    {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n} {g Gp : Time}
    (hS : StandaloneRunU wm u tr H U proposer g) (hw : wm.width = sp.k)
    (hprop : PropAC proposer H g Gp) (t : Time)
    (ht : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ t) :
    ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧
      HonestProposalU u tr (proposer p) p P ∧
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = t + Gp + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := Int.natCast_nonneg _
  have hkΔ := mul_nonneg hk hΔ.le
  exact corollary_atU (c := (8 * (sp.k : Time) + 4) * sp.Δ) (by linarith) hS hprop
    (fun p P hpH hP hp => (ac_healing_standalone_of_parent_tightU hS hw hpH hP hp).2) t ht

end Consensus.Goldilocks.SA

end
