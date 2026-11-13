module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.1, AC healing standalone (trivial frames), and its corollary

H.1 over driven AC traces of the SA with trivial frames (the frame of every honest call is the
tree of the blocks the node has accepted, rooted at genesis), under `Healthy(g)`, `Catch(2Δ)`,
`NoColl` and unforgeable signatures. Proved on paper (claims H.1, proof shape): with
`r = r_AC(ḡ)`, results of one slot `≥ r` are compatible; a fast origin of label `≥ r`, and a
slow origin whose window is `≥ r`, transfers to the next slot's honest votes and every later one
(A1.2, A1.4, A1.3, A1.8); every other lock expires before `t_r + 2Θ`; at `P` the voter's tree is
contained in the proposer's and the scores agree, so every honest slot-`p` vote is `P`, and from
`t_p + 6Δ` the record extends `P`.

The steps and their assembly are in `Steps.lean` (`ac_healing_standalone_of_parent_tight`,
H.1's conclusions for one honest proposal at `t_p ≥ ḡ + (8k + 4)Δ`). H.1 at that threshold
(`ac_healing_standalone_tight`) implies H.1 at `ḡ + 2Θ + 8Δ = ḡ + (8k + 16)Δ`
(`standalone_of_tight`), which is how `ac_healing_standalone` is proved.

Each corollary follows from its H.1 (`corollary_of_standalone`, `corollary_of_standalone_tight`):
`Prop(G_p)` gives an honest proposer in `[t, t + G_p]`, joined there (no restart after `ḡ`), so
its `ac_proposal` returns a payload and `Driven (b)` gives its proposal. The tight corollary is
proposal-block inclusion from `ḡ + (8k + 10)Δ + G_p`; it implies the corollary
(`corollary_of_tight_corollary`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

/-- **H.1 at `ḡ + (8k + 4)Δ`** (claims H.1, proof shape, with the locks settled from the slot
start `t_{p−1} ≥ ḡ + 8kΔ`). -/
theorem ac_healing_standalone_tight (sp : SAParams) : ACHealingStandaloneTight (sp := sp) :=
  fun _ _ _ _ _ _ _ hrun hdr htriv hheal hcatch _ _ hpH hP hp =>
    ac_healing_standalone_of_parent_tight ⟨⟨hrun, hdr, hheal, hcatch, hrun.stock⟩, htriv⟩ hpH hP hp

/-- **H.1 at `ḡ + (8k + 4)Δ` gives H.1**: `ḡ + (8k + 4)Δ ≤ ḡ + 2Θ + 8Δ = ḡ + (8k + 16)Δ`. -/
theorem standalone_of_tight (sp : SAParams) (h : ACHealingStandaloneTight (sp := sp)) :
    ACHealingStandalone (sp := sp) :=
  fun FGP ro H U tr proposer g hrun hdr htriv hheal hcatch p P hpH hP hp =>
    h FGP ro H U tr proposer g hrun hdr htriv hheal hcatch p P hpH hP
      (by have := sp.toParams.hΔ; unfold Θ at hp; linarith)

/-- **H.1, AC healing standalone** (claims H.1, proof shape): from H.1 at `ḡ + (8k + 4)Δ`. -/
theorem ac_healing_standalone (sp : SAParams) : ACHealingStandalone (sp := sp) :=
  standalone_of_tight sp (ac_healing_standalone_tight sp)

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

/-- **H.1 at `ḡ + (8k + 4)Δ` with the unlock given** (`ac_healing_standalone_tight` for every lock
rule related to the parent's unlock, at every write mode of width `k`): H.1's conclusions at an
honest proposal of `Prop(G_p)`. -/
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

/-- **H.1 gives its corollary**: for `t ≥ ḡ + 2Θ + 8Δ`, `Prop(G_p)` gives a slot `p` with an
honest proposer and `t ≤ t_p ≤ t + G_p`; the proposer is awake and joined at `t_p` (no restart
after `ḡ`), so `ac_proposal` returns a payload and `Driven (b)` gives the honest proposal `P`;
H.1 at `P` holds from `t_p + 6Δ ≤ t + G_p + 6Δ`. -/
theorem corollary_of_standalone (sp : SAParams) (h : ACHealingStandalone (sp := sp)) :
    ACHealingStandaloneCorollary (sp := sp) := by
  intro FGP ro H U tr proposer g Gp hrun hdr htriv hheal hcatch hprop t ht
  have hΘ := Θ_nonneg sp
  have hΔ := sp.toParams.hΔ
  exact corollary_at (c := 2 * Θ sp + 8 * sp.Δ) (by linarith)
    ⟨⟨hrun, hdr, hheal, hcatch, hrun.stock⟩, htriv⟩ hprop
    (fun p P hpH hP hp => (h FGP ro H U tr proposer g hrun hdr htriv hheal hcatch p P hpH hP
      (by linarith)).2) t (by linarith)

/-- **H.1 at `ḡ + (8k + 4)Δ` gives its corollary**, proposal-block inclusion from
`ḡ + (8k + 10)Δ + G_p`, as `corollary_of_standalone`. -/
theorem corollary_of_standalone_tight (sp : SAParams) (h : ACHealingStandaloneTight (sp := sp)) :
    ACHealingStandaloneTightCorollary (sp := sp) := by
  intro FGP ro H U tr proposer g Gp hrun hdr htriv hheal hcatch hprop t ht
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := Int.natCast_nonneg _
  have hkΔ := mul_nonneg hk hΔ.le
  exact corollary_at (c := (8 * (sp.k : Time) + 4) * sp.Δ) (by linarith)
    ⟨⟨hrun, hdr, hheal, hcatch, hrun.stock⟩, htriv⟩ hprop
    (fun p P hpH hP hp => (h FGP ro H U tr proposer g hrun hdr htriv hheal hcatch p P hpH hP
      (by linarith)).2) t (by linarith)

/-- **H.1, corollary**: H.1 at an honest proposal of `Prop(G_p)`. -/
theorem ac_healing_standalone_corollary (sp : SAParams) :
    ACHealingStandaloneCorollary (sp := sp) :=
  corollary_of_standalone sp (ac_healing_standalone sp)

/-- **H.1 at `ḡ + (8k + 4)Δ`, corollary** (proposal-block inclusion): H.1 at `ḡ + (8k + 4)Δ` at
an honest proposal of `Prop(G_p)`. -/
theorem ac_healing_standalone_tight_corollary (sp : SAParams) :
    ACHealingStandaloneTightCorollary (sp := sp) :=
  corollary_of_standalone_tight sp (ac_healing_standalone_tight sp)

/-- **The corollary at `ḡ + (8k + 4)Δ` gives the corollary**: its threshold is lower. -/
theorem corollary_of_tight_corollary (sp : SAParams)
    (h : ACHealingStandaloneTightCorollary (sp := sp)) :
    ACHealingStandaloneCorollary (sp := sp) :=
  fun FGP ro H U tr proposer g Gp hrun hdr htriv hheal hcatch hprop t ht =>
    h FGP ro H U tr proposer g Gp hrun hdr htriv hheal hcatch hprop t
      (by have := sp.toParams.hΔ; unfold Θ at ht; linarith)

end Consensus.Goldilocks.SA

end
