module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowCrossed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RowsSupplyUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ExposureUpTo

public section

/-! # Goldilocks Refinement: the lock window or a crossing report, through a horizon (#137)

consensus-lean#137 (finite-horizon port). `window_justifies_or_crossed` and
`window_justifies_or_crossed_after` from `HealedUpTo … b` and `HSSharedUpTo … b`, with every
window slot by `b` (`hwb`) and `v ≤ b`. `entry_HZ_bounds_upTo` is `entry_HZ_bounds` for
`HealedRecordsUpTo`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The reset-height bounds of an entry state, through the horizon** (`entry_HZ_bounds_upTo`
for `HealedRecordsUpTo`: RH only). -/
theorem entry_HZ_bounds_upTo {gR b : Time} {h₀ : Nat} {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E) {σ : FG.ChainState sp.n}
    (hh₀ : h₀ + 1 ≤ σ.h) :
    Healing.HZ tr H gR + 1 ≤ σ.h ∧ (σ.bound → Healing.HZ tr H gR + 1 ≤ σ.hj) := by
  have hrh := hR.rh
  refine ⟨by omega, fun hb => ?_⟩
  have := bound_hj hb
  omega

/-- **The lock window or a crossing report, through the horizon.** `window_justifies_or_crossed`
from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_crossed_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hreports : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
        Anc (tr.HonestBlocks H) X C) :
    (∃ X ∈ (tr.state y k).fg.tree, X.root = T ∧ (tr.state y k).fg.Anc X B ∧
      ∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
        Anc (tr.HonestBlocks H) X C ∧ C ∈ (tr.state z r).fg.tree ∧
        h < ((tr.state z r).fg.σ C.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hX, hXr, hXB, hXh, hXT⟩ := lock_entry_block hrun hy hBy
  rw [hT] at hXr
  rw [hh] at hXh
  have hR := hH.toHealedRecordsUpTo
  obtain ⟨hhT, hhj⟩ := entry_HZ_bounds_upTo hR (σ := (tr.state y k).fg.σ X.root) (by omega)
  rcases rows_supply_or_crossed_upTo hp hR hy hX rfl hXT hhT hhj (by omega) hvb
      (hreports X hX hXr) with ⟨z, hz, r, ell, C, hto, hrv, hXC, hC, hlt⟩ | ⟨S, hSH, hS, hsig⟩
  · exact Or.inl ⟨X, hX, hXr, hXB, z, hz, r, ell, C, hto, hrv, hXC, hC, by omega⟩
  · refine Or.inr (window_justifies_of_lock_healed_upTo hrun hq hH hs hv hvb hM4 hs₁ hvs hwb hy
    hc htH hl hf
      hB hBl hks hh hT hh₀ S hSH hS ?_)
    intro z hz
    obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
    exact ⟨kz, att, hsg, hkv, hah.trans hXh, haT.trans hXr, by rw [← hXh]; exact hfirst⟩

/-- **The lock window or a crossing report, after `u`, through the horizon.**
`window_justifies_or_crossed_after` from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo …
b`). -/
theorem window_justifies_or_crossed_after_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (hs : Healing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁) (hwb : ∀ s', s' < s₁ + gM → sp.ts s' ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b) {u : Time}
    (hreports' : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ u ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) :
    (∃ X ∈ (tr.state y k).fg.tree, X.root = T ∧ (tr.state y k).fg.Anc X B ∧
      ∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ u ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C ∧ C ∈ (tr.state z r).fg.tree ∧
        h < ((tr.state z r).fg.σ C.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hX, hXr, hXB, hXh, hXT⟩ := lock_entry_block hrun hy hBy
  rw [hT] at hXr
  rw [hh] at hXh
  have hR := hH.toHealedRecordsUpTo
  obtain ⟨hhT, hhj⟩ := entry_HZ_bounds_upTo hR (σ := (tr.state y k).fg.σ X.root) (by omega)
  rcases rows_supply_or_crossed_after_upTo hp hR hy hX rfl hXT hhT hhj (by omega) hvb
      (hreports' X hX hXr) with
    ⟨z, hz, r, ell, C, hto, hur, hrv, hXC, hC, hlt⟩ | ⟨S, hSH, hS, hsig⟩
  · exact Or.inl ⟨X, hX, hXr, hXB, z, hz, r, ell, C, hto, hur, hrv, hXC, hC, by omega⟩
  · refine Or.inr (window_justifies_of_lock_healed_upTo hrun hq hH hs hv hvb hM4 hs₁ hvs hwb hy
    hc htH hl hf
      hB hBl hks hh hT hh₀ S hSH hS ?_)
    intro z hz
    obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
    exact ⟨kz, att, hsg, hkv, hah.trans hXh, haT.trans hXr, by rw [← hXh]; exact hfirst⟩

end Consensus.Goldilocks.Refinement

end
