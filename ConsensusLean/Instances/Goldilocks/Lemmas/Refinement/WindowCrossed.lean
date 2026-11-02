module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RowsSupply

public section

/-! # Goldilocks Refinement: the lock window or a crossing report (L5.4, WI-18)

`window_justifies_of_lock_healed` takes `h := σ[B].h` and `T := σ[B].Th` from the state of a
live fast lock on `B`; `rows_supply_or_crossed` takes a held entry block `T` with its state.

* `lock_entry_block`: for a block `B` held by an honest node, the entry block of `σ[B]`: a held
  ancestor `T` of `B` with `T.root = σ[B].Th`, `σ[T].h = σ[B].h` and `σ[T].Th = T.root`.
* `entry_HZ_bounds`: under `HealedRecords` (RH: `H_z + 1 ≤ h₀`) and `h₀ + 1 ≤ σ.h`, the bounds
  `H_z + 1 ≤ σ.h` and `σ.bound → H_z + 1 ≤ σ.h_j` of `rows_supply_or_crossed`.
* `window_justifies_or_crossed`: `window_justifies_of_lock_healed` with `S`, `hS`, `hsig`
  replaced by `ResetPremisesUpTo` (at `gR`, with `v ≤ b`) and a report `C ⪰ T` by `v` from each
  honest node. Either some honest report crosses `h`, or the window conclusion holds. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The entry block of a held block.** For `B` held by an honest `y` at cut `k`, a held
ancestor `T` of `B` with `T.root = σ[B].Th`, `σ[T].h = σ[B].h` and `σ[T].Th = T.root`. -/
theorem lock_entry_block (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y k).fg.tree) :
    ∃ T ∈ (tr.state y k).fg.tree, T.root = ((tr.state y k).fg.σ B.root).Th ∧
      (tr.state y k).fg.Anc T B ∧
      ((tr.state y k).fg.σ T.root).h = ((tr.state y k).fg.σ B.root).h ∧
      ((tr.state y k).fg.σ T.root).Th = T.root := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  obtain ⟨⟨T, hT, hTr, hTB, hTh, hTT⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr _ hB
  exact ⟨T, hT, hTr, hTB, hTh, hTT.trans hTr.symm⟩

/-- **The reset-height bounds of an entry state.** Under `HealedRecords` (RH) and
`h₀ + 1 ≤ σ.h`: `H_z + 1 ≤ σ.h`, and `σ.bound → H_z + 1 ≤ σ.h_j` (`bound_hj`). -/
theorem entry_HZ_bounds {gR : Time} {h₀ : Nat} {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : Healing.HealedRecords tr H gR h₀ E) {σ : FG.ChainState sp.n} (hh₀ : h₀ + 1 ≤ σ.h) :
    Healing.HZ tr H gR + 1 ≤ σ.h ∧ (σ.bound → Healing.HZ tr H gR + 1 ≤ σ.hj) := by
  have hrh := hR.rh
  refine ⟨by omega, fun hb => ?_⟩
  have := bound_hj hb
  omega

/-- **The lock window or a crossing report.** The premises of `window_justifies_of_lock_healed`
without `S`, `hS`, `hsig`; plus `ResetPremisesUpTo` at the healing time `gR` up to `b` with
`v ≤ b`, and: for the held block `X` with root `T`, each honest `z` reports by `v` some `C` with
`X ⪯ C`. Conclusion: (A) a held block `X` with root `T` below `B` and an honest report `C ⪰ X`
by `v` held by its reporter with `h < σ[C].h`; or the window conclusion. -/
theorem window_justifies_or_crossed (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
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
  have hR := hH.toHealedRecords
  obtain ⟨hhT, hhj⟩ := entry_HZ_bounds hR (σ := (tr.state y k).fg.σ X.root) (by omega)
  rcases rows_supply_or_crossed hp hR hy hX rfl hXT hhT hhj (by omega) hvb
      (hreports X hX hXr) with ⟨z, hz, r, ell, C, hto, hrv, hXC, hC, hlt⟩ | ⟨S, hSH, hS, hsig⟩
  · exact Or.inl ⟨X, hX, hXr, hXB, z, hz, r, ell, C, hto, hrv, hXC, hC, by omega⟩
  · refine Or.inr (window_justifies_of_lock_healed hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf
      hB hBl hks hh hT hh₀ S hSH hS ?_)
    intro z hz
    obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
    exact ⟨kz, att, hsg, hkv, hah.trans hXh, haT.trans hXr, by rw [← hXh]; exact hfirst⟩

/-- **The lock window or a crossing report, after `u`.** As `window_justifies_or_crossed`, with
each honest report at a cut `r` with `u ≤ t_r ≤ v`: case (A) also carries `u ≤ t_r`. -/
theorem window_justifies_or_crossed_after (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
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
  have hR := hH.toHealedRecords
  obtain ⟨hhT, hhj⟩ := entry_HZ_bounds hR (σ := (tr.state y k).fg.σ X.root) (by omega)
  rcases rows_supply_or_crossed_after hp hR hy hX rfl hXT hhT hhj (by omega) hvb
      (hreports' X hX hXr) with
    ⟨z, hz, r, ell, C, hto, hur, hrv, hXC, hC, hlt⟩ | ⟨S, hSH, hS, hsig⟩
  · exact Or.inl ⟨X, hX, hXr, hXB, z, hz, r, ell, C, hto, hur, hrv, hXC, hC, by omega⟩
  · refine Or.inr (window_justifies_of_lock_healed hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf
      hB hBl hks hh hT hh₀ S hSH hS ?_)
    intro z hz
    obtain ⟨kz, att, hsg, hkv, hah, haT, hfirst⟩ := hsig z hz
    exact ⟨kz, att, hsg, hkv, hah.trans hXh, haT.trans hXr, by rw [← hXh]; exact hfirst⟩

end Consensus.Goldilocks.Refinement

end
