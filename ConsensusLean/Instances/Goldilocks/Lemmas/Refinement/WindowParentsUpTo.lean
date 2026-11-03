module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParents
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowCrossedUpTo

public section

/-! # Goldilocks Refinement: parents above a crossing report, through a horizon (#137)

consensus-lean#137 (finite-horizon port). `crossed_parents_above` and the
`window_justifies_or_parents_above` family from `HealedUpTo … b` and `HSSharedUpTo … b`. C3
through the horizon needs `t_s ≤ b`, so case (A) bounds the parents of the honest proposals of
slots `s` with `v + Δ ≤ t_s ≤ b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Parents above a crossing report, through the horizon.** `crossed_parents_above` from the
horizon premises (`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem crossed_parents_above_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    {z : Fin sp.n} (hz : z ∈ H) {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C)
    (htH : tH ≤ tr.time r) {h : Nat} (hlt : h < ((tr.state z r).fg.σ C.root).h)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hs : tr.time r + sp.Δ ≤ sp.ts s)
    (hsb : sp.ts s ≤ b) :
    ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
      ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree → h < ((tr.state y k).fg.σ Pr.root).h := by
  obtain ⟨hCf, l, hl, hlb, hlf, -⟩ := toFG_live_fast_lock hto
  obtain ⟨Pr, hPr, hpar, hCPr⟩ :=
    hH.c3 z hz r ell hto.1 htH l hl hlf C hCf hlb.symm s P hP hs hsb
  refine ⟨Pr, hPr, hpar, hCPr, fun y hy k hPrk => ?_⟩
  have hCz : C ∈ (tr.state z r).fg.tree := Healing.mem_tree_of_frame hrun hz hto.1 hCf
  have hCk : C ∈ (tr.state y k).fg.tree := Healing.mem_of_honest_anc hrun hnc hy hCPr hPrk
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
    (Healing.store_anc_of_honest_anc hrun hnc hy hCPr hPrk)
  rw [Healing.σ_eq_honest hrun hnc hz hy hCz hCk] at hlt
  omega

/-- **The lock window or parents above a crossing report, through the horizon.**
`window_justifies_or_parents_above` from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo …
b`). -/
theorem window_justifies_or_parents_above_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (tH ≤ tr.time r → ∀ s P, Healing.HonestProposalRun tr H proposer s P →
        v + sp.Δ ≤ sp.ts s → sp.ts s ≤ b →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).previousHeightJustified →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_crossed_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf hB hBl
    hks
      hh hT hh₀ hp hvb hreports with
    ⟨-, -, -, -, z, hz, r, ell, C, hto, hrv, -, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, hrv, hlt, ?_⟩
    · have hrh := hH.toHealedRecordsUpTo.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · intro htr s P hP hsv hsb
      exact crossed_parents_above_upTo hrun hp.noColl hH hz hto htr hlt hP (by linarith) hsb
  · exact Or.inr hW

/-- **The lock window or parents above a crossing report, `tH ≤ cutZ(gR)`, through the
horizon.** `window_justifies_or_parents_above_of_le_cutZ` from the horizon premises (`HealedUpTo
… b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_of_le_cutZ_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : HealedUpTo tr H proposer gR tH b h₀ E)
    (htZ : tH ≤ Healing.cutZ sp.toParams gR)
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
    (∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s → sp.ts s ≤ b →
      ∃ C Pr, Pr ∈ tr.HonestBlocks H ∧ P.parent = some Pr.root ∧
        Anc (tr.HonestBlocks H) C Pr ∧
        ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree → h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).previousHeightJustified →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_parents_above_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf
    hB hBl
      hks hh hT hh₀ hp hvb hreports with ⟨z, hz, r, ell, C, -, hcz, -, -, hA⟩ | hW
  · refine Or.inl fun s P hP hsv hsb => ?_
    obtain ⟨Pr, hPr, hpar, hCPr, hab⟩ := hA (htZ.trans hcz.le) s P hP hsv hsb
    exact ⟨C, Pr, hPr, hpar, hCPr, hab⟩
  · exact Or.inr hW

/-- **The lock window or parents above a crossing report, reports after `tH`, through the
horizon.** `window_justifies_or_parents_above_after` from the horizon premises (`HealedUpTo …
b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_after_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (hreports' : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tH ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s → sp.ts s ≤ b →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).previousHeightJustified →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_crossed_after_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf
    hB hBl
      hks hh hT hh₀ hp hvb hreports' with
    ⟨-, -, -, -, z, hz, r, ell, C, hto, htr, hrv, -, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, htr, hrv, hlt, fun s P hP hsv hsb => ?_⟩
    · have hrh := hH.toHealedRecordsUpTo.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · exact crossed_parents_above_upTo hrun hp.noColl hH hz hto htr hlt hP (by linarith) hsb
  · exact Or.inr hW

end Consensus.Goldilocks.Refinement

end
