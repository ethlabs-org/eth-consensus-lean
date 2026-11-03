module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowCrossed

public section

/-! # Goldilocks Refinement: parents above a crossing report (L5.4, WI-18)

Case (A) of `window_justifies_or_crossed` is an honest report `C` with `h < σ[C].h`. Through C3
(`Healed.c3`) it bounds the parents of later honest proposals.

* `toFG_live_fast_lock`: the block `C` that `ac_to_fg` returns at an honest call is in the
  frame, and its root is the block of a live fast lock of that call.
* `crossed_parents_above`: if the report is at a time `≥ tH`, every honest proposal of a slot
  `s` with `t_r + Δ ≤ t_s` has an honest parent `Pr ⪰ C` with `h < σ[Pr].h` at each holder.
* `window_justifies_or_parents_above`: `window_justifies_or_crossed` with case (A) in this form
  (a crossing report after cutZ by `v`; for proposals with `v + Δ ≤ t_s` when `tH ≤ t_r`).
* `window_justifies_or_parents_above_of_le_cutZ`: the same under `tH ≤ cutZ(gR)`, with case
  (A) without the condition on `t_r`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A report is a live fast lock block.** If `ac_to_fg` returns `C` at the call of `z` at
cut `r`, then `C` is in the frame and some live fast lock `l` of that call has
`l.block = C.root` (and slot `≥ slot(t_r) − 2`). -/
theorem toFG_live_fast_lock {z : Fin sp.n} {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C) :
    C ∈ ell.frame.tree ∧
      ∃ l ∈ SA.liveLocks sp (tr.projAC.state z r).locks ell.frame (tr.time r),
        l.block = C.root ∧ l.fast = true ∧ sp.slot (tr.time r) ≤ l.slot + 2 := by
  obtain ⟨-, -, h⟩ := hto
  have hC : C ∈ SA.toFGCandidates sp (tr.projAC.state z r) ell.frame (tr.projAC.time r) := by
    unfold SA.acToFG at h
    split_ifs at h
    split at h
    · cases h
    · rename_i C' hC'
      split_ifs at h
      cases h
      exact (SA.deepest_mem hC').1
  exact ⟨hC.1.1, hC.2⟩

/-- **Parents above a crossing report** (C3 with `X := C`). For an honest report `C` of `z` at
cut `r` with `tH ≤ t_r` and `h < σ[C].h`: every honest proposal `P` of a slot `s` with
`t_r + Δ ≤ t_s` has an honest parent `Pr` with `C ⪯ Pr`, and `h < σ[Pr].h` at every honest
holder of `Pr`. -/
theorem crossed_parents_above (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    {z : Fin sp.n} (hz : z ∈ H) {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C)
    (htH : tH ≤ tr.time r) {h : Nat} (hlt : h < ((tr.state z r).fg.σ C.root).h)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hs : tr.time r + sp.Δ ≤ sp.ts s) :
    ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
      ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree → h < ((tr.state y k).fg.σ Pr.root).h := by
  obtain ⟨hCf, l, hl, hlb, hlf, -⟩ := toFG_live_fast_lock hto
  obtain ⟨Pr, hPr, hpar, hCPr⟩ :=
    hH.c3 z hz r ell hto.1 htH l hl hlf C hCf hlb.symm s P hP hs
  refine ⟨Pr, hPr, hpar, hCPr, fun y hy k hPrk => ?_⟩
  have hCz : C ∈ (tr.state z r).fg.tree := Healing.mem_tree_of_frame hrun hz hto.1 hCf
  have hCk : C ∈ (tr.state y k).fg.tree := Healing.mem_of_honest_anc hrun hnc hy hCPr hPrk
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hy k)
    (Healing.store_anc_of_honest_anc hrun hnc hy hCPr hPrk)
  rw [Healing.σ_eq_honest hrun hnc hz hy hCz hCk] at hlt
  omega

/-- **The lock window or parents above a crossing report.** The premises of
`window_justifies_or_crossed`. Conclusion: (A) an honest report `C` of some `z` at a cut `r`
with `cutZ(gR) < t_r ≤ v` and `h < σ[C].h`, and, if `tH ≤ t_r`, every honest proposal of a
slot `s` with `v + Δ ≤ t_s` has an honest parent `Pr ⪰ C` with `h < σ[Pr].h` at every honest
holder; or the window conclusion. -/
theorem window_justifies_or_parents_above (hrun : GoldilocksRun proposer dg H tr)
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
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (tH ≤ tr.time r → ∀ s P, Healing.HonestProposalRun tr H proposer s P →
        v + sp.Δ ≤ sp.ts s →
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
  rcases window_justifies_or_crossed hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl hks
      hh hT hh₀ hp hvb hreports with
    ⟨-, -, -, -, z, hz, r, ell, C, hto, hrv, -, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, hrv, hlt, ?_⟩
    · have hrh := hH.toHealedRecords.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · intro htr s P hP hsv
      exact crossed_parents_above hrun hp.noColl hH hz hto htr hlt hP (by linarith)
  · exact Or.inr hW

/-- **The lock window or parents above a crossing report, `tH ≤ cutZ(gR)`.** As
`window_justifies_or_parents_above`, with the premise `tH ≤ cutZ(gR)`: in case (A) every honest
proposal of a slot `s` with `v + Δ ≤ t_s` has an honest parent `Pr ⪰ C` with `h < σ[Pr].h` at
every honest holder. -/
theorem window_justifies_or_parents_above_of_le_cutZ (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (htZ : tH ≤ Healing.cutZ sp.toParams gR)
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
    (∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
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
  rcases window_justifies_or_parents_above hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl
      hks hh hT hh₀ hp hvb hreports with ⟨z, hz, r, ell, C, -, hcz, -, -, hA⟩ | hW
  · refine Or.inl fun s P hP hsv => ?_
    obtain ⟨Pr, hPr, hpar, hCPr, hab⟩ := hA (htZ.trans hcz.le) s P hP hsv
    exact ⟨C, Pr, hPr, hpar, hCPr, hab⟩
  · exact Or.inr hW

/-- **The lock window or parents above a crossing report, reports after `tH`.** As
`window_justifies_or_parents_above`, with each honest report at a cut `r` with
`tH ≤ t_r ≤ v`. Conclusion: (A) an honest report `C` of some `z` at a cut `r` with
`cutZ(gR) < t_r`, `tH ≤ t_r ≤ v` and `h < σ[C].h`, and every honest proposal of a slot `s` with
`v + Δ ≤ t_s` has an honest parent `Pr ⪰ C` with `h < σ[Pr].h` at every honest holder; or the
window conclusion. -/
theorem window_justifies_or_parents_above_after (hrun : GoldilocksRun proposer dg H tr)
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
    (hreports' : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tH ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
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
  rcases window_justifies_or_crossed_after hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl
      hks hh hT hh₀ hp hvb hreports' with
    ⟨-, -, -, -, z, hz, r, ell, C, hto, htr, hrv, -, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, htr, hrv, hlt, fun s P hP hsv => ?_⟩
    · have hrh := hH.toHealedRecords.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · exact crossed_parents_above hrun hp.noColl hH hz hto htr hlt hP (by linarith)
  · exact Or.inr hW

end Consensus.Goldilocks.Refinement

end
