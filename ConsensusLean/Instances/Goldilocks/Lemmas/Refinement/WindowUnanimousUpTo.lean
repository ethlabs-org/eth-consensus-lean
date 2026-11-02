module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParentsUpTo

public section

/-! # Goldilocks Refinement: the window from a unanimous slot, through a horizon (#137)

consensus-lean#137 (finite-horizon port). The `window_justifies_or_parents_above_unanimous`
family from `HealedUpTo … b` and `HSSharedUpTo … b`. The report duty
(`window_reports_of_unanimous`) already works through `b`; case (A) is for the honest proposals
of slots `s` with `v + Δ ≤ t_s ≤ b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The lock window or parents above a crossing report, from a unanimous slot, through the
horizon.** `window_justifies_or_parents_above_unanimous` from the horizon premises (`HealedUpTo
… b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_unanimous_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    ((∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
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
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj)))) ∨
    (∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧ tH ≤ tr.time r ∧
      tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  rcases window_reports_of_unanimous hp hcatch hP hslot hu hPg hun hgu hR
      (huv.trans hvb) htu huv hXP with hrep | hesc
  · exact Or.inl (window_justifies_or_parents_above_after_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb
    hy hc
      htH hl hf hB hBl hks hh hT hh₀ hp hvb hrep)
  · exact Or.inr hesc

/-- **The lock window or parents above a crossing report, from a unanimous slot, two-way,
through the horizon.** `window_justifies_or_parents_above_unanimous'` from the horizon premises
(`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_unanimous'_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P)
    (hXe : ∃ X ∈ (tr.state y k).fg.tree, X.root = T ∧ ((tr.state y k).fg.σ X.root).h = h) :
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
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_parents_above_unanimous_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc
    htH hl
      hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with
    hW | ⟨x, hx, r, e, C, hto, htr, hrv, hPC, hlt⟩
  · exact hW
  obtain ⟨X, hXk, hXT, hXh⟩ := hXe
  have hnc := hp.noColl
  have hXPa := hXP X hXk hXT
  have hCx : C ∈ (tr.state x r).fg.tree :=
    Healing.mem_tree_of_frame hrun hx hto.1 (toFG_live_fast_lock hto).1
  have hPx : P ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hPC hCx
  have hXx : X ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hXPa hPx
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hx r)
    (Healing.store_anc_of_honest_anc hrun hnc hx hXPa hPx)
  rw [Healing.σ_eq_honest hrun hnc hx hy hXx hXk, hXh] at hle
  have hhC : h < ((tr.state x r).fg.σ C.root).h := by omega
  refine Or.inl ⟨x, hx, r, e, C, hto, ?_, htr, hrv, hhC, fun s P' hP' hsv hsb => ?_⟩
  · have hrh := hH.toHealedRecordsUpTo.rh
    exact hp.cutZ_lt_of_high hx hCx (by omega)
  · exact crossed_parents_above_upTo hrun hnc hH hx hto htr hhC hP' (by linarith) hsb

/-- **The two-way window theorem without `hXe`, through the horizon.**
`window_justifies_or_parents_above_unanimous''` from the horizon premises (`HealedUpTo … b`,
`HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_unanimous''_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
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
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hX, hXr, -, hXh, -⟩ := Refinement.lock_entry_block hrun hy hBy
  exact window_justifies_or_parents_above_unanimous'_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH
    hl hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP
    ⟨X, hX, hXr.trans hT, hXh.trans hh⟩


end Consensus.Goldilocks.Refinement

end
