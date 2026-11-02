module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimousUpTo

public section

/-! # Goldilocks Refinement: the entry is justified on the parent's chain, through a horizon

consensus-lean#137 (finite-horizon port) of the trace-level half of `WindowEntry` (L5.4,
WI-19): `window_justifies_or_parents_above_after'`, `..._unanimous_entry`,
`window_entry_justified_or_window`, `window_entry_justified_M4` and
`window_entry_justified_M4_anc`, from `HealedUpTo … b` and `HSSharedUpTo … b`. Guards:

* `hwb`: every slot `s' < s₁ + g` of the lock window has `t_{s'} ≤ b` (the window proposal is
  served by `b`; C3 through the horizon for its parent in `window_entry_justified_M4_anc_upTo`);
* case (A) is for the honest proposals of slots `s` with `v + Δ ≤ t_s ≤ b` (C3 through the
  horizon); in the M4 forms, `hwb₂`: every slot `s < s₂ + g` has `t_s ≤ b`;
* `v ≤ b` (the reports and rows by `v`). -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Two held blocks of one honest store with the same root are equal. -/
private theorem eq_of_root_eq' (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {X X' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hX' : X' ∈ (tr.state y k).fg.tree)
    (he : X.root = X'.root) : X = X' :=
  (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy k)).2.1.1 hX hX' he

/-- **The window with the entry below the report.** `window_justifies_or_parents_above_after'`
from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_after'_upTo (hrun : GoldilocksRun proposer dg H tr)
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
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
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
  rcases window_justifies_or_crossed_after_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf
    hB hBl
      hks hh hT hh₀ hp hvb hreports' with
    ⟨X₀, hX₀, hX₀r, -, z, hz, r, ell, C, hto, htr, hrv, hXC, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, htr, hrv, hlt, fun X hX hXr => ?_,
      fun s P hP hsv hsb => ?_⟩
    · have hrh := hH.toHealedRecordsUpTo.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · rw [eq_of_root_eq' hrun hy hX hX₀ (hXr.trans hX₀r.symm)]
      exact hXC
    · exact crossed_parents_above_upTo hrun hp.noColl hH hz hto htr hlt hP (by linarith) hsb
  · exact Or.inr hW

/-- **The two-way window theorem with the entry below the report.**
`window_justifies_or_parents_above_unanimous_entry` from the horizon premises (`HealedUpTo … b`,
`HSSharedUpTo … b`). -/
theorem window_justifies_or_parents_above_unanimous_entry_upTo
    (hrun : GoldilocksRun proposer dg H tr)
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
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
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
  obtain ⟨X, hXk, hXr, -, hXh, -⟩ := lock_entry_block hrun hy hBy
  rcases window_reports_of_unanimous hp hcatch hP hslot hu hPg hun hgu hR
      (huv.trans hvb) htu huv hXP with hrep | ⟨x, hx, r, e, C, hto, htr, hrv, hPC, hlt⟩
  · exact window_justifies_or_parents_above_after'_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc
      htH hl hf hB hBl hks hh hT hh₀ hp hvb hrep
  have hnc := hp.noColl
  have hXPa := hXP X hXk (hXr.trans hT)
  have hCx : C ∈ (tr.state x r).fg.tree :=
    Healing.mem_tree_of_frame hrun hx hto.1 (toFG_live_fast_lock hto).1
  have hPx : P ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hPC hCx
  have hXx : X ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hXPa hPx
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hx r)
    (Healing.store_anc_of_honest_anc hrun hnc hx hXPa hPx)
  rw [Healing.σ_eq_honest hrun hnc hx hy hXx hXk, hXh, hh] at hle
  have hhC : h < ((tr.state x r).fg.σ C.root).h := by omega
  refine Or.inl ⟨x, hx, r, e, C, hto, ?_, htr, hrv, hhC,
    fun X' hX' hX'r => (hXP X' hX' hX'r).trans hPC, fun s P' hP' hsv hsb => ?_⟩
  · have hrh := hH.toHealedRecordsUpTo.rh
    exact hp.cutZ_lt_of_high hx hCx (by omega)
  · exact crossed_parents_above_upTo hrun hnc hH hx hto htr hhC hP' (by linarith) hsb

/-- **L5.4: the entry is justified on the parent's chain (r14 s5).**
`window_entry_justified_or_window` from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo …
b`). -/
theorem window_entry_justified_or_window_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s → sp.ts s ≤ b →
        s ≤ ((tr.state y k).fg.σ X.root).ThSlot + sp.toParams.fg.δt →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, -, hX₀h, hX₀T⟩ := lock_entry_block hrun hy hBy
  rcases window_justifies_or_parents_above_unanimous_entry_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb
    hy hc htH
    hl hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with
    ⟨-, -, -, -, C, -, -, -, -, -, hXC, hA⟩ | hW
  · refine Or.inl fun X hX hXr s P' hP' hsv hsb hsδ => ?_
    obtain rfl : X = X₀ := eq_of_root_eq' hrun hy hX hX₀ (hXr.trans (hX₀r.trans hT).symm)
    obtain ⟨Pr, hPr, hpar, hCPr, habove⟩ := hA s P' hP' hsv hsb
    have hXPr := (hXC X hX hXr).trans hCPr
    refine ⟨Pr, hPr, hpar, hXPr, fun w hw j hPrj => ?_⟩
    have hnc := hp.noColl
    have hXw := Healing.mem_of_honest_anc hrun hnc hw hXPr hPrj
    have hσ := Healing.σ_eq_honest hrun hnc hy hw hX hXw
    obtain ⟨-, ℓ', -, -, -, -, -, -, -, hPs, -, -, j', -, hacc, -⟩ := hP'.2
    have hP'm : P' ∈ tr.HonestBlocks H := ⟨_, hP'.1, j', hp.acceptAt_mem hP'.1 hacc⟩
    have hPrs : Pr.slot < P'.slot := hp.honest_coherent.2 Pr hPr P' hP'm hpar
    have hXh : ((tr.state w j).fg.σ X.root).h = h := by rw [← hσ, hX₀h, hh]
    have hXT : ((tr.state w j).fg.σ X.root).Th = T := by rw [← hσ, hX₀T, hX₀r, hT]
    obtain ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩ := Store.entry_justified_of_anc
      (Compose.fg_reachable hrun.toLocalRun hw j) hXw
      (Healing.store_anc_of_honest_anc hrun hnc hw hXPr hPrj)
      (by rw [hXh]; exact habove w hw j hPrj) (by rw [← hσ]; omega)
    rw [hXh] at h1 h2
    rw [hXT] at h3
    rw [← hσ] at h4
    exact ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩
  · exact Or.inr hW

/-- **L5.4 with the M4 proposal (r14 s5).** `window_entry_justified_M4` from the horizon
premises (`HealedUpTo … b`, `HSSharedUpTo … b`). -/
theorem window_entry_justified_M4_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T → s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1 →
      ∃ s, s₂ ≤ s ∧ s < s₂ + gM ∧ ∃ P, Healing.HonestProposalRun tr H proposer s P ∧
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  rcases window_entry_justified_or_window_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf
    hB hBl
    hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with hA | hW
  · refine Or.inl fun X hX hXr hδ => ?_
    obtain ⟨s, hs₂s, hss, P', hP'⟩ := hM4 s₂ hs₂
    have hThs := (lock_entry_ThSlot hrun hy hBy hX (hXr.trans hT.symm)).1
    have hts : sp.ts s₂ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs₂s)
    exact ⟨s, hs₂s, hss, P', hP', hA X hX hXr s P' hP' (hvs₂.trans hts) (hwb₂ s hss)
      (by rw [hThs]; omega)⟩
  · exact Or.inr hW

/-- **L5.4 with the M4 proposal, the entry below the parent in the window case.**
`window_entry_justified_M4_anc` from the horizon premises (`HealedUpTo … b`, `HSSharedUpTo …
b`). -/
theorem window_entry_justified_M4_anc_upTo (hrun : GoldilocksRun proposer dg H tr)
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
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂)
    (hwb₂ : ∀ s, s < s₂ + gM → sp.ts s ≤ b) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T → s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1 →
      ∃ s, s₂ ≤ s ∧ s < s₂ + gM ∧ ∃ P, Healing.HonestProposalRun tr H proposer s P ∧
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ kp X Pr,
      tr.ProposesAt (proposer s') kp X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') kp).fg.tree ∧
      (h < ((tr.state (proposer s') kp).fg.σ Pr.root).h ∨
        (((tr.post kp).fg.σ X.root).hj = h ∧ ((tr.post kp).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') kp).fg.σ Pr.root).bound →
            ((tr.post kp).fg.σ X.root).hF =
              ((tr.state (proposer s') kp).fg.σ Pr.root).hj))) ∧
      ∀ X' ∈ (tr.state y k).fg.tree, X'.root = T → Anc (tr.HonestBlocks H) X' Pr := by
  have hnc := hp.noColl
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, hX₀B, -, -⟩ := lock_entry_block hrun hy hBy
  rcases window_entry_justified_M4_upTo hrun hq hH hs hv hM4 hs₁ hvs hwb hy hc htH hl hf hB hBl
    hks hh
    hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP hs₂ hvs₂ hwb₂ with hA | hW
  · exact Or.inl hA
  obtain ⟨s', hs's, hs'g, hpH, k', Xp, Pr, hprop, hsl, hpar, hPr, harm⟩ := hW
  have hXr := Healing.honestProposalRun_of_proposesAt hrun hnc hpH
    (proposesAt_designated hrun hpH hprop) hprop rfl
  have hts : tr.time k + sp.Δ ≤ sp.ts Xp.slot :=
    hks.trans ((SA.ts_le_iff sp).2 (by rw [hsl]; exact_mod_cast hs's))
  obtain ⟨Pr', hPr'H, hpar', hanc⟩ := hH.c3 y hy k ℓ hc htH l hl hf B hB hBl Xp.slot Xp hXr hts
    (hsl ▸ hwb s' hs'g)
  obtain rfl : Pr' = Pr := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 hPr'H
    ⟨_, hpH, k', hPr⟩ (Option.some.inj (hpar'.symm.trans hpar))
  refine Or.inr ⟨s', hs's, hs'g, hpH, k', Xp, Pr', hprop, hsl, hpar, hPr, harm,
    fun X' hX' hX'r => ?_⟩
  obtain rfl : X' = X₀ := eq_of_root_eq' hrun hy hX' hX₀ (hX'r.trans (hX₀r.trans hT).symm)
  exact (Anc.mono (T := tr.HonestBlocks H) (fun _ hZ => ⟨y, hy, k, hZ⟩) hX₀B).trans hanc

end Consensus.Goldilocks.Refinement

end
