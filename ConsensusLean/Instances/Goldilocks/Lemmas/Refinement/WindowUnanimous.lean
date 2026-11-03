module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParents
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # Goldilocks Refinement: window reports from a unanimous slot (L5.4, WI-18)

`window_justifies_or_parents_above_after` takes the report duty `hreports'`: every honest node
reports some `C ⪰ X` at a cut in `[tH, v]`, for each held `X` with root `T`. Here a unanimous
slot `u` on an honest `P` with `X ⪯ P` discharges it, through
`UpTo.report_cover_of_unanimous`. That theorem has an escape case (an honest report `C ⪰ P`
strictly higher than `P`), which these statements keep as a separate disjunct.

* `report_slot_le_time`: an honest report `C ⪰ P` is at a cut `r` with `t_{P.slot} ≤ t_r`.
* `window_reports_of_unanimous`: the report duty from a unanimous slot, with `tH ≤ t_u` and
  `t_u + 6Δ ≤ v`, or the escape report in `[tH, v]`.
* `window_justifies_or_parents_above_unanimous`: the window theorem with the report duty
  replaced by the unanimous-slot premises.
* `window_justifies_or_parents_above_unanimous'`: the same with a held `X` of root `T` at
  height `h`; the escape folds into case (A), so the conclusion is two-way.
* `window_justifies_or_parents_above_unanimous''`: the same without `hXe`, from
  `lock_entry_block`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A report above `P` is not before the slot of `P`.** If an honest `z` reports `C` at cut
`r` and `P ⪯ C` in the honest tree, then `t_{P.slot} ≤ t_r`. -/
theorem report_slot_le_time (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC z r ell C) (hPC : Anc (tr.HonestBlocks H) P C) :
    sp.ts (P.slot : Int) ≤ tr.time r := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hC := (toFG_live_fast_lock hto).1
  have hCs : C.slot ≤ sp.slot (tr.time r) := SA.frame_slot_le sp hr hz hto.1 C hC
  have hPs := Healing.slot_le_of_anc hr.coherent hPC
  exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r) _).2 (by omega)

/-- **The window report duty from a unanimous slot.** Under `ResetPremisesUpTo` (to `b`) and
`CatchRun 2Δ`, let the honest votes of slot `u` up to `b` all be for the honest `P` of slot `u`
(`0 < u`, `P` not genesis), with `ḡ + 4Δ ≤ t_u`, `drainTime(a) ≤ t_{u+1}`, `t_u + 6Δ ≤ b`.
Let every held `X` with root `T` have `X ⪯ P`, and `tH ≤ t_u`, `t_u + 6Δ ≤ v`. Then every
honest `z` reports some `C ⪰ X` at a cut in `[tH, v]` (the form of `hreports'`), or some
honest `x` reports `C ⪰ P` at a cut in `[tH, v]` with `σ[P].h < σ[C].h` at that cut. -/
theorem window_reports_of_unanimous {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {tH v : Time} (htH : tH ≤ sp.ts u) (hv : sp.ts u + 6 * sp.Δ ≤ v)
    {y : Fin sp.n} {k T : Nat}
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tH ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) ∨
    (∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧ tH ≤ tr.time r ∧
      tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  have hlow : ∀ {z : Fin sp.n}, z ∈ H → ∀ {r : Nat} {ell : ACLabel (goldilocksNode sp ro)}
      {C : SA.Blk sp.n (List (FG.Att sp.n))}, SA.ToFGAt tr.projAC z r ell C →
      Anc (tr.HonestBlocks H) P C → tH ≤ tr.time r := by
    intro z hz r ell C hto hPC
    have := report_slot_le_time hp.run hp.noColl hz hto hPC
    rw [hslot] at this
    exact htH.trans this
  rcases UpTo.report_cover_of_unanimous hp hc hP hslot hu hPg hun hgu hR hTb with
    hall | ⟨x, hx, r, e, C, hto, ht, hPC, hh⟩
  · refine Or.inl fun X hX hXT z hz => ?_
    obtain ⟨r, e, R, hto, ht, hPR⟩ := hall z hz
    exact ⟨r, e, R, hto, hlow hz hto hPR, ht.trans hv,
      (hXP X hX hXT).trans hPR⟩
  · exact Or.inr ⟨x, hx, r, e, C, hto, hlow hx hto hPC, ht.trans hv, hPC, hh⟩

/-- **The lock window or parents above a crossing report, from a unanimous slot.**
`window_justifies_or_parents_above_after` with `hreports'` replaced by the premises of
`window_reports_of_unanimous` (the reset premises `hp` to `b` with `v ≤ b`, `CatchRun 2Δ` from
`gR`, a unanimous slot `u` on the honest `P`, `tH ≤ t_u`, `t_u + 6Δ ≤ v`, and `X ⪯ P` for
every held `X` with root `T`). Conclusion: the conclusion of
`window_justifies_or_parents_above_after`, or an honest report `C ⪰ P` at a cut in `[tH, v]`
with `σ[P].h < σ[C].h` at that cut. -/
theorem window_justifies_or_parents_above_unanimous (hrun : GoldilocksRun proposer dg H tr)
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
              ((tr.state (proposer s') k).fg.σ Pr.root).hj)))) ∨
    (∃ x ∈ H, ∃ r e C, SA.ToFGAt tr.projAC x r e C ∧ tH ≤ tr.time r ∧
      tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  rcases window_reports_of_unanimous hp hcatch hP hslot hu hPg hun hgu hR
      (huv.trans hvb) htu huv hXP with hrep | hesc
  · exact Or.inl (window_justifies_or_parents_above_after hrun hq hH hs hv hM4 hs₁ hvs hy hc
      htH hl hf hB hBl hks hh hT hh₀ hp hvb hrep)
  · exact Or.inr hesc

/-- **The lock window or parents above a crossing report, from a unanimous slot, two-way.**
`window_justifies_or_parents_above_unanimous` with one more premise `hXe`: some held `X` with
root `T` has `σ[X].h = h` at the store of `y` at cut `k`. Then `X ⪯ P` gives `h ≤ σ[P].h`, so
the escape report `C` has `h < σ[C].h` and `crossed_parents_above` applies to it: the
conclusion is that of `window_justifies_or_parents_above_after` (no escape disjunct). -/
theorem window_justifies_or_parents_above_unanimous' (hrun : GoldilocksRun proposer dg H tr)
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
  rcases window_justifies_or_parents_above_unanimous hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl
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
  refine Or.inl ⟨x, hx, r, e, C, hto, ?_, htr, hrv, hhC, fun s P' hP' hsv => ?_⟩
  · have hrh := hH.toHealedRecords.rh
    exact hp.cutZ_lt_of_high hx hCx (by omega)
  · exact crossed_parents_above hrun hnc hH hx hto htr hhC hP' (by linarith)

/-- **The two-way window theorem without `hXe`.** `window_justifies_or_parents_above_unanimous'`
with `hXe` discharged by `lock_entry_block`: the entry block `X` of the held lock block `B` has
root `σ[B].Th = T` and `σ[X].h = σ[B].h = h`. -/
theorem window_justifies_or_parents_above_unanimous'' (hrun : GoldilocksRun proposer dg H tr)
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
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hX, hXr, -, hXh, -⟩ := Refinement.lock_entry_block hrun hy hBy
  exact window_justifies_or_parents_above_unanimous' hrun hq hH hs hv hM4 hs₁ hvs hy hc htH
    hl hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP
    ⟨X, hX, hXr.trans hT, hXh.trans hh⟩


end Consensus.Goldilocks.Refinement

end
