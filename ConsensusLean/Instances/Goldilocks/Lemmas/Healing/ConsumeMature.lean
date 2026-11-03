module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing

public section

/-! # Goldilocks Healing, HS.5: mature progress consumption

`hs5-exact-helpers.md` §3 ("choose `X` before inspecting its
parent"), over `Γ` and the phase `(m, c)` through the first cut `j_b` after
`b = τ + G_p + Δ`, `τ = max(v + Δ_F, t_{E.slot + δ_t})`, `v = t_s + 6Δ`
(`mature_progress_of`; `Service` splits off the phase-change branch).

The assembly (proved): `Prop⁺` at `τ` selects the ready proposal `X` of slot `x`,
`τ ≤ t_x ≤ τ + G_p`, kept throughout (also when its parent already crossed). Its proposal cut is
before `j_b`, so the protected parent clause gives `X`'s parent `Pr ⪰ W`, hence `W ⪯ X`; `E ⪯ Pr`
gives `ht(Pr) ≥ h`. If `ht(Pr) > h`, `ht(X) ≥ h + 1` at once; if `ht(Pr) = h`, the crossing is
`crossing_of_rows` (§3.1, `ConsumeCrossing`), with the rows delivered to the proposer before
its cut by `GST(g)` (`rows_delivered`). Universal acceptance (§3.2): `X` is above the floor, so
allowed at its proposer after its cut (`effAllowed_of_floor_lt`); HS.1 (`hret`) puts every
honest `Σ.F` below `X` at the tick at `t_x + Δ` (before `j_b`); the acceptance relay of `GST(g)`
(the proposer's acceptance at `t_x ≥ ḡ`, deadline `t_x + Δ`, no restart after `ḡ`) gives an
actual acceptance strictly before `t_x + Δ`. Sorry-free. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- **The rows reach the proposer before `t_x`** (`hs5-exact-helpers.md` §3.1, first paragraph;
`GST(g)`'s attestation delivery): a row signed by an honest validator by `v` is processed by the
honest proposer of slot `x`, `t_x ≥ v + Δ_F`, at a cut before its proposal cut (as an attestation
or carried by an accepted block). Post-`g` rows have the deadline `time + Δ_F ≤ v + Δ_F`, pre-`g`
rows the effective deadline `g + Δ_F` (no honest restart after `ḡ ≤ v`). -/
theorem rows_delivered (hs : HSShared tr H dg g ΔF) {v : Time}
    (hv : gbar g ≤ v) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j, tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := fun j => by
    have := deadline_le_of_healthy hs hp j (max (tr.time k) g) ΔF
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hs.healthy.1.attestation y hy k att (Or.inl hsig) trivial p hp
    kX ⟨_, hcall⟩ (by linarith [hdl kX])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith [hdl k']

/-- **Mature progress consumption in the phase** (`hs5-exact-helpers.md` §3; the mature-progress
step of `Service`'s `consume_continue`, with the phase `(m, c)` through `j_b`, `RowsBy` spelled out
and HS.1 as the hypothesis `hret`). -/
theorem mature_progress_of (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H proposer g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hret : ViableWitnessRetention) {s h kW : Nat}
    {E W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt (proposer s) kW W) (_hWs : W.slot = s)
    (hpH : proposer s ∈ H) (hE : EntryOf (tr.post kW).fg W E h)
    (hh : phaseFloor m c ≤ h) (hws : w ≤ sp.ts s)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
      proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr)
    (hrows : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
      att.T = E.root) {jb : Nat}
    (hjb : FirstCutAfter tr jb
      (max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ))
    (hon : PhaseOn tr.projFG H i₀ jb m c) :
    ∃ (x kX : Nat) (X : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer (proposer x) kX x X ∧
      max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) ≤ sp.ts x ∧
      sp.ts x + sp.Δ ≤
        max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ ∧
      h + 1 ≤ ((tr.post kX).fg.σ X.root).h ∧ Anc (tr.HonestBlocks H) W X ∧
      ∀ y ∈ H, ∃ k, tr.AcceptAt y k X ∧ tr.time k < sp.ts x + sp.Δ := by
  have hnc := hs.noColl
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΔF : 0 ≤ ΔF := hs.healthy.1.deltaF.le
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  set τ := max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) with hτ
  have hτ₁ : sp.ts s + 6 * sp.Δ + ΔF ≤ τ := le_max_left _ _
  -- the ready proposal `X` of `Prop⁺` at `τ`, kept throughout
  obtain ⟨x, kX, X, -, hx₁, hx₂, hX⟩ := hp τ (by linarith)
  obtain ⟨hpX, -, -, hprop, hXs, -⟩ := id hX
  refine ⟨x, kX, X, hX, hx₁, by linarith, ?_⟩
  have hkX : tr.time kX = sp.ts x := by rw [hprop.2.2, hXs, sp.slotTime_eq]; rfl
  have hX₁ : sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts x := hτ₁.trans hx₁
  have hkjb : kX < jb := hjb.lt_of_time_le hrun.time_mono (by linarith)
  have hi₀ : i₀ ≤ kX := by
    by_contra hlt
    have := hset.2.1.2 kX (not_le.1 hlt)
    linarith
  have hsx : s < x := by
    have : sp.ts s < sp.ts x := by linarith
    exact_mod_cast (SA.ts_lt_iff sp).1 this
  obtain ⟨hacc, hXt, hpost⟩ := accept_of_proposesAt hrun hnc hpX hprop
  obtain ⟨-, hWt, hpostW⟩ := accept_of_proposesAt hrun hnc hpH hW
  obtain ⟨Pr, hpar, hWPr⟩ :=
    hparents x X kX hsx hXs hprop hpX (fun k' h₁ h₂ => hon k' h₁ (by omega))
  have hsub : ∀ {y : Fin sp.n} (_ : y ∈ H) (i : Nat),
      (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun hy i X hX => ⟨_, hy, i, hX⟩
  have hWX := anc_of_parentRoot (hsub hpH _ hWt) hWPr (hsub hpX _ hXt) hpar
  -- the height of `X`
  have hcross : h + 1 ≤ ((tr.post kX).fg.σ X.root).h := by
    rw [hpost]
    have hR := Compose.fg_reachable hrun.toLocalRun hpX (kX + 1)
    have hPrX : Anc (tr.HonestBlocks H) Pr X := Relation.ReflTransGen.single
      ⟨mem_of_anc_right hWPr (hsub hpH _ hWt), hsub hpX _ hXt, hpar⟩
    have hPrt := mem_of_honest_anc hrun hnc hpX hPrX hXt
    have hPrX' := h_le_of_store_anc hR (store_anc_of_honest_anc hrun hnc hpX hPrX hXt)
    obtain ⟨⟨hEt, hETh⟩, hEh, hEW⟩ := hpostW ▸ hE
    have hEPr : Anc (tr.HonestBlocks H) E Pr := (hEW.mono (hsub hpH _)).trans hWPr
    have hEt' := mem_of_honest_anc hrun hnc hpX hEPr hPrt
    have hEPr' := h_le_of_store_anc hR (store_anc_of_honest_anc hrun hnc hpX hEPr hPrt)
    rw [σ_eq_honest hrun hnc hpX hpH hEt' hEt, hEh] at hEPr'
    rcases hEPr'.lt_or_eq with hlt | heq
    · omega
    · have hdel : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ att.h = h ∧ att.T = E.root ∧
          ∃ k' < kX, tr.ProcessAttAt (proposer x) k' att := fun y hy => by
        obtain ⟨k, att, hsig, hk, hah, haT⟩ := hrows y hy
        exact ⟨k, att, hsig, hah, haT, rows_delivered hs (by linarith) hpX hprop
          (by rw [hkX]; exact hX₁) hy hsig hk⟩
      have hEs : E.slot + sp.toParams.δt ≤ X.slot := by
        have := (le_max_right _ _).trans hx₁
        rw [hXs]
        exact_mod_cast (SA.ts_le_iff sp).1 this
      have := crossing_of_rows hrun hs hpX hprop hpar hEPr hpH hEt hETh hEh
        (by rw [hpost]; exact heq.symm) hEs hdel
      rwa [hpost] at this
  refine ⟨hcross, hWX, fun y hy => ?_⟩
  -- universal acceptance before `t_x + Δ`
  rw [hpost] at hcross
  have hall := effAllowed_of_floor_lt hrun hnc hpX (hon (kX + 1) (by omega) (by omega)) hXt
    (by omega)
  have hgx : gbar g ≤ sp.ts x := by linarith
  obtain ⟨j, _x, hne, hcs, -⟩ := hrun.tick_of_awake y hy (sp.ts x + sp.Δ)
    (by linarith [gbar_nonneg g]) ⟨4 * (x : Int) + 1, by simp only [SAParams.ts]; ring⟩
    (hs.healthy.2.1 y hy _ (by change gbar g ≤ _; linarith))
  obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn ht hl
  have hkj : kX + 1 ≤ j := by
    by_contra hlt
    have := hrun.time_mono (show j ≤ kX by omega)
    linarith
  have hjjb : j < jb := hjb.lt_of_time_le hrun.time_mono (by rw [ht]; linarith)
  have hF := (hret sp ro proposer dg H tr g ΔF hrun hs hc (kX + 1) jb m c
    (fun k' h₁ h₂ => hon k' (by omega) h₂) _ hpX X hall y hy j hkj hjjb.le).1
  have hτg : max (tr.time kX) g = sp.ts x := by
    rw [hkX]; exact max_eq_left ((le_gbar g).trans hgx)
  obtain ⟨k, -, hak, hlt⟩ := hs.healthy.1.relay _ hpX kX X hacc
    (show g ≤ tr.time kX by rw [hkX]; exact (le_gbar g).trans hgx) y hy j ⟨_, hn, hl⟩
    (by rw [hτg, ht]; linarith [deadline_le_of_healthy hs hy j (sp.ts x) sp.Δ,
      max_eq_left hgx]) hF
  rw [hτg] at hlt
  exact ⟨k, hak, by linarith [deadline_le_of_healthy hs hy k (sp.ts x) sp.Δ, max_eq_left hgx]⟩

end Consensus.Goldilocks.Healing

end
