module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ExposureHealed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service

public section

/-! # Goldilocks Refinement: the supply of first rows for the lock window (L5.4, WI-18)

`window_justifies_of_lock_healed` asks for `S`, `q ≤ |S|` and `hsig`: each `y ∈ S` signs by `v`
a row at `(h, T)` that is its first own row at height `h`.

* `first_row_of_sign`: a row at height `h` by `v` gives a first own row at `h` by `v`
  (`Nat.find` over the cuts).
* `rows_supply`: under `HealedRecords` (`h₀ ≤ h`, `T = (E h).root`) and `q ≤ |H|`, a row at
  height `h` by `v` from each honest node gives `S`, `hS` and `hsig`.
* `q_le_ncard_of_faults`: `3 |Hᶜ| ≤ n − 1` gives `q ≤ |H|`.
* `rows_supply_of_reports`: under `ResetPremisesUpTo` and `HealedRecords`, a same-height report
  `C ⪰ T` from each honest node by `v ≤ b` (`ResetPremisesUpTo.row_of_report`) gives `S`, `hS`
  and `hsig` at `(σT.h, T.root)`. The per-node reports stay a premise: no Lean lemma yet gives a
  report at the entry height (`report_of_viable_unanimous_pool` gives `P ⪯ R`, no height).
* `reports_same_height_or_crossed`, `rows_supply_or_crossed`: from reports `C ⪰ T` of any
  height, either some honest report crosses `σT.h` or the same-height supply holds. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A first own row at a height.** If `y` signs `att` at cut `k` with `time k ≤ v`, then `y`
signs at some cut `k₀` (the least cut with a row of height `att.h`) a row `att₀` with
`att₀.h = att.h`, `time k₀ ≤ v`, and no row of height `att.h` before `k₀`. -/
theorem first_row_of_sign (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} {k : Nat}
    {att : FG.Att sp.n} {v : Time} (hs : tr.SignAt y k att) (hkv : tr.time k ≤ v) :
    ∃ k₀ att₀, tr.SignAt y k₀ att₀ ∧ tr.time k₀ ≤ v ∧ att₀.h = att.h ∧
      ∀ k' < k₀, ∀ att', tr.SignAt y k' att' → att'.h ≠ att.h := by
  classical
  have hex : ∃ k, ∃ a : FG.Att sp.n, tr.SignAt y k a ∧ a.h = att.h := ⟨k, att, hs, rfl⟩
  obtain ⟨a₀, hs₀, hh₀⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, a₀, hs₀, ?_, hh₀, fun k' hk' a' hs' hh' => ?_⟩
  · exact (hrun.time_mono (Nat.find_min' hex ⟨att, hs, rfl⟩)).trans hkv
  · exact Nat.find_min hex hk' ⟨a', hs', hh'⟩

/-- **The rows supply of `window_justifies_of_lock_healed`.** Under `HealedRecords` with
`h₀ ≤ h`, `(E h).root = T` and `q ≤ |H|`: if each honest node signs a row of height `h` by `v`,
then the honest nodes form `S` with `q ≤ |S|`, and each `y ∈ S` signs by `v` a row at `(h, T)`
that is its first own row at height `h`. -/
theorem rows_supply (hrun : GoldilocksRun proposer dg H tr) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {h T : Nat} (hh₀ : h₀ ≤ h) (hT : (E h).root = T) (hqH : sp.toParams.fg.q ≤ H.ncard)
    {v : Time} (hrow : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h) :
    ∃ S : Finset (Fin sp.n), (∀ y ∈ S, y ∈ H) ∧ sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = T ∧
        ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ h := by
  classical
  refine ⟨Finset.univ.filter (· ∈ H), fun y hy => (Finset.mem_filter.1 hy).2, ?_, ?_⟩
  · have hcard : (Finset.univ.filter (· ∈ H)).card = H.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [hcard]
    exact hqH
  · intro y hy
    have hyH := (Finset.mem_filter.1 hy).2
    obtain ⟨k, att, hs, hkv, hah⟩ := hrow y hyH
    obtain ⟨k₀, a₀, hs₀, hk₀, hh, hmin⟩ := first_row_of_sign hrun hs hkv
    rw [hah] at hh hmin
    refine ⟨k₀, a₀, hs₀, hk₀, hh, ?_, hmin⟩
    rw [hR.rows y hyH k₀ a₀ hs₀ (hh ▸ hh₀), hh, hT]

/-- **The fault bound gives an honest quorum.** `3 |Hᶜ| ≤ n − 1` gives `q ≤ |H|`. -/
theorem q_le_ncard_of_faults (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) : sp.toParams.fg.q ≤ H.ncard := by
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  change (2 * sp.n + 2) / 3 ≤ _
  omega

/-- **The rows supply from same-height reports.** Under `ResetPremisesUpTo` (horizon `b`) and
`HealedRecords` with `h₀ ≤ σT.h`, for a held `T` with `σ[T] = σT`, `σT.T_h = T`,
`H_z + 1 ≤ σT.h` and (when bound) `H_z + 1 ≤ σT.h_j`: if each honest `z` reports by `v ≤ b` a
`C ⪰ T` whose state has height `σT.h`, then `S`, `q ≤ |S|` and the first rows at
`(σT.h, T.root)` by `v` of `rows_supply` hold. -/
theorem rows_supply_of_reports {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {m : Nat}
    (hTm : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : Healing.HZ tr H g + 1 ≤ σT.h) (hhj : σT.bound → Healing.HZ tr H g + 1 ≤ σT.hj)
    (hh₀ : h₀ ≤ σT.h) {v : Time} (hvb : v ≤ b)
    (hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ S : Finset (Fin sp.n), (∀ y ∈ S, y ∈ H) ∧ sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = σT.h ∧
        att.T = T.root ∧ ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ σT.h := by
  obtain ⟨r, ell, C, hr, hrv, hTC, hCh⟩ := hreports y hy
  obtain ⟨j, att, hs, -, -, hah, hroot, -⟩ :=
    hp.row_of_report hy hr (hrv.trans hvb) hy hTm hσ hTe hhT hhj hTC hCh
  have hET : (E σT.h).root = T.root := by
    rw [← hroot, hR.rows y hy j att hs (hah ▸ hh₀), hah]
  refine rows_supply hp.run hR hh₀ hET (q_le_ncard_of_faults hp.faults) fun z hz => ?_
  obtain ⟨r, ell, C, hr, hrv, hTC, hCh⟩ := hreports z hz
  obtain ⟨j, att, hs, ht, -, hah, -⟩ :=
    hp.row_of_report hz hr (hrv.trans hvb) hy hTm hσ hTe hhT hhj hTC hCh
  exact ⟨j, att, hs, ht.trans hrv, hah⟩

/-- **Same height or crossed** (the case split of "either `J` is revealed or we advance").
Under `ResetPremisesUpTo`, for a held `T` with `σ[T] = σT`: if each honest `z` reports by `v` a
`C ⪰ T`, then either (A) some honest `z` reports by `v` a `C ⪰ T`, held by `z`, whose state
height is above `σT.h` (height `σT.h` is crossed on `T`'s chain), or (B) each honest `z` reports
by `v` a `C ⪰ T` whose state height is `σT.h` (heights do not decrease along ancestry). -/
theorem reports_same_height_or_crossed {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {m : Nat}
    (hTm : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) {v : Time}
    (hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ C ∈ (tr.state z r).fg.tree ∧
      σT.h < ((tr.state z r).fg.σ C.root).h) ∨
    (∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) := by
  classical
  by_cases hA : ∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ C ∈ (tr.state z r).fg.tree ∧
      σT.h < ((tr.state z r).fg.σ C.root).h
  · exact Or.inl hA
  · refine Or.inr fun z hz => ?_
    obtain ⟨r, ell, C, hrep, hrv, hTC⟩ := hreports z hz
    have hCt := Healing.toFG_mem_tree hp.run hz hrep
    have hTt := hp.mem_tree_of_anc hz hTC hCt
    have hσT := Healing.σ_eq_honest hp.run hp.noColl hz hy hTt hTm
    have hle := Healing.σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (Healing.store_anc_of_honest_anc hp.run hp.noColl hz hTC hCt)
    rw [hσT, hσ] at hle
    refine ⟨r, ell, C, hrep, hrv, hTC, ?_⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd ⟨z, hz, r, ell, C, hrep, hrv, hTC, hCt, hlt⟩ hA
    · exact heq.symm

/-- **The rows supply or a crossing** (`rows_supply_of_reports` with the same-height premise
dropped, via `reports_same_height_or_crossed`). Same premises as `rows_supply_of_reports`, but
each honest `z` only reports by `v` some `C ⪰ T`: then some honest `z` holds and reports by `v`
a `C ⪰ T` with state height above `σT.h`, or `S`, `q ≤ |S|` and the first rows at
`(σT.h, T.root)` by `v` hold. -/
theorem rows_supply_or_crossed {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecords tr H gR h₀ E)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {m : Nat}
    (hTm : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : Healing.HZ tr H g + 1 ≤ σT.h) (hhj : σT.bound → Healing.HZ tr H g + 1 ≤ σT.hj)
    (hh₀ : h₀ ≤ σT.h) {v : Time} (hvb : v ≤ b)
    (hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ C ∈ (tr.state z r).fg.tree ∧
      σT.h < ((tr.state z r).fg.σ C.root).h) ∨
    ∃ S : Finset (Fin sp.n), (∀ y ∈ S, y ∈ H) ∧ sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = σT.h ∧
        att.T = T.root ∧ ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ σT.h := by
  rcases reports_same_height_or_crossed hp hy hTm hσ hreports with hA | hB
  · exact Or.inl hA
  · exact Or.inr (rows_supply_of_reports hp hR hy hTm hσ hTe hhT hhj hh₀ hvb hB)

end Consensus.Goldilocks.Refinement

end
