module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RowsSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedUpTo

public section

/-! # Goldilocks Refinement: the supply of first rows through a finite horizon (#137)

consensus-lean#137 (finite-horizon port). `rows_supply`, `rows_supply_of_reports`,
`rows_supply_or_crossed` and `rows_supply_or_crossed_after` from `HealedRecordsUpTo … b`. The
rows are signed by `v ≤ b`, so C2*⁺ (i) through the horizon names their entries. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The rows supply through the horizon** (`rows_supply` from `HealedRecordsUpTo … b`, rows
signed by `v ≤ b`). -/
theorem rows_supply_upTo (hrun : GoldilocksRun proposer dg H tr) {gR b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
    {h T : Nat} (hh₀ : h₀ ≤ h) (hT : (E h).root = T) (hqH : sp.toParams.fg.q ≤ H.ncard)
    {v : Time} (hvb : v ≤ b)
    (hrow : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h) :
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
    rw [hR.rows y hyH k₀ a₀ hs₀ (hk₀.trans hvb) (hh ▸ hh₀), hh, hT]

/-- **The rows supply from same-height reports, through the horizon**
(`rows_supply_of_reports` from `HealedRecordsUpTo … b`). -/
theorem rows_supply_of_reports_upTo {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
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
  obtain ⟨j, att, hs, hjr, -, hah, hroot, -⟩ :=
    hp.row_of_report hy hr (hrv.trans hvb) hy hTm hσ hTe hhT hhj hTC hCh
  have hET : (E σT.h).root = T.root := by
    rw [← hroot, hR.rows y hy j att hs (hjr.trans (hrv.trans hvb)) (hah ▸ hh₀), hah]
  refine rows_supply_upTo hp.run hR hh₀ hET (q_le_ncard_of_faults hp.faults) hvb fun z hz => ?_
  obtain ⟨r, ell, C, hr, hrv, hTC, hCh⟩ := hreports z hz
  obtain ⟨j, att, hs, ht, -, hah, -⟩ :=
    hp.row_of_report hz hr (hrv.trans hvb) hy hTm hσ hTe hhT hhj hTC hCh
  exact ⟨j, att, hs, ht.trans hrv, hah⟩

/-- **The rows supply or a crossing, through the horizon** (`rows_supply_or_crossed` from
`HealedRecordsUpTo … b`). -/
theorem rows_supply_or_crossed_upTo {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
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
  · exact Or.inr (rows_supply_of_reports_upTo hp hR hy hTm hσ hTe hhT hhj hh₀ hvb hB)

/-- **The rows supply or a crossing, after `u`, through the horizon**
(`rows_supply_or_crossed_after` from `HealedRecordsUpTo … b`). -/
theorem rows_supply_or_crossed_after_upTo {g ΔF a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {gR : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {m : Nat}
    (hTm : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : Healing.HZ tr H g + 1 ≤ σT.h) (hhj : σT.bound → Healing.HZ tr H g + 1 ≤ σT.hj)
    (hh₀ : h₀ ≤ σT.h) {u v : Time} (hvb : v ≤ b)
    (hreports' : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ u ≤ tr.time r ∧
      tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) T C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ u ≤ tr.time r ∧ tr.time r ≤ v ∧
      Anc (tr.HonestBlocks H) T C ∧ C ∈ (tr.state z r).fg.tree ∧
      σT.h < ((tr.state z r).fg.σ C.root).h) ∨
    ∃ S : Finset (Fin sp.n), (∀ y ∈ S, y ∈ H) ∧ sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = σT.h ∧
        att.T = T.root ∧ ∀ k' < k, ∀ att', tr.SignAt y k' att' → att'.h ≠ σT.h := by
  rcases reports_same_height_or_crossed_after hp hy hTm hσ hreports' with hA | hB
  · exact Or.inl hA
  · exact Or.inr (rows_supply_of_reports_upTo hp hR hy hTm hσ hTe hhT hhj hh₀ hvb hB)

end Consensus.Goldilocks.Refinement

end
