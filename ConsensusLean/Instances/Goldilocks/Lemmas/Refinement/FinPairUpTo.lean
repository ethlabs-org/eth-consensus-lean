module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPair
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedClientUpTo

public section

/-! # Goldilocks Refinement: the finality pair of an entry state through a horizon (#137)

consensus-lean#137 (finite-horizon port). `J_eq_entry_of_healed` and
`finalityPair_entry_healed'` from `HealedRecordsUpTo … b`. The held state `σ_p[Pr]` is at a cut
`k'` with `t_{k'} ≤ b`: its target quorum row is signed before the acceptance of the carrying
block, so before `k'`. The record is read at a cut `i` with `t_i ≤ b`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The justification of a held honest state is the entry, through the horizon.**
`J_eq_entry_of_healed` from `HealedRecordsUpTo … b`, for a state held at a cut by `b`. -/
theorem J_eq_entry_of_healed_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q) {gR b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree) (hkb : tr.time k' ≤ b)
    (hj₀ : h₀ ≤ ((tr.state p k').fg.σ Pr.root).hj) (hj1 : 1 ≤ ((tr.state p k').fg.σ Pr.root).hj) :
    ((tr.state p k').fg.σ Pr.root).J = (E ((tr.state p k').fg.σ Pr.root).hj).root := by
  obtain ⟨c, hcT, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hp k') Pr hPr
  obtain ⟨Q, hQ, hQv⟩ := (FG.FGParams.justified_evidence _ hc).2 hj1
  have hv : ∃ v ∈ Q, v ∈ H := by
    by_contra hn
    push Not at hn
    have := Set.ncard_le_ncard (s := (Q : Set (Fin sp.toParams.fg.n))) (t := Hᶜ) hn
      (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    exact lt_irrefl _ (lt_of_lt_of_le hq (hQ.trans this))
  obtain ⟨v, hvQ, hvH⟩ := hv
  obtain ⟨a, ha, rfl, hah, haT, -⟩ := hQv v hvQ
  obtain ⟨B, hB, ha⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hB
  change a ∈ X.fgPayload at ha
  rcases Healing.tree_accepted hrun.toLocalRun hp (hcT X hX) with hg | ⟨i', hi', hA⟩
  · rw [hg] at ha
    cases ha
  obtain ⟨d, hdi, hsd⟩ := hrun.att_unforgeable p hp i' a (Or.inr ⟨X, ⟨true, hA⟩, ha⟩) hvH
  have hdb : tr.time d ≤ b := (hrun.time_mono (hdi.trans hi').le).trans hkb
  rw [← haT, hR.rows _ hvH d a hsd hdb (hah ▸ hj₀), hah]

/-- **The fin-pair link through the horizon** (`finalityPair_entry_healed'` from
`HealedRecordsUpTo … b`): the held state at a cut `k'` by `b`, the record at a cut `i` by `b`. -/
theorem finalityPair_entry_healed'_upTo (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hq : Hᶜ.ncard < sp.toParams.fg.q) {gR b : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hR : Healing.HealedRecordsUpTo tr H gR b h₀ E)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state y k).fg.tree)
    {p : Fin sp.n} (hp : p ∈ H) {k' : Nat} {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPr : Pr ∈ (tr.state p k').fg.tree) (hk'b : tr.time k' ≤ b)
    (hT : ((tr.state p k').fg.σ Pr.root).Th =
      ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)
    (hb : ((tr.state p k').fg.σ Pr.root).bound)
    (hj₀ : h₀ ≤ ((tr.state p k').fg.σ Pr.root).hj) (hj1 : 1 ≤ ((tr.state p k').fg.σ Pr.root).hj)
    {i : Nat} (hib : tr.time i ≤ b) :
    (tr.state y i).record.finalityPair ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th) =
      some (((tr.state p k').fg.σ Pr.root).hj, ((tr.state p k').fg.σ Pr.root).J) := by
  refine (finalityPair_entry_iff hrun hnc hy hC hp hPr hT hb _).2 ?_
  rw [J_eq_entry_of_healed_upTo hrun hq hR hp hPr hk'b hj₀ hj1]
  exact hR.permits_entry hrun hy hib _ hj₀

end Consensus.Goldilocks.Refinement

end
