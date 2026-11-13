module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- Votes retain their honest emission provenance at the reading cut. -/
theorem goldilocks_ac_projection : GoldilocksACProjection := by
  intro sp ro dg H tr proposer h hnc
  have retained (i : Nat) := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer (h.upTo (h.time_nonneg i)) (hnc.upTo _)
  have call {y i ℓ} (hc : tr.projAC.CallAt y i ℓ) :
      (tr.upTo (tr.time i)).projAC.CallAt y i ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have emission {i v} (hv : ∃ j < i, ∃ e,
      SA.VoteAt (tr.upTo (tr.time i)).projAC v.val j e ∧ e.msg = v) :
      ∃ j < i, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
    obtain ⟨j, hj, e, he, hev⟩ := hv
    rw [RunTrace.upTo_projAC] at he
    exact ⟨j, hj, e, (SA.upTo_voteAt.mp he).2, hev⟩
  refine ⟨h.stock,
    ac_projection _ _ dg H _ tr proposer (Compose.requirements sp ro)
      (fun y _ => Compose.payloadFrom_initial (Compose.requirements sp ro) y) h.toLocalRun hnc,
    { pool_vote := fun y i σ hy v hv hval => ?_
      message_vote := fun y i ℓ v hy hc hm hv =>
        emission ((retained i).honest.message_vote y hy i ℓ v (call hc) hm hv)
      carried_vote := fun y i ℓ hy hc B hB v hv hval =>
        emission ((retained i).honest.carried_vote y hy i ℓ (call hc) B hB v hv hval)
      proposer := fun B hB hng => ?_
      one_block := fun y i ℓ B y' i' ℓ' B' hy hc hB hy' hc' hB' hp hprop hslot => ?_ }⟩
  · apply emission
    apply (retained i).honest.pool_vote y hy i σ v
    · simpa only [RunTrace.upTo_projAC,
        Trace.upTo_state tr.projAC y (i := i) (fun k hk => h.time_mono hk.le)] using hv
    · exact hval
  · obtain ⟨y, i, ℓ, hy, hc, hB⟩ := hB
    exact (retained i).honest.proposer B ⟨y, hy, i, ℓ, call hc, hB⟩ hng
  · -- Each reader retains its own prefix; only the proposer is retained at both horizons.
    have hpi := h.antitone (le_max_left _ _) hp
    have hpi' := h.antitone (le_max_right _ _) hp
    have frame_cases {y i ℓ B} (hy : y ∈ H (tr.time i))
        (hc : tr.projAC.CallAt y i ℓ) (hB : B ∈ ℓ.frame.tree) :
        B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
          ∃ k < i, tr.AcceptAt y k B := by
      have ht : B ∈ ((tr.upTo (tr.time i)).state y i).fg.tree := by
        rw [RunTrace.upTo_state_of_le h.time_mono le_rfl]
        rw [(h.cutLaw y i _ (Compose.projAC_callAt.mp hc) hy).1] at hB
        exact hB.1
      rcases Compose.tree_cases (h.upTo (h.time_nonneg i)).toLocalRun hy ht with hg | ⟨k, hk, ha⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k, hk, ((RunTrace.upTo_acceptAt _).mp ha).2⟩
    have own {y i ℓ B} (hy : y ∈ H (tr.time i)) (hc : tr.projAC.CallAt y i ℓ)
        (hB : B ∈ ℓ.frame.tree) (hp : B.proposer ∈ H (tr.time i))
        (hng : B ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) :
        ∃ j acc, tr.CallAt B.proposer j (.fg (.block B acc)) ∧
          ∃ j₀, tr.TickAt proposer dg B.proposer j₀ (sp.toParams.slotTime B.slot) ∧
            j = j₀ + 2 ∧ 0 < B.slot ∧ sp.toParams.slotTime B.slot ≤ tr.time i := by
      obtain ⟨k, hk, ha⟩ := (frame_cases hy hc hB).resolve_left hng
      have ha' := (RunTrace.upTo_acceptAt _).mpr ⟨h.time_mono hk.le, ha⟩
      obtain ⟨j, hjk, ⟨acc, hj⟩, hpos⟩ :=
        (h.upTo (h.time_nonneg i)).block_unforgeable y hy k B ⟨true, ha'⟩ hp
      rcases Compose.blockCall_cases (h.upTo (h.time_nonneg i)).toLocalRun hp hj with
        hg | ⟨j₀, x, rfl, ht, hP, d, p, _, hBdef, _⟩
      · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1) hpos
      · have hs : B.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hBdef]; rfl
        have htime : sp.toParams.slotTime B.slot = tr.time (j₀ + 2) := hs ▸ hP.2.1.symm
        refine ⟨j₀ + 2, acc, ((Trace.upTo_callAt _).mp hj).2, j₀, ?_, rfl, hs ▸ hP.1,
          htime ▸ (h.time_mono (hjk.trans hk.le))⟩
        have ht' := (RunTrace.upTo_tickAt h.time_mono).mp (show
          (tr.upTo (tr.time i)).TickAt proposer dg B.proposer j₀ (tr.time (j₀ + 2)) from ⟨x, ht⟩)
        rw [← htime] at ht'
        exact ht'.2
    by_cases hg : B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
    · by_cases hg' : B' = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
      · exact hg.trans hg'.symm
      · obtain ⟨_, _, _, _, _, _, hs, _⟩ := own hy' hc' hB' (hprop ▸ hpi') hg'
        simp only [hg, Params.genesisBlock] at hslot
        omega
    · obtain ⟨j, acc, hj, j₀, ht, hje, hs, htime⟩ := own hy hc hB hpi hg
      by_cases hg' : B' = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
      · simp only [hg', Params.genesisBlock] at hslot
        omega
      · obtain ⟨j', acc', hj', j₀', ht', hje', _, _⟩ := own hy' hc' hB' (hprop ▸ hpi') hg'
        have hpstart := h.antitone htime hpi
        rw [hslot] at hpstart
        rw [hprop, hslot] at ht
        have he := h.tick_unique B'.proposer j₀ j₀' _ (hprop ▸ hpstart) ht ht'
        rw [hje, he, ← hje', hprop] at hj
        exact (Cut.fg.inj (Option.some.inj (hj.2.symm.trans hj'.2)) |> FGLabel.block.inj).1

end Consensus.Goldilocks.Compose.Growing

end
