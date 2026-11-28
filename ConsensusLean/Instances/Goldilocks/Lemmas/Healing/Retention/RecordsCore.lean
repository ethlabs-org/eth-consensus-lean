module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.ClientEquivalence
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Entry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store

public section

/-! # Client-record provenance over any node run

The client record starts empty and changes only by recording an attestation the node signs.
These facts use no retention premise or Goldilocks AC operation.
-/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
  {tr : RunTrace A} {ini : Fin P.n → A.State} {y : Fin P.n}

/-- Creating an attestation records precisely that attestation. -/
private theorem createAtt_record {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
    {σe : FG.ChainState n} {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    Λ' = Λ.recordAtt a := by
  exact (FG.Record.createAtt_some h).2.1

/-- An honest record changes only by recording an attestation signed at that cut. -/
theorem record_step_from (hrun : LocalRun proposer dg H sg tr ini) (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ att, tr.SignAt y i att ∧
        (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt att := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    have hsucc := tr.state_succ_of_call hc
    cases c with
    | ac ℓ => exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
    | fg ℓ =>
      rcases ℓ with ⟨B, _ | _⟩ | a' | ⟨C, _ | a'⟩
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2)
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ createAtt_record hlaw.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- The compact client record at every honest cut is the projection of a reachable old record. -/
theorem client_record_legacy_reachable (hrun : LocalRun proposer dg H sg tr ini) (hy : y ∈ H) :
    ∀ i, ∃ sent, FG.LegacyClient.Reachable (tr.state y i).record sent
  | 0 => by
    rw [Trace.state, hrun.init y hy]
    exact ⟨[], FG.LegacyClient.Reachable.empty⟩
  | i + 1 => by
    obtain ⟨sent, hr⟩ := client_record_legacy_reachable hrun hy i
    rcases record_step_from hrun hy i with he | ⟨a, ⟨src, hc⟩, _⟩
    · exact ⟨sent, he ▸ hr⟩
    · have hs := (hrun.cutLaw y hy i _ hc).1
      rw [← tr.state_succ_of_call hc] at hs
      change (tr.state y i).record.createAtt y ((tr.state y i).fg.σ
        ((tr.state y i).fg.σ src.root).Th) = some (a, (tr.state y (i + 1)).record) at hs
      exact ⟨sent ++ [a.content], hr.sign ((FG.LegacyClient.createAtt_some_iff hr y _ a).2
        ⟨hs, rfl⟩)⟩

/-- Target, timeout and lock records have their actual earlier signing witnesses. -/
theorem client_record_origin_from (hrun : LocalRun proposer dg H sg tr ini) (hy : y ∈ H)
    (h r : Nat) : ∀ i,
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r))
  | 0 => by
    rw [Trace.state, hrun.init y hy]
    refine ⟨fun hx => ?_, fun hx => ?_⟩ <;>
      simp [Node.initWith, FG.Record.empty] at hx
  | i + 1 => by
    obtain ⟨ih₁, ih₂⟩ := client_record_origin_from hrun hy h r i
    rcases record_step_from hrun hy i with he | ⟨a', hs, he⟩ <;> rw [he]
    · exact ⟨fun hx => let ⟨k, hk, att, h'⟩ := ih₁ hx; ⟨k, by omega, att, h'⟩,
        fun hx => let ⟨k, hk, att, h'⟩ := ih₂ hx; ⟨k, by omega, att, h'⟩⟩
    · refine ⟨fun hx => ?_, fun hx => ?_⟩
      · have key : (tr.state y i).record.target h = some r ∨
            r ∈ (tr.state y i).record.timeout h ∨ (a'.h = h ∧ a'.T = r) := by
          rcases hx with hx | hx
          · dsimp only [FG.Record.recordAtt] at hx
            split_ifs at hx
            · rw [Function.update_apply] at hx
              split_ifs at hx with hh
              · exact Or.inr (Or.inr ⟨hh.symm, Option.some.inj hx⟩)
              · exact Or.inl hx
            · exact Or.inl hx
          · dsimp only [FG.Record.recordAtt] at hx
            split_ifs at hx
            · rw [Function.update_apply] at hx
              split_ifs at hx with hh
              · rcases Finset.mem_insert.1 hx with rfl | hx
                · exact Or.inr (Or.inr ⟨hh.symm, rfl⟩)
                · exact Or.inr (Or.inl (by rw [hh]; exact hx))
              · exact Or.inr (Or.inl hx)
            · exact Or.inr (Or.inl hx)
        rcases key with hx | hx | ⟨h₁, h₂⟩
        · obtain ⟨k, hk, att, h'⟩ := ih₁ (Or.inl hx)
          exact ⟨k, by omega, att, h'⟩
        · obtain ⟨k, hk, att, h'⟩ := ih₁ (Or.inr hx)
          exact ⟨k, by omega, att, h'⟩
        · exact ⟨i, by omega, a', hs, h₁, h₂⟩
      · dsimp only [FG.Record.recordAtt] at hx
        rcases hf : a'.fin with _ | ⟨p₁, p₂⟩
        · rw [hf] at hx
          dsimp only at hx
          obtain ⟨k, hk, att, h'⟩ := ih₂ hx
          exact ⟨k, by omega, att, h'⟩
        · rw [hf] at hx
          dsimp only at hx
          rw [Function.update_apply] at hx
          split_ifs at hx with hh
          · cases Option.some.inj hx
            exact ⟨i, by omega, a', hs, by rw [hf, hh]⟩
          · obtain ⟨k, hk, att, h'⟩ := ih₂ hx
            exact ⟨k, by omega, att, h'⟩

/-- An honest signature is well formed at its signing cut. -/
theorem signAt_wellFormed_from (hrun : LocalRun proposer dg H sg tr ini) (hy : y ∈ H) {k : Nat}
    {att : FG.Att P.n} (hs : tr.SignAt y k att) : att.WellFormed := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  have hr := Compose.fg_reachable hrun hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  rcases hsrc : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = P.genesisRoot := by
      rw [Store.σ_of_blocks_none hr hsrc]; rfl
    rw [hg, Store.σ_genesis hr] at hcl
    exact Compose.createAtt_wellFormed le_rfl Nat.one_pos (by simp [FG.ChainState.init]) hcl
  · have hXr := Goldilocks.Store.Reachable.blocks_root hr hsrc
    have hX : X ∈ (tr.state y k).fg.tree := by
      change (tr.state y k).fg.blocks X.root = some X
      rw [hXr]; exact hsrc
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
    obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr E hE
    obtain ⟨h1, -, h3, -, -, -, -, h8, -⟩ := FG.chain_invariants P.fg _ _ hcs
    rw [hXr] at hEr
    rw [← hEr] at hcl
    exact Compose.createAtt_wellFormed h1 h3 (fun p hp => lt_of_le_of_lt (h8 p hp).2 h3) hcl

end Consensus.Goldilocks.Healing

end
