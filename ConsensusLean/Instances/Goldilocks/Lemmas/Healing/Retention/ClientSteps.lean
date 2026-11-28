module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance

public section

/-! # Goldilocks Healing: the honest client's attestations and the frame of a fast-lock write

Facts that the report service (`Outcome/Service`), its growing-fault sibling
(`Growing/Healing/RowService`) and the retention rows (`Retention/Rows`) share: the entry named by
a source's `T_h` (`source_entry`), what `create_attestation` signs (`createAtt_fields`) and when
it refuses (`FG.Record.createAtt_eq_none`), and the frame of a fast-lock write
(`fastLockAt_frame_mem`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

section Store

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- The block named by a source's `T_h` is held and is the entry of its own state. -/
theorem source_entry {st : Store P ACP} (hr : st.Reachable acp₀) (src : NodeBlock P ACP) :
    ∃ E ∈ st.tree, E.root = (st.σ src.root).Th ∧ (st.σ E.root).Th = E.root := by
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by rw [Store.σ_of_blocks_none hr hs]; rfl
    refine ⟨_, Store.genesis_mem hr, hg.symm, ?_⟩
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]; rfl
  · have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source P ACP acp₀ _ hr X hX
    rw [← hXr]
    exact ⟨E, hE, hEr, hET.trans hEr.symm⟩

end Store

/-- `create_attestation` signs `(h, T_h)` of its input with the record's finality pair and
records it; a timeout only on a recorded timeout or another target at that height. -/
theorem createAtt_fields {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ a.h = σe.h ∧ a.T = σe.Th ∧ a.fin = Λ.finalityPair σe ∧ Λ' = Λ.recordAtt a ∧
      (a.timeout = true → Λ.timeout σe.h ≠ ∅ ∨ ∃ T', Λ.target σe.h = some T' ∧ T' ≠ σe.Th) := by
  obtain ⟨hv, hrec, hh, hT, hfin, -, hne, -, ht⟩ := FG.Record.createAtt_some h
  refine ⟨hv, hh, hT, hfin, hrec, fun hτ => ?_⟩
  have hn : Λ.target a.h ≠ none := by simpa [hτ] using ht
  obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.1 hn
  exact Or.inr ⟨R, hh ▸ hR, fun e => hne ((e.trans hT.symm) ▸ hR)⟩

variable {sp : ACParams} {tr : GoldilocksTrace sp}

/-- The selection of a fast-lock write is in the frame of its call. -/
theorem fastLockAt_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (h : AC.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  rcases h with ⟨ℓ', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ℓ', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (AC.deepest_mem hD).1.1.1
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (AC.deepest_mem hsel).1.1

end Consensus.Goldilocks.Healing

end
