module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance

public section

/-! # Goldilocks Healing: the honest client's attestations and the frame of a fast-lock write

Facts that the report service (`Outcome/Service`), its growing-fault sibling
(`Growing/Healing/RowService`) and the retention rows (`Retention/Rows`) share: the entry named by
a source's `T_h` (`source_entry`), what `create_attestation` signs (`createAtt_fields`) and when
it refuses (`createAtt_refused`), and the frame of a fast-lock write (`fastLockAt_frame_mem`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

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
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · cases h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := Store.heightPair_eq hp
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hτ => ?_⟩
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  · exact Or.inl h2
  · simp_all
  · push Not at h3
    obtain ⟨T'', hT''⟩ := Option.ne_none_iff_exists'.1 h3.1
    exact Or.inr ⟨T'', hT'', fun e => h3.2 (hT''.trans (by rw [e]))⟩

/-- `create_attestation` signs nothing only on a lock of another root at the input's height, or
a content of that height already sent. -/
theorem createAtt_refused {n : Nat} {Λ : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    (h : Λ.createAtt v σe = none) :
    (Λ.lock σe.h ≠ none ∧ Λ.lock σe.h ≠ some σe.Th) ∨ ∃ b ∈ Λ.sent, b.1 = σe.h := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · unfold FG.Record.heightPair at hp
    split_ifs at hp with h1
    exact Or.inl h1
  · obtain ⟨rfl, -⟩ := Store.heightPair_eq hp
    dsimp only at h
    split_ifs at h with hany
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 hany
    exact Or.inr ⟨b, hb, (of_decide_eq_true hb').1⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}

/-- The selection of a fast-lock write is in the frame of its call. -/
theorem fastLockAt_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (h : SA.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  rcases h with ⟨ℓ', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ℓ', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (SA.deepest_mem hD).1.1.1
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.deepest_mem hsel).1.1

end Consensus.Goldilocks.Healing

end
