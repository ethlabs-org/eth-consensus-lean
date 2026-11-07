module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Components

public section

/-! # FG execution and signing provenance before compromise

Only node-local execution is retained here. In particular, no invariant requiring an honest
origin is reconstructed for the terminal honest set.
-/

namespace Consensus.Goldilocks.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- The validators still honest at `d` execute the static FG in the retained prefix. -/
theorem FGLocalRun.exec_upTo (hr : FGLocalRun acp₀ H U tr) {d : Time} (hd : 0 ≤ d) :
    Store.FGExec acp₀ (H d) (tr.upTo d) :=
  (hr.upTo hd).toExec

/-- A store read while its node is honest is reachable from the initial FG store. -/
theorem FGLocalRun.store_reachable (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) : (tr.store y i).Reachable acp₀ := by
  have h := Store.store_reachable_of_exec (hr.exec_upTo (hr.time_nonneg i)) hy i
  simpa only [FGTrace.store, Trace.upTo_state tr y
    (fun k hk => hr.time_mono hk.le)] using h

/-- A block held while honest is genesis or was accepted earlier by that same node. -/
theorem FGLocalRun.tree_accepted (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    B = P.genesisBlock acp₀ ∨ ∃ k < i, tr.AcceptAt y k B := by
  have hs := Trace.upTo_state tr y (i := i) (fun k hk => hr.time_mono hk.le)
  have hB' : B ∈ (FGTrace.store (tr.upTo (tr.time i)) y i).tree := by
    simpa only [FGTrace.store, hs] using hB
  rcases Store.tree_accepted (hr.upTo (hr.time_nonneg i)) hy hB' with h | ⟨k, hk, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk, ((Trace.upTo_callAt tr).mp hc).2⟩

/-- All signatures before a cut bounded by `d`, by a validator honest at `d`, belong to
one serialized client run. No honesty after `d` is required. -/
theorem FGLocalRun.signed_run (hr : FGLocalRun acp₀ H U tr) {d : Time} (hd : 0 ≤ d)
    {v : Fin P.n} (hv : v ∈ H d) (i : Nat) (hi : ∀ k < i, tr.time k ≤ d) :
    ∃ inputs, FG.EntryInputs P.fg inputs ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 := by
  obtain ⟨inputs, hin, hs⟩ := Store.signed_run_of_exec (hr.exec_upTo hd) hv i
  refine ⟨inputs, hin, fun j hj a ha => hs j hj a ?_⟩
  obtain ⟨src, hc⟩ := ha
  exact ⟨src, (Trace.upTo_callAt tr).mpr ⟨hi j hj, hc⟩⟩

/-- Two signatures made before compromise cannot constitute a slashable pair. -/
theorem FGLocalRun.non_framing (hr : FGLocalRun acp₀ H U tr) {v : Fin P.n}
    {i j : Nat} {a b : FG.Att P.n} (ha : tr.SignAt v i a) (hb : tr.SignAt v j b)
    (hv : v ∈ H (max (tr.time i) (tr.time j))) : ¬ FG.slashable a b := by
  obtain ⟨inputs, hin, hs⟩ := hr.signed_run
    ((hr.time_nonneg i).trans (le_max_left _ _)) hv (max i j + 1) (fun k hk => by
      have hki : k ≤ max i j := Nat.lt_succ_iff.mp hk
      rcases le_total i j with hij | hji
      · exact (hr.time_mono (hki.trans (max_le hij le_rfl))).trans (le_max_right _ _)
      · exact (hr.time_mono (hki.trans (max_le le_rfl hji))).trans (le_max_left _ _))
  exact FG.client_safety P.fg v inputs hin a
    (hs i (Nat.lt_succ_of_le (le_max_left _ _)) a ha) b
    (hs j (Nat.lt_succ_of_le (le_max_right _ _)) b hb)

end Consensus.Goldilocks.Growing

end
