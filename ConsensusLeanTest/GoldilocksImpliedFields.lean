module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
@[expose] public section

/-! # Implied statements: dropped bundle fields from the remaining ones

Two statements were dropped from `Challenge` bundles because the remaining fields imply them;
these theorems keep the derivations checked.

* C0.1 at the node (the former `Compose.ThreeTips`, stated inline): from `TipsNested` (C0.1 at
  the AC, in `ComposeInterfaceStatements`) and `ACStatesReachable` (in `ComposeNodeStatements`).
* `Store.FinalizedMonotone` (the `Σ` half of C0.2, formerly a field of `FGStoreLocalAt`): from
  `AcceptIsFrameStep` and `TreeGrows` (both fields of `FGStoreLocalAt`). -/

namespace Consensus.Goldilocks.Compose.Test

open Node

/-- **C0.1 at the node from the remaining fields.** At a reachable configuration of an honest
node and any time not before its clock, with `Φ = fg_to_ac(Σ)`: `ac_confirmed` and `ac_head` are
blocks of `Φ.tree` and `Σ.F ⪯ ac_confirmed ⪯ ac_head` inside `Φ.tree`. -/
theorem threeTips_of_fields {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (hT : TipsNested A) (hR : ACStatesReachable proposer dg self) :
    A.Requirements → ∀ cfg : Config A, Reachable proposer dg self cfg → ∀ t, cfg.time ≤ t →
      A.confirmed cfg.st.ac (frame cfg.st) t ∈ (frame cfg.st).tree ∧
      A.head cfg.st.ac (frame cfg.st) t ∈ (frame cfg.st).tree ∧
      (frame cfg.st).Anc cfg.st.fg.F (A.confirmed cfg.st.ac (frame cfg.st) t) ∧
      (frame cfg.st).Anc (A.confirmed cfg.st.ac (frame cfg.st) t)
        (A.head cfg.st.ac (frame cfg.st) t) := by
  intro hq cfg h t ht
  obtain ⟨hc, t₀, ht₀, hRa⟩ := hR hq cfg h
  exact hT hq.outputs self _ hc _ _ t₀ hRa t (ht₀.trans ht)

end Consensus.Goldilocks.Compose.Test

namespace Consensus.Goldilocks.Store.Test

/-- **The `Σ` half of C0.2 from the remaining `FGStoreLocalAt` fields.** -/
theorem finalizedMonotone_of_fields (P : Params) (ACP : Type)
    (hstep : AcceptIsFrameStep P ACP) (hgrow : TreeGrows P ACP) : FinalizedMonotone P ACP := by
  rw [finalizedMonotone_iff]
  intro acp₀ st hr
  refine ⟨fun B st' h => ?_, fun a => ?_⟩
  · have hF := ((hstep acp₀ st hr).1 B st' h).F_anc_F'
    change Goldilocks.Anc st'.tree st.F st'.F
    rw [(hgrow acp₀ st hr).1 B st' h]
    exact hF.mono (Set.insert_subset_insert fun _ hx => hx.1)
  · exact congrArg Frame.F ((hstep acp₀ st hr).2 a)

end Consensus.Goldilocks.Store.Test

end
