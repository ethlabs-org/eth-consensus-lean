module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
@[expose] public section

/-! # Implied statements: dropped bundle fields from the remaining ones

Two statements were dropped from `Challenge` bundles because the remaining fields imply them;
these theorems keep the derivations checked.

* C0.1 at the node (the former `Compose.ThreeTips`, stated inline): from `TipsNested` (C0.1 at
  the AC, in `ComposeInterfaceStatements`) and `ACStatesReachable` (in `ComposeNodeStatements`).
* `Store.FinalizedMonotone` (the `Σ` half of C0.2, formerly a field of `FGStoreLocalAt`): from
  `AcceptIsFrameStep` and `TreeGrows` (both fields of `FGStoreLocalAt`).
* H.4's former closed-form, (ii) and (iii) conjuncts (stated inline): from `AvailableHealing`,
  which now states (i) only, with `Healing.T_heal_eq`, `Healing.available_healing_windows` and
  `Healing.available_healing_all`. -/

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

namespace Consensus.Goldilocks.Healing.Test

open SA (SAParams ReplayOrder Payload gbar)

/-- **H.4 in the claims' form from `AvailableHealing`.** Every conjunct the statement used to
carry: the closed form of `T_heal`, (i), (ii) under `(U_B)` and (iii) under `(U_all)`. -/
theorem availableHealing_claims_form (h : AvailableHealing) :
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H proposer g Gp →
      ∀ a Tb, IsReset tr H g a → 0 ≤ Tb → BridgeAt tr H proposer g a Tb →
        T_heal sp g ΔF Gp Tb =
          gbar g + (104 * (sp.k : Time) + 628 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
            36 * Gp + Tb ∧
        (∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
          Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P) ∧
        (∀ B : Time,
          (∀ t, T_heal sp g ΔF Gp Tb ≤ t →
            ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧ sp.ts p ≤ t + B ∧
              HonestProposalRun tr H proposer p P ∧ Unanimous tr H p P) →
          ∀ t, T_heal sp g ΔF Gp Tb ≤ t →
            ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧ sp.ts p ≤ t + B ∧
              HonestProposalRun tr H proposer p P ∧ IncludedFrom tr H (t + B + 6 * sp.Δ) P) ∧
        ((∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
            Unanimous tr H p P) →
          ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
            IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P) := by
  intro sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a Tb ha hTb hb
  have hi := h sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a Tb ha hTb hb
  exact ⟨T_heal_eq sp g ΔF Gp Tb, hi, fun _ hB => available_healing_windows hi hB,
    available_healing_all hi⟩

end Consensus.Goldilocks.Healing.Test

end
