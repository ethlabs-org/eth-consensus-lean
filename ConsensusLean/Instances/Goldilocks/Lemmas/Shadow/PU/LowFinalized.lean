module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Origins
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # P-U shadow: a low finalized block is below every bounded high origin

Copies of `Growing.FGLocalRun.finalized_anc_of_lt_at` (G1.2 at strict height under growing faults)
and `ResetPremisesUpTo.low_finalized_below_origin_at` (`Clean/LowFinalized`) over the shadow run.
They read no viability. The store side is the `_with` lemmas of `Shadow/PU/Cache`; the signing
side is the shadow client safety `held_atts_safe_at'` (`Shadow/PU/Safety`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- A linked chain from `A` lies below its last block. -/
private theorem anc_of_linked {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))} :
    ∀ (c : List (AC.Blk sp.n (List (FG.Att sp.n)))) (A : AC.Blk sp.n (List (FG.Att sp.n))),
      A ∈ S → (∀ X ∈ c, X ∈ S) →
      c.map Block.parent = ((A.root :: c.map Block.root).take c.length).map some →
      ∀ B, (A :: c).getLast? = some B → ∀ X ∈ A :: c, Goldilocks.Anc S X B
  | [], A, _, _, _, B, hB, X, hX => by
    simp only [List.getLast?_singleton, Option.some.injEq, List.mem_singleton] at hB hX
    exact hX ▸ hB ▸ .refl
  | C :: c, A, hA, hc, hl, B, hB, X, hX => by
    simp only [List.map_cons, List.length_cons, List.take_succ_cons, List.cons.injEq] at hl
    rw [List.getLast?_cons_cons] at hB
    have ih := anc_of_linked c C (hc C List.mem_cons_self)
      (fun X hX => hc X (List.mem_cons_of_mem _ hX)) hl.2 B hB
    rcases List.mem_cons.1 hX with rfl | hX
    · exact .head ⟨hA, hc C List.mem_cons_self, hl.1⟩ (ih C List.mem_cons_self)
    · exact ih X hX

/-- An attestation of a chain of held blocks is in the payload of a held block. -/
private theorem chainAtts_held {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    {c : List (AC.Blk sp.n (List (FG.Att sp.n)))} (hc : ∀ X ∈ c, X ∈ S) {a : FG.Att sp.n}
    (ha : a ∈ sp.toParams.fg.chainAtts (c.map Block.fgView)) :
    ∃ Y ∈ S, a ∈ Y.fgPayload := by
  obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
  exact ⟨X, hc X hXc, haX⟩

/-- **G1.2 at strict height over the shadow run** (`Growing.FGLocalRun.finalized_anc_of_lt_at`):
a block finalized by the state of a held `X` of a reader honest at `t` is an ancestor of every
block held by a reader honest at `u` above the finalized height, when fewer than `2q − n`
validators are faulty at `max t u`. -/
theorem finalized_anc_of_lt_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {k m : Nat} {t u : Time}
    (ht : 0 ≤ t) (hk : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hm : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u)
    (hH : (H (max t u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n)
    {X F W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hF : F ∈ (tr.state y k).fg.tree)
    (hFr : F.root = ((tr.state y k).fg.σ X.root).F) (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Goldilocks.Anc (tr.HonestBlocksAt H) F W := by
  have hfs := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hR₁ := (Compose.Growing.reachable_at hrun ht hy hk).reachableWith
  have hR₂ := (Compose.Growing.reachable_at hrun hu hz hm).reachableWith
  have hsub₁ := Compose.Growing.tree_held_at ht hy hk
  have hsub₂ := Compose.Growing.tree_held_at hu hz hm
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  obtain ⟨c₁, hc₁, -, -, hσ₁⟩ := chain_state_of_chain_with hfs hR₁ X hX
  obtain ⟨c₂, hc₂, hl₂, hlast₂, hσ₂⟩ := chain_state_of_chain_with hfs hR₂ W hW
  have hg₂ := genesis_mem_with hfs hR₂
  have hanc := anc_of_linked c₂ _ hg₂ hc₂ hl₂ W (by
    rcases hlast₂ with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  by_contra hn
  have hnot : ((tr.state y k).fg.σ X.root).F ∉ sp.toParams.fg.roots (c₂.map Block.fgView) := by
    intro hmem
    rw [← hFr] at hmem
    obtain ⟨Y, hY, hYF⟩ : ∃ Y ∈ sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload
        :: c₂, Y.root = F.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hmem
    have hYt : Y ∈ (tr.state z m).fg.tree := by
      rcases List.mem_cons.1 hY with rfl | h
      exacts [hg₂, hc₂ _ h]
    obtain rfl : Y = F := hU.1 (hsub₂ hYt) (hsub₁ hF) hYF
    exact hn ((hanc Y hY).mono hsub₂)
  have hF1 : 1 ≤ ((tr.state y k).fg.σ X.root).hF := by
    by_contra h0
    apply hnot
    rw [(FG.chain_invariants sp.toParams.fg _ _ hσ₁).2.2.2.2.1 (by omega)]
    exact List.mem_cons_self
  obtain ⟨S, hS, hSv⟩ := sp.toParams.fg.finalization_meets_crossing hσ₁ hσ₂ hF1 hlt hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H (max t u) := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin sp.toParams.fg.n))) (t := (H (max t u))ᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : ((H (max t u))ᶜ : Set (Fin sp.toParams.fg.n)).ncard =
        ((H (max t u))ᶜ : Set (Fin sp.toParams.n)).ncard := rfl
    have : sp.toParams.fg.n = sp.toParams.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  exact Shadow.held_atts_safe_at hrun hnc ht hk hy hu hm hz (le_max_left _ _)
    (le_max_right _ _) a b (chainAtts_held hc₁ ha) (chainAtts_held hc₂ hb) hv hab

end Consensus.Goldilocks.Healing.Growing

end
