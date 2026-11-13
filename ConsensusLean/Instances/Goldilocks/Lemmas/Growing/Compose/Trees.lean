module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Coherence of trees held while honest

Each held tree is retained at its own honesty horizon. Different trees need not have a common
honest cohort: collision resistance identifies their blocks across the two retained prefixes.
-/

namespace Consensus.Goldilocks.Compose.Growing

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

private theorem held_block_cases
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {X : A.Blk} (hX : X ∈ tr.HonestBlocksAt H) :
    X = P.genesisBlock A.genesisPayload ∨
      tr.Occurs X ∧ X.RootOk dg ∧ X.proposer = proposer X.slot ∧ X.root ≠ P.genesisRoot := by
  obtain ⟨y, i, t, ht, hb, hy, hX⟩ := hX
  have hs := Trace.upTo_state tr y hb
  have hp := h.upTo ht
  rw [← hs] at hX
  rcases Compose.tree_cases hp hy hX with hg | ⟨k, _, hk⟩
  · exact Or.inl hg
  · obtain ⟨hr, hpr, _, hng⟩ := Compose.accept_facts hp hy hk
    exact Or.inr ⟨RunTrace.upTo_occurs ⟨y, k, true, hk⟩, hr, hpr, hng⟩

private theorem held_root_inj (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : NoCollRun dg tr) {X Y : A.Blk}
    (hX : X ∈ tr.HonestBlocksAt H) (hY : Y ∈ tr.HonestBlocksAt H)
    (hr : X.root = Y.root) : X = Y := by
  rcases held_block_cases h hX with rfl | ⟨hx, hro, hpr, hng⟩ <;>
    rcases held_block_cases h hY with rfl | ⟨hy, hro', hpr', hng'⟩
  · rfl
  · exact absurd hr.symm hng'
  · exact absurd hr hng
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hnc X (Or.inr hx) Y (Or.inr hy)
    (by rw [← hro, ← hro', hr])
  obtain ⟨r, pa, sl, pp, inp, fp, ap⟩ := X
  obtain ⟨r', pa', sl', pp', inp', fp', ap'⟩ := Y
  simp only at hr h₁ h₂ h₃ h₄ h₅ hpr hpr'
  subst hr h₁ h₂ h₃ h₄ h₅
  rw [hpr, hpr']

/-- Blocks held while honest form a coherent tree universe under collision resistance. -/
theorem honest_blocks_coherent_local
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) := by
  refine ⟨fun _ hx _ hy hr => held_root_inj h hnc hx hy hr,
    fun Y hY X hX hp => ?_⟩
  obtain ⟨y, i, t, ht, hb, hy, hXi⟩ := hX
  have hs := Trace.upTo_state tr y hb
  have hr := h.upTo ht
  rw [← hs] at hXi
  rcases Compose.tree_cases hr hy hXi with rfl | ⟨k, hki, hk⟩
  · cases hp
  obtain ⟨pr, _, hpar, _, hheld, _⟩ := Store.onBlock_eq_some (hr.cutLaw y hy k _ hk).2.1
  rw [hp] at hpar
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hheld
  have hZr := (Compose.fg_reachable hr hy k).blocks_root hZ
  have hZt : Z ∈ ((tr.upTo t).state y k).fg.tree := by
    change _ = _
    rw [hZr, hZ]
  cases Option.some.inj hpar
  have hZH : Z ∈ tr.HonestBlocksAt H :=
    RunTrace.honestBlocks_upTo_subset h.time_mono ht ⟨y, hy, k, hZt⟩
  obtain rfl : Z = Y := held_root_inj h hnc hZH hY hZr
  exact (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hr hy i)).2.1.2 Z
    (Compose.tree_mono hr hy hki.le hZt) X hXi hp

/-- Blocks held while honest in a Goldilocks run form a coherent tree universe. -/
theorem honest_blocks_coherent {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (h : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) :=
  honest_blocks_coherent_local h.toLocalRun hnc

end Consensus.Goldilocks.Compose.Growing

end
