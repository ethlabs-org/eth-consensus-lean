module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame

public section

/-! # Goldilocks under `Sleepy` with growing faults: members of the healed family

Every member of the healed family sits below an origin of its label written at the member's cut
(`HealedOrigin.below_origin`): an origin is itself, a lock write keeps a prefix of its update's
confirmation or is an optimistic selection (`lock_below_origin_at`), and a high origin is the
viable ancestor of a fast lock write. So members are held while honest (`HealedOrigin.mem`), a
vote extending the origin extends the member, and compatibility with every origin passes to every
member (`HealedOrigin.compatible_of_origins`). A block below one member is compatible with every
member once the members are pairwise compatible (`OnHealedChain.compatible`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Compatibility with `B` passes to ancestors. -/
theorem compatible_of_anc_left {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {X Y B : SA.Blk sp.n (List (FG.Att sp.n))} (hXY : Anc U X Y) (h : Compatible U Y B) :
    Compatible U X B := by
  rcases h with h | h
  · exact Or.inl (hXY.trans h)
  · exact SA.anc_total hU hXY h

/-- A vote extending a block extends each of its ancestors. -/
theorem voteExtends_of_anc {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} {v : Vote sp.n}
    {C O : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.VoteExtends U v O) (hCO : Anc U C O) :
    SA.VoteExtends U v C :=
  let ⟨Hd, hHd, hHdr, hOHd⟩ := h
  ⟨Hd, hHd, hHdr, hCO.trans hOHd⟩

/-- An origin within `b` is held while honest. -/
theorem OriginWithin.mem (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} (h : OriginWithin tr H C s b) :
    C ∈ tr.HonestBlocksAt H := by
  obtain ⟨x, k, CV, hx, -, hO⟩ := originWithin_iff.1 h
  exact upTo_subset hrun (hrun.time_nonneg k)
    (origin_mem_upTo hrun hnc (hrun.time_nonneg k) hx le_rfl hO)

/-- **Every member of the healed family is below an origin of its label within `b`**. -/
theorem HealedOrigin.below_origin (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {s : Nat} {b : Time} (hC : HealedOrigin tr H g rL rO C s b) :
    ∃ O, OriginWithin tr H O s b ∧ Anc (tr.HonestBlocksAt H) C O := by
  rcases healedOrigin_iff.1 hC with ⟨-, h⟩ | ⟨-, h⟩ | ⟨x, i, hib, ho⟩
  · exact ⟨C, h, .refl⟩
  · exact h.below_origin hrun hnc
  · obtain ⟨CV, ell, D, hcall, hfl, rfl⟩ := ho.2.2.1
    obtain ⟨O, OV, hO, hDO⟩ := lock_below_origin_at hrun hnc ho.1 (Or.inl ⟨CV, hfl⟩)
    exact ⟨O, originWithin_iff.2 ⟨x, i, OV, ho.1, hib, hO⟩,
      (Anc.mono (frameIn_at hrun hnc ho.1 hcall).2 (SA.anc_viableAncestor _ D)).trans hDO⟩

/-- A member of the healed family is held while honest. -/
theorem HealedOrigin.mem (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {rL rO : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time}
    (hC : HealedOrigin tr H g rL rO C s b) : C ∈ tr.HonestBlocksAt H := by
  obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
  by_cases h : C = O
  · exact h ▸ hO.mem hrun hnc
  · exact (Anc.mem hCO h).1

/-- **Compatibility with the origins gives compatibility with the family**: a block compatible
with every origin within `b` of label `≤ s` is compatible with every member of label `≤ s`. -/
theorem HealedOrigin.compatible_of_origins (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {g : Time} {rL rO s : Nat} {b : Time}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C) :
    ∀ C j, HealedOrigin tr H g rL rO C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C := by
  intro C j hC hj
  obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
  exact (compatible_of_anc_left (honestBlocksAt_coherent hrun hnc) hCO (h O j hO hj).symm).symm

/-- Two blocks below two compatible blocks are compatible. -/
theorem compatible_of_anc_both {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {C C' O O' : SA.Blk sp.n (List (FG.Att sp.n))} (hCO : Anc U C O) (hC'O' : Anc U C' O')
    (h : Compatible U O O') : Compatible U C C' := by
  rcases h with h | h
  · exact SA.anc_total hU (hCO.trans h) hC'O'
  · exact SA.anc_total hU hCO (hC'O'.trans h)

/-- **A block on the healed chain is compatible with every member** when the members are
pairwise compatible: it is below one member `C₀`, and every member is compatible with `C₀`. -/
theorem OnHealedChain.compatible (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {g : Time} {rL rO : Nat} {b : Time}
    (hP : ∀ C s C' s', HealedOrigin tr H g rL rO C s b → HealedOrigin tr H g rL rO C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {X D : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hX : OnHealedChain tr H g rL rO X b)
    (hD : HealedOrigin tr H g rL rO D s b) : Compatible (tr.HonestBlocksAt H) X D := by
  obtain ⟨C₀, s₀, hC₀, hXC₀⟩ := onHealedChain_iff.1 hX
  exact compatible_of_anc_left (honestBlocksAt_coherent hrun hnc) hXC₀ (hP C₀ s₀ D s hC₀ hD)

end Consensus.Goldilocks.Compose.Growing

end
