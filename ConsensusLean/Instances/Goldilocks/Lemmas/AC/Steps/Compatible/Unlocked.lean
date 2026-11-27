module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Goldilocks AC: the locks of a node after its slot-`(s+1)` unlocking (A1.9, case (i))

Let an honest node write a fast lock of slot `s` on `D ⪰ B` with counted votes `CV`, under
`Carry(s, S, B)`. At an honest `x`'s slot-`(s+1)` vote, the counted validators (at least half of
the committee) are supporters of `B` in `x`'s merged view or equivocate there, so its unlocking
moves every lock of a slot below `s` to a block compatible with `B` (`unlock_compatible`; when
`B` is below the frame's `Φ.F`, every block of the tree extends it). Later, locks only move back,
and the fast locks written after the vote are of slot `s` or later: every lock of a slot below
`s` that `x` holds after the vote is on a block compatible with `B`. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → ACState sp.n}

/-- The counted votes of an honest fast lock of slot `s` on `B`: their validators are at least
half of the committee, and each is a slot-`s` vote whose head, of slot at most `s`, extends `B`
inside `U`. From starts up to the vote permission. -/
theorem fastLock_counted (hrun : ACRun proposer tr H U ini)
    {w : Fin sp.n} (hw : w ∈ H) {i₀ s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr w i₀ s B CV) :
    sp.committeeSize ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R := by
  have hr := hrun.localRun
  rcases hfl with ⟨ℓ, C, ⟨hc, -, -, -⟩, -, hD, rfl⟩ | ⟨ℓ, A, hpt, hsl, hsel, rfl⟩
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callU hr.toU hw hc
    refine ⟨?_, ?_⟩
    · have hfast := (deepest_mem hD).1.2.2
      unfold FastTest confirmationScore at hfast
      refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
      rintro u ⟨hu, x, ⟨hx, hres⟩, hval, -, hanc⟩
      exact ⟨x, ⟨hx, hval ▸ hu, hres, hanc⟩, hval⟩
    · rintro v ⟨hvp, -, hres, R, hR, hRr, hBR⟩
      refine ⟨state_pool_slotU sp hr.toU hrun.vstart hw i₀ s v hvp, R, hΦU hR, hRr, ?_,
        Anc.mono hΦU hBR⟩
      have hvs := state_pool_slotU sp hr.toU hrun.vstart hw i₀ s v hvp
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · rename_i Hd hl
        obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
        obtain rfl : Hd = R := hΦ.coherent.1 hHd hR (hHdr.trans hRr.symm)
        split_ifs at hres with hlt
        · exact absurd hres (by simp [ETime.of])
        · omega
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callU hr.toU hw hpt.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    refine ⟨?_, ?_⟩
    · have hsub : optimisticVoters sp A ℓ.frame (sp.slot (tr.time i₀)) B ⊆
          {u | ∃ v ∈ {v | v ∈ A.pool s ∧ AncR ℓ.frame B v.head}, v.val = u} := by
        rintro u ⟨v, hv, rfl, hanc⟩
        exact ⟨v, ⟨hsl ▸ hv, hanc⟩, rfl⟩
      have := Set.ncard_le_ncard hsub
      omega
    · rintro v ⟨hv, R, hR, hRr, hBR⟩
      refine ⟨optimisticPoint_pool_slotU hr.toU hrun.vstart hw hpt hv, R, hΦU hR, hRr, ?_,
        Anc.mono hΦU hBR⟩
      have := frame_slot_leU sp hr.toU hw hpt.1 R hR
      omega

end Consensus.Goldilocks.AC

end
