module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # Healing provenance at an honest reading cut

Retaining the history through the reader's cut preserves the block universe and all
earlier writes. Validators of pool votes are required honest at that same reading cut.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- Every stored lock has an earlier result or optimistic origin of its slot. -/
theorem lock_below_origin
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  intro l hl
  have hm := hr.time_mono
  have hs : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y (fun q hq => hm hq.le)
  obtain ⟨L, hL, hLr, O, hLO, k, hki, CV, hO⟩ :=
    SA.lock_below_origin (hr.upTo (hr.time_nonneg i)) hy i l (hs.symm ▸ hl)
  refine ⟨L, hL, hLr, O, hLO, k, hki, CV, ?_⟩
  rcases hO with hO | hO
  · exact Or.inl ((upTo_resultAt hm).mp hO).2
  · exact Or.inr ((upTo_optimisticLockAt hm).mp hO).2

/-- A vote in an optimistic point of a reader and validator honest at that cut has
an actual emission no later than the reading cut. -/
theorem optimisticPoint_pool_vote (hrun : ACRun proposer tr H U)
    {x : Fin sp.n} {j : Nat} (hx : x ∈ H (tr.time j))
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {A : SAState sp.n}
    (hp : OptimisticPoint tr x j ℓ A) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ A.pool σ) (hvH : v.val ∈ H (tr.time j)) :
    v.slot = σ ∧ ∃ j' ≤ j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  have hm := hrun.localRun.time_mono
  obtain ⟨hs, j', hj', e', he', hev⟩ := SA.optimisticPoint_pool_vote
    (hrun.upTo (hrun.localRun.time_nonneg j)) hx
    ((upTo_optimisticPoint hm).mpr ⟨le_rfl, hp⟩) hv hvH
  exact ⟨hs, j', hj', e', (upTo_voteAt.mp he').2, hev⟩

end Consensus.Goldilocks.SA.Growing
