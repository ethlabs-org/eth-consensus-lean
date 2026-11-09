module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.SeedCandidate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows

public section

/-! # A held target is an ancestor candidate, under growing faults

`held_target_ancestor_candidate_at_state_at`, the growing form of
`Obligations.UpTo.held_target_ancestor_candidate_at_state`: at a state of a reader honest at an
observation `t ≤ b`, every earlier cut at a time `≤ t`, a held target above a bounded high seed
and compatible with every earlier high origin is an ancestor candidate of the reader's frame.

The seed is held because it lies below the held target (`mem_of_honest_anc_at`), so this is the
guarded-seed candidacy `guarded_seed_ancestor_candidate_at_state_at` with the target above the
seed. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **A held target is an ancestor candidate.** At a state of a reader honest at `t ≤ b`, every
earlier cut at a time `≤ t`, a target held in the reader's frame above a bounded high seed and
compatible with every earlier high origin is an ancestor candidate of the frame. -/
theorem held_target_ancestor_candidate_at_state_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) P B) :
    (Node.frame (tr.state y i)).AncestorCandidate P :=
  hp.guarded_seed_ancestor_candidate_at_state_at ht hle hy htb hPt hseed hqb
    (fun _ => mem_of_honest_anc_at hp.run hp.noColl ht hle hy hSP hPt.1) (Or.inr hSP) hcompare

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
