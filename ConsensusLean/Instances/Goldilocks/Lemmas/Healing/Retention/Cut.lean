module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps

public section

/-! # Goldilocks Healing, HR.4: prefix comparison of high origins

* **Prefix comparison**: with `VoteInv` through cut `k`, every high origin written by `k` is
  comparable with every high origin active at `k` (`origins_compatible_prefix`): earlier labels
  by the honest votes of the later label (`fastLock_compatible_of_votes`; the votes of a pending
  label precede `t_{j+1}`), the same label by TSQ (`fastLock_same_slot`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### Run facts -/

/-! ### The prefix comparison of origins -/

/-- Finite prefix comparison bounds both writes and the votes used by the
induction hypothesis. Activation may precede the target's eventual write. -/
theorem ResetPremisesUpTo.origins_compatible_prefix {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : AC.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c ≤ k, tr.time c ≤ b → ∀ e, AC.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) {x' : Fin sp.n} {r l : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))} (ho' : HighOrigin tr H g x' r l O)
    (hrk : r ≤ k) (hrb : tr.time r ≤ b) : Compatible (tr.HonestBlocks H) B O := by
  apply hp.origins_compatible_before (k := k + 1)
    (fun ho₀ hi₀ z hz c hc => hvote ho₀ hi₀ z hz c (by omega)) ho
    (hp.cutZ_le_ts_of_highOrigin ho) ?_ ho'
    (by omega) hib hrb
  rcases hact with h | h
  · exact Or.inl (by omega)
  · refine Or.inr fun c hc => ?_
    by_contra hck
    exact (not_lt_of_ge (h.trans (hp.run.time_mono (show k ≤ c by omega)))) hc

/-! ### The cut step and the attestations -/

end Consensus.Goldilocks.Healing

end
