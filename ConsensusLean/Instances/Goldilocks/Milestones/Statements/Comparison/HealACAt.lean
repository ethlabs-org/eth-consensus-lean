module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.ACU
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes

@[expose] public section

/-! # Slice 0 at Tier A at one write mode: the AC heal profile (statement)

`HealProfileACAt sp m d` is the Tier A Slice 0 heal profile `HealProfileAC0` at the single write
mode `m`. It has the same incident premises (`IncidentAC0 m u q b₀ g`), the same claim and the same
monotone bound. It quantifies over every unlock oracle `u`, but not over the mode. It is the
profile of a lock rule whose writes are the mode `m`: the parent SA's handlers at mode `m`, with
the locks after each unlock given by `u`. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

/-- **The Tier A Slice 0 heal profile at the write mode `m`** with bound `d`, a `Δ`-coefficient
after `ḡ`. `d` is monotone. The claim covers every unlock oracle `u`, every run with the incident
premises at mode `m` and point `q` (`IncidentAC0 m u q b₀ g`), and every honest proposal `P` of
slot `p` with `t_p ≥ ḡ + d(q)·Δ`:
1. every honest vote of slot `p` is `P`;
2. at every call of an honest node at a time `t ≥ t_p + 6Δ` (at `t_p + 6Δ` itself, from its tick
   there on), `P ⪯ ac_confirmed` after the call. -/
def HealProfileACAt (sp : SAParams) (m : WriteMode) (d : Bound (Slice0Q (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (u : Nat → Set Lock) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    (q : Slice0Q (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentAC0 m u q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposalU u tr (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))

end Consensus.Goldilocks.Comparison

end
