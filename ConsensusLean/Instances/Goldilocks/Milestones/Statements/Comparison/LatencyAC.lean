module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC

@[expose] public section

/-! # Slice 0 at Tier A: proposal latency (statements)

The Tier A counterpart of the Slice 0 proposal latency, over AC traces of the Goldilocks SA with
the unlock given (`StandaloneRunU m u`) at every write mode of width `k`: on a run synchronous
from the start (`g ≤ 0`), every honest proposal `P` of a slot `p ≥ p₀` is in every honest
confirmed tip from `t_p + D`. It is a proposal-inclusion claim, not transaction latency, and it
has no contract default.

* `SyncAC0 m u f g`: H.1's run premises with the unlock `u` at mode `m` (`StandaloneRunU`), GST
  `g ≤ 0`, every member of the constant honest set `H` awake from `0`, and `|Hᶜ| ≤ f`.
* `ProposalLatencyAC0 p₀ d`: monotone `d` (a `Δ`-coefficient per cap `f`), and for every honest
  proposal `P` of a slot `p ≥ p₀`, `P ⪯ ac_confirmed` at every call of an honest node at a time
  `t ≥ t_p + d(f)·Δ` (at `t_p + d(f)·Δ` itself, from its tick there on).
* `ProposalLatencyAC0Sync`: the instance `p₀ = 2`, `d = acLat0` (`6` at `2·f < n`, `⊤`
  elsewhere), for every SA parameter set.
* `ProposalLatencyAC0Bridge`: with `Prop(G_p)` (an honest proposer in every window of length
  `G_p`), for every `t ≥ t₂` some honest proposal released in `[t, t + G_p]` is in every honest
  confirmed tip from `t + G_p + 6Δ` on: inclusion of some honest proposal by `t + G_p + 6Δ`.

All static (constant `H`). -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **Tier A Slice 0 synchronous premises** at cap `f`, mode `m` and unlock oracle `u`: H.1's
premises with the unlock given (`StandaloneRunU`) at GST `g ≤ 0`, every member of the constant
honest set `H` awake from `0`, and `|Hᶜ| ≤ f`. -/
def SyncAC0 (m : WriteMode) (u : Nat → Set Lock) (f : ℕ) (g : Time) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (proposer : Nat → Fin sp.n) : Prop :=
  StandaloneRunU m u tr H U proposer g ∧ g ≤ 0 ∧ (∀ y ∈ H, ∀ t, 0 ≤ t → tr.awake y t) ∧
    Hᶜ.ncard ≤ f

variable (sp) in
/-- **The Tier A Slice 0 proposal latency** from slot `p₀` with bound `d` (a `Δ`-coefficient after
the proposal's slot time): `d` is monotone in the cap, and for every write mode `m` of width `k`,
every unlock oracle `u` and every run with the synchronous premises at cap `f`, every honest
proposal `P` of a slot `p ≥ p₀` is, at every call of an honest node at a time `t ≥ t_p + d(f)·Δ`
(at `t_p + d(f)·Δ` itself, from its tick there on), an ancestor of `ac_confirmed` after the call. -/
def ProposalLatencyAC0 (p₀ : ℕ) (d : Bound ℕ) : Prop :=
  AdverseMonotone d ∧
  ∀ (m : WriteMode), m.width = sp.k → ∀ (u : Nat → Set Lock) (FGP : Type)
    (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (f c : ℕ) (g : Time), d f = c →
    SyncAC0 m u f g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), p₀ ≤ p → proposer p ∈ H →
      HonestProposalU u tr (proposer p) p P →
      ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + (c : Time) * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + (c : Time) * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))

variable (sp) in
/-- The synchronous-start latency bound: `6` at caps with `2·f < n` (the fault field of
`StandaloneRunU`), `⊤` elsewhere. -/
def acLat0 : Bound ℕ := fun f => if 2 * f < sp.n then ((6 : ℕ) : WithTop ℕ) else ⊤

/-- **The synchronous-start Tier A instance**: at every SA parameter set, the Tier A Slice 0
proposal latency from slot `2` holds with `acLat0` (`6Δ` at `2·f < n`) for every width-`k` write
mode and every unlock oracle. -/
def ProposalLatencyAC0Sync : Prop := ∀ sp : SAParams, ProposalLatencyAC0 sp 2 (acLat0 sp)

/-- **The bridge to inclusion of some honest proposal**: at every SA parameter set, width-`k` write
mode and unlock oracle, on every run with the synchronous premises and `Prop(G_p)`, for every
`t ≥ t₂` there is a proposal `P` of a slot `p` with `t ≤ t_p ≤ t + G_p`, whose proposer is in `H`
(an honest proposal), that is, at every
call of an honest node at a time `≥ t + G_p + 6Δ` (at `t + G_p + 6Δ` itself, from its tick there
on), an ancestor of `ac_confirmed` after the call. -/
def ProposalLatencyAC0Bridge : Prop :=
  ∀ (sp : SAParams) (m : WriteMode), m.width = sp.k → ∀ (u : Nat → Set Lock) (FGP : Type)
    (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (f : ℕ) (g Gp : Time),
    SyncAC0 m u f g tr H U proposer → PropAC proposer H g Gp →
    ∀ t, sp.ts 2 ≤ t →
      ∃ (p : Nat) (P : Blk sp.n FGP), t ≤ sp.ts p ∧ sp.ts p ≤ t + Gp ∧ proposer p ∈ H ∧
        HonestProposalU u tr (proposer p) p P ∧
        ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → t + Gp + 6 * sp.Δ ≤ tr.time j →
          (tr.time j = t + Gp + 6 * sp.Δ →
            ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
          Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))

end Consensus.Goldilocks.Comparison

end
