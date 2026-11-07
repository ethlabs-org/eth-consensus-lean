module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ACWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed

public section

/-! # Pending growing AC healing interface

The growing forms of five AC-level healing lemmas that the window's next-slot no-reorg step
consumes, under their agreed names (static name + `_at`), each in `SA.Growing`. A held or counted
vote is charged at the reading cut: its voter is honest at the observer's call (or at the counting
time), not merely at its cast, since a voter compromised later can block the admission of its
genuine vote with forged ones. A held state's reader is honest at an observation time after the
state's cuts.

* `honest_voters_half_before_at` (`SA.honest_voters_half_before`);
* `batch_proposal_at` (`SA.batch_proposal`);
* `lock_below_origin_at` (`SA.lock_below_origin`);
* `late_vote_held_of_frame_before_at` (`SA.late_vote_held_of_frame_before`);
* `optimisticPoint_pool_vote_at` (`SA.optimisticPoint_pool_vote`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- At least half of the committee are validators honest at a counting time `t ∈ [t_m + Δ, b]`
that vote in slot `m` by `t_m + Δ`. -/
theorem honest_voters_half_before_at {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) {t : Time} (hmt : sp.ts m + sp.Δ ≤ t)
    (htb : t ≤ b)
    (hrestart : ∀ x r, x ∈ H (tr.time r) → tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    sp.n ≤ 2 * {x | x ∈ H t ∧ ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ}.ncard := by
  sorry

/-- **The batch proposal** of slot `σ + 1` by a node honest at its proposal call `i`: with half
of the committee voting `σ` among the validators honest at `i`, every such vote extending `B` and
held at the proposal, `B` in the frame (viable or below `fc_root`) and the high locks compatible,
`B` is an honest ancestor of the duty head. -/
theorem batch_proposal_at (hrun : ACRun proposer tr H U) {σ : Nat} {B : Blk sp.n FGP}
    {x : Fin sp.n} {i : Nat} (hx : x ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hhalf : sp.n ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ j e', VoteAt tr z j e' ∧
      e'.msg.slot = σ}.ncard)
    (hB : ∀ z j e, z ∈ H (tr.time i) → VoteAt tr z j e → e.msg.slot = σ →
      VoteExtends U e.msg B)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ z j e, z ∈ H (tr.time i) → VoteAt tr z j e → e.msg.slot = σ →
      HeldAtProposal (tr.state x i) ℓ.frame σ e.msg)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head := by
  sorry

/-- Every lock held by a node honest at an observation time after the state's cuts lies below an
earlier result or optimistic lock of the same node. -/
theorem lock_below_origin_at
    (hr : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  sorry

/-- A slot-`s` vote of a validator honest at the observer's call `j` is held there, with its
block in the frame, by `t_s + 2Δ`. -/
theorem late_vote_held_of_frame_before_at {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H (tr.time j)) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ B ∈ U, B.root = e.msg.head → Anc U ell.frame.F B) :
    ∃ B ∈ ell.frame.tree, B.root = e.msg.head ∧ B.slot ≤ s ∧
      e.msg ∈ (tr.state y j).pool s ∧
      (tr.state y j).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (tr.state y j).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
  sorry

/-- A pool vote at an optimistic point of a node honest at its call `j`, by a validator honest at
`j`, is an actual vote of that validator by `j`. -/
theorem optimisticPoint_pool_vote_at (hrun : ACRun proposer tr H U)
    {x : Fin sp.n} {j : Nat} (hx : x ∈ H (tr.time j))
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {A : SAState sp.n} (hp : OptimisticPoint tr x j ℓ A)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H (tr.time j)) :
    v.slot = σ ∧ ∃ j' ≤ j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  sorry

end Consensus.Goldilocks.SA.Growing

end
