module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ACWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed

public section

/-! # Pending growing AC healing interface

The growing forms of five AC-level healing lemmas that the window's next-slot no-reorg step
consumes, under their agreed names, each in `SA.Growing`. A vote is an
actual vote only at a cast cut of a voter honest there. A held or counted vote is charged both at
its cast and at the reading cut (the observer's call or the counting time), since a voter
compromised later can block the admission of its genuine vote with forged ones; counted and held
votes carry the vote deadline `t_σ + Δ`, so the cast is before the read. A held state's reader is
honest at its cut.

* `honest_voters_half_before_at` (`SA.honest_voters_half_before`);
* `batch_proposal_at` (`SA.batch_proposal`);
* `late_vote_held_of_frame_before_at` (`SA.late_vote_held_of_frame_before`);
* `lock_below_origin`, `optimisticPoint_pool_vote` (the same names as the static ones, in
  `SA.Growing`), copies of the statements of `Lemmas/Growing/AC/Healing/Origins`.

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
of the committee voting `σ` by `t_σ + Δ` among the validators honest at `i`, every vote of slot
`σ` of a voter honest at its cast extending `B`, the counted votes held at the proposal, `B` in
the frame (viable or below `fc_root`) and the high locks compatible, `B` is an honest ancestor of
the duty head. -/
theorem batch_proposal_at (hrun : ACRun proposer tr H U) {σ : Nat} {B : Blk sp.n FGP}
    {x : Fin sp.n} {i : Nat} (hx : x ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hhalf : sp.n ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ j e', VoteAt tr z j e' ∧
      e'.msg.slot = σ ∧ tr.time j ≤ sp.ts σ + sp.Δ}.ncard)
    (hB : ∀ z j e, z ∈ H (tr.time j) → VoteAt tr z j e → e.msg.slot = σ →
      VoteExtends U e.msg B)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ z j e, z ∈ H (tr.time i) → VoteAt tr z j e → e.msg.slot = σ →
      tr.time j ≤ sp.ts σ + sp.Δ → HeldAtProposal (tr.state x i) ℓ.frame σ e.msg)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head := by
  sorry

/-- Every lock held by a node honest at its cut lies below an earlier result or optimistic lock
of the same node. -/
theorem lock_below_origin
    (hr : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ ∃ O, Anc U L O ∧
      ∃ k < i, ∃ CV, ResultAt tr y k l.slot O CV ∨ OptimisticLockAt tr y k l.slot O CV := by
  sorry

/-- A slot-`s` vote of a validator honest at its cast and at the observer's call `j` is held
there, with its block in the frame, by `t_s + 2Δ`. -/
theorem late_vote_held_of_frame_before_at {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {x : Fin sp.n} {i : Nat} (hx : x ∈ H (tr.time i)) (hxj : x ∈ H (tr.time j))
    {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s)
    (hF : ∀ B ∈ U, B.root = e.msg.head → Anc U ell.frame.F B) :
    ∃ B ∈ ell.frame.tree, B.root = e.msg.head ∧ B.slot ≤ s ∧
      e.msg ∈ (tr.state y j).pool s ∧
      (tr.state y j).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (tr.state y j).blockStamp e.msg.head < ETime.of (sp.ts s + 2 * sp.Δ) := by
  sorry

/-- A pool vote at an optimistic point of a node honest at its call `j`, by a validator honest at
`j`, is an actual vote of that validator by `j`. -/
theorem optimisticPoint_pool_vote (hrun : ACRun proposer tr H U)
    {x : Fin sp.n} {j : Nat} (hx : x ∈ H (tr.time j))
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {A : SAState sp.n} (hp : OptimisticPoint tr x j ℓ A)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H (tr.time j)) :
    v.slot = σ ∧ ∃ j' ≤ j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  sorry

end Consensus.Goldilocks.SA.Growing

end
