module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ProposalReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore

public section

/-! # Frozen source contracts for post-drain proposals

Each holder is honest at its observation and each origin writer at its write.
The label and optimistic-proposal obligations belong to the growing AC origin/lock owner.
The three retention/relay obligations remain explicitly open; none asserts a global
static cache-origin invariant.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An earlier high origin has a label before the actual proposal slot. -/
theorem ResetPremisesUpTo.origin_label_lt_at_proposal_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {v : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  sorry

/-- An old origin is held at the proposal, or below its finalized cache. -/
theorem ResetPremisesUpTo.proposal_holds_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u) :
    O ∈ ell.frame.tree ∨ Anc (tr.HonestBlocksAt H) O ell.frame.F := by
  exact ProposalImpl.proposal_holds_old_at hp hpH hci hcall hd hti hib ho hrt

/-- A held high origin is viable or below the frame root at the honest reader. -/
theorem ResetPremisesUpTo.held_high_origin_viable_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {c : Nat} (hpH : p ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p c ell)
    (hcb : tr.time c ≤ b) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) (ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ell.frame.tree) :
    B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot := by
  sorry

/-- Post-drain live high locks are compatible with each bounded high origin. -/
theorem ResetPremisesUpTo.proposal_stored_locks_compatible_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {q j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x q j O) (hqb : tr.time q ≤ b) :
    SA.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state p i)
      (tr.time i) (u - 1) O := by
  exact ProposalImpl.proposal_stored_locks_compatible_old_at hp hc hpH hR hci hcall hti hib ho hqb

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.SA.Growing

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {proposer : Nat → Fin sp.n} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {T : SATrace sp FGP ro}

/-- An optimistic lock with its counted votes held at the next proposal puts its
ancestor below the proposed head; writers and readers are separately honest. -/
theorem optimistic_first_proposal_anc_at
    (hrun : ACRun proposer T H U) {i : Nat}
    (hf : 2 * (H (T.time i))ᶜ.ncard < sp.n)
    {X : Fin sp.n} {i₀ σ : Nat} (hX : X ∈ H (T.time i₀))
    {D B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt T X i₀ σ D CV) (hBD : Anc U B D)
    {x : Fin sp.n} (hx : x ∈ H (T.time i))
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : T.CallAt x i ell)
    (hslot : sp.slot (T.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (T.state x i) ell.frame (T.time i)).2 = some (d, pay))
    (hV : B ∈ ell.frame.tree ∧
      (B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (T.state x i) ell.frame σ v)
    (hhigh : HighLocksCompatible U (T.state x i) (T.time i) σ B) :
    Anc U B d.head := by
  exact ProposalSources.optimistic_first_proposal_anc_at hrun hf hX hopt hBD hx hc
    hslot hprop hV hP hhigh

end Consensus.Goldilocks.SA.Growing

end
