module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the setting of unanimity (H.1 (i))

`proposal_votes`'s premises with the honest proposal unfolded: a `StandaloneRun`, the honest
proposer `q` of slot `p` and its `ac_proposal` call at cut `k` at `t_p` (label `ℓp`, duty head
`d`, payload `pay`), the block `P` it makes on `d.head`, `t_p ≥ ḡ + 2Θ + 8Δ`, and the locks
settled from `t_{p−1}`. The canonical walk is the proposer's walk (`ℓp.frame`'s scores
and eligibility at `t_p` against `View.ofLists pay`) on its tree with `P` added. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **The setting of unanimity** for the honest proposal `P` of slot `p`, made from the
`ac_proposal` call at cut `k` with label `ℓp`, duty head `d` and payload `pay`. -/
structure UnanimitySetting (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (schedule : Nat → Fin sp.n) (g : Time) (p : Nat) (P : Blk sp.n FGP) (k : Nat)
    (ℓp : ACLabel (goldilocksSA sp FGP ro))
    (d : DutyHead sp.n FGP (Payload sp.n)) (pay : Payload sp.n) : Prop where
  standalone : StandaloneRun tr H U schedule g
  proposer_mem : schedule p ∈ H
  call : tr.CallAt (schedule p) k ℓp
  call_proposal : ℓp.call = .proposal
  payload : (acProposal sp (tr.state (schedule p) k) ℓp.frame (tr.time k)).2 =
    some (d, pay)
  time : tr.time k = sp.ts p
  parent : P.parent = some d.head.root
  slot : P.slot = p
  proposer : P.proposer = schedule p
  acPayload : P.acPayload = pay
  accepted : ∃ j, k < j ∧ tr.AcceptAt (schedule p) j P ∧ tr.time j = sp.ts p
  late : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p
  settled : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)

/-- **The setting of unanimity with the weak lateness** `t_p ≥ ḡ + 8Δ`, all the unanimity
argument reads of the slot (`t_{p−1} ≥ ḡ + 4Δ`, `p > 0`); the margin for the locks is in
`settled`. Otherwise the fields of `UnanimitySetting`. -/
structure UnanimitySettingCore (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (schedule : Nat → Fin sp.n) (g : Time) (p : Nat) (P : Blk sp.n FGP)
    (k : Nat) (ℓp : ACLabel (goldilocksSA sp FGP ro))
    (d : DutyHead sp.n FGP (Payload sp.n)) (pay : Payload sp.n) : Prop where
  standalone : StandaloneRun tr H U schedule g
  proposer_mem : schedule p ∈ H
  call : tr.CallAt (schedule p) k ℓp
  call_proposal : ℓp.call = .proposal
  payload : (acProposal sp (tr.state (schedule p) k) ℓp.frame (tr.time k)).2 =
    some (d, pay)
  time : tr.time k = sp.ts p
  parent : P.parent = some d.head.root
  slot : P.slot = p
  proposer : P.proposer = schedule p
  acPayload : P.acPayload = pay
  accepted : ∃ j, k < j ∧ tr.AcceptAt (schedule p) j P ∧ tr.time j = sp.ts p
  late : gbar g + 8 * sp.Δ ≤ sp.ts p
  settled : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)

/-- The setting of unanimity gives the one with the weak lateness. -/
theorem UnanimitySetting.toCore {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {schedule : Nat → Fin sp.n} {g : Time} {p : Nat} {P : Blk sp.n FGP}
    {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n} (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) :
    UnanimitySettingCore tr H U schedule g p P k ℓp d pay :=
  ⟨hs.standalone, hs.proposer_mem, hs.call, hs.call_proposal, hs.payload, hs.time, hs.parent,
    hs.slot, hs.proposer, hs.acPayload, hs.accepted,
    by have := Θ_nonneg sp; linarith [hs.late], hs.settled⟩

end Consensus.Goldilocks.SA

end
