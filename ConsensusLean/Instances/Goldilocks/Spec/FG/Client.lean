module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State

@[expose] public section

/-! # Goldilocks FG: validator client and slashing conditions

The validator client of fg.tex §"Validator client" with loose BJ (the
finality pair is read from the entry state of the source) and the weakened E1
(the timeout record is a set of roots, `permits` needs
`timeout[j] ⊆ {T}`, `height_pair` tests the lock first), and the slashing
conditions of fg.tex §"Slashing conditions". The client's input is the entry state
`σe = Σ.σ[T_c]` of its source (`fg_attest`): its height is the source's height `h_c`
and its `Th` is `T_c` itself, so the height pair names `(σe.h, σe.Th)`.

This module holds only what the Challenge statements reach; `Record.run`, a client run, is in
`Milestones/Spec/FG/Client` (`docs/decisions.md` §"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks.FG

/-- The content of an attestation: height pair and finality pair. -/
abbrev Content : Type := Nat × Nat × Bool × Option (Nat × Nat)

/-- The content of an attestation. -/
def Att.content {n : Nat} (a : Att n) : Content := (a.h, a.T, a.timeout, a.fin)

/-- The anti-slashing record `Λ = (target[·], timeout[·], lock[·], sent)`: the first
target at each height, the roots that the timeouts at each height name, the target of
the first finality pair at each height, and the contents sent. -/
structure Record where
  /-- The first target sent at each height. -/
  target : Nat → Option Nat
  /-- The roots that the timeouts sent at each height name. -/
  timeout : Nat → Finset Nat
  /-- The target of the first finality pair at each height. -/
  lock : Nat → Option Nat
  /-- The contents sent. -/
  sent : List Content

namespace Record

/-- The empty record. -/
def empty : Record := ⟨fun _ => none, fun _ => ∅, fun _ => none, []⟩

/-- `permits`: the record allows the finality pair `(j, T)`. -/
def permits (Λ : Record) (j T : Nat) : Prop :=
  (Λ.target j = none ∨ Λ.target j = some T) ∧ Λ.timeout j ⊆ {T} ∧
    (Λ.lock j = none ∨ Λ.lock j = some T)

instance (Λ : Record) (j T : Nat) : Decidable (Λ.permits j T) :=
  inferInstanceAs (Decidable ((Λ.target j = none ∨ Λ.target j = some T) ∧
    Λ.timeout j ⊆ {T} ∧ (Λ.lock j = none ∨ Λ.lock j = some T)))

/-- `finality_pair`: at an entry whose previous height is justified the predecessor when permitted
(also if a later state finalized it), else the newest permitted pending pair of the entry state. -/
def finalityPair {n : Nat} (Λ : Record) (σe : ChainState n) : Option (Nat × Nat) :=
  if σe.previousHeightJustified then
    if Λ.permits σe.hj σe.J then some (σe.hj, σe.J) else none
  else
    (σe.pending.filter (fun p => decide (Λ.permits p.1 p.2))).foldl (fun acc p =>
      match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) none

/-- `height_pair`: locked elsewhere gives none; a recorded timeout gives a timeout; a
free or equal target gives a target; otherwise a timeout. `(h, T, τ)`. -/
def heightPair (Λ : Record) (hc Tc : Nat) : Option (Nat × Nat × Bool) :=
  if Λ.lock hc ≠ none ∧ Λ.lock hc ≠ some Tc then none
  else if Λ.timeout hc ≠ ∅ then some (hc, Tc, true)
  else if Λ.target hc = none ∨ Λ.target hc = some Tc then some (hc, Tc, false)
  else some (hc, Tc, true)

/-- `record_attestation`, the only writer of the record. -/
def recordAtt {n : Nat} (Λ : Record) (a : Att n) : Record where
  target := if !a.timeout ∧ Λ.target a.h = none then Function.update Λ.target a.h (some a.T)
    else Λ.target
  timeout := if a.timeout then Function.update Λ.timeout a.h (insert a.T (Λ.timeout a.h))
    else Λ.timeout
  lock := match a.fin with
    | some p => Function.update Λ.lock p.1 (some p.2)
    | none => Λ.lock
  sent := Λ.sent ++ [a.content]

/-- `create_attestation` of validator `v` for a source with entry state `σe`: the
attestation and the new record, or none (no height pair, or a target that is not the
first vote at its height, or an entry named twice). -/
def createAtt {n : Nat} (Λ : Record) (v : Fin n) (σe : ChainState n) :
    Option (Att n × Record) :=
  match Λ.heightPair σe.h σe.Th with
  | none => none
  | some (h, T, τ) =>
      if Λ.sent.any (fun b => b.1 = h ∧ (!τ ∨ b.2.1 = T)) then none
      else
        let a : Att n := ⟨v, h, T, τ, Λ.finalityPair σe⟩
        some (a, Λ.recordAtt a)

end Record

/-- E1 (weakened): the finality pair `(h, T)` of `a` meets a height pair of `b` at
height `h` that names another block, as a timeout or a target vote. -/
def e1 {n : Nat} (a b : Att n) : Prop := ∃ p ∈ a.fin.toList, b.h = p.1 ∧ b.T ≠ p.2

instance {n : Nat} (a b : Att n) : Decidable (e1 a b) :=
  inferInstanceAs (Decidable (∃ p ∈ a.fin.toList, b.h = p.1 ∧ b.T ≠ p.2))

/-- E2: two target votes at one height for different blocks. -/
def e2 {n : Nat} (a b : Att n) : Prop :=
  a.h = b.h ∧ a.timeout = false ∧ b.timeout = false ∧ a.T ≠ b.T

/-- Two attestations of one validator are slashable (they can be the same one). -/
def slashable {n : Nat} (a b : Att n) : Prop := a.val = b.val ∧ (e1 a b ∨ e1 b a ∨ e2 a b)

instance {n : Nat} (a b : Att n) : Decidable (e2 a b) :=
  inferInstanceAs (Decidable (a.h = b.h ∧ a.timeout = false ∧ b.timeout = false ∧ a.T ≠ b.T))

instance {n : Nat} (a b : Att n) : Decidable (slashable a b) :=
  inferInstanceAs (Decidable (a.val = b.val ∧ (e1 a b ∨ e1 b a ∨ e2 a b)))

end Consensus.Goldilocks.FG

end
