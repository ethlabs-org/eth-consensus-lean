module
public import AvailableChainGeneric.Statements.Pure.PCQuorum

@[expose] public section

/-! Generic Pure layer: an abstract PC record, its rank order and the
held-PC update `preferPC`. Source: `pcsa-decisions.md` (R-c, R-e, R-f; user
decision 2026-10-05 23:11) and `pcsa-v2-plan-fable.md` M0; the SAPC templates
are `AvailableChainSAPC/Model/Certificates.lean:38` (`preferPC`) and
`AvailableChainSAPC/Proofs/Rank.lean:11` (`PCRankLE`). The record keeps the
acker seat set and leaves the ack carrier to the instance. The rank compares
the slot, then a tie key of a linear order that the instance picks.
Definitions, contract Props and defining equations only. -/

namespace AvailableChain.Gen.Pure

/-- A PC: the seats `ackers` sent an exact ack on `(slot, target)`. -/
structure PC (n : Nat) (Target : Type) where
  slot : Nat
  target : Target
  ackers : Finset (Fin n)

namespace PC

variable {n : Nat} {Target : Type}

/-- A formed PC has at least `q_A` ackers. -/
def Formed (c : PC n Target) : Prop := qA n ≤ c.ackers.card

theorem Formed_def (c : PC n Target) : c.Formed = (qA n ≤ c.ackers.card) := by rfl

end PC

variable {n : Nat} {Target K : Type} [LinearOrder K]

/-- Strict rank: a higher slot, or the same slot and a higher tie key. -/
def RankLT (key : PC n Target → K) (c d : PC n Target) : Prop :=
  c.slot < d.slot ∨ (c.slot = d.slot ∧ key c < key d)

theorem RankLT_def (key : PC n Target → K) (c d : PC n Target) :
    RankLT key c d = (c.slot < d.slot ∨ (c.slot = d.slot ∧ key c < key d)) := by rfl

/-- Weak rank: a higher slot, or the same slot and a tie key at least as high. -/
def RankLE (key : PC n Target → K) (c d : PC n Target) : Prop :=
  c.slot < d.slot ∨ (c.slot = d.slot ∧ key c ≤ key d)

theorem RankLE_def (key : PC n Target → K) (c d : PC n Target) :
    RankLE key c d = (c.slot < d.slot ∨ (c.slot = d.slot ∧ key c ≤ key d)) := by rfl

/-- The held PC, or the candidate if its rank is strictly higher. The held
PC wins a rank tie. -/
def pickPC (key : PC n Target → K) (held cand : PC n Target) : PC n Target :=
  if held.slot < cand.slot ∨ (held.slot = cand.slot ∧ key held < key cand) then cand
  else held

theorem pickPC_def (key : PC n Target → K) (held cand : PC n Target) :
    pickPC key held cand =
      if held.slot < cand.slot ∨ (held.slot = cand.slot ∧ key held < key cand) then cand
      else held := by rfl

/-- Offer a candidate to the held PC slot: keep the rank-maximal PC. -/
def preferPC (key : PC n Target → K) (held : Option (PC n Target)) (cand : PC n Target) :
    Option (PC n Target) :=
  some ((held.map fun c => pickPC key c cand).getD cand)

theorem preferPC_def (key : PC n Target → K) (held : Option (PC n Target))
    (cand : PC n Target) :
    preferPC key held cand = some ((held.map fun c => pickPC key c cand).getD cand) := by rfl

/-- The held PC does not lose rank: each PC held before has a PC held after
of at least its rank. -/
def OptRankLE (key : PC n Target → K) (before after : Option (PC n Target)) : Prop :=
  ∀ c, before = some c → ∃ d, after = some d ∧ RankLE key c d

theorem OptRankLE_def (key : PC n Target → K) (before after : Option (PC n Target)) :
    OptRankLE key before after =
      (∀ c, before = some c → ∃ d, after = some d ∧ RankLE key c d) := by rfl

/-- Two formed PCs of one slot have the same target. `sent v b`: seat `v`
sent an exact HEAD on `b` at that slot; `acked v b`: seat `v` sent an ack on
`b` at that slot. A seat outside `F` sends at most one exact HEAD per slot and
acks `b` only if some `q_N` seat set sent exact HEADs on `b`.
The caller must specialize `sent` and `acked` to one fixed slot. The caller
must also connect both PC records to those ack occurrences through
certificate validity: each acker of `c` and of `d` sent an ack on the record's
target at that slot. Equal `slot` fields alone do not give this. -/
def PCSameSlotTargetStatement : Prop :=
  ∀ {n : Nat} {B : Type} (sent acked : Fin n → B → Prop) (F : Finset (Fin n))
    (c d : PC n B),
    (∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y) →
    (∀ v, v ∉ F → ∀ b, acked v b → ∃ S : Finset (Fin n), qN n ≤ S.card ∧ ∀ w ∈ S, sent w b) →
    F.card < qA n →
    c.Formed → d.Formed →
    (∀ v ∈ c.ackers, acked v c.target) → (∀ v ∈ d.ackers, acked v d.target) →
    c.target = d.target

/-- Defining equation. -/
theorem PCSameSlotTargetStatement_def : PCSameSlotTargetStatement =
    (∀ {n : Nat} {B : Type} (sent acked : Fin n → B → Prop) (F : Finset (Fin n))
      (c d : PC n B),
      (∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y) →
      (∀ v, v ∉ F → ∀ b, acked v b →
        ∃ S : Finset (Fin n), qN n ≤ S.card ∧ ∀ w ∈ S, sent w b) →
      F.card < qA n →
      c.Formed → d.Formed →
      (∀ v ∈ c.ackers, acked v c.target) → (∀ v ∈ d.ackers, acked v d.target) →
      c.target = d.target) := by rfl

end AvailableChain.Gen.Pure
