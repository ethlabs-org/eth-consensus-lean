module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Memory
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.ParentOracleM

@[expose] public section

/-! # Cost at Tier A: carried votes, lock counts and working rows (statements)

Standalone Tier A predicates over AC traces of the Goldilocks family, static (constant honest set
`H`), like `SigningRateAC0`. They are counterparts of the generic coordinates of
`Comparison/Cost`: the vote class (`RoleClass.duty` of the vote kind) and the proposer class
(`RoleClass.proposer`) of `Consensus.Comparison.CarriedBound`, and the `locks` and `saved` fields
of `Consensus.Comparison.LockMemory` (each a `StateBound`). They are not instances of them: an
instance needs a representation of these runs as runs of a compiled chain-shape system, the
family's measures as `StateBound` measures and a run bridge, none of which is stated here.

* `CarriedBoundAC0`: on every AC trace with the unlock given at any write mode (`ACLocalRunU m u`,
  every unlock oracle, so every lawful stage) whose honest signers are unforgeable
  (`HonestObjects`), every payload an honest node's `ac_proposal` returns carries at most
  `|H| + 2·|Hᶜ|` distinct votes (its votes and support votes together): the pool keeps at most
  two distinct votes per validator and slot, and an honest validator signs one vote per slot
  (`SigningRateAC0`). Without `HonestObjects` a pool may hold votes attributed to an honest
  validator that it never sent, and the bound is only `2n`.
* `LockMemoryAC0`, `LockMemoryERAC0`, `LockMemoryCertAC0`: on the runs of each lawful lock store
  stage over its own SA at a write mode `m` without the optimistic write (`m.optimistic =
  false`): the parent's (`ACLocalRunU m (parentOracleM sp m tr)`), evidence-release's
  (`evidenceReleaseSAM`) and the late-certificate rule's (`certRecoverySAM`). At every cut, every
  honest node
  * holds at most `lockBound m = (fast arm ? 2 : 1) · k` unexpired locks (`lockMemory`,
    `lockMemoryW`, counted in `ℕ∞`), at every formation width;
  * saves no row of a slot `≥ slot(t)` (no future rows);
  * holds at most `max m.width 1` working saved rows (`savedMemory m.width`, `countMemory
    m.width`): the rows of the slots `slot(t) − max m.width 1 ≤ j` that a later update can still
    read. These are row counts, not stored bytes (the rows below the window stay in the state)
    and not roots per row (an evidence-release row holds a count for each scored block).

**Why the lock bound is `(fast arm ? 2 : 1) · k`.** Without the optimistic write, locks are
written only by the update of slot `j = s − 1` at `t_s + 2Δ`: at most one fast and one slow lock,
each of slot `j` and expiry at most `j + k` (the slow expiry is `j + k` at every width). A lock
unexpired at `t` has `slot(t) ≤ expiry ≤ j + k`, and `j ≤ slot(t) − 1`, so `j` ranges over `k`
slots. One tick per node and time (`TickOnce`, supplied by the run's `tick_unique`) makes the
update of each slot one call; the unlock and the move to viable ancestors map each lock to one
lock, so they never add to the count. With the unlock given by an arbitrary oracle the count is
not bounded (`UnlockRel` allows one input lock to reappear on every ancestor of its target), so
the lock claims are stated per stage, not per oracle.

**The optimistic modes are outside these claims.** The parent's write mode and `slowOnly k true`
get no lock or row claim here. The optimistic confirmation writes a fast lock of slot `slot(t)` at
every receipt before `t_s + 2Δ`, on the deepest block with three quarters of the slot's voters
that conflicts with no live lock, with the current fast expiry; successive receipts can select
different blocks and expiries, and the earlier locks are kept, so no bound in `n` and `k` follows
from the argument above.

**Not claimed.** The late-certificate rule's archive keeps every received vote of every slot (at
most two per validator and slot) until a restart, so its size grows with the slots; it has no
claim here.

**Registry rows** (the generic coordinate of `Comparison/Cost` each Tier A claim stands for; `⊤`:
no claim):

* `CarriedBoundAC0`: `CarriedBound`, role class `RoleClass.duty` of the vote kind, at `(h, f)`:
  `h + 2f`, every mode; role class `RoleClass.proposer`: `0` (the payload holds votes only).
* `LockMemoryAC0` (parent stage), `LockMemoryERAC0` (evidence-release), `LockMemoryCertAC0`
  (late certificate), each at `m.optimistic = false`: `LockMemory`'s `locks` field at
  `κ = lockBound m` and its `saved` field in working rows (the rows in the read window) at
  `κ' = max m.width 1`; the stored rows (every row the state holds): `⊤`.
* The parent's write mode (optimistic): `LockMemory` `κ = ⊤`, `κ' = ⊤`.
* `slowOnly k true`: `LockMemory` `κ = ⊤`, `κ' = ⊤`.
* The late-certificate archive, every mode: `⊤`.

Here `h = |H|` and `f = |Hᶜ|`. At width `k` (`WriteMode.parent sp`'s width, `slowOnly k _`)
the row bound is `κ' = k`; it is at most `k` at every width `≤ k`. The saved bound counts rows,
not roots per row.

All static (constant `H`). -/

namespace Consensus.Goldilocks.Comparison

open SA EvidenceRelease LateCertificate

/-- **One tick per honest node and time** on an AC trace (the run's `tick_unique`). -/
def TickOnce {P : Params} {FGP : Type} {A : ACInterface P FGP} (tr : ACTrace A)
    (H : Set (Fin P.n)) : Prop :=
  ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel A), tr.CallAt y i ℓ → tr.CallAt y j ℓ' → ℓ.call = .tick →
    ℓ'.call = .tick → tr.time i = tr.time j → i = j

/-- The lock bound at a write mode without the optimistic write: one slow lock, and one fast lock
with the fast arm, for each of the last `k` slots. -/
def lockBound (sp : SAParams) (m : WriteMode) : ℕ := (if m.fastArm then 2 else 1) * sp.k

/-- **Tier A carried bound** (static, every write mode and unlock oracle): on every AC trace with
the unlock given (`ACLocalRunU m u`) whose honest signers are unforgeable (`HonestObjects`), every
payload an honest node's `ac_proposal` returns (at the locks `u k` of its call) carries at most
`|H| + 2·|Hᶜ|` distinct votes. Stands for `Consensus.Comparison.CarriedBound`'s vote class at
`h + 2f`. -/
def CarriedBoundAC0 : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (u : Nat → Set Lock) (FGP : Type) (ro : ReplayOrder sp FGP)
    (proposer : Nat → Fin sp.n) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACLocalRunU m u H U tr → HonestObjects proposer tr H →
    ∀ y ∈ H, ∀ k ℓ d (pay : Payload sp.n), tr.CallAt y k ℓ → ℓ.call = .proposal →
      (acProposalWith sp (u k) (tr.state y k) ℓ.frame (tr.time k)).2 = some (d, pay) →
      {v : Vote sp.n | v ∈ pay.1 ∨ v ∈ pay.2}.encard ≤ (H.ncard + 2 * Hᶜ.ncard : ℕ)

/-- **Tier A lock memory for the parent's stage** (static, every write mode without the
optimistic write): on every AC trace of the parent's SA at mode `m` (`ACLocalRunU m` at the
parent's unlock oracle at mode `m`, `parentOracleM`) with one tick per honest node and time,
every honest node holds, at every cut, at most `lockBound m` unexpired locks, no saved row of a
slot `≥ slot(t)`, and at most `max m.width 1` working saved rows. Stands for
`Consensus.Comparison.LockMemory`'s `locks` at `κ = lockBound m` and `saved` (working rows) at
`κ' = max m.width 1` (`k` at width `k`). -/
def LockMemoryAC0 : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro),
    m.optimistic = false → ACLocalRunU m (parentOracleM sp m tr) H U tr → TickOnce tr H →
    ∀ y ∈ H, ∀ i, lockMemory sp (tr.state y i) (tr.time i) ≤ (lockBound sp m : ℕ) ∧
      (∀ j : Int, (tr.state y i).saved j ≠ none → j < sp.slot (tr.time i)) ∧
      savedMemory sp m.width (tr.state y i) (tr.time i) ≤ (max m.width 1 : ℕ)

/-- **Tier A lock memory for evidence-release** (static, every write mode without the optimistic
write): on every AC trace of evidence-release's SA at mode `m` with one tick per honest node and
time, every honest node holds, at every cut, at most `lockBound m` unexpired weighted locks, no
saved count of a slot `≥ slot(t)`, and saved counts in at most `max m.width 1` working rows.
Stands for `Consensus.Comparison.LockMemory`'s `locks` at `κ = lockBound m` and `saved`
(working rows) at `κ' = max m.width 1`. -/
def LockMemoryERAC0 : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)),
    m.optimistic = false → ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr → TickOnce tr H →
    ∀ y ∈ H, ∀ i, lockMemoryW sp (tr.state y i) (tr.time i) ≤ (lockBound sp m : ℕ) ∧
      (∀ (j : Int) r, (tr.state y i).counts j r ≠ 0 → j < sp.slot (tr.time i)) ∧
      countMemory sp m.width (tr.state y i) (tr.time i) ≤ (max m.width 1 : ℕ)

/-- **Tier A lock memory for the late-certificate rule** (static, every write mode without the
optimistic write): as `LockMemoryERAC0`, on its evidence-release state (its archive is not
bounded: `⊤`). Stands for `Consensus.Comparison.LockMemory`'s `locks` at `κ = lockBound m` and
`saved` (working rows) at `κ' = max m.width 1`. -/
def LockMemoryCertAC0 : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : ACTrace (certRecoverySAM sp m FGP ro)),
    m.optimistic = false → ACLocalRun (certRecoverySAM sp m FGP ro) H U tr → TickOnce tr H →
    ∀ y ∈ H, ∀ i, lockMemoryW sp (tr.state y i).er (tr.time i) ≤ (lockBound sp m : ℕ) ∧
      (∀ (j : Int) r, (tr.state y i).er.counts j r ≠ 0 → j < sp.slot (tr.time i)) ∧
      countMemory sp m.width (tr.state y i).er (tr.time i) ≤ (max m.width 1 : ℕ)

end Consensus.Goldilocks.Comparison

end
