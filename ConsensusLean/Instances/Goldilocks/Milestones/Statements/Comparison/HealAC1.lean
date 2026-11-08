module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Candidates
public import ConsensusLean.Comparison.HealProfile

@[expose] public section

/-! # Slice 1 at Tier A: activity, participation and the held split (statements)

The Tier A Slice 0 heal profile (`HealAC.lean`) with Slice 1's coordinates (`Comparison/
HealProfile.lean`, `HealQ`), over AC traces of the Goldilocks SA with the unlock given at every
write mode of width `k`, and over the candidate lock rules' own runs (`Candidates.lean`). The heal
claim is Slice 0's proposal-inclusion heal; the new coordinates only add premises.

* **AC-call activity** (`ActiveAC`, `activityAC`, `activityFromAC`): a Tier A specialization of
  Slice 1's charging rule (first origin, duty floor), not Slice 1's raw-receipt activity. The signed
  contents are votes (signed by `v.val`) and blocks (signed by their proposer); a node of `H`
  receives a content at an AC call that passes it in: an AC message (`message v`), or a block
  (`block B`) with every vote of its payload (`blockVotes B`), whether or not the handler admits it.
  It does not see contents buffered or rejected before any AC call, arbitrary outer containers, or
  signatures inside the FG payload; a restart's replay of frame blocks, or a frame's provenance, is
  no receipt. A content's charging time is `max t₀ t_s`, with `t₀` its first AC-call receipt by a
  node of `H` and `t_s` the start of its slot. A validator is active on a window when it is outside
  `H` and some content it signs has its charging time in the window; at Tier A every validator
  outside `H` is treated as Byzantine, so a validator of `Hᶜ` that only sleeps and votes is charged
  too. No equality with Slice 1's `activity` is claimed: relating the two (each counted content's
  first network receipt, at any depth, to its first AC call) is a separate transport obligation.
* **The Tier A hold** (`HoldAC G b₀ g`): no node of `H` of one group receives at an AC call before
  `g` a content signed by a validator of the other group whose first release under **the Tier A
  release convention** (`HonestReleaseAC`: the vote's `VoteAt` emission by its own node in `H`, or
  the block's passing to its own proposer's `ac_on_block`) is at `b₀ ≤ t₀ < g` (`HeldOriginAC`).
  The convention is an operational surrogate for Slice 1's first signer release at any nesting
  depth, not a network release; relating them is a transport obligation. The window is the send
  cut of the Slice 0 premise `SyncAC` on `[0, b₀ − 1]`, deliberately not Slice 1's deadline cut
  (`b₀ < t₀ + ΔAC − 1`): content released before `b₀` is owed by that premise. The Tier A hold is
  weaker than Slice 1's, so its class is larger; no equivalence, coverage or common domain with
  Slice 1's held class is claimed.
* `HealQ.slice0 q`: the Slice 0 point `⟨L, fcap, a.async⟩`.
* `Slice1AC q b₀ g tr H`: the hold for `splitHeld`, activity at most `hpre` on `[0, ḡ)` and at most
  `hpost` from `ḡ`, and `m ≤ |Hᶜ|` (with `|Hᶜ| ≤ fcap` from Slice 0's clause, `fcap` caps `|Hᶜ|`,
  the Tier A `nacap`).
* `IncidentAC1 m u q b₀ g` := `IncidentAC0 m u q.slice0 b₀ g` and `Slice1AC` on the trace;
  `HealProfileAC1 sp d`: monotone `d`, and Slice 0's heal claim at `t_p ≥ ḡ + d(q)·Δ` on every run
  with the incident premises at `q`, at every width-`k` mode and unlock oracle;
  `IncidentAC1Mono`: the order of `HealQ` implies inclusion of the incident premises.
* `acFree1` (`8k + 4` at `2·fcap < n`, every `hpre`, `hpost`, `m`) and `HealProfileAC1Free`. A
  bound below `8k + 4` that depends on `h` or `m` is not stated here: it is the template's slot for
  short-asynchrony healing, which is open.
* Over candidate runs: `IncidentER1`, `IncidentCert1` (`IncidentER0`, `IncidentCert0` and
  `Slice1AC` on the forgotten trace), `HealProfileER1At`, `HealProfileCert1At`, the free
  instances at every width-`k` mode, and the named rules at their modes: evidence release and the
  late certificate at the parent's mode, minimal-ac (`slowOnly k false`) and minimal-ac with the
  locked optimistic confirmation (`slowOnly k true`). The late certificate is a pool-trace
  statement (`Candidates.lean`): its activity is read on the forgotten trace too.

All static (constant `H`). -/

namespace Consensus.Goldilocks.Comparison

open SA EvidenceRelease LateCertificate Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### Activity and the hold on an AC trace -/

/-- A signed content of the AC: a vote, or a block. -/
inductive ContentAC (sp : SAParams) (FGP : Type) where
  | vote (v : Vote sp.n)
  | block (B : Blk sp.n FGP)

namespace ContentAC

/-- The signer of a content: the vote's validator, the block's proposer. -/
def signer : ContentAC sp FGP → Fin sp.n
  | .vote v => v.val
  | .block B => B.proposer

/-- The slot of a content (its duty's slot). -/
def slot : ContentAC sp FGP → Nat
  | .vote v => v.slot
  | .block B => B.slot

end ContentAC

/-- The call of an AC trace passes content `c` in: the AC message `v` (a `message v` call), or
the block `B` (a `block B` call), and the votes of its payload. -/
def CallReceives (call : (goldilocksSA sp FGP ro).Call) (c : ContentAC sp FGP) : Prop :=
  match c with
  | .vote v => call = .message v ∨ ∃ B, call = .block B ∧ v ∈ blockVotes B
  | .block B => call = .block B

/-- A node of `H` receives content `c` at time `t`: at a call of that time that passes it in. -/
def ReceiptAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (c : ContentAC sp FGP) (t : Time) :
    Prop :=
  ∃ z ∈ H, ∃ k ℓ, tr.CallAt z k ℓ ∧ tr.time k = t ∧ CallReceives ℓ.call c

/-- `t₀` is the first receipt of `c` by a node of `H`. -/
def FirstReceiptAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (c : ContentAC sp FGP)
    (t₀ : Time) : Prop :=
  ReceiptAC tr H c t₀ ∧ ∀ t, ReceiptAC tr H c t → t₀ ≤ t

/-- The charging time of `c` first received at `t₀`: `max t₀ t_s`, with `t_s` the start of its
slot (the duty floor). -/
def chargeAC (c : ContentAC sp FGP) (t₀ : Time) : Time := max t₀ (sp.ts c.slot)

/-- Validator `x` is **active** (AC-call activity) at charging times satisfying `W`: it is outside
`H`, and some content it signs has its first AC-call receipt by `H` at `t₀` with charging time in
`W`. Not Slice 1's raw-receipt activity (module docstring). -/
def ActiveAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (W : Time → Prop) (x : Fin sp.n) :
    Prop :=
  x ∉ H ∧ ∃ c t₀, c.signer = x ∧ FirstReceiptAC tr H c t₀ ∧ W (chargeAC c t₀)

/-- **AC-call activity** on `[a, b)`: the number of validators active there (`ActiveAC`). -/
noncomputable def activityAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a b : Time) : ℕ :=
  {x | ActiveAC tr H (fun t => a ≤ t ∧ t < b) x}.ncard

/-- **AC-call activity** on `[a, ∞)`. -/
noncomputable def activityFromAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (a : Time) : ℕ :=
  {x | ActiveAC tr H (fun t => a ≤ t) x}.ncard

/-- **The Tier A release convention**: content `c` is released honestly at `t` when its signer is
in `H` and, at a cut of time `t`, its own node emits the vote (`VoteAt`), or passes the block to its
own `ac_on_block`. An operational surrogate, not a generic network release (Slice 1 reads the first
release by the signer at any nesting depth). -/
def HonestReleaseAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (c : ContentAC sp FGP)
    (t : Time) : Prop :=
  c.signer ∈ H ∧
    match c with
    | .vote v => ∃ i e, VoteAt tr v.val i e ∧ e.msg = v ∧ tr.time i = t
    | .block B => ∃ i, tr.AcceptAt B.proposer i B ∧ tr.time i = t

/-- **A held origin at Tier A** for the incident `[b₀, g)`: the first release of `c` under the
Tier A release convention is at `b₀ ≤ t₀ < g`, the send cut of the premise `SyncAC` on
`[0, b₀ − 1]` (deliberately not Slice 1's deadline cut). -/
def HeldOriginAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (b₀ g : Time)
    (c : ContentAC sp FGP) : Prop :=
  ∃ t₀, HonestReleaseAC tr H c t₀ ∧ (∀ t, HonestReleaseAC tr H c t → t₀ ≤ t) ∧ b₀ ≤ t₀ ∧ t₀ < g

/-- **The Tier A hold** of the split `G` for the incident `[b₀, g)`: no node of `H` receives at an
AC call before `g` a content signed by a validator of the other group with a held origin at Tier A
(`HeldOriginAC`). Weaker than Slice 1's content-origin hold. -/
def HoldAC (G : Fin sp.n → Bool) (H : Set (Fin sp.n)) (b₀ g : Time) (tr : SATrace sp FGP ro) :
    Prop :=
  ∀ z ∈ H, ∀ k ℓ c, tr.CallAt z k ℓ → tr.time k < g → CallReceives ℓ.call c →
    G c.signer ≠ G z → ¬ HeldOriginAC tr H b₀ g c

/-- The hold clause of a class on an AC trace: `HoldAC` for `splitHeld G`, nothing otherwise. -/
def HoldACOn (H : Set (Fin sp.n)) (b₀ g : Time) (tr : SATrace sp FGP ro) :
    IncidentClass (Fin sp.n) → Prop
  | .splitHeld G => HoldAC G H b₀ g tr
  | .any => True
  | .split _ => True

/-! ### The Tier A incident premises at Slice 1 -/

/-- The Slice 0 point of a Slice 1 point: `⟨L, fcap, a.async⟩`. -/
def _root_.Consensus.Comparison.HealQ.slice0 {V : Type} (q : HealQ V) : Slice0Q V :=
  ⟨q.L, q.fcap, q.a.async⟩

/-- **The Slice 1 coordinates on an AC trace** at `q` with incident `[b₀, g)`: the class's hold,
AC-call activity at most `hpre` on `[0, ḡ)` and at most `hpost` from `ḡ`, and at least `m`
validators outside `H`. -/
def Slice1AC (q : HealQ (Fin sp.n)) (b₀ g : Time) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) :
    Prop :=
  HoldACOn H b₀ g tr q.a ∧ activityAC tr H 0 (gbar g) ≤ q.hpre ∧
    activityFromAC tr H (gbar g) ≤ q.hpost ∧ q.m ≤ Hᶜ.ncard

/-- **Tier A Slice 1 incident premises** at `q`, mode `m` and unlock oracle `u`: the Slice 0
premises at `q.slice0` (H.1's premises with the unlock given, `H` awake from `0`,
`|Hᶜ| ≤ fcap`, `Sync` on `[0, b₀)`, `b₀ ≤ g ≤ b₀ + L·Δ`, the class's in-group `Sync`) and the
Slice 1 coordinates. -/
def IncidentAC1 (m : WriteMode) (u : Nat → Set Lock) (q : HealQ (Fin sp.n)) (b₀ g : Time)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  IncidentAC0 m u q.slice0 b₀ g tr H U proposer ∧ Slice1AC q b₀ g tr H

/-- **The order implies inclusion of the incident premises**: at every SA parameter set, a run with
the premises at `q` has them at every `q' ≥ q`. -/
def IncidentAC1Mono : Prop :=
  ∀ (sp : SAParams) (m : WriteMode) (u : Nat → Set Lock) (FGP : Type) (ro : ReplayOrder sp FGP)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro)
    (proposer : Nat → Fin sp.n) (q q' : HealQ (Fin sp.n)) (b₀ g : Time), q ≤ q' →
    IncidentAC1 m u q b₀ g tr H U proposer → IncidentAC1 m u q' b₀ g tr H U proposer

variable (sp) in
/-- **The Tier A Slice 1 heal profile** with bound `d`: `d` is monotone, and for every write mode
`m` of width `k`, every unlock oracle `u`, every run with the incident premises at `q`, and every
honest proposal `P` of slot `p` with `t_p ≥ ḡ + d(q)·Δ`: (i) every honest vote of slot `p` is `P`,
and (ii) at every call of an honest node at a time `t ≥ t_p + 6Δ` (at `t_p + 6Δ` itself, from its
tick there on), `P ⪯ ac_confirmed` after the call. -/
def HealProfileAC1 (d : Bound (HealQ (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (m : WriteMode), m.width = sp.k → ∀ (u : Nat → Set Lock) (FGP : Type)
    (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n) (q : HealQ (Fin sp.n)) (c : ℕ)
    (b₀ g : Time), d q = c → IncidentAC1 m u q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H → HonestProposalU u tr (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)))

variable (sp) in
/-- The free static bound at Slice 1: `8k + 4` at points with `2·fcap < n`, at every activity and
participation, `⊤` elsewhere. -/
def acFree1 : Bound (HealQ (Fin sp.n)) := fun q =>
  if 2 * q.fcap < sp.n then ((8 * sp.k + 4 : ℕ) : WithTop ℕ) else ⊤

/-- **The free static Tier A instance at Slice 1**: at every SA parameter set, `acFree1`. -/
def HealProfileAC1Free : Prop := ∀ sp : SAParams, HealProfileAC1 sp (acFree1 sp)

/-! ### Over candidate runs -/

/-- **Slice 1 incident premises for a run of the evidence-release SA at mode `m`**:
`IncidentER0` at `q.slice0` and the Slice 1 coordinates, on the forgotten trace. -/
def IncidentER1 (m : WriteMode) (q : HealQ (Fin sp.n)) (b₀ g : Time)
    (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  IncidentER0 m q.slice0 b₀ g tr H U proposer ∧ Slice1AC q b₀ g (projTraceM tr) H

/-- **Slice 1 incident premises for a run of the late-certificate SA at mode `m`**:
`IncidentCert0` at `q.slice0` and the Slice 1 coordinates, on the forgotten (pool) trace. -/
def IncidentCert1 (m : WriteMode) (q : HealQ (Fin sp.n)) (b₀ g : Time)
    (tr : ACTrace (certRecoverySAM sp m FGP ro)) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  IncidentCert0 m q.slice0 b₀ g tr H U proposer ∧ Slice1AC q b₀ g (projTraceCM tr) H

variable (sp) in
/-- **The Tier A Slice 1 heal profile of evidence release at mode `m`** with bound `d`, as
`HealProfileER0At` with `IncidentER1`. -/
def HealProfileER1At (m : WriteMode) (d : Bound (HealQ (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) (proposer : Nat → Fin sp.n)
    (q : HealQ (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentER1 m q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H →
      HonestProposalU (erOracleM tr) (projTraceM tr) (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt (projTraceM tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, (projTraceM tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).ac ℓ.frame (tr.time j)))

variable (sp) in
/-- **The Tier A Slice 1 heal profile of the late certificate at mode `m`** with bound `d`, as
`HealProfileCert0At` with `IncidentCert1`. -/
def HealProfileCert1At (m : WriteMode) (d : Bound (HealQ (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : ACTrace (certRecoverySAM sp m FGP ro)) (proposer : Nat → Fin sp.n)
    (q : HealQ (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentCert1 m q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H →
      HonestProposalU (certOracleM tr) (projTraceCM tr) (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt (projTraceCM tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, (projTraceCM tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceCM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j)))

/-- **Evidence release at Slice 1, free instance at every width-`k` mode**: `acFree1`. -/
def HealProfileER1Free : Prop :=
  ∀ (sp : SAParams) (m : WriteMode), m.width = sp.k → HealProfileER1At sp m (acFree1 sp)

/-- **The late certificate at Slice 1, free instance at every width-`k` mode**: `acFree1`. -/
def HealProfileCert1Free : Prop :=
  ∀ (sp : SAParams) (m : WriteMode), m.width = sp.k → HealProfileCert1At sp m (acFree1 sp)

/-- **Evidence release at the parent's mode, Slice 1**: `acFree1`. -/
def HealProfileERParent1 : Prop :=
  ∀ sp : SAParams, HealProfileER1At sp (WriteMode.parent sp) (acFree1 sp)

/-- **The late certificate at the parent's mode, Slice 1**: `acFree1`. -/
def HealProfileCertParent1 : Prop :=
  ∀ sp : SAParams, HealProfileCert1At sp (WriteMode.parent sp) (acFree1 sp)

/-- **Minimal-ac at Slice 1** (`slowOnly k false`, `w = k` only): `acFree1`. -/
def HealProfileMinimalAC1 : Prop :=
  ∀ sp : SAParams, HealProfileER1At sp (WriteMode.slowOnly sp.k false) (acFree1 sp)

/-- **Minimal-ac with the locked optimistic confirmation at Slice 1** (`slowOnly k true`; evidence
release's release, simulator class `minimal-ac+opt-locked`; integrated-pc's own single release
is not covered): `acFree1`. -/
def HealProfileMinimalACOptLocked1 : Prop :=
  ∀ sp : SAParams, HealProfileER1At sp (WriteMode.slowOnly sp.k true) (acFree1 sp)

end Consensus.Goldilocks.Comparison

end
