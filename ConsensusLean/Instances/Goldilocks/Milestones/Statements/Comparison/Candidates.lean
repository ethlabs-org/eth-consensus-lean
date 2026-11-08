module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealAC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Projection

@[expose] public section

/-! # Slice 0 at Tier A over candidate runs (statements)

The Tier A Slice 0 heal profile restated over each candidate lock rule's **own** runs at a write
mode `m`: a valid AC trace of the candidate's SA (`ACLocalRun` of `evidenceReleaseSAM sp m` or
`certRecoverySAM sp m`), with H.1's other premises read on its forgotten trace (`projTraceM`,
`projTraceCM`: the parent's states, calls and emissions) and the honest proposals read through the
candidate's unlock oracle (`erOracleM`, `certOracleM`: the candidate's own `ac_proposal`). The
heal claim is a proposal-inclusion heal, as `HealProfileAC0`'s: unanimity of slot `p`, and `P` in
every honest confirmed tip of the candidate (`acConfirmed` of its parent state) from `t_p + 6Δ`.

* `IncidentER0 m q b₀ g` / `IncidentCert0 m q b₀ g`: the candidate's run law, the honest objects,
  `DrivenU` at the candidate's oracle, trivial frames, `Healthy(g)` (`HealthyACCore` and
  `2·|Hᶜ| < n`) and `Catch(2Δ)` on the forgotten trace, and `IncidentAC0`'s Slice 0 clauses
  (every member of the constant honest set `H` awake from `0`, `|Hᶜ| ≤ q.fcap`, `Sync` on
  `[0, b₀)`, `b₀ ≤ g ≤ b₀ + q.L·Δ`, the class's in-group `Sync`), all on the forgotten trace.
* `HealProfileER0At sp m d` / `HealProfileCert0At sp m d`: monotone `d`, and the heal claim at
  `t_p ≥ ḡ + d(q)·Δ` on every run with the incident premises at `q`.
* The instances, all at `acFree0` (`8k + 4` at `2·fcap < n`): `HealProfileER0Free` and
  `HealProfileCert0Free` at every width-`k` mode; and the three named rules: `HealProfileERParent0`
  (evidence release at the parent's mode, P1), `HealProfileMinimalAC0` (minimal-ac at `w = k`:
  `slowOnly k false`, P2), `HealProfileMinimalACOptLocked0` (minimal-ac at `w = k` with the locked ¾
  optimistic confirmation and evidence release's release: `slowOnly k true`, P3; integrated-pc's own
  single release is not covered); and `HealProfileCertParent0` (the late certificate at the parent's
  mode, P1).

**The late certificate is a pool-trace statement.** Its premises are read on the forgotten trace,
whose `holdsMsg` is the pool's: `HealthyACCore` there constrains the delivery of the votes the pool
admits: it imposes no forwarding obligation for admissions that exist only in the archive (which
the candidate's own `holdsMsg` holds), and it does not forbid additional archive forwarding.
Archive-aware network transport is unproved: no bridge from an archive-aware network premise exists
yet.

All static (constant `H`). -/

namespace Consensus.Goldilocks.Comparison

open SA EvidenceRelease LateCertificate Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **Slice 0 incident premises for a run of the evidence-release SA at mode `m`**, with H.1's
premises read on its forgotten trace and the honest proposals through its unlock oracle. -/
def IncidentER0 (m : WriteMode) (q : Slice0Q (Fin sp.n)) (b₀ g : Time)
    (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr ∧ HonestObjects proposer (projTraceM tr) H ∧
    DrivenU (erOracleM tr) proposer (projTraceM tr) H ∧ TrivialFrames (projTraceM tr) H ∧
    HealthyACCore (projTraceM tr) H U g ∧ 2 * Hᶜ.ncard < sp.n ∧
    CatchAC (projTraceM tr) H U g (2 * sp.Δ) ∧ (∀ y ∈ H, ∀ t, 0 ≤ t → tr.awake y t) ∧
    Hᶜ.ncard ≤ q.fcap ∧ SyncAC (goldilocksSA sp FGP ro) H U 0 (b₀ - 1) (projTraceM tr) ∧
    b₀ ≤ g ∧ g - b₀ ≤ (q.L : Time) * sp.Δ ∧ GroupSyncACOn H U b₀ g (projTraceM tr) q.a

/-- **Slice 0 incident premises for a run of the late-certificate SA at mode `m`**, with H.1's
premises read on its forgotten trace (a pool trace) and the honest proposals through its unlock
oracle. -/
def IncidentCert0 (m : WriteMode) (q : Slice0Q (Fin sp.n)) (b₀ g : Time)
    (tr : ACTrace (certRecoverySAM sp m FGP ro)) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) : Prop :=
  ACLocalRun (certRecoverySAM sp m FGP ro) H U tr ∧ HonestObjects proposer (projTraceCM tr) H ∧
    DrivenU (certOracleM tr) proposer (projTraceCM tr) H ∧ TrivialFrames (projTraceCM tr) H ∧
    HealthyACCore (projTraceCM tr) H U g ∧ 2 * Hᶜ.ncard < sp.n ∧
    CatchAC (projTraceCM tr) H U g (2 * sp.Δ) ∧ (∀ y ∈ H, ∀ t, 0 ≤ t → tr.awake y t) ∧
    Hᶜ.ncard ≤ q.fcap ∧ SyncAC (goldilocksSA sp FGP ro) H U 0 (b₀ - 1) (projTraceCM tr) ∧
    b₀ ≤ g ∧ g - b₀ ≤ (q.L : Time) * sp.Δ ∧ GroupSyncACOn H U b₀ g (projTraceCM tr) q.a

variable (sp) in
/-- **The Tier A Slice 0 heal profile of evidence release at mode `m`** with bound `d`: `d` is
monotone, and on every run of the evidence-release SA at mode `m` with the incident premises at
`q`, for every honest proposal `P` of slot `p` with `t_p ≥ ḡ + d(q)·Δ`: (i) every honest vote of
slot `p` is `P`, and (ii) at every call of an honest node at a time `t ≥ t_p + 6Δ` (at `t_p + 6Δ`
itself, from its tick there on), `P ⪯ ac_confirmed` after the call. -/
def HealProfileER0At (m : WriteMode) (d : Bound (Slice0Q (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) (proposer : Nat → Fin sp.n)
    (q : Slice0Q (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentER0 m q b₀ g tr H U proposer →
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
/-- **The Tier A Slice 0 heal profile of the late certificate at mode `m`** with bound `d`, as
`HealProfileER0At` over runs of the late-certificate SA (its confirmed tip: `acConfirmed` of its
parent state). -/
def HealProfileCert0At (m : WriteMode) (d : Bound (Slice0Q (Fin sp.n))) : Prop :=
  AdverseMonotone d ∧
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : ACTrace (certRecoverySAM sp m FGP ro)) (proposer : Nat → Fin sp.n)
    (q : Slice0Q (Fin sp.n)) (c : ℕ) (b₀ g : Time), d q = c →
    IncidentCert0 m q b₀ g tr H U proposer →
    ∀ (p : Nat) (P : Blk sp.n FGP), proposer p ∈ H →
      HonestProposalU (certOracleM tr) (projTraceCM tr) (proposer p) p P →
      gbar g + (c : Time) * sp.Δ ≤ sp.ts p →
      (∀ x ∈ H, ∀ j e, VoteAt (projTraceCM tr) x j e → e.msg.slot = p → e.msg.head = P.root) ∧
      (∀ y ∈ H, ∀ j ℓ, (projTraceCM tr).CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
        (tr.time j = sp.ts p + 6 * sp.Δ →
          ∃ k ≤ j, ∃ ℓ', (projTraceCM tr).CallAt y k ℓ' ∧ ℓ'.call = .tick ∧
            tr.time k = tr.time j) →
        Anc U P (acConfirmed sp (tr.post j).er.ac ℓ.frame (tr.time j)))

/-- **Evidence release, free instance at every width-`k` mode**: `acFree0` (`8k + 4` at
`2·fcap < n`). -/
def HealProfileER0Free : Prop :=
  ∀ (sp : SAParams) (m : WriteMode), m.width = sp.k → HealProfileER0At sp m (acFree0 sp)

/-- **The late certificate, free instance at every width-`k` mode**: `acFree0`. -/
def HealProfileCert0Free : Prop :=
  ∀ (sp : SAParams) (m : WriteMode), m.width = sp.k → HealProfileCert0At sp m (acFree0 sp)

/-- **Evidence release at the parent's mode** (P1): `acFree0`. -/
def HealProfileERParent0 : Prop :=
  ∀ sp : SAParams, HealProfileER0At sp (WriteMode.parent sp) (acFree0 sp)

/-- **The late certificate at the parent's mode** (P1): `acFree0`. -/
def HealProfileCertParent0 : Prop :=
  ∀ sp : SAParams, HealProfileCert0At sp (WriteMode.parent sp) (acFree0 sp)

/-- **Minimal-ac** (P2): evidence release with no fast lock at the update and no optimistic
confirmation, `WriteMode.slowOnly k false` (`w = k` only); `acFree0`. Full committees; the fast
increment `c` is vacuous (no fast lock). -/
def HealProfileMinimalAC0 : Prop :=
  ∀ sp : SAParams, HealProfileER0At sp (WriteMode.slowOnly sp.k false) (acFree0 sp)

/-- **Minimal-ac with the locked optimistic confirmation** (P3): minimal-ac `w = k` + locked ¾
optimistic, evidence release's release (simulator class `minimal-ac+opt-locked`),
`WriteMode.slowOnly k true`; `acFree0`. Integrated-pc's own single release is not covered. Full
committees; the fast increment `c` is live here (it is vacuous at P2, with no fast lock). -/
def HealProfileMinimalACOptLocked0 : Prop :=
  ∀ sp : SAParams, HealProfileER0At sp (WriteMode.slowOnly sp.k true) (acFree0 sp)

end Consensus.Goldilocks.Comparison

end
