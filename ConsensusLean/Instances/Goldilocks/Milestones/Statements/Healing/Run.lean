module
public import Mathlib.Order.Lattice.Nat
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks

@[expose] public section

/-! # Goldilocks milestone Healing: the run-level healing statements (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex` §"Healing: top-level
statements" (HR.1, `HighOrigin` and `T_heal`) and §"Healing: phase service" (the
HS shared premises, the settled predicate and the constants `D`, `C`, `A`), over the Goldilocks run
(`Spec/Run`, `GoldilocksRun`). The run bundle, H.3 including its bridge vocabulary, HR.2–HR.4,
H.4 and the phase-service statements HS.0–HS.5 are
retired as milestone statements; the statements here are the types of the lemmas the recovery
proofs read.

**Vocabulary.**

* `cutZ` is `c_z = t_{slot(ḡ)+3}`; `HZ` is `H_z`, the greatest `Σ.h_max` of the honest nodes
  after all events at `c_z` (`FirstCutAfter`: the state before the first cut after `c_z`);
  `IsReset` says that `a` is the reset `a_z`, the first time at which an honest validator signs an
  attestation whose height pair has height `H_z + 1` (honest signing is at public times, in ticks,
  so this is the first public time of one); `HighEntries` are the entries of heights `≥ H_z + 1`
  of the honest accepted chains.
* `CatchRun` is `Catch(κ)`, `PropPlus` is `Prop⁺(G_p)` (an honest joined proposal at a slot start
  in every window `[τ, τ + G_p]` from `ḡ`, whose slot-`(s−1)` support references are held by every
  honest node before the vote deadline `t_s + Δ`: the ready-proposer premise), `NoRestartAfter`
  is "no honest restart after `t`"; `HSShared` bundles the HS shared premises (with the
  parameter bound `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`); `D_HS`, `C_HS`, `A_HS` are the HS constants.
* **The effective phase** (HS shared premises, HR.2) is read over an FG trace at a cut: the
  frontier `m` is the greatest honest `Σ.h_max` (`FrontierAt`); the case (`PhaseCase`) is a gap
  (no justification at `m − 1` on an honest accepted chain), a top `J` (a justification of `J` at
  `m − 1` and no contest) or a contest (`J` justified at `m − 1` and an honest accepted block of
  state height `m` that does not extend `J`). It reads the honest accepted blocks of all nodes, not
  one node's `Σ.F`, so an advance of an honest `Σ.F` changes no phase by definition (HR.2's last
  sentence). Over a run it is read on the FG projection (`projFG`), cut by cut.
  `SettledAt` is the HS settled predicate, `PhaseChanged` a change of the frontier or the case.

"The state at `t`" is the state before the first cut at a time `≥ t` (`FirstCutFrom`); "after
all events at `t`" is the state before the first cut at a time `> t` (`FirstCutAfter`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar declaredSupportVotes)

section Vocabulary

/-- Cut `j` is the first cut after the time `t`: every earlier cut is at a time `≤ t` and cut `j`
is later, so the state before `j` is the state after all events at `t`. -/
def FirstCutAfter {N S L : Type} (tr : Trace N S L) (j : Nat) (t : Time) : Prop :=
  (∀ k < j, tr.time k ≤ t) ∧ t < tr.time j

/-- `c_z = t_{slot(ḡ)+3}`, the cut of the reset (claims HR.1). -/
def cutZ (P : Params) (g : Time) : Time := P.slotTime (P.slotOf (gbar g) + 3)

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Set (Fin P.n))

/-- `H_z` (claims HR.1): the greatest `Σ.h_max` of the honest nodes after all events at `c_z`.
(When no cut follows `c_z`, which `Healthy(g)` excludes, the set is empty and this is `0`.) -/
noncomputable def HZ (g : Time) : Nat :=
  sSup {h | ∃ y ∈ H, ∃ j, FirstCutAfter tr j (cutZ P g) ∧ (tr.state y j).fg.hmax = h}

/-- **The reset `a_z`** (claims HR.1 (c)): `a` is the first time at which an honest validator
signs an attestation whose height pair has height `H_z + 1`. -/
def IsReset (g a : Time) : Prop :=
  (∃ y ∈ H, ∃ k att, tr.SignAt y k att ∧ att.h = HZ tr H g + 1 ∧ tr.time k = a) ∧
    ∀ y ∈ H, ∀ k att, tr.SignAt y k att → att.h = HZ tr H g + 1 → a ≤ tr.time k

/-- The entries of heights `≥ H_z + 1` of the honest accepted chains: the blocks `E` of an honest
tree that are the entry `T_h` of an accepted state of height `h ≥ H_z + 1`. -/
def HighEntries (Hz : Nat) : Set (NodeBlock P A.Payload) :=
  {E | ∃ y ∈ H, ∃ i, E ∈ (tr.state y i).fg.tree ∧ ∃ B ∈ (tr.state y i).fg.tree,
    Hz + 1 ≤ ((tr.state y i).fg.σ B.root).h ∧ ((tr.state y i).fg.σ B.root).Th = E.root}

/-- **`Catch(κ)` over a run** (accepted-old-block catch-up): every block an honest node accepts
at a time `< ḡ` is accepted before `ḡ + κ` by every honest `y` whose `Σ.F` at `ḡ + κ` it extends
(its needed ancestry with it: the FG accepts a block only on a held parent). -/
def CatchRun (g κ : Time) : Prop :=
  ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (gbar g + κ) →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B → ∃ k < j, tr.AcceptAt y k B

/-- No honest restart after `t`. -/
def NoRestartAfter (t : Time) : Prop := ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ t

end Vocabulary

section Constants

variable (sp : ACParams)

/-- The HS constant `D = (8k + 48)Δ + 2G`. -/
def D_HS (G : Time) : Time := (8 * (sp.k : Time) + 48) * sp.Δ + 2 * G

/-- The HS constant `C = D + 4Δδ_t + Δ_F + G + Δ`. -/
def C_HS (ΔF G : Time) : Time := D_HS sp G + 4 * sp.Δ * (sp.toParams.δt : Time) + ΔF + G + sp.Δ

/-- The HS constant `A = 2C + Δ` (`Producer(A)`). -/
def A_HS (ΔF G : Time) : Time := 2 * C_HS sp ΔF G + sp.Δ

end Constants

section Phase

variable {P : Params} {ACP : Type} (tr : FGTrace P ACP) (H : Set (Fin P.n))

/-- The frontier at cut `i` is `m`: the greatest `Σ.h_max` of the honest nodes. -/
def FrontierAt (i m : Nat) : Prop :=
  (∃ y ∈ H, (tr.store y i).hmax = m) ∧ ∀ y ∈ H, (tr.store y i).hmax ≤ m

/-- At cut `i`, `J` is justified at height `h` on an honest accepted chain: an honest node holds
`J` and a block whose state has the justification `(h, J)`. -/
def JustifiedAt (i h : Nat) (J : NodeBlock P ACP) : Prop :=
  ∃ y ∈ H, J ∈ (tr.store y i).tree ∧ ∃ B ∈ (tr.store y i).tree,
    ((tr.store y i).σ B.root).hj = h ∧ ((tr.store y i).σ B.root).J = J.root

/-- At cut `i`, a contest against `J` at `m`: an honest node holds a block of state height `m`
that does not extend `J`. -/
def ContestAt (i m : Nat) (J : NodeBlock P ACP) : Prop :=
  ∃ y ∈ H, ∃ B ∈ (tr.store y i).tree, ((tr.store y i).σ B.root).h = m ∧ ¬ (tr.store y i).Anc J B

/-- The case of an effective phase (claims HR.2 (b), HS shared premises). -/
inductive PhaseCase (β : Type) where
  /-- No justification at `m − 1`. -/
  | gap
  /-- A unique top justification `J` at `m − 1` and no contest. -/
  | top (J : β)
  /-- A contest: a block of height `m` that does not extend the top justification `J`. -/
  | contest (J : β)

/-- The order of the cases: gap, then top `J`, then contest. -/
def PhaseCase.rank {β : Type} : PhaseCase β → Nat
  | .gap => 0
  | .top _ => 1
  | .contest _ => 2

/-- The top justification of a case, if any. -/
def PhaseCase.topJ {β : Type} : PhaseCase β → Option β
  | .gap => none
  | .top J => some J
  | .contest J => some J

/-- **The effective phase at cut `i`** is `(m, c)`: the frontier is `m` and the case is `c`, read
on the honest accepted blocks (not on one node's `Σ.F` or local allowedness). -/
def PhaseAt (i m : Nat) : PhaseCase (NodeBlock P ACP) → Prop
  | .gap => FrontierAt tr H i m ∧ ∀ J, ¬ JustifiedAt tr H i (m - 1) J
  | .top J => FrontierAt tr H i m ∧ JustifiedAt tr H i (m - 1) J ∧ ¬ ContestAt tr H i m J
  | .contest J => FrontierAt tr H i m ∧ JustifiedAt tr H i (m - 1) J ∧ ContestAt tr H i m J

/-- The effective phase changes from cut `i` to cut `j`: the frontier has risen or the case has
changed (no phase at `i` is the phase at `j`). -/
def PhaseChanged (i j : Nat) : Prop :=
  ∀ m c, PhaseAt tr H i m c → ¬ PhaseAt tr H j m c

/-- The FG state `st` holds the defining evidence of the effective phase `(m, c)`: a block of
state height `m`; for a top `J` or a contest, `J` and a block whose state justifies `J` at
`m − 1`; for a contest, also a block of state height `m` that does not extend `J`. -/
def HoldsEvidence (st : Store P ACP) (m : Nat) : PhaseCase (NodeBlock P ACP) → Prop
  | .gap => ∃ B ∈ st.tree, (st.σ B.root).h = m
  | .top J => (∃ B ∈ st.tree, (st.σ B.root).h = m) ∧ J ∈ st.tree ∧
      ∃ B ∈ st.tree, (st.σ B.root).hj = m - 1 ∧ (st.σ B.root).J = J.root
  | .contest J => (∃ B ∈ st.tree, (st.σ B.root).h = m) ∧ J ∈ st.tree ∧
      (∃ B ∈ st.tree, (st.σ B.root).hj = m - 1 ∧ (st.σ B.root).J = J.root) ∧
      ∃ B ∈ st.tree, (st.σ B.root).h = m ∧ ¬ st.Anc J B

end Phase

section Run

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) (H : Set (Fin P.n))

/-- **Settled at `w`** (HS shared premises): `w ≥ max(ḡ + κ, ḡ + 8Δ)`; at `w` every honest
validator is joined and holds the defining frontier, top-`J` and contest evidence of the current
effective phase; and the pre-GST acceptance catch-up is complete (every block an honest node
accepted before `ḡ` is held by every honest node whose `Σ.F` at `w` it extends). -/
structure SettledAt (g κ w : Time) : Prop where
  /-- `w ≥ max(ḡ + κ, ḡ + 8Δ)`. -/
  late : max (gbar g + κ) (gbar g + 8 * P.Δ) ≤ w
  /-- Every honest validator is joined at `w`. -/
  joined : ∀ y ∈ H, tr.JoinedAt y w
  /-- At `w`, every honest node holds the evidence of the effective phase. -/
  evidence : ∀ j, tr.FirstCutFrom j w → ∀ m c, PhaseAt tr.projFG H j m c →
    ∀ y ∈ H, HoldsEvidence (tr.projFG.store y j) m c
  /-- The pre-GST acceptance catch-up is complete at `w`. -/
  catchUp : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
    ∀ y ∈ H, ∀ j, tr.FirstCutFrom j w → Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      ∃ k < j, tr.AcceptAt y k B

end Run

section Goldilocks

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))

/-- **A ready proposal**: the honest proposer `p` of slot `s`, joined at `t_s`, makes its
proposal `B` of slot `s` at cut `k`, and every slot-`(s−1)` support reference of `B` is a block of
slot `≤ s − 1` that every honest node holds before the vote deadline `t_s + Δ` (so `B` is ready
at every honest voter: `vote_ready`'s condition). -/
def ReadyProposal (proposer : Nat → Fin sp.n)
    (p : Fin sp.n) (k s : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  p ∈ H ∧ p = proposer s ∧ tr.JoinedAt p (sp.ts s) ∧ tr.ProposesAt p k B ∧
    B.slot = s ∧
    ∀ x ∈ declaredSupportVotes B, x.slot + 1 = s → ∀ y ∈ H, ∀ j,
      tr.FirstCutFrom j (sp.ts s + sp.Δ) →
      ∃ R ∈ (tr.state y j).fg.tree, R.root = x.head ∧ R.slot + 1 ≤ s

/-- **`Prop⁺(G_p)`** (the HS ready-proposer premise with `G = G_p`): for every trigger `τ ≥ ḡ`
there is a slot `s ≥ 1` with `τ ≤ t_s ≤ τ + G_p` with a ready proposal (`ReadyProposal`). -/
def PropPlus (proposer : Nat → Fin sp.n) (g Gp : Time) : Prop :=
  ∀ τ, gbar g ≤ τ → ∃ (s : Nat) (k : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))),
    1 ≤ s ∧ τ ≤ sp.ts s ∧ sp.ts s ≤ τ + Gp ∧
    ReadyProposal tr H proposer (proposer s) k s B

/-- **The HS shared premises** (claims §"Healing: phase service") other than the two regime
premises (`CatchRun`, `PropPlus`, taken separately): `NoColl` with a genesis whose root is its
digest (the model's reading of `NoColl` for genesis, as C0.3), `Healthy(g)` (with `GST(g)`'s
strict delivery, acceptance relay and attestation convention), no honest restart after `ḡ`, and the
protocol's parameter bound `δ_t ≥ 𝓕 = ⌈(6Δ + Δ_F)/(4Δ)⌉` (from `δ_t ≥ x + 𝓕 + k_F`,
`x, k_F ≥ 0`; `k ≥ 2` and `0 < Δ_F` are carried by `ACParams` and `SyncOn`; no order between
`Δ` and `Δ_F` is assumed), and the committee premises of the slot dictionary `K`: its committee
facts (`Compose.Growing.CommitteeFacts` at the constant honest set: committees of `committeeSize`
members, honest pools and optimistic-check states hold only committee signatures, the frames of
honest nodes carry only members' votes, and an honest node may vote in exactly its committees'
slots) and CS2 for every slot after the slot of `ḡ` (no bound on a committee whose slot starts at
or before `ḡ`). The statements that take it run from `K`'s committee start (`AC.committeeStart`).
Unforgeable
signatures, persistent honest client records and finite event prefixes are laws of the run
(`GoldilocksRun`). -/
structure HSShared (K : AC.CommitteeDict sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (g ΔF : Time) : Prop where
  /-- `NoColl` on the blocks of the run. -/
  noColl : Compose.NoCollRun dg tr
  /-- Genesis's root is its digest (as C0.3 and A1.7 take it): otherwise an honest proposal
  whose digest is the genesis root is refused by every FG, and the healing statements that need
  honest proposals to be accepted (the reset, C1.2, H.3, H.4) fail. -/
  genesisRoot : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg
  /-- `Healthy(g)`. -/
  healthy : tr.HealthyRun H ΔF g
  /-- No honest restart after `ḡ`. -/
  noRestart : NoRestartAfter tr H (gbar g)
  /-- `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)
  /-- The committee facts of `K` (committees of `committeeSize` members, P, the frames of honest
  nodes carry members' votes, and the vote gate), at the constant honest set. -/
  committee : Compose.Growing.CommitteeFacts tr (fun _ => H) K
  /-- CS2 for the slots after `ḡ`: fewer than half of each such slot committee is faulty. -/
  twoK : ∀ s : Nat, sp.slot (gbar g) + 1 ≤ s →
    2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard

/-- **A high origin** `(B, j)` (claims HR.4), written at cut `i` of `x`: a write of a fast lock
(fast test or optimistic confirmation) of label `j` at the honest node `x`, joined at the write,
whose stored block `B` has state height `≥ H_z + 1`. The stored block is the selected block `D`
after the move back of `add_locks` (`viable_ancestor` in the frame of the writing call; claims
C1.1, "stored block after the move back"), not the raw selected block. -/
def HighOrigin (g : Time) (x : Fin sp.n) (i j : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  x ∈ H ∧ tr.JoinedAt x (tr.time i) ∧
    (∃ CV, Compose.StoredFastLockAt tr x i j B CV) ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

end Goldilocks

/-- **HR.1, cut and reset.** In a Goldilocks run (unforgeable signatures, durable records) under
`Healthy(g)` and `NoColl`, with `c_z = t_{slot(ḡ)+3}` (`≤ ḡ + 12Δ`) and `H_z`:
(a) every honest attestation signed at or before `c_z` has a height pair of height `≤ H_z`; from
`c_z` on, every block `C` that `ac_to_fg` returns at an honest `x` is the block of a live fast
lock of `x` whose label `j` has a fast-lock write at `x` after `ḡ` on a descendant of `C` (A1.5
with `τ = ḡ`; the lock's block is the written block moved back to an ancestor), or, with deep
sources on and no fast-lock candidate, a deep candidate under the deep anchor, which, when its
state height is `≥ H_z + 1`, `x` received after `c_z` (its stamp is later than `c_z`, so with
the deep age guard it is unusable before `D` slots after `c_z`);
(b) the chain of an honest accepted block of state height `≥ H_z + 2` carries an honest
attestation whose height pair has height `H_z + 1`;
(c) if `a` is the reset `a_z`: `a > c_z` and no honest height pair of height `≥ H_z + 1` is
signed before `a`; at the FG update (`fg_attest`) of each honest tick at `a` the accepted
frontier is `≤ H_z + 1`, so every honest attestation signed at `a` has height `≤ H_z + 1`; and
for every entry of height `≥ H_z + 1` the first clause of (K1) of G1.10 holds with
`T₀ = a − Δ`. -/
def CutAndReset : Prop :=
  ∀ (sp : ACParams)
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → tr.HealthyRun H ΔF g → Compose.NoCollRun dg tr →
    cutZ sp.toParams g ≤ gbar g + 12 * sp.Δ ∧
    (∀ y ∈ H, ∀ k att, tr.SignAt y k att → tr.time k ≤ cutZ sp.toParams g →
      att.h ≤ HZ tr H g) ∧
    (∀ x ∈ H, ∀ i ℓ C, AC.ToFGAt tr.projAC x i ℓ C → cutZ sp.toParams g ≤ tr.time i →
      (∃ l ∈ AC.liveLocks sp (tr.state x i).ac.locks ℓ.frame (tr.time i),
        l.fast = true ∧ l.block = C.root ∧
        ∃ i' < i, ∃ B CV, AC.FastLockAt tr.projAC x i' l.slot B CV ∧ gbar g < tr.time i' ∧
          Anc (tr.HonestBlocks H) C B) ∨
      (∃ D a, sp.deepDepth = some D ∧
        AC.deepest ℓ.frame (AC.toFGCandidates sp (tr.state x i).ac ℓ.frame (tr.time i)) = none ∧
        AC.deepAnchor sp (tr.state x i).ac ℓ.frame (tr.time i) = some a ∧
        C ∈ AC.toFGDeepCandidates sp D a (tr.state x i).ac ℓ.frame (tr.time i) ∧
        (HZ tr H g + 1 ≤ ((tr.state x i).fg.σ C.root).h →
          AC.ETime.of (cutZ sp.toParams g) < (tr.state x i).ac.blockStamp C.root))) ∧
    (∀ y ∈ H, ∀ i, ∀ X ∈ (tr.state y i).fg.tree, HZ tr H g + 2 ≤ ((tr.state y i).fg.σ X.root).h →
      ∃ Y, (tr.state y i).fg.Anc Y X ∧ ∃ att ∈ Y.fgPayload, att.val ∈ H ∧ att.h = HZ tr H g + 1) ∧
    ∀ a, IsReset tr H g a →
      cutZ sp.toParams g < a ∧
      (∀ y ∈ H, ∀ k att, tr.SignAt y k att → HZ tr H g + 1 ≤ att.h → a ≤ tr.time k) ∧
      (∀ y ∈ H, ∀ k src signed, tr.CallAt y k (.fg (.attest src signed)) → tr.time k = a →
        (tr.state y k).fg.hmax ≤ HZ tr H g + 1) ∧
      (∀ y ∈ H, ∀ k att, tr.SignAt y k att → tr.time k = a → att.h ≤ HZ tr H g + 1) ∧
      ∀ E ∈ HighEntries tr H (HZ tr H g),
        (Store.namers sp.toParams (Payload sp.n) H tr.projFG (a - sp.Δ) E).ncard <
          sp.toParams.fg.q

section Top

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))

/-- The honest votes of slot `p` (over the AC projection) are all `P`. -/
def Unanimous (p : Nat) (P : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x ∈ H, ∀ j e, AC.VoteAt tr.projAC x j e → e.msg.slot = p → e.msg.head = P.root

/-- `P` is the honest proposal of slot `p` (its proposer is honest) over the AC projection. -/
def HonestProposalRun (proposer : Nat → Fin sp.n)
    (p : Nat) (P : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  proposer p ∈ H ∧ AC.HonestProposal tr.projAC (proposer p) p P

end Top

/-- `T_heal = ḡ + 24Δ + 12C_HS + T_b + 2Θ + 8Δ` (claims H.4), that is
`ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G_p + T_b` with the optimistic confirmation on and
`ḡ + (104k + 616 + 48δ_t)Δ + 12Δ_F + 36G_p + T_b` with it off. -/
def T_heal (sp : ACParams) (g ΔF Gp Tb : Time) : Time :=
  gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp + Tb + 2 * AC.Θ sp + 8 * sp.Δ

end Consensus.Goldilocks.Healing

end
