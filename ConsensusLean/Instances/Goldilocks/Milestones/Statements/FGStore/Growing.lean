module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing

@[expose] public section

/-! # Goldilocks milestone FGStore under growing faults (statements)

The statements of `Statements/FGStore/{Trace,Service}` that bind the honest set, for a
time-indexed honest set `H` (antitone), over `Growing.FGLocalRun`:

* **G1.4**: two nodes, each honest at its own cut, have compatible finalized tips when fewer than
  `2q − n` validators are compromised by the later of the two cuts.
* **G1.10**: the namers of an entry are charged at a consumption horizon `d ≥ T + Δ`, which every
  acceptance the statement covers precedes: the validators compromised by `d`, or signing by `T₀`
  an attestation naming it. The attestations signed in `(T₀, T]` are those of validators honest
  at their signing; no premise excludes a compromise in `(T₀, T]`. The accepting node is honest at
  its cut.
* **The good window**: the proposal is an honest proposal of a proposer honest at its proposal
  cut. An attestation of the window is on the parent's chain, or, when its signer is honest at the
  window's deadline `t_{u+a} + 6Δ`, signed by that deadline (`emitted`).
* **G1.6–G1.8**: as the static statements, over the growing-fault good window; the node of G1.8 is
  honest at its cut.

The statements without an honest set (FGSafety, FGStore part 1, `CacheAcceptance`) are unchanged
and are not restated. At `H := fun _ => H₀` each statement here implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Store.Growing

variable (P : Params) (ACP : Type)

/-- **G1.4 under growing faults, finalized safety.** -/
def FinalizedSafety : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    ∀ y z i j, y ∈ H (tr.time i) → z ∈ H (tr.time j) →
      (H (max (tr.time i) (tr.time j)))ᶜ.ncard < 2 * P.fg.q - P.n →
      Compatible U (tr.store y i).F (tr.store z j).F

/-- The validators that name the entry block `E` by `T₀`, charged at the horizon `d`: compromised
by `d`, or signing by `T₀` an attestation whose target is `E`. -/
noncomputable def namers (H : Time → Set (Fin P.n)) (tr : FGTrace P ACP) (T₀ d : Time)
    (E : NodeBlock P ACP) : Set (Fin P.n) :=
  {v | v ∉ H d ∨ ∃ j a, tr.SignAt v j a ∧ tr.time j ≤ T₀ ∧ a.T = E.root}

/-- **G1.10 under growing faults, quorum-free entries (the core).** -/
def QuorumFreeEntries : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP)
    (𝓔 : Set (NodeBlock P ACP)) (T₀ T d : Time) (y : Fin P.n),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr → P.IsPublic T₀ → P.IsPublic T →
    T + P.Δ ≤ d → (∀ E ∈ 𝓔, (namers P ACP H tr T₀ d E).ncard < P.fg.q) →
    (∀ v j a, v ∈ H (tr.time j) → tr.SignAt v j a → T₀ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ 𝓔, a.T ≠ E.root) →
    ∀ i X, y ∈ H (tr.time i) → tr.AcceptAt y i X →
      (tr.time i < T + P.Δ ∨
        (tr.time i = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
    ∀ E ∈ 𝓔, ∀ h, ∀ A ∈ (tr.store y (i + 1)).tree, (tr.store y (i + 1)).Anc A X →
      ((tr.store y (i + 1)).σ A.root).h = h → ((tr.store y (i + 1)).σ A.root).Th = E.root →
      ((tr.store y (i + 1)).σ X.root).h = h ∧ ((tr.store y (i + 1)).σ X.root).Th = E.root ∧
        ((tr.store y (i + 1)).σ X.root).prog.card < P.fg.q

/-- `B` is an honest proposal at cut `i` with parent `Pr`, by a proposer honest at that cut. -/
def HonestProposal (H : Time → Set (Fin P.n)) (tr : FGTrace P ACP) (p : Fin P.n) (i : Nat)
    (B Pr : NodeBlock P ACP) : Prop :=
  p ∈ H (tr.time i) ∧ tr.AcceptAt p i B ∧ B.proposer = p ∧ P.slotTime B.slot = tr.time i ∧
    Pr ∈ (tr.store p i).tree ∧ B.parent = some Pr.root ∧
    ∀ r ∈ (tr.store p i).atts, ((tr.store p i).σ Pr.root).validAtt r →
      ¬ (tr.store p i).OnChain Pr r → r ∈ B.fgPayload

/-- **The good window under growing faults.** As `Store.GoodWindow`, with the honest proposal of
a proposer honest at its proposal cut, and `emitted` reading the signer's honesty at the window's
deadline `t_{u+a} + 6Δ`. -/
structure GoodWindow (H : Time → Set (Fin P.n)) (tr : FGTrace P ACP) (cF : Nat)
    (T : NodeBlock P ACP) (a kF : Nat) (p : Fin P.n) (i : Nat) (Bs Pr : NodeBlock P ACP)
    (R : Finset (FG.Att P.n)) : Prop where
  /-- P1, P5: an honest proposal. -/
  proposal : HonestProposal P ACP H tr p i Bs Pr
  /-- `T` is an entry block at `p`. -/
  entry : IsEntry P ACP (tr.store p i) T
  /-- P1: the parent extends `T`. -/
  extends_entry : (tr.store p i).Anc T Pr
  /-- P1: the slot is in the window. -/
  window : T.slot + a + cF ≤ Bs.slot ∧ Bs.slot ≤ T.slot + a + cF + kF
  /-- P2: the attestations' validators weigh at least `q`. -/
  quorum : P.fg.q ≤ (R.image FG.Att.val).card
  /-- P2: target attestations for `E`, carrying `P_E` at an entry whose previous height is
  justified. -/
  fgAtts : ∀ r ∈ R, r.h = ((tr.store p i).σ T.root).h ∧ r.T = T.root ∧ r.timeout = false ∧
    (((tr.store p i).σ T.root).previousHeightJustified →
      r.fin = some (((tr.store p i).σ T.root).hj, ((tr.store p i).σ T.root).J))
  /-- P2: on the chain already, or, for a signer honest at the deadline `t_{u+a} + 6Δ`, signed by
  that deadline. -/
  emitted : ∀ r ∈ R, (tr.store p i).OnChain Pr r ∨
    (r.val ∈ H (P.slotTime (T.slot + a) + 6 * P.Δ) →
      ∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ P.slotTime (T.slot + a) + 6 * P.Δ)
  /-- P3–P4: on the chain already, or in the proposer's pool before its proposal. -/
  pooled : ∀ r ∈ R, (tr.store p i).OnChain Pr r ∨ r ∈ (tr.store p i).atts
  /-- P6. -/
  params : a + cF + kF ≤ P.δt ∧ 1 ≤ FG.FGParams.KW

/-- **G1.6 under growing faults (theorem A).** -/
def PreviousHeightJustifiedEntry : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    ∀ (cF : Nat) (T : NodeBlock P ACP) (a kF : Nat) (p : Fin P.n)
      (i : Nat) (Bs Pr : NodeBlock P ACP) (R : Finset (FG.Att P.n)),
    GoodWindow P ACP H tr cF T a kF p i Bs Pr R →
    ((tr.store p i).σ T.root).previousHeightJustified →
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      ((tr.store p (i + 1)).σ X.root).F = ((tr.store p i).σ T.root).J ∧
      ((tr.store p (i + 1)).σ X.root).hF = ((tr.store p i).σ T.root).hj

/-- **G1.7 under growing faults (theorem B).** -/
def PreviousHeightNotJustifiedEntry : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    ∀ (cF : Nat) (T : NodeBlock P ACP) (a₀ kF : Nat) (p : Fin P.n)
      (i : Nat) (Bs Pr : NodeBlock P ACP) (R : Finset (FG.Att P.n)),
    GoodWindow P ACP H tr cF T a₀ kF p i Bs Pr R →
    ¬ ((tr.store p i).σ T.root).previousHeightJustified →
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      (((tr.store p i).σ T.root).h, T.root) ∈ ((tr.store p (i + 1)).σ X.root).pending ∧
      ((tr.store p (i + 1)).σ X.root).h = ((tr.store p i).σ T.root).h + 1 ∧
      ((tr.store p (i + 1)).σ X.root).Th = X.root ∧
      ((tr.store p (i + 1)).σ X.root).previousHeightJustified ∧
      ∀ (a₁ : Nat) (p₁ : Fin P.n) (i₁ : Nat) (Bs₁ Pr₁ : NodeBlock P ACP)
        (R₁ : Finset (FG.Att P.n)), GoodWindow P ACP H tr cF X a₁ kF p₁ i₁ Bs₁ Pr₁ R₁ →
        ∃ Z ∈ (tr.store p₁ (i₁ + 1)).tree, (tr.store p₁ (i₁ + 1)).Anc Z Bs₁ ∧
          ((tr.store p₁ (i₁ + 1)).σ Z.root).F = T.root ∧
          ((tr.store p₁ (i₁ + 1)).σ Z.root).hF = ((tr.store p i).σ T.root).h

/-- **G1.8 (a) under growing faults, crossing bound**, at a node honest at its cut. -/
def Crossing : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    ∀ y (k : Nat) (C T : NodeBlock P ACP) (g r : Nat), y ∈ H (tr.time k) →
    C ∈ (tr.store y k).tree → IsEntry P ACP (tr.store y k) T → (tr.store y k).Anc T C →
    1 ≤ g → 1 ≤ r → T.slot + max P.δt r + g - 1 ≤ C.slot →
    (∀ w, T.slot < w → w + g - 1 ≤ C.slot →
      ∃ (Y Pr : NodeBlock P ACP) (p : Fin P.n) (j : Nat), HonestProposal P ACP H tr p j Y Pr ∧
        (tr.store y k).Anc Y C ∧ w ≤ Y.slot ∧ Y.slot ≤ w + g - 1 ∧
        (T.slot + r ≤ Y.slot →
          P.fg.q ≤ (((tr.store p j).atts.filter fun x =>
            x.h = ((tr.store y k).σ T.root).h ∧ x.T = T.root).map FG.Att.val).toFinset.card)) →
    ∃ X ∈ (tr.store y k).tree, (tr.store y k).Anc T X ∧ (tr.store y k).Anc X C ∧
      ((tr.store y k).σ T.root).h < ((tr.store y k).σ X.root).h ∧
      X.slot ≤ T.slot + max P.δt r + g - 1

/-- **G1.8 (b) under growing faults, coverage after failed entries.** -/
def Coverage : Prop :=
  ∀ (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr →
    ∀ (cF : Nat) (T₁ T : NodeBlock P ACP) (a₀ kF : Nat) (p : Fin P.n)
      (i : Nat) (Bs Pr : NodeBlock P ACP) (R : Finset (FG.Att P.n)),
    GoodWindow P ACP H tr cF T a₀ kF p i Bs Pr R →
    ¬ ((tr.store p i).σ T.root).previousHeightJustified →
    IsEntry P ACP (tr.store p i) T₁ → (tr.store p i).Anc T₁ T → T₁ ≠ T →
    (∀ Y, IsEntry P ACP (tr.store p i) Y → (tr.store p i).Anc T₁ Y → (tr.store p i).Anc Y T →
      Y ≠ T₁ → ¬ ((tr.store p i).σ Y.root).previousHeightJustified) →
    ∀ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X →
      (tr.store p (i + 1)).Anc X Bs →
    ∀ (a₁ : Nat) (p₁ : Fin P.n) (i₁ : Nat) (Bs₁ Pr₁ : NodeBlock P ACP)
      (R₁ : Finset (FG.Att P.n)), GoodWindow P ACP H tr cF X a₁ kF p₁ i₁ Bs₁ Pr₁ R₁ →
      ∃ Z ∈ (tr.store p₁ (i₁ + 1)).tree, (tr.store p₁ (i₁ + 1)).Anc Z Bs₁ ∧
        Z.slot ≤ T₁.slot + (T.slot - T₁.slot) + (a₀ + cF + kF) + (a₁ + cF + kF) ∧
        ∃ F ∈ (tr.store p₁ (i₁ + 1)).tree, F.root = ((tr.store p₁ (i₁ + 1)).σ Z.root).F ∧
          (tr.store p₁ (i₁ + 1)).Anc T₁ F

/-- The FGStore trace statements under growing faults. -/
structure FGStoreTraceAt : Prop where
  finalizedSafety : FinalizedSafety P ACP
  quorumFreeEntries : QuorumFreeEntries P ACP

/-- The FGStore service statements under growing faults (`CacheAcceptance` binds no honest set
and is the static one). -/
structure FGStoreServiceAt : Prop where
  previousHeightJustifiedEntry : PreviousHeightJustifiedEntry P ACP
  previousHeightNotJustifiedEntry : PreviousHeightNotJustifiedEntry P ACP
  crossing : Crossing P ACP
  coverage : Coverage P ACP

/-- **FGStore, part 2, under growing faults.** -/
def FGStoreTrace : Prop := ∀ (P : Params) (ACP : Type), FGStoreTraceAt P ACP

/-- **FGStore, part 3, under growing faults.** -/
def FGStoreService : Prop := ∀ (P : Params) (ACP : Type), FGStoreServiceAt P ACP

end Consensus.Goldilocks.Store.Growing

end
