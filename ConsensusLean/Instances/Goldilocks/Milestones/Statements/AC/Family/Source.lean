module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Locks

/-! # Independent actual-output source packages and supplier-named evidence -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- Supplier-named evidence and eligible source candidates. A supplier must document
the actual meaning of eligible; successful outputs alone are not the full candidate set. -/
structure SourceData (A : SAOperations sp FGP S M) where
  evidence : Fin sp.n → Nat → Blk sp.n FGP → Prop
  eligible : Fin sp.n → Nat → ACLabel A.toAC → Set (Blk sp.n FGP)

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

/-- Viability of an actual candidate source output. -/
def SourceViability (_F : SAFamily A ro) (tr : ACTrace A.toAC)
    (H : Set (Fin sp.n)) : Prop :=
  ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr x i ℓ C →
    C ∈ ℓ.frame.viableTree ℓ.frame.tree

/-- An actual source output has a parent live-lock justification or independent evidence. -/
def SourceLockOrEvidence (D : SourceData A) : Prop :=
  ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr x i ℓ C →
    C ∈ SA.toFGCandidates sp ((F.proj tr).state x i) ℓ.frame (tr.time i) ∨ D.evidence x i C

/-- The observed report-only effect and freshness of a successful output. -/
def SourceReport : Prop :=
  ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr x i ℓ C →
    (F.proj tr).post i = { (F.proj tr).state x i with fgReported := C.root } ∧
    ¬ SA.AncR ℓ.frame C ((F.proj tr).state x i).fgReported

/-- Chain and justification properties quantify the supplier-named candidate set. -/
structure SourceCandidates (D : SourceData A) : Prop where
  output_mem : ∀ x ∈ H, ∀ i ℓ C, ACToFGAt tr x i ℓ C → C ∈ D.eligible x i ℓ
  chain : ∀ x ∈ H, ∀ i ℓ, tr.CallAt x i ℓ → ℓ.call = .toFG →
    ∀ B ∈ D.eligible x i ℓ, ∀ C ∈ D.eligible x i ℓ, Compatible ℓ.frame.tree B C
  viable : ∀ x ∈ H, ∀ i ℓ, tr.CallAt x i ℓ → ℓ.call = .toFG →
    ∀ C ∈ D.eligible x i ℓ, C ∈ ℓ.frame.viableTree ℓ.frame.tree
  justification : ∀ x ∈ H, ∀ i ℓ, tr.CallAt x i ℓ → ℓ.call = .toFG →
    ∀ C ∈ D.eligible x i ℓ,
      C ∈ SA.toFGCandidates sp ((F.proj tr).state x i) ℓ.frame (tr.time i) ∨ D.evidence x i C

/-- Evidence compatibility with a named protected block under the exact transfer premises.
Evidence remains separate from enabled lock-write origins. -/
def SourceEvidenceCompatibility (D : SourceData A) : Prop :=
  ∀ (s m : Nat) (w x : Fin sp.n) (i₀ i : Nat) (P C : Blk sp.n FGP)
    (CV : Set (Vote sp.n)) (ℓ : ACLabel A.toAC),
    w ∈ H → FastWriteEvent F.mode (F.proj tr) w i₀ s P CV →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
      (F.proj tr) →
    Carry (F.proj tr) H U s CV → 2 * Hᶜ.ncard < sp.n → x ∈ H →
    ACToFGAt tr x i ℓ C → D.evidence x i C →
    sp.ts (s + 1 : Nat) + sp.Δ < tr.time i → tr.time i ≤ sp.ts m + sp.Δ →
    (∀ z ∈ H, ∀ j < i, ∀ e, VoteAt (F.proj tr) z j e →
      s < e.msg.slot → e.msg.slot ≤ m → VoteExtends U e.msg P) →
    ((∃ j < i, ∃ ℓ' e, CastAt (F.proj tr) x j ℓ' e ∧ e.msg.slot = s + 1 ∧
        Compatible U ℓ'.frame.F P) ∨
     (∃ k < i, (F.proj tr).RestartAt x k ∧ sp.ts s < (F.proj tr).time k)) →
    Compatible U C P

end Consensus.Goldilocks.SA.FamilyFacts

end
