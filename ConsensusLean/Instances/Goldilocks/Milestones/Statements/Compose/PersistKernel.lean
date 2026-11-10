module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Trace

@[expose] public section

/-! # Conditional FG persistence kernel (statements only)

The AC supplies its opaque predicate and compatibility of actual sources. The future kernel
proves the FG attestation/cut steps and strong induction; none is assumed here. Times are absolute:
the cut window is `[Ts, T1 + Δ)` and the source window is `(T0, T1]`, without ordering assumptions.
-/

namespace Consensus.Goldilocks.FG.Persist

variable {P : Params} {A : NodeAC P}

/-- Full FG cut invariant: compatible caches, compatible chain justifications, and the height
bound above a deepest common ancestor for an accepted block conflicting with `B`. -/
def CutInv (tr : RunTrace A) (H : Set (Fin P.n))
    (Ts T1 : Time) (B : A.Blk) (k : Nat) : Prop :=
  ∀ y ∈ H, tr.IsCall y k → Ts ≤ tr.time k → tr.time k < T1 + P.Δ →
    (Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) ∧
    ∀ X, tr.AcceptAt y k X →
      let S := (tr.post k).fg
      (∀ E ∈ S.tree, S.Anc E X → ∀ Jb, S.blocks (S.σ E.root).J = some Jb →
        Compatible (tr.HonestBlocks H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocks H) X B →
        ∀ Pc, Anc (tr.HonestBlocks H) Pc X → Anc (tr.HonestBlocks H) Pc B →
          (∀ Q, Anc (tr.HonestBlocks H) Q X → Anc (tr.HonestBlocks H) Q B →
            Anc (tr.HonestBlocks H) Q Pc) →
          (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)

/-- The AC step supplies only its own predicate at the current cut. -/
def VoteStep (tr : RunTrace A) (H : Set (Fin P.n))
    (Ts T1 : Time) (B : A.Blk) (V : Nat → Prop) : Prop :=
  ∀ k, (∀ j < k, V j ∧ CutInv tr H Ts T1 B j) → V k

/-- Compatibility of each actual honest source output, using only strictly earlier cuts. -/
def SourceStep (tr : RunTrace A) (H : Set (Fin P.n))
    (Ts T0 T1 : Time) (B : A.Blk) (V : Nat → Prop) : Prop :=
  ∀ i, (∀ j < i, V j ∧ CutInv tr H Ts T1 B j) →
    ∀ y ∈ H, ∀ (ℓ : ACLabel A) (C : A.Blk),
      tr.CallAt y i (.ac ℓ) → ℓ.call = .toFG →
      (A.toFG (tr.state y i).ac ℓ.frame (tr.time i)).2 = some C →
      T0 < tr.time i → tr.time i ≤ T1 → Compatible (tr.HonestBlocks H) C B

/-- The future induction contract, not a proof of it. K0 is the first-cut cache condition;
K1 bounds namers of conflicting entries strictly above an honest first-cut final cache.
No ordering of the three times or membership of the protected block is assumed. -/
def Contract : Prop :=
  ∀ (tr : RunTrace A) (H : Set (Fin P.n))
    (proposer : Nat → Fin P.n) (sg : A.Msg → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload),
    A.Requirements → Node.LocalRun proposer dg H sg tr →
    (P.genesisBlock A.genesisPayload).RootOk dg → Compose.NoCollRun dg tr →
    ∀ (Ts T0 T1 : Time) (B : A.Blk) (V : Nat → Prop),
    P.IsPublic T0 → P.IsPublic T1 →
    (∀ y ∈ H, ∀ j, Ts ≤ tr.time j → (∀ k < j, tr.time k < Ts) →
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.J B) →
    (∀ E : A.Blk, (¬ Compatible (tr.HonestBlocks H) E B ∧
      ∃ z ∈ H, ∃ j, Ts ≤ tr.projFG.time j ∧ (∀ k < j, tr.projFG.time k < Ts) ∧
        Anc (tr.HonestBlocks H) (tr.projFG.store z j).F E ∧
        E ≠ (tr.projFG.store z j).F) →
      (Store.namers P A.Payload H tr.projFG T0 E).ncard < P.fg.q) →
    VoteStep tr H Ts T1 B V → SourceStep tr H Ts T0 T1 B V →
    ∀ k, V k ∧ CutInv tr H Ts T1 B k

end Consensus.Goldilocks.FG.Persist
