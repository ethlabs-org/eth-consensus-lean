module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace

@[expose] public section

/-! # Goldilocks milestone FGStore, part 2: FG traces (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (main `a470648c`), the
multi-node FG store nodes over FG traces (`FGLocalRun`): G1.4 (finalized safety) and the core of
G1.10 (quorum-free entries), with the node's own proposal in its scope, which is the test case
§4.7 case 2 of the decomposition note asks the trace contract to express before it is frozen
(the pool at the proposal step, the signing times of its honest rows through unforgeability,
and that no object received at the proposal time precedes the proposal). G1.6–G1.9 and
G1.10's C1.1 scope ((a)–(c), with (K0)) are later statements of this part.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

open Classical in
/-- The validators that are faulty, or honest and sign at or before `T₀` an attestation whose
height pair names `E` (claims G1.10, (K1)). -/
noncomputable def namers (H : Set (Fin P.n)) (tr : FGTrace P ACP) (T₀ : Time)
    (E : NodeBlock P ACP) : Set (Fin P.n) :=
  {v | v ∉ H ∨ ∃ j a, tr.SignAt v j a ∧ tr.time j ≤ T₀ ∧ a.T = E.root}

/-- **G1.4, finalized safety.** In an FG trace (with unforgeable honest signatures and the
honest validators' records serialized, `FGLocalRun`), if the faulty validators number fewer than
`2q − n`, the finalized tips of any two honest nodes, at any two cuts, are compatible (inside the
coherent set `U`). -/
def FinalizedSafety : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → Hᶜ.ncard < 2 * P.fg.q - P.n →
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j, Compatible U (tr.store y i).F (tr.store z j).F

/-- **G1.10, quorum-free entries (the core).** Let `𝓔` be a set of blocks, `T₀`, `T` public
times and `y` honest. Assume (K1_𝓔): for every `E ∈ 𝓔` the validators that are faulty or sign at
or before `T₀` an attestation naming `E` have weight less than `q`, and no honest attestation
signed in `(T₀, T]` names a block of `𝓔`. Let `X` be a block that `y` accepts before `T + Δ`,
or its own proposal of the slot that starts at `T + Δ` (accepted in that tick, before any object
received then). If `E ∈ 𝓔` is the entry of a height `h` on the chain of `X` (some accepted
ancestor of `X` has state height `h` and entry `E`), then `E` gets neither a target nor a
progress quorum on that chain, so it is never left there: `X`'s state still has height `h` and
entry `E`, and its progress set (which contains its target set) is below `q`. -/
def QuorumFreeEntries : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP)
    (𝓔 : Set (NodeBlock P ACP)) (T₀ T : Time) (y : Fin P.n),
    FGLocalRun acp₀ H U tr → P.IsPublic T₀ → P.IsPublic T → y ∈ H →
    (∀ E ∈ 𝓔, (namers P ACP H tr T₀ E).ncard < P.fg.q) →
    (∀ v ∈ H, ∀ j a, tr.SignAt v j a → T₀ < tr.time j → tr.time j ≤ T → ∀ E ∈ 𝓔, a.T ≠ E.root) →
    ∀ i X, tr.AcceptAt y i X →
      (tr.time i < T + P.Δ ∨
        (tr.time i = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
    ∀ E ∈ 𝓔, ∀ h, ∀ A ∈ (tr.store y (i + 1)).tree, (tr.store y (i + 1)).Anc A X →
      ((tr.store y (i + 1)).σ A.root).h = h → ((tr.store y (i + 1)).σ A.root).Th = E.root →
      ((tr.store y (i + 1)).σ X.root).h = h ∧ ((tr.store y (i + 1)).σ X.root).Th = E.root ∧
        ((tr.store y (i + 1)).σ X.root).prog.card < P.fg.q

/-- The statements of FGStore part 2 (so far) at parameters `P` and AC payload type `ACP`. -/
structure FGStoreTraceAt : Prop where
  finalizedSafety : FinalizedSafety P ACP
  quorumFreeEntries : QuorumFreeEntries P ACP

/-- **FGStore, part 2 (so far).** The FG trace statements hold at every parameter and AC payload
type. The statements of G1.6–G1.9 over FG traces will extend `FGStoreTraceAt`. -/
def FGStoreTrace : Prop := ∀ (P : Params) (ACP : Type), FGStoreTraceAt P ACP

end Consensus.Goldilocks.Store

end
