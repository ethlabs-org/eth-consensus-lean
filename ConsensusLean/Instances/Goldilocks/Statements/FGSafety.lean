module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

@[expose] public section

/-! # Goldilocks milestone M₁: FG chain and client safety (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (main `00df7945`),
nodes G0.2, G0.5, G0.7–G0.10, G1.1 and G1.3, against the FG of `Spec/FG/` (fg.tex with
loose BJ and the weakened E1). Every statement is about the pure FG: chains, chain states
and the client; none reads a run. The run-level nodes (the store G0.3/G0.4, finalized
monotone C0.2, honest acceptance G0.6, finalized safety G1.4, the evidence binding G1.5)
are a later milestone, with `Refinement/Defs`. `docs/goldilocks-mapping.md` maps each
field to its node.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.FG

variable (gp : FGParams)

/-- **G1.1, quorum intersection.** Two quorums meet in at least `2q − n` validators,
and `2q − n ≥ n/3`. -/
def QuorumIntersection : Prop :=
  ∀ S₁ S₂ : Finset (Fin gp.n), gp.q ≤ S₁.card → gp.q ≤ S₂.card →
    2 * gp.q - gp.n ≤ (S₁ ∩ S₂).card ∧ gp.n ≤ 3 * (2 * gp.q - gp.n)

/-- **G0.2 (a), (c) part, (d) without the entry blocks, (e), and `Q_target ⊆ Q_prog`.**
(The ancestry `F ⪯ J ⪯ T_h ⪯ L` and the entry blocks `E_j` need parent links, which a chain
list leaves implicit; they come with the run-level milestone.) Every chain state that a
chain reaches: `1 ≤ h`, `h_F ≤ h_j < h`; `h_j = 0` only at genesis (likewise `h_F`); at
most `K_W` pending pairs, strictly increasing in height, each in `(h_F, h_j]`; when the
justification is not finalized it is the newest pending pair; the target bits are
progress bits. -/
def ChainInvariants : Prop :=
  ∀ (c : List (FGBlock gp.n)) (σ : ChainState gp.n), gp.chainState c = some σ →
    1 ≤ σ.h ∧ σ.hF ≤ σ.hj ∧ σ.hj < σ.h ∧
    (σ.hj = 0 → σ.J = gp.genesis) ∧ (σ.hF = 0 → σ.F = gp.genesis) ∧
    σ.pending.length ≤ FGParams.KW ∧ σ.pending.Pairwise (fun p r => p.1 < r.1) ∧
    (∀ p ∈ σ.pending, σ.hF < p.1 ∧ p.1 ≤ σ.hj) ∧
    (σ.hF < σ.hj → σ.pending.getLast? = some (σ.hj, σ.J)) ∧
    σ.target ⊆ σ.prog

/-- **G0.2 (b), (h), (i), height step and entry constancy.** Along one accepted block:
the height grows by at most one; `h_j` and `h_F` do not decrease; while the height stays,
its entry and its justification `(J, h_j)` stay; a new height is entered by the block
itself, and it is bound exactly when the block justified the old height; the entry state
of a bound height has not finalized its predecessor, which is its newest pending pair. -/
def HeightStep : Prop :=
  ∀ (c : List (FGBlock gp.n)) (σ σ' : ChainState gp.n) (B : FGBlock gp.n),
    gp.chainState c = some σ → gp.stateTransition σ B = some σ' →
    (σ'.h = σ.h ∨ σ'.h = σ.h + 1) ∧ σ.hj ≤ σ'.hj ∧ σ.hF ≤ σ'.hF ∧
    (σ'.h = σ.h → σ'.Th = σ.Th ∧ σ'.J = σ.J ∧ σ'.hj = σ.hj) ∧
    (σ'.h = σ.h + 1 → σ'.Th = B.root ∧ (σ'.bound ↔ σ'.hj = σ.h) ∧
      (σ'.bound → σ'.hF < σ'.hj ∧ σ'.pending.getLast? = some (σ'.hj, σ'.J)))

/-- **G0.7 (c), gated consumption (I7 restated).** A chain state that keeps a target
quorum is at a bound height whose predecessor is pending and unfinalized, and its
timeout is not yet due. (The old "a target quorum is consumed" does not hold.) -/
def GatedConsumption : Prop :=
  ∀ (c : List (FGBlock gp.n)) (σ : ChainState gp.n), gp.chainState c = some σ →
    gp.q ≤ σ.target.card →
    σ.bound ∧ (σ.hj, σ.J) ∈ σ.pending ∧ σ.hF < σ.hj ∧ σ.s < σ.ThSlot + gp.δt

/-- **G0.8, finality before the gate (I7-LB).** At a bound height whose predecessor
`(h_j, J)` is pending (pairs strictly increasing, none above `h_j`), a finality quorum
for `h_j` finalizes it in the finality step of the same block, and with a target quorum
the same block justifies. -/
def FinalityBeforeGate : Prop :=
  ∀ σ : ChainState gp.n, σ.bound → (σ.hj, σ.J) ∈ σ.pending →
    σ.pending.Pairwise (fun p r => p.1 < r.1) → (∀ p ∈ σ.pending, p.1 ≤ σ.hj) →
    gp.q ≤ (σ.fin σ.hj).card →
    (gp.finalizePrune σ).hF = σ.hj ∧ (gp.finalizePrune σ).F = σ.J ∧
    (gp.q ≤ σ.target.card → gp.justifies (gp.finalizePrune σ))

/-- **G0.9 (a), retention.** While a bound height stays current and its predecessor is
not finalized, the predecessor stays pending. -/
def Retention : Prop :=
  ∀ (c : List (FGBlock gp.n)) (σ σ' : ChainState gp.n) (B : FGBlock gp.n),
    gp.chainState c = some σ → gp.stateTransition σ B = some σ' →
    σ.bound → σ'.h = σ.h → σ'.hF < σ'.hj → (σ.hj, σ.J) ∈ σ'.pending

/-- **G0.9 (b), the window `K_W = 2`.** The newest pending pair survives the next block,
whatever it appends, unless that block finalizes at its height or above. (False with a
window of one pair: an append would drop it.) -/
def RetentionThroughAppend : Prop :=
  ∀ (c : List (FGBlock gp.n)) (σ σ' : ChainState gp.n) (B : FGBlock gp.n) (P : Nat × Nat),
    gp.chainState c = some σ → gp.stateTransition σ B = some σ' →
    σ.pending.getLast? = some P → σ'.hF < P.1 → P ∈ σ'.pending

/-- **G0.10, aggregation at a bound entry.** A record *allows a target* at the entry
height `h` when it holds no lock at `h` for another block and has sent nothing at `h`
(its target and timeout entries at `h` are then empty, as for every record of a client run).
For a bound entry state, such a record makes the client send a target whose content is
`(h, T_h, target; (h_j, J))` when the record permits the predecessor and
`(h, T_h, target; none)` otherwise: never a timeout, and the same content at every
validator with a permitting record. -/
def Aggregation : Prop :=
  ∀ (σe : ChainState gp.n) (Λ : Record) (v : Fin gp.n), σe.bound →
    (Λ.lock σe.h = none ∨ Λ.lock σe.h = some σe.Th) → Λ.timeout σe.h = ∅ →
    Λ.target σe.h = none → (∀ b ∈ Λ.sent, b.1 ≠ σe.h) →
    ∃ a Λ', Λ.createAtt v σe = some (a, Λ') ∧
      a.content = (σe.h, σe.Th, false,
        if Λ.permits σe.hj σe.J then some (σe.hj, σe.J) else none)

/-- The inputs of an honest client: entry states whose justification and pending pairs
are below their height (G0.2 (a), (d) give this for the entry states of chains). -/
def EntryInputs (inputs : List (ChainState gp.n)) : Prop :=
  ∀ σe ∈ inputs, 1 ≤ σe.h ∧ σe.hj < σe.h ∧ ∀ p ∈ σe.pending, p.1 < σe.h

/-- **G0.5, client safety.** A client that starts from the empty record and keeps it
sends no slashable pair (E1 weakened, E2), also of one attestation with itself. -/
def ClientSafety : Prop :=
  ∀ (v : Fin gp.n) (inputs : List (ChainState gp.n)), EntryInputs gp inputs →
    ∀ a ∈ (Record.run v Record.empty inputs).2, ∀ b ∈ (Record.run v Record.empty inputs).2,
      ¬ slashable a b

/-- **G1.3, accountable safety (chain level).** If two chains finalize conflicting
blocks (neither finalized block is on the other chain, genesis included), at least
`2q − n` validators each have a slashable pair among the attestations of the two
chains. -/
def AccountableSafety : Prop :=
  ∀ (c₁ c₂ : List (FGBlock gp.n)) (σ₁ σ₂ : ChainState gp.n),
    gp.chainState c₁ = some σ₁ → gp.chainState c₂ = some σ₂ →
    σ₁.F ∉ gp.roots c₂ → σ₂.F ∉ gp.roots c₁ →
    ∃ S : Finset (Fin gp.n), 2 * gp.q - gp.n ≤ S.card ∧
      ∀ v ∈ S, ∃ a ∈ gp.chainAtts c₁ ++ gp.chainAtts c₂,
        ∃ b ∈ gp.chainAtts c₁ ++ gp.chainAtts c₂, a.val = v ∧ slashable a b

/-- The statements of milestone M₁ at parameters `gp`. -/
structure FGSafetyAt : Prop where
  quorumIntersection : QuorumIntersection gp
  chainInvariants : ChainInvariants gp
  heightStep : HeightStep gp
  gatedConsumption : GatedConsumption gp
  finalityBeforeGate : FinalityBeforeGate gp
  retention : Retention gp
  retentionThroughAppend : RetentionThroughAppend gp
  aggregation : Aggregation gp
  clientSafety : ClientSafety gp
  accountableSafety : AccountableSafety gp

/-- **Milestone M₁ (FG safety).** The statements hold at every FG parameter. -/
def FGSafety : Prop := ∀ gp : FGParams, FGSafetyAt gp

end Consensus.Goldilocks.FG

end
