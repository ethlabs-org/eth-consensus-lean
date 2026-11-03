module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace

@[expose] public section

/-! # Goldilocks milestone FGStore, part 3: the FG service lemmas (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (main `4ea71d05`), §"L1:
components / Finality gadget": the good window `GW(E, a, k_F)`, G1.6 (entry whose previous height is
justified, theorem A), G1.7 (entry whose previous height is not justified, two windows, theorem B),
G1.8 (crossing and coverage, corollary C) and G1.9 (a) (cache acceptance, per call); paper proofs in
workbench `repos/goldilocks/notes/fg-liveness/r9-loose-bj/theorem.md` §3–§5. G1.9 (b) is not fixed
in the claims yet, and G1.10 at C1.1's scope is a composition statement.

**Shape: over FG traces.** The conclusions are about one chain and the FG transition, but the
good window is a premise on rows as they reach an honest proposer: when they are signed (P2, the
emission deadline), that they are in the proposer's pool before its proposal (P3–P4), and that
the proposal includes every pooled row valid against its parent's state (P5). Pools, signing
times and honest proposals exist only in an FG trace, so the statements are over FG traces
(`FGLocalRun`), with the literal `GW` premises that the composition node C1.2 discharges; P7
(durable, serialized honest clients) is part of `FGLocalRun`.

**Reading.**
* An entry `E = (h, T_h, u)` is given by its entry block `T`: a held block whose state's entry is
  itself (`σ[T].T_h = T`, `IsEntry`), with `h = σ[T].h` and `u = T.slot`; its entry state `σ[T]`
  gives `previous_height_justified(E)` and `P_E = (σ[T].h_j, σ[T].J)`.
* The serving block `B*` is the honest proposer `p`'s own proposal, accepted at `p`'s cut `i`
  (at its slot's start); "the chain of `B*`" is read in `p`'s store after that cut.
* `c_F = ⌈(6Δ + Δ_F)/(4Δ)⌉` comes from the delivery bound `Δ_F`, which the FG lemmas do not read
  (P4 states the delivery it gives), so `c_F` is a parameter.
* A faulty row has no signing time: P2 counts it when it is already on the chain of `B*`'s parent
  or, through P3–P4, in the proposer's pool. "Already on the chain of `B*`" reads as on the chain
  of `B*`'s parent (every row of `B*` itself is on `B*`'s chain, which would empty the deadline).
* P5 includes every pooled row valid against the parent's state, as `proposal_attestations`
  does; a malformed pooled row that `valid_attestation` accepts would make `B*` refused, so in a
  trace whose pools hold one no window is good (a node's wire checks exclude it).
* "Finalized `P_E = (h−1, J_E)` at or before the block `X` that justifies `E`" reads as
  `σ[X].F = J_E` with `σ[X].h_F = h − 1` (the gate opens only when `h_F = h_j`, and no later pair
  is pending at `X`); "justified at `X`" as `σ[X].J = T_h`, `σ[X].h_j = h`; "`h` does not cross
  by timeout first" as: every block from `T` to `X`, `X` excluded, keeps height `h` and entry
  `T_h`. "By slot `u + D`" follows from `X ⪯ B*` and P1.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- `T` is an entry block in `st`: held, and the entry of its own state's height. -/
def IsEntry (st : Store P ACP) (T : NodeBlock P ACP) : Prop :=
  T ∈ st.tree ∧ (st.σ T.root).Th = T.root

/-- `B` is an honest proposal at cut `i` with parent `Pr`: the own proposal of the honest `p`,
accepted at its slot's start, whose parent `Pr` is held, and which includes every row of `p`'s
pool that is valid against `Pr`'s state and not on `Pr`'s chain (the composition's inclusion
rule, uncapped). -/
def HonestProposal (H : Set (Fin P.n)) (tr : FGTrace P ACP) (p : Fin P.n) (i : Nat)
    (B Pr : NodeBlock P ACP) : Prop :=
  p ∈ H ∧ tr.AcceptAt p i B ∧ B.proposer = p ∧ P.slotTime B.slot = tr.time i ∧
    Pr ∈ (tr.store p i).tree ∧ B.parent = some Pr.root ∧
    ∀ r ∈ (tr.store p i).atts, ((tr.store p i).σ Pr.root).validAtt r →
      ¬ (tr.store p i).OnChain Pr r → r ∈ B.fgPayload

/-- **The good window `GW(E, a, k_F)`** for the entry with entry block `T`, with slack `c_F`,
served by the block `Bs` that `p` proposes at cut `i` on the parent `Pr`, with the rows `R`:
* P1, P5: `Bs` is an honest proposal (accepted, so it passes `state_transition`) of a slot in
  `I(E, a, k_F) = [u + a + c_F, u + a + c_F + k_F]`, whose parent `Pr` extends `T`;
* P2: the validators of `R` weigh at least `q`; each row is a target row for `E` (height `h`, root
  `T_h`, no timeout), carrying `P_E` at an entry whose previous height is justified, and is on
  `Pr`'s chain already or, when its signer is honest, signed by `t_{u+a} + 6Δ`;
* P3–P4: each row is on `Pr`'s chain or in `p`'s pool at its proposal cut (processed at an
  earlier cut, before every object received at `t_{v*}`: the trace's tick order);
* P6: `δ_t ≥ D = a + c_F + k_F` and `K_W ≥ 1`. -/
structure GoodWindow (H : Set (Fin P.n)) (tr : FGTrace P ACP) (cF : Nat) (T : NodeBlock P ACP)
    (a kF : Nat) (p : Fin P.n) (i : Nat) (Bs Pr : NodeBlock P ACP) (R : Finset (FG.Att P.n)) :
    Prop where
  /-- P1, P5: an honest proposal. -/
  proposal : HonestProposal P ACP H tr p i Bs Pr
  /-- `T` is an entry block at `p`. -/
  entry : IsEntry P ACP (tr.store p i) T
  /-- P1: the parent extends `T`. -/
  extends_entry : (tr.store p i).Anc T Pr
  /-- P1: the slot is in the window. -/
  window : T.slot + a + cF ≤ Bs.slot ∧ Bs.slot ≤ T.slot + a + cF + kF
  /-- P2: the rows' validators weigh at least `q`. -/
  quorum : P.fg.q ≤ (R.image FG.Att.val).card
  /-- P2: target rows for `E`, carrying `P_E` at an entry whose previous height is justified. -/
  rows : ∀ r ∈ R, r.h = ((tr.store p i).σ T.root).h ∧ r.T = T.root ∧ r.timeout = false ∧
    (((tr.store p i).σ T.root).previousHeightJustified →
      r.fin = some (((tr.store p i).σ T.root).hj, ((tr.store p i).σ T.root).J))
  /-- P2: on the chain already, or (honest) signed by `t_{u+a} + 6Δ`. -/
  emitted : ∀ r ∈ R, (tr.store p i).OnChain Pr r ∨
    (r.val ∈ H → ∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ P.slotTime (T.slot + a) + 6 * P.Δ)
  /-- P3–P4: on the chain already, or in the proposer's pool before its proposal. -/
  pooled : ∀ r ∈ R, (tr.store p i).OnChain Pr r ∨ r ∈ (tr.store p i).atts
  /-- P6. -/
  params : a + cF + kF ≤ P.δt ∧ 1 ≤ FG.FGParams.KW

/-- `X` justifies the entry `T` at height `h` in `st`, and every block from `T` to `X`, `X`
excluded, keeps height `h` and entry `T` (so `h` is not left before `X`, by timeout or
otherwise). -/
def JustifiesEntry (st : Store P ACP) (T : NodeBlock P ACP) (h : Nat) (X : NodeBlock P ACP) :
    Prop :=
  X ∈ st.tree ∧ st.Anc T X ∧ (st.σ X.root).hj = h ∧ (st.σ X.root).J = T.root ∧
    ∀ Y ∈ st.tree, st.Anc T Y → st.Anc Y X → Y ≠ X →
      (st.σ Y.root).h = h ∧ (st.σ Y.root).Th = T.root

/-- **G1.6, entry whose previous height is justified (theorem A).** Let `E` be an entry whose
previous height is justified with predecessor `P_E` and `GW(E, a, k_F)`. Then on the chain of `B*`:
`E` is justified at `B*` or at an earlier block `X` (so by slot `u + D`), `h` is not left before `X`
(in particular not by timeout), and `P_E` is finalized at `X` or before (`σ[X].F = J_E`, `σ[X].h_F =
h − 1`). -/
def PreviousHeightJustifiedEntry : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → ∀ (cF : Nat) (T : NodeBlock P ACP) (a kF : Nat) (p : Fin P.n)
      (i : Nat) (Bs Pr : NodeBlock P ACP) (R : Finset (FG.Att P.n)),
    GoodWindow P ACP H tr cF T a kF p i Bs Pr R →
    ((tr.store p i).σ T.root).previousHeightJustified →
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      ((tr.store p (i + 1)).σ X.root).F = ((tr.store p i).σ T.root).J ∧
      ((tr.store p (i + 1)).σ X.root).hF = ((tr.store p i).σ T.root).hj

/-- **G1.7, entry whose previous height is not justified, two windows (theorem B).** Let `U` be an
entry whose previous height is not justified (height `h`, entry block `T`) with `GW(U, a₀, k_F)`
(target rows, no finality pair needed). Then `U` justifies at a block `X` of `B*₀`'s chain (so `u₁ =
X.slot ≤ u₀ + D₀`), appending `Q = (h, T_h)`, and `X` enters a height whose previous height is
justified `E₁` (its own entry) with predecessor `Q`. If moreover `GW(E₁, a₁, k_F)` for that actual
entry `X`, with serving block `B*₁`, then on the chain of `B*₁` the pair `Q` is finalized at a block
`Z ⪯ B*₁` (so by `u₁ + D₁ ≤ u₀ + D₀ + D₁`): `σ[Z].F = T_h`, which covers `T_h` and every ancestor.
-/
def PreviousHeightNotJustifiedEntry : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → ∀ (cF : Nat) (T : NodeBlock P ACP) (a₀ kF : Nat) (p : Fin P.n)
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

/-- **G1.8 (a), crossing bound (corollary C).** Let `C` be a block at an honest node `y` whose
chain extends an entry `T` of slot `u` (height `h`), and let `g ≥ 1`, `r ≥ 1` with
`C.slot ≥ u + max(δ_t, r) + g − 1`. If in every `g` consecutive slots after `u` up to `C.slot`
the chain of `C` has an honest proposal whose proposer's pool, for a proposal of slot at least
`u + r`, holds a progress quorum of current-entry rows (height `h`, root `T_h`, target or
timeout) before its proposal, then the chain of `C` leaves height `h`, by justification or
timeout, within `max(δ_t, r) + g − 1` slots of `u`. (`r ≥ 1`: rows for an entry of slot `u` are
signed from `t_u` on; at `max(δ_t, r) = 0` the bound would be one slot short.) -/
def Crossing : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → ∀ y ∈ H, ∀ (k : Nat) (C T : NodeBlock P ACP) (g r : Nat),
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

/-- **G1.8 (b), coverage after failed entries (corollary C).** Let the entries from `T₁` to the
entry whose previous height is not justified `T` (`T₁ ≺ T` on the chain of `B*₀`, `m ≥ 1`
consecutive entries that cross by timeout: every entry block after `T₁` up to `T` does not have its
previous height justified), and let `T` and its actual successor entry, entered by justifying it,
satisfy G1.7's two windows, with serving block `B*₁`. Then `T₁` is covered on the chain of `B*₁`
within `Σ τ_i + D₀ + D₁ = (T.slot − T₁.slot) + D₀ + D₁` slots of `T₁.slot`: some `Z ⪯ B*₁` has a
finalized block that extends `T₁`. -/
def Coverage : Prop :=
  ∀ (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP),
    FGLocalRun acp₀ H U tr → ∀ (cF : Nat) (T₁ T : NodeBlock P ACP) (a₀ kF : Nat) (p : Fin P.n)
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

open Classical in
/-- The FG state after `update_finality(Σ, σ)`'s `h_max` and justification steps, which its
finalization step reads (`updateFinality`'s `st₂`). -/
noncomputable def afterJustification (st : Store P ACP) (σ : FG.ChainState P.n) :
    Store P ACP :=
  let st₁ : Store P ACP := { st with hmax := max st.hmax σ.h }
  match st₁.blocks σ.J with
  | some X =>
      if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J) then
        { st₁ with J := X, hj := σ.hj }
      else st₁
  | none => st₁

/-- **G1.9 (a), cache acceptance (per call).** When `update_finality(Σ, σ[B])` runs (for a held
`B` whose state `σ = σ[B]` has `h_j < h` and finalizes an ancestor `X` of `B`, as in
`fg_on_block`) with `Σ.F ≺ X`, `X ⪯ Σ.J` after the call's justification step, and
`has_viable_descendant(Σ, X)` after its `h_max` step, then `X ⪯ Σ.F` afterwards. (The
finalization step reads viability after the justification step too; for such a `σ` that step
does not raise the head height floor.) -/
def CacheAcceptance : Prop :=
  ∀ (st : Store P ACP) (B : NodeBlock P ACP) (X : NodeBlock P ACP),
    B ∈ st.tree → (st.σ B.root).hj < (st.σ B.root).h → st.blocks (st.σ B.root).F = some X →
    st.Anc X B → st.Anc st.F X → st.F ≠ X →
    (afterJustification P ACP st (st.σ B.root)).Anc X
      (afterJustification P ACP st (st.σ B.root)).J →
    ({ st with hmax := max st.hmax (st.σ B.root).h } : Store P ACP).HasViableDescendant X →
    (st.updateFinality (st.σ B.root)).Anc X (st.updateFinality (st.σ B.root)).F

/-- The statements of FGStore part 3 at parameters `P` and AC payload type `ACP`. -/
structure FGStoreServiceAt : Prop where
  previousHeightJustifiedEntry : PreviousHeightJustifiedEntry P ACP
  previousHeightNotJustifiedEntry : PreviousHeightNotJustifiedEntry P ACP
  crossing : Crossing P ACP
  coverage : Coverage P ACP
  cacheAcceptance : CacheAcceptance P ACP

/-- **FGStore, part 3.** The FG service lemmas hold at every parameter and AC payload type. -/
def FGStoreService : Prop := ∀ (P : Params) (ACP : Type), FGStoreServiceAt P ACP

end Consensus.Goldilocks.Store

end
