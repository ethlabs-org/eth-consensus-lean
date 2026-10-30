module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Events

@[expose] public section

/-! # Goldilocks milestone ACSteps: the AC step lemmas over AC traces (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main `a470648c`;
A1.9 at `688e287b`), the L1 nodes of the AC module (decomposition §3.1, §3.2): A1.1 (proposer and
voters agree on unlocking), A1.2 (first transfer), A1.3 (next transfer), A1.4 (optimistic is fast),
A1.5 (source age), A1.8 (result transfer) and A1.9 (source compatibility after the cut). A1.2–A1.4
and A1.8 are stated **per vote**: the conclusion is about one honest vote and the hypotheses about
that vote and strictly earlier events (claims §"L1: components / Available chain"), so that C1.1's
induction over events can discharge them; A1.9 is stated per `ac_to_fg` call. The origin of a lock
or a result (a fast lock write, an update's result) is a fixed datum, as in the claims, and can be
later than the vote (an update of slot `s` runs at `t_s + 6Δ`, after the slot-`(s+1)` votes). A1.6
and A1.7 are run-level (milestone Service).

Every statement is over an AC trace of the Goldilocks SA with its contract and the honest-object
facts (`ACRun`, for the honest validators `H` inside the coherent set `U` of all frame blocks),
with the network premises over the trace (`SyncAC`, `Carry` / `CarryAt`, `FaultBound`), never
over the FG state. `NoColl` is the coherence of `U` (roots injective; every AC lookup goes through
frames inside `U`). The SA is parametric in its restart replay order and the statements quantify
over every order. "Precedes in the run's event order" (F.5 (run)) is the cut order. A block
"extends" another inside `U`. `docs/goldilocks-mapping.md` §"ACSteps" maps each statement to its
node.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.1, proposer and voters agree on unlocking.** Under `Sync[t_s, t_{s+1}]`: for the honest
proposer `p` of slot `s + 1` with a proposal (payload `pay`) at `t_{s+1}`, and an honest voter
`y` of slot `s + 1` that holds that proposal (a slot-`(s+1)` block of its frame with that
payload), if `p`'s frame at the proposal and `y`'s frame at its vote hold the same blocks of slot
at most `s`, then the proposal's view and `y`'s merged view give the same opponents (against the
slot-`s` votes) to every block of slot at most `s`. -/
def ProposerVotersAgree : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s : Nat) (p y : Fin sp.n) (i j : Nat)
      (ℓp ℓy : ACLabel (goldilocksSA sp FGP ro))
      (pay : Payload sp.n) (e : Em sp FGP),
    p ∈ H → y ∈ H → p = sp.toParams.proposer (s + 1) →
    ProposalAt tr p i ℓp pay → tr.time i = sp.ts (s + 1 : Nat) →
    CastAt tr y j ℓy e → e.msg.slot = s + 1 →
    (∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay) →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr →
    {X | X ∈ ℓp.frame.tree ∧ X.slot ≤ s} = {X | X ∈ ℓy.frame.tree ∧ X.slot ≤ s} →
    ∀ B ∈ ℓp.frame.tree, B.slot ≤ s →
      opponents sp ℓp.frame (View.ofLists pay) s B =
        opponents sp ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s B

/-- **A1.2, first transfer (per vote).** Let an honest node write a fast lock of slot `s` on `B`
(by the fast test of the update or by an optimistic confirmation) with counted votes `CV`, and
let an honest `y` cast its slot-`(s+1)` vote at cut `i` (time `τ`). Under `Sync[t_s, τ]`,
`Carry_y(s, S, B)`, `f < h_τ`, `B` in `y`'s viable voter block tree or at or below its
`fc_root` at that vote, and every honest slot-`(s+1)` vote at an earlier cut extending `B`, the
vote extends `B`. (The writer-pool condition A1.8 (d) follows from `Sync`, which forwards votes
admitted from a block's payload; goldilocks#32.) -/
def FirstTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s : Nat) (x y : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    x ∈ H → FastLockAt tr x i₀ s B CV →
    y ∈ H → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr →
    CarryAt tr U y i e s CV → FaultBound tr H (tr.time i) →
    ViableAtVote ℓ e (s + 1) B → EarlierVotesExtend tr H U i (s + 1) B →
    VoteExtends U e.msg B

/-- **A1.3, next transfer (per vote).** Let an honest `y` cast its slot-`(m+1)` vote at cut `i`
(time `τ`). If every honest vote of slot `m` extends `B`, the honest voters of slot `m` are at
least half of the committee, `Carry_y(m, S_m, B)` holds for the honest slot-`m` votes, `f < h_τ`,
`Sync[t_m, τ]`, at that vote `B` is in `y`'s viable voter block tree or at or below its
`fc_root`, and every honest slot-`(m+1)` vote at an earlier cut extends `B`, then the vote
extends `B`. -/
def NextTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (m : Nat) (y : Fin sp.n) (i : Nat) (B : Blk sp.n FGP)
      (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    y ∈ H → CastAt tr y i ℓ e → e.msg.slot = m + 1 →
    (∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B) →
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard →
    CarryAt tr U y i e m {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} →
    FaultBound tr H (tr.time i) →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts m) (tr.time i) tr →
    ViableAtVote ℓ e (m + 1) B → EarlierVotesExtend tr H U i (m + 1) B →
    VoteExtends U e.msg B

/-- **A1.4 (a), optimistic is fast: the transfer (per vote).** Let an honest node confirm `B`
optimistically in slot `s` with counted votes `CV`, and assume `f < n/2`. For an honest `y`
casting its slot-`(s+1)` vote at cut `i` (time `τ`): under `Sync[t_s, τ]`, `Carry_y(s, S, B)`,
`B` in `y`'s viable voter block tree or at or below its `fc_root` at that vote, and every honest
slot-`(s+1)` vote at an earlier cut extending `B`, the vote extends `B`. -/
def OptimisticTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s : Nat) (x y : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    x ∈ H → OptimisticLockAt tr x i₀ s B CV → 2 * Hᶜ.ncard < sp.n →
    y ∈ H → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr →
    CarryAt tr U y i e s CV →
    ViableAtVote ℓ e (s + 1) B → EarlierVotesExtend tr H U i (s + 1) B →
    VoteExtends U e.msg B

/-- **A1.4 (b), optimistic is fast: the next update.** Let an honest node confirm `B`
optimistically in slot `s`, with `f < n/2`. Under `Sync[t_s, t_{s+1} + Δ]`, if every honest
vote of slot `s + 1` extends `B` ((a)'s conclusion), then an honest `z` whose update of slot
`s + 1` runs at cut `k` (joined at `t_{s+1} + 6Δ`), holding the slot-`(s+1)` votes of at least
`n/2` honest voters and with every honest slot-`(s+1)` vote it holds resolved before
`t_{s+1} + 2Δ`, has a slot-`(s+1)` result that extends `B`, and, if `B` is not genesis, its fast
test selects a block `D` that extends `B` (the write can still be vetoed or moved back). -/
def OptimisticNextUpdate : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s : Nat) (x z : Fin sp.n) (i₀ k : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)),
    x ∈ H → OptimisticLockAt tr x i₀ s B CV → 2 * Hᶜ.ncard < sp.n →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr →
    (∀ x' ∈ H, ∀ j e, VoteAt tr x' j e → e.msg.slot = s + 1 → VoteExtends U e.msg B) →
    z ∈ H → UpdateAt tr z k (s + 1) ℓ →
    sp.n ≤ 2 * {v | v ∈ H ∧ ∃ x' ∈ (tr.state z k).pool (s + 1), x'.val = v}.ncard →
    (∀ x' ∈ (tr.state z k).pool (s + 1), x'.val ∈ H →
      resolutionTime (tr.state z k) ℓ.frame x' < ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ)) →
    ∃ C, getConfirmation sp (tr.state z k) ℓ.frame (s + 1) = some C ∧ Anc U B C ∧
      (B.root ≠ sp.genesisRoot →
        ∃ D, fastSelect sp (tr.state z k) ℓ.frame (s + 1) C = some D ∧ Anc U B D)

/-- **A1.5, source age.** From slot `slot(τ) + 3` on, every block that `ac_to_fg` returns at an
honest node is the block of a fast lock that node wrote after `τ`: at or below the block of a
fast lock of a slot `s'` with `slot(t) ≤ s' + 2`, written at a cut after `τ`. -/
def SourceAge : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (τ : Time) (x : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksSA sp FGP ro))
      (C : Blk sp.n FGP),
    x ∈ H → ToFGAt tr x i ℓ C → sp.slot τ + 3 ≤ sp.slot (tr.time i) →
    ∃ j ≤ i, ∃ s' B' CV', FastLockAt tr x j s' B' CV' ∧ τ < tr.time j ∧
      sp.slot (tr.time i) ≤ s' + 2 ∧ Anc U C B'

/-- **A1.8, result transfer (per vote).** Let an honest `X`, joined at `t_s + 6Δ`, get a result
`C ≠ ⊥` from `get_confirmation` for slot `s` (fast, slow, vetoed or not) with counted votes
`CV`, and let an honest `y` cast its slot-`(s+1)` vote at cut `i`. Assume, at that vote: `y` is
awake and joined, and before `t_s + 3Δ` it accepted the heads of the counted votes and their
ancestors and holds each counted vote or two other slot-`s` votes of its validator (`CarryAt`);
`C` is in its viable voter block tree or at or below its `fc_root`; every live lock block of `y`
after its unlocking is compatible with `C`; and every slot-`s` vote of its merged view is in
`X`'s pool at `t_s + 6Δ`, or that pool holds two distinct votes of its validator. Then the vote
extends `C`. (No participation bound.) -/
def ResultTransfer : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s : Nat) (X y : Fin sp.n) (i₀ i : Nat) (C : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP),
    X ∈ H → ResultAt tr X i₀ s C CV →
    y ∈ H → CastAt tr y i ℓ e → e.msg.slot = s + 1 →
    CarryAt tr U y i e s CV → ViableAtVote ℓ e (s + 1) C →
    (∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L C) →
    (∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) →
    VoteExtends U e.msg C

/-- **A1.9, source compatibility after the cut (per call).** Let an honest node write a fast
lock of slot `s` on `B` with counted votes `CV`. Assume `Sync[t_s, t_{s+1} + Δ]`,
`Carry(s, S, B)` and `f < n/2`; let `x`'s `ac_to_fg` call at cut `i` be at a public time
`t ∈ (t_{s+1} + Δ, t_m + Δ]`; assume every honest vote of a slot in `(s, m]` at an earlier cut
extends `B`, and that at the call `Φ.F` and `fc_root` are compatible with `B`, and either (i) `x`
cast its slot-`(s+1)` vote at an earlier cut, and at the unlocking before that vote (the vote's
call) `Φ.F` and `fc_root` are compatible with `B`, or (ii) `x` restarted after `t_s`, at an
earlier cut (claims at goldilocks `688e287b`, goldilocks#33; not vacuous when `x` makes no
unlocking in slot `s + 1`: consensus-lean#66). Then the block `fg_confirmed ≠ ⊥` that the call
returns is compatible with `B`. -/
def SourceCompatible : Prop :=
  ∀ (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro),
    ACRun tr H U → ∀ (s m : Nat) (w x : Fin sp.n) (i₀ i : Nat) (B : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (C : Blk sp.n FGP),
    w ∈ H → FastLockAt tr w i₀ s B CV →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr →
    Carry tr H U s CV → 2 * Hᶜ.ncard < sp.n →
    x ∈ H → ToFGAt tr x i ℓ C → sp.toParams.IsPublic (tr.time i) →
    sp.ts (s + 1 : Nat) + sp.Δ < tr.time i → tr.time i ≤ sp.ts m + sp.Δ →
    (∀ z ∈ H, ∀ j < i, ∀ e, VoteAt tr z j e → s < e.msg.slot → e.msg.slot ≤ m →
      VoteExtends U e.msg B) →
    ((∃ j < i, ∃ ℓ' e, CastAt tr x j ℓ' e ∧ e.msg.slot = s + 1 ∧
        Compatible U ℓ'.frame.F B ∧ Compatible U ℓ'.frame.fcRoot B) ∨
      (∃ k < i, tr.RestartAt x k ∧ sp.ts s < tr.time k)) →
    Compatible U ℓ.frame.F B → Compatible U ℓ.frame.fcRoot B →
    Compatible U C B

/-- The ACSteps statements, for the SA parameters `sp`. -/
structure ACStepsAt : Prop where
  proposerVotersAgree : ProposerVotersAgree sp
  firstTransfer : FirstTransfer sp
  nextTransfer : NextTransfer sp
  optimisticTransfer : OptimisticTransfer sp
  optimisticNextUpdate : OptimisticNextUpdate sp
  sourceAge : SourceAge sp
  resultTransfer : ResultTransfer sp
  sourceCompatible : SourceCompatible sp

/-- **Milestone ACSteps**: the ACSteps statements for all SA parameters. -/
def ACSteps : Prop := ∀ sp : SAParams, ACStepsAt sp

end Consensus.Goldilocks.SA

end
