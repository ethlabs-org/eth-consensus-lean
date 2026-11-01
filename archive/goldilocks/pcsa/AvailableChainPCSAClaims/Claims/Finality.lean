module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAClaims.Statements.FinalityApi
public import AvailableChainPCSAClaims.Statements.Slashing

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C12, C13] The Finality lane
statements over PC-SA objects: source transfer under R8′ (pcsa34-r4 5.7) and
its formation helper, Q0-PC (5.8.3, the replacement of Q0) and its selection
helper, and the finality safety claims of the FG-SA `FGSAFinalityClaims`
shape (5.8.2: UNCHANGED, pure FG), with the slashing claims. Every statement
reads the PC-SA source (`fgSource`: the R8′ selector over the `z_{rR}`
snapshot), the PC-SA store and `pcsa_finalityView`; none reads a fast write
or a gate service, so the proofs can go through the generic FG interface.
The kernel (F1–F9) and finality liveness are not stated here: they need the
stage-2 frame (under `StageOneFrame` no block is ever finalized) and the
deferred kernel-reuse decision (plan §5). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA claims, W0; pcsa34-r4 5.7 proof; plan C12] Formation-to-source
helper: at the opening `rR = r·R`, the formation premises (F1)–(F7) at slot
`rR` (an honest awake proposer of `N`, `h_{rR} ≥ q_N`, `a ≤ ⌊n/4⌋`, stage 1,
so `PC(rR, P_{rR})` is frame-active at `a_r`) give every honest node the
source `P_{rR}` at `a_r` (`C_fg = P_{rR}`). The common view (F3) and the
lock condition (F4) are premises here; the paper's source-transfer claim
gets them from CI (`CleanSourceTransferClaim`) or from healing. -/
def FormationSourceClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (r : Nat) (N : NamedProposal p.n)
    (ΔF : Time),
    FormationPrem p c E rho (r * p.R) N ΔF →
    ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase

theorem FormationSourceClaim_def (p : Params) : FormationSourceClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (r : Nat) (N : NamedProposal p.n)
      (ΔF : Time),
      FormationPrem p c E rho (r * p.R) N ΔF →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase) := by
  rw [FormationSourceClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.7 Claim (honest opening), CLEAN form,
PROVED-paper; plan C12] Source transfer in a CLEAN run: round `r` with an
honest awake proposer of `N` at the opening slot `rR` and `a_r = d_{rR} ≤ b₀`
(CLEAN(b₀), `Clean₂`; synchrony from genesis, so `t_{rR} ≥ t_GST + Δ` holds),
`h_{rR} ≥ q_N`, `a ≤ ⌊n/4⌋`, the stage-1 frame (5.3 (F6)/(F7)), and the frame
premise of 5.7: `PC(rR, P_{rR})` is frame-active at every honest node at
`a_r`. Then every honest source at `a_r` is `P_{rR}`. The healed-suffix form
is `HealedSourceTransferClaim`. -/
def CleanSourceTransferClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time) (r : Nat)
    (N : NamedProposal p.n),
    Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → StageOneFrame p c E rho →
    HonestNamedProposal p c E rho (r * p.R) N →
    nQuorum p.n ≤ (awakeHonestLabel p c E rho (r * p.R)).card →
    p.actionTime r ≤ b₀ →
    (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
      ∃ B ∈ fullTree p nd.st, eraseFG B = N.erase) →
    ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase

theorem CleanSourceTransferClaim_def (p : Params) : CleanSourceTransferClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time) (r : Nat)
      (N : NamedProposal p.n),
      Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → StageOneFrame p c E rho →
      HonestNamedProposal p c E rho (r * p.R) N →
      nQuorum p.n ≤ (awakeHonestLabel p c E rho (r * p.R)).card →
      p.actionTime r ≤ b₀ →
      (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
        ∃ B ∈ fullTree p nd.st, eraseFG B = N.erase) →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase) := by
  rw [CleanSourceTransferClaim]

/-- [PC-SA claims; pcsa34-r4 5.7 Claim (honest opening), healed-suffix form,
PROVED-paper; plan C12] Source transfer after the healing time: under
`HealedSourcePrem` (RECOVERY, `t_{rR} ≥ t_GST + Δ`, `h_{rR} ≥ q_N`, the
honest awake proposer of `N` at `rR`, the formation premises (F3) common
view and (F4) locks, the explicit frame premises (F6) equal frames and (F7)
`F`-compatibility, and `PC(rR, P_{rR})` frame-active at `a_r`), every honest
source at `a_r` is `P_{rR}`. There is no `StageOneFrame` premise. The
producers of (F3)/(F4) after `t*` are the HEALING_INPUT items H2/H3
([FG-HEAL], OPEN); the frame premises are discharged by `StageOneFrame` in
stage 1 and by the stage-2 frame lemmas otherwise. -/
def HealedSourceTransferClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (G ΔF : Time) (r : Nat) (N : NamedProposal p.n),
    HealedSourcePrem p c E rho G ΔF r N →
    ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase

theorem HealedSourceTransferClaim_def (p : Params) : HealedSourceTransferClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (G ΔF : Time) (r : Nat) (N : NamedProposal p.n),
      HealedSourcePrem p c E rho G ΔF r N →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase) := by
  rw [HealedSourceTransferClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.8.3; q0-pc.md §2 steps 2–4, PROVED-paper;
plan C13] Q0-PC selection helper: the selection steps of Q0-PC after step 1
is supplied. Let `D` be a block with `PC(cD, D)` stamped before `z_{cD}` at
every honest node (step 1a), and `j = rR = r·R` an opening label with
`cD ≤ j < cD + R`. Premises: `F ⪯ D` at every honest read through `a_r`
(step 1b); `PC(cD, D)` is frame-active at every honest node at `a_r` (the
conclusion of steps 1c–1d); H2′: every honest HEAD of every label in
`(cD, j]` covers `D`; `a < ⌈n/2⌉`. Conclusion: at `a_r` every honest node
has a source `T ⪰ D` with `slot(T) ∈ [cD, j]`; under the cap `H ≤ ht(D)`
every honest source has the height and the entry of `D`. The full Q0-PC
statement is `Q0PCClaim`. -/
def Q0PCSelectionClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (r : Nat) (cD : Slot) (D : Block),
    Base₂ p c E rho → FaultsBelowQA p c rho →
    cD ≤ r * p.R → r * p.R < cD + p.R → p.actionTime r ≤ rho.horizon →
    (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams cD) cD D) →
    (∀ y ∈ rho.honest, ∀ t : Time, t ≤ p.actionTime r →
      Block.Preceq (eraseFG (storeAt p c E rho y t).fg.F) D) →
    (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
      ∃ B ∈ fullTree p nd.st, eraseFG B = D) →
    (∀ (s' : Slot) (x : V) (H : Block), cD < s' → s' ≤ r * p.R →
      HonestHeadAt p c E rho x s' H → Block.Preceq D H) →
    (∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
        cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
    (∀ Dfg : FGBlock (Fin p.n), eraseFG Dfg = D →
      (∀ x ∈ rho.honest, ∀ nd, pcsa_postClock E rho x (p.actionTime r) = some nd →
        ∀ B ∈ nd.st.fg.TF, (FGSA.heightView p B).h ≤ (FGSA.heightView p Dfg).h) →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧
          (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
          (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)

theorem Q0PCSelectionClaim_def (p : Params) : Q0PCSelectionClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (r : Nat) (cD : Slot) (D : Block),
      Base₂ p c E rho → FaultsBelowQA p c rho →
      cD ≤ r * p.R → r * p.R < cD + p.R → p.actionTime r ≤ rho.horizon →
      (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams cD) cD D) →
      (∀ y ∈ rho.honest, ∀ t : Time, t ≤ p.actionTime r →
        Block.Preceq (eraseFG (storeAt p c E rho y t).fg.F) D) →
      (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
        ∃ B ∈ fullTree p nd.st, eraseFG B = D) →
      (∀ (s' : Slot) (x : V) (H : Block), cD < s' → s' ≤ r * p.R →
        HonestHeadAt p c E rho x s' H → Block.Preceq D H) →
      (∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
          cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
      (∀ Dfg : FGBlock (Fin p.n), eraseFG Dfg = D →
        (∀ x ∈ rho.honest, ∀ nd, pcsa_postClock E rho x (p.actionTime r) = some nd →
          ∀ B ∈ nd.st.fg.TF, (FGSA.heightView p B).h ≤ (FGSA.heightView p Dfg).h) →
        ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
          actionSourceAt p c E rho x r = some (some C) ∧
            (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
            (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)) := by
  rw [Q0PCSelectionClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.8.3 Q0-PC; q0-pc.md §2 Statement,
PROVED-paper under the finality package; fg-port-r8-gaps.md §6; plan C13]
Q0-PC: let `D` be the honest proposal of slot `cD` after `t*`, with height
`y ≥ M + 1`, and `rR` an opening label with `cD ≤ rR < cD + R`. Under the
premise package `Q0PCPackage` (H2′, the causal cap `H ≤ y + 1`, `F ⪯ D`
through `a_r`, HEALING_INPUT(t*), H.11 `μ ≤ M`, FF2, FF2-C and the
source-transfer premise), the base run premises, `a < ⌈n/2⌉` and `a ≤ f`
(the count `n − q_N < q_F − a` of step (1c)), every honest node has at `a_r`
a source `T ⪰ D` with `slot(T) ∈ [cD, rR]`; under the cap `H ≤ y` every
honest source has height `y` and the entry of `D`. The PC-SA producers of the
package are OPEN (q0-pc.md §2, H.13-PC′). -/
def Q0PCClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (tStar : Time) (M μ r : Nat)
    (cD : Slot) (D : Block) (Dfg : FGBlock (Fin p.n)),
    Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
    Q0PCPackage p c E rho tStar M μ r cD D Dfg → Q0PCConcl p c E rho r cD D Dfg

theorem Q0PCClaim_def (p : Params) : Q0PCClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (tStar : Time) (M μ r : Nat)
      (cD : Slot) (D : Block) (Dfg : FGBlock (Fin p.n)),
      Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
      Q0PCPackage p c E rho tStar M μ r cD D Dfg → Q0PCConcl p c E rho r cD D Dfg) := by
  rw [Q0PCClaim]

/-! ### Finality safety (FGSAFinalityClaims shape; pcsa34-r4 5.8.2 UNCHANGED) -/

/-- [PC-SA claims, W0; FG-SA PureAccountableClaim; DC certificatesAccountable]
Two window certificates finalize compatible blocks, or slashable weight lies
between their chains. Pure FG; scoped root injectivity. -/
def PCSAPureAccountableClaim (p : Params) : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true

theorem PCSAPureAccountableClaim_def (p : Params) : PCSAPureAccountableClaim p =
    (∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
        FGBlock.compatible T₁ T₂ = true) := by
  rw [PCSAPureAccountableClaim]

/-- [PC-SA claims, W0; FG-SA PureAgreementClaim] Without slashable weight
between the chains, two window certificates finalize compatible blocks. -/
def PCSAPureAgreementClaim (p : Params) : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
      FGBlock.compatible T₁ T₂ = true

theorem PCSAPureAgreementClaim_def (p : Params) : PCSAPureAgreementClaim p =
    (∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
        FGBlock.compatible T₁ T₂ = true) := by
  rw [PCSAPureAgreementClaim]

/-- [PC-SA claims, W0; FG-SA WholeRunAccountableClaim; DC finalizedAccountable]
Whole-run accountability over a PC-SA run with root collision freedom and
sorted events. -/
def PCSAWholeRunAccountableClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCWholeRunAccountable p c E rho

theorem PCSAWholeRunAccountableClaim_def (p : Params) : PCSAWholeRunAccountableClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCWholeRunAccountable p c E rho) := by
  rw [PCSAWholeRunAccountableClaim]

/-- [PC-SA claims, W0; FG-SA WholeRunAgreementClaim; DC finalizedSafe]
Whole-run agreement under the slashable bound. -/
def PCSAWholeRunAgreementClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCFinalitySlashableBound p c E rho → PCWholeRunAgreement p c E rho

theorem PCSAWholeRunAgreementClaim_def (p : Params) : PCSAWholeRunAgreementClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCFinalitySlashableBound p c E rho → PCWholeRunAgreement p c E rho) := by
  rw [PCSAWholeRunAgreementClaim]

/-- [PC-SA claims, W0; FG-SA EventPrefixAgreementClaim] Under the slashable
bound, the finalized blocks of any two honest event states are compatible. -/
def PCSAEventPrefixAgreementClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCFinalitySlashableBound p c E rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
      FGBlock.compatible (storeBefore p c E rho i x).fg.F (storeBefore p c E rho j y).fg.F = true

theorem PCSAEventPrefixAgreementClaim_def (p : Params) : PCSAEventPrefixAgreementClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCFinalitySlashableBound p c E rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
        FGBlock.compatible (storeBefore p c E rho i x).fg.F
          (storeBefore p c E rho j y).fg.F = true) := by
  rw [PCSAEventPrefixAgreementClaim]

/-- [PC-SA claims, W0; FG-SA FinalizedMonotonicityClaim; DC finalizedMonotone]
The finalized output of an honest node is monotone in time. A restart resets
`F`, so `NoRestart` is a premise. No fault bound. -/
def PCSAFinalizedMonotoneClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    PCFinalityExecution p c rho → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
        (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x))

theorem PCSAFinalizedMonotoneClaim_def (p : Params) : PCSAFinalizedMonotoneClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
      PCFinalityExecution p c rho → V2.D.NoRestart rho →
      ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
        Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
          (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x))) := by
  rw [PCSAFinalizedMonotoneClaim]

/-- [PC-SA claims, W0; FG-SA FaultCountSlashableBoundClaim; DC
L/FinalitySafety.lean] Linked FG seats, authentic carriage of the rows of
every finality block, honest nodes that emit no slashable row pair, and
`a ≤ f` give the slashable bound `PCFinalitySlashableBound` (the premise of
the whole-run claims). -/
def PCSAFaultCountSlashableBoundClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
    V2.D.Linked (pcsaFamilies p c).linked rho →
    (∀ K, PCFinalityBlock p c E rho K → PCFinalityRowCarriage p c E rho (chainRows K)) →
    (∀ x ∈ rho.honest, PCEmittedRowsNoSlash p c E rho x) →
    FGSafetyBound p c rho →
    PCFinalitySlashableBound p c E rho

theorem PCSAFaultCountSlashableBoundClaim_def (p : Params) :
    PCSAFaultCountSlashableBoundClaim p =
      (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)),
        V2.D.Linked (pcsaFamilies p c).linked rho →
        (∀ K, PCFinalityBlock p c E rho K → PCFinalityRowCarriage p c E rho (chainRows K)) →
        (∀ x ∈ rho.honest, PCEmittedRowsNoSlash p c E rho x) →
        FGSafetyBound p c rho →
        PCFinalitySlashableBound p c E rho) := by
  rw [PCSAFaultCountSlashableBoundClaim]

/-- [PC-SA claims, W0; FG-SA HonestNeverSlashedClaim; DC Generic/Claims.lean
honestNeverSlashed] Under unforgeable signatures and linked FG seats, no
honest validator is slashed (`pcsaSlashing`). Validators are the fixed FG
seats (`V = Fin p.n`), as in FG-SA. No fault bound. -/
def PCSAHonestNeverSlashedClaim (p : Params) : Prop :=
  ∀ {In : Type} (c : AppCodec In) (m : FGMode) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (pcsaWith m p c)),
    V2.D.UnforgeableSignatures E rho →
    V2.D.Linked (pcsaFamilies p c).linked rho →
    Gen.V2.Duty.HonestNeverSlashed (pcsaSlashing p c E) rho

theorem PCSAHonestNeverSlashedClaim_def (p : Params) : PCSAHonestNeverSlashedClaim p =
    (∀ {In : Type} (c : AppCodec In) (m : FGMode) (E : Generic.Env (Fin p.n))
      (rho : V2.D.Run (Fin p.n) (pcsaWith m p c)),
      V2.D.UnforgeableSignatures E rho →
      V2.D.Linked (pcsaFamilies p c).linked rho →
      Gen.V2.Duty.HonestNeverSlashed (pcsaSlashing p c E) rho) := by
  rw [PCSAHonestNeverSlashedClaim]

/-- [PC-SA claims, W0; FG-SA FGSAFinalityClaims] The finality safety claims
of PC-SA: accountability and agreement, and the slashing claims that
discharge their slashable-bound premise (`faultCountSlashableBound`, with
its row-carriage and honest-emission premises; `honestNeverSlashed`). Not
stated: the kernel (F1–F9) and finality liveness (stage 2, plan §5). -/
structure PCSAFinalitySafetyClaims (p : Params) : Prop where
  accountable : PCSAPureAccountableClaim p
  agreement : PCSAPureAgreementClaim p
  runAccountable : PCSAWholeRunAccountableClaim p
  runAgreement : PCSAWholeRunAgreementClaim p
  eventPrefixAgreement : PCSAEventPrefixAgreementClaim p
  finalizedMonotone : PCSAFinalizedMonotoneClaim p
  faultCountSlashableBound : PCSAFaultCountSlashableBoundClaim p
  honestNeverSlashed : PCSAHonestNeverSlashedClaim p

end AvailableChain.PCSA.Run

end
