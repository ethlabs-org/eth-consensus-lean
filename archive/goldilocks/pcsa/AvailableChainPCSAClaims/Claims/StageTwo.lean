module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C15 (stage 2, shape only)] The
stage-2 statements that W0 can state without new protocol decisions:
persistence under ARM with J-STABLE and `a ≤ f` (pcsa34-r4 5.4.1), and the
PC-SA-native stage-2 forms of ARM-healthy (5.4.2) and strong inclusion
(5.2.3) over `Clean₂` with `a ≤ f` and no frame premise. The generic
`PCCompanion` instance over `pcsa` is not stated: `PCArmedRegime` and
`PCIncludedRegime` do not bound the faulty FG seats, so an unrestricted
instance is false (W0 review, item 1). Not stated: CI item (vi) (the
[FGSA.cleanFrame] transfer is HAND), the Π scope (5.4.3, PROVED-paper,
cited), and B_H^PC (5.6.4, PENDING: its values need a PC-SA proof). No proof
in M1. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 (stage 2) J-STABLE(B)] No honest `F`
conflicts with `B` at any event state, and from `e_s` no block that conflicts
with `B` is justified at an honest node. The justified blocks are all the
justification evidence of the store (`HeldJustification`): the stored
`(h_j, J)` and, for every held FG block, its window pair and its retained
window entries, at every honest event state from `e_s` (also the
intermediate states inside one time). -/
def JStable (s : Slot) (B : Block) : Prop :=
  (∀ x ∈ rho.honest, ∀ i : Nat,
    Block.Compatible (eraseFG (storeBefore p c E rho i x).fg.F) B) ∧
  HonestStatesFrom p c E rho (SA.earlyTime p.toParams s) (fun st =>
    ∀ (h : Nat) (X : FGBlock (Fin p.n)), HeldJustification p st h X →
      Block.Compatible (eraseFG X) B)

theorem JStable_def (s : Slot) (B : Block) :
    JStable p c E rho s B =
      ((∀ x ∈ rho.honest, ∀ i : Nat,
        Block.Compatible (eraseFG (storeBefore p c E rho i x).fg.F) B) ∧
      HonestStatesFrom p c E rho (SA.earlyTime p.toParams s) (fun st =>
        ∀ (h : Nat) (X : FGBlock (Fin p.n)), HeldJustification p st h X →
          Block.Compatible (eraseFG X) B)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 (stage 2), PROVED under ARM; plan
C15] Persistence in stage 2: ARM(s, B, j₀), `a ≤ f` (`FGSafetyBound`),
`a < ⌈n/2⌉`, and J-STABLE(B), with no frame premise. -/
def ArmPersistenceJStableClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (B : Block) (j₀ : Slot),
    Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
    s < j₀ → Arm p c E rho s B j₀ → JStable p c E rho s B → ArmConcl p c E rho s B j₀

theorem ArmPersistenceJStableClaim_def (p : Params) : ArmPersistenceJStableClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (B : Block) (j₀ : Slot),
      Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
      s < j₀ → Arm p c E rho s B j₀ → JStable p c E rho s B → ArmConcl p c E rho s B j₀) := by
  rw [ArmPersistenceJStableClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.4.2 ARM-healthy (stage 2), 5.4.3
"CLEAN from genesis: W₀ holds"; plan C8, C15] The stage-2 form of
`ArmHealthyClaim`: CLEAN(b₀) (`Clean₂`, which includes the linked FG seats
of `Base₂`), `a < ⌈n/2⌉`, `a ≤ f` (`FGSafetyBound`; with linked seats it
bounds the faulty FG seats), a read time `T` with `T + 3Δ ≤ b₀`, and no
frame premise. Then every block below an honest strong read at `T` is in
every honest strong read from `b₀` to the horizon. J-STABLE comes from CI
(vi) up to `b₀` and from Lemma 5.4.3 (W₀ ⇒ J-STABLE) after it. Status:
PROVED modulo [FGSA.cleanFrame] (HAND). -/
def ArmHealthyStageTwoClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (T b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → FGSafetyBound p c rho →
    0 ≤ T → T ≤ b₀ → T + 3 * E.Δ ≤ b₀ →
    Gen.V2.Duty.PersistsFrom E rho (pcsaInterface p c).strong T b₀

theorem ArmHealthyStageTwoClaim_def (p : Params) : ArmHealthyStageTwoClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (T b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → FGSafetyBound p c rho →
      0 ≤ T → T ≤ b₀ → T + 3 * E.Δ ≤ b₀ →
      Gen.V2.Duty.PersistsFrom E rho (pcsaInterface p c).strong T b₀) := by
  rw [ArmHealthyStageTwoClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Strong inclusion (3Δ) (stage 2); plan
C9, C15] The stage-2 form of `StrongIncludedClaim`: CLEAN(b₀) (`Clean₂`),
`a ≤ ⌊n/4⌋`, `a ≤ f`, no frame premise, and `h_u ≥ q_N` at the honest slot
`u`. Then the honest proposal `P` of `u` is below every honest strong read
from `z_u` to the cut. Reconcile drops nothing by CI (vi). Status: PROVED
modulo [FGSA.cleanFrame] (HAND). -/
def StrongIncludedStageTwoClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → FGSafetyBound p c rho →
    ∀ (u : Slot) (P : Block),
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c).toInterface rho u P →
      nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card →
      ∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ b₀ →
        Block.Preceq P (strong (storeAt p c E rho x t))

theorem StrongIncludedStageTwoClaim_def (p : Params) : StrongIncludedStageTwoClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → QuarterCap p c rho → FGSafetyBound p c rho →
      ∀ (u : Slot) (P : Block),
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c).toInterface rho u P →
        nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card →
        ∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ b₀ →
          Block.Preceq P (strong (storeAt p c E rho x t))) := by
  rw [StrongIncludedStageTwoClaim]

end AvailableChain.PCSA.Run

end
