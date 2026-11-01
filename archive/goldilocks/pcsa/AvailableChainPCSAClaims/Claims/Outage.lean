module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C8, C10] The Outage lane
statements: PC persistence under ARM (pcsa34-r4 5.4.1), its ARM-healthy
instance (5.4.2, the stage-1 form of the generic `PCPersistenceStatement`),
and slow P1 (5.5). Stage 1: every claim takes `StageOneFrame`; the stage-2
forms (J-STABLE, `a ≤ f`, no frame premise) are in `Claims/StageTwo`. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 Theorem, PROVED under ARM, stage 1;
plan C8] Persistence `Π_pc = ∞`: under ARM(s, B, j₀) with `s < j₀`, the
base run premises, `a < ⌈n/2⌉` (5.1 and `q_N − a ≥ 1`) and the stage-1
frame, the conclusion `ArmConcl` holds. Delivery after `v_{j₀}` is
arbitrary (no delivery premise). Gate results are not used. -/
def ArmPersistenceClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (s : Slot) (B : Block) (j₀ : Slot),
    Base₂ p c E rho → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    s < j₀ → Arm p c E rho s B j₀ → ArmConcl p c E rho s B j₀

theorem ArmPersistenceClaim_def (p : Params) : ArmPersistenceClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (s : Slot) (B : Block) (j₀ : Slot),
      Base₂ p c E rho → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      s < j₀ → Arm p c E rho s B j₀ → ArmConcl p c E rho s B j₀) := by
  rw [ArmPersistenceClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.4.2 ARM-healthy, PROVED st. 1; App. B
pcPersistence (StrongArmedRegime shape, lag 3Δ); plan C8] The stage-1 form of
the generic `PCPersistenceStatement` (`PCArmedRegime` fields over `pcsa`):
CLEAN(b₀) (`Clean₂`: healthy prefix, `a < h_j` per label), `a < ⌈n/2⌉`, a read time `T` with
`T + 3Δ ≤ b₀`, and the stage-1 frame. Then every block below an honest strong
read at `T` is in every honest strong read from `b₀` to the horizon
(available follows by the floor). Delivery after `b₀` is arbitrary. -/
def ArmHealthyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    0 ≤ T → T ≤ b₀ → T + 3 * E.Δ ≤ b₀ →
    Gen.V2.Duty.PersistsFrom E rho (pcsaInterface p c (m := m)).strong T b₀

theorem ArmHealthyClaim_def (p : Params) : ArmHealthyClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      0 ≤ T → T ≤ b₀ → T + 3 * E.Δ ≤ b₀ →
      Gen.V2.Duty.PersistsFrom E rho (pcsaInterface p c (m := m)).strong T b₀) := by
  rw [ArmHealthyClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.5 Theorem (stableResilient;
stableResilientFast with fastArmingLag := armingLag), PROVED st. 1; plan
C10] Slow P1: under OUTAGE(T, b₀, b₁) (`k ≥ 2` is a parameter law),
`a < ⌈n/2⌉` (base safety, r4.3 §1.1) and the stage-1 frame, every block below
an honest available read at `T` is below every honest available read in
`[b₀, b₁)`. -/
def PCSASlowP1Claim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
    Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ u ∈ rho.honest, ∀ X : Block, Block.Preceq X (confirmed (storeAt p c E rho u T)) →
      ∀ w ∈ rho.honest, ∀ t : Time, b₀ ≤ t → t < b₁ →
        Block.Preceq X (confirmed (storeAt p c E rho w t))

theorem PCSASlowP1Claim_def (p : Params) : PCSASlowP1Claim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
      Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ u ∈ rho.honest, ∀ X : Block, Block.Preceq X (confirmed (storeAt p c E rho u T)) →
        ∀ w ∈ rho.honest, ∀ t : Time, b₀ ≤ t → t < b₁ →
          Block.Preceq X (confirmed (storeAt p c E rho w t))) := by
  rw [PCSASlowP1Claim]

end AvailableChain.PCSA.Run

end
