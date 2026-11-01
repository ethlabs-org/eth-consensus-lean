module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C11] The Recovery lane statements:
stage-1 healing after a short break, `t* ≤ t_GST + G + 7Δ` (pcsa34-r4 5.6.1),
and the long-break bound `2L + G + 8Δ` (5.6.3). The long-break bound is
PROVED-sketch under L*′ (3.7), which the model has; both claims are in
`PCSAClaims`.
Healing uses an honest-proposer recurrence (`Recovery₂.gap`), as FG-SA does;
there is no run recovery regime. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V] [Fintype V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 5.6.1 Theorem conclusion] Healed from slot
`s₁` with the honest proposal `P` (`t* = d_{s₁}`), to the horizon:
- every honest available read from `d_{s₁}` and every honest strong read
  from `z_{s₁}` covers `P` ("covers", not equality: Astra M5);
- from `d_{s₁}` the honest available and strong reads are on one chain
  (pairwise compatible) and monotone at every node;
- every honest proposal `B` of a slot `u ≥ s₁ + 1` is covered by every honest
  available read from `t_u + 6Δ = d_u` and every honest strong read from
  `t_u + 3Δ = z_u`. -/
def HealedFrom (s₁ : Slot) (P : Block) : Prop :=
  (∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
    Block.Preceq P (confirmed (storeAt p c E rho x t))) ∧
  (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
    Block.Preceq P (strong (storeAt p c E rho x t))) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
    SA.gateTime p.toParams s₁ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho y t')) ∧
    Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
    Block.Compatible (confirmed (storeAt p c E rho x t)) (strong (storeAt p c E rho y t'))) ∧
  (∀ x ∈ rho.honest, ∀ t t' : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ t' →
    t' ≤ rho.horizon →
    Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
    Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t'))) ∧
  (∀ (u : Slot) (B : Block), s₁ + 1 ≤ u →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u B →
    (∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (confirmed (storeAt p c E rho x t))) ∧
    (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (strong (storeAt p c E rho x t))))

omit [Fintype V] in
theorem HealedFrom_def (s₁ : Slot) (P : Block) :
    HealedFrom p c E rho s₁ P =
      ((∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
        Block.Preceq P (confirmed (storeAt p c E rho x t))) ∧
      (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
        Block.Preceq P (strong (storeAt p c E rho x t))) ∧
      (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
        SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
        SA.gateTime p.toParams s₁ ≤ t' → t' ≤ rho.horizon →
        Block.Compatible (confirmed (storeAt p c E rho x t))
          (confirmed (storeAt p c E rho y t')) ∧
        Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
        Block.Compatible (confirmed (storeAt p c E rho x t))
          (strong (storeAt p c E rho y t'))) ∧
      (∀ x ∈ rho.honest, ∀ t t' : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ t' →
        t' ≤ rho.horizon →
        Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
        Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t'))) ∧
      (∀ (u : Slot) (B : Block), s₁ + 1 ≤ u →
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u B →
        (∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ rho.horizon →
          Block.Preceq B (confirmed (storeAt p c E rho x t))) ∧
        (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ rho.horizon →
          Block.Preceq B (strong (storeAt p c E rho x t))))) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.6.1 Premises] The short-break premises
with the anchor `cA` and the first post-GST honest slot `s₁`:
- `recovery`: RECOVERY (5.0), with `a ≤ ⌊n/4⌋` and full participation after
  GST; `frame`: stage 1;
- the anchor: a slot `cA > 0` with an honest awake proposer, CLEAN(z_cA)
  (clean from genesis through `z_cA`) and `h_cA ≥ q_N`. Slot 0 has no
  proposal and no PC; the genesis-anchor case is left to
  `LongBreakRecoveredClaim`, with the weaker bound;
- `s₁`: the first slot with an honest awake proposer and `t_{s₁} ≥ t_GST + Δ`;
- `cA < s₁` and `D′ = s₁ − 1 − cA ≤ k − 1`;
- `horizon`: the gate `d_{s₁}` is in the run. -/
structure ShortBreakPrem (G ΔF : Time) (cA s₁ : Slot) : Prop where
  recovery : Recovery₂ p c E rho G ΔF
  frame : StageOneFrame p c E rho
  anchorPos : 0 < cA
  anchorProposer : Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho cA
  anchorClean : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF
  anchorPart : nQuorum p.n ≤ (awakeHonestLabel p c E rho cA).card
  firstProposer : Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s₁
  firstAfterGST : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s₁
  firstMin : ∀ s : Slot, E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s → s < s₁ →
    ¬ Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s
  order : cA < s₁
  window : s₁ - 1 - cA ≤ p.k - 1
  horizon : SA.gateTime p.toParams s₁ ≤ rho.horizon

/-- [PC-SA claims, W0; pcsa34-r4 5.6.1 Theorem, PROVED st. 1; 1.3 healing
ρ_fast; App. B fastRecovered; plan C11] Stage-1 healing after a short break:
under the short-break premises, the honest proposal `P` of `s₁` exists,
`t* = d_{s₁} ≤ t_GST + G + 7Δ`, and the run is healed from `s₁` with `P`. -/
def FastRecoveredClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (G ΔF : Time) (cA s₁ : Slot),
    ShortBreakPrem p c E rho G ΔF cA s₁ →
    ∃ P : Block,
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s₁ P ∧
      SA.gateTime p.toParams s₁ ≤ E.t_GST + G + 7 * p.Δ ∧ HealedFrom p c E rho s₁ P

theorem FastRecoveredClaim_def (p : Params) : FastRecoveredClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
      (G ΔF : Time) (cA s₁ : Slot),
      ShortBreakPrem p c E rho G ΔF cA s₁ →
      ∃ P : Block,
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s₁ P ∧
        SA.gateTime p.toParams s₁ ≤ E.t_GST + G + 7 * p.Δ ∧ HealedFrom p c E rho s₁ P) := by
  rw [FastRecoveredClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.6.3, PROVED-sketch under L*′ (3.7); 1.3
healing ρ (D′ ≥ k); App. B recoveryBound] Stage-1 healing after a general
break: under RECOVERY, the stage-1 frame and `L = (4k − 1)Δ` (`pcsaL`), with
no anchor and no bound on the stale-PC stock, some honest slot `s` with
`d_s ≤ t_GST + 2L + G + 8Δ` has a proposal `P` and the run is healed from
`s` with `P` (5.6.1 steps 2–4). The model has the L*′ lock rule (3.7) and
the lock lifetime `GridCO.lifetime = (4k − 1)Δ = L`, so r4.3's premises are
RECOVERY, L*′, `L = (4k − 1)Δ` and (for Lemma K) common frames and locks
compatible with every honest `F`, which `StageOneFrame` gives. No premise
is missing. The paper status is PROVED-sketch. -/
def LongBreakRecoveredClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (G ΔF : Time),
    Recovery₂ p c E rho G ΔF → StageOneFrame p c E rho →
    E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ≤ rho.horizon →
    ∃ (s : Slot) (P : Block),
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s P ∧
      SA.gateTime p.toParams s ≤ E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ∧
      HealedFrom p c E rho s P

theorem LongBreakRecoveredClaim_def (p : Params) : LongBreakRecoveredClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (G ΔF : Time),
      Recovery₂ p c E rho G ΔF → StageOneFrame p c E rho →
      E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ≤ rho.horizon →
      ∃ (s : Slot) (P : Block),
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s P ∧
        SA.gateTime p.toParams s ≤ E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ∧
        HealedFrom p c E rho s P) := by
  rw [LongBreakRecoveredClaim]

end AvailableChain.PCSA.Run

end
