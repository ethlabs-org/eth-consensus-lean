module
public import AvailableChainPCSAProofs.Proofs.Recovery.Anchor
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstHonestSlot
public import AvailableChainPCSAProofs.Proofs.Recovery.LockBound
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs

public section

/-! Recovery suffix interfaces (pcsa34-r4.3b §5.6.1).
Assembly/Recovery supplies Formation, persistence and the restarted chain invariant
for both break kinds. The local root predicate is the corrected F4 field. -/

namespace AvailableChain.PCSA.Run

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))

/-- Corrected F4: the proposer root is on the walk from the common base. -/
def RecoveryRootReachable (s : Slot) : Prop :=
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s)))

/-- The two-read lock bound supplies corrected F4 at the proposer. -/
theorem recovery_root_reachable (s : Slot) (P : Block)
    (rootBounds : ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
      walkBase p nd.st (proposerPC p nd.st) =
        ((proposerPC p nd.st).map PC.target).getD (eraseFG (controls p nd.st).Z) ∧
      Block.Preceq P (walkBase p nd.st (proposerPC p nd.st)) ∧
      ∀ B, LiveLease nd.st B → Block.Preceq B P) :
    RecoveryRootReachable p c E rho s := by
  intro nd hnd
  obtain ⟨he, hb, hl⟩ := rootBounds nd hnd
  dsimp only
  rw [← he]
  exact root_reachable_of_locks_below p nd.st (proposerPC p nd.st) P hb hl _ _ _

/-- The Recovery root clause is the corrected F4 field of `FormationPrem`. -/
theorem pcsa_recovery_rootReachable_iff_formation (s : Slot) :
    RecoveryRootReachable p c E rho s ↔ FormationRootReachable p c E rho s :=
  Iff.rfl

/-- The corrected proposer-root clause holds with the genesis anchor. -/
theorem recovery_genesis_root_reachable (hs : V2.D.ScheduleWellFormed E rho)
    (s : Slot) (hpos : 0 < s) (hwindow : s - 1 ≤ p.k - 1)
    (hp : V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s ∈ rho.honest) :
    RecoveryRootReachable p c E rho s := by
  apply recovery_root_reachable p c E rho s .genesis
  intro nd hn
  refine ⟨recovery_proposer_base p nd.st, Gen.Pure.block_genesis_preceq _, ?_⟩
  exact recovery_genesis_anchor_locks E rho hs s hpos hwindow _ hp _ (Or.inl rfl) nd hn

/-- The output parts of the restarted CI, with the later inclusion producer. -/
structure RecoveryChainRestart (s₁ : Slot) : Prop where
  chain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
    SA.gateTime p.toParams s₁ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho y t')) ∧
    Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
    Block.Compatible (confirmed (storeAt p c E rho x t)) (strong (storeAt p c E rho y t'))
  mono : ∀ x ∈ rho.honest, ∀ t t' : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ t' →
    t' ≤ rho.horizon →
    Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
    Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t'))
  inclusion : ∀ u B, s₁ + 1 ≤ u →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u B →
    (∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (confirmed (storeAt p c E rho x t))) ∧
    (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (strong (storeAt p c E rho x t)))

variable [Fintype V]

/-- Named producers for the recovery suffix.
Assembly/Recovery supplies all fields from the short-break or long-break run
premises. `FormationPrem` carries `FormationRootReachable`; the separate
`RecoveryRootReachable` argument is retained for the existing interface.
RunInputs supplies the stamp-to-reader boundary. -/
structure RecoverySuffixInputs (s₁ : Slot) (ΔF : Time) : Prop where
  firstSlot : ∃ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
  formation : ∀ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF → RecoveryRootReachable p c E rho s₁ →
    ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams s₁) s₁ N.erase
  persistence : ∀ B, Arm p c E rho s₁ B (s₁ + 1) → ArmConcl p c E rho s₁ B (s₁ + 1)
  ciRestart : ∀ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF → RecoveryRootReachable p c E rho s₁ →
    ArmConcl p c E rho s₁ N.erase (s₁ + 1) → RecoveryChainRestart p c E rho s₁

end AvailableChain.PCSA.Run
end

public section
namespace AvailableChain.PCSA.Run
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))

/-- The explicit proposer walk is the recovery root predicate. -/
theorem RecoveryRootReachable_def (s : Slot) :
    RecoveryRootReachable p c E rho s =
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s))) := by rfl

end AvailableChain.PCSA.Run
end
