module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep (joint)

set_option linter.privateModule false

/-! Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The zero fixture consumes C. The successor fixture applies E to explicit
step functions and projects the retained cone at the first successor cut. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetJoint2
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- JOINT2-C-zero (pure/model): consume the complete empty-cut quadruple.
example (w : HealingWitness) :
    PostResetInv p c E rho w 0 ∧ PostResetResetLeaseCompatible p c E rho w 0 ∧
      PostResetOpeningDomain p c E rho w 0 ∧ PostResetRetainedConeP p c E rho w 0 :=
  postReset_joint₂_zero p c E rho w

variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (cap : RCap p c E rho) (source : TSrc p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (finalityCap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono emittedNonempty emittedName writes xing origin cap source
    heldRows finalityCap hhead h0r

-- JOINT2-E-cone-one (conditional package): concrete constant step functions.
-- The fixture supplies successor witnesses; E still produces the other fields.
example
    (nextRL : ∀ i, PostResetResetLeaseCompatible p c E rho w (i + 1))
    (nextLease : ∀ i, PostResetLeaseSafe p c E rho w (i + 1))
    (nextRaw : ∀ i, PostResetRawTransfer p c E rho w (i + 1))
    (nextCone : ∀ i, PostResetRetainedConeP p c E rho w (i + 1))
    (nextOD : ∀ i, PostResetOpeningDomain p c E rho w (i + 1))
    (nextService : ∀ i, PostResetService p c E rho w (i + 1)) :
    PostResetRetainedConeP p c E rho w 1 := by
  have stepRL : ∀ i, PostResetResetLeaseStep p c E rho w i := by
    intro i
    rw [PostResetResetLeaseStep_def]
    exact fun _prior => nextRL i
  have stepLease : ∀ i, PostResetLeaseStep p c E rho w i := by
    intro i
    rw [PostResetLeaseStep_def]
    exact fun _prior _rl => nextLease i
  have stepRaw : ∀ i, PostResetRawStep p c E rho w i := by
    intro i
    rw [PostResetRawStep_def]
    exact fun _prior _rl _lease _fprov => nextRaw i
  have stepCone : ∀ i, PostResetConeStep p c E rho w i := by
    intro i
    rw [PostResetConeStep_def]
    exact fun _prior _rl _lease _fprov _raw => nextCone i
  have stepOD : ∀ i, PostResetOpeningDomainStep₂ p c E rho w i := by
    intro i
    rw [PostResetOpeningDomainStep₂_def]
    exact fun _prior _rl _lease _fprov _raw _cone => nextOD i
  have stepService : ∀ i, PostResetServiceStep₂ p c E rho w i := by
    intro i
    rw [PostResetServiceStep₂_def]
    exact fun _prior _rl _lease _fprov _raw _cone _od => nextService i
  exact (postReset_joint₂_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepCone stepOD stepService 1).2.2.2

end AvailableChain.FGSA.Run.Tests.HealingPostResetJoint2
end
