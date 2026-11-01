module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint

public section

/-! Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The joint induction keeps the cone after raw transfer and before opening domain.
The old joint induction and its step definitions stay unchanged. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The run-level PostResetRetainedCone body (PostResetRead.lean:21) with the cut guard
`timeIdx rho (voteTime s) ≤ i`. -/
def PostResetRetainedConeP (w : HealingWitness) (i : Nat) : Prop :=
  ∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  timeIdx rho (SA.voteTime p.toParams s) ≤ i →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (N : NamedProposal p.n),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The retained-cone step uses the prior joint fields and the new raw-transfer field. -/
def PostResetConeStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The opening-domain step uses the prior joint fields and the new retained cone. -/
def PostResetOpeningDomainStep₂ (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The service step uses the prior joint fields, the new retained cone and opening domain. -/
def PostResetServiceStep₂ (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1) →
  PostResetService p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Equation export for BUILD §7.2 B3a. -/
theorem PostResetRetainedConeP_def (w : HealingWitness) (i : Nat) :
    PostResetRetainedConeP p c E rho w i = (
  ∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  timeIdx rho (SA.voteTime p.toParams s) ≤ i →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (N : NamedProposal p.n),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Equation export for BUILD §7.2 B3a. -/
theorem PostResetConeStep_def (w : HealingWitness) (i : Nat) :
    PostResetConeStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1)) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Equation export for BUILD §7.2 B3a. -/
theorem PostResetOpeningDomainStep₂_def (w : HealingWitness) (i : Nat) :
    PostResetOpeningDomainStep₂ p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1)) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Equation export for BUILD §7.2 B3a. -/
theorem PostResetServiceStep₂_def (w : HealingWitness) (i : Nat) :
    PostResetServiceStep₂ p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1) →
  PostResetService p c E rho w (i + 1)) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
A larger cut supplies the cone at every smaller cut. -/
theorem PostResetRetainedConeP_mono (w : HealingWitness) {i j : Nat}
    (hij : i ≤ j) (hcone : PostResetRetainedConeP p c E rho w j) :
    PostResetRetainedConeP p c E rho w i := by
  rw [PostResetRetainedConeP_def] at hcone ⊢
  intro s hs hh hcut
  exact hcone s hs hh (hcut.trans hij)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Use the cut at the proposal's HEAD deadline to obtain the run-level cone. -/
theorem postReset_retainedCone_of_cut (w : HealingWitness)
    (hcone : ∀ i, PostResetRetainedConeP p c E rho w i) :
    PostResetRetainedCone p c E rho w := by
  rw [postResetRetainedCone_iff]
  intro s hs hh
  have hcut := hcone (timeIdx rho (SA.voteTime p.toParams s))
  rw [PostResetRetainedConeP_def] at hcut
  intro ip x hx
  exact hcut s hs hh le_rfl hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
An actual proposal tick makes its inclusive HEAD cut positive. -/
theorem postReset_cone_zero (w : HealingWitness) :
    PostResetRetainedConeP p c E rho w 0 := by
  rw [PostResetRetainedConeP_def]
  intro s _hs _hh hcut ip x _hx hip
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hmem := List.mem_of_getElem? hip
  have hpos : 0 < timeIdx rho (SA.voteTime p.toParams s) := by
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, by
      change decide (SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s) = true
      exact decide_eq_true htv⟩)
  exact False.elim (Nat.not_lt_of_ge hcut hpos)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Extend the existing empty-cut triple with its vacuous cone. -/
theorem postReset_joint₂_zero (w : HealingWitness) :
    PostResetInv p c E rho w 0 ∧ PostResetResetLeaseCompatible p c E rho w 0 ∧
      PostResetOpeningDomain p c E rho w 0 ∧ PostResetRetainedConeP p c E rho w 0 := by
  obtain ⟨hinv, hrl, hod⟩ := postReset_joint_zero p c E rho w
  exact ⟨hinv, hrl, hod, postReset_cone_zero p c E rho w⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The old opening-domain step drops the two added cone hypotheses. -/
theorem postReset_openingDomainStep₂_of_old (w : HealingWitness) (i : Nat)
    (hstep : PostResetOpeningDomainStep p c E rho w i) :
    PostResetOpeningDomainStep₂ p c E rho w i := by
  rw [PostResetOpeningDomainStep_def] at hstep
  rw [PostResetOpeningDomainStep₂_def]
  intro hprior hrl hlease hfprov hraw _hcone
  exact hstep ⟨hprior.1, hprior.2.1, hprior.2.2.1⟩ hrl hlease hfprov hraw

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
The old service step drops the two added cone hypotheses. -/
theorem postReset_serviceStep₂_of_old (w : HealingWitness) (i : Nat)
    (hstep : PostResetServiceStep p c E rho w i) :
    PostResetServiceStep₂ p c E rho w i := by
  rw [PostResetServiceStep_def] at hstep
  rw [PostResetServiceStep₂_def]
  intro hprior hrl hlease hfprov hraw _hcone hod
  exact hstep ⟨hprior.1, hprior.2.1, hprior.2.2.1⟩ hrl hlease hfprov hraw hod

section Induction
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
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

variable
    (stepRL : ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ i, PostResetRawStep p c E rho w i)
    (stepCone : ∀ i, PostResetConeStep p c E rho w i)
    (stepOD : ∀ i, PostResetOpeningDomainStep₂ p c E rho w i)
    (stepService : ∀ i, PostResetServiceStep₂ p c E rho w i)

include hrec mono emittedNonempty emittedName writes xing origin cap source
    heldRows finalityCap hhead h0r stepRL stepLease stepRaw stepCone stepOD stepService

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Order: reset lease, lease safety, F provenance, raw transfer, cone,
opening domain, service. Each open step has a named full type. All other fields use producers.
Foundations producers: fgsa_rMono, sourceDiscipline_emittedNonempty,
emittedName_window, fgsa_leaseOrigins_lastWrite, fgsa_rXing,
sourceDiscipline_qcOrigin, fgsa_rCap_channel, sourceDiscipline_tSrc,
held_chain_row_origin_before, fgsa_finalityCap, cap_finality_head. -/
theorem postReset_joint₂_all :
    ∀ i, PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i := by
  intro i
  induction i with
  | zero => exact postReset_joint₂_zero p c E rho w
  | succ i ih =>
    have stepRLAt := stepRL i
    rw [PostResetResetLeaseStep_def] at stepRLAt
    have stepLeaseAt := stepLease i
    rw [PostResetLeaseStep_def] at stepLeaseAt
    have stepRawAt := stepRaw i
    rw [PostResetRawStep_def] at stepRawAt
    have stepConeAt := stepCone i
    rw [PostResetConeStep_def] at stepConeAt
    have stepODAt := stepOD i
    rw [PostResetOpeningDomainStep₂_def] at stepODAt
    have stepServiceAt := stepService i
    rw [PostResetServiceStep₂_def] at stepServiceAt
    have prior : PostResetInv p c E rho w i ∧
        PostResetResetLeaseCompatible p c E rho w i ∧
        PostResetOpeningDomain p c E rho w i := ⟨ih.1, ih.2.1, ih.2.2.1⟩
    have hrl := stepRLAt prior
    have hlease := stepLeaseAt prior hrl
    have hfprov := postReset_fProv_all (hroots := hrec.base.idealization) p c E rho
      hrec.base.valid
      origin heldRows finalityCap hhead xing h0r (i + 1)
    have hraw := stepRawAt prior hrl hlease hfprov
    have hcone := stepConeAt ih hrl hlease hfprov hraw
    have hod := stepODAt ih hrl hlease hfprov hraw hcone
    have hservice := stepServiceAt ih hrl hlease hfprov hraw hcone hod
    have hLoss := healing_loss_service_scope_recovery E rho hrec mono source
      emittedNonempty emittedName
    have htransfer := healing_resetTransferCore_recovery p c E rho hrec mono xing cap source w h0r
    refine ⟨⟨?_, ?_, ?_, hlease, hfprov, hraw, hservice⟩, hrl, hod, hcone⟩
    · exact postReset_protected_kept_succ (hroots := hrec.base.idealization) p c E rho
        hrec.base.valid.toScheduleWellFormed
        xing origin h0r htransfer ih.1
    · exact postReset_high_compatible_all p c E rho hrec hLoss mono emittedNonempty emittedName
        writes xing origin h0r (i + 1)
    · exact postReset_reset_compatible_all p c E rho hrec hLoss mono emittedNonempty emittedName
        writes xing origin h0r (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Projection with the same named steps and producer inputs. -/
theorem postReset_inv_all₂ : ∀ i, PostResetInv p c E rho w i :=
  fun i => (postReset_joint₂_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepCone stepOD stepService i).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Projection with the same named steps and producer inputs. -/
theorem postReset_cone_all : ∀ i, PostResetRetainedConeP p c E rho w i :=
  fun i => (postReset_joint₂_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepCone stepOD stepService i).2.2.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Centaur FGSA-S5-CONE retained-cone route; plan "Induction design"; ruling R3.
Projection with the same named steps and producer inputs. -/
theorem postReset_retainedCone_run : PostResetRetainedCone p c E rho w :=
  postReset_retainedCone_of_cut p c E rho w
    (postReset_cone_all p c E rho hrec mono emittedNonempty emittedName writes
      xing origin cap source heldRows finalityCap hhead h0r
      stepRL stepLease stepRaw stepCone stepOD stepService)

end Induction

end AvailableChain.FGSA.Run
end
