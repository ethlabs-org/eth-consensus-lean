module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant -- shake: keep (r2 owner)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetOpening

public section

/-! Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
Joint induction keeps the two extra cut predicates outside PostResetInv.
Order: reset lease, lease safety, F provenance, raw transfer, opening domain,
service. Compatibility and protected-body retention use Healing producers. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
All event-prefix guards are empty at zero. An honest proposal supplies a
tick at its proposal time, so its inclusive time cut is positive. -/
theorem postReset_joint_zero (w : HealingWitness) :
    PostResetInv p c E rho w 0 ∧ PostResetResetLeaseCompatible p c E rho w 0 ∧
      PostResetOpeningDomain p c E rho w 0 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rw [PostResetProtectedKept_def]
      intro j hj
      exact False.elim (Nat.not_lt_zero j hj)
    · rw [PostResetHighCompatible_def]
      intro K K' s s' hK
      obtain ⟨j, x, r, a, hj, _⟩ := hK
      exact False.elim (Nat.not_lt_zero j hj)
    · rw [PostResetResetCompatible_def]
      intro K s hK
      obtain ⟨j, x, r, a, hj, _⟩ := hK
      exact False.elim (Nat.not_lt_zero j hj)
    · rw [PostResetLeaseSafe_def]
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
    · rw [PostResetFProv_def]
      intro j hj
      exact False.elim (Nat.not_lt_zero j hj)
    · rw [PostResetRawTransfer_def]
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
    · rw [PostResetService_def]
      intro v Q hQ _hv hcut
      obtain ⟨_, o, ⟨j, hj, _hem⟩, _hb⟩ := hQ
      rw [proposalTime_fgsa p c v] at hj
      have hmem := List.mem_of_getElem? hj
      have hpos : 0 < timeIdx rho (SA.proposalTime p.toParams v) := by
        exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, by
          change decide (SA.proposalTime p.toParams v ≤ SA.proposalTime p.toParams v) = true
          exact decide_eq_true le_rfl⟩)
      exact False.elim (Nat.not_lt_of_ge hcut hpos)
  · rw [PostResetResetLeaseCompatible_def]
    intro j hj
    exact False.elim (Nat.not_lt_zero j hj)
  · rw [PostResetOpeningDomain_def]
    intro k hk
    exact False.elim (Nat.not_lt_zero k hk)


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15–H.18:2885–3064; plan "Induction design"; ruling R3.
This named step uses the prior triple and only earlier successor fields. -/
def PostResetResetLeaseStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15–H.18:2885–3064; plan "Induction design"; ruling R3.
This named step uses the prior triple and only earlier successor fields. -/
def PostResetLeaseStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15–H.18:2885–3064; plan "Induction design"; ruling R3.
This named step uses the prior triple and only earlier successor fields. -/
def PostResetRawStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15–H.18:2885–3064; plan "Induction design"; ruling R3.
This named step uses the prior triple and only earlier successor fields. -/
def PostResetOpeningDomainStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15–H.18:2885–3064; plan "Induction design"; ruling R3.
This named step uses the prior triple and only earlier successor fields. -/
def PostResetServiceStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1) →
  PostResetService p c E rho w (i + 1)

-- Equation exports for BUILD §7.2 B3a.
theorem PostResetResetLeaseStep_def (w : HealingWitness) (i : Nat) :
    PostResetResetLeaseStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1)) := by rfl

theorem PostResetLeaseStep_def (w : HealingWitness) (i : Nat) :
    PostResetLeaseStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1)) := by rfl

theorem PostResetRawStep_def (w : HealingWitness) (i : Nat) :
    PostResetRawStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1)) := by rfl

theorem PostResetOpeningDomainStep_def (w : HealingWitness) (i : Nat) :
    PostResetOpeningDomainStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1)) := by rfl

theorem PostResetServiceStep_def (w : HealingWitness) (i : Nat) :
    PostResetServiceStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
    PostResetOpeningDomain p c E rho w i →
  PostResetResetLeaseCompatible p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetOpeningDomain p c E rho w (i + 1) →
  PostResetService p c E rho w (i + 1)) := by rfl

/-- The reset transfer service is produced only under its release horizon. -/
theorem healing_resetTransferCore_recovery [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (xing : RXing p c E rho) (cap : RCap p c E rho) (source : TSrc p c E rho)
    (w : HealingWitness) (h0r : H0Reset p c E rho w) :
    ResetTransferCore p c E rho w := by
  rw [ResetTransferCore_def]
  intro hhor
  have hearly : SA.earlyTime p.toParams w.sStar ≤ rho.horizon := by
    apply le_trans _ hhor
    change 4 * p.Δ * (w.sStar : Int) + 2 * p.Δ ≤
      4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E (SA.voteTime p.toParams w.sStar) := by
    refine ⟨4 * w.sStar + 1, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (w.sStar : Int) + p.Δ = _
    push_cast
    ring
  have htime : SA.voteTime p.toParams w.sStar + p.Δ =
      SA.earlyTime p.toParams w.sStar := by
    change 4 * p.Δ * (w.sStar : Int) + p.Δ + p.Δ =
      4 * p.Δ * (w.sStar : Int) + 2 * p.Δ
    ring
  have hcore := healing_resetTransferCore E rho hrec.toRecovery₂ xing cap source mono w h0r
    (fun x hx j z W hz hj hW _ hF => by
      rw [← htime] at hF ⊢
      exact healing_target_service_of_tick E rho hrec hz hx hj
        (((storeBundle_stateBefore E rho j z).cstore.baseTree _).mpr ⟨W, hW, rfl⟩)
        hpub h0r.synchronous (htime ▸ hearly)
        (Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq hF))))
  exact (ResetTransferCore_def p c E rho w ▸ hcore) hhor

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
    (stepOD : ∀ i, PostResetOpeningDomainStep p c E rho w i)
    (stepService : ∀ i, PostResetServiceStep p c E rho w i)

include hrec mono emittedNonempty emittedName writes xing origin cap source
    heldRows finalityCap hhead h0r stepRL stepLease stepRaw stepOD stepService

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
Order: reset lease, lease safety, F provenance, raw transfer, opening domain,
service. Each open step has a named full type. All other fields use producers.
Foundations producers: fgsa_rMono, sourceDiscipline_emittedNonempty,
emittedName_window, fgsa_leaseOrigins_lastWrite, fgsa_rXing,
sourceDiscipline_qcOrigin, fgsa_rCap_channel, sourceDiscipline_tSrc,
held_chain_row_origin_before, fgsa_finalityCap, cap_finality_head. -/
theorem postReset_joint_all :
    ∀ i, PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      PostResetOpeningDomain p c E rho w i := by
  intro i
  induction i with
  | zero => exact postReset_joint_zero p c E rho w
  | succ i ih =>
    have hrl := stepRL i ih
    have hlease := stepLease i ih hrl
    have hfprov := postReset_fProv_all (hroots := hrec.base.idealization) p c E rho
      hrec.base.valid
      origin heldRows finalityCap hhead xing h0r (i + 1)
    have hraw := stepRaw i ih hrl hlease hfprov
    have hod := stepOD i ih hrl hlease hfprov hraw
    have hservice := stepService i ih hrl hlease hfprov hraw hod
    have hLoss := healing_loss_service_scope_recovery E rho hrec mono source
      emittedNonempty emittedName
    have htransfer := healing_resetTransferCore_recovery p c E rho hrec mono xing cap source w h0r
    refine ⟨⟨?_, ?_, ?_, hlease, hfprov, hraw, hservice⟩, hrl, hod⟩
    · exact postReset_protected_kept_succ (hroots := hrec.base.idealization) p c E rho
        hrec.base.valid.toScheduleWellFormed
        xing origin h0r htransfer ih.1
    · exact postReset_high_compatible_all p c E rho hrec hLoss mono emittedNonempty emittedName
        writes xing origin h0r (i + 1)
    · exact postReset_reset_compatible_all p c E rho hrec hLoss mono emittedNonempty emittedName
        writes xing origin h0r (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
Projection of the joint induction with the same named steps and producer inputs. -/
theorem postReset_inv_all : ∀ i, PostResetInv p c E rho w i :=
  fun i => (postReset_joint_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepOD stepService i).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
Projection of the joint induction with the same named steps and producer inputs. -/
theorem postReset_reset_lease_compatible_all : ∀ i, PostResetResetLeaseCompatible p c E rho w i :=
  fun i => (postReset_joint_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepOD stepService i).2.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12–H.18:2652–3064; plan "Induction design"; ruling R3.
Projection of the joint induction with the same named steps and producer inputs. -/
theorem postReset_opening_domain_all : ∀ i, PostResetOpeningDomain p c E rho w i :=
  fun i => (postReset_joint_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead h0r
    stepRL stepLease stepRaw stepOD stepService i).2.2

end Induction

end AvailableChain.FGSA.Run
end
