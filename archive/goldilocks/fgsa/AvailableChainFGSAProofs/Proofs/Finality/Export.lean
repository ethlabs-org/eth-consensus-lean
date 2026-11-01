module
public import AvailableChainFGSAProofs.Proofs.Finality.Suppliers
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers
public import AvailableChainFGSAProofs.Proofs.Finality.Kernel
public import AvailableChainFGSAProofs.Proofs.Finality.Joined
public import AvailableChainFGSAProofs.Proofs.Finality.TailBatch
public import AvailableChainFGSAProofs.Proofs.Finality.Local
public import AvailableChainFGSAProofs.Proofs.Finality.Proposal
public import AvailableChainFGSAProofs.Proofs.Finality.Above

public section

namespace AvailableChain.FGSA.Run

/-- Blueprint 01:126–129, plan item 18; lead ruling B30. DC: INTENTIONAL AC service contract.
Recovery supplies every public TVote read within its previous-slot GST cutoff. -/
theorem fgsa_kernelACSide_W (p : Params) :
    KernelACSideClaim_W p := by
  intro G ΔF _ _ _ _ _ c E rho w hr hbound hInput
  exact fgsa_coreServices E rho hr.base w
    (finality_vote_receipts hr.toRecovery₂)

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1171–1305 (F1–F9), lead ruling B34: export the forward W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention, exact signed
rows and actual receipt guards. The suppliers retain the lane boundary. -/
theorem fgsa_finalityKernel_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityKernelClaim_W p := by
  intro G ΔF hδ V _ _ In c E rho pt hK
  exact finality_kernel_W_of p c E rho
    (finality_action_receipts hK.set (hGenesis c E rho)) G ΔF hδ pt hK
    (hsel c E rho hK.set.base.valid) (horigin c E rho hK.set.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF pt hK) (hXing c E rho G ΔF pt hK)
    (hI3 c E rho G ΔF pt hK) (hStrat c E rho G ΔF pt hK)
    (hEmittedSource c E rho G ΔF pt hK) (hcapBefore c E rho G ΔF pt hK)

/-- Paper 00:1119–1134, 22:1171–1305; plan §4: export the joined W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt.
The joined premise supplies every split supplier premise. -/
theorem fgsa_finalityKernelJoined_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityKernelJoinedClaim_W p := by
  intro G ΔF hδ V _ _ In c E rho pt h
  obtain ⟨w, hK⟩ := finality_kernel_prem_W_of_joined p c E rho G ΔF pt h
  let kpt : KernelPt := ⟨w, pt.r⟩
  exact finality_kernel_joined_W_of p c E rho
    (finality_action_receipts h.set (hGenesis c E rho)) G ΔF hδ pt h
    (hsel c E rho h.set.base.valid) (horigin c E rho h.set.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF kpt hK) (hXing c E rho G ΔF kpt hK)
    (hI3 c E rho G ΔF kpt hK) (hStrat c E rho G ΔF kpt hK)
    (hEmittedSource c E rho G ΔF kpt hK) (hcapBefore c E rho G ΔF kpt hK)

/-- Paper 22:1985–2009 (FT-Tail-W): export the full tail kernel as the frozen claim.
DC: INTENTIONAL: Assembly supplies the existing producers at each Tail premise. -/
theorem fgsa_tailKernel_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (hqc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RMono p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho) :
    TailKernelClaim_W p := by
  intro G ΔF _ V _ _ In c E rho pt hT
  exact tail_kernel_W_full_of G ΔF pt
    (finality_action_receipts hT.set (hGenesis c E rho))
    (finality_tail_head_receipts hT (hGenesis c E rho)) hT
    (hOrigin c E rho G ΔF pt hT)
    (hBatch c E rho G ΔF pt hT)
    (hSOCOVTarget c E rho G ΔF pt hT)
    (hqc c E rho G ΔF pt hT)
    (hI3 c E rho G ΔF pt hT)
    (hStrat c E rho G ΔF pt hT)
    (hEmittedSource c E rho G ΔF pt hT)
    (hcapBefore c E rho G ΔF pt hT)
    (hmono c E rho G ΔF pt hT)
    (hXing c E rho G ΔF pt hT)

/-- Paper 22:1371–1400; firstfin plan §5 C. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the inherited kernel suppliers;
the frozen claim keeps its common HealingInput and full horizon. -/
theorem fgsa_finalityLivenessRecFE_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityLivenessRecFEClaim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_supplier_bundle p hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource
      hcapBefore c E rho G ΔF h.set.core.toRecovery₂
  obtain ⟨U, hS, hheight, hacc⟩ := finality_liveness_FE_W_of p c E rho
    (finality_action_receipts h.set.core.toRecovery₂ (hGenesis c E rho))
    G ΔF g w hδ pt h
    sel origin
    batch qc crossing
    safety strat
    emitted cap
  exact ⟨U, fun x hx => hS x hx.1, hheight, hacc⟩

/-- Paper 22:1371–1400; firstfin plan §5 C. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the inherited kernel suppliers;
the frozen claim keeps its common HealingInput and full horizon. -/
theorem fgsa_finalityLivenessRecF4_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityLivenessRecF4Claim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  apply fgsa_finalityLivenessRecFE_W_of p hGenesis hsel horigin hBatch hQC hXing hI3 hStrat
    hEmittedSource hcapBefore G ΔF g w hδ c E rho pt
  exact ⟨⟨h.set.core, h.set.bound, F4_W_implies_FE_W h.set.recur⟩,
    h.input, h.start, h.hhor⟩

/-- Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL specified proposal coverage before its local W deadline.
Recovery₂ in the frozen package supplies the inherited kernel suppliers. -/
theorem fgsa_proposalFinalRecFE_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    ProposalFinalRecFEClaim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_supplier_bundle p hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource
      hcapBefore c E rho G ΔF h.set.core.toRecovery₂
  exact proposal_final_FE_W_of p c E rho
    (finality_action_receipts h.set.core.toRecovery₂ (hGenesis c E rho))
    G ΔF g w hδ pt h
    sel origin
    batch qc crossing
    safety strat
    emitted cap

/-- Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL specified proposal coverage before its local W deadline.
Recovery₂ in the frozen package supplies the inherited kernel suppliers. -/
theorem fgsa_proposalFinalRecF4_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    ProposalFinalRecF4Claim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_supplier_bundle p hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource
      hcapBefore c E rho G ΔF h.set.core.toRecovery₂
  exact proposal_final_F4_W_of p c E rho
    (finality_action_receipts h.set.core.toRecovery₂ (hGenesis c E rho))
    G ΔF g w hδ pt h
    sel origin
    batch qc crossing
    safety strat
    emitted cap

end AvailableChain.FGSA.Run
end

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
The frozen claim keeps both receipt horizons. Kernel and frontier inputs stay conditional. -/
theorem fgsa_aboveFrontierRecFE_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hNames : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      BaseSet p c E rho → ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    AboveFrontierRecFEClaim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_supplier_bundle p hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource
      hcapBefore c E rho G ΔF h.set.core.toRecovery₂
  exact above_frontier_FE_W_of p c E rho
    (finality_action_receipts h.set.core.toRecovery₂ (hGenesis c E rho))
    G ΔF g w hδ pt h
    sel origin
    batch qc crossing
    safety strat
    emitted cap
    (hNames c E rho h.set.core.base) (hOrigin c E rho h.set.core.base.valid)

/-- Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
The frozen claim keeps both receipt horizons. Kernel and frontier inputs stay conditional. -/
theorem fgsa_aboveFrontierRecF4_W_of (p : Params)
    (hGenesis : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (D : Time) (x : V), TargetReceiptService E rho .genesis D x)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hNames : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      BaseSet p c E rho → ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    AboveFrontierRecF4Claim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_supplier_bundle p hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource
      hcapBefore c E rho G ΔF h.set.core.toRecovery₂
  exact above_frontier_F4_W_of p c E rho
    (finality_action_receipts h.set.core.toRecovery₂ (hGenesis c E rho))
    G ΔF g w hδ pt h
    sel origin
    batch qc crossing
    safety strat
    emitted cap
    (hNames c E rho h.set.core.base) (hOrigin c E rho h.set.core.base.valid)

end AvailableChain.FGSA.Run
end

-- P-Fi round 2: strict audits of the conditional claim suppliers.
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierRecF4_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierRecFE_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_finalityKernelJoined_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_finalityKernel_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessRecF4_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessRecFE_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_kernelACSide_W
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalRecF4_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalRecFE_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_tailKernel_W_of
