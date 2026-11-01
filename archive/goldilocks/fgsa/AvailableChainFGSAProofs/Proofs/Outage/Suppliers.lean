module
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionOrigins
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (read API)
public import AvailableChainFGSAClaims.Statements.Packages.Finality -- shake: keep (W types)
public import AvailableChainFGSAClaims.Statements.Packages.Inclusion -- shake: keep (cut types)
public import AvailableChainFGSAClaims.Statements.Packages.Safety -- shake: keep (base types)
public import AvailableChainFGSAClaims.Statements.FinalityApi -- shake: keep (F API)
public import AvailableChainFGSAClaims.Statements.Fold -- shake: keep (batch API)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

theorem outage_supplier_history (p : Params)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hordered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
        confirmedReader p c E rho x (SA.gateTime p.toParams r) →
        confirmedReader p c E rho y (SA.gateTime p.toParams s) →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ j x s, j < timeIdx rho pt.b₀ → x ∈ rho.honest → enabledGateAt p c E rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ pt.b₀ → gateResult p c E rho x s = some (some B) →
        joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
        vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i v, i ≤ timeIdx rho pt.b₀ → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → enabledGateAt p c E rho j v s →
          V2.D.restartFree rho v j i → FGSA.activeCompatible st C = true →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)))
    (hrows : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i j x r a e, i ≤ timeIdx rho pt.b₀ → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {ΔF : Time} (hset : CleanSet p c E rho ΔF) (hpos : 0 < rho.horizon) :
    (SrcFrameAboveStmt p c E rho) ∧
    (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
    (∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest → enabledGateAt p c E rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
    (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
        joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
        vHead p c E rho y s = some H → Block.Preceq B H) ∧
    (∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → enabledGateAt p c E rho j v s →
          V2.D.restartFree rho v j i → FGSA.activeCompatible st C = true →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
    (∀ i j x r a e, i ≤ timeIdx rho rho.horizon → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) :=
  let hq := hset.pre.toCleanCut.faultQ_of_pos hpos
  And.intro (hsrc c E rho () ⟨hset.pre.base, hq⟩)
    (And.intro (inclusion_ordered_of_scoped E rho hset.pre.base.valid
      (hordered c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hset.sleepPre.sleepPre⟩))
    (And.intro (hnonempty c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hset.sleepPre.sleepPre⟩)
    (And.intro (htransfer c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hset.sleepPre.sleepPre⟩)
    (And.intro (hleases c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hset.sleepPre.sleepPre⟩)
      (hrows c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hset.sleepPre.sleepPre⟩)))))

/-- The Clean assembly supplies gate output and bounded public monotonicity.
P-Ou derives the later reader's enabled gate and result origin from those fields. -/
theorem outage_supplier_later_origins {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hBase : Base₂ p c E rho)
    (hGate : ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x))
    (hMono : ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon)) (s : Slot) :
    ∀ t x, SA.gateTime p.toParams s ≤ t → t ≤ rho.horizon →
      confirmedReader p c E rho x t →
      ∃ q i B, s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
        enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
  intro t x hst hhor hx
  exact inclusion_later_reader_origin E rho hBase.valid hBase.delta hGate hMono hst hhor hx

/-- Clean inclusion services have a regime producer, with no assumed scope callback. -/
theorem outage_supplier_inclusion_inputs {p : Params} {In V : Type} [DecidableEq V]
    [Fintype V] {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {pt : Unit} (h : CleanPrem p c E rho pt ΔF) :
    InclusionReceiverInputs E rho := inclusion_receiver_inputs_of_clean h.set

end AvailableChain.FGSA.Run
end
