module
public import AvailableChainFGSAProofs.Proofs.Healing.PostReset -- shake: keep (J9 fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.12–H.18 and H.22; plan J9; B1/B13/B17/B18/B31/B32.
Each fixture is a conditional package. The adapter fixtures apply the
actual J3/J4 producers under H0 and consume their conclusions. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostReset
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- conditional package: A supplies reset delivery from the actual J1 producer.
example [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (xing : RXing p c E rho) (cap : RCap p c E rho)
    (source : TSrc p c E rho) (origin : RQCOrigin p c E rho)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (h0 : H0 p c E rho w) (hhor : SA.releaseTime p.toParams w.sStar ≤ rho.horizon) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho (fun nd =>
      ∃ C ∈ nd.st.fg.TF, eraseFG C = w.CStar)
      (SA.releaseTime p.toParams w.sStar) x := by
  exact (healing_healTContract_reset p c E rho hrec mono xing cap source origin writes
    rowCoverage h0r).delReset h0 hhor

-- conditional package, anti-vacuity: RKeep under H0 supplies the general kept path.
example (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (inv : ∀ i, PostResetInv p c E rho w i) (h0 : H0 p c E rho w)
    {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))} {C B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (htick : ∃ t, rho.events[i]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (hreset : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar)
    (hhigh : ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K'))
    (path : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hBC : Block.Compatible (eraseFG B) w.CStar)
    (hBK : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K)) : Kept p c E rho i x X B := by
  have h := healing_rKeep_of_reset (hroots := hroots) p c E rho xing origin inv h0 i x X C
    hx hX htick hC he cover hreset hhigh
  exact h.2.2.2.2.2 B path hBC hBK

-- conditional package, anti-vacuity: RFProv under H0 supplies both F and high-J arms.
example (hv : V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
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
    (xing : RXing p c E rho) {w : HealingWitness} (h0 : H0 p c E rho w)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hJ : high p w (storeAt p c E rho i x).fg.J) :
    (Block.Preceq (F_at p c E rho i x) w.CStar ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
        SA.gateTime p.toParams s + P p ≤ (storeAt p c E rho i x).base.now ∧
        Block.Preceq (F_at p c E rho i x) (eraseFG K)) ∧
    (∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
      SA.gateTime p.toParams s ≤ (storeAt p c E rho i x).base.now ∧
      Block.Preceq (J_at p c E rho i x) (eraseFG K)) := by
  have h := healing_rFProv_of_reset (hroots := hroots) p c E rho hv origin heldRows cap
      hhead xing w
    h0 i x hx hi
  exact ⟨h.1, h.2 hJ⟩

-- conditional package: C preserves each full T-stream field.
example {w : HealingWitness} {ΔF : Time} (tHigh : THigh p c E rho w)
    (tCarrier : TCarrier p c E rho w) (rows : TRows p c E rho ΔF) :
    THigh p c E rho w ∧ TCarrier p c E rho w ∧ TRows p c E rho ΔF := by
  have h := healing_healT_of p c E rho tHigh tCarrier rows
  exact ⟨h.h1, h.h2, h.rows⟩

-- conditional package: C preserves every AC-output field and its horizon guards.
example {w : HealingWitness} (h2A : H2A p c E rho w) (h2Prime : H2Prime p c E rho w)
    (h3 : H3 p c E rho w) (h4 : H4 p c E rho w)
    (h5 : H5RawTransfer p c E rho w) (h6 : H6GateService p c E rho w) :
    H2A p c E rho w ∧ H2Prime p c E rho w ∧ H3 p c E rho w ∧
      H4 p c E rho w ∧ H5RawTransfer p c E rho w ∧ H6GateService p c E rho w := by
  have h := healing_healAC_of p c E rho h2A h2Prime h3 h4 h5 h6
  exact ⟨h.h2A, h.h2', h.h3, h.h4, h.h5, h.h6⟩

-- conditional package: D consumes C's packages and the named H.18 source prefix.
example {w : HealingWitness} {ΔF : Time} (healed : Healed p c E rho (tstar p w))
    (start : PostResetStart p c E rho w) (sourcePrefix : Block.Preceq w.CStar w.QStar)
    (tHigh : THigh p c E rho w) (tCarrier : TCarrier p c E rho w)
    (rows : TRows p c E rho ΔF) (h2A : H2A p c E rho w) (h2Prime : H2Prime p c E rho w)
    (h3 : H3 p c E rho w) (h4 : H4 p c E rho w)
    (h5 : H5RawTransfer p c E rho w) (h6 : H6GateService p c E rho w) :
    HealingInput p c E rho w ΔF :=
  healing_healingInput_of p c E rho healed start sourcePrefix
    (healing_healT_of p c E rho tHigh tCarrier rows)
    (healing_healAC_of p c E rho h2A h2Prime h3 h4 h5 h6)

end AvailableChain.FGSA.Run.Tests.HealingPostReset
end
