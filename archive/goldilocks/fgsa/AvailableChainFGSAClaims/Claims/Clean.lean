module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSAClaims.Statements.ComposeNext

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure (CompatOn MonoOn)

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- bp.cleanHistory.v1, P3 §4.7 and 00:767–775. The clauses use public
event reads and BelowLabel; no F2 invariant occurs in this statement.
Nonempty and continuation refer to actual ticks, including at the cut. -/
def CleanHistoryAt (b₀ : Time) : Prop :=
  (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
    confirmedReader p c E rho x (SA.gateTime p.toParams r) →
    confirmedReader p c E rho y (SA.gateTime p.toParams s) →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho b₀ → x ∈ rho.honest →
    enabledGateAt p c E rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho x s = some (some B) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, V2.D.restartFree rho v j i ∧
        enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → enabledGateAt p c E rho j v s →
      V2.D.restartFree rho v j i →
      FGSA.activeCompatible st C = true →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, V2.D.restartFree rho v j i ∧ enabledGateAt p c E rho j v s
        ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho b₀ → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho b₀ → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho b₀ → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)

/-- bp.cleanPrefixTruncation.v1 gate facts (P3:3331; S3a FS6; 03 §6 :439–487). Consumer:
F3 (03 §6 origin argument). Producer: F2.7. -/
def CleanGateAt (b₀ : Time) : Prop :=
  ∀ l x, SA.gateTime p.toParams l ≤ b₀ → x ∈ rho.honest →
    confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams l)) (SA.gateTime p.toParams l) →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, enabledGateAt p c E rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B

/-- bp.cleanPrefixTruncation.v1 (00:795–802). All event states at the
inclusive cut and all public reads in [0,b₀] have the Clean properties. -/
def CleanTruncAt (b₀ : Time) : Prop :=
  ScopedCompat (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ b₀) ∧
    ScopedMono (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ b₀)) ∧
  CleanHistoryAt p c E rho b₀ ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) ∧
  CleanGateAt p c E rho b₀

/-- FS20 named conclusion of bp.cleanSafety.v1, using the Gen property kernel. -/
def CleanSafetyAt : Prop :=
  ScopedCompat (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ rho.events.length) ∧
  ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ rho.events.length) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
      (fun _ => True) ∧
    ScopedMono (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True))

/-- Blueprint cut form. Assembly of its two lanes is deferred.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanCutClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
    CleanCutPrem p c E rho pt ΔF → CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀

/-- F2 zero lane. There is no channel or quorum premise.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanCutZeroClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time},
    CleanCutPrem p c E rho ⟨0⟩ ΔF → CleanHistoryAt p c E rho 0 ∧ CleanTruncAt p c E rho 0

def CleanHistoryClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
    CleanPrefixPrem p c E rho pt ΔF → CleanHistoryAt p c E rho pt.b₀

def CleanPrefixTruncationClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
    CleanPrefixPrem p c E rho pt ΔF → CleanTruncAt p c E rho pt.b₀

def CleanSafetyClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
    CleanPrem p c E rho pt ΔF → CleanSafetyAt p c E rho

/-- P3 §4.7, L39: the positive F2 lane has both F1 channels as premises.
This lane Prop is not a field of FGSASafetyClaims.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def CleanCutPosClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
    CleanCutPrem p c E rho pt ΔF → 0 < pt.b₀ →
    FGFoundationNext p c E rho → SrcFrameAboveStmt p c E rho →
    CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀

end AvailableChain.FGSA.Run
end
