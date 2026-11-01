module
public import AvailableChainFGCompose.Statements.FrontierSearch

@[expose] public section

/-! P0d5b: maturity, age service and the capped receipt.
Fieldwise translations of PromotionSourceAt (PromotionSource:16) and FrontierHG2aResult
(FrontierSearchHG2a:25). The leaf propositions below are the supplier boundary of plan
§5 P0d5b. Each one is an effect of an existing protocol producer. None of them states
height advance, age service or the capped receipt result. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S)

/-- Frozen `PromotionSourceAt` (PromotionSource:16): the nine fields.
The same fixed rows, saved entry and parent path at the proposal read. No phase field. -/
structure PromotionSourceAt (ΔF : Time) (r height : Nat) (U : FGBlock (Fin n))
    (s : Slot) (X : FGBlock (Fin n)) : Prop where
  entry : EntryAt O.height U height
  parentPath : FGBlock.Preceq U X.parent
  proposal : HonestProposal E rho I s (R.erase X)
  slot : X.slot = s
  sync : E.t_GST ≤ T.action r
  carrier : carrierTimeW T ΔF r ≤ T.proposal s
  age : T.proposal U.slot + 2 * FGCompose.P T ≤ T.proposal s
  horizon : T.proposal s ≤ rho.horizon
  rows : ∀ x ∈ rho.honest, ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
    NamesEntry D.heightPair .progress a height U

/-- Frozen `FrontierHG2aResult` (FrontierSearchHG2a:25): a first rise or a strict
honest high receipt, both by the exact HG.2a_F terminal deadline. -/
def FrontierHG2aResult (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin n)) : Prop :=
  let D := max (T.action r + Γ T G - T.delta + epsF T ΔF)
    (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta)
  FrontierRiseBy R E rho i m D ∨
    ∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      m + 1 ≤ (O.height X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) D y

theorem FrontierHG2aResult_def (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin n)) :
    FrontierHG2aResult R E rho O T I G ΔF i m r U ↔
  let D := max (T.action r + Γ T G - T.delta + epsF T ΔF)
    (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta)
  FrontierRiseBy R E rho i m D ∨
    ∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      m + 1 ≤ (O.height X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) D y := Iff.rfl

/-- Construction leaf: an honest slot whose proposer joined before the previous slot
start has an actual proposal with that slot. -/
def PromotionSlotProposal : Prop :=
  ∀ s, Gen.V2.Duty.HonestSlot rho I s → E.t_GST + 4 * T.delta ≤ T.proposal s →
    T.proposal s ≤ rho.horizon → ∃ X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s

theorem PromotionSlotProposal_def : PromotionSlotProposal R E rho T I ↔
  ∀ s, Gen.V2.Duty.HonestSlot rho I s → E.t_GST + 4 * T.delta ≤ T.proposal s →
    T.proposal s ≤ rho.horizon → ∃ X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s :=
  Iff.rfl

variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))

/-- Proposal leaf: the actual carrier with its full row list, and the post-clock parent
read whose stored R6W fold gives the parent's height entry and row validity. -/
def PromotionProposalRead : Prop :=
  ∀ s X, HonestProposal E rho I s (R.erase X) → X.slot = s →
    (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows) s
      (R.erase X) rows ∧ X.rows = rows.filterMap S.decode) ∧
    ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (O.height X.parent).h ∧
      (fold nd s X.parent).T_h = (O.height X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b

theorem PromotionProposalRead_def :
    PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold ↔
  ∀ s X, HonestProposal E rho I s (R.erase X) → X.slot = s →
    (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows) s
      (R.erase X) rows ∧ X.rows = rows.filterMap S.decode) ∧
    ∃ nd, proposalStateAt E rho I s = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent ∧
      (fold nd s X.parent).h = (O.height X.parent).h ∧
      (fold nd s X.parent).T_h = (O.height X.parent).T_h ∧
      parentHeight nd s X.parent = ((fold nd s X.parent).h, (fold nd s X.parent).T_h.root) ∧
      ∀ a, validFor nd s X.parent a =
        match S.decode a with | none => false | some b => Window.r6w (fold nd s X.parent) b :=
  Iff.rfl

/-- Stored R6W leaf: a stored parent at the entry height orders each named row
of its own chain after the entry. -/
def PromotionRowOrder : Prop :=
  ∀ s X height U, HonestProposal E rho I s (R.erase X) → X.slot = s →
    (O.height X.parent).h = height → FGBlock.Preceq U X.parent →
    ∀ i W, FGBlock.Preceq W X.parent → (∃ row ∈ W.rows, RowNames .progress row i height U) →
      FGBlock.Preceq U W.parent

theorem PromotionRowOrder_def : PromotionRowOrder R E rho O I ↔
  ∀ s X height U, HonestProposal E rho I s (R.erase X) → X.slot = s →
    (O.height X.parent).h = height → FGBlock.Preceq U X.parent →
    ∀ i W, FGBlock.Preceq W X.parent → (∃ row ∈ W.rows, RowNames .progress row i height U) →
      FGBlock.Preceq U W.parent := Iff.rfl

/-- Row leaf: an honest row decodes, and it is signed by its holder's seat. -/
def PromotionRowSigner : Prop :=
  (∀ j x r a, HonestRowAt S E rho T j x r a → ∃ b, S.decode a = some b) ∧
  ∀ i j r a, HonestRowAt S E rho T j (safetyHolder S rho i) r a → D.signer a = some i

theorem PromotionRowSigner_def : PromotionRowSigner S E rho T D ↔
  (∀ j x r a, HonestRowAt S E rho T j x r a → ∃ b, S.decode a = some b) ∧
  ∀ i j r a, HonestRowAt S E rho T j (safetyHolder S rho i) r a → D.signer a = some i :=
  Iff.rfl

/-- Source transfer leaf: inside the old phase, each selected opening source is on the
parent path of a later honest proposal read at or after the action. -/
def PromotionSourceParent (Jst : Time) : Prop :=
  ∀ u m J contested r s X x K, Jst ≤ u →
    PhaseInterval R E rho O u (T.proposal s) m J contested →
    u ≤ T.vote (r * T.roundSlots) → T.action r ≤ T.proposal s → r * T.roundSlots + 2 ≤ s →
    HonestProposal E rho I s (R.erase X) → x ∈ rho.honest →
    actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent

theorem PromotionSourceParent_def (Jst : Time) :
    PromotionSourceParent R E rho O T I Jst ↔
  ∀ u m J contested r s X x K, Jst ≤ u →
    PhaseInterval R E rho O u (T.proposal s) m J contested →
    u ≤ T.vote (r * T.roundSlots) → T.action r ≤ T.proposal s → r * T.roundSlots + 2 ≤ s →
    HonestProposal E rho I s (R.erase X) → x ∈ rho.honest →
    actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq K X.parent := Iff.rfl

/-- Receipt leaf, phase form: one honest node processes a selected proposal strictly
before its Δ deadline while the old phase holds through that deadline. -/
def PromotionPhaseReceipt (Jst : Time) : Prop :=
  ∀ u m J contested s X, Jst ≤ u → HonestProposal E rho I s (R.erase X) →
    u ≤ T.proposal s → PhaseInterval R E rho O u (T.proposal s + T.delta) m J contested →
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y

theorem PromotionPhaseReceipt_def (Jst : Time) :
    PromotionPhaseReceipt R E rho O T I Jst ↔
  ∀ u m J contested s X, Jst ≤ u → HonestProposal E rho I s (R.erase X) →
    u ≤ T.proposal s → PhaseInterval R E rho O u (T.proposal s + T.delta) m J contested →
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y := Iff.rfl

/-- Receipt leaf, cap form: a strict honest frontier cap through the Δ deadline lets one
honest node process a proposal that extends a held block of the capped height. -/
def PromotionCapReceipt : Prop :=
  ∀ m s Qfg X, HonestProposal E rho I s (R.erase X) → E.t_GST ≤ T.proposal s →
    FGBlock.Preceq Qfg X.parent →
    (∀ i x, i ≤ V2.D.Run.idxBefore rho (T.proposal s + T.delta) → x ∈ rho.honest →
      (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max ≤ m) →
    (O.height Qfg).h = m → T.proposal s + T.delta ≤ rho.horizon →
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y

theorem PromotionCapReceipt_def : PromotionCapReceipt R E rho O T I ↔
  ∀ m s Qfg X, HonestProposal E rho I s (R.erase X) → E.t_GST ≤ T.proposal s →
    FGBlock.Preceq Qfg X.parent →
    (∀ i x, i ≤ V2.D.Run.idxBefore rho (T.proposal s + T.delta) → x ∈ rho.honest →
      (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max ≤ m) →
    (O.height Qfg).h = m → T.proposal s + T.delta ≤ rho.horizon →
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y := Iff.rfl

end AvailableChain.FGCompose
end
