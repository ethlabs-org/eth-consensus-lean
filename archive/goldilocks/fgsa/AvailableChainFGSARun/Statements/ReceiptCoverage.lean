module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSARun.Statements.AC -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
K8 inputs (bp00:707–708; bp01:858–930).

`required o t` names an object and its original trigger time. `paths K d`
names a required authentic support path, from genesis to `K`, with cutoff
`d`. The `deadline` field assigns every non-genesis vertex its own proposal
receipt. It does not add a delay for each edge. A required carried HEAD has
its own trigger; receipt of its containing proposal is not that trigger.

The transport index range is `first .. idxBefore rho D`, including the final
read. Slot windows concern only the required objects and their receipt
intervals. The endpoint bound prevents old-label exclusion at the receipt
read; the handler bounds give the current/previous-slot HEAD vote window.
Proposals use the trigger's admission threshold (T7.8).

There is no store premise. `ExecutionValid`, stated separately below,
supplies the checked wire and dependency conditions of base receipt.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure ReceiptCoveragePremises {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop) : Prop where
  within : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut
  slotWindow : ∀ o t, required o t →
    Gen.V2.Duty.Trigger E rho o t ∧ (fgsa p c).wellFormed o = true ∧
    (∀ s a K, (toWire p o).decode = some (.vote s a K) →
      ((V2.D.Run.stateBeforeTime E rho (dl t) x).st.slot p ≤ s + 1) ∧
      ∀ i t', first ≤ i → i < V2.D.Run.idxBefore rho (dl t) → t ≤ t' →
        V2.D.Run.handlesAt E rho i x o t' →
        s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
          (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1)
  compat : ∀ i, first ≤ i → i ≤ V2.D.Run.idxBefore rho D →
    Block.Compatible B (eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F)
  deadline : Monotone dl ∧ D ≤ cut ∧ cut ≤ rho.horizon ∧
    first ≤ V2.D.Run.idxBefore rho D ∧
    (∀ o t, required o t → first ≤ V2.D.Run.idxBefore rho t ∧
      0 ≤ t ∧ t < dl t ∧ dl t ≤ D) ∧
    (∀ K d, paths K d → Block.Preceq B K ∧ d ≤ D ∧
      ∀ b, Block.Preceq b K → b ≠ .genesis →
        ∃ o t s N, N.erase = b ∧ required o t ∧
          (toWire p o).decode = some (.block s N) ∧ dl t ≤ d) ∧
    (∀ o t s N, required o t →
      (toWire p o).decode = some (.block s N) →
      ∃ K d, paths K d ∧ Block.Preceq N.erase K)

/-- DECISION P23-A: receiver-local sleep receipt premises.
The legacy ReceiptCoveragePremises record remains unchanged. -/
structure ReceiptCoverageSleepPremises {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop) : Prop where
  within : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut
  slotWindow : ∀ o t, required o t →
    ∃ a, t ≤ a ∧ 0 ≤ a ∧ a < dl a ∧
    Gen.V2.Duty.ReadyTrigger E rho o t x a (dl a) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o a ∧
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
    first ≤ V2.D.Run.actionCut rho a ∧ dl a ≤ dl t ∧
    (fgsa p c).wellFormed o = true ∧
    (∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
      ((V2.D.Run.stateBeforeTime E rho (dl t) x).st.slot p ≤ s + 1) ∧
      ∀ i t', V2.D.Run.actionCut rho a ≤ i → i < V2.D.Run.idxBefore rho (dl a) → a ≤ t' →
        V2.D.Run.handlesAt E rho i x o t' →
        s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
          (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1)
  compat : ∀ i, first ≤ i → i ≤ V2.D.Run.idxBefore rho D →
    Block.Compatible B (eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F)
  deadline : Monotone dl ∧ D ≤ cut ∧ cut ≤ rho.horizon ∧
    first ≤ V2.D.Run.idxBefore rho D ∧
    (∀ o t, required o t → first ≤ V2.D.Run.idxBefore rho t ∧
      0 ≤ t ∧ t < dl t ∧ dl t ≤ D) ∧
    (∀ K d, paths K d → Block.Preceq B K ∧ d ≤ D ∧
      ∀ b, Block.Preceq b K → b ≠ .genesis →
        ∃ o t s N, N.erase = b ∧ required o t ∧
          (toWire p o).decode = some (.block s N) ∧ dl t ≤ d) ∧
    (∀ o t s N, required o t →
      (toWire p o).decode = some (.block s N) →
      ∃ K d, paths K d ∧ Block.Preceq N.erase K)

/-- DECISION P23-A: receipt coverage with receiver readiness and receipt-scope roots.
No per-required named-scope premise is needed. A global root premise over all
values is false: root is a free field. DC divergence is intentional because
P2 permits root-keyed processing history instead of a new handler call. -/
def ReceiptCoverageSleepStatement : Prop :=
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho
      → x ∈ rho.honest →
    ReceiptCoverageSleepPremises E rho dl cut D first x B required paths →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s N, required o t →
        (toWire p o).decode = some (.block s N) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t)

theorem ReceiptCoverageSleepStatement_def :
    ReceiptCoverageSleepStatement =
      (∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
        (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
        (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
        NamedReceiptRootCollisionFree p c E rho → E.Δ = p.Δ → V2.D.ExecutionValid E rho
          → x ∈ rho.honest →
        ReceiptCoverageSleepPremises E rho dl cut D first x B required paths →
        let st := (V2.D.Run.stateBeforeTime E rho D x).st
        ((Block.Preceq B (eraseFG st.fg.F) ∧
          Block.Preceq B st.base.stableRecord ∧
          (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
          (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
          Block.Preceq B (fgHead p st) ∧
          (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
         (Block.Preceq (eraseFG st.fg.F) B ∧
          (∀ o t s N, required o t →
            (toWire p o).decode = some (.block s N) →
            ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = N.erase) ∧
          (∀ K d, paths K d → ∀ b, Block.Preceq b K →
            ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
        (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
          let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
          (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
          ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
            v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
            GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
            GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t)) := by
  rw [ReceiptCoverageSleepStatement]

end AvailableChain.FGSA.Run
end
