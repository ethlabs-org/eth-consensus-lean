module
public import AvailableChainPCSAProofs.Proofs.Shared.HeldReceipt

public section

/-! Strict stamp and freeze boundaries (pcsa34-r4.3 §5.2.3).
FG-SA Shared/GateReceipt supplies the strict-stamp proof pattern.
Its FG-SA run and frame facts cannot be instantiated on a PC-SA run. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- A stamp no later than receipt is strictly before the receipt deadline. -/
theorem pcsa_receipt_stamp_strict (stamp receipt deadline : Time)
    (hs : stamp ≤ receipt) (hr : receipt < deadline) : stamp < deadline :=
  lt_of_le_of_lt hs hr

/-- Early-duty receipt deadlines precede the gate deadline. -/
theorem pcsa_freeze_lt_gate (p : Params) (s : Slot) :
    SA.freezeTime p.toParams s < SA.gateTime p.toParams s := by
  have hd := p.deltaPos
  change 4 * p.Δ * (s : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith

/-- A pre-freeze pool quorum gives a PC after the freeze, given store assembly.
`hCollect` is the missing store fact: resolve the root, select distinct acks,
assemble and install the PC. `hKeep` is its run lift through the freeze tick.
The model collects on receipt; the freeze tick records the held PCs. -/
theorem pcsa_pc_after_freeze_of_pool (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (r : BlockId)
    (Q : Finset (Fin p.n)) (hQ : pcQuorum p.n ≤ Q.card) (y : V)
    (hp : ∀ i ∈ Q, (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.ackPool)
    (hCollect :
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target.root = r)
    (hKeep : (collectPCs
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
      (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) :
    ∃ C ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
      C.slot = s ∧ C.target.root = r := by
  obtain ⟨C, hC, hs, hr⟩ := hCollect hp hQ
  exact ⟨C, hKeep hC, hs, hr⟩

end AvailableChain.PCSA.Run
end
