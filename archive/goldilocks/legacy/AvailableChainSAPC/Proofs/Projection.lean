module
public import AvailableChainSAPC.Proofs.Basic

@[expose] public section
namespace AvailableChain.SAPC

/-- The new signature field has no effect on the internal base key. -/
theorem baseHead_ack_irrelevant {n : Nat} (auth : Auth Slot n) (b : Block)
    (ack₁ ack₂ : Option (Slot × Block)) :
    baseHead ⟨auth, ⟨b, ack₁⟩⟩ = baseHead ⟨auth, ⟨b, ack₂⟩⟩ := rfl

theorem gateWithPC_none (p : Params) {n : Nat} (st : GridCO.State n) (r : Slot) :
    gateWithPC p st r none = SA.gate p st r := rfl

/-- Use the existing SA gate and its proofs exactly in the disabled mode. -/
theorem gate_base_of_capBroken (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : capBroken p st = true) : (gate p st r).base = SA.gate p st.base r := by
  simp [gate, h, gateWithPC]

theorem gate_base_of_noPC (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : st.bestPC = none) : (gate p st r).base = SA.gate p st.base r := by
  simp [gate, h, gateWithPC]

theorem choice_of_capBroken (p : Params) {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (GridCO.Wire n)) (r : Slot)
    (c : Option (PC n)) (h : capBroken p st = true) :
    choice p st tree raw support r c = GridCO.forkChoice st.base tree raw support r := by
  simp [choice, h]

/-- The disabled HEAD uses SA's original domain as well as its root. -/
theorem headTarget_of_capBroken (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : capBroken p st = true) :
    some (GridCO.Msg.head (headTarget p st r)) = SA.act p st.base r := by
  simp [headTarget, h, choice, SA.act, GridCO.act]
  split <;> rfl

theorem installPC_base {n : Nat} (st : State n) (c : PC n) :
    (installPC st c).base = st.base := rfl

theorem installPC_tie {n : Nat} (st : State n) (old c : PC n)
    (h : st.bestPC = some old) (hslot : c.slot ≤ old.slot) :
    (installPC st c).bestPC = st.bestPC := by
  simp [installPC, preferPC, h, Nat.not_lt.mpr hslot]

/-- A later live receipt cannot change the HEAD's selected PC. It can
still change the live cap test and the gate, as required by the protocol. -/
theorem selectedPC_installPC (p : Params) {n : Nat} (st : State n)
    (c : PC n) (r : Slot) : selectedPC p (installPC st c) r = selectedPC p st r := by
  have hpath (b : Block) : pathKnown (installPC st c) b = pathKnown st b := by
    induction b with
    | genesis => rfl
    | node parent s r_s root ih =>
        rw [pathKnown, pathKnown, ih]
        rfl
  have hvalid (cert : PC n) : pcValid p (installPC st c) cert = pcValid p st cert := by
    simp only [pcValid, pcPaths, hpath]
    rfl
  simp only [selectedPC, hvalid]
  rfl

theorem ackFor_extends {n : Nat} (st : State n) (r s : Slot) (h b : Block)
    (ha : ackFor st r h = some (s, b)) : Block.Preceq b h := by
  unfold ackFor at ha
  split at ha
  · simp at ha
  · split at ha
    next x b' he =>
      split at ha
      · simp only [Option.some.injEq, Prod.mk.injEq] at ha
        rcases ha with ⟨_, rfl⟩
        assumption
      · simp at ha
    next => simp at ha

theorem saveTimely_latched (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : (savedTimely st r).isSome = true) : saveTimely p st r = st := by
  simp [saveTimely, h]

/-- A mandatory root cannot move below or off the live lease root. -/
theorem mandatoryRoot_covers (r anchor : Block) :
    Block.Preceq r (mandatoryRoot r anchor) := by
  unfold mandatoryRoot
  split
  · assumption
  · exact GridCO.block_preceq_self _

end AvailableChain.SAPC
end
