module
public import AvailableChainFGSA.Model.Spec.Objects

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- [spec 243–247, 954–960] The pinned spec digest uses Lean's digest at app zero.
No injectivity assumption on the digest is introduced. -/
def digestSpec (p : Params) (parent : BlockId) (slot : Slot)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) : BlockId :=
  p.digest ⟨parent, slot, 0, rows, raw, support⟩

/-- [spec 249–258, 954–967] The AC payload check keeps order and duplicates. -/
def validPayload {n : Nat} (s : Slot) (raw support : List (HeadWire n)) : Bool :=
  raw.all (fun v => match v.decode? with
    | some (r, _, _) => r + 1 == s
    | none => false) && support.all (fun v => decide (v ∈ raw))

/-- [spec 249–258] Stateless input checks, including supplied digest equality.
A genesis delivery is refused. Ancestor validation remains a store obligation. -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ a) => a.valid
  | some (.block s (.node P r _ root rows raw support)) =>
      s == r && validPayload r raw support &&
      rows.all RowWire.valid && root == digestSpec p P.root r rows raw support
  | _ => false

/-- [spec 721] The parent-slot assertion belongs to admission, not the wire check. -/
def parentSlotValid {n : Nat} (o : Wire n) : Bool :=
  match o.decode with
  | some (.block _ (.node P s _ _ _ _ _)) => decide (P.slot < s)
  | some (.block _ .genesis) => false
  | _ => true

/-- [spec 720] Check the declared proposer against the assigned proposer at admission. -/
def proposerAllowed {n : Nat} (assigned : Slot → Fin n) (o : Wire n) : Bool :=
  match o.payload with
  | .proposal (.node _ s i _ _ _ _) => i == assigned s
  | .proposal .genesis => false
  | _ => true

/-- [spec 720–721] The two pure admission assertions, before any state change. -/
def admissionValid {n : Nat} (assigned : Slot → Fin n) (o : Wire n) : Bool :=
  proposerAllowed assigned o && parentSlotValid o

/-- [spec 249–258, 720] Refusal adapter for Lean's assigned-slot-key abstraction.
A valid signature by a non-assigned proposer is retained in the spec object; its
Lean delivery has absent auth. The complete source identity is kept by `Wire.identities`. -/
def deliveryWire {n : Nat} (assigned : Slot → Fin n) (o : Wire n) : FGSA.Wire n :=
  if proposerAllowed assigned o then o.embed else ⟨.none, o.embed.payload⟩

/-- [spec 249–258, 412–418, 720–721] Wire refusal and admission refusal precede writes.
The continuation stands for the remaining state-dependent handler checks. -/
def checkedDelivery {σ : Type} (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (next : σ → σ) (state : σ) : σ :=
  if wellFormed p o then
    if admissionValid assigned o then next state else state
  else state

-- Generate equations in their owning model module (BUILD B3a).
private theorem digestSpec_eq_1_export :
    type_of% (@digestSpec.eq_1) := @digestSpec.eq_1
private theorem validPayload_eq_1_export :
    type_of% (@validPayload.eq_1) := @validPayload.eq_1
private theorem wellFormed_eq_1_export :
    type_of% (@wellFormed.eq_1) := @wellFormed.eq_1

private theorem spec_parentSlotValid_eq_1_export :
    type_of% (@parentSlotValid.eq_1) := @parentSlotValid.eq_1

private theorem spec_proposerAllowed_eq_1_export :
    type_of% (@proposerAllowed.eq_1) := @proposerAllowed.eq_1

private theorem spec_admissionValid_eq_1_export :
    type_of% (@admissionValid.eq_1) := @admissionValid.eq_1

private theorem spec_deliveryWire_eq_1_export :
    type_of% (@deliveryWire.eq_1) := @deliveryWire.eq_1

private theorem spec_checkedDelivery_eq_1_export :
    type_of% (@checkedDelivery.eq_1) := @checkedDelivery.eq_1

end AvailableChain.FGSA.Spec
end
