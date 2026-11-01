module
public import AvailableChainEngineV2.Laws.Duty.Isolation
public import AvailableChainPCSARun.Model.Protocol

@[expose] public section

/-! The label families and the E5 isolation value of PC-SA on engine v2 (FG-SA
`AvailableChainFGSARun/Model/Families.lean` with the ack label). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In)

/-- [PC-SA M1; FRAMEWORK E2, E5; 2a Task 3 Step 5; DC N9] The PC-SA label
families (pcsa34-v2-delta (1)): the AP labels are the HEAD, the ack and the
proposal labels; the fresh family is the HEAD and the ack labels (one
committee of `n` seats per slot); the linked family is exactly the fixed FG
label. A proposal label has one seat, so it is not fresh (`CStar` needs
`seats ℓ = |V|`); it is `SingleSeat`. One definition for every FG mode
(`pcsaWith m p c`): the modes have the same labels and seats. -/
def pcsaFamilies {m : FGMode} : V2.D.LabelFamilies (pcsaWith m p c) where
  ap
    | .base (.head _) => True
    | .base .fg => False
    | .base (.ack _) => True
    | .prop _ => True
  fresh
    | .base (.head _) => True
    | .base (.ack _) => True
    | _ => False
  linked
    | .base .fg => True
    | _ => False

/-- [PC-SA M1; FRAMEWORK E5 (:294–319); plan T7.2] The isolation value. The
base is the store (`Node.st`): F and its basis are in the base (E5 restore
law), and Λ is not. `clock`, `process` and `recordOwn` act on the base
through the store functions; the AP payloads (`actS`, including the ack) and
the hooks read only the store, so `hooks_base` holds by `rfl` for every
object. `separation`: the AP labels and the designated fresh family are not
self-visible; the FG label, which is `Linked`, may be self-visible. -/
def pcsaIso : V2.D.Isolation (pcsa p c) (pcsaFamilies p c) where
  Base := State p.n
  base := Node.st
  clockB := PCSA.clock p
  clock_base _ _ := rfl
  processB st o := PCSA.process p st (toWire p o)
  process_base _ _ := rfl
  recordOwn_base _ _ := rfl
  actB := actS p c
  act_base st d x h := by
    cases d with
    | headAction s => rfl
    | fgAction r => exact h.elim
    | propAction s => rfl
    | ackAction s => rfl
  gossipB _ _ := []
  gossip_base _ _ := rfl
  depsB := depsS p
  processedB := processedS p
  excludesB := excludesS p
  handlesB := handlesS p
  hooks_base _ _ _ := ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation ℓ h := by
    rcases ℓ with (_ | _ | _) | _
    · rfl
    · rcases h with h | h <;> exact h.elim
    · rfl
    · rfl

end AvailableChain.PCSA.Run

end
