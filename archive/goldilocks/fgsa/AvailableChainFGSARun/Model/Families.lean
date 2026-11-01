module
public import AvailableChainEngineV2.Laws.Duty.Isolation
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

/-! The label families and the E5 isolation value of FG-SA on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2). -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In)

/-- [FRAMEWORK E2, E5; 2a Task 3 Step 5; DC N9] The FG-SA label families (the 2a
reference assignment): the AP labels are the HEAD and the proposal labels; the
designated fresh family is the HEAD labels; the linked family is exactly the fixed FG
label. A proposal label has one seat, so it is not fresh (`CStar` needs
`seats ℓ = |V|`); it is `SingleSeat`. -/
def fgsaFamilies : V2.D.LabelFamilies (fgsa p c) where
  ap
    | .base (.head _) => True
    | .base .fg => False
    | .prop _ => True
  fresh
    | .base (.head _) => True
    | _ => False
  linked
    | .base .fg => True
    | _ => False

/-- [FRAMEWORK E5 (:294–319); plan T7.2] The isolation value. The base is the
store (`Node.st`): F and its basis are in the base (E5 restore law), and Λ is
not. `clock`, `process` and `recordOwn` act on the base through the store
functions; the AP payloads (`actS`) and the hooks (`depsS`, `processedS`,
`excludesS`, `handlesS`) read only the store, so `hooks_base` holds by `rfl`
for every object (the isolation check: the hooks on AP labels and unsigned
objects read neither Λ nor pending state; the proposal hooks read F and the
store, which E5 allows).

`separation` (2a field; FRAMEWORK dated E5 note :302–306, 7e40fba): the
restriction applies to the AP labels and to the designated fresh family, not
to every `CStar` family. So the FG labels, which are `Linked`, may be
self-visible (Opus m16, closed). -/
def fgsaIso : V2.D.Isolation (fgsa p c) (fgsaFamilies p c) where
  Base := State p.n
  base := Node.st
  clockB := FGSA.clock p
  clock_base _ _ := rfl
  processB st o := FGSA.process p st (toWire p o)
  process_base _ _ := rfl
  recordOwn_base _ _ := rfl
  actB := actS p c
  act_base st d x h := by
    cases d with
    | headAction s => rfl
    | fgAction r => exact h.elim
    | propAction s => rfl
  gossipB _ _ := []
  gossip_base _ _ := rfl
  depsB := depsS p
  processedB := processedS p
  excludesB := excludesS p
  handlesB := handlesS p
  hooks_base _ _ _ := ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation ℓ h := by
    rcases ℓ with (_ | _) | _
    · rfl
    · rcases h with h | h <;> exact h.elim
    · rfl

end AvailableChain.FGSA.Run

end
