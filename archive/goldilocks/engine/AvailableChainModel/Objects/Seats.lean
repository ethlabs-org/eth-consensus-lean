module
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain

/-- The authentication of a wire object. There are no validator keys.

* `seat ℓ i`: seat `i` of the committee of label `ℓ`. Every label has a
  committee of all `n` seats. The run assigns seats to validators by a fresh
  bijection per label, which honest code cannot see, so seats of different
  labels are unlinkable.
* `proposer s`: the proposer of slot `s`, a slot-scoped key.
* `none`: an unsigned object. Anyone can create it. -/
inductive Auth (L : Type) (n : Nat) where
  | seat (ℓ : L) (i : Fin n)
  | proposer (s : Slot)
  | none
  deriving DecidableEq, Repr

/-- A wire object: an authentication and a protocol payload. Honest code
chooses only the payload; the engine attaches the authentication. A payload
can carry other signed objects (a nested inductive through `Signed`). -/
structure Signed (L : Type) (n : Nat) (Payload : Type) where
  auth : Auth L n
  payload : Payload
  deriving DecidableEq, Repr

end AvailableChain
end
