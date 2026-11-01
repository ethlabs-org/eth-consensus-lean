module
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain.V2

/-- The authentication of a wire object (design §2 E1). There are no
validator keys and no global committee size.

* `seat ℓ i`: seat `i` of the committee of label `ℓ`, which has `seats ℓ`
  seats. The run assigns seats to validators (`Run.seatOf`), which honest
  code cannot see. A proposal duty is a label with one seat.
* `none`: an unsigned object. Anyone can create it. -/
inductive Auth (L : Type) (seats : L → Nat) where
  | seat (ℓ : L) (i : Fin (seats ℓ))
  | none
  deriving DecidableEq, Repr

/-- A wire object: an authentication and a protocol payload. Honest code
chooses only the payload; the engine attaches the authentication. A payload
can carry other signed objects (a nested inductive through `Signed`). -/
structure Signed (L : Type) (seats : L → Nat) (Payload : Type) where
  auth : Auth L seats
  payload : Payload
  deriving DecidableEq, Repr

end AvailableChain.V2

end
