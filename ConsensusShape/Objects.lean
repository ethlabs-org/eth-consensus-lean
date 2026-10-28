module
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Encodable.Basic
public import ConsensusModel.Protocol
@[expose] public section

/-! Headers and chains for the shape layer. Wire objects are those of ConsensusModel. -/
namespace Consensus.Shape

/-- A slot index. -/
abbrev Slot := Nat

/-- A block header. It names its parent by digest. `input` is the application
input of the proposal; `aux` is protocol data (for example an encoding of the
protocol's own block fields). The digest of a header is `hash h`, for the run's
hash function (`Run.hash`), which is arbitrary: it may have collisions.
Genesis is not a header; its digest is `0`. -/
structure Header where
  parent : Nat
  slot : Slot
  input : Nat
  aux : Nat
  deriving DecidableEq, Repr

def Header.equiv : Header ≃ Nat × Nat × Nat × Nat where
  toFun h := (h.parent, h.slot, h.input, h.aux)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable Header := Encodable.ofEquiv _ Header.equiv

/-- A chain: headers oldest first, genesis implicit before the first. An output
is a chain. Chains are compared structurally, never through digests. -/
abbrev Chain := List Header

namespace Chain

/-- `c ⪯ d`: `c` is a prefix of `d`. -/
def Preceq (c d : Chain) : Prop := c <+: d

/-- `c ≺ d`: a strict prefix. -/
def Prec (c d : Chain) : Prop := c <+: d ∧ c ≠ d

/-- Each header names the previous one (genesis, digest `0`, for the first). -/
def LinkedFrom (hash : Header → Nat) : Nat → Chain → Prop
  | _, [] => True
  | prev, h :: t => h.parent = prev ∧ LinkedFrom hash (hash h) t

/-- The chain is linked by digests under `hash`. -/
def Linked (hash : Header → Nat) (c : Chain) : Prop := LinkedFrom hash 0 c

/-- Slots strictly increase along the chain, starting above 0 (genesis's
slot). -/
def SlotsFrom : Slot → Chain → Prop
  | _, [] => True
  | prev, h :: t => prev < h.slot ∧ SlotsFrom h.slot t

/-- The prefix of `c` up to and including `h`. -/
def upTo (h : Header) (c : Chain) : Chain := c.take (c.idxOf h + 1)

theorem preceq_refl (c : Chain) : Preceq c c := List.prefix_refl c

theorem nil_preceq (c : Chain) : Preceq [] c := List.nil_prefix

end Chain

end Consensus.Shape
end
