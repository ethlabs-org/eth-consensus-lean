module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface

@[expose] public section

/-! # Goldilocks: AC call labels

The label of a cut of the AC component trace (decomposition §2 D, `AC.LocalRun`), a `Trace` over the
AC state alone whose labelled cuts are AC calls. Each label carries the call (`on_tick`, `proposal`,
`to_fg`, `on_message(m)`, `on_block(B)`, `restart`), the **frame the call was given**, and the
call's emissions (each with its internal read point and duty head). FG cuts and the other nodes'
cuts are stutters (no label).

This module holds only what the Challenge statements reach; the AC trace itself (`ACTrace`), its
contract `ACLocalRun` and `SyncAC` are in `Milestones/Spec/AC/Trace` (docs/decisions.md,
2026-11-04). -/

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type}

/-- The label of an AC call: the call, the frame it was given, and its emissions. -/
structure ACLabel (A : ACInterface P FGP) where
  /-- The call. -/
  call : A.Call
  /-- The frame the call was given. -/
  frame : A.Frm
  /-- The call's emissions. -/
  emits : List A.Em

end Consensus.Goldilocks

end
