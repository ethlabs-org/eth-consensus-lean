module
public import AvailableChainFGSAClaims.Statements.Channels

-- Test fixtures stay private; the Claims guard forbids imports between Tests modules.
set_option linter.privateModule false

@[expose] public section

/-! ROOT-DIGEST W3: explicit small roots for statement fixtures. -/

/-! F0.8a kernel controls: live/expired source, proposer parent, the lo branch,
and a store edit that keeps F. The path control is F0.0b; F2.0 adds its own control. -/

namespace AvailableChain.FGSA.Run.Tests.Channels
open AvailableChain.SimplexFG

private abbrev channelParams : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- The round-zero candidate has a lease until time seven. -/
private def channelSourceStore : State 1 :=
  { initial 1 with
    base := { (initial 1).base with now := 6, obligations := [(.genesis, 1, 7)] }
    fastWrite := [(0, [.genesis])] }

private def channelJointSource : Option (FGBlock (Fin 1)) :=
  jointSource channelParams channelSourceStore

example : sourceCandidates channelParams channelSourceStore = {.genesis} := by decide +kernel
example : channelJointSource = some .genesis ∧
    FGSA.fgSource channelParams channelSourceStore = some .genesis := by decide +kernel
example : jointSource channelParams
    { channelSourceStore with base := { channelSourceStore.base with now := 7 } } = none := by
  decide +kernel

example : proposerHead channelParams channelSourceStore 1 = .genesis := by decide +kernel
example : FGSA.propose channelParams channelSourceStore 1 =
    some (.proposal (.node .genesis 1 ⟨2⟩ (packBody (n := 1) 0 []) [] [] [])) := by decide +kernel

/-- A non-current child with no votes: only the raised band floor admits it. -/
private def channelLateChild : Block := .node .genesis 9 ⟨10⟩ 0
private def channelRaisedLoStore : State 1 :=
  { channelSourceStore with fg := { channelSourceStore.fg with h_max := 3 } }

example : FGSA.eligible channelParams channelSourceStore [] [] channelLateChild = false ∧
    FGSA.eligible channelParams channelRaisedLoStore [] [] channelLateChild = true := by
  decide +kernel

example : ¬ FAdvance channelParams channelSourceStore channelRaisedLoStore := by
  rw [FAdvance_def]
  decide +kernel
example : FAdvance channelParams channelSourceStore
    { channelSourceStore with
      fg := { channelSourceStore.fg with F := .node .genesis 1 ⟨2⟩ 0 [] } } := by
  rw [FAdvance_def]
  decide +kernel

#print axioms channelJointSource
#print axioms channelParams
#print axioms channelSourceStore
#print axioms channelLateChild
#print axioms channelRaisedLoStore

end AvailableChain.FGSA.Run.Tests.Channels
end
