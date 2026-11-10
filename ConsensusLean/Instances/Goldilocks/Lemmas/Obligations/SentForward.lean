module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance

public section

/-! # Goldilocks Obligations: an own forwarding release in the simulating trace

Two facts of the simulating trace of a valid execution, independent of which nodes are honest:

* `cutMap_succ_le_of_time_lt`: the trace cuts of an engine event before the time of a trace cut
  come before that cut;
* `sent_forward_accepted`: a forwarding wrapper a node releases at its sending event is stamped
  with that event's time, and the node accepted the wrapped block at that time, at a cut of the
  event.

The holdings and the observation deadline are their users' (`NetworkTransport` for constant
faults, `Growing/Obligations/Network/Service` for nodes honest at their cuts). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- **The cuts of an earlier event come first**: an engine event `i` strictly before the time of
trace cut `j` has all its trace cuts before `j`. -/
theorem cutMap_succ_le_of_time_lt (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {i j : Nat} {ev : Model.Event V (Wire (Fintype.card V))} (he : rho.events[i]? = some ev)
    (hlt : ev.time < (simTrace S rho hn).time j) : cutMap S rho hn (i + 1) ≤ j := by
  by_contra h
  have hj' : j < cutMap S rho hn (i + 1) := by omega
  have hlen : j < (allCuts S rho hn).length := by
    rw [length_allCuts]
    exact hj'.trans_le (cutMap_mono S rho hn (List.getElem?_eq_some_iff.mp he).1)
  have hl : (simTrace S rho hn).label j ≠ none := by
    rw [simTrace_label, List.getElem?_eq_getElem hlen]
    simp
  obtain ⟨_, q, e, _, hq, hstart, _, _, _, htime, _⟩ := simTrace_cut S rho hn hl
  have hqi : q ≤ i := by
    by_contra hq'
    have := cutMap_mono S rho hn (show i + 1 ≤ q by omega)
    omega
  have hle : e.time ≤ ev.time := by
    rcases hqi.lt_or_eq with hqlt | rfl
    · rcases keyLe_of_lt S rho hv hq he hqlt with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · rw [he] at hq
      cases hq
      rfl
  rw [← htime] at hle
  exact absurd hlt (not_lt.mpr hle)

/-- **An own forwarding release is an own acceptance**: a forwarding wrapper of `B` with stamp `t`
that `y`'s node releases at its sending event `i` at `u` has `t = u`, and `y` accepts `B` at time
`t` at a cut of the event. -/
theorem sent_forward_accepted (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {i : Nat} {u t : Time} {o : Wire (Fintype.card V)}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hi : rho.SendsAt (rho.key y) i u) (ho : o ∈ rho.releasesAt i)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    t = u ∧ ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt y k B ∧ (simTrace S rho hn).time k = t := by
  have hxy := released_forward_signer S rho hn hi ho hdecode
  rw [hxy] at hdecode
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  refine ⟨released_forward_stamp S rho hn hv hi ho hdecode, ?_⟩
  obtain ⟨k, hk, ha, ht⟩ : ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
      (simTrace S rho hn).time k = t := by
    rcases hi with he | ⟨receipt, he⟩
    · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
    · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
  exact ⟨k, hk, hkey ▸ ha, ht⟩

end Consensus.Goldilocks.Obligations

end
