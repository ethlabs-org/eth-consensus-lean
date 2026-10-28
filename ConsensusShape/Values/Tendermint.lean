module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Tendermint as a value (D-16, decision T)

A poll shape: no slot proposals (`proposerSel := .fixed ∅`) and no committee
kinds; every key may sign in the poll role (`pollSel := .all`). Proposals come
from the poll proposal duty (height in `pos`, round in `info`) and votes from
the poll message duty, both at every unit tick; the round-robin leader of a
round is computed locally from the own key and the public `Fin n`. Unit ticks,
no responsiveness claim.

Contract (index: a fault count `m : ℕ+`): final safety with no premise,
escaped by global slashability of a third, and local accountability for a
third; liveness from GST under partial synchrony, fewer than a third faulty,
at most `m` faulty (`faultsAtMost`) and full participation from GST, with
latency `latency.eval m` (a `Δ`-coefficient, affine in `m`). There is no
`progress` atom: with at most `m` statically faulty validators, round robin
meets an honest leader within `m + 1` rounds (the faulty leaders may be
consecutive), which is a protocol proof, not a premise; the latency therefore
grows with the fault count, and no bound independent of it is claimed. A
locked value is re-proposed by carrying its original signed header: the engine
writes the payload of every new header. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)
open Consensus.Premise (fromGST faultsBelowThird)

/-- The Tendermint skeleton (the grid is unused). -/
def tendermintSkeleton (n : Nat) : Skeleton n where
  grid := ⟨1, by decide⟩
  proposerSel := .fixed ∅
  pollSel := .all
  Kind := Empty
  decKind := inferInstance
  kinds := []
  kinds_nodup := List.nodup_nil
  kinds_complete := fun k => nomatch k
  phase := fun k => nomatch k
  kindSel := fun k => nomatch k

/-- Liveness with at most `m` faulty: partial synchrony, fewer than a third
faulty, at most `m` faulty, full participation from GST. -/
def tendermintLivePremise (m : ℕ+) : Premise ProgressReq :=
  .conj .sync <| .conj faultsBelowThird <| .conj (.atTime .zero (.faultsAtMost m)) <|
    fromGST .full

/-- The Tendermint contract, with the readers' catch-up and the latency bound
(affine in the fault count) as parameters. -/
def tendermintContract (catchUp : Nat) (latency : Affine) : Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  catchUp := catchUp
  spec
    | .final => some
        { safety := { premise := .truth, escape := some (1 / 3) }
          live := ⟨tendermintLivePremise, fun _ => .gst, fun m => latency.eval m⟩
          accountable := some (1 / 3) }
    | _ => none

theorem tendermintContract_wellFormed (catchUp : Nat) (latency : Affine) :
    (tendermintContract catchUp latency).WellFormed := by
  constructor
  intro c s h
  cases c
  · cases h
  · cases h
  · obtain rfl := Option.some.inj h
    have ha : FracWF (some (1 / 3 : ℚ)) := fun α h => by cases h; norm_num
    refine ⟨trivial, ha, fun m => ?_, ha, (fun _ h => nomatch h), (fun _ h => nomatch h),
      fun _ => trivial, (fun _ h => nomatch h)⟩
    change ℕ+ at m
    norm_num [tendermintLivePremise, faultsBelowThird, fromGST, Premise.WellFormed,
      EnvAtom.WellFormed, TimeExpr.HorizonFree]
    exact m.pos

/-- Non-vacuity of the Tendermint contract for every family (no skeleton
hypothesis: the premises have no `progress` atom). -/
theorem tendermint_realizable {Info : Type} [DecidableEq Info] [Encodable Info]
    (catchUp : Nat) (latency : Affine) (F : ShapeFamily bftCore Info) :
    (tendermintContract catchUp latency).Realizable F := by
  have hwf := tendermintContract_wellFormed catchUp latency
  have hnp : ∀ (Q : Premise ProgressReq), ¬ Q.UsesProgress → Q.UsesProgress →
      ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m := fun _ h h' => absurd h' h
  constructor
  · intro c s h
    cases c
    · cases h
    · cases h
    · obtain rfl := Option.some.inj h
      exact witness_realizable F _ _ (hwf.caps _ _ h).safety (fun h => h.elim) (fun _ => 0) 0 0
        le_rfl (fun _ _ => trivial) (fun _ _ => trivial)
  · intro c s h i
    change ℕ+ at i
    cases c
    · cases h
    · cases h
    · have hw := (hwf.caps _ _ h).live i
      obtain rfl := Option.some.inj h
      have hu : ¬ (tendermintLivePremise i).UsesProgress := by
        simp [tendermintLivePremise, faultsBelowThird, fromGST, Premise.UsesProgress]
      refine live_realizable F _ _ hw (hnp _ hu) _ _ (fun _ => 0)
        (1 + ((latency.eval i : Nat) : Time)) 0 0
        (fun _ _ => ⟨trivial, trivial, trivial, trivial⟩)
        (fun _ _ => Premise.progressAll_of_not_usesProgress hu) (fun _ => ?_) le_rfl ?_
      · simp [TimeExpr.eval, EnvPoint.extremal]
      · simp
  · intro c s P h hP
    cases c
    · cases h
    · cases h
    · obtain rfl := Option.some.inj h
      cases hP
  · intro c s R h hR
    cases c
    · cases h
    · cases h
    · obtain rfl := Option.some.inj h
      cases hR

end Consensus.Shape

end
