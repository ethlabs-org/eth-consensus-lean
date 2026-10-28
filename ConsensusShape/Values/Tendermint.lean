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

Contract (one index): final safety under fewer than a third faulty, local
accountability for a third; liveness from GST under partial synchrony, fewer
than a third faulty and full participation from GST, latency `latency·Δ`.
There is no `progress` atom: under static corruption with `f < n/3`, round
robin meets an honest leader within `f + 1` rounds, which is a protocol proof,
not a premise. -/

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

/-- Liveness: partial synchrony, fewer than a third faulty, full
participation from GST. -/
def tendermintLivePremise : Premise ProgressReq :=
  .conj .sync <| .conj faultsBelowThird <| fromGST .full

/-- The Tendermint contract, with the readers' catch-up and the latency as
parameters. -/
def tendermintContract (catchUp latency : Nat) : Contract bftCore ProgressReq where
  Idx := Unit
  idx_nonempty := ⟨()⟩
  catchUp := catchUp
  spec
    | .final => some
        { safety := { premise := faultsBelowThird }
          live := ⟨fun _ => tendermintLivePremise, fun _ => .gst, fun _ => latency⟩
          accountable := some (1 / 3) }
    | _ => none

theorem tendermintContract_wellFormed (catchUp latency : Nat) :
    (tendermintContract catchUp latency).WellFormed := by
  constructor
  intro c s h
  cases c
  · cases h
  · cases h
  · obtain rfl := Option.some.inj h
    refine ⟨?_, (fun _ h => nomatch h), fun _ => ?_, ?_, (fun _ h => nomatch h),
      (fun _ h => nomatch h)⟩
    · norm_num [faultsBelowThird, Premise.WellFormed, EnvAtom.WellFormed]
    · norm_num [tendermintLivePremise, faultsBelowThird, fromGST, Premise.WellFormed,
        EnvAtom.WellFormed]
    · intro α h; cases h; norm_num

/-- Non-vacuity of the Tendermint contract for every family (no skeleton
hypothesis: the premises have no `progress` atom). -/
theorem tendermint_realizable {Info : Type} [DecidableEq Info] [Encodable Info]
    (catchUp latency : Nat) (F : ShapeFamily bftCore Info) :
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
      have hu : ¬ (faultsBelowThird : Premise ProgressReq).UsesProgress := by
        simp [faultsBelowThird, Premise.UsesProgress]
      exact witness_realizable F _ _ (hwf.caps _ _ h).safety (hnp _ hu) (fun _ => 0) 0 0 le_rfl
        (fun _ _ => trivial) (fun _ _ => Premise.progressAll_of_not_usesProgress hu)
  · intro c s h i
    cases c
    · cases h
    · cases h
    · have hw := (hwf.caps _ _ h).live i
      obtain rfl := Option.some.inj h
      have hu : ¬ tendermintLivePremise.UsesProgress := by
        simp [tendermintLivePremise, faultsBelowThird, fromGST, Premise.UsesProgress]
      refine live_realizable F _ _ hw (hnp _ hu) _ _ (fun _ => 0)
        (1 + ((latency : Nat) : Time)) 0 0 (fun _ _ => ⟨trivial, trivial, trivial⟩)
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
