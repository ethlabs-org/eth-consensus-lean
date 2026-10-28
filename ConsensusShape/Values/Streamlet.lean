module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Streamlet as a value (D-16)

Final-only (`bftCore`) on a grid of `2·Δ` slots, one proposer per slot,
polling disabled, one committee kind (votes) at phase 1 signed by every key.
Contract (index: the recurrence gap `k : ℕ+`): safety with no premise, escaped
by global slashability of a third, and local accountability for a third
(conflicting notarizations convict their signers); liveness from GST under partial
synchrony, fewer than a third faulty, full participation from GST, and five
consecutive honest ready proposers (`streamletPattern`) in every window of
`k` slots from GST, with latency `latency k` (`Δ`-coefficient). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)
open Consensus.Premise (fromGST faultsBelowThird)

/-- Slots of `2·Δ`. -/
def streamletGrid : TimeGrid := ⟨2, by decide⟩

/-- The Streamlet skeleton. -/
def streamletSkeleton (n : Nat) : Skeleton n where
  grid := streamletGrid
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  kinds_nodup := List.nodup_singleton _
  kinds_complete := fun _ => List.mem_singleton_self _
  phase := fun _ => 1
  kindSel := fun _ => .all

/-- Five consecutive honest proposers. -/
def streamletPattern : Pattern := ⟨[0, 1, 2, 3, 4], by simp⟩

/-- Liveness at gap `k`. -/
def streamletLivePremise (k : ℕ+) : Premise ProgressReq :=
  .conj .sync <| .conj faultsBelowThird <| .conj (fromGST .full) <|
    .progress ⟨streamletPattern, k⟩ .gst

/-- The Streamlet contract, with the readers' catch-up and the latency bound
as parameters. -/
def streamletContract (catchUp : Nat) (latency : Affine) : Contract bftCore ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  catchUp := catchUp
  spec
    | .final => some
        { safety := { premise := .truth, escape := some (1 / 3) }
          live := ⟨streamletLivePremise, fun _ => .gst, fun k => latency.eval k⟩
          accountable := some (1 / 3) }
    | _ => none

theorem streamletContract_wellFormed (catchUp : Nat) (latency : Affine) :
    (streamletContract catchUp latency).WellFormed := by
  constructor
  intro c s h
  cases c
  · cases h
  · cases h
  · obtain rfl := Option.some.inj h
    have ha : FracWF (some (1 / 3 : ℚ)) := fun α h => by cases h; norm_num
    refine ⟨trivial, ha, fun k => ?_, ha, (fun _ h => nomatch h), (fun _ h => nomatch h),
      fun _ => trivial, (fun _ h => nomatch h)⟩
    norm_num [streamletLivePremise, faultsBelowThird, fromGST, Premise.WellFormed,
      EnvAtom.WellFormed, TimeExpr.HorizonFree]

/-- Non-vacuity of the Streamlet contract for every family with the
skeleton's proposer selection size and grid. -/
theorem streamlet_realizable {Info : Type} [DecidableEq Info] [Encodable Info]
    (catchUp : Nat) (latency : Affine) (F : ShapeFamily bftCore Info)
    (hsel : ∀ pub, (F pub).skel.proposerSel = .sized 1)
    (hG : ∀ pub, (F pub).skel.grid = streamletGrid) :
    (streamletContract catchUp latency).Realizable F := by
  have hwf := streamletContract_wellFormed catchUp latency
  have hs1 : ∀ (Q : Premise ProgressReq), Q.UsesProgress →
      ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m := fun _ _ => ⟨1, le_rfl, hsel⟩
  have hnn (m : Nat) : (0 : Time) ≤ (m : Time) := by positivity
  constructor
  · intro c s h
    cases c
    · cases h
    · cases h
    · obtain rfl := Option.some.inj h
      exact witness_realizable F _ _ (hwf.caps _ _ h).safety (hs1 _) (fun _ => 0) 0 0 le_rfl
        (fun _ _ => trivial) (fun _ _ => trivial)
  · intro c s h k
    change ℕ+ at k
    cases c
    · cases h
    · cases h
    · have hw := (hwf.caps _ _ h).live k
      obtain rfl := Option.some.inj h
      refine live_realizable F _ _ hw (hs1 _) _ _ (fun _ => 0)
        (1 + 2 * (((k : Nat) + 4 : Nat) : Time) + ((latency.eval k : Nat) : Time)) 0 0
        (fun _ _ => ⟨trivial, trivial, trivial, trivial⟩)
        (fun n submit => ⟨trivial, trivial, trivial, ?_⟩) (fun _ => ?_) le_rfl ?_
      · change max (EnvPoint.extremal n _ 0 submit).env.gst 0 + (((k : Nat) + 4 : Nat) : Time) *
          (F (pubOf (EnvPoint.extremal n _ 0 submit).env)).skel.grid.slotLen
            (EnvPoint.extremal n _ 0 submit).env.Δ ≤ (EnvPoint.extremal n _ 0 submit).horizon
        rw [hG]
        simp only [TimeGrid.slotLen, streamletGrid, EnvPoint.extremal]
        push_cast
        rw [max_self]
        linarith [hnn (latency.eval k)]
      · simp [TimeExpr.eval, EnvPoint.extremal]
      · have := hnn ((k : Nat) + 4); push_cast at this ⊢; simp only [max_self]; linarith
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
