module
public import AvailableChainFGCompose.Statements.SafetyStore
public import AvailableChainFGCompose.Statements.EventReads -- shake: keep (re-export)
public import AvailableChainKitV2.DutyStable
public import AvailableChainKitFG.Correspondence -- shake: keep (re-export)

public section

/-! S3a field 7: finalized monotonicity from the core and order laws.
Ports F/FinalizedSafety.lean:27-64 and F/Store.lean:35-53 (fgsa_rMono). -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

/-- The local finalized block only extends on a restart-free run. -/
theorem safety_F_mono (C : FGCoreLaws R) (O : FGSafetyOrderLaws R S)
    (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j x)).fg.F := by
  apply V2.D.Engine.stateBefore_stable (P := P)
    (fun nd => FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F (R.core nd).fg.F)
    ?_ ?_ ?_ E rho hij x (hnr.restartFree x i j) (KitFG.preceq_refl _)
  · intro nd t h
    rw [C.clock_fg]
    exact h
  · intro nd o h
    exact KitFG.preceq_trans h (O.process_F nd o)
  · intro nd o h
    rw [C.own_core]
    exact h

/-- The local finalized block extends when restore keeps F. -/
theorem safety_F_mono_all (C : FGCoreLaws R) (O : FGSafetyOrderLaws R S)
    (L : FGSafetyRestartLaws R) {i j : Nat} (hij : i ≤ j) (x : V) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j x)).fg.F := by
  apply V2.D.Engine.stateBefore_stable_restore (P := P)
    (fun nd => FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F (R.core nd).fg.F)
    ?_ ?_ ?_ E rho hij x ?_ (KitFG.preceq_refl _)
  · intro nd t h
    rw [C.clock_fg]
    exact h
  · intro nd o h
    exact KitFG.preceq_trans h (O.process_F nd o)
  · intro nd o h
    rw [C.own_core]
    exact h
  · intro nd t h
    rw [L.restart_F]
    exact h

private theorem safety_filter_prefix {α : Type} {r : α → α → Prop} {q : α → Bool}
    (hd : ∀ a b, r a b → q b = true → q a = true)
    (xs : List α) (hs : xs.Pairwise r) : xs.filter q = xs.takeWhile q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq, List.takeWhile_cons_of_pos hq, ih hs]
      · rw [List.filter_cons_of_neg hq, List.takeWhile_cons_of_neg hq]
        exact List.filter_eq_nil_iff.mpr (fun b hb hqb => hq (hd a b (ha b hb) hqb))

/-- On a key-sorted run, the inclusive time read is an event-prefix read. -/
theorem safety_readAt_prefix (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (t : Time) : V2.D.Run.readAt E rho t = V2.D.Run.stateBefore E rho (timeIdx rho t) := by
  have hf := safety_filter_prefix (q := fun e => decide (e.time ≤ t))
    (fun a b hk hb => decide_eq_true
      (le_trans (V2.D.Engine.time_le_of_key_le a b hk) (of_decide_eq_true hb))) rho.events hs
  have hp : (rho.events.filter (fun e => decide (e.time ≤ t))).IsPrefix rho.events := by
    rw [hf]
    exact List.takeWhile_prefix _
  rw [timeIdx_def]
  exact congrArg (fun es => es.foldl (V2.D.World.step E rho) V2.D.World.init)
    (List.prefix_iff_eq_take.mp hp)

/-- Field 7. Sorted inclusive time reads inherit the event-prefix order of F.
Restore may reset F, so NoRestart is required. -/
theorem safety_finalized_monotone
    (C : FGCoreLaws R) (O : FGSafetyOrderLaws R S)
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (S.finalizedOut (V2.D.Run.readAt E rho t x))
        (S.finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  intro x _ t t' htt
  rw [safety_readAt_prefix E rho hs t, safety_readAt_prefix E rho hs t', O.output_eq,
    O.output_eq]
  exact O.erase_prefix _ _
    (safety_F_mono R S E rho C O hnr (V2.D.Engine.read_length_mono t t' htt) x)

/-- DC: SAME. Sorted inclusive time reads preserve finalized output across restarts. -/
theorem safety_finalized_monotone_all
    (C : FGCoreLaws R) (O : FGSafetyOrderLaws R S) (L : FGSafetyRestartLaws R)
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key)) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (S.finalizedOut (V2.D.Run.readAt E rho t x))
        (S.finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  intro x _ t t' htt
  rw [safety_readAt_prefix E rho hs t, safety_readAt_prefix E rho hs t', O.output_eq,
    O.output_eq]
  exact O.erase_prefix _ _
    (safety_F_mono_all R S E rho C O L (V2.D.Engine.read_length_mono t t' htt) x)

end AvailableChain.FGCompose
end
