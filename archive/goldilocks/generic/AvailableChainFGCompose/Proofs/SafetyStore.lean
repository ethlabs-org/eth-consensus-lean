module
public import AvailableChainFGCompose.Statements.SafetyStore
public import AvailableChainKitV2.DutyStable

public section

/-! Store facts for the generic FG safety theorems. Every reachable state is
`Good`. A stored non-genesis block was delivered to the same node, with its
proposal erasure and its rows. Time reads replay a filtered run. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable [DecidableEq V] {Good : P.State → Prop} {Q : Block → Prop}

private theorem safety_block_preceq_refl (b : Block) : Block.Preceq b b := by
  cases b <;> simp [Block.Preceq, Block.preceq]

/-- Every state before an event index is `Good`. -/
theorem safety_good_stateBefore (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    Good (V2.D.Run.stateBefore E rho i x) := by
  refine V2.D.Engine.stateBefore_step_induction E rho Good (Nat.zero_le i) x ?_ L.initial_good
  intro k e _ _ _ hv hk
  cases e with
  | restart u t =>
    dsimp only [V2.Event.node] at hv
    subst u
    simpa only [V2.D.World.step, Function.update_self] using L.restart_good _ t hk
  | tick u t =>
    dsimp only [V2.Event.node] at hv
    subst u
    simpa only [V2.D.World.step, Function.update_self] using
      V2.D.Engine.tick_preserve E rho Good L.own_good (L.clock_good _ t hk)
  | deliver u o t =>
    dsimp only [V2.Event.node] at hv
    subst u
    simpa only [V2.D.World.step, Function.update_self] using L.process_good _ o hk

/-- Each stored block is genesis or was delivered to the same node. -/
private theorem safety_stateBefore_origin (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    Good (V2.D.Run.stateBefore E rho i x) ∧
      ∀ B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF, B = .genesis ∨
        ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
          S.proposalErase o = some (R.erase B) ∧
          B.rows = (S.proposalRows o).filterMap S.decode := by
  let M : P.State → Prop := fun st => Good st ∧ ∀ B ∈ (R.core st).fg.TF, B = .genesis ∨
    ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
      S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode
  refine V2.D.Engine.stateBefore_step_induction E rho M (Nat.zero_le i) x ?_
    ⟨L.initial_good, fun B hB => Or.inl (L.initial_tf B hB)⟩
  intro k e _ _ he hv hk
  obtain ⟨hg, htf⟩ := hk
  cases e with
  | restart u t =>
    dsimp only [V2.Event.node] at hv
    subst u
    have hM : M (P.restore (P.durable (V2.D.Run.stateBefore E rho k x)) t) :=
      ⟨L.restart_good _ t hg, fun B hB => htf B (L.restart_tf _ t B hg hB)⟩
    simpa only [V2.D.World.step, Function.update_self] using hM
  | tick u t =>
    dsimp only [V2.Event.node] at hv
    subst u
    have hown : ∀ st o, M st → M (P.recordOwn st o) := by
      intro st o hst
      refine ⟨L.own_good st o hst.1, ?_⟩
      rw [C.own_core]
      exact hst.2
    have hclock : M (P.clock (V2.D.Run.stateBefore E rho k x) t) := by
      refine ⟨L.clock_good _ t hg, ?_⟩
      rw [C.clock_fg]
      exact htf
    simpa only [V2.D.World.step, Function.update_self] using
      V2.D.Engine.tick_preserve E rho M hown hclock
  | deliver u o t =>
    dsimp only [V2.Event.node] at hv
    subst u
    have hM : M (P.process (V2.D.Run.stateBefore E rho k x) o) := by
      refine ⟨L.process_good _ o hg, fun B hB => ?_⟩
      by_cases hold : B ∈ (R.core (V2.D.Run.stateBefore E rho k x)).fg.TF
      · exact htf B hold
      · obtain ⟨hp, hrows⟩ := L.process_new _ o B hg hB hold
        exact Or.inr ⟨o, t, List.mem_of_getElem? he, hp, hrows⟩
    simpa only [V2.D.World.step, Function.update_self] using hM

/-- A time read is the final state of a run with a subset of the events. -/
theorem safety_readAt_replay (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) :
    ∃ rho' : V2.D.Run V P, (∀ e ∈ rho'.events, e ∈ rho.events) ∧
      V2.D.Run.readAt E rho t = V2.D.Run.stateBefore E rho' rho'.events.length := by
  let rho' : V2.D.Run V P :=
    { rho with events := rho.events.filter (fun e => decide (e.time ≤ t)) }
  refine ⟨rho', fun e he => (List.mem_filter.mp he).1, ?_⟩
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  change _ = (rho'.events.take rho'.events.length).foldl (V2.D.World.step E rho')
    V2.D.World.init
  rw [List.take_length, hs]
  rfl

theorem safety_good_readAt (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) :
    Good (V2.D.Run.readAt E rho t x) := by
  obtain ⟨rho', -, h⟩ := safety_readAt_replay E rho t
  rw [h]
  exact safety_good_stateBefore L E rho' _ x

theorem safety_stored_delivery (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) (hne : B ≠ .genesis) :
    ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
      S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode :=
  ((safety_stateBefore_origin C L E rho i x).2 B hB).resolve_left hne

theorem safety_read_delivery (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    ∃ o t', V2.Event.deliver x o t' ∈ rho.events ∧
      S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode := by
  obtain ⟨rho', hsub, h⟩ := safety_readAt_replay E rho t
  rw [h] at hB
  obtain ⟨o, t', hd, hp, hrows⟩ := safety_stored_delivery C L E rho' _ x B hB hne
  exact ⟨o, t', hsub _ hd, hp, hrows⟩

theorem safety_stored_runBlock (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t, hd, hp, -⟩ := safety_stored_delivery C L E rho i x B hB hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t, hd⟩, safety_block_preceq_refl _⟩

theorem safety_read_runBlock (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t', hd, hp, -⟩ := safety_read_delivery C L E rho t x B hB hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t', hd⟩, safety_block_preceq_refl _⟩

theorem safety_stored_scope {E : Generic.Env V} {rho : V2.D.Run V P}
    (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (N : FGSafetyScopeLaws R S E rho Q) (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t, hd, hp, -⟩ := safety_stored_delivery C L E rho i x B hB hne
  exact N.delivered_scope x o t _ hd hp

theorem safety_read_scope {E : Generic.Env V} {rho : V2.D.Run V P}
    (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (N : FGSafetyScopeLaws R S E rho Q) (t : Time) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t', hd, hp, -⟩ := safety_read_delivery C L E rho t x B hB hne
  exact N.delivered_scope x o t' _ hd hp

theorem safety_invariant_stateBefore (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    FGStoreInvariant H f (R.core (V2.D.Run.stateBefore E rho i x)).fg :=
  L.invariant _ (safety_good_stateBefore L E rho i x)

theorem safety_invariant_readAt (L : FGSafetyStoreLaws R S H f Good)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) :
    FGStoreInvariant H f (R.core (V2.D.Run.readAt E rho t x)).fg :=
  L.invariant _ (safety_good_readAt L E rho t x)

end AvailableChain.FGCompose
end
