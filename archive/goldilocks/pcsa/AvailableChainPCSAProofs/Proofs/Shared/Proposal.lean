module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties

public section

/-! Exact honest proposer geometry (pcsa34-r4.3b §5.3), shared by the lanes.
Copied from the Formation lane (Clean/FormationProposal.lean, 6a5fc76) under
lane-neutral names. -/
namespace AvailableChain.PCSA

/-- Changing the application value keeps the selected parent and walk inputs. -/
theorem pcsa_propose_parent (p : Params) (st : State p.n) (s app : Nat)
    (N : NamedProposal p.n)
    (h : (propose p st s).map (Run.withApp p app) = some (.proposal N)) :
    N.erase.slot = s ∧ N.erase.parent =
      getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s) ∧
      N.pc = proposerPC p st := by
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp h
  delta propose at hM
  split at hM
  · cases hM
  · obtain ⟨P, hP, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p P s app _ _ _ _) = Msg.proposal N at hN
    have he := Msg.proposal.inj hN
    subst N
    have hErase : P.erase =
        getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s) := by
      delta namedByErase? at hP
      cases heq : (st.namedBodies.filter (fun X => X.erase ==
          getHead p st (proposerPC p st) (proposerVotes st s)
            (proposerSupport st s))).eraseDups with
      | nil => rw [heq] at hP; cases hP
      | cons A tail =>
        rw [heq] at hP
        cases ht : tail with
        | nil =>
          rw [ht] at hP
          change some A = some P at hP
          cases Option.some.inj hP
          have hm : P ∈ (st.namedBodies.filter (fun X => X.erase ==
              getHead p st (proposerPC p st) (proposerVotes st s)
                (proposerSupport st s))).eraseDups := by
            rw [heq, ht]
            exact List.mem_singleton_self _
          exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_eraseDups.mp hm)).2
        | cons B rest => rw [ht] at hP; cases hP
    exact ⟨rfl, hErase, rfl⟩

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Only the proposal duty uses the proposal signing label of a slot. -/
theorem pcsa_signLabel_prop (d : RunDuty) (s : Slot) :
    d.signLabel = .prop s ↔ d = .propAction s := by
  cases d <;> delta RunDuty.signLabel <;>
    simp only [RunLabel.prop.injEq, RunDuty.propAction.injEq, reduceCtorEq]

/-- An honest emitted proposal has the exact parent selected by its duty. -/
theorem pcsa_emitted_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (x : V) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho k) :
    t = SA.proposalTime p.toParams s ∧ N.erase.slot = s ∧
      N.erase.parent = getHead p (clock p (V2.D.Run.stateBefore E rho k x).st t)
        (proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st t))
        (proposerVotes (clock p (V2.D.Run.stateBefore E rho k x).st t) s)
        (proposerSupport (clock p (V2.D.Run.stateBefore E rho k x).st t) s) ∧
      N.pc = proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st t) := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s) ⟨0, Nat.one_pos⟩
      (.proposal N)).mp ho
  obtain rfl := (pcsa_signLabel_prop d s).mp hl
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
      (withApp p (c.app (rho.input x t))) = some (.proposal N) at ha
  all_goals exact ⟨ht.symm, pcsa_propose_parent p _ s _ N ha⟩


/-- The honest proposal of slot `s` is built at the proposer post-clock state
of `t_s`: its parent is the proposer head and its PC is the proposer view. -/
theorem pcsa_honest_proposal_state (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N) :
    ∃ nd : Node p, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd ∧
      N.erase.slot = s ∧
      N.erase.parent =
        getHead p nd.st (proposerPC p nd.st) (proposerVotes nd.st s) (proposerSupport nd.st s) ∧
      N.pc = proposerPC p nd.st := by
  obtain ⟨k, hk, hem⟩ := hN.2
  have hd := pcsa_emitted_parent E rho s N _ _ k hk hem
  let nd : Node p := (pcsaWith m p c).clock
    (V2.D.Run.stateBefore E rho k
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s))
    (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)
  have hr : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd := by
    rw [pcsa_postClock_def, pcsa_preTick_def]
    have hk' := hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp
      (show (V2.D.Run.tickIdx? rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)).isSome = true from by
        delta V2.D.Run.tickIdx?
        rw [List.findIdx?_isSome, List.any_eq_true]
        refine ⟨_, List.mem_of_getElem? hk', ?_⟩
        exact decide_eq_true ⟨rfl, rfl⟩)
    have he := V2.D.Run.tickIdx?_spec hj
    have heq : j = k := (List.Nodup.getElem?_inj
      (List.getElem?_eq_some_iff.mp he).1 h.valid.nodup).mp (he.trans hk.symm)
    rw [heq] at hj
    rw [hj]
    rfl
  exact ⟨nd, hr, hd.2.1, hd.2.2.1, hd.2.2.2⟩

end AvailableChain.PCSA.Run
end
