module
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents

public section

/-! K3 of the CI restart: lock origin from a cut index. A lock row stored after
the cut was stored at the cut, or a later own gate wrote it below its raw
result. Renewals count as writes. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A lock row stored after a cut index was stored at the cut or written by a
later own gate below that gate's raw result. -/
theorem pcsa_lock_stateBefore_origin_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (c₀ k : Nat) (hck : c₀ ≤ k) (x : V) (row : Block × Nat × Time)
    (hr : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations) :
    row ∈ (V2.D.Run.stateBefore E rho c₀ x).st.base.obligations ∨
      ∃ j, c₀ ≤ j ∧ j < k ∧ ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
        gateResultAt p c E rho x s = some (some X) ∧ Block.Preceq row.1 X ∧
          row.2.1 = SA.releaseThreshold p.toParams := by
  induction k, hck using Nat.le_induction generalizing row with
  | base => exact Or.inl hr
  | succ k hck ih =>
    have carry (hm : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations) :
        row ∈ (V2.D.Run.stateBefore E rho c₀ x).st.base.obligations ∨
          ∃ j, c₀ ≤ j ∧ j < k + 1 ∧ ∃ s X,
            rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
            gateResultAt p c E rho x s = some (some X) ∧ Block.Preceq row.1 X ∧
              row.2.1 = SA.releaseThreshold p.toParams := by
      rcases ih row hm with hold | ⟨j, hcj, hj, rest⟩
      · exact Or.inl hold
      · exact Or.inr ⟨j, hcj, Nat.lt_succ_of_lt hj, rest⟩
    cases he : rho.events[k]? with
    | none =>
      have hsame : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      exact carry (hsame ▸ hr)
    | some e =>
      have hstep := V2.D.Run.stateBefore_succ E rho he
      by_cases hn : e.node = x
      · cases e with
        | restart y t => exact (h.noRestart k y t he).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          rw [hstep] at hr
          change row ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.obligations
            at hr
          rw [Function.update_self] at hr
          exact carry (pcsa_process_locks_subset p _ (toWire p o) hr)
        | tick y t =>
          change y = x at hn
          subst y
          have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
              clock p (V2.D.Run.stateBefore E rho k x).st t := by
            rw [hstep]
            change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
            rw [Function.update_self]
            exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
          rw [hclock] at hr
          rcases pcsa_clock_lock_origin p _ t row hr with hold | ⟨s, X, ht, hX, hb, hl⟩
          · exact carry hold
          · have hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) := ht ▸ he
            have hread : gateResultAt p c E rho x s = some (some X) := by
              rw [pcsa_gateResultAt_at_tick E rho h.valid.nodup k x s hk,
                pcsa_clock_confirmation_eq_pre, ← ht]
              exact congrArg some hX
            exact Or.inr ⟨k, hck, Nat.lt_succ_self k, s, X, hk, hread, hb, hl⟩
      · have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
        rw [hstep, hh] at hr
        exact carry hr
end AvailableChain.PCSA.Run

end
