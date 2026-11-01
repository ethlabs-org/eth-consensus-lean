module
public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch

public section

/-! C6 LockEvents: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem lock_write_origin (st : State n) (b : Block) (g : Nat)
    (deadline : Time) (rank : Option PCRank) (row : Block × Nat × Time)
    (hr : row ∈ (writeLease st b g deadline rank).base.obligations) :
    row ∈ st.base.obligations ∨ (row.1 = b ∧ row.2.1 = g) := by
  change row ∈ st.base.obligations.filter _ ++ [_] at hr
  rcases List.mem_append.mp hr with hold | hnew
  · exact Or.inl (List.mem_filter.mp hold).1
  · have he := List.mem_singleton.mp hnew
    subst row
    exact Or.inr ⟨rfl, rfl⟩
/-- Each gate lock is an old row or a slow-level row below the raw result. -/
theorem pcsa_gate_lock_origin (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (row : Block × Nat × Time)
    (hr : row ∈ (gateFrom p a cs rank st s).base.obligations) :
    row ∈ st.base.obligations ∨
      ∃ X, SA.Root.confirmationFrom p.toParams a (actView st) s = some X ∧
        Block.Preceq row.1 X ∧ row.2.1 = SA.releaseThreshold p.toParams := by
  rw [gateFrom_def] at hr
  dsimp only at hr
  cases hx : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rw [hx] at hr; exact Or.inl hr
  | some X =>
    rw [hx] at hr
    dsimp only at hr
    split at hr
    · exact Or.inl hr
    · let Good (acc : State n) := ∀ row ∈ acc.base.obligations,
        row ∈ st.base.obligations ∨
          (Block.Preceq row.1 X ∧ row.2.1 = SA.releaseThreshold p.toParams)
      have hfold (start : State n) (hs : Good start) (bs : List Block)
          (hb : ∀ b ∈ bs, Block.Preceq b X) :
          Good (bs.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
            (fun acc g => writeLease acc b g
              (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine)
                rank) acc) start) := by
        apply List.foldlRecOn (motive := Good)
        · exact hs
        · intro acc ha b hbm
          have hlevels : ∀ g ∈ slowLevels p (actView acc) s b,
              g = SA.releaseThreshold p.toParams := by
            intro g hg
            delta slowLevels at hg
            split at hg
            · exact List.mem_singleton.mp hg
            · exact (List.not_mem_nil hg).elim
          apply List.foldlRecOn (motive := Good)
          · exact ha
          · intro acc' ha' g hg r hmem
            rcases lock_write_origin acc' b g _ rank r hmem with hold | ⟨hrb, hrg⟩
            · exact ha' r hold
            · exact Or.inr ⟨hrb ▸ hb b hbm, hrg.trans (hlevels g hg)⟩
      let start : State n := { st with base := { st.base with
        goldfishRecord := GridCO.advance (actView st).goldfishRecord X
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root
          (actView st) s (some X)
        stableRecord := GridCO.advance st.base.stableRecord X } }
      have hgood := hfold start (fun r hm => Or.inl hm)
        ((actView st).blocks.filter (fun b => b != .genesis && Block.preceq b X &&
          leaseWriteOK cs rank b))
        (fun b hb =>
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).1).2)
      rcases hgood row hr with hold | hnew
      · exact Or.inl hold
      · exact Or.inr ⟨X, rfl, hnew⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA
/-- A new clock lock is below that clock's raw gate result. -/
theorem pcsa_clock_lock_origin (p : Params) (st : State p.n) (t : Time)
    (row : Block × Nat × Time)
    (hr : row ∈ (clock p st t).base.obligations) :
    row ∈ st.base.obligations ∨
      ∃ s X, t = SA.gateTime p.toParams s ∧
        SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
          (actView (clockPre p st t)) s = some X ∧
        Block.Preceq row.1 X ∧ row.2.1 = SA.releaseThreshold p.toParams := by
  delta clock at hr
  dsimp only at hr
  split at hr
  · rename_i hg
    have ht := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def] at hr
    split at hr
    · have hn (acc : State p.n) : (normalizeS acc).base.obligations = acc.base.obligations := by
        delta normalizeS; split <;> rfl
      rw [hn] at hr
      exact Or.inl (pcsa_clockPre_locks_subset p st t hr)
    · have hn (acc : State p.n) : (normalizeS acc).base.obligations = acc.base.obligations := by
        delta normalizeS; split <;> rfl
      rw [hn] at hr
      rcases pcsa_gate_lock_origin p (clockPre p st t) _ _ _ _ row hr with
        hold | ⟨X, hX, hb, hlevel⟩
      · exact Or.inl (pcsa_clockPre_locks_subset p st t hold)
      · exact Or.inr ⟨_, X, ht, hX, hb, hlevel⟩
  · exact Or.inl (pcsa_clockPre_locks_subset p st t hr)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every reachable lock comes from a prior gate result and has the SA release level. -/
theorem pcsa_lock_stateBefore_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (row : Block × Nat × Time)
    (hr : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations) :
    ∃ j < k, ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      gateResultAt p c E rho x s = some (some X) ∧ Block.Preceq row.1 X ∧
        row.2.1 = SA.releaseThreshold p.toParams := by
  induction k with
  | zero => exact (List.not_mem_nil hr).elim
  | succ k ih =>
    have carry (hm : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations) :
        ∃ j < k + 1, ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
          gateResultAt p c E rho x s = some (some X) ∧ Block.Preceq row.1 X ∧
            row.2.1 = SA.releaseThreshold p.toParams := by
      obtain ⟨j, hj, rest⟩ := ih hm
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
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
            exact ⟨k, Nat.lt_succ_self k, s, X, hk, hread, hb, hl⟩
      · have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
        rw [hstep, hh] at hr
        exact carry hr
end AvailableChain.PCSA.Run

end
