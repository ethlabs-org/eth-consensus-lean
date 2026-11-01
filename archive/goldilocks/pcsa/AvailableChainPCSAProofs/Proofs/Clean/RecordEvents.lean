module
public import AvailableChainPCSAProofs.Proofs.Clean.StoreOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.GateReads
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch

public section

/-! C6 RecordEvents: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem gate_record_origin (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.stableRecord = st.base.stableRecord ∨
      ∃ X, SA.Root.confirmationFrom p.toParams a (actView st) s = some X ∧
        (gateFrom p a cs rank st s).base.stableRecord = X := by
  rw [gateFrom_def]
  dsimp only
  cases hr : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact Or.inl rfl
  | some X =>
    dsimp only
    split
    · exact Or.inl rfl
    · have hs (start : State n) (blocks : List Block) :
          (blocks.foldl
            (fun (acc : State n) b => (slowLevels p (actView acc) s b).foldl
              (fun acc g => writeLease acc b g
                (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine) rank) acc)
            start).base.stableRecord = start.base.stableRecord := by
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.base.stableRecord = start.base.stableRecord)
        · rfl
        · intro acc hh b _
          apply List.foldlRecOn
            (motive := fun acc : State n => acc.base.stableRecord = start.base.stableRecord)
          · exact hh
          · intro acc' hh' g _
            exact hh'
      rw [hs]
      delta GridCO.advance
      split
      · exact Or.inl rfl
      · exact Or.inr ⟨X, rfl, rfl⟩
private theorem normalize_record_genesis (st : State n) (hf : st.fg.F = .genesis) :
    (normalizeS st).base.stableRecord = st.base.stableRecord := by
  delta normalizeS
  split
  · rfl
  · rename_i hn
    rw [hf] at hn
    exact (hn (Gen.Pure.block_genesis_preceq _)).elim
/-- In stage 1, a changed clock record is the raw result of the clock's exact gate label. -/
theorem pcsa_clock_record_origin (p : Params) (st : State p.n) (t : Time)
    (hf : st.fg.F = .genesis) :
    (clock p st t).base.stableRecord = st.base.stableRecord ∨
      ∃ s X, t = SA.gateTime p.toParams s ∧
        SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p st t).fg.F) (actView (clockPre p st t)) s = some X ∧
        (clock p st t).base.stableRecord = X := by
  let label := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  have hpre : (clockPre p st t).fg.F = .genesis := by
    rw [(clockPre_output_fields p st t).1]
    exact hf
  have hs := (clockPre_output_fields p st t).2
  delta clock
  dsimp only
  split
  · rename_i hg
    have ht := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def]
    split
    · rw [normalize_record_genesis _ hpre]
      exact Or.inl hs
    · have hfg : (gateFrom p (eraseFG (clockPre p st t).fg.F)
          (clockPre p st t).pcs (gateRank p (clockPre p st t) label)
          (clockPre p st t) label).fg.F = .genesis := by
        rw [(gateFrom_pc_frame _ _ _ _ _ _).2]
        exact hpre
      rw [normalize_record_genesis _ hfg]
      rcases gate_record_origin p (clockPre p st t) (eraseFG (clockPre p st t).fg.F)
        (clockPre p st t).pcs (gateRank p (clockPre p st t) label) label with hold | ⟨X, hr, hX⟩
      · exact Or.inl (hold.trans hs)
      · exact Or.inr ⟨_, X, ht, hr, hX⟩
  · exact Or.inl hs
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every honest S is genesis or an earlier own raw gate result. -/
theorem pcsa_record_stateBefore_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (x : V) (hx : x ∈ rho.honest) :
    (V2.D.Run.stateBefore E rho k x).st.base.stableRecord = .genesis ∨
      ∃ j < k, ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
        gateResultAt p c E rho x s = some (some X) ∧
        (V2.D.Run.stateBefore E rho k x).st.base.stableRecord = X := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    cases he : rho.events[k]? with
    | none =>
      have hsame : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      rw [hsame]
      rcases ih with hh | ⟨j, hj, rest⟩
      · exact Or.inl hh
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    | some e =>
      have hstep := V2.D.Run.stateBefore_succ E rho he
      have carry (hkeep : (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord =
          (V2.D.Run.stateBefore E rho k x).st.base.stableRecord) :
          (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord = .genesis ∨
            ∃ j < k + 1, ∃ s X, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
              gateResultAt p c E rho x s = some (some X) ∧
              (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord = X := by
        rw [hkeep]
        rcases ih with hh | ⟨j, hj, rest⟩
        · exact Or.inl hh
        · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, rest⟩
      by_cases hn : e.node = x
      · cases e with
        | restart y t => exact (h.noRestart k y t he).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          apply carry
          have hf := (hF x hx (k + 1)).1
          rw [hstep] at hf ⊢
          change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.fg.F = .genesis at hf
          change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.stableRecord = _
          rw [Function.update_self] at hf ⊢
          exact pcsa_process_record_of_genesis p _ (toWire p o) hf
        | tick y t =>
          change y = x at hn
          subst y
          have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
              clock p (V2.D.Run.stateBefore E rho k x).st t := by
            rw [hstep]
            change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
            rw [Function.update_self]
            exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
          rcases pcsa_clock_record_origin p (V2.D.Run.stateBefore E rho k x).st t
              (hF x hx k).1 with hold | ⟨s, X, ht, hr, hX⟩
          · exact carry (by rw [hclock]; exact hold)
          · have hread : gateResultAt p c E rho x s = some (some X) := by
              have hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) := ht ▸ he
              rw [pcsa_gateResultAt_at_tick E rho h.valid.nodup k x s hk,
                pcsa_clock_confirmation_eq_pre]
              rw [← ht]
              exact congrArg some hr
            exact Or.inr ⟨k, Nat.lt_succ_self k, s, X, ht ▸ he, hread,
              by rw [hclock]; exact hX⟩
      · apply carry
        have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
        rw [hstep, hh]
end AvailableChain.PCSA.Run

end
