module
public import AvailableChainPCSAProofs.Proofs.Clean.GateAdvance
public import AvailableChainPCSAProofs.Proofs.Clean.RecordEvents
public import AvailableChainPCSAProofs.Proofs.Shared.RestartSeed
public import AvailableChainPCSAProofs.Proofs.Shared.SlotOrder

public section

/-! K4 of the CI restart: the record reset at the seed gate (pcsa34-r5 §5.5).
A fresh gate with a clear guard sets `S` to its raw result unless the old record
strictly extends it. -/
namespace AvailableChain.PCSA
variable {n : Nat}

/-- With a clear lock guard, the gate sets S to its raw result when the old S
does not strictly extend it. -/
theorem pcsa_gate_record_eq_result (p : Params) (st : State n) (anchor : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (X : Block)
    (hX : SA.Root.confirmationFrom p.toParams anchor (actView st) s = some X)
    (hg : st.base.obligations.any (fun row => st.base.now < row.2.2 &&
      !Block.compatible row.1 X) = false)
    (hS : Block.preceq X st.base.stableRecord = true → st.base.stableRecord = X) :
    (gateFrom p anchor cs rank st s).base.stableRecord = X := by
  rw [gateFrom_def]
  dsimp only
  rw [hX]
  dsimp only
  rw [ite_eq_right (Bool.eq_false_iff.mp hg)]
  apply List.foldlRecOn (motive := fun acc : State n => acc.base.stableRecord = X)
  · change GridCO.advance st.base.stableRecord X = X
    delta GridCO.advance
    split
    · rename_i hp
      exact hS hp
    · rfl
  · intro acc ha b _
    apply List.foldlRecOn (motive := fun acc : State n => acc.base.stableRecord = X)
    · exact ha
    · intro acc' ha' g _
      exact ha'

/-- The full clock at a fresh stage-one gate with a clear guard sets S to its raw
result when the old S does not strictly extend it. -/
theorem pcsa_clock_gate_record_eq_result (p : Params) (st : State p.n) (s : Slot) (X : Block)
    (hf : st.fg.F = .genesis)
    (hfresh : (GridCO.savedGenuine (clockPre p st (SA.gateTime p.toParams s)).base s).isSome =
      false)
    (hX : SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st (SA.gateTime p.toParams
      s)).fg.F) (actView (clockPre p st (SA.gateTime p.toParams s))) s = some X)
    (hg : (clockPre p st (SA.gateTime p.toParams s)).base.obligations.any
      (fun row => (clockPre p st (SA.gateTime p.toParams s)).base.now < row.2.2 &&
        !Block.compatible row.1 X) = false)
    (hS : Block.preceq X st.base.stableRecord = true → st.base.stableRecord = X) :
    (clock p st (SA.gateTime p.toParams s)).base.stableRecord = X := by
  have he := Run.clock_early_succ p st s
  rw [Run.earlyTime_succ_eq_gateTime] at he
  rw [he, gateStep_def]
  dsimp only
  rw [ite_eq_right (Bool.eq_false_iff.mp hfresh)]
  have hF : (gateFrom p (eraseFG (clockPre p st (SA.gateTime p.toParams s)).fg.F)
      (clockPre p st (SA.gateTime p.toParams s)).pcs
      (gateRank p (clockPre p st (SA.gateTime p.toParams s)) s)
      (clockPre p st (SA.gateTime p.toParams s)) s).fg.F = .genesis := by
    rw [(gateFrom_pc_frame _ _ _ _ _ _).2, (clockPre_output_fields p st _).1]
    exact hf
  have hn : ∀ st : State p.n, st.fg.F = .genesis →
      (normalizeS st).base.stableRecord = st.base.stableRecord := by
    intro st hf
    delta normalizeS
    split
    · rfl
    · rename_i hn
      rw [hf] at hn
      exact (hn (Gen.Pure.block_genesis_preceq _)).elim
  rw [hn _ hF]
  apply pcsa_gate_record_eq_result p _ _ _ _ s X hX hg
  rw [(clockPre_output_fields p st _).2]
  exact hS
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- K4: after the seed gate `d_a`, the record of every honest node is the seed block. The
old record is genesis or an earlier own result, whose slot is below `a`; the seed
locks clear the guard. -/
theorem pcsa_restart_post_gate_record (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (hF : StageOneFrame p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (x : V) (hx : x ∈ rho.honest) (nd : Node p)
    (hn : pcsa_postClock E rho x (SA.gateTime p.toParams a) = some nd) :
    nd.st.base.stableRecord = A := by
  have hs := h.valid.toScheduleWellFormed
  rw [pcsa_postClock_def] at hn
  obtain ⟨pre, hpre, he⟩ := Option.map_eq_some_iff.mp hn
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hk, hpre⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  have hev := V2.D.Run.tickIdx?_spec hk
  have hgi : gateInAt p c E rho x a =
      some (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams a)) := by
    rw [pcsa_gateInAt_def, pcsa_preTick_def, hk]
    rfl
  have hX := hS.result x hx _ (by rw [pcsa_gateResultAt_def, hgi]; rfl)
  have hread := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hev
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hread
  have hmono : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤
      V2.D.Run.idxBefore rho (SA.gateTime p.toParams a) := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    apply decide_eq_true
    apply (of_decide_eq_true he).trans_le
    change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  change (clock p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams a)).base.stableRecord
    = A
  apply pcsa_clock_gate_record_eq_result p _ a A ((hF x hx k).1)
    (pcsa_gate_input_unsaved E rho h.valid.nodup k x a hev) hX
  · apply List.any_eq_false.mpr
    intro row hrow
    have hr := pcsa_clockPre_locks_subset p _ _ hrow
    rw [hread] at hr
    have hb := hS.locksFromFreeze x hx _ hmono le_rfl row hr
    have hc : Block.compatible row.1 A = true := Bool.or_eq_true_iff.mpr (Or.inl hb)
    simp [hc]
  · intro hp
    rcases pcsa_record_stateBefore_origin E rho h hF k x hx with hg | ⟨j, hj, s, X, hjev, hXr, hSX⟩
    · rw [hg] at hp ⊢
      exact (of_decide_eq_true hp).symm
    · exfalso
      rw [hSX] at hp
      have hsa : s < a := by
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjev
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hev
        have ht := (List.pairwise_iff_getElem.mp hs.sorted) j k hjl hkl hj
        rw [hje, hke] at ht
        have hle := V2.D.Engine.time_le_of_key_le _ _ ht
        have hne : SA.gateTime p.toParams s ≠ SA.gateTime p.toParams a := by
          intro hst
          rw [hst] at hjev
          have := (List.Nodup.getElem?_inj hjl h.valid.nodup).mp (hjev.trans hev.symm)
          omega
        have hlt := lt_of_le_of_ne hle hne
        change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (a : Int) + 6 * p.Δ at hlt
        have hp' : (0 : Int) < p.Δ := p.deltaPos
        have : (s : Int) < a := by nlinarith
        exact_mod_cast this
      obtain ⟨i, hi, hc⟩ := pcsa_gateResultAt_source E rho x s X hXr
      have hord := pcsa_reachable_slot_order p _
        (Reachable.tick (SA.gateTime p.toParams s) (pcsa_reachable_stateBefore E rho i x))
      have hslot := pcsa_result_prefix_slot p _ _ X A s
        (fun D hD => hord D (List.mem_filter.mp hD).1) hc hp
      rw [hS.slot] at hslot
      exact absurd hslot (Nat.not_le.mpr hsa)
end AvailableChain.PCSA.Run

end
