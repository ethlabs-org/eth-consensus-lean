module
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun
public import AvailableChainPCSAProofs.Proofs.Outage.Healthy
public import AvailableChainPCSAProofs.Proofs.Shared.Relay

public section

/-! The PC relay in a clean stage-1 prefix (pcsa34-r4.3 §5.4.2 ARM-healthy
(a), §5.2.3), from block receipt. A held key was first installed by a
delivery that accepts the installed PC object: in stage 1 the installing call
carries the PC (an ack in it, a PC or proposal on its slot and root). Strict
relay hands that object to every honest node within `Δ`; a handled PC object
pools its acks, and once the target is stored, collection closure installs
the key (`CollectClosed`). Block receipt (the target is stored at every honest
node by `T + Δ`) is a hypothesis. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (a), §5.2.3] The relay item from block
receipt: a PC held by an honest node at `T` with `T + Δ ≤ b₀` is held, by
slot and target, at every honest node after the ticks of every `t ≥ T + Δ`,
when its target is stored there. -/
theorem pcsa_heldPCRelay_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hfr : StageOneFrame p c E rho)
    (hrecv : ∀ v ∈ rho.honest, ∀ (T : Time) (B : Block), 0 ≤ T → T + E.Δ ≤ b₀ →
      B ∈ (storeAt p c E rho v T).base.blocks → ∀ y ∈ rho.honest, ∀ t : Time,
        T + E.Δ ≤ t → B ∈ (storeAfterTicks p c E rho y t).base.blocks) :
    CleanHeldPCRelay p c E rho b₀ := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  rw [CleanHeldPCRelay_def]
  intro v hv T d hT hTb hd y hy t ht
  rw [pcsa_storeAt_index E rho hs] at hd
  have hB := hrecv v hv T d.target hT hTb (by
    rw [pcsa_storeAt_index E rho hs]
    exact (pcsa_outageStore_stateBefore E rho _ v hv).pcBlocks d hd) y hy t ht
  have hkd : KeyHeld _ d.slot d.target := (KeyHeld_def _ _ _).mpr ⟨d, hd, rfl, rfl⟩
  obtain ⟨i, hiK, C, ti, hCs, hCt, hCm, hacc⟩ := pcsa_keyHeld_accepted E rho h hfr v hv
    d.slot d.target _ hkd
  obtain ⟨o', hev, -⟩ := hacc.1
  have hti : ti ≤ T := pcsa_read_events_le E rho hs T i hiK _ hev
  have hTt : T < t := lt_of_lt_of_le (lt_add_of_pos_right T E.Δ_pos) ht
  have hst : storeAfterTicks p c E rho y t =
      (V2.D.Run.stateBefore E rho (FGSA.Run.afterTicksIdx rho t) y).st := by
    change (FGSA.Run.afterTicks E rho t y).st = _
    rw [FGSA.Run.afterTicks_eq_stateBefore E rho hs t]
  have hidx : ∀ k e, rho.events[k]? = some e → e.time < t →
      k + 1 ≤ FGSA.Run.afterTicksIdx rho t := by
    intro k e hk het
    have h1 := (V2.D.Engine.index_lt_read_length_iff hs e.time hk).mpr le_rfl
    have h2 : (rho.events.filter (fun f => decide (f.time ≤ e.time))).length ≤
        (rho.events.filter (fun f => decide (f.time < t))).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro f _ hf
      exact decide_eq_true (lt_of_le_of_lt (of_decide_eq_true hf) het)
    have h3 := (FGSA.Run.preIdx_le_afterTicksIdx E rho hs t).1
    omega
  have hiA : i + 1 ≤ FGSA.Run.afterTicksIdx rho t :=
    hidx i _ hev (lt_of_le_of_lt hti hTt)
  have hOi := pcsa_outageStore_stateBefore E rho (i + 1) v hv
  have hwf := (pcsa_source_facts _ rho _ _ hOi (pcsa_certSafe_horizon E rho h (i + 1) v)
    0 0 C (Or.inl hCm)).1
  suffices hk : KeyHeld (V2.D.Run.stateBefore E rho (FGSA.Run.afterTicksIdx rho t) y).st
      C.slot C.target by
    rw [KeyHeld_def] at hk
    rw [pcsa_PCStampedBefore_def, hst, ← hCs, ← hCt]
    exact hk
  cases hpr : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y)
      (⟨.none, .pc C⟩ : Obj p) with
  | true =>
    exact pcsa_keyHeld_mono (pcsa_stageOne_mono E rho h.noRestart hfr y hy hiA).1
      ((pcsa_processed_pc _ C).mp hpr)
  | false =>
    obtain ⟨t', -, ht2, j, o'', hevj, hh⟩ := pcsa_strict_relay E rho hC.healthy
      (⟨.none, .pc C⟩ : Obj p) (fun body hb => by cases hb) v y i ti hv hy hacc hpr
      (by linarith) (pcsa_pc_not_excluded _ C)
    have hjA : j + 1 ≤ FGSA.Run.afterTicksIdx rho t :=
      hidx j _ hevj (show t' < t by linarith)
    rcases pcsa_handles_pc_store _ o'' C hwf hh with hk | hp
    · rw [← pcsa_deliver_succ E rho hevj] at hk
      exact pcsa_keyHeld_mono (pcsa_stageOne_mono E rho h.noRestart hfr y hy hjA).1 hk
    · rw [← pcsa_deliver_succ E rho hevj] at hp
      have hFA := hfr y hy (FGSA.Run.afterTicksIdx rho t)
      rw [hst, ← hCt] at hB
      exact pcsa_keyHeld_of_collectClosed _
        (pcsa_collectClosed_stateBefore E rho h y hy (FGSA.Run.afterTicksIdx rho t)) C hwf
        (fun a ha => pcsa_ackPool_mono_run E rho h.noRestart y hjA (hp a ha)) hB
        (pcsa_activeCompatible_genesis _ ((FrameVacuous_def p _).mp hFA).1 C.target)

end AvailableChain.PCSA.Run
end
