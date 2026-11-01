module
public import AvailableChainPCSAProofs.Proofs.Outage.Healthy
public import AvailableChainPCSAProofs.Proofs.Shared.BodyReceipt

public section

/-! CLEAN block receipt (pcsa34-r4.3 §5.2.3) from the Shared body relay and
the healthy-prefix delivery of `Clean₂`. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- [pcsa34-r4.3 §5.2.3; FG-SA fgsa_proposal_receipt] CLEAN block receipt:
a block that an honest node stores at `T` with `T + Δ ≤ b₀` is stored at
every honest node after the ticks of every `t ≥ T + Δ`. -/
theorem pcsa_healthy_block_receipt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hfr : StageOneFrame p c E rho)
    (v : V) (hv : v ∈ rho.honest) (T : Time) (B : Block) (hTb : T + E.Δ ≤ b₀)
    (hB : B ∈ (storeAt p c E rho v T).base.blocks) (y : V) (hy : y ∈ rho.honest)
    (t : Time) (ht : T + E.Δ ≤ t) :
    B ∈ (storeAfterTicks p c E rho y t).base.blocks := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hst : storeAfterTicks p c E rho y t =
      (V2.D.Run.stateBefore E rho (FGSA.Run.afterTicksIdx rho t) y).st := by
    change (FGSA.Run.afterTicks E rho t y).st = _
    rw [FGSA.Run.afterTicks_eq_stateBefore E rho hs t]
  rw [hst]
  rw [pcsa_storeAt_index E rho hs] at hB
  by_cases hg : B = .genesis
  · subst hg
    have h0 : Block.genesis ∈ (V2.D.Run.stateBefore E rho 0 y).st.base.blocks := by
      change Block.genesis ∈ [Block.genesis]
      exact List.mem_singleton_self _
    exact pcsa_body_stateBefore_mono E rho h.noRestart y (Nat.zero_le _) h0
  obtain ⟨j, hjK, tj, o, s, N, P, hev, hd, hNB, hP, hacc, hA⟩ :=
    pcsa_body_receipt_origin E rho h.valid _ v B hg hB
  have htj : tj ≤ T := pcsa_read_events_le E rho hs T j hjK _ hev
  have hR := pcsa_body_relay_before_deadline E rho h hfr hC.healthy j v y hv hy tj o s N P
    hev hd hP hacc hA (by linarith)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs, hNB] at hR
  refine pcsa_body_stateBefore_mono E rho h.noRestart y ?_ hR
  have h3 := (FGSA.Run.preIdx_le_afterTicksIdx E rho hs t).1
  have h2 : (rho.events.filter (fun f => decide (f.time < tj + E.Δ))).length ≤
      (rho.events.filter (fun f => decide (f.time < t))).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro f _ hf
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true hf) (by linarith))
  rw [V2.D.Run.idxBefore_def]
  omega

end AvailableChain.PCSA.Run
end
