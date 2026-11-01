module
public import AvailableChainFGSAProofs.Proofs.Clean.Closure

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A protected receiver constructs a current-epoch saved row above the earlier Clean origin.
The alternative permits a caller to stop when current finality already covers its target.
The receiver window begins at this row's label start, including a restart at that start. -/
theorem clean_epoch_saved_row {ΔF b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {x : V} {q : Slot} {B : Block} (hx : x ∈ rho.honest)
    (hcut : SA.gateTime p.toParams q ≤ b₀)
    (hAw : AwakeClosed E x (slotStartZ p (q : Int)) b₀)
    (hEpoch : RestartFreeTime rho x (slotStartZ p (q : Int)) b₀)
    (hOrigin : B = .genesis ∨ ∃ r D, r < q ∧
      (r, D) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B D) :
    Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
      ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
        some (some C) ∧ Block.Preceq B C := by
  by_cases hFinal : Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x)
  · exact Or.inl hFinal
  have hS := h.base.valid.toScheduleWellFormed
  have h0 : 0 ≤ slotStartZ p (q : Int) := by
    change 0 ≤ 4 * p.Δ * (q : Int)
    have := p.deltaPos
    positivity
  have hsg : slotStartZ p (q : Int) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hAwGate := hAw _ (h0.trans hsg) hsg hcut
  have hpub : V2.PublicTime E (SA.gateTime p.toParams q) := by
    refine ⟨4 * q + 6, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (q : Int) + 6 * p.Δ = _
    push_cast
    ring
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (h.base.valid.tick_total x hx _ hpub
    (h0.trans hsg) (hcut.trans h.cut.2) hAwGate)
  have hJ : joinedAt p E rho x (q + 1) (SA.gateTime p.toParams q) := by
    refine ⟨hAwGate, ?_, ?_⟩
    · intro w hw hwg hW
      change w ≤ 4 * p.Δ * (((q + 1 : Nat) : Int) - 1)
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      by_contra hn
      have hStart : slotStartZ p (q : Int) < w := by
        change 4 * p.Δ * (q : Int) < w
        exact lt_of_not_ge hn
      have haw := hAw (w - 1) (by dsimp [Time] at *; omega)
        (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
      have hFalse := hW.2
      rw [haw] at hFalse
      cases hFalse
    · intro w _ hwg he
      change w ≤ 4 * p.Δ * (((q + 1 : Nat) : Int) - 1)
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      by_contra hn
      exact hEpoch w (by change 4 * p.Δ * (q : Int) < w; exact lt_of_not_ge hn)
        (hwg.trans hcut) he
  have hG := clean_enabledGate_of_joinedAt hS hj hJ
  have hji := (V2.D.Engine.index_lt_read_length_iff hS b₀ hj).mpr hcut
  have hh := clean_invariant p c E rho h hq hf hsrc (timeIdx rho b₀) le_rfl
  obtain ⟨C, hC, _⟩ := hh.nonempty j x q hji hG
  have hCm : (q, C) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
    ⟨j, hji, x, hj, hG.2, hC⟩
  have hBC : Block.Preceq B C := by
    rcases hOrigin with rfl | ⟨r, D, hr, hD, hBD⟩
    · exact block_genesis_preceq C
    · exact block_preceq_trans hBD (hh.ordered r q D C hD hCm hr)
  have hRF : V2.D.restartFree rho x j (timeIdx rho b₀) := by
    intro k w hjk hki he
    have hw : SA.gateTime p.toParams q < w := by
      by_contra hn
      have hkj := V2.D.Engine.restart_index_lt_event hS he hj (le_of_not_gt hn)
        (show 0 < 1 from by decide)
      omega
    have hwcut := (V2.D.Engine.index_lt_read_length_iff hS b₀ he).mp hki
    exact hEpoch w (hsg.trans_lt hw) hwcut (List.mem_of_getElem? he)
  have st := cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho) le_rfl hh
  have hCompat : activeCompatible (storeAt p c E rho (timeIdx rho b₀) x) C = true :=
    cleanHist_belowLabel_compatible hh (belowLabel_of_mem hCm le_rfl) (st.fOrigin x).1
  exact Or.inr ⟨C, st.saved x j q C hji hG hRF hCompat hC, hBC⟩

end AvailableChain.FGSA.Run
end
