module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot
public import AvailableChainPCSAProofs.Proofs.Shared.Roots

public section

/-! StageOneFrame supplies Formation F6 and F7 (pcsa34-r4.3 §5.3).
The post-clock duty read keeps the FG state of its indexed pre-tick read. -/

namespace AvailableChain.PCSA

private theorem formation_normalize_fg {n : Nat} (st : State n) :
    (normalizeS st).fg = st.fg := by
  delta normalizeS
  split <;> rfl

private theorem formation_clock_fg (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).fg = st.fg := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    rw [formation_normalize_fg]
    split
    · exact (clockPre_output_fields p st t).1
    · rw [(gateFrom_pc_frame _ _ _ _ _ _).2]
      exact (clockPre_output_fields p st t).1
  · exact (clockPre_output_fields p st t).1

/-- Clock and gate steps preserve a vacuous FG frame. -/
theorem pcsa_formation_frame_clock (p : Params) (st : State p.n) (t : Time)
    (h : Run.FrameVacuous p st) : Run.FrameVacuous p (clock p st t) := by
  rw [Run.FrameVacuous_def, controls_def] at h ⊢
  rw [formation_clock_fg]
  exact h

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- StageOneFrame also holds at every honest post-clock duty read. -/
theorem pcsa_formation_frame_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : StageOneFrame p c E rho)
    (y : V) (t : Time) (nd : Node p) (hy : y ∈ rho.honest)
    (hRead : pcsa_postClock E rho y t = some nd) : FrameVacuous p nd.st := by
  rw [pcsa_postClock_def] at hRead
  obtain ⟨pre, hpre, hclock⟩ := Option.map_eq_some_iff.mp hRead
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  exact pcsa_formation_frame_clock p _ t (h y hy k)

/-- F6: honest duty reads have the same Z and band floor in stage 1. -/
theorem pcsa_formation_equal_frames (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : StageOneFrame p c E rho)
    (x y : V) (t u : Time) (src dst : Node p) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hSrc : pcsa_postClock E rho x t = some src) (hDst : pcsa_postClock E rho y u = some dst) :
    (controls p src.st).Z = (controls p dst.st).Z ∧
      (controls p src.st).lo = (controls p dst.st).lo := by
  have hs := pcsa_formation_frame_read E rho h x t src hx hSrc
  have hd := pcsa_formation_frame_read E rho h y u dst hy hDst
  exact ⟨hs.2.1.trans hd.2.1.symm, hs.2.2.trans hd.2.2.symm⟩

/-- F7: every block is F-compatible at an honest duty read in stage 1. -/
theorem pcsa_formation_fCompatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : StageOneFrame p c E rho)
    (y : V) (t : Time) (nd : Node p) (P : Block) (hy : y ∈ rho.honest)
    (hRead : pcsa_postClock E rho y t = some nd) : Block.Compatible (eraseFG nd.st.fg.F) P := by
  have hf := pcsa_formation_frame_read E rho h y t nd hy hRead
  rw [hf.1]
  exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq P)
    (Gen.Pure.block_preceq_refl P)

end AvailableChain.PCSA.Run
end
