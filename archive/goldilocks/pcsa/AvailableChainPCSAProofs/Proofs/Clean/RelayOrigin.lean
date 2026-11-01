module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayCarrier

public section

/-! C6 RelayOrigin: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
open AvailableChain.PCSA.CleanPCRelay
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A PC object is processed exactly when its key is held. -/
theorem pcsa_clean_processed_pc (nd : Node p) (C : PC p.n) :
    (pcsaWith m p c).processed nd (⟨.none, .pc C⟩ : Obj p) = true ↔
      KeyHeld nd.st C.slot C.target := by
  rw [pcsa_keyHeld_iff_any]
  exact Iff.rfl

/-- The state after a tick of its node is the clock. -/
theorem pcsa_clean_tick_step (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat)
    (v : V) (t : Time) :
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick v t) v).st =
      clock p (V2.D.Run.stateBefore E rho k v).st t := by
  change (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st = _
  rw [Function.update_self]
  exact pcsa_tick_st E rho _ v t

/-- The state after a delivery to its node is the delivery handler. -/
theorem pcsa_clean_deliver_succ (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) {k : Nat}
    {v : V} {o : Obj p} {t : Time} (he : rho.events[k]? = some (.deliver v o t)) :
    (V2.D.Run.stateBefore E rho (k + 1) v).st =
      process p (V2.D.Run.stateBefore E rho k v).st (toWire p o) := by
  rw [V2.D.Run.stateBefore_succ E rho he]
  change (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st = _
  rw [Function.update_self]
  rfl

/-- [pcsa34-r4.3 §3.6, §5.2.3] Stage 1: a key held at an honest index was
installed by an earlier delivery that accepts the installed PC object (the
installing call carries it). -/
theorem pcsa_clean_keyHeld_accepted (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (v : V) (hv : v ∈ rho.honest)
    (s : Slot) (B : Block) (K : Nat)
    (hK : KeyHeld (V2.D.Run.stateBefore E rho K v).st s B) :
    ∃ i < K, ∃ (C : PC p.n) (t : Time), C.slot = s ∧ C.target = B ∧
      C ∈ (V2.D.Run.stateBefore E rho (i + 1) v).st.pcs ∧
      V2.D.Run.acceptsAt E rho i v (⟨.none, .pc C⟩ : Obj p) t := by
  by_contra hno
  revert hK
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ¬ KeyHeld nd.st s B) (Nat.zero_le K) v ?_ ?_
  · intro k e _ hkK he hn hk
    cases e with
    | restart u t => exact absurd he (h.noRestart k u t)
    | tick u t =>
      change u = v at hn
      subst u
      show ¬ KeyHeld (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick v t) v).st s B
      rw [pcsa_clean_tick_step, KeyHeld_def, (pcsa_clock_frame p _ t).1, ← KeyHeld_def]
      exact hk
    | deliver u o t =>
      change u = v at hn
      subst u
      have hsucc := pcsa_clean_deliver_succ E rho he
      rw [← V2.D.Run.stateBefore_succ E rho he, hsucc]
      intro hk'
      apply hno
      rw [KeyHeld_def] at hk'
      obtain ⟨C, hC, hCs, hCt⟩ := hk'
      have hCn : C ∉ (V2.D.Run.stateBefore E rho k v).st.pcs := by
        intro hm
        exact hk ((KeyHeld_def _ _ _).mpr ⟨C, hm, hCs, hCt⟩)
      refine ⟨k, hkK, C, t, hCs, hCt, by rw [hsucc]; exact hC, ⟨o, he, ?_⟩, ?_, ?_⟩
      · have hcar := pcsa_install_carries _ o (h.valid.wire k v o t he)
          (pcsa_clean_collectClosed E rho h k v hv)
          ((FrameVacuous_def p _).mp (hfr v hv k)).1 C hC (by rw [hCs, hCt]; exact hk)
        exact Or.inr (Or.inr ⟨hcar, C, rfl, hC, hCn⟩)
      · cases hb : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho k v)
          (⟨.none, .pc C⟩ : Obj p)
        · rfl
        · have hk2 := (pcsa_clean_processed_pc _ C).mp hb
          rw [hCs, hCt] at hk2
          exact absurd hk2 hk
      · refine (pcsa_clean_processed_pc _ C).mpr ?_
        rw [hsucc, KeyHeld_def]
        exact ⟨C, hC, rfl, rfl⟩
  · intro h0
    rw [KeyHeld_def] at h0
    obtain ⟨c', hc, -⟩ := h0
    exact List.not_mem_nil hc

end AvailableChain.PCSA.Run

end
