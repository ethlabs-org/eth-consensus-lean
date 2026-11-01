module
public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch
public import AvailableChainPCSAProofs.Proofs.Clean.ResultPaths

public section

/-! C6 ZeroResult: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A stored non-genesis body has a positive slot, by its parent admission test. -/
theorem pcsa_body_positive_slot (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ B ∈ st.base.blocks, B = .genesis ∨ 0 < B.slot := by
  induction h with
  | init =>
    intro B hB
    exact Or.inl (List.mem_singleton.mp hB)
  | tick t h ih =>
    rw [pcsa_clock_blocks]
    exact ih
  | @deliver st o h ih =>
    apply pcsa_c3_process_body_pred p _ st o ih
    intro s N P _ _ ha
    right
    change (_ && _ && _ && _ && decide (N.erase.parent.slot < N.erase.slot) &&
      _ && _ && _ && _) = true at ha
    have h8 := (Bool.and_eq_true_iff.mp ha).1
    have h7 := (Bool.and_eq_true_iff.mp h8).1
    have h6 := (Bool.and_eq_true_iff.mp h7).1
    have h5 := (Bool.and_eq_true_iff.mp h6).1
    have hs : N.erase.parent.slot < N.erase.slot :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h5).2
    exact lt_of_le_of_lt (Nat.zero_le _) hs
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Any nonempty label-zero result is genesis. -/
theorem pcsa_zero_result_eq_genesis (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (u : Time) (X : Block)
    (hr : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho k x).st u).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) 0 = some X) : X = .genesis := by
  obtain ⟨i, H, hearly, hresolve, hXH⟩ := pcsa_result_early_support E rho hF k x hx u 0 X hr
  have hm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hresolve)).1
  have ht : GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho k x).st u))
      ⟨.seat 0 i, .head H.root⟩ (SA.earlyTime p.toParams 0) = true :=
    (List.mem_filter.mp hearly).2
  delta GridCO.resolvedBefore at ht
  rw [hresolve] at ht
  have hslot : H.slot ≤ 0 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).1
  rcases pcsa_body_positive_slot p _
      (Reachable.tick u (pcsa_reachable_stateBefore E rho k x)) H hm with hg | hp
  · rw [hg] at hXH
    exact of_decide_eq_true hXH
  · exact (Nat.not_lt.mpr hslot hp).elim
/-- The result component of the clean label-zero base case is exactly genesis. -/
theorem pcsa_clean_zero_result [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) (hc : SA.gateTime p.toParams 0 ≤ cut) :
    gateResultAt p c E rho x 0 = some (some .genesis) := by
  obtain ⟨X, hX⟩ := pcsa_clean_result_exists E rho h hF x hx 0 hc
  obtain ⟨k, _, hr⟩ := pcsa_gateResultAt_source E rho x 0 X hX
  have he := pcsa_zero_result_eq_genesis E rho hF k x hx _ X hr
  rwa [he] at hX
end AvailableChain.PCSA.Run

end
