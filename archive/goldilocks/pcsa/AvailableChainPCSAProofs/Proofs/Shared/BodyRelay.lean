module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyReceipt
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

public section

/-! Body relay under a `DeliveryWithinOn` premise, shared by the lanes.
The deadline map `dl` is the lane's own: `max t z_{s-1} + Δ` under RECOVERY
and Formation, `t + Δ` under a healthy prefix. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- An accepted exact body is admitted at every honest receiver by `dl t`. -/
theorem pcsa_body_relay_within_on (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {Q : Obj p → Prop} {dl : Time → Time} {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho Q dl cut)
    (j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hj : rho.events[j]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hp : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P)
    (ha : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true)
    (hAccept : V2.D.Run.acceptsAt E rho j x o t) (hQ : Q o) (htd : t < dl t)
    (hc : dl t ≤ cut) :
    N.erase ∈ (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.blocks :=
  pcsa_body_relay_admitted E rho h hF j x y hx hy t o s N P hj hd hp ha (dl t) htd
    (fun hn hnx => hD.relay x hx j o hQ t hAccept y hy hn hc hnx)

/-- A block stored at an honest node before `T` is stored at every honest node
before `dl T`, for a monotone deadline map above the identity. -/
theorem pcsa_stored_body_within_on (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {Q : Obj p → Prop} {dl : Time → Time} {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho Q dl cut)
    (hQ : ∀ (o : Obj p) s N, (toWire p o).decode = some (.block s N) → Q o)
    (hmono : Monotone dl) (hlt : ∀ t, t < dl t)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (T : Time) (hc : dl T ≤ cut)
    (B : Block) (hB : B ∈ (V2.D.Run.stateBeforeTime E rho T x).st.base.blocks) :
    B ∈ (V2.D.Run.stateBeforeTime E rho (dl T) y).st.base.blocks := by
  have hS := h.valid.toScheduleWellFormed
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho T hS] at hB
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl T) hS]
  by_cases hg : B = .genesis
  · subst hg
    have h0 : Block.genesis ∈ (V2.D.Run.stateBefore E rho 0 y).st.base.blocks := by
      change Block.genesis ∈ [Block.genesis]
      exact List.mem_singleton_self _
    exact pcsa_body_stateBefore_mono E rho h.noRestart y (Nat.zero_le _) h0
  obtain ⟨j, hjk, t, o, s, N, P, hev, hd, hNB, hP, hacc, hA⟩ :=
    pcsa_body_receipt_origin E rho h.valid _ x B hg hB
  have htT : t < T := (Gen.V2.Duty.index_lt_idxBefore_iff hS hev T).mp hjk
  have hR := pcsa_body_relay_within_on E rho h hF hD j x y hx hy t o s N P hev hd hP hacc hA
    (hQ o s N hd) (hlt t) ((hmono htT.le).trans hc)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS, hNB] at hR
  have hIdx' : V2.D.Run.idxBefore rho (dl t) ≤ V2.D.Run.idxBefore rho (dl T) := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
      ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) (hmono htT.le))
  exact pcsa_body_stateBefore_mono E rho h.noRestart y hIdx' hR

end AvailableChain.PCSA.Run
end
