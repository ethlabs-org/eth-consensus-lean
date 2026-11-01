module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! Recovery timing and participation (pcsa34-r4.3b §5.6.1).
The delivery bridge states its exclusion transport input explicitly. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [DecidableEq V] [Fintype V] in
/-- The preceding freeze is after GST at the first recovery proposal. -/
theorem recovery_freeze_after_gst (E : Generic.Env V) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s) :
    E.t_GST ≤ SA.freezeTime p.toParams (s - 1) := by
  try delta Slot Time at *
  have hc : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
  change E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) at ha
  change E.t_GST ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
  rw [hc]
  linarith

/-- Full participation makes the label's honest set the whole honest set. -/
theorem recovery_awake_label (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s : Slot)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon) :
    awakeHonestLabel p c E rho s = rho.honest := by
  try delta Slot Time at *
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hv : E.t_GST ≤ SA.voteTime p.toParams s ∧
      SA.voteTime p.toParams s ≤ rho.horizon := by
    try delta Slot Time at *
    change E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) at ha
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ rho.horizon at hh
    change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ ∧
      4 * p.Δ * (s : Int) + p.Δ ≤ rho.horizon
    constructor <;> linarith
  have he : E.t_GST ≤ SA.earlyTime p.toParams s ∧
      SA.earlyTime p.toParams s ≤ rho.horizon := by
    try delta Slot Time at *
    change E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) at ha
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ rho.horizon at hh
    change E.t_GST ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ ∧
      4 * p.Δ * (s : Int) + 2 * p.Δ ≤ rho.horizon
    constructor <;> linarith
  rw [pcsa_awakeHonestLabel_def]
  ext x
  simp only [Finset.mem_inter, Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
  exact ⟨fun hx => hx.1.1, fun hx =>
    ⟨⟨hx, h.awake x hx _ hv.1 hv.2⟩, ⟨hx, h.awake x hx _ he.1 he.2⟩⟩⟩

/-- F2 and the strict honest majority follow from the recovery fault cap. -/
theorem recovery_participation (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s : Slot)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon) :
    nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card ∧
      (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho s).card := by
  try delta Slot Time at *
  rw [recovery_awake_label E rho h s ha hh]
  have hn : p.n = Fintype.card V :=
    h.base.cstar.seats_eq (ℓ := .base (.head s)) trivial
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    try delta Slot Time at *
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hle := Finset.card_le_univ rho.honest
    omega
  have hcap : 4 * (Gen.V2.Duty.faulty rho).card ≤ p.n := h.quarterCap
  have hpos := p.nPos
  rw [pcsa_nQuorum_eq_qN, Gen.Pure.qN_def]
  omega

/-- F1 follows from RECOVERY once non-exclusion transports to the earlier deadline. -/
theorem recovery_delivery (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (exclusionTransport : ∀ y ∈ rho.honest, ∀ o, IsNonRow o → ∀ t,
      (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho
        (max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) y) o = false →
      (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho
        (max t E.t_GST + E.Δ) y) o = false) :
    Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ)
      (SA.gateTime p.toParams s) := by
  try delta Slot Time at *
  have hdelay : ∀ o : Obj p, IsNonRow o → pcsaDelay p E.Δ ΔF o = E.Δ := by
    intro o ho
    rw [pcsaDelay_def]
    cases he : o.payload <;> simp only [pcsa_IsNonRow_def, he] at ho ⊢
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho h.sync
    IsNonRow E.Δ hdelay
  have hbound (t : Time) : max t E.t_GST + E.Δ ≤
      max t (SA.freezeTime p.toParams (s - 1)) + E.Δ :=
    by
      have hb := max_le_max_left t (recovery_freeze_after_gst E s hs ha)
      exact Int.add_le_add_right hb E.Δ
  constructor
  · intro x hx o ho t ht y hy hc hn
    obtain ⟨u, hu, hd, hr⟩ := hD.broadcast x hx o ho t ht y hy
      ((hbound t).trans (hc.trans hh)) (exclusionTransport y hy o ho t hn)
    exact ⟨u, hu, hd.trans_le (hbound t), hr⟩
  · intro x hx i o ho t ht y hy hp hc hn
    obtain ⟨u, hu, hd, hr⟩ := hD.relay x hx i o ho t ht y hy hp
      ((hbound t).trans (hc.trans hh)) (exclusionTransport y hy o ho t hn)
    exact ⟨u, hu, hd.trans_le (hbound t), hr⟩

/-- The first honest recovery proposal meets the advertised gate deadline.
The horizon case split avoids an extra recurrence-horizon premise. -/
theorem recovery_first_gate_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s₁ : Slot)
    (hmin : ∀ s : Slot, E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s → s < s₁ →
      ¬ Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s)
    (hh : SA.gateTime p.toParams s₁ ≤ rho.horizon) :
    SA.gateTime p.toParams s₁ ≤ E.t_GST + G + 7 * p.Δ := by
  try delta Slot Time at *
  have hd : (0 : Int) < p.Δ := p.deltaPos
  by_cases hhor : E.t_GST + p.Δ + G ≤ rho.horizon
  · obtain ⟨s, hlow, hupp, hhon⟩ := h.gap (E.t_GST + p.Δ) (by linarith) hhor
    have hlo : E.t_GST + p.Δ < SA.proposalTime p.toParams s := hlow
    have hup : SA.proposalTime p.toParams s ≤ E.t_GST + p.Δ + G := hupp
    have hp : Gen.V2.Duty.HonestAwakeProposer E
        (pcsaInterface p c (m := m)).toInterface rho s :=
      ⟨hhon.2, h.awake _ hhon.2 _ (by change E.t_GST ≤ SA.proposalTime p.toParams s; linarith)
        (hupp.trans hhor)⟩
    have hle : s₁ ≤ s := by
      try delta Slot Time at *
      by_contra hn
      exact hmin s (le_of_lt hlo) (by omega) hp
    have hc : (s₁ : Int) ≤ (s : Int) := by exact_mod_cast hle
    have ht := mul_le_mul_of_nonneg_left hc (show (0 : Int) ≤ 4 * p.Δ by positivity)
    change 4 * p.Δ * (s : Int) ≤ E.t_GST + p.Δ + G at hup
    change 4 * p.Δ * (s₁ : Int) + 6 * p.Δ ≤ _
    linarith
  · linarith

/-- Recovery gives quorum participation when the early read is in the run. -/
theorem recovery_participation_at_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (u : Slot)
    (hafter : E.t_GST ≤ SA.proposalTime p.toParams u)
    (he : SA.earlyTime p.toParams u ≤ rho.horizon) :
    nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card ∧
      (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho u).card := by
  have hd := p.deltaPos
  have hv : E.t_GST ≤ SA.voteTime p.toParams u ∧
      SA.voteTime p.toParams u ≤ rho.horizon := by
    change E.t_GST ≤ 4 * p.Δ * (u : Int) at hafter
    change 4 * p.Δ * (u : Int) + 2 * p.Δ ≤ rho.horizon at he
    change E.t_GST ≤ 4 * p.Δ * (u : Int) + p.Δ ∧
      4 * p.Δ * (u : Int) + p.Δ ≤ rho.horizon
    constructor <;> linarith
  have hge : E.t_GST ≤ SA.earlyTime p.toParams u := by
    change E.t_GST ≤ 4 * p.Δ * (u : Int) at hafter
    change E.t_GST ≤ 4 * p.Δ * (u : Int) + 2 * p.Δ
    linarith
  have hlabel : awakeHonestLabel p c E rho u = rho.honest := by
    rw [pcsa_awakeHonestLabel_def]
    ext x
    simp only [Finset.mem_inter, Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    exact ⟨fun hx => hx.1.1, fun hx =>
      ⟨⟨hx, h.awake x hx _ hv.1 hv.2⟩, ⟨hx, h.awake x hx _ hge he⟩⟩⟩
  rw [hlabel]
  have hn : p.n = Fintype.card V :=
    h.base.cstar.seats_eq (ℓ := .base (.head u)) trivial
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hle := Finset.card_le_univ rho.honest
    omega
  have hcap : 4 * (Gen.V2.Duty.faulty rho).card ≤ p.n := h.quarterCap
  have hpos := p.nPos
  rw [pcsa_nQuorum_eq_qN, Gen.Pure.qN_def]
  omega

end AvailableChain.PCSA.Run
end
