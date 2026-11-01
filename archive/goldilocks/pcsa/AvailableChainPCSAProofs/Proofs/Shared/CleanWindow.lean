module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy

public section

/-! The delivery window of the clean induction (pcsa34-r4.3 §5.2.2, §5.6.1 step 4).
`StrictFrom E rho T₀ cut` is strict non-row delivery from `T₀`: an object sent at
`t ≥ T₀` reaches every honest node before `t + Δ`, and an object accepted at an
earlier time before `T₀ + Δ`. `CleanWindow` adds the execution, the cut and the
label bound `a < h_j` for the labels `j ≥ j₀`. CLEAN(b₀) gives the window with
`T₀ = 0`, `j₀ = 0`; the RECOVERY components give it with `T₀ = t_GST` from a
label `j₀` with `t_GST ≤ t_{j₀}`. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Strict non-row delivery from `T₀` up to `cut`: the deadline `dl t` is
`t + Δ` from `T₀` and at most `max t T₀ + Δ` before. -/
structure StrictFrom (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T₀ cut : Time) :
    Prop where
  deadline : ∃ dl : Time → Time, Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow dl cut ∧
    (∀ t, T₀ ≤ t → dl t = t + E.Δ) ∧ (∀ t, t < dl t) ∧ (∀ t, dl t ≤ max t T₀ + E.Δ)

/-- Non-row objects have the base delay. -/
theorem pcsa_isNonRow_delay (o : Obj p) (Δ ΔF : Time) (ho : IsNonRow o) :
    pcsaDelay p Δ ΔF o = Δ := by
  rw [pcsaDelay_def]
  cases he : o.payload <;> simp only [pcsa_IsNonRow_def, he] at ho ⊢

/-- An object that is not a row is `IsNonRow`. -/
theorem pcsa_isNonRow_of_ne (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) : IsNonRow o := by
  rw [pcsa_IsNonRow_def]
  cases he : o.payload with
  | row body => exact (hn body he).elim
  | _ => trivial

/-- Healthy prefix delivery gives strict delivery from every `T₀`. -/
theorem pcsa_strictFrom_of_healthy (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut) (T₀ : Time) :
    StrictFrom E rho T₀ cut := by
  refine ⟨⟨fun t => t + E.Δ, Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho cut hD
    IsNonRow E.Δ (fun o ho => pcsa_isNonRow_delay o E.Δ ΔF ho), fun _ _ => rfl,
    fun t => lt_add_of_pos_right t E.Δ_pos, fun t => ?_⟩⟩
  exact Int.add_le_add_right (le_max_left t T₀) E.Δ

/-- Partial synchrony gives strict delivery from `t_GST` to the horizon. -/
theorem pcsa_strictFrom_of_sync (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {ΔF : Time} (hD : Gen.V2.Duty.PartialSynchronyBy E rho (pcsaDelay p E.Δ ΔF)) :
    StrictFrom E rho E.t_GST rho.horizon := by
  refine ⟨⟨fun t => max t E.t_GST + E.Δ, Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E
    rho hD IsNonRow E.Δ (fun o ho => pcsa_isNonRow_delay o E.Δ ΔF ho), fun t ht => ?_,
    fun t => ?_, fun _ => le_refl _⟩⟩
  · change max t E.t_GST + E.Δ = t + E.Δ
    rw [max_eq_left ht]
  · change t < max t E.t_GST + E.Δ
    exact lt_of_le_of_lt (le_max_left t E.t_GST) (lt_add_of_pos_right _ E.Δ_pos)

/-- Delivery within `max t T₀ + Δ` (the formation premise (F1) shape, with
`T₀ = z_{s−1}`) is strict delivery from `T₀`. -/
theorem pcsa_strictFrom_of_within (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T₀ cut : Time}
    (hW : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow (fun t => max t T₀ + E.Δ) cut) :
    StrictFrom E rho T₀ cut := by
  refine ⟨⟨fun t => max t T₀ + E.Δ, hW, fun t ht => ?_, fun t => ?_, fun _ => le_refl _⟩⟩
  · change max t T₀ + E.Δ = t + E.Δ
    rw [max_eq_left ht]
  · change t < max t T₀ + E.Δ
    exact lt_of_le_of_lt (le_max_left t T₀) (lt_add_of_pos_right _ E.Δ_pos)

/-- Strict delivery to a cut gives it to every earlier cut. -/
theorem pcsa_strictFrom_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T₀ cut cut' : Time} (hD : StrictFrom E rho T₀ cut) (hc : cut' ≤ cut) :
    StrictFrom E rho T₀ cut' := by
  obtain ⟨dl, hW, hexact, hlt, hle⟩ := hD.deadline
  refine ⟨⟨dl, ⟨?_, ?_⟩, hexact, hlt, hle⟩⟩
  · intro v hv o ho t he w hw hcut hx
    exact hW.broadcast v hv o ho t he w hw (hcut.trans hc) hx
  · intro v hv i o ho t ha w hw hp hcut hx
    exact hW.relay v hv i o ho t ha w hw hp (hcut.trans hc) hx

/-- A floor below `t_s` is below `t_{s'}` for every `s' ≥ s`. -/
theorem pcsa_floor_le {T₀ : Time} {s s' : Slot} (hT : T₀ ≤ SA.proposalTime p.toParams s)
    (hs : s ≤ s') : T₀ ≤ SA.proposalTime p.toParams s' := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s' : Int)
  have hd := p.deltaPos
  have hle : (s : Int) ≤ (s' : Int) := by exact_mod_cast hs
  nlinarith

/-- A floor below `t_s` is below `v_s`. -/
theorem pcsa_floor_vote {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.proposalTime p.toParams s) :
    T₀ ≤ SA.voteTime p.toParams s := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
  linarith [p.deltaPos]

/-- A floor below `t_s` is below `e_s`. -/
theorem pcsa_floor_early {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.proposalTime p.toParams s) :
    T₀ ≤ SA.earlyTime p.toParams s := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
  linarith [p.deltaPos]

/-- A floor below `t_s` is below `z_s`. -/
theorem pcsa_floor_freeze {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.proposalTime p.toParams s) :
    T₀ ≤ SA.freezeTime p.toParams s := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
  linarith [p.deltaPos]

/-- A floor below `t_s` is below `d_s`. -/
theorem pcsa_floor_gate {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.proposalTime p.toParams s) :
    T₀ ≤ SA.gateTime p.toParams s := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith [p.deltaPos]

/-- Every proposal time is nonnegative: the floor `0` of a clean run is below it. -/
theorem pcsa_zero_le_proposal (s : Slot) : (0 : Time) ≤ SA.proposalTime p.toParams s := by
  have hd := p.deltaPos
  change (0 : Time) ≤ 4 * p.Δ * (s : Int)
  positivity

/-- A floor below `z_s` is below `t_{s+1}`. -/
theorem pcsa_floor_freeze_next {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.freezeTime p.toParams s) :
    T₀ ≤ SA.proposalTime p.toParams (s + 1) := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)
  push_cast
  linarith [p.deltaPos]

/-- A floor below `e_s` is below `t_{s+1}`. -/
theorem pcsa_floor_early_next {T₀ : Time} {s : Slot} (hT : T₀ ≤ SA.earlyTime p.toParams s) :
    T₀ ≤ SA.proposalTime p.toParams (s + 1) := by
  apply hT.trans
  change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)
  push_cast
  linarith [p.deltaPos]

/-- The window of the clean induction from label `j₀`: the execution, the cut,
strict delivery from `T₀ ≤ t_{j₀}`, and `a < h_j` at every label `j ≥ j₀` with
`e_j ≤ b₀`. -/
structure CleanWindow [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (j₀ : Slot) (T₀ b₀ : Time) : Prop where
  base : Base₂ p c E rho
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon
  strict : StrictFrom E rho T₀ b₀
  floor : T₀ ≤ SA.proposalTime p.toParams j₀
  labels : ∀ j : Slot, j₀ ≤ j → SA.earlyTime p.toParams j ≤ b₀ →
    (Gen.V2.Duty.faulty rho).card < (awakeHonestLabel p c E rho j).card

variable [Fintype V]

/-- CLEAN(b₀) gives the window from label `0` with `T₀ = 0`. -/
theorem pcsa_cleanWindow_of_clean (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {cut ΔF : Time} (h : Clean₂ p c E rho cut ΔF) : CleanWindow E rho 0 0 cut := by
  refine ⟨h.base, h.cut, pcsa_strictFrom_of_healthy E rho h.healthy 0, ?_,
    fun j _ hj => h.labels j hj⟩
  change (0 : Time) ≤ 4 * p.Δ * ((0 : Nat) : Int)
  simp

/-- A later label of the window is in the window. -/
theorem pcsa_cleanWindow_floor (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {j₀ : Slot} {T₀ cut : Time} (h : CleanWindow E rho j₀ T₀ cut) (s : Slot) (hs : j₀ ≤ s) :
    T₀ ≤ SA.proposalTime p.toParams s := by
  apply h.floor.trans
  change 4 * p.Δ * (j₀ : Int) ≤ 4 * p.Δ * (s : Int)
  have hd := p.deltaPos
  have hle : (j₀ : Int) ≤ (s : Int) := by exact_mod_cast hs
  nlinarith

/-- Synchrony after `t_GST`, full participation and `a ≤ ⌊n/4⌋` (the RECOVERY
components) give the window from every label `j₀` with `t_GST ≤ t_{j₀}`. -/
theorem pcsa_cleanWindow_of_sync (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {ΔF : Time} (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (pcsaDelay p E.Δ ΔF))
    (hawake : Gen.V2.Duty.FullParticipation E rho E.t_GST) (hcap : QuarterCap p c rho)
    (j₀ : Slot) (cut : Time)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams j₀) (hcut : 0 ≤ cut ∧ cut ≤ rho.horizon) :
    CleanWindow E rho j₀ E.t_GST cut := by
  refine ⟨hb, hcut, pcsa_strictFrom_mono E rho (pcsa_strictFrom_of_sync E rho hsync) hcut.2,
    hgst, fun j hj he => ?_⟩
  have hd := p.deltaPos
  have hj' : (j₀ : Int) ≤ (j : Int) := by exact_mod_cast hj
  have hpj : E.t_GST ≤ SA.proposalTime p.toParams j := by
    apply hgst.trans
    change 4 * p.Δ * (j₀ : Int) ≤ 4 * p.Δ * (j : Int)
    nlinarith
  have hv : E.t_GST ≤ SA.voteTime p.toParams j ∧ SA.voteTime p.toParams j ≤ rho.horizon := by
    change E.t_GST ≤ 4 * p.Δ * (j : Int) at hpj
    change 4 * p.Δ * (j : Int) + 2 * p.Δ ≤ cut at he
    have := hcut.2
    change E.t_GST ≤ 4 * p.Δ * (j : Int) + p.Δ ∧ 4 * p.Δ * (j : Int) + p.Δ ≤ rho.horizon
    constructor <;> linarith
  have he' : E.t_GST ≤ SA.earlyTime p.toParams j ∧
      SA.earlyTime p.toParams j ≤ rho.horizon := by
    change E.t_GST ≤ 4 * p.Δ * (j : Int) at hpj
    refine ⟨?_, he.trans hcut.2⟩
    change E.t_GST ≤ 4 * p.Δ * (j : Int) + 2 * p.Δ
    linarith
  have hlabel : awakeHonestLabel p c E rho j = rho.honest := by
    rw [pcsa_awakeHonestLabel_def]
    ext x
    simp only [Finset.mem_inter, Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    exact ⟨fun hx => hx.1.1, fun hx =>
      ⟨⟨hx, hawake x hx _ hv.1 hv.2⟩, ⟨hx, hawake x hx _ he'.1 he'.2⟩⟩⟩
  rw [hlabel]
  have hn : p.n = Fintype.card V := hb.cstar.seats_eq (ℓ := .base (.head j)) trivial
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hle := Finset.card_le_univ rho.honest
    omega
  have hcap : 4 * (Gen.V2.Duty.faulty rho).card ≤ p.n := hcap
  have hpos := p.nPos
  omega

end AvailableChain.PCSA.Run
end
