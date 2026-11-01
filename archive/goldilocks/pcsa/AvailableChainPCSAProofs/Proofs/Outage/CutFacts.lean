module
public import AvailableChainPCSAProofs.Proofs.Outage.CutRun

public section

/-! The Clean facts at the cut `b₀` (pcsa34-r4.3 §5.5 steps 1–2), stage 1, as
one record: CI (i) on one label (`CleanInvariantClaim`), the locks below `S`
(`LeaseBelowRecordClaim`), the facts at the pending labels (`CutChain`), and
the clean-gate successor bridge (a HEAD of label `j + 1` extends an honest
result of label `j` with `d_j ≤ b₀`). The Outage assembly proves every field
from the Clean claims and the HEAD cone (`pcsa_cleanCutItems_of_cone`,
`pcsa_cleanConeItems`).
From a result `A = R_u(j₁)`: every later
honest result and HEAD in the prefix extends `A`, every honest ack and record
in the prefix is compatible with `A`. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

variable (p c) in
/-- [pcsa34-r4.3 §5.2.2, §5.2.3, §5.5 steps 1–2] The Clean facts of one run
at the cut `b₀`. -/
structure CutFacts (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ : Time) :
    Prop extends CutChain p c E rho b₀ where
  same : ∀ j : Slot, SA.gateTime p.toParams j ≤ b₀ → ∀ x ∈ rho.honest, ∀ y ∈ rho.honest,
    ∀ X Y, gateResultAt p c E rho x j = some (some X) →
      gateResultAt p c E rho y j = some (some Y) → Block.Compatible X Y
  rows : ∀ x ∈ rho.honest, ∀ t : Time, 0 ≤ t → t ≤ b₀ →
    ∀ ℓ ∈ (storeAt p c E rho x t).base.obligations,
      (storeAt p c E rho x t).base.now < ℓ.2.2 →
      Block.Preceq ℓ.1 (storeAt p c E rho x t).base.stableRecord
  bridge : ∀ (j : Slot) (u x : V) (A H : Block), SA.gateTime p.toParams j ≤ b₀ →
    u ∈ rho.honest → gateResultAt p c E rho u j = some (some A) →
    HonestHeadAt p c E rho x (j + 1) H → Block.Preceq A H

/-- [pcsa34-r4.3 §5.2.2, §5.5 steps 1–2] The Clean facts at the cut of every
clean stage-1 run. The Outage assembly builds them from the Clean claims and
the HEAD cone `CleanConeItems` (`pcsa_cleanConeItems`). -/
def CleanCutItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      CutFacts p c E rho b₀

theorem CleanCutItems_def (p : Params) : CleanCutItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
        CutFacts p c E rho b₀) := by
  delta CleanCutItems
  rfl

/-! ### Slot times -/

omit [DecidableEq V] [Fintype V] in
/-- Gate times order the labels. -/
theorem pcsa_gate_lt_slot {a b : Slot}
    (h : SA.gateTime p.toParams a < SA.gateTime p.toParams b) : a < b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 6 * p.Δ < 4 * p.Δ * (b : Int) + 6 * p.Δ at h
  by_contra hn
  have : (b : Int) ≤ a := by exact_mod_cast Nat.le_of_not_lt hn
  nlinarith

omit [DecidableEq V] [Fintype V] in
/-- The early time is at most the gate time of the same label. -/
theorem pcsa_early_le_gate (s : Slot) :
    SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith

omit [DecidableEq V] [Fintype V] in
/-- Gate times are not negative. -/
theorem pcsa_gate_nonneg (s : Slot) : 0 ≤ SA.gateTime p.toParams s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
  positivity

omit [DecidableEq V] [Fintype V] in
/-- The lock lifetime is more than `4Δ`. -/
theorem pcsa_lifetime_gt : 4 * p.Δ < SA.lifetime p.toParams := by
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  have hk : (2 : Int) ≤ (p.k : Int) := by exact_mod_cast p.kLarge
  have hL : SA.lifetime p.toParams = pcsaL p := rfl
  rw [hL, pcsaL_def]
  nlinarith

/-! ### Results and HEADs after `A` -/

omit [Fintype V] in
/-- An honest node has a gate result for every label whose gate is in the run. -/
theorem pcsa_gate_result_exists (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) {x : V} (hx : x ∈ rho.honest)
    {i : Slot} (hg : SA.gateTime p.toParams i ≤ rho.horizon) :
    ∃ r, gateResultAt p c E rho x i = some r := by
  have hs := h.valid.toScheduleWellFormed
  obtain ⟨k, hk⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_gate_public E h.delta i)
    (pcsa_gate_nonneg i) hg
  exact ⟨_, pcsa_gate_tick_result E rho hs hfr hx hk⟩

omit [Fintype V] in
/-- [§5.5 step 1] Every honest result of a later label in the prefix extends
`A = R_u(j₁)`. -/
theorem pcsa_cut_res {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest) {j₁ : Slot} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A)) {x : V} (hx : x ∈ rho.honest)
    {i : Slot} (hi : j₁ < i) (he : SA.earlyTime p.toParams i ≤ b₀) {r : Option Block}
    (hr : gateResultAt p c E rho x i = some r) : ∃ R, r = some R ∧ Block.Preceq A R := by
  cases r with
  | none => exact absurd hr (hK.nonempty i he x hx)
  | some R => exact ⟨R, rfl, hK.chain j₁ i u x A R hi he hu hx hA hr⟩

omit [Fintype V] in
/-- [§5.5 steps 1, 3] Every honest HEAD of a later label `r` with `v_r ≤ b₀`
extends `A` when `d_{j₁} ≤ b₀`: the bridge gives the HEADs of label `j₁ + 1`,
the vote-time HEAD cone the later labels. -/
theorem pcsa_cut_head {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest) {j₁ : Slot} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A))
    (hd : SA.gateTime p.toParams j₁ ≤ b₀) {z : V} {r : Slot} {H : Block}
    (hr : j₁ < r) (hv : SA.voteTime p.toParams r ≤ b₀)
    (hH : HonestHeadAt p c E rho z r H) : Block.Preceq A H := by
  have hB : ∀ y G, HonestHeadAt p c E rho y (j₁ + 1) G → Block.Preceq A G :=
    fun y G hG => hK.bridge j₁ u y A G hd hu hA hG
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hr) with hlt | heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact pcsa_voteCone_up (pcsa_cutChain_voteCone hK.toCutChain) hB n hv z H hH
  · rw [← heq] at hH
    exact hB z H hH

/-- [§5.5 step 3, CL4] Every honest ack of a label with `v_s ≤ b₀` is
compatible with `A`. -/
theorem pcsa_cut_ack {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ ΔF : Time}
    (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest) {j₁ : Slot} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A))
    (hd1 : SA.gateTime p.toParams (j₁ + 1) ≤ b₀) {y : V} {s : Slot} {X : Block}
    (hX : HonestAckAt p c E rho y s X) (hv : SA.voteTime p.toParams s ≤ b₀) :
    Block.Compatible X A := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  by_cases hsj : j₁ < s
  · obtain ⟨z, hz⟩ := pcsa_honest_ack_head E rho h hf hfr y s X hX
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl X)
      (pcsa_cut_head hK hu hA (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1) hsj hv hz)
  · have hsj' : s ≤ j₁ := Nat.le_of_not_lt hsj
    have hg : SA.gateTime p.toParams (s + 1) ≤ b₀ :=
      le_trans (pcsa_gate_mono (Nat.succ_le_succ hsj')) hd1
    have he : SA.earlyTime p.toParams (s + 1) ≤ b₀ := le_trans (pcsa_early_le_gate _) hg
    obtain ⟨r, hr⟩ := pcsa_gate_result_exists E rho h hfr hu (le_trans hg hC.cut.2)
    obtain ⟨R, rfl⟩ : ∃ R, r = some R := by
      cases r with
      | none => exact absurd hr (hK.nonempty _ he u hu)
      | some R => exact ⟨R, rfl⟩
    have hXR := (hK.dis s y X hX).2 he u hu R hr
    rcases Nat.lt_or_eq_of_le hsj' with hlt | heq
    · rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with hlt' | heq'
      · have hRA := hK.chain (s + 1) j₁ u u R A hlt'
          (le_trans (pcsa_early_le_gate _) (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1))
          hu hu hr hA
        exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hXR hRA)
          (Gen.Pure.block_preceq_refl A)
      · have heq'' : s + 1 = j₁ := heq'
        rw [heq'', hA] at hr
        have hRA : R = A := (Option.some.inj (Option.some.inj hr)).symm
        rw [← hRA]
        exact Gen.Pure.block_compatible_of_common hXR (Gen.Pure.block_preceq_refl R)
    · rw [heq] at hr
      obtain ⟨R', hR', hAR⟩ := pcsa_cut_res hK hu hA hu (Nat.lt_succ_self j₁)
        (by rw [← heq]; exact he) hr
      cases hR'
      exact Gen.Pure.block_compatible_of_common hXR hAR

/-! ### Records and locks at the cut -/

omit [Fintype V] in
/-- [§5.2.2 (v)] The record of an honest node before index `K` (events up to
`b₀`) is compatible with `A`. -/
theorem pcsa_cut_record {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (hK : CutFacts p c E rho b₀)
    {u : V} (hu : u ∈ rho.honest) {j₁ : Slot} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A))
    (hd1 : SA.gateTime p.toParams (j₁ + 1) ≤ b₀) {x : V} (hx : x ∈ rho.honest) {K : Nat}
    (hT : ∀ k < K, ∀ e, rho.events[k]? = some e → e.time ≤ b₀) :
    Block.Compatible (V2.D.Run.stateBefore E rho K x).st.base.stableRecord A := by
  rcases pcsa_record_origin E rho h hfr x hx K with hg | ⟨i, k, hk, he, hR⟩
  · rw [hg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq A)
      (Gen.Pure.block_preceq_refl A)
  · have hdi : SA.gateTime p.toParams i ≤ b₀ := hT k hk _ he
    rcases lt_trichotomy i j₁ with hlt | heq | hgt
    · exact Gen.Pure.block_compatible_of_common
        (hK.chain i j₁ x u _ A hlt (le_trans (pcsa_early_le_gate _)
          (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1)) hx hu hR hA)
        (Gen.Pure.block_preceq_refl A)
    · rw [heq] at hR
      exact hK.same j₁ (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1) x hx u hu _ A hR hA
    · obtain ⟨R, hR', hAR⟩ := pcsa_cut_res hK hu hA hx hgt
        (le_trans (pcsa_early_le_gate _) hdi) hR
      cases hR'
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) hAR

omit [Fintype V] in
/-- The record of an honest node before index `K` is below its result of a
label whose gate is after every earlier event of the node. -/
theorem pcsa_cut_record_below {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)}
    {b₀ : Time} (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho)
    (hK : CutFacts p c E rho b₀) {x : V} (hx : x ∈ rho.honest) {K : Nat} {i' : Slot}
    {R : Block} (hT : ∀ k < K, ∀ e, rho.events[k]? = some e → e.node = x →
      e.time < SA.gateTime p.toParams i')
    (he : SA.earlyTime p.toParams i' ≤ b₀) (hR : gateResultAt p c E rho x i' = some (some R)) :
    Block.Preceq (V2.D.Run.stateBefore E rho K x).st.base.stableRecord R := by
  rcases pcsa_record_origin E rho h hfr x hx K with hg | ⟨i, k, hk, hek, hRi⟩
  · rw [hg]
    exact Gen.Pure.block_genesis_preceq R
  · exact hK.chain i i' x x _ R (pcsa_gate_lt_slot (hT k hk _ hek rfl)) he hx hx hRi hR

omit [Fintype V] in
/-- [§5.2.2 (iv)] Every lock row of an honest node at a time of the prefix is
below its record. -/
theorem pcsa_cut_rows {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)} {b₀ : Time}
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (hK : CutFacts p c E rho b₀)
    {x : V} (hx : x ∈ rho.honest) {t : Time} (h0 : 0 ≤ t) (ht : t ≤ b₀) :
    ∀ row ∈ (storeAt p c E rho x t).base.obligations,
      Block.Preceq row.1 (storeAt p c E rho x t).base.stableRecord := by
  have hs := h.valid.toScheduleWellFormed
  intro row hr
  refine hK.rows x hx t h0 ht row hr ?_
  rw [pcsa_storeAt_index E rho hs] at hr ⊢
  exact pcsa_rows_live E rho h hfr x hx (le_of_lt (lt_of_le_of_lt (by
    have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
    linarith) (pcsa_lifetime_gt (p := p)))) _ row hr

end AvailableChain.PCSA.Run
end
