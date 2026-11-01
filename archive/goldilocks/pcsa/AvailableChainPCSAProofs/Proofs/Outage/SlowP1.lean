module
public import AvailableChainPCSAProofs.Proofs.Outage.Healthy

public section

/-! Slow P1 (pcsa34-r4.3 §5.5). `X ⪯ available_u(T) = floor(S_u(T), pc_u(T))`
splits into the PC case (ARM-healthy, 5.4.2, with `T + 3Δ ≤ T + 4(k−1)Δ ≤ b₀`)
and the S case. The S case needs, in `[b₀, b₁)`, `S_w ⪰ S_u(T)` and every
held PC compatible with `S_u(T)` (steps 1–4); the floor (step 5) is proved
here. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

variable (p c) in
omit [Fintype V] in
/-- [pcsa34-r4.3 §5.5 S case, steps 1–4] Every honest `S` in `[b₀, b₁)` is
`⪰ S_u(T)` and every PC held there is compatible with `S_u(T)`. -/
def SlowStableHolds (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (T b₀ b₁ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ w ∈ rho.honest, ∀ t : Time, b₀ ≤ t → t < b₁ →
    Block.Preceq (storeAt p c E rho u T).base.stableRecord
        (storeAt p c E rho w t).base.stableRecord ∧
      ∀ d ∈ (storeAt p c E rho w t).pcs,
        Block.Compatible d.target (storeAt p c E rho u T).base.stableRecord

variable (p c) in
omit [Fintype V] in
theorem SlowStableHolds_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (T b₀ b₁ : Time) : SlowStableHolds p c E rho T b₀ b₁ =
      (∀ u ∈ rho.honest, ∀ w ∈ rho.honest, ∀ t : Time, b₀ ≤ t → t < b₁ →
        Block.Preceq (storeAt p c E rho u T).base.stableRecord
            (storeAt p c E rho w t).base.stableRecord ∧
          ∀ d ∈ (storeAt p c E rho w t).pcs,
            Block.Compatible d.target (storeAt p c E rho u T).base.stableRecord) := by
  delta SlowStableHolds
  rfl

/-- [pcsa34-r4.3 §5.5 S case, steps 1–4] `SlowStableHolds` in every
OUTAGE stage-1 run with `a < ⌈n/2⌉`. -/
def SlowStableItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
    Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    SlowStableHolds p c E rho T b₀ b₁

theorem SlowStableItems_def (p : Params) : SlowStableItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (T b₀ b₁ ΔF : Time),
      Outage₂ p c E rho T b₀ b₁ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      SlowStableHolds p c E rho T b₀ b₁) := by
  delta SlowStableItems
  rfl

/-! ### The floor -/

/-- The PC target of a store is a held PC target. -/
theorem pcsa_pcTarget_held (st : State p.n) (b : Block) (h : pcTarget? st = some b) :
    ∃ d ∈ st.pcs, d.target = b := by
  change (latestPC st).map PC.target = some b at h
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨d, bestPC_mem _ d hd, rfl⟩

/-- [pcsa34-r4.3 §5.5 step 5] If `A ⪯ S` and every held PC is compatible
with `A`, then `A` is below the available read. -/
theorem pcsa_floor_ge (st : State p.n) (A : Block)
    (hS : Block.Preceq A st.base.stableRecord)
    (hpc : ∀ d ∈ st.pcs, Block.Compatible d.target A) :
    Block.Preceq A (confirmed st) := by
  change Block.Preceq A (match pcTarget? st with
    | some b => if Block.preceq b st.base.stableRecord then st.base.stableRecord else b
    | none => st.base.stableRecord)
  cases hb : pcTarget? st with
  | none => exact hS
  | some b =>
    dsimp only
    by_cases hbs : Block.preceq b st.base.stableRecord = true
    · rw [ite_eq_left hbs]
      exact hS
    · rw [ite_eq_right hbs]
      obtain ⟨d, hd, rfl⟩ := pcsa_pcTarget_held st b hb
      rcases Bool.or_eq_true_iff.mp (hpc d hd) with h | h
      · exact absurd (Gen.Pure.block_preceq_trans h hS) hbs
      · exact h

/-! ### Slow P1 -/

/-- The available read at `T` is the PC target (not below `S`) or `S`. -/
theorem pcsa_confirmed_cases (st : State p.n) :
    (∃ d, latestPC st = some d ∧ confirmed st = d.target) ∨
      confirmed st = st.base.stableRecord := by
  change (∃ d, latestPC st = some d ∧ (match pcTarget? st with
    | some b => if Block.preceq b st.base.stableRecord then st.base.stableRecord else b
    | none => st.base.stableRecord) = d.target) ∨ (match pcTarget? st with
    | some b => if Block.preceq b st.base.stableRecord then st.base.stableRecord else b
    | none => st.base.stableRecord) = st.base.stableRecord
  cases hl : latestPC st with
  | none =>
    right
    have hp : pcTarget? st = none := by
      change (latestPC st).map PC.target = none
      rw [hl]
      rfl
    rw [hp]
  | some d =>
    have hp : pcTarget? st = some d.target := by
      change (latestPC st).map PC.target = some d.target
      rw [hl]
      rfl
    rw [hp]
    dsimp only
    by_cases hbs : Block.preceq d.target st.base.stableRecord = true
    · right
      rw [ite_eq_left hbs]
    · left
      exact ⟨d, rfl, ite_eq_right hbs⟩

/-- [pcsa34-r4.3 §5.5] Slow P1, given the Clean-lane ARM items and the S
case facts. -/
theorem pcsa_slowP1_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T b₀ b₁ ΔF : Time} (hO : Outage₂ p c E rho T b₀ b₁ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho)
    (hrelay : CleanHeldPCRelay p c E rho b₀) (hacks : CleanArmAcks p c E rho b₀)
    (hS : SlowStableHolds p c E rho T b₀ b₁)
    (u : V) (hu : u ∈ rho.honest) (X : Block)
    (hX : Block.Preceq X (confirmed (storeAt p c E rho u T)))
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hbt : b₀ ≤ t) (htb : t < b₁) :
    Block.Preceq X (confirmed (storeAt p c E rho w t)) := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hk : (2 : Int) ≤ (p.k : Int) := by exact_mod_cast p.kLarge
  have hT3 : T + 3 * E.Δ ≤ b₀ := by
    have hl := hO.lag
    rw [hO.pre.base.delta]
    nlinarith
  rcases pcsa_confirmed_cases (storeAt p c E rho u T) with ⟨d, hd, he⟩ | he
  · rw [he] at hX
    have hpc := pcsa_armHealthy_pc E rho hO.pre hf hfr hO.order.1 hT3 hrelay hacks u hu d
      (bestPC_mem _ d hd) w hw t hbt
    exact Gen.Pure.block_preceq_trans hX
      (Gen.Pure.block_preceq_trans hpc (strong_preceq_confirmed _))
  · rw [he] at hX
    obtain ⟨h1, h2⟩ := hS u hu w hw t hbt htb
    exact Gen.Pure.block_preceq_trans hX (pcsa_floor_ge _ _ h1 h2)

end AvailableChain.PCSA.Run
end
