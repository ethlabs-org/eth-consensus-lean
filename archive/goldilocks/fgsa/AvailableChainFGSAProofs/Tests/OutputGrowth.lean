module
public import AvailableChainFGSAProofs.Proofs.Outage.Growth
-- shake: keep (boundary and body examples)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims
-- shake: keep (frozen GST claim example)

public section

namespace AvailableChain.FGSA.Run.Tests.OutputGrowth

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- Time zero is a valid inclusive trigger, including a sleeping reader.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) :
    (V2.D.Run.stateBefore E rho (timeIdx rho 0) x).st.base.now ≤ 0 :=
  fgsa_timeIdx_now_le E rho hs 0 le_rfl x

-- A terminal read needs no event after its index.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (x : V)
    (hend : timeIdx rho rho.horizon = rho.events.length) :
    (V2.D.Run.stateBefore E rho rho.events.length x).st.base.now ≤ rho.horizon := by
  simpa only [hend] using fgsa_timeIdx_now_le E rho hs rho.horizon hs.horizon_nonneg x

-- The first selected slot can be 1 at the minimum window G = 4Δ.
example (s : Slot) (hs : 0 < s)
    (hupper : SA.proposalTime p.toParams s ≤ 4 * p.Δ) : s = 1 := by
  have hpos : 0 < 4 * p.Δ := mul_pos (by decide) p.deltaPos
  change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ at hupper
  have hle : (s : Int) ≤ 1 := (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_one] using hupper)
  exact Nat.le_antisymm (by exact_mod_cast hle) hs

example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (B : Block) (hslot : B.slot = 1)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) (x : V) :
    ¬ Block.Preceq B (V2.D.outputAt E rho g x 0) := by
  apply fgsa_output_noFuture_of_slot E rho hs le_rfl (s := 1) ?_ hslot.ge g hg x
  change 0 < 4 * p.Δ * (1 : Int)
  simpa only [mul_one] using mul_pos (by decide : (0 : Int) < 4) p.deltaPos

-- Upper endpoints stay inclusive: τ_s = t+G and d_s = D = horizon.
example (t G horizon : Time) (s : Slot)
    (hτ : SA.proposalTime p.toParams s = t + G)
    (hD : t + G + 6 * p.Δ = horizon) :
    SA.gateTime p.toParams s = horizon := by
  change SA.proposalTime p.toParams s + 6 * p.Δ = horizon
  rw [hτ, hD]

example : SA.proposalTime p.toParams 1 = 4 * p.Δ ∧
    SA.gateTime p.toParams 1 = (0 : Time) + 4 * p.Δ + 6 * p.Δ := by
  constructor <;> simp [SA.proposalTime, SA.gateTime,
    GridCO.proposalTime, GridCO.gateTime, SA.Params.engine]

-- Same-time deliveries at a healing gate stay in the suffix.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (a : Time) :
    HealSuffix p c rho a (timeIdx rho a) := fgsa_healSuffix_timeIdx E rho hs le_rfl

-- The actual application value survives the proposal payload adapter.
example (H : NamedProposal p.n) (s : Slot) (raw sup : List (HeadWire p.n))
    (rows : List (RowWire p.n))
    (a : Nat) :
    withApp p a (.proposal (namedProposal p H s 0 raw sup rows)) =
      .proposal (namedProposal p H s a raw sup rows) := rfl

-- ABSTRACT regression: this is not a reachable FGSA execution. Both
-- outputs already equal B at t and D. Monotonicity and inclusion hold, but
-- strict growth fails when the no-future pair is removed.
example (B : Block) :
    let O : Bool → Unit → Time → Block := fun _ _ _ => B
    (∀ g x, Block.Preceq (O g x 0) (O g x 1)) ∧
    (∀ g x, Block.Preceq B (O g x 1)) ∧
    (0 : Time) < 1 ∧
    ¬ (∀ g x, Block.Prec (O g x 0) B) := by
  dsimp only
  refine ⟨fun _ _ => Gen.Pure.block_preceq_refl B,
    fun _ _ => Gen.Pure.block_preceq_refl B, by decide, ?_⟩
  intro h
  simpa only [Block.Prec, Block.prec, decide_true, Bool.not_true, Bool.false_and,
    Bool.false_eq_true] using h true ()


-- The unfolded body matches AvailableGrowthConcl with no added public premise.
example [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hcompatible : ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u))
    (hrec : AwakeProposerRecurrenceFrom p c E rho 0 G)
    (hgap : 4 * p.Δ ≤ G) (t : Time) (ht : 0 ≤ t)
    (hhor : t + G + 6 * p.Δ ≤ rho.horizon) :
    AvailableGrowthConcl p c E rho t (t + G + 6 * p.Δ) := by
  exact clean_growth_body E rho G ΔF hset hcompatible hinclusion hrec hgap t ht hhor

-- The conditional theorem has the exact frozen GST claim type.
example (p : Params) (hH : HTimeClaim p) : AvailableGrowthGSTClaim p :=
  fgsa_availableGrowthGST hH

end AvailableChain.FGSA.Run.Tests.OutputGrowth
end
