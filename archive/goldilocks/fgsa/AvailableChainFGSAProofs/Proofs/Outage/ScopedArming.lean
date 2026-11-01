module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedClose

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The Clean boundary supplies facts only at the finite healthy cut.
Saved rows use the receiver's actual awake interval and local epoch. -/
structure OutageCleanCutInputs [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (b₀ : Time) : Prop where
  state : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i
  history : CleanHist p c E rho (timeIdx rho b₀)
  output : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
    ∃ C, gateResultAt p c E rho j = some (some C) ∧
      Block.Preceq C (S_at p c E rho (j + 1) y)
  transfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
    joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
    SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
    vHead p c E rho z s = some H → Block.Preceq C H
  saved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
    SA.gateTime p.toParams q ≤ b₀ →
    AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
    RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
    (B = .genesis ∨ ∃ r C, r < q ∧
      (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
    Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
      ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
        some (some C) ∧ Block.Preceq B C

/-- Each outage lag gives a positive healthy cut, even when T is zero. -/
theorem outage_cut_pos [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : 0 < b₀ := by
  have hT := h.order.1
  have hlag := h.lag
  have hd := p.deltaPos
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  cases fast with
  | false =>
    change T + ((4 * (p.k : Time) - 1) * p.Δ - 3 * p.Δ) ≤ b₀ at hlag
    nlinarith
  | true =>
    change T + 4 * p.Δ ≤ b₀ at hlag
    linarith

/-- Select the actual scoped arming certificate. The empty covered set has
no receiver demand; the joined pending HEAD bounds still use Clean history. -/
theorem outage_scoped_arming [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) (hClean : OutageCleanCutInputs (p := p) (c := c) E rho b₀)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho fast T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  classical
  have hprov := outage_joined_provenance h.pre.base.valid h.pre.base.delta
  cases fast with
  | true =>
    exact fast_arming_scoped_on h hf hsrc htsrc hClean.state hClean.history
      hClean.transfer hprov hread hne
  | false =>
    by_cases he : coveredNodes p E rho false b₀ = ∅
    · exact outage_empty_covered_certificate h hf hsrc htsrc hClean.state hClean.history
        hClean.transfer hprov hread hne he
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr he
      exact slow_arming_scoped_on h hf hsrc htsrc hClean.state hClean.history
        hClean.transfer hClean.saved hread hne hy

end AvailableChain.FGSA.Run
end
