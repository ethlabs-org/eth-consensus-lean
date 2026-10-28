module
public import ConsensusShape.Problem
public import ConsensusModelProofs.Canonical
public import ConsensusModelProofs.Lift
public import Mathlib.Tactic
@[expose] public section
namespace Consensus.Shape
open Model Run

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

theorem readyAbove_nonempty (p : EnvPoint V) {θ : ℚ} {c t : Time}
    (hθ : 0 ≤ θ) (h : p.ReadyAbove θ c t) : (p.readyAt c t).Nonempty := by
  classical
  by_contra hn
  have hz : (p.readyAt c t).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  unfold EnvPoint.ReadyAbove at h
  rw [hz] at h
  have : 0 ≤ θ * (0 + p.faulty.card : ℚ) := mul_nonneg hθ (by positivity)
  exact (not_lt_of_ge this) h

/-- Assignment coverage: the scheduler preserves the complete environment
point, and every slot with a ready validator receives a ready proposer. -/
theorem canonical_coverage (F : Family) (p : EnvPoint V) (hp : p.WellFormed) (c : Time) :
    ∃ r : Model.Run (compiled F) p.env,
      r.point = p ∧ r.ExecutionValid ∧ r.PartialSynchrony ∧
      (∀ t, r.HealthyPrefixDelivery t) ∧ ¬ r.HashCollision ∧
      (∀ s, (p.readyAt c ((protoOf F p.env).proposalTime s)).Nonempty → ReadyProposer r c s) := by
  classical
  let choose : Slot → V := fun s =>
    if h : (p.readyAt c ((protoOf F p.env).proposalTime s)).Nonempty then h.choose
    else Classical.choice inferInstance
  let holder : (ℓ : (Model.protoOf (compiled F) p.env).Label) →
      Fin ((Model.protoOf (compiled F) p.env).seats ℓ) ↪ V := fun ℓ =>
    match ℓ with
    | .inl _ => (Fintype.equivFin V).symm.toEmbedding
    | .inr s => ⟨fun _ => choose s, fun a b _ => by
        apply Fin.ext
        have ha := a.isLt
        have hb := b.isLt
        change a.val < min 1 (Fintype.card V) at ha
        change b.val < min 1 (Fintype.card V) at hb
        omega⟩
  let hash : Header → Nat := fun h => Encodable.encode h + 1
  obtain ⟨relay, es, hv, hs, hh⟩ := Model.canonical_run (compiled F) V p.env
    p.honest p.horizon hp holder p.submit hash
  let r := Model.mkRun (F := compiled F) (E := p.env)
    p.honest p.horizon holder p.submit relay hash es
  refine ⟨r, ?_, hv, hs, hh, ?_, ?_⟩
  · cases p; rfl
  · apply Model.Run.not_hashCollision_of_injective
    exact ⟨fun _ _ h => Encodable.encode_injective (Nat.add_right_cancel h), fun _ => Nat.succ_ne_zero _⟩
  · intro s h
    have hc : choose s ∈ p.readyAt c ((protoOf F p.env).proposalTime s) := by
      simp only [choose, dif_pos h]
      exact h.choose_spec
    have hc' : p.Ready c (choose s) ((protoOf F p.env).proposalTime s) :=
      (Finset.mem_filter.mp hc).2
    exact hc'

/-- Arithmetic recurrence for a positive gap and a nonnegative start. -/
theorem recurrence_of_ready (F : Family) {E : Env V} (r : Model.Run (compiled F) E)
    (c start : Time) (k : Nat) (hs : 0 ≤ start) (hk : 1 ≤ k)
    (hr : ∀ s, start ≤ (protoOf F E).proposalTime s →
      (protoOf F E).proposalTime s ≤ r.horizon → ReadyProposer r c s) :
    Recurrence r c start k := by
  intro t ht hh
  let L := (protoOf F E).slotLen
  have hL : 0 < L := (protoOf F E).slotLen_pos
  have hq : 0 ≤ t / L + 1 := by
    have := Int.ediv_nonneg (hs.trans ht) hL.le
    simp only [Time] at *; omega
  let s := (t / L + 1).toNat
  have hlo : t < (protoOf F E).proposalTime s := by
    change t < (s : Int) * L
    dsimp [s]; rw [Int.toNat_of_nonneg hq]
    have := Int.emod_lt_of_pos t hL
    have := Int.mul_ediv_add_emod t L
    nlinarith
  have hhi : (protoOf F E).proposalTime s ≤ t + (k : Time) * L := by
    change (s : Int) * L ≤ _
    dsimp [s]; rw [Int.toNat_of_nonneg hq]
    have := Int.emod_nonneg t hL.ne'
    have := Int.mul_ediv_add_emod t L
    have hk' : (1 : Int) ≤ k := by exact_mod_cast hk
    nlinarith
  exact ⟨s, hlo, hhi, hr s (ht.trans hlo.le) (hhi.trans hh)⟩

/-- Coverage only ranges over physically meaningful starts and positive
recurrence gaps. These domain guards do not enter any claim premise. -/
def CoverageDomain {V : Type} (q : System.ClaimKey) (p : EnvPoint V) : Prop :=
  match q with
  | .live k => 1 ≤ k
  | .recovery k | .finality k => 0 ≤ p.env.gst ∧ 1 ≤ k
  | _ => True

theorem exec_conservative (F : Family) (A : Assumptions) (hA : A.WellFormed)
    (C : Constants) (q : System.ClaimKey) (p : EnvPoint V) (hp : p.WellFormed)
    (hd : CoverageDomain q p) (he : System.EnvAssumption A (bounds C) q p) :
    ∃ r : (Model.sysOf (compiled F) V).Run,
      ((Model.sysOf (compiled F) V).trace r).point = p ∧
      (Model.sysOf (compiled F) V).Valid r ∧
      (Model.sysOf (compiled F) V).Exec (profile A) q r ∧
      ¬ (Model.sysOf (compiled F) V).Excuse r ∧ r.2.PartialSynchrony ∧
      (∀ s, (r.2.point.readyAt ((A.catchUp : Time) * r.1.Δ)
        ((protoOf F r.1).proposalTime s)).Nonempty →
        ReadyProposer r.2 ((A.catchUp : Time) * r.1.Δ) s) := by
  obtain ⟨r, hr, hv, hs, hh, hn, ready⟩ := canonical_coverage F p hp ((A.catchUp : Time) * p.env.Δ)
  refine ⟨⟨p.env, r⟩, hr, hv, ?_, hn, hs, ?_⟩
  swap
  · simpa only [hr] using ready
  have recur (start : Time) (k : Nat) (hstart : 0 ≤ start) (hk : 1 ≤ k)
      (θ : ℚ) (hθ : 0 ≤ θ)
      (hpart : ∀ t, start ≤ t → t ≤ p.horizon → p.ReadyAbove θ ((A.catchUp : Time) * p.env.Δ) t) :
      Recurrence r ((A.catchUp : Time) * p.env.Δ) start k := by
    apply recurrence_of_ready F r _ _ _ hstart hk
    intro s hst hsh
    apply ready s
    apply readyAbove_nonempty p hθ
    apply hpart _ hst
    have := congrArg EnvPoint.horizon hr
    change r.horizon = p.horizon at this
    rwa [← this]
  cases q with
  | sleepy | stableInclusion | fastInclusion => exact hs
  | outage T b₀ b₁ | fastOutage T b₀ b₁ => exact hh b₀
  | live k =>
    exact ⟨hs, recur 0 k (le_refl _) hd _ hA.sleepy_lower he.2⟩
  | recovery k =>
    exact ⟨hs, recur p.env.gst k hd.1 hd.2 _ hA.recovery_lower he.1⟩
  | finality k =>
    exact ⟨hs, recur p.env.gst k hd.1 hd.2 _ hA.recovery_lower he.1.1⟩
end Consensus.Shape
end
