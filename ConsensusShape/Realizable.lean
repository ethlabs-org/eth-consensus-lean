module
public import ConsensusShape.Conservative
public import Mathlib.Tactic
@[expose] public section
namespace Consensus.Shape
open Model Run

/-- All reported deadlines, including the relay step. -/
def serviceBounds (C : Constants) (k : Nat) : List Nat :=
  [C.D_c, C.D_s, C.D_f, C.growth.eval k + 1, C.stableGrowth.eval k + 1,
   C.recovery.eval k, C.recovery.eval k + C.recGrowth.eval k + 1,
   C.finStart.eval k + C.finDelay.eval k + 1]

private theorem population (A : Assumptions) (hA : A.WellFormed) :
    ∃ n : Nat, 2 < n ∧
      (∀ θ ∈ [A.sleepyReadyAbove, A.stableEtaAbove, A.recovery.readyAbove,
        A.finalityReadyOfAll, A.fastOutageReadyAtLeast], θ * (n + 1 : ℚ) < n) ∧
      (1 : ℚ) < A.fastFaultsBelow * (n + 1 : ℚ) := by
  let θ := max A.sleepyReadyAbove (max A.stableEtaAbove
    (max A.recovery.readyAbove (max A.finalityReadyOfAll A.fastOutageReadyAtLeast)))
  have hu : θ < 1 := by
    dsimp [θ]
    simp only [max_lt_iff]
    exact ⟨hA.sleepy_upper, hA.stable_upper, hA.recovery_upper,
      hA.finality_upper, hA.outage_upper⟩
  have hl : 0 ≤ θ := hA.sleepy_lower.trans (le_max_left _ _)
  have hd : 0 < 1 - θ := sub_pos.mpr hu
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℚ) / (1 - θ) + 1 / A.fastFaultsBelow + 2)
  have hni : 1 / (1 - θ) < (n : ℚ) := by
    have : 0 < 1 / A.fastFaultsBelow := div_pos (by norm_num) hA.fast_lower
    linarith
  have hnb : 1 / A.fastFaultsBelow < (n : ℚ) := by
    have : 0 < 1 / (1 - θ) := div_pos (by norm_num) hd
    linarith
  have hm := (div_lt_iff₀ hd).mp hni
  have hb := (div_lt_iff₀ hA.fast_lower).mp hnb
  have hn0 : 0 < (n : ℚ) := lt_trans (div_pos (by norm_num) hd) hni
  have hn2 : (2 : ℚ) < n := by
    have hi := div_pos (by norm_num : (0 : ℚ) < 1) hd
    have hi' := div_pos (by norm_num : (0 : ℚ) < 1) hA.fast_lower
    linarith
  refine ⟨n, by exact_mod_cast hn2, ?_, by nlinarith [hA.fast_lower]⟩
  intro x hx
  have hxθ : x ≤ θ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> dsimp [θ] <;> grind
  have : x * (n + 1 : ℚ) ≤ θ * (n + 1 : ℚ) := mul_le_mul_of_nonneg_right hxθ (by positivity)
  nlinarith

/-- A witness activates service independently of the protocol's outputs. -/
def realizableEnv (V : Type) : Env V := ⟨1, by decide, 0, fun _ _ => true⟩

/-- Active ready readers, a submission, a proposal after startup, a recurrence
window, and all deadlines (including relay latency) within the horizon. -/
def ActiveEnvironment {V : Type} [Fintype V] [DecidableEq V]
    (F : Family) (A : Assumptions) (C : Constants) (k : Nat) (p : EnvPoint V) : Prop :=
  p.SubmittedToSome 42 0 ∧
  (∃ w ∈ p.honest, ∀ τ, p.submit w τ = []) ∧
  ∃ s, 0 < (protoOf F p.env).proposalTime s ∧
    p.env.gst + (C.recovery.eval k : Time) * p.env.Δ < (protoOf F p.env).proposalTime s ∧
    p.env.gst + (C.finStart.eval k : Time) * p.env.Δ < (protoOf F p.env).proposalTime s ∧
    (k : Time) * (protoOf F p.env).slotLen ≤ p.horizon ∧
    ∀ d ∈ serviceBounds C k,
      (protoOf F p.env).proposalTime s + (d : Time) * p.env.Δ ≤ p.horizon ∧
      (p.readyAt ((A.catchUp : Time) * p.env.Δ)
        ((protoOf F p.env).proposalTime s + (d : Time) * p.env.Δ)).Nonempty

/-- Nonempty adversaries and active service for every well-formed set of
parameters. Outage endpoints are existential, so their interval is active. -/
theorem env_realizable (F : Family) (A : Assumptions) (hA : A.WellFormed) (C : Constants) (k : Nat) :
    ∃ n : Nat, ∃ p : EnvPoint (Fin (n + 1)),
      p.WellFormed ∧ p.faulty.Nonempty ∧ ActiveEnvironment F A C k p ∧
      System.EnvAssumption A (bounds C) .sleepy p ∧
      System.EnvAssumption A (bounds C) .stableInclusion p ∧
      System.EnvAssumption A (bounds C) .fastInclusion p ∧
      System.EnvAssumption A (bounds C) (.live k) p ∧
      System.EnvAssumption A (bounds C) (.recovery k) p ∧
      System.EnvAssumption A (bounds C) (.finality k) p ∧
      ∃ T b₀ b₁, 0 < T ∧ T < b₀ ∧ b₀ < b₁ ∧
        System.EnvAssumption A (bounds C) (.outage T b₀ b₁) p ∧
        System.EnvAssumption A (bounds C) (.fastOutage T b₀ b₁) p := by
  classical
  obtain ⟨n, hn, hθ, hβ⟩ := population A hA
  let B := (serviceBounds C k).sum
  let E := realizableEnv (Fin (n + 1))
  let L := (protoOf F E).slotLen
  have hL : 0 < L := (protoOf F E).slotLen_pos
  let t := (protoOf F E).proposalTime (B + 1)
  have ht : (B : Time) < t := by
    change (B : Int) < ((B + 1 : Nat) : Int) * L
    push_cast
    have : 1 ≤ L := by simp only [Time] at *; omega
    nlinarith
  let lag := A.armingLag + A.fastArmingLag + 1
  let H : Time := t + B + lag + A.outageBudget + (k : Time) * L + 2
  let p : EnvPoint (Fin (n + 1)) :=
    ⟨E, Finset.univ.erase 0, H,
      fun v τ => if v.val = 1 ∧ τ = 0 then [42] else []⟩
  have hc : p.honest.card = n := by simp [p]
  have hf : p.faulty = {0} := by ext v; simp [EnvPoint.faulty, p]
  have hr : ∀ c t, p.readyAt c t = p.honest := by
    intro c t; ext v
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, p, E, realizableEnv]
  have ha : ∀ t, p.awakeIn (t - (A.eta : Time) * p.env.Δ) t = p.honest := by
    intro t; ext v
    simp only [EnvPoint.awakeIn, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hv
      refine ⟨hv, t, ?_, le_rfl, rfl⟩
      change t - (A.eta : Int) * 1 ≤ t
      simp only [Time] at *
      omega
  have hne : p.honest.Nonempty := Finset.card_pos.mp (by omega)
  have ready (θ : ℚ) (hx : θ ∈ [A.sleepyReadyAbove, A.stableEtaAbove,
      A.recovery.readyAbove, A.finalityReadyOfAll, A.fastOutageReadyAtLeast]) (s : Time) :
      p.ReadyAbove θ ((A.catchUp : Time) * p.env.Δ) s := by
    unfold EnvPoint.ReadyAbove
    rw [hr, hc, hf]
    simpa using hθ θ hx
  have eta (s : Time) : p.EtaSleepy A.stableEtaAbove ((A.eta : Time) * p.env.Δ) ((A.catchUp : Time) * p.env.Δ) s := by
    unfold EnvPoint.EtaSleepy
    rw [ha, hr, hc]
    have hun : p.honest ∪ p.faulty = Finset.univ := by
      ext v; simp [EnvPoint.faulty]
    rw [hun]
    simpa using hθ A.stableEtaAbove (by simp)
  have full (start : Time) : p.FullParticipation start := by intro _ _ _ _ _; rfl
  have sleepy : System.EnvAssumption A (bounds C) .sleepy p :=
    ⟨rfl, fun s _ _ => ready _ (by simp) s⟩
  have hrec : C.recovery.eval k ≤ B :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by simp [serviceBounds])
  have recovery : System.EnvAssumption A (bounds C) (.recovery k) p := by
    refine ⟨fun s _ _ => ready _ (by simp) s, fun _ => full _, ?_, ?_⟩
    · intro _ v hv s hs hh
      simp [Wakes, p, E, realizableEnv]
    · change 0 + (C.recovery.eval k : Int) * 1 ≤ H
      dsimp only [H, lag, Time] at *; have := mul_nonneg (Int.natCast_nonneg k) hL.le; omega
  have fin (s : Time) : p.ReadyOfAll A.finalityReadyOfAll ((A.catchUp : Time) * p.env.Δ) s := by
    unfold EnvPoint.ReadyOfAll
    rw [hr, hc]
    simpa using hθ A.finalityReadyOfAll (by simp)
  have high (s : Time) : p.ReadyOfAllAtLeast A.fastOutageReadyAtLeast
      ((A.catchUp : Time) * p.env.Δ) s := by
    unfold EnvPoint.ReadyOfAllAtLeast
    rw [hr, hc]
    exact le_of_lt (by simpa using hθ A.fastOutageReadyAtLeast (by simp))
  refine ⟨n, p, ?_, ?_, ?_, sleepy, ⟨sleepy, fun s _ _ => eta s⟩,
    ⟨sleepy, full _, ?_⟩, sleepy, recovery, ⟨recovery, fun s _ _ => fin s⟩,
    t, t + lag, t + lag + 1, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ H
    dsimp [H, lag]; have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht; positivity
  · rw [hf]; simp
  · constructor
    · exact ⟨⟨1, by omega⟩, by simp [p], 0, le_rfl, le_rfl, rfl, by simp [p]⟩
    · refine ⟨⟨⟨2, by omega⟩, by simp [p], fun τ => by simp [p]⟩, ?_⟩
      have hfin : C.finStart.eval k + C.finDelay.eval k + 1 ≤ B :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by simp [serviceBounds])
      refine ⟨B + 1, ?_, ?_, ?_, ?_, ?_⟩
      · exact lt_of_le_of_lt (by positivity : (0 : Time) ≤ B) ht
      · change 0 + (C.recovery.eval k : Int) * 1 < t
        simp only [Time] at *; omega
      · change 0 + (C.finStart.eval k : Int) * 1 < t
        simp only [Time] at *; omega
      · change (k : Time) * L ≤ H
        dsimp only [H, lag, Time] at *
        have := mul_nonneg (Int.natCast_nonneg k) hL.le
        omega
      · intro d hd
        have hdB : d ≤ B := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hd
        refine ⟨?_, ?_⟩
        · change t + (d : Int) * 1 ≤ H
          dsimp only [H, lag, Time] at *; have := mul_nonneg (Int.natCast_nonneg k) hL.le; omega
        · rw [hr]; exact hne
  · unfold EnvPoint.FaultsBelow
    rw [hf]
    simpa using hβ
  · exact lt_of_le_of_lt (by positivity : (0 : Time) ≤ B) ht
  · change t < t + (lag : Int)
    dsimp [lag]; simp only [Time] at *; omega
  · simp only [Time] at *; omega
  · refine ⟨?_, ?_, ?_, fun s _ _ => ready _ (by simp) s, fun s _ _ => eta s⟩
    · change 0 ≤ t ∧ t ≤ t + lag ∧ t + lag ≤ t + lag + 1 ∧ t + lag + 1 ≤ H
      dsimp only [H, lag, Time] at *; have := mul_nonneg (Int.natCast_nonneg k) hL.le; omega
    · change t + (A.armingLag : Int) * 1 ≤ t + lag
      dsimp [lag]; simp only [Time] at *; omega
    · change t + lag + 1 - (t + lag) ≤ (A.outageBudget : Int) * 1
      have := hA.budget_pos; simp only [Time] at *; omega
  · refine ⟨⟨?_, ?_, ?_, fun s _ _ => ready _ (by simp) s, fun s _ _ => eta s⟩,
      fun s _ _ => high s⟩
    · change 0 ≤ t ∧ t ≤ t + lag ∧ t + lag ≤ t + lag + 1 ∧ t + lag + 1 ≤ H
      dsimp only [H, lag, Time] at *; have := mul_nonneg (Int.natCast_nonneg k) hL.le; omega
    · change t + (A.fastArmingLag : Int) * 1 ≤ t + lag
      dsimp [lag]; simp only [Time] at *; omega
    · change t + lag + 1 - (t + lag) ≤ (A.outageBudget : Int) * 1
      have := hA.budget_pos; simp only [Time] at *; omega
/-- Synchrony activates an actual relay to a receiver with no local
submission, rather than merely reusing a source's own mempool. -/
theorem active_relay {V : Type} [Fintype V] [DecidableEq V] {F : Family}
    {E : Env V} (r : Model.Run (compiled F) E) (A : Assumptions) (C : Constants) (k : Nat)
    (hs : r.PartialSynchrony) (hg : E.gst = 0) (hf : r.point.FullParticipation 0)
    (ha : ActiveEnvironment F A C k r.point) :
    ∃ w ∈ r.honest, ∃ τ, 0 ≤ τ ∧ τ < E.Δ ∧ 42 ∈ r.relay w τ := by
  obtain ⟨hsubmit, ⟨w, hw, hempty⟩, s, hp, _, _, _, hd⟩ := ha
  change 0 < (protoOf F E).proposalTime s at hp
  change ∀ τ, r.submit w τ = [] at hempty
  have hbound := (hd (C.growth.eval k + 1) (by simp [serviceBounds])).1
  have hdelay : E.Δ ≤ r.horizon := by
    change (protoOf F E).proposalTime s + ((C.growth.eval k + 1 : Nat) : Time) * E.Δ ≤ r.horizon at hbound
    have hm : E.Δ ≤ ((C.growth.eval k + 1 : Nat) : Time) * E.Δ := by
      have := E.Δ_pos
      push_cast
      nlinarith [Int.natCast_nonneg (C.growth.eval k)]
    dsimp only [Time] at *; omega
  obtain ⟨u, hu, τ, hτ, hτ0, haw, hx⟩ := hsubmit
  have hz : τ = 0 := by dsimp only [Time] at *; omega
  subst τ
  have held := hs.txs u hu 42 0 (le_refl _) haw hx w hw 0 (le_refl _)
    (by simpa [hg] using hdelay) (by simpa [hg] using hdelay)
    (by
      intro z hz hzd
      apply hf w hw z hz
      have hzΔ : z < E.Δ := by simpa [hg] using hzd
      exact hzΔ.le.trans hdelay)
  simp only [hg, max_self, zero_add] at held
  obtain ⟨τ, hτ, hτd, hx⟩ := held
  refine ⟨w, hw, τ, hτ, hτd, ?_⟩
  simpa only [Model.Run.inbox, hempty, List.nil_append] using hx

/-- Environment and execution realizability composed, with a genuine
adversary, active service guards, and nonempty ordinary and fast outages. -/
theorem profile_realizable (F : Family) (A : Assumptions) (hA : A.WellFormed)
    (C : Constants) (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, ∃ p : EnvPoint (Fin (n + 1)),
      p.WellFormed ∧ p.faulty.Nonempty ∧ ActiveEnvironment F A C k p ∧
      ∃ T b₀ b₁, 0 < T ∧ T < b₀ ∧ b₀ < b₁ ∧
        ∀ q ∈ [System.ClaimKey.sleepy, .stableInclusion, .fastInclusion, .live k,
            .recovery k, .finality k, .outage T b₀ b₁, .fastOutage T b₀ b₁],
          ∃ r : (Model.sysOf (compiled F) (Fin (n + 1))).Run,
            ((Model.sysOf (compiled F) (Fin (n + 1))).trace r).point = p ∧
            (Model.sysOf (compiled F) (Fin (n + 1))).Valid r ∧
            (Model.sysOf (compiled F) (Fin (n + 1))).Premise A (bounds C) (profile A) q r ∧
            ¬ (Model.sysOf (compiled F) (Fin (n + 1))).Excuse r ∧
            (∃ s, 0 < (protoOf F r.1).proposalTime s ∧
              ReadyProposer r.2 ((A.catchUp : Time) * r.1.Δ) s) ∧
            (∃ w ∈ r.2.honest, ∃ τ, 0 ≤ τ ∧ τ < r.1.Δ ∧ 42 ∈ r.2.relay w τ) := by
  obtain ⟨n, p, hp, hf, ha, hs, hst, hfast, hl, hr, hfin,
    T, b₀, b₁, hT, hTb, hbb, ho, hfo⟩ := env_realizable F A hA C k
  refine ⟨n, p, hp, hf, ha, T, b₀, b₁, hT, hTb, hbb, ?_⟩
  intro q hq
  have he : System.EnvAssumption A (bounds C) q p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hd : CoverageDomain q p := by
    have hg : p.env.gst = 0 := hs.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [CoverageDomain]
  obtain ⟨r, hpoint, hv, hx, hn, hsync, hready⟩ := exec_conservative F A hA C q p hp hd he
  have hactive : ActiveEnvironment F A C k r.2.point := by
    change ActiveEnvironment F A C k ((Model.sysOf (compiled F) _).trace r).point
    rwa [hpoint]
  have hSleepy : System.EnvAssumption A (bounds C) .sleepy r.2.point := by
    change System.EnvAssumption A (bounds C) .sleepy ((Model.sysOf (compiled F) _).trace r).point
    rwa [hpoint]
  have hfull : r.2.point.FullParticipation 0 := by
    change ((Model.sysOf (compiled F) _).trace r).point.FullParticipation 0
    rw [hpoint]; exact hfast.2.1
  refine ⟨r, hpoint, hv, ⟨?_, hx⟩, hn, ?_, active_relay r.2 A C k hsync hSleepy.1 hfull hactive⟩
  · rwa [hpoint]
  · obtain ⟨_, _, s, hs, _, _, _, hd⟩ := hactive
    change 0 < (protoOf F r.1).proposalTime s at hs
    refine ⟨s, hs, hready s ?_⟩
    apply readyAbove_nonempty _ hA.sleepy_lower
    apply hSleepy.2 _ hs.le
    change (protoOf F r.1).proposalTime s ≤ r.2.horizon
    have hb := (hd C.D_c (by simp [serviceBounds])).1
    change (protoOf F r.1).proposalTime s + (C.D_c : Time) * r.1.Δ ≤ r.2.horizon at hb
    have hm : (0 : Time) ≤ (C.D_c : Time) * r.1.Δ := mul_nonneg (by positivity) r.1.Δ_pos.le
    dsimp only [Time] at *; omega

end Consensus.Shape
end
