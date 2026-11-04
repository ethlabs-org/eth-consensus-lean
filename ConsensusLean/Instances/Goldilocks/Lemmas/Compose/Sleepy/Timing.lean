module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers

public section

/-! # Goldilocks Compose: delivery timing helpers

Deadlines after restarts (`ac_deadline_le_of_restarts`) and block stamps after an acceptance
(`blockStamp_ge_of_accept`) and between restarts (`blockStamp_finite`), shared by the transport,
service and delivery arguments. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder)

/-! ### Deadlines -/

section Deadline

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} {T : ACTrace A}

/-- The last wake, when finite, is the time of a restart at or before the cut. -/
theorem lastWake_coe {y : Fin P.n} {w : Time} :
    ∀ {c : Nat}, T.lastWake y c = (w : WithBot Time) → ∃ k ≤ c, T.RestartAt y k ∧ T.time k = w
  | 0, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

/-- **The deadline after restarts**: with every restart up to cut `c` at or before `a`, the
deadline of `τ` is at most `max(τ, a) + Δ`. -/
theorem ac_deadline_le_of_restarts {y : Fin P.n} {c : Nat} {a : Time}
    (h : ∀ k ≤ c, T.RestartAt y k → T.time k ≤ a) (τ : Time) :
    T.deadline y c τ ≤ max τ a + P.Δ := by
  unfold ACTrace.deadline
  rcases hw : T.lastWake y c with _ | w
  · change τ + P.Δ ≤ max τ a + P.Δ
    linarith [le_max_left τ a]
  · obtain ⟨k, hk, hrk, rfl⟩ := lastWake_coe hw
    change max τ (T.time k) + P.Δ ≤ max τ a + P.Δ
    linarith [max_le_max (le_refl τ) (h k hk hrk)]

end Deadline

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

private theorem state_succ_call {y : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : T.CallAt y k ℓ) :
    T.state y (k + 1) = T.post k := by
  simp [Trace.state, hc.1, hc.2]

private theorem state_succ_not {y : Fin sp.n} {k : Nat} (hn : ∀ ℓ, ¬ T.CallAt y k ℓ) :
    T.state y (k + 1) = T.state y k := by
  rw [Trace.state]
  split_ifs with h
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 h.2
    exact absurd ⟨h.1, hℓ⟩ (hn ℓ)
  · rfl

/-- **A stamp is not earlier than the acceptance**: after an honest node accepts a block other
than genesis at cut `k`, its stamp is at least the time of `k` (a later receipt or a restart
writes a later time, or a restart resets it to `+∞`). -/
theorem blockStamp_ge_of_accept (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n FGP} (hk : T.AcceptAt y k B)
    (hB : B.root ≠ sp.genesisRoot) :
    ∀ c, k + 1 ≤ c → SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root := by
  have hpost : ∀ c (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)), T.CallAt y c ℓ → k ≤ c →
      (ℓ.call = .block B ∨ SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root) →
      SA.ETime.of (T.time k) ≤ (T.post c).blockStamp B.root := by
    intro c ℓ hc hkc hpre
    have hΦ : FrameOK ℓ.frame := by
      rcases hr.frameLaw y hy c ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp : T.post c =
        ((SA.goldilocksSA sp FGP ro).step y (T.state y c) ℓ.frame (T.time c) ℓ.call).1 := by
      rw [he]
    have htk : SA.ETime.of (T.time k) ≤ SA.ETime.of (T.time c) :=
      SA.etime_of_le_of.2 (hr.time_mono hkc)
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro y (T.state y c) hΦ (hr.time_nonneg c) ℓ.call
    rw [hp]
    generalize ℓ.call = cl at hpre hblk hoth ⊢
    cases cl with
    | block B' =>
      rw [hblk B' rfl, Function.update_apply]
      split_ifs with h
      · exact htk
      · rcases hpre with hpre | hpre
        · cases hpre
          exact absurd rfl h
        · exact hpre
    | restart =>
      change _ ≤ (SA.acRestart sp ro y (T.state y c) ℓ.frame (T.time c)).1.blockStamp B.root
      rcases ((SA.restart_state sp) FGP ro y (T.state y c) ℓ.frame (T.time c) hΦ
        (hr.time_nonneg c)).2.2.2.2.2.2.2.2.2.2 B.root with h | ⟨h, -⟩
      · rw [h]; simp [SA.SAState.initial, hB]
      · rw [h]; exact htk
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    obtain ⟨ℓ, hcl, hcall⟩ := hk
    rw [state_succ_call hcl]
    exact hpost k ℓ hcl le_rfl (Or.inl hcall)
  | succ c hkc ih =>
    by_cases hn : ∃ ℓ, T.CallAt y c ℓ
    · obtain ⟨ℓ, hcl⟩ := hn
      rw [state_succ_call hcl]
      exact hpost c ℓ hcl (by omega) (Or.inr ih)
    · rw [state_succ_not fun ℓ hcl => hn ⟨ℓ, hcl⟩]
      exact ih

/-- **Between restarts, a finite block stamp stays finite** (a receipt writes a finite time). -/
theorem blockStamp_finite (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {y : Fin sp.n}
    (hy : y ∈ H) {a b : Nat} (hab : a ≤ b) (hnr : ∀ k, a ≤ k → k < b → ¬ T.RestartAt y k)
    {q : Nat} (h : (T.state y a).blockStamp q < ⊤) : (T.state y b).blockStamp q < ⊤ := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ b hab ih =>
    have ih := ih fun k h₁ h₂ => hnr k h₁ (h₂.trans (Nat.lt_succ_self b))
    by_cases hc : ∃ ℓ, T.CallAt y b ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      rw [state_succ_call hc]
      have hΦ : FrameOK ℓ.frame := by
        rcases hr.frameLaw y hy b ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
          exact h.1.1
      have he := hr.exec b ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have hp : T.post b =
          ((SA.goldilocksSA sp FGP ro).step y (T.state y b) ℓ.frame (T.time b) ℓ.call).1 := by
        rw [he]
      rw [hp]
      obtain ⟨hblk, -, hoth⟩ := SA.step_blockStamp_eq ro y (T.state y b) hΦ (hr.time_nonneg b)
        ℓ.call
      generalize hcl : ℓ.call = cl at hblk hoth
      cases cl with
      | block B =>
        rw [hblk B rfl, Function.update_apply]
        split_ifs
        · exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
        · exact ih
      | restart => exact absurd ⟨ℓ, hc, hcl⟩ (hnr b hab (Nat.lt_succ_self b))
      | tick => rw [hoth (fun _ => by simp) (by simp)]; exact ih
      | message m => rw [hoth (fun _ => by simp) (by simp)]; exact ih
      | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact ih
      | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact ih
    · rw [state_succ_not fun ℓ h => hc ⟨ℓ, h⟩]
      exact ih

end Node

end Consensus.Goldilocks.Compose

end
