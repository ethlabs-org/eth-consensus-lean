module
public import AvailableChainPCSAProofs.Proofs.Clean.RestartRoots

public section

/-! The restricted joint state of the CI restart from label `a` (pcsa34-r5 §5.5).
Every label quantifier starts at `a`: results of labels `a..j`, HEADs of labels
`a..j`, PCs of slot at least `a`, the roots for `v_{j+1}`, and the coverage of
acks of labels at least `a`. -/
namespace AvailableChain.PCSA.Run
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In) {m : FGMode}
    (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- The joint restart state from label `a` through label `j`. -/
structure CleanStateFrom (a j : Slot) : Prop where
  results : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (i i' : Slot) (X Y : Block),
    a ≤ i → i ≤ i' → i' ≤ j →
    gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
    (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y)
  headsAbove : ∀ (i : Slot) (x y : V) (H X : Block), a < i → i ≤ j →
    HonestHeadAt p c E rho x i H → y ∈ rho.honest →
    gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H
  headsEqual : ∀ (i : Slot) (P : Block) (x : V) (H : Block), a ≤ i → i ≤ j →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho i P →
    HonestHeadAt p c E rho x i H → H = P
  pcResults : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t : Time) (C : PC p.n) (i : Slot)
    (X : Block), t < SA.voteTime p.toParams (j + 1) → a ≤ C.slot →
    C ∈ (storeAt p c E rho x t).pcs → a ≤ i → i ≤ j →
    gateResultAt p c E rho y i = some (some X) → Block.Compatible C.target X
  roots : ∀ x ∈ rho.honest, ∀ R : Block, liveRootAt p c E rho x (j + 1) = some R →
    ∀ y ∈ rho.honest, ∀ X, gateResultAt p c E rho y j = some (some X) →
      Block.Compatible R X
  ackHeads : ∀ i k, a ≤ i → i < k → k ≤ j + 1 → ∀ y B, HonestAckAt p c E rho y i B →
    ∀ x H, HonestHeadAt p c E rho x k H → Block.Preceq B H
  ackResults : ∀ i k, a ≤ i → i < k → k ≤ j → ∀ y B, HonestAckAt p c E rho y i B →
    ∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x k = some (some X) → Block.Preceq B X

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- The restart state at the seed label. -/
theorem pcsa_restart_state_base (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (hz : SA.freezeTime p.toParams a ≤ rho.horizon) :
    CleanStateFrom p c E rho a a := by
  have hres : ∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x a = some (some X) → X = A := by
    intro x hx X hX
    exact Option.some.inj (hS.result x hx _ hX)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy i i' X Y hi hii hi' hX hY
    have he : i = a := Nat.le_antisymm (hii.trans hi') hi
    have he' : i' = a := Nat.le_antisymm hi' (hi.trans hii)
    subst he he'
    rw [hres x hx X hX, hres y hy Y hY]
    exact ⟨fun hlt => absurd hlt (lt_irrefl _), fun _ =>
      Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_refl _))⟩
  · intro i x y H X hi hj
    exact absurd (hi.trans_le hj) (lt_irrefl _)
  · intro i P x H hi hj hP hH
    have he : i = a := Nat.le_antisymm hj hi
    subst he
    rw [hS.heads x H hH, hS.proposal P hP]
  · intro x hx y hy t C i X ht hC hCm hi hj hX
    have he : i = a := Nat.le_antisymm hj hi
    subst he
    obtain ⟨hs, z, hza⟩ := pcsa_pc_storeAt_ack_slot E rho h hFault i x hx t ht C hCm
    have hCs : C.slot = i := Nat.le_antisymm hs hC
    rw [hCs] at hza
    rw [pcsa_restart_ack_target E rho h hF hFault hS z C.target hza, hres y hy X hX]
    exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_refl _))
  · intro x hx R hR y hy X hX
    rw [pcsa_restart_root_base E rho h hF hFault hS hz x hx R hR, hres y hy X hX]
    exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_refl _))
  · intro i k hi hik hk y B hB x H hH
    have he : i = a := Nat.le_antisymm (Nat.le_of_lt_succ (hik.trans_le hk)) hi
    subst he
    have hk' : k = i + 1 := Nat.le_antisymm hk hik
    subst hk'
    rw [pcsa_restart_ack_target E rho h hF hFault hS y B hB]
    exact hS.arm.1 (i + 1) x H le_rfl hH
  · intro i k hi hik hk
    exact absurd (hi.trans_lt (hik.trans_le hk)) (lt_irrefl _)

/-- From label `a`: the restart state bounds every lock read after `z_a` and before
`v_{s+1}` by each result of label `s`. A result of label `a` supplies the seed. -/
theorem pcsa_restart_pre_vote_lock_below_result (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    {a : Slot} {A : Block} (hS : CleanRestartSeed p c E rho a A)
    (s : Slot) (has : a ≤ s) (hst : CleanStateFrom p c E rho a s)
    (hseed : ∃ w ∈ rho.honest, ∃ W, gateResultAt p c E rho w a = some (some W))
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hzk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ k)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)))
    (row : Block × Nat × Time) (hr : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations)
    (X : Block) (hX : gateResultAt p c E rho y s = some (some X)) : Block.Preceq row.1 X := by
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hAX : Block.Preceq A X := by
    obtain ⟨w, hw, W, hW⟩ := hseed
    have hWA : W = A := Option.some.inj (hS.result w hw _ hW)
    rw [← hWA]
    rcases has.lt_or_eq with hlt | heq
    · exact (hst.results w hw y hy a s W X le_rfl has le_rfl hW hX).1 hlt
    · subst heq
      rw [hWA, Option.some.inj (hS.result y hy _ hX)]
      exact Gen.Pure.block_preceq_refl _
  let cut := V2.D.Run.idxBefore rho (SA.gateTime p.toParams a)
  have hzc : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ cut := by
    change V2.D.Run.idxBefore rho _ ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams a)
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    apply decide_eq_true
    apply (of_decide_eq_true he).trans_le
    change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (a : Int) + 6 * p.Δ
    linarith
  rcases le_total k cut with hkc | hck
  · exact Gen.Pure.block_preceq_trans (hS.locksFromFreeze x hx k hzk hkc row hr) hAX
  · rcases pcsa_lock_stateBefore_origin_from E rho h cut k hck x row hr with
      hold | ⟨j, hcj, hjk, s', Y, hj, hY, hrY, _⟩
    · exact Gen.Pure.block_preceq_trans (hS.locksFromFreeze x hx cut hzc le_rfl row hold) hAX
    · have hge : ¬ SA.gateTime p.toParams s' < SA.gateTime p.toParams a := fun hlt =>
        absurd ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr hlt) (not_lt.mpr hcj)
      have has' : a ≤ s' := by
        by_contra hn
        apply hge
        change 4 * p.Δ * (s' : Int) + 6 * p.Δ < 4 * p.Δ * (a : Int) + 6 * p.Δ
        have : (s' : Int) + 1 ≤ a := by exact_mod_cast Nat.lt_of_not_ge hn
        nlinarith
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp (hjk.trans_le hk)
      have hi := pcsa_gate_label_lt_next_vote p s' s ht
      exact Gen.Pure.block_preceq_trans hrY
        ((hst.results x hx y hy s' s Y X has' hi.le le_rfl hY hX).1 hi)
end AvailableChain.PCSA.Run

end
