module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingStep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingHistory
public import AvailableChainFGSARun.Proofs.AC

public section

/-! Plan O-ARM §4 field 7 (output and F clauses), §6.2 step 5. At or before
the cut, Clean gate coverage and monotonicity keep B in S. After the cut, S
changes only by a normalization to an F below `D`; it stays between B and `D`. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; the stable record
at the cut is below `D`: genesis, an actual gate result of label at most `l`,
or an F value of the healthy prefix. -/
theorem arming_S_cut {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {D : Block}
    (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmax : ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq X D)
    {y : V} (hy : y ∈ rho.honest)
    (hF : ∀ q, q ≤ timeIdx rho b₀ → Block.Preceq (F_at p c E rho q y) D) :
    Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D := by
  rcases hsOrigin (timeIdx rho b₀) y le_rfl hy with hg | ⟨q, hq, s, hqt, hres⟩ | ⟨q, hq, he⟩
  · rw [hg]
    exact block_genesis_preceq D
  · have hmem : (s, S_at p c E rho (timeIdx rho b₀) y) ∈
        cleanResults p c E rho (timeIdx rho b₀) :=
      ⟨q, hq, y, hqt, (arming_enabled_of_result hs hqt hres).2, hres⟩
    obtain ⟨_, _, _, _, _, hsb, _, _⟩ := arming_clean_mem hs le_rfl hmem
    exact hmax s _ hmem (arming_lt_pending p l s (hsb.trans_lt hcut))
  · rw [he]
    exact hF q hq

/-- Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; between the cut and
the pending gate, S stays between B and `D`. The only change is the delivery
normalization to an F below `D`. -/
theorem arming_S_interval {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {b₀ : Time} {l : Slot} {B D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (h₀ : Block.Preceq B (S_at p c E rho (timeIdx rho b₀) y) ∧
      Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D)
    {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))) :
    Block.Preceq B (S_at p c E rho i y) ∧ Block.Preceq (S_at p c E rho i y) D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkd : k < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
      lt_of_lt_of_le (Nat.lt_succ_self k) hi
    obtain ⟨hB, hD⟩ := ih hkd.le
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le hkd (arming_idxBefore_le_length rho _)
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    obtain ⟨hb, hd⟩ := arming_event_window hs he hk hkd
    rcases fgsaAC_output_step E rho k y with heq | ⟨s, hgs⟩ | ⟨o, t, b, hdel, _, _, hnorm⟩ |
        ⟨t, hrs, _⟩
    · change S_at p c E rho (k + 1) y = S_at p c E rho k y at heq
      rw [heq]
      exact ⟨hB, hD⟩
    · exfalso
      obtain ⟨hb', hd'⟩ := arming_event_window hs hgs hk hkd
      exact arming_offGate p l hl hb' hd' s rfl
    · change S_at p c E rho (k + 1) y =
        Gen.AC.normalizeOutput (F_at p c E rho (k + 1) y) (S_at p c E rho k y) at hnorm
      rw [hnorm, Gen.AC.normalizeOutput_def]
      have hFk := hF (k + 1) hi
      split
      · exact ⟨hB, hD⟩
      · next hn =>
        rcases block_preceq_total_of_common hFk hD with h | h
        · exact absurd h hn
        · exact ⟨block_preceq_trans hB h, hFk⟩
    · exact absurd hrs (hnr k y t)

/-- Plan O-ARM §6.2 step 5. Class (iii). DC: INTENTIONAL; between the cut and
the pending gate, S stays between B and `D`. The only change is the delivery
normalization to an F below `D`. -/
theorem arming_S_interval_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    {b₀ : Time} {l : Slot} {B D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (h₀ : Block.Preceq B (S_at p c E rho (timeIdx rho b₀) y) ∧
      Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D)
    {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (hEpoch : V2.D.restartFree rho y (timeIdx rho b₀) i) :
    Block.Preceq B (S_at p c E rho i y) ∧ Block.Preceq (S_at p c E rho i y) D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkd : k < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
      lt_of_lt_of_le (Nat.lt_succ_self k) hi
    obtain ⟨hB, hD⟩ := ih hkd.le (hEpoch.mono le_rfl (Nat.le_succ k))
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le hkd (arming_idxBefore_le_length rho _)
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    obtain ⟨hb, hd⟩ := arming_event_window hs he hk hkd
    rcases fgsaAC_output_step E rho k y with heq | ⟨s, hgs⟩ | ⟨o, t, b, hdel, _, _, hnorm⟩ |
        ⟨t, hrs, _⟩
    · change S_at p c E rho (k + 1) y = S_at p c E rho k y at heq
      rw [heq]
      exact ⟨hB, hD⟩
    · exfalso
      obtain ⟨hb', hd'⟩ := arming_event_window hs hgs hk hkd
      exact arming_offGate p l hl hb' hd' s rfl
    · change S_at p c E rho (k + 1) y =
        Gen.AC.normalizeOutput (F_at p c E rho (k + 1) y) (S_at p c E rho k y) at hnorm
      rw [hnorm, Gen.AC.normalizeOutput_def]
      have hFk := hF (k + 1) hi
      split
      · exact ⟨hB, hD⟩
      · next hn =>
        rcases block_preceq_total_of_common hFk hD with h | h
        · exact absurd h hn
        · exact ⟨block_preceq_trans hB h, hFk⟩
    · exact absurd hrs (hEpoch k t hk (Nat.lt_succ_self k))

/-- Plan O-ARM §4 field 7, §6.2 step 5. Class (iii). DC: INTENTIONAL; B is in
the honest stable output on [d(l), d(l + 1)), for awake and asleep readers. -/
theorem arming_cover {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {b₀ : Time}
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') → Block.Preceq C' C)
    {l : Slot} {B D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    {u : V} {s : Slot} {C : Block} (hu : u ∈ rho.honest) (hsl : s < l)
    (hC : gateResult p c E rho u s = some (some C)) (hBC : Block.Preceq B C)
    (hF : ∀ k y, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho k y) D)
    (hS₀ : ∀ y, y ∈ rho.honest → Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D) :
    ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
      t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) := by
  have hsb : SA.gateTime p.toParams s ≤ b₀ :=
    ((arming_gate_le_iff p s l).mpr hsl.le).trans hl
  have hbefore : ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t → t ≤ b₀ →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) := by
    intro y t hy hlt htb
    obtain ⟨Cl, hCl, _, hClS, _⟩ := hcleanGate l y hl hy
    have hCCl := (hordered u y s l C Cl hu hy hsb hl hC hCl).1 hsl
    have hidx : afterTicksIdx rho (SA.gateTime p.toParams l) ≤ timeIdx rho t :=
      (afterTicksIdx_mono rho hlt).trans (preIdx_le_afterTicksIdx E rho hs t).2
    exact block_preceq_trans (block_preceq_trans hBC hCCl)
      (block_preceq_trans hClS (hmono y hy _ _ hidx (arming_timeIdx_mono rho htb)))
  intro y t hy hlt htd _
  rcases le_or_gt t b₀ with htb | htb
  · exact hbefore y t hy hlt htb
  · exact (arming_S_interval hs hnr hl y (fun k hk => hF k y hk hy)
      ⟨hbefore y b₀ hy hl le_rfl, hS₀ y hy⟩ (arming_timeIdx_mono rho htb.le)
      (arming_timeIdx_le_idxBefore rho htd)).1

/-- Plan O-ARM §4 field 7. Class (iii). DC: INTENTIONAL; every honest F before
the pending gate is compatible with B, from time 0. -/
theorem arming_compat {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {l : Slot} {B D : Block} (hBD : Block.Preceq B D)
    (hF : ∀ k y, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho k y) D) :
    ∀ y t, y ∈ rho.honest → 0 ≤ t → t < SA.gateTime p.toParams (l + 1) →
      t ≤ rho.horizon → Block.Compatible B (F_at p c E rho (timeIdx rho t) y) :=
  fun y _ hy _ htd _ =>
    block_compatible_of_common hBD (hF _ y (arming_timeIdx_le_idxBefore rho htd) hy)

end AvailableChain.FGSA.Run
end
