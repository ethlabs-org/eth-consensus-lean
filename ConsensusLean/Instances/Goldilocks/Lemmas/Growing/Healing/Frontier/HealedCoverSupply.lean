module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Frontier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.CommitteeFaults
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The healed frontier after the deep quarantine

From reset premises up to a time `T` with the drain of the reset at least `4Δ` before `T`, and the
healthy participation from `ḡ` through `b ≥ T` (awake honest nodes, faults below a third,
committee faults below `βK`) and the reset service, the healed family
of the reset at the floors `(cleanLabel a + k + 2, cleanLabel a + 2k + 1)` is pairwise compatible
and extended by every later honest vote through `b` (`healthy_healed_frontier_at`). Conviction
below a third through `b` follows from the faults through `b` (`chainConvictedBelowUpTo_of_faults`):
the frontier reads conviction only for readers honest by `b`.

The hand-over core is built at `T` (`HandoverCore.of_reset`); the slot and committee counts from
its lock floor through `b` come from the healthy participation (`sleepyBoundsFrom_of_faultBoundAt`
and the committee bound below); `healed_frontier_at` then gives the frontier at every label. At
`T = c_z + 4DΔ` the reset premises are inside the deep quarantine, so the seed uses only
pre-expiry facts. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A restart of a node honest at its cut, by `b`, is no later than `t_{slot ḡ + 1}` when every
node honest at a time of `[ḡ, b]` is awake then (the argument of `restart_le_before_at`). -/
private theorem restart_le_of_awake (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg
      H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hk : tr.RestartAt y k)
    (hkb : tr.time k ≤ b) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hrun.sleep_of_restart y k hy hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (AC.ts_le_iff_le_slot sp (gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hawake y u (hrun.antitone huk.le hy) hgu (huk.le.trans hkb))
  · have htk : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ tr.time k := (lt_of_not_ge hlt).le
    have hy' := hrun.antitone htk hy
    obtain ⟨j, _x, fgDue, hne, hcs, -⟩ := hrun.tick_of_awake y _ hy'
      ((gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [ACParams.ts]; ring⟩
      (hawake y _ hy' hp₀ (htk.trans hkb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hrun.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- From `c_z` through `b`, a node honest at `t` is awake and joined at `t`. -/
private theorem awake_joined_of_awake (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer
      dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {t : Time} (ht : cutZ sp.toParams g ≤ t) (htb : t ≤ b) {y : Fin sp.n} (hy : y ∈ H t) :
    tr.awake y t ∧ tr.JoinedAt y t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans hgt
  have hst : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (AC.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  refine ⟨hawake y t hy hgt htb, fun k hk hkt => ?_⟩
  change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
  have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
    sp.slotTime_eq _
  refine ⟨by omega, (restart_le_of_awake hrun hawake (hrun.antitone hkt hy) hk
    (hkt.trans htb)).trans ?_⟩
  rw [he]
  exact (AC.ts_le_iff sp).mpr (by omega)

/-- **The population count from `c_z` through `b`**: the nodes compromised by `d ∈ [t, b]` are
fewer than those honest at `d`, awake and joined at `t`. -/
private theorem faultBoundAt_of_awake (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer
      dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans (by have := lt_cutZ sp g; linarith)
  have hsub : H d ⊆ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t} := fun y hy =>
    ⟨hy, awake_joined_of_awake hrun hawake ht (htd.trans hdb) (hrun.antitone htd hy)⟩
  have hle := Set.ncard_le_ncard hsub
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hf d (ht0.trans htd) hdb
  have hpos := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  exact lt_of_lt_of_le (by omega : (H d)ᶜ.ncard < (H d).ncard) hle

/-- **CS at a slot committee from `c_z` through `b`** (the argument of `faultBoundK_late_at`):
the faulty members at `d ∈ [t, b]` of a slot committee from `ḡ` are fewer than its members honest
at `d`, awake and joined at `t`. -/
private theorem faultBoundK_of_awake_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcf : Generic.CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) (hβ : βK ≤ 1 / 2)
    (hpos : 0 < sp.committeeSize)
    (hsize : ∀ s, ((Generic.dictOfTime sp cm).committee s).ncard = sp.committeeSize) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    AC.FaultBoundK (Generic.dictOfTime sp cm) s tr.projAC (H d) t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans (by have := lt_cutZ sp g; linarith)
  have hsub : (Generic.dictOfTime sp cm).committee s ∩ H d ⊆
      (Generic.dictOfTime sp cm).committee s ∩
        {y | y ∈ H d ∧ tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t} := by
    rintro z ⟨hzK, hzd⟩
    have hz := hrun.antitone htd hzd
    obtain ⟨hza, hj⟩ := awake_joined_of_awake hrun hawake ht (htd.trans hdb) hz
    refine ⟨hzK, hzd, hza, ?_⟩
    have hjp := (Compose.joined_projection_from (hrun.upTo ht0) hz t).1
    have hjpre : (tr.upTo t).JoinedAt z t := fun k hk hkt =>
      hj k ((RunTrace.upTo_restartAt tr).mp hk).2 hkt
    intro k hk hkt
    obtain ⟨ℓ, hc, hr⟩ := hk
    refine hjp.mp hjpre k ?_ hkt
    rw [RunTrace.upTo_projAC]
    exact ⟨ℓ, (Trace.upTo_callAt _).mpr ⟨hkt, hc⟩, hr⟩
  have hf := hcf.committee_cs2_at hβ hpos (hsize s) hgs hsb (ht0.trans htd) hdb
  have hsplit : ((Generic.dictOfTime sp cm).committee s ∩ H d).ncard +
      ((Generic.dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard = sp.committeeSize := by
    rw [← hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  unfold AC.FaultBoundK
  exact lt_of_lt_of_le (by omega) (Set.ncard_le_ncard hsub)

/-- **Conviction below a third from faults below a third at every time**: a validator with a
slashable pair among the attestations on the chains held by two readers, honest at `t` and `t'`,
is compromised by `max t t'` (`held_atts_safe_at`), and fewer than a third are. -/
theorem chainConvictedBelow_of_faults (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer
      dg H tr ini)
    (hf : ∀ t, 0 ≤ t → 3 * (H t)ᶜ.ncard ≤ sp.n - 1) :
    Compose.Growing.ChainConvictedBelow tr H := by
  classical
  refine Compose.Growing.chainConvictedBelow_iff.2 fun y z i j t t' ht hi hy ht' hj hz X₁ _ X₂ _ W
    hW => ?_
  set d := max t t'
  have hheld : ∀ c ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
      (∃ Y ∈ (tr.state y i).fg.tree, c ∈ Y.fgPayload) ∨
        ∃ Y ∈ (tr.state z j).fg.tree, c ∈ Y.fgPayload := by
    rintro c (⟨Y, hY, -, hc⟩ | ⟨Y, hY, -, hc⟩)
    · exact Or.inl ⟨Y, hY, hc⟩
    · exact Or.inr ⟨Y, hY, hc⟩
  have hsub : (W : Set (Fin sp.n)) ⊆ (H d)ᶜ := by
    intro v hv hvd
    obtain ⟨a, ha, b', hb, hav, hab⟩ := hW v hv
    have hav' : a.val ∈ H d := hav ▸ hvd
    have hyd := le_max_left t t'
    have hzd := le_max_right t t'
    rcases hheld a ha with ha' | ha' <;> rcases hheld b' hb with hb' | hb'
    · exact held_atts_safe_at hrun ht hi hy ht hi hy hyd hyd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht hi hy ht' hj hz hyd hzd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht' hj hz ht hi hy hzd hyd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht' hj hz ht' hj hz hzd hzd a b' ha' hb' hav' hab
  have hle : W.card ≤ (H d)ᶜ.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub
  have h3 := hf d (ht.trans (le_max_left _ _))
  have hpos := sp.toParams.hn
  have hn' : sp.toParams.n = sp.n := rfl
  omega

/-- **Conviction below a third through `b` from faults below a third through `b`**: a validator
with a slashable pair among the attestations on the chains held by two readers, honest at
`t, t' ≤ b`, is compromised by `max t t' ≤ b` (`held_atts_safe_at`), and fewer than a third are. -/
theorem chainConvictedBelowUpTo_of_faults
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {b : Time} (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1) :
    Compose.Growing.ChainConvictedBelowUpTo tr H b := by
  classical
  refine Compose.Growing.chainConvictedBelowUpTo_iff.2 fun y z i j t t' ht htb hi hy ht' ht'b hj hz
    X₁ _ X₂ _ W hW => ?_
  set d := max t t'
  have hheld : ∀ c ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
      (∃ Y ∈ (tr.state y i).fg.tree, c ∈ Y.fgPayload) ∨
        ∃ Y ∈ (tr.state z j).fg.tree, c ∈ Y.fgPayload := by
    rintro c (⟨Y, hY, -, hc⟩ | ⟨Y, hY, -, hc⟩)
    · exact Or.inl ⟨Y, hY, hc⟩
    · exact Or.inr ⟨Y, hY, hc⟩
  have hsub : (W : Set (Fin sp.n)) ⊆ (H d)ᶜ := by
    intro v hv hvd
    obtain ⟨a, ha, b', hb, hav, hab⟩ := hW v hv
    have hav' : a.val ∈ H d := hav ▸ hvd
    have hyd := le_max_left t t'
    have hzd := le_max_right t t'
    rcases hheld a ha with ha' | ha' <;> rcases hheld b' hb with hb' | hb'
    · exact held_atts_safe_at hrun ht hi hy ht hi hy hyd hyd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht hi hy ht' hj hz hyd hzd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht' hj hz ht hi hy hzd hyd a b' ha' hb' hav' hab
    · exact held_atts_safe_at hrun ht' hj hz ht' hj hz hzd hzd a b' ha' hb' hav' hab
  have hle : W.card ≤ (H d)ᶜ.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub
  have h3 := hf d (ht.trans (le_max_left _ _)) (max_le htb ht'b)
  have hpos := sp.toParams.hn
  have hn' : sp.toParams.n = sp.n := rfl
  omega

/-- **The healed frontier through `b` from reset premises up to `T`**: with the drain of the reset
`a` at least `4Δ` before `T`, the healthy participation from `ḡ` through `b ≥ T` and the reset
service, the healed family of `a` at the floors
`(cleanLabel a + k + 2, cleanLabel a + 2k + 1)` satisfies S1 (`HealedOriginsBelow`) and S2
(`HealedVotesBelow`) at every label through `b`. The seed is `HandoverCore.of_reset` at `T` with
the split slot `σ = cleanLabel a + 2k + 1` (`t_σ + 8Δ = drainTime a + 4Δ`); the slot counts and
the committee counts from the lock floor and conviction below a third through `b` come from the
participation; `healed_frontier_at` concludes. -/
theorem healthy_healed_frontier_at {T : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time}
    (hpT : ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold)
    (hdrain : Healing.drainTime sp a + 4 * sp.Δ ≤ T) (hTb : T ≤ b)
    (hsvc : ACResetService tr H g ΔF)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcf : Generic.CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) :
    ∀ s, Compose.Growing.HealedOriginsBelow tr H g (Healing.cleanLabel sp a + sp.k + 2)
        (Healing.cleanLabel sp a + sp.k + 2 + sp.k - 1) s b ∧
      Compose.Growing.HealedVotesBelow tr H g (Healing.cleanLabel sp a + sp.k + 2)
        (Healing.cleanLabel sp a + sp.k + 2 + sp.k - 1) s b := by
  have hrun := hpT.run
  have hΔ := sp.toParams.hΔ
  set r := Healing.cleanLabel sp a + sp.k + 2 with hr
  have hts (s : Nat) : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  -- the split slot `σ = r + k − 1`: `t_σ + 8Δ = t_{r+k} + 4Δ = drainTime a + 4Δ`
  have hσ : sp.ts (r + sp.k - 1 : Nat) + 8 * sp.Δ ≤ T := by
    have h1 := hts (r + sp.k - 1)
    have h2 := hts (r + sp.k)
    have hk := sp.two_le_k
    rw [show r + sp.k - 1 + 1 = r + sp.k by omega] at h1
    rw [Healing.drainTime_eq,
      show sp.slot a + 2 * sp.k + 5 = r + sp.k by rw [hr, Healing.cleanLabel_eq]; omega] at hdrain
    linarith
  have hcore := Compose.Growing.HandoverCore.of_reset (σ := r + sp.k - 1) hpT hr hσ
    (by have := sp.two_le_k; omega)
  -- the lock floor's slots start after `c_z`
  have hca := hpT.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by linarith [AC.gbar_nonneg g, lt_cutZ sp g]
  have hsa : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hzr : ∀ s, r ≤ s → cutZ sp.toParams g ≤ sp.ts s := fun s hs => by
    have := Compose.ts_le_ts (sp := sp) (show sp.slot a + 1 ≤ s by
      rw [hr, Healing.cleanLabel_eq] at hs; omega)
    push_cast at this
    linarith
  have hrT : sp.ts r + sp.Δ ≤ T := by
    have := Compose.ts_le_ts (sp := sp) (show r ≤ r + sp.k - 1 by have := sp.two_le_k; omega)
    linarith
  have hgz := lt_cutZ sp g
  -- the slot counts from `r` through `b`
  have hB : Compose.Growing.SleepyBoundsFrom tr H r b :=
    Obligations.Growing.sleepyBoundsFrom_of_faultBoundAt hrun.antitone le_rfl
      (le_max_of_le_left (hrT.trans hTb)) fun t _ ht htb =>
        faultBoundAt_of_awake hrun hawake hf
          ((hzr r le_rfl).trans (by linarith)) (le_min (by linarith) htb) (min_le_right _ _)
  -- the committee counts from `r` through `b`
  have hKB : Compose.Growing.CommitteeBoundsFrom tr H (Generic.dictOfTime sp cm) r b := by
    refine ⟨fun s d hs h1 hdb _ => ?_, fun s d hs h0 hdb _ => ?_⟩
    · have hz := hzr s hs
      exact faultBoundK_of_awake_at hrun hawake hcf hpT.beta_le hpT.committee_pos
        hpT.committeeFacts.hsize (by linarith) (by linarith) (by linarith) h1 hdb
    · have hz := hzr s hs
      have h := hcf.committee_cs2_at hpT.beta_le hpT.committee_pos
        (hpT.committeeFacts.hsize s) (by linarith) (h0.trans hdb)
        (by linarith [AC.gbar_nonneg g]) hdb
      rwa [hpT.committeeFacts.hsize s]
  exact Compose.Growing.healed_frontier_at hrun hpT.noColl hcore hTb hsvc hB
    (chainConvictedBelowUpTo_of_faults hrun hf)
    hpT.committeeFacts hKB

/-- **The high-source cover after the deep quarantine** (the post-expiry arm of `deepCover`): from
reset premises up to `T` inside the deep quarantine, with the drain of `a` at least `4Δ` before
`T`, and the healthy participation and the reset service through `b ≥ T`, the healed family of
`a` satisfies S1 and S2 through `b`
(`healthy_healed_frontier_at`); the quarantine ends `4Δ` after the drain at the latest. At
`T = c_z + 4DΔ` nothing is circular: the premises up to `T` take the quarantine arm. -/
theorem healthy_high_source_cover_at {T : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {hold : Time}
    (hpT : ResetPremisesUpTo tr H proposer dg g ΔF a T cm βK hold)
    (hT : ∀ D, sp.deepDepth = some D → T ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hdrain : Healing.drainTime sp a + 4 * sp.Δ ≤ T) (hTb : T ≤ b)
    (hsvc : ACResetService tr H g ΔF)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcf : Generic.CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) :
    HighSourceCover tr H g a b := by
  have hF := healthy_healed_frontier_at hpT hdrain hTb hsvc hawake hf hcf
  refine ⟨fun D hD => hdrain.trans (hT D hD), fun C s C' s' h h' =>
    Compose.Growing.healedOriginsBelow_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega)
      (by omega) h h', fun C s h y i e he hib hs => ?_⟩
  exact Compose.Growing.healedVotesBelow_iff.1 (hF e.msg.slot).2 C s h y i e he hib hs le_rfl

end Consensus.Goldilocks.Healing.Growing

end
