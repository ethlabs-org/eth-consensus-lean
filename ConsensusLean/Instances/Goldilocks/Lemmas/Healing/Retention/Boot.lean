module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: the base case, activation, the vote premises and the records

HBoot (`boot_caches`), the label bound, the carries
from a finalized ancestor (`first_carry_of_finalized_anc`, `later_carry_of_finalized_anc`), half
the committee (`half_committee`).

Proved here: the label bound, half the committee, both carries (relay after
the GST, `Retention/Relay`) and HBoot's caches from G1.2 over the run
(`finalized_anc_of_height_lt_of_run`, `Retention/Finality`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### The base case, the vote premises and the records -/

/-- **The label bound of a high origin** (`j ≥ slot(c)`).
The writer accepted the counted heads, of state height `≥ H_z + 1`, before `t_j + 2Δ`; no honest
node accepts such a block at or before `c_z` (the definition of `H_z`), so `t_j + 2Δ > c_z`, and
`t_j ≥ c_z` since both are slot starts. -/
theorem ResetPremisesUpTo.cutZ_le_ts_of_highOrigin {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨ℓ, D, CV, hc, hfl, -, -, -, hBD, -⟩ := hp.highOrigin_mem ho
  obtain ⟨v, hv⟩ := fastLock_counted_nonempty hp.committee_pos hfl
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHv⟩, -, hDHv, hacc⟩ := fastLock_writer hr
    hp.run.vstart ho.1 hfl v hv
  have hBHv : Anc (tr.HonestBlocks H) B Hv :=
    (Anc.mono (AC.frameIn_of_callAt hr ho.1 hc).2 hBD).trans hDHv
  rcases hacc with hg | ⟨k, hk, hkt⟩
  · exact absurd hg (hp.cutZ_lt_of_anc ho hz hHv hBHv).2
  have hck := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hk) hBHv).1
  have hkt' : tr.time k < sp.ts j + 2 * sp.Δ := hkt
  rw [cutZ_eq sp g] at hck ⊢
  refine (AC.ts_le_iff sp).2 ?_
  by_contra hlt
  have h₂ := (AC.ts_le_iff sp).2 (show (j : Int) + 1 ≤ ((sp.slot (gbar g) + 3 : Nat) : Int) by
    clear * - hlt; omega)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  simp only [ACParams.ts] at h₂ hck hkt'
  linarith

/-- Whole-run specialization of the origin label lower bound. -/
theorem cutZ_le_ts_of_highOrigin (hp : ResetPremises tr H K proposer dg g ΔF a)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j :=
  (hp.toUpTo tr H (le_refl a)).cutZ_le_ts_of_highOrigin ho

/-- **No high justification before the reset**: at a state all of
whose earlier cuts are before `a`, every held block is justified at `≤ H_z`: otherwise it has state
height `≥ H_z + 2` (`h_j < h`), so its chain carries an honest attestation of height `H_z + 1` (HR.1
(b)), signed before the state's cut, hence before `a`, against HR.1 (c). -/
theorem ResetPremisesUpTo.hj_le_HZ_of_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : ∀ k' < k, tr.time k' < a) {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) : ((tr.state y k).fg.σ X.root).hj ≤ HZ tr H g := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr X hX
  obtain ⟨-, -, hjh, -⟩ := FG.chain_invariants _ _ _ hc
  by_contra hlt
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults
    have hn := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn h3; omega
  obtain ⟨Y, hYX, att, hatt, hattH, hatth⟩ :=
    Store.exists_honest_att_of_lt hr hq hX (HZ tr H g + 1) (by clear * -; omega) (by
        clear * - hjh hlt; omega)
  have hY : Y ∈ (tr.state y k).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases Compose.tree_cases hp.run.toLocalRun hy hY with rfl | ⟨i, hik, hA⟩
  · cases hatt
  obtain ⟨j, hji, hj⟩ := hp.run.att_unforgeable y hy i att (Or.inr ⟨Y, ⟨true, hA⟩, hatt⟩) hattH
  have := hp.reset.2 _ hattH j att hj hatth
  have := hk j (by clear * - hik hji; omega)
  linarith

/-- **HBoot, the caches before the reset.** At a state all of whose earlier cuts are before `a`: no
honest `Σ.J` is high (a justification at `h ≥ H_z + 1` needs an honest attestation at `h`, none
before `a`, HR.1 (c)), and `Σ.F`, of height `≤ H_z` (no chain has crossed `H_z + 1`, G0.2 (a)), is
below every high origin: its finality quorum meets the crossing quorum on a counted head's chain at
its height in an honest validator (G1.2, G0.5, `f < 2q − n`). -/
theorem ResetPremisesUpTo.boot_caches {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  obtain ⟨hFm, -, -, ⟨X, hX, -, hXj⟩, -, -, ⟨Y, hY, hYF⟩⟩ := Store.cache_invariants _ _ _ _ hr
  refine ⟨by rw [← hXj]; exact hp.hj_le_HZ_of_before hy hk hX, fun x i j B ho => Or.inl ?_⟩
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr Y hY
  obtain ⟨-, hFj, -⟩ := FG.chain_invariants _ _ _ hc
  have := hp.hj_le_HZ_of_before hy hk hY
  have := ho.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := hp.highOrigin_mem ho
  exact finalized_anc_of_height_lt_of_run hp.run hp.noColl hp.faults
    hy ho.1 hY hFm hYF.symm hBx (by omega)

/-- Whole-run specialization of the pre-reset cache bounds. -/
theorem boot_caches (hp : ResetPremises tr H K proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B :=
  (hp.toUpTo tr H (le_refl a)).boot_caches hy hk

/-- **`Carry` at a first-transfer vote.** At an honest vote of slot `j + 1` at which `B` is not
below `fc_root` (so `Σ.F ⪯ B`), the voter holds the counted votes of the origin and has accepted
their heads before `t_j + 3Δ`: the heads, of height `≥ H_z + 1`, were first accepted after `c_z`
and before `t_j + 2Δ`, and extend `Σ.F`, so acceptance relay delivers them. -/
theorem ResetPremisesUpTo.first_carry_of_finalized_anc {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨ℓw, D, hcw, hflD, rfl⟩ := hfl
  obtain ⟨ℓ', hc', hD⟩ := fastLock_mem hflD
  obtain rfl : ℓw = ℓ' := Option.some.inj (hcw.2.symm.trans hc'.2)
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (AC.frameIn_of_callAt hr ho.1 hcw).2 (AC.anc_viableAncestor _ D)
  have hW := fastLock_writer hr hp.run.vstart ho.1 hflD
  have hgj : g ≤ sp.ts j := by
    have := hp.cutZ_le_ts_of_highOrigin ho
    have := lt_cutZ sp g
    have := AC.le_gbar g
    have := sp.toParams.hΔ
    linarith
  refine carryAt_of_writer_window hr hp.run.vstart (hp.sync.syncAC hp.run le_rfl) hgj
    le_rfl ho.1 hy hc hs fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hDHv, h₃⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans (hBD.trans hDHv), Or.inr ?_⟩
  have hBHv := hBD.trans hDHv
  obtain ⟨z, hz, k₀, hHvz⟩ := hHv
  rcases h₃ with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (hp.cutZ_lt_of_anc ho hz hHvz hBHv).2
  refine ⟨kw, hkw, ?_, hkwt⟩
  have := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hkw) hBHv).1
  have := lt_cutZ sp g
  have := AC.le_gbar g
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  change g ≤ tr.time kw
  linarith

/-- Whole-run specialization of the first carry. -/
theorem first_carry_of_finalized_anc (hp : ResetPremises tr H K proposer dg g ΔF a) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV :=
  (hp.toUpTo tr H (le_refl a)).first_carry_of_finalized_anc k ho hfl hy hc hs hF

/-- **`Carry` at a later vote.** At an honest vote of slot `m' + 1`, `m' > j`, at which `B` is not
below `fc_root`, the voter holds the honest slot-`m'` votes and has accepted their heads (which
extend `B`, by the earlier votes, hence `Σ.F`) before `t_{m'} + 3Δ`, by relay. -/
theorem ResetPremisesUpTo.later_carry_of_finalized_anc {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', AC.VoteAt tr.projAC z q e' →
      e'.msg.slot = m' → AC.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hU := hr.coherent
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hone : ∀ v ∈ Compose.honestVotes tr H m',
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' {v} := by
    rintro v ⟨z, hz, k', e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk' := (AC.castAt_specU hr.toU hz ⟨hck, he'⟩).2.1
    have hk'k : k' < k := by
      by_contra hkk
      have h₁ := AC.slot_mono sp (hr.time_nonneg k) (hr.time_mono (not_lt.mp hkk))
      have h₂ := (AC.castAt_specU hr.toU hy hc).2.1
      change e'.msg.slot = m' at hvs
      clear * - hm' hk' h₁ h₂ hvs; omega
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz k' hk'k e' ⟨ℓk, hck, he'⟩ hvs
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := Compose.cast_head_fcRoot hr
        hp.run.vstart hz ⟨hck, he'⟩
    obtain rfl : Hd = Hv :=
      hU.1 ((AC.frameIn_of_callAt hr hz hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.projAC.time k' < sp.ts m' + 2 * sp.Δ := by
      change e'.msg.slot = m' at hvs
      rw [hvs] at hkt
      linarith
    have hgm : g ≤ sp.ts m' := by
      have := hp.cutZ_le_ts_of_highOrigin ho
      have := lt_cutZ sp g
      have := AC.le_gbar g
      have := (AC.ts_le_iff sp).mpr (show (j : Int) ≤ m' by clear * - hjm; omega)
      linarith
    refine carryAt_of_writer_window hr hp.run.vstart (hp.sync.syncAC hp.run le_rfl)
      hgm le_rfl hz hy hc hm' ?_
    rintro v rfl
    refine ⟨hvs, ⟨k', ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (AC.ts_le_iff_le_slot sp (hr.time_nonneg k') m').2 (by clear * - hvs hk'; omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases Compose.frame_anc_acceptedU hr.toU hz k' ℓk hck Hd hHd Hd .refl
        with hg | ⟨k'', hk'', hacc⟩
    · exact Or.inl hg
    refine Or.inr ⟨k'', hacc, ?_, lt_of_le_of_lt (hr.time_mono hk'') hkt'⟩
    have := (hp.cutZ_lt_of_anc ho hz (hp.acceptAt_mem hz hacc) hBHv).1
    have := lt_cutZ sp g
    have := AC.le_gbar g
    change g ≤ tr.time k''
    linarith
  exact ⟨hr.awake_of_call y hy k ℓ hc.1, (AC.castAt_specU hr.toU hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- Whole-run specialization of later carry. -/
theorem later_carry_of_finalized_anc (hp : ResetPremises tr H K proposer dg g ΔF a) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', AC.VoteAt tr.projAC z q e' →
      e'.msg.slot = m' → AC.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') :=
  (hp.toUpTo tr H (le_refl a)).later_carry_of_finalized_anc k ho hy hc hm' hjm hF hprior

/-- The finite healthy interval contains the predecessor votes used by transfer: the honest
members of the slot-`m` committee vote, and fewer than half of it is faulty. -/
theorem ResetPremisesUpTo.half_committee {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) {m : Nat}
    (hm : cutZ sp.toParams g ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b) :
    sp.committeeSize ≤
      2 * {z | z ∈ H ∧ ∃ q e, AC.VoteAt tr.projAC z q e ∧ e.msg.slot = m}.ncard := by
  have hΔ := sp.toParams.hΔ
  have hgt : AC.gbar g ≤ sp.ts m + sp.Δ := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ sp.ts m + sp.Δ := (AC.gbar_nonneg g).trans hgt
  have hsl : sp.slot (sp.ts m + sp.Δ) = m :=
    AC.slot_of_mem sp m (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  have hm3 : sp.slot (AC.gbar g) + 3 ≤ m := by
    have h := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hm)
    exact_mod_cast h
  have hsub : K.committee m ∩ H ⊆
      {z | z ∈ H ∧ ∃ q e, AC.VoteAt tr.projAC z q e ∧ e.msg.slot = m} := by
    rintro y ⟨hyK, hy⟩
    have hj : tr.JoinedAt y (sp.ts m + sp.Δ) := fun k hk hkt => by
      change 0 < sp.slot (sp.ts m + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
      rw [hsl, sp.slotTime_eq]
      exact ⟨by omega, (restart_le_before hp hy hk (hkt.trans hmb)).trans
        ((AC.ts_le_iff sp).mpr (by exact_mod_cast (show sp.slot (AC.gbar g) + 1 ≤ m - 1 by
            clear * - hm3; omega)))⟩
    obtain ⟨q, e, hv, he, -⟩ := Compose.vote_of_awake_joined hp.run hp.noColl hy
      (fun i => (hp.mayVote_iff hy i m).2 hyK) (hp.awake y hy _ hgt hmb) hj
    exact ⟨hy, q, e, hv, he⟩
  have hle := Set.ncard_le_ncard hsub
  have hsplit : (K.committee m ∩ H).ncard + (K.committee m ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hp.hsize m]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hf := hp.cs2 (s := m) (by clear * - hm3; omega)
  omega

/-- **Half of the committee votes** (`Healthy(g)`): in a slot `s'` with `t_{s'} ≥ c_z`, every
honest member of the slot-`s'` committee is awake and joined (no honest restart after `max(g, 0)`)
and votes by `t_{s'} + Δ` (`tryVote`), and fewer than half of the committee is faulty (CS2). -/
theorem half_committee (hp : ResetPremises tr H K proposer dg g ΔF a) {s' : Nat}
    (hs : cutZ sp.toParams g ≤ sp.ts s') :
    sp.committeeSize ≤
      2 * {x' | x' ∈ H ∧ ∃ j e', AC.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard :=
  (hp.toUpTo tr H (le_max_left a (sp.ts s' + sp.Δ))).half_committee hs (le_max_right _ _)

end Consensus.Goldilocks.Healing

end
