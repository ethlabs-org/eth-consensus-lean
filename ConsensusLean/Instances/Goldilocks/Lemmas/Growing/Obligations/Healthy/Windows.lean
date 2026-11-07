module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset's service windows under growing faults

The finite reset service, read on the prefix through a read time `d`, is the static service of
the validators honest at `d` (`ResetService.upTo_at`: every sender and recipient of the prefix is
honest at its own cut). From it, the static AC synchrony window at the reset on that prefix
(`sync_window_at_reset_at`), the input of the served head of a reader at `d`. The restart bound
and the late fault bound read each node's honesty at its own time (`restart_le_before_at`,
`fault_bound_late_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The service on a prefix**: the finite reset service, read on the prefix through `d ≥ 0`, is
the static reset service of the validators honest at `d`. -/
theorem ResetService.upTo_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {b : Time} (hs : ResetService tr H g ΔF b) {d : Time} :
    Healing.ResetService (tr.upTo d) (H d) g ΔF b := by
  have hm := hrun.time_mono
  refine ⟨hs.deltaF, ?_, ?_, ?_, ?_⟩
  · intro x hx i m hsa y hy j hj hdl
    obtain ⟨hid, hsa⟩ := (RunTrace.upTo_sendOrAdmitAt hm).mp hsa
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.message x i m (hrun.antitone hid hx) hsa y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_processMsgAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB y hy j hj hdl
    have hB' : (tr.time i ≤ d) ∧ (tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B) := by
      rcases hB with hB | hB
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
        exact ⟨h, Or.inl hB⟩
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_ownBlockAt (tr := tr)).mp hB
        exact ⟨h, Or.inr hB⟩
    obtain ⟨hid, hB⟩ := hB'
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.block x i B (hrun.antitone hid hx) hB y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_blockCallAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB hgi y hy j hj hdl hF
    obtain ⟨hid, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    have hd0 : 0 ≤ d := (hrun.time_nonneg j).trans hjd
    rw [RunTrace.upTo_state_of_le hm hjd] at hF
    obtain ⟨k, hkj, hak, hkd⟩ := hs.relay x i B (hrun.antitone hid hx) hB hgi y j
      (hrun.antitone hjd hy) hj hdl (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hk, hak⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i att hsg y hy j hj hjb hdl
    obtain ⟨hid, hsg⟩ := (RunTrace.upTo_signAt (tr := tr)).mp hsg
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hpk, hkd⟩ :=
      hs.signedRow x i att (hrun.antitone hid hx) hsg y j (hrun.antitone hjd hy) hj hjb hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_processAttAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩

/-- **AC synchrony from the reset on the prefix through `t`**: for the validators honest at `t`,
over the blocks they hold on that prefix, from any source time `a ≥ g` through `t`. -/
theorem sync_window_at_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {b : Time} (hs : ResetService tr H g ΔF b) {t : Time} (hga : g ≤ a) (ht0 : 0 ≤ t) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) := by
  have hsy := (hs.upTo_at hrun (d := t)).syncAC (hi := t) (hrun.upTo ht0) hga
  rw [RunTrace.upTo_projAC] at hsy
  have hsource : ∀ y j (u : Time),
      u ≤ ACTrace.deadline (A := goldilocksNode sp ro) (tr.projAC.upTo t) y j u := by
    intro y j u
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases ACTrace.lastWake (A := goldilocksNode sp ro) (tr.projAC.upTo t) y j with
    | bot => change u ≤ u + sp.Δ; linarith
    | coe w =>
      change u ≤ max u w + sp.Δ
      have := le_max_left u w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj ht hd
    exact hsy.1 x hx i m hm hi ((hsource y j _).trans ht) y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj ht hd hF
    exact hsy.2 x hx i B hB hi ((hsource y j _).trans ht) y hy j ell hj hd hF

/-- **A restart of a node honest at it is no later than the slot after `ḡ`**: the node is awake
from `ḡ` on while honest, and ticks at the public time `t_{slot(ḡ)+1}`. -/
theorem restart_le_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hp.run.sleep_of_restart y k hy hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hp.awake y u (hp.run.antitone huk.le hy) hgu (huk.le.trans hkb))
  · have hlt' := (lt_of_not_ge hlt).le
    obtain ⟨j, _x, hne, hcs, -⟩ := hp.run.tick_of_awake y _ (hp.run.antitone hlt' hy)
      ((SA.gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      (hp.awake y _ (hp.run.antitone hlt' hy) hp₀ (hlt'.trans hkb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hp.run.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- **The late fault bound**: from the cut on, the faults at any `d ∈ [t, b]` are fewer than the
validators honest at `d` that are awake and joined at `t`. -/
theorem fault_bound_late_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (SA.gbar_nonneg g).trans hgt
  have hs : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H d ⊆ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    intro y hy
    have hyt := hp.run.antitone htd hy
    refine ⟨hy, hp.awake y t hyt hgt (htd.trans hdb), fun k hk hkt => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (restart_le_before_at hp (hp.run.antitone hkt hyt) hk
      (hkt.trans (htd.trans hdb))).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle := Set.ncard_le_ncard hsub
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.faults d (ht0.trans htd) hdb
  have hpos := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  unfold RunTrace.FaultBoundAt
  refine lt_of_lt_of_le ?_ hle
  omega

end Consensus.Goldilocks.Healing.Growing

end
