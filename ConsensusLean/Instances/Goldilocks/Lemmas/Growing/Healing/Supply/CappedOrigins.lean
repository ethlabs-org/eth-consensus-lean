module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksHealing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.DeepQuarantine
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fast-only healing origins within the deep quarantine -/

namespace Consensus.Goldilocks.Generic

open AC (ACParams ReplayOrder Payload)
open Healing (cutZ)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {sign : Fin sp.n → Time → Bool} {G : Nat}

/-- The slot-indexed origin cap is the end of the deep quarantine. -/
theorem goldilocks_origin_cap_bound {g t : Time}
    (hcap : OriginInCap sp.toParams sp.deepDepth g t) :
    ∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ := by
  intro D hD
  have h := hcap D hD
  have hcz : sp.toParams.slotOf (cutZ sp.toParams g) = sp.slot (AC.gbar g) + 3 := by
    rw [Healing.cutZ_eq]
    exact AC.slot_of_mem sp _ le_rfl
      (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
  rw [hcz, sp.slotTime_eq] at h
  rw [Healing.cutZ_eq]
  simp only [ACParams.ts] at h ⊢
  push_cast at h ⊢
  linarith

/-- Restrict the observation horizon without changing the trace or the honest sets. The
snapshot cut must itself fit within the smaller horizon. -/
theorem goldilocks_premises_before
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time} {g ΔF b c : Time}
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hcb : c ≤ b) (hsnap : ∃ k, Healing.FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ c) :
    Premises tr H cm βK proposer dg (fun v => v.val) g ΔF c hold := by
  have hr := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  refine { hp with
    committee := ?_
    sync := { hp.sync with signedRow := ?_ }
    awake := fun y t hy hgt htc => hp.awake y t hy hgt (htc.trans hcb)
    faults := fun t ht htc => hp.faults t ht (htc.trans hcb)
    snapshot := hsnap
    nonempty := hp.nonempty.mono (hr.antitone hcb) }
  · intro t d hgt htc hd hdc hne
    exact hp.committee t d hgt (htc.trans hcb) hd (hdc.trans hcb) hne
  · intro x i att hx hs hhold y j hy hj hjc hdeadline
    exact hp.sync.signedRow x i att hx hs hhold y j hy hj (hjc.trans hcb) hdeadline

/-- A finite deep stamp of a report made before the snapshot puts its honest FG acceptance
at least one slot before the snapshot, even at depth zero. -/
theorem deep_report_acceptance_before_cut
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hto : AC.ToFGAt tr.projAC y i ell R)
    (hRi : R ∈ (tr.state y i).fg.tree) (hRg : R.root ≠ sp.genesisRoot)
    (hi : tr.time i < cutZ sp.toParams g) {D : Nat}
    (hst : (tr.state y i).ac.blockStamp R.root ≤
      AC.ETime.of (sp.ts ((sp.slot (tr.time i) : Int) - D))) :
    ∃ k < i, y ∈ H (tr.time k) ∧ tr.AcceptAt y k R ∧
      tr.time k ≤ cutZ sp.toParams g - 4 * sp.Δ := by
  have hd := hrun.time_nonneg i
  have hr := hrun.upTo hd
  have hs : ∀ m ≤ i, (tr.upTo (tr.time i)).state y m = tr.state y m :=
    fun m hm => Trace.upTo_state tr y (fun q hq => hrun.time_mono (hq.le.trans hm))
  rcases Healing.tree_accepted hr.toLocalRun hy (by rw [hs i le_rfl]; exact hRi) with
    rfl | ⟨k, hki, ha⟩
  · exact absurd rfl hRg
  obtain ⟨ell', hc', hcall', ht'⟩ := Compose.accept_next hr.toLocalRun hy ha
  have hk1 : k + 1 < i := by
    rcases (Nat.succ_le_of_lt hki).lt_or_eq with h | h
    · exact h
    · subst i
      have hc := (Healing.Growing.toFGAt_upTo_iff hrun.time_mono le_rfl).mpr hto
      obtain ⟨hc, ht, -⟩ := hc
      have he := Option.some.inj ((Compose.projAC_callAt.mp hc).2.symm.trans hc'.2)
      cases he
      rw [hcall'] at ht
      cases ht
  have hstamp := Compose.blockStamp_ge_of_accept
    (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun hy
    ⟨ell', Compose.projAC_callAt.mpr hc', hcall'⟩ hRg i hk1
  rw [Compose.projAC_state hr.toLocalRun hy i, hs i le_rfl] at hstamp
  change AC.ETime.of ((tr.upTo (tr.time i)).time (k + 1)) ≤ _ at hstamp
  rw [ht', Trace.upTo_time] at hstamp
  have hkt := AC.etime_of_le_of.1 (hstamp.trans hst)
  have hslot : (sp.slot (tr.time i) : Int) < sp.slot (AC.gbar g) + 3 := by
    by_contra h
    have ht := (AC.ts_le_iff_le_slot sp hd _).2 (not_lt.1 h)
    rw [Healing.cutZ_eq] at hi
    norm_cast at ht
    exact (not_le_of_gt hi) ht
  have hle : sp.ts ((sp.slot (tr.time i) : Int) - D) ≤
      cutZ sp.toParams g - 4 * sp.Δ := by
    rw [Healing.cutZ_eq]
    have ht := (AC.ts_le_iff sp).2
      (show (sp.slot (tr.time i) : Int) - D ≤ sp.slot (AC.gbar g) + 2 by omega)
    simp only [ACParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith
  exact ⟨k, hki, hrun.antitone (hrun.time_mono hki.le) hy,
    ((RunTrace.upTo_acceptAt _).mp ha).2, hkt.trans hle⟩

/-- An acceptance at least one slot before the snapshot cannot have height above its frontier:
an honest snapshot receiver catches it before that snapshot, even if its sender is corrupted. -/
theorem accepted_before_cut_height_le
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time} {g ΔF b : Time}
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    {x : Fin sp.n} {k : Nat} (hx : x ∈ H (tr.time k))
    {R : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.AcceptAt x k R)
    (hk : tr.time k ≤ cutZ sp.toParams g - 4 * sp.Δ) :
    ((tr.state x (k + 1)).fg.σ R.root).h ≤ Healing.Growing.HZ tr H g := by
  have hΔ := sp.toParams.hΔ
  have hg0 := AC.gbar_nonneg g
  have hcut : AC.gbar g + 8 * sp.Δ < cutZ sp.toParams g := by
    have ht := (AC.ts_le_iff_le_slot sp hg0 (sp.slot (AC.gbar g) + 1)).not.mpr
      (show ¬ (sp.slot (AC.gbar g) + 1 : Int) ≤ sp.slot (AC.gbar g) by omega)
    rw [Healing.cutZ_eq]
    simp only [ACParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith [not_le.mp ht]
  obtain ⟨qZ, hZ, hZb⟩ := hp.snapshot
  have hcb : cutZ sp.toParams g ≤ b := hZ.2.le.trans hZb
  obtain ⟨y, hyb⟩ := hp.nonempty
  have hyZ := hrun.antitone hcb hyb
  have tick_call : ∀ t, AC.gbar g ≤ t → t ≤ cutZ sp.toParams g → sp.toParams.IsPublic t →
      ∃ j, tr.IsCall y j ∧ tr.time j = t := by
    intro t hgt htc hpub
    have hyt := hrun.antitone htc hyZ
    obtain ⟨j, xt, f, hne, hcs, -⟩ := hrun.tick_of_awake y t hyt
      (hg0.trans hgt) hpub (hp.awake y t hyt hgt (htc.trans hcb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    exact ⟨j, ⟨_, hn, hl⟩, ht⟩
  have hpub (d : Int) : sp.toParams.IsPublic (cutZ sp.toParams g - d * sp.Δ) := by
    refine ⟨4 * (sp.slot (AC.gbar g) + 3 : Nat) - d, ?_⟩
    rw [Healing.cutZ_eq]
    simp only [ACParams.ts]
    push_cast
    ring
  obtain ⟨j, hj, hjt⟩ := tick_call (cutZ sp.toParams g - 2 * sp.Δ)
    (by linarith) (by linarith) (hpub 2)
  obtain ⟨m, -, hmt⟩ := tick_call (cutZ sp.toParams g - sp.Δ)
    (by linarith) (by linarith) (by simpa using hpub 1)
  have hmZ : m ≤ qZ := by
    by_contra h
    have := hrun.time_mono (show qZ ≤ m by omega)
    linarith [hZ.2]
  have hy := hrun.antitone (show tr.time m ≤ cutZ sp.toParams g by linarith) hyZ
  have hs : ∀ n ≤ qZ, (tr.upTo (cutZ sp.toParams g)).state y n = tr.state y n :=
    fun n hn => Trace.upTo_state tr y (fun r hr => hZ.1 r (hr.trans_le hn))
  have hmmax : (tr.state y m).fg.hmax ≤ Healing.Growing.HZ tr H g := by
    have hmono := Healing.hmax_mono (hrun.upTo (by linarith : 0 ≤ cutZ sp.toParams g)).toLocalRun
      hyZ hmZ
    simp only at hmono
    rw [hs m hmZ, hs qZ le_rfl] at hmono
    apply hmono.trans
    refine le_csSup (((Set.finite_range fun z => (tr.state z qZ).fg.hmax).subset ?_).bddAbove)
      ⟨y, hyZ, qZ, hZ, rfl⟩
    rintro _ ⟨z, -, q', hq', rfl⟩
    obtain rfl := hq'.unique hZ
    exact ⟨z, rfl⟩
  have hRk : R ∈ (tr.state x (k + 1)).fg.tree := by
    have h := Healing.accept_mem_from (hrun.upTo (hrun.time_nonneg k)).toLocalRun hx
      ((RunTrace.upTo_acceptAt _).mpr ⟨le_rfl, ha⟩)
    rwa [Trace.upTo_state tr x (fun r hr => hrun.time_mono (by omega))] at h
  by_contra hhigh
  have hh : (tr.state y m).fg.hmax ≤ ((tr.state x (k + 1)).fg.σ R.root).h := by omega
  have hf : (H (max (tr.time k) (tr.time m)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.toParams.n := by
    have h3 := hp.faults (max (tr.time k) (tr.time m))
      ((hrun.time_nonneg k).trans (le_max_left _ _)) (max_le (by linarith) (by linarith))
    have hn := sp.toParams.hn
    change 3 * _ ≤ sp.toParams.n - 1 at h3
    change _ < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have hRm := held_of_relay_le_at_from hrun.toLocalRun hp.noColl hp.sync hp.catchUp
    (hrun.time_nonneg k) hx hy hf hRk hh
    (fun r hr => hrun.time_mono (by omega))
    (by
      refine ⟨j, ?_, hj, ?_⟩
      · by_contra h
        have := hrun.time_mono (show m ≤ j by omega)
        linarith
      · have hd := Compose.deadline_le_of_restarts (tr := tr)
          (fun r hr hrs => hp.noRestart y r
            (hrun.antitone ((hrun.time_mono hr).trans
              (by linarith : tr.time j ≤ tr.time m)) hy) hrs)
          (max (tr.time k) g) sp.Δ
        have hgg := AC.le_gbar g
        have hmax : max (max (tr.time k) g) (AC.gbar g) ≤
            cutZ sp.toParams g - 3 * sp.Δ := max_le
          (max_le (by linarith) (by linarith)) (by linarith)
        linarith)
    (by linarith : AC.gbar g + 2 * sp.Δ ≤ tr.time m)
  have he := σ_eq_honest_at_from hrun.toLocalRun hp.noColl
    (hrun.time_nonneg k) (fun r hr => hrun.time_mono (by omega)) hx
    (hrun.time_nonneg m) (fun r hr => hrun.time_mono hr.le) hy hRk hRm
  have hbound := (Store.cache_invariants _ _ _ _
    (fg_reachable_at_from hrun.toLocalRun (hrun.time_nonneg m)
      (fun r hr => hrun.time_mono hr.le) hy)).2.2.2.2.1 R hRm
  rw [← he] at hbound
  omega

/-- Every high report within the cap is a fast candidate. Before the snapshot, the deep
stamp and acceptance relay contradict the snapshot height even for a later-corrupted reporter. -/
theorem high_report_fast_of_cap
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time} {g ΔF b : Time}
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hto : AC.ToFGAt tr.projAC y i ell R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h)
    (hq : ∀ D, sp.deepDepth = some D → tr.time i ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    R ∈ AC.toFGCandidates sp (tr.state y i).ac ell.frame (tr.time i) := by
  by_cases hi : cutZ sp.toParams g ≤ tr.time i
  · exact Healing.Growing.KernelProof.high_toFG_fast_at hrun hp.noColl
      (hp.snapshot.imp fun _ h => h.1) (by rwa [max_eq_right hi]) hto hh hq
  have hbefore : tr.time i < cutZ sp.toParams g := lt_of_not_ge hi
  have hsource := hto.2.2
  rw [Compose.Growing.projAC_state_at hrun hy] at hsource
  obtain ⟨-, hfast | ⟨D, a, -, -, -, hdeep⟩⟩ := AC.toFG_source hsource
  · exact hfast
  have hRi := Healing.Growing.toFG_mem_tree_at hrun hy hto
  obtain ⟨k, hki, hx, ha, hk⟩ := deep_report_acceptance_before_cut hrun hp.noColl hy hto
    hRi hdeep.2.2.1 hbefore hdeep.2.2.2
  have hRk : R ∈ (tr.state y (k + 1)).fg.tree := by
    have h := Healing.accept_mem_from (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy
      ((RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono hki.le, ha⟩)
    rwa [Trace.upTo_state tr y (fun r hr => hrun.time_mono (by omega))] at h
  have he := σ_eq_honest_at_from hrun.toLocalRun hp.noColl
    (hrun.time_nonneg i) (fun r hr => hrun.time_mono (by omega)) hy
    (hrun.time_nonneg i) (fun r hr => hrun.time_mono hr.le) hy hRk hRi
  have hbound := accepted_before_cut_height_le hrun hp hx ha hk
  rw [he] at hbound
  omega

/-- A high report inside the quarantine has an earlier fast-only origin. The reporter is
honest both at the report and at the high-state snapshot. -/
theorem goldilocks_report_origin_of_quarantine
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time} {g ΔF a b : Time}
    (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hcap : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (max (cutZ sp.toParams g) (tr.time i))) (hib : tr.time i ≤ b)
    (hR : ReportAt tr y i R) (hh : Healing.Growing.HZ tr H g + 1 ≤
      ((tr.state y i).fg.σ R.root).h) :
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧
      (tr.JoinedAt y (tr.time r) ∧ ∃ CV, Compose.StoredFastLockAt tr y r j B CV) ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B := by
  have hq := resetPremisesUpTo_of_premises hβ hrun hp hr hab
    (fun D hD => Or.inl (hcap D hD))
  have hyi := hq.run.antitone (le_max_right _ _) hy
  obtain ⟨ell, hc, hto, hret⟩ := hR
  have hrep : AC.ToFGAt tr.projAC y i ell R := by
    refine ⟨Compose.projAC_callAt.mpr hc, hto, ?_⟩
    rw [Compose.Growing.projAC_state_at hq.run hyi]
    exact hret
  obtain ⟨r, hri, j, B, _, _, ho, _, _, hRB, _⟩ :=
    hq.high_report_origin_of_quarantine_at hy hrep hib hh
      (fun D hD => hib.trans (hcap D hD))
  exact ⟨r, hri.le, j, B, hq.run.antitone (le_max_right _ _) ho.1,
    ⟨ho.2.1, ho.2.2.1⟩, Healing.Growing.highOrigin_mem_at hq.run hq.noColl ho, hRB⟩

/-- Two fast-only high origins are compatible while the entire observation horizon remains
inside the deep quarantine. No post-expiry source cover is used. -/
theorem goldilocks_origins_comparable_of_quarantine
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp ro sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hcap : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    {x x' : Fin sp.n} {i j i' j' : Nat} {B B' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (ho : tr.JoinedAt x (tr.time i) ∧ ∃ CV, Compose.StoredFastLockAt tr x i j B CV)
    (hib : tr.time i ≤ b) (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hx' : x' ∈ H (max (cutZ sp.toParams g) (tr.time i')))
    (ho' : tr.JoinedAt x' (tr.time i') ∧ ∃ CV, Compose.StoredFastLockAt tr x' i' j' B' CV)
    (hi'b : tr.time i' ≤ b)
    (hh' : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h) :
    Compatible (tr.HonestBlocksAt H) B B' :=
  (resetPremisesUpTo_of_premises hβ hrun hp hr hab
    (fun D hD => Or.inl (hcap D hD))).origins_compatible_at
      ⟨hx, ho.1, ho.2, hh⟩ hib ⟨hx', ho'.1, ho'.2, hh'⟩ hi'b

end Consensus.Goldilocks.Generic

end
