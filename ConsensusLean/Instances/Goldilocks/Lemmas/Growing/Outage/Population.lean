module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1Proofs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Lemmas.Problem.Facts.Regimes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The outage population at an explicit retained window end -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder)
open Consensus.Goldilocks.Generic

variable {sp : ACParams}

section

variable {A : NodeAC sp.toParams} {tr : RunTrace A}
  {H : Time → Set (Fin sp.n)} {p : EnvPoint (Fin sp.n)}

/-- The ready validators retained through the outage window end. -/
def outageHolders (p : EnvPoint (Fin sp.n)) (c z : Time) : Set (Fin sp.n) :=
  {x | x ∈ (p.retain z).readyAt c z}

/-- The other validators seen awake in the retained look-back window. -/
def outageOpponents (p : EnvPoint (Fin sp.n)) (η c z : Time) : Set (Fin sp.n) :=
  {x | x ∈ (p.retain z).awakeIn (max 0 (z - η)) z \ (p.retain z).readyAt c z}

theorem mem_outageHolders {c z : Time} {x : Fin sp.n} :
    x ∈ outageHolders p c z ↔ x ∈ (p.retain z).readyAt c z := by rfl

theorem mem_outageOpponents {η c z : Time} {x : Fin sp.n} :
    x ∈ outageOpponents p η c z ↔
      x ∈ (p.retain z).awakeIn (max 0 (z - η)) z \ (p.retain z).readyAt c z := by rfl

theorem outageHolders_subset (hb : RunPointBinding tr H p) {c z : Time} :
    outageHolders p c z ⊆ H z := by
  classical
  intro x hx
  exact (hb.2.1 x z).2 (Finset.mem_filter.mp (mem_outageHolders.mp hx)).2.1

theorem outageOpponents_subset (hb : RunPointBinding tr H p) {η c z : Time} :
    outageOpponents p η c z ⊆ H z := by
  classical
  intro x hx
  obtain ⟨_, u, _, _, hh, _⟩ :=
    Finset.mem_filter.mp (Finset.mem_sdiff.mp (mem_outageOpponents.mp hx)).1
  exact (hb.2.1 x z).2 hh

theorem outageHolders_disjoint {η c z : Time} :
    Disjoint (outageHolders p c z) (outageOpponents p η c z) :=
  Set.disjoint_left.2 fun _ h₁ h₂ =>
    (Finset.mem_sdiff.mp (mem_outageOpponents.mp h₂)).2 (mem_outageHolders.mp h₁)

open Classical in
theorem outage_classify (hb : RunPointBinding tr H p) {η c z a : Time}
    (ha : max 0 (z - η) ≤ a) {x : Fin sp.n} {t : Time}
    (hat : a ≤ t) (htz : t ≤ z) (hx : x ∈ H z) (haw : tr.awake x t) :
    x ∈ outageHolders p c z ∪ outageOpponents p η c z := by
  by_cases hr : x ∈ (p.retain z).readyAt c z
  · exact Or.inl (mem_outageHolders.mpr hr)
  · exact Or.inr (mem_outageOpponents.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, t, ha.trans hat, htz, (hb.2.1 x z).1 hx,
        (hb.2.2.1 x t).1 haw⟩, hr⟩))

theorem outage_holder_awake (hb : RunPointBinding tr H p) {c z a : Time}
    (ha : max 0 (z - c - 1) ≤ a) {x : Fin sp.n} (hx : x ∈ outageHolders p c z)
    {t : Time} (hat : a ≤ t) (htz : t ≤ z) : tr.awake x t := by
  classical
  obtain ⟨-, -, hr⟩ := Finset.mem_filter.mp (mem_outageHolders.mp hx)
  exact (hb.2.2.1 x t).2 (hr t (ha.trans hat) htz)

/-- A shifted count at the window end reads the selection at its specified earlier time. -/
theorem outage_opponents_lt_at (hb : RunPointBinding tr H p)
    {cm : Time → Finset (Fin sp.n)} {η c L z : Time} (hη : 0 < η) (hL : 0 ≤ L)
    (hz : 0 ≤ z) (hzh : z ≤ p.horizon)
    (hc : ∀ δ, 0 ≤ δ → δ ≤ η →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) (1 / 2) η c L 0 p.horizon)
    {t : Time} (hne : (cm t).Nonempty)
    (ha : max 0 (z - η) ≤ t) (htz : t ≤ z) :
    ((cm t : Set (Fin sp.n)) ∩
      ((H z)ᶜ ∪ outageOpponents p η c z)).ncard <
      ((cm t : Set (Fin sp.n)) ∩ outageHolders p c z).ncard := by
  classical
  have ht0 := (le_max_left 0 (z - η)).trans ha
  have hsel : max 0 (z - (z - t)) = t := by
    rw [sub_sub_cancel, max_eq_right ht0]
  have hcnt := hc (z - t) (sub_nonneg.mpr htz)
    (by have := (le_max_right 0 (z - η)).trans ha; linarith) z hz hzh
    (by simpa only [hsel] using hne)
  dsimp only at hcnt
  rw [ite_eq_right (not_le.mpr hη), hsel] at hcnt
  have h := EnvPoint.opponents_inter_lt_of_retain (p := p)
    (η := η) (c := c) (t := z) (d := z) (e := p.lookAhead L z) (cm t)
    (le_min (by linarith) hzh) hcnt
  have hf : (H z)ᶜ = (↑(p.faultyAt z) : Set (Fin sp.n)) := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, hb.2.1 x z, EnvPoint.HonestAt, not_not]
  rw [hf]
  change ((↑(cm t) : Set (Fin sp.n)) ∩
    (↑(p.faultyAt z) ∪ ↑((p.retain z).awakeIn (max 0 (z - η)) z \
      (p.retain z).readyAt c z))).ncard <
    ((↑(cm t) : Set (Fin sp.n)) ∩ ↑((p.retain z).readyAt c z)).ncard
  simpa only [← Finset.coe_union, ← Finset.coe_inter, Set.ncard_coe_finset,
    Finset.inter_comm, Finset.union_comm, EnvPoint.retain] using h

/-- At a slot start the shifted selection is exactly the run dictionary's committee. -/
theorem outage_opponents_lt_committee (hb : RunPointBinding tr H p)
    {cm : Time → Finset (Fin sp.n)} {η c L z : Time} (hη : 0 < η) (hL : 0 ≤ L)
    (hz : 0 ≤ z) (hzh : z ≤ p.horizon)
    (hc : ∀ δ, 0 ≤ δ → δ ≤ η →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) (1 / 2) η c L 0 p.horizon)
    {s : Nat} (hne : (cm (sp.ts s)).Nonempty)
    (ha : max 0 (z - η) ≤ sp.ts s) (hsz : sp.ts s ≤ z) :
    ((dictOfTime sp cm).committee s ∩ ((H z)ᶜ ∪ outageOpponents p η c z)).ncard <
      ((dictOfTime sp cm).committee s ∩ outageHolders p c z).ncard := by
  have h := outage_opponents_lt_at hb hη hL hz hzh hc hne ha hsz
  simpa only [dictOfTime, sp.slotTime_eq, AC.ACParams.ts] using h

/-- Disjoint holders turn the opponent comparison into a strict half-committee bound. -/
theorem outage_two_mul_opponents_lt (hb : RunPointBinding tr H p)
    {K : AC.CommitteeDict sp.n} {η c z : Time} {s : Nat}
    (h : (K.committee s ∩ ((H z)ᶜ ∪ outageOpponents p η c z)).ncard <
      (K.committee s ∩ outageHolders p c z).ncard) :
    2 * (K.committee s ∩ ((H z)ᶜ ∪ outageOpponents p η c z)).ncard <
      (K.committee s).ncard := by
  have hd : Disjoint (K.committee s ∩ outageHolders p c z)
      (K.committee s ∩ ((H z)ᶜ ∪ outageOpponents p η c z)) := by
    apply Disjoint.mono Set.inter_subset_right Set.inter_subset_right
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun _ hx hf => hf (outageHolders_subset hb hx),
      outageHolders_disjoint⟩
  have hsum := Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
  have hle : (K.committee s ∩ outageHolders p c z ∪
      K.committee s ∩ ((H z)ᶜ ∪ outageOpponents p η c z)).ncard ≤ (K.committee s).ncard :=
    Set.ncard_le_ncard (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
  omega

end

private theorem outage_retained_count {H : Time → Set (Fin sp.n)} {p : EnvPoint (Fin sp.n)}
    {A : NodeAC sp.toParams} {tr : RunTrace A}
    (hanti : Antitone H) (hb : RunPointBinding tr H p)
    {η c t d e : Time} (htd : t ≤ d)
    (hjoin : ∀ y, y ∈ H t → (∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t)
    (hde : d ≤ e) (S : Finset (Fin sp.n))
    (h : (1 / 2 : ℚ) * ((((p.retain e).readyAt c t ∪
      (p.retain e).awakeIn (max 0 (t - η)) t ∪ (p.retain e).faultyAt t) ∩ S).card : ℚ) <
      (((p.retain e).readyAt c t ∩ S).card : ℚ)) :
    ((S : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard <
      ((S : Set (Fin sp.n)) ∩ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}).ncard := by
  classical
  have hlt := EnvPoint.opponents_inter_lt_of_retain S hde h
  have hsub : p.faultyAt d ∩ S ⊆
      (((p.retain d).awakeIn (max 0 (t - η)) t \ (p.retain d).readyAt c t) ∪
        (p.retain d).faultyAt t) ∩ S :=
    Finset.inter_subset_inter (Finset.subset_union_right) (Finset.Subset.refl _)
  have hf := (Finset.card_le_card hsub).trans_lt hlt
  apply SleepyLayer1.retained_count_of_join hanti hb htd hjoin S
  have hfq : ((p.faultyAt d ∩ S).card : ℚ) < ((p.retain d).readyAt c t ∩ S).card := by
    exact_mod_cast hf
  push_cast
  linarith

/-- **The slot-committee count of the shifted outage family over any node's run**: the
selection at `t_s` has fewer members faulty at `d` than members honest at `d` and awake and
joined at `t_s + δ`, for every shift `δ ∈ [0, η]` and every `d ∈ [t_s + δ, t_s + δ + 5Δ]`
within `b`, from antitone honesty and a joining law. -/
theorem outage_committee_count {A : NodeAC sp.toParams} {tr : RunTrace A}
    {H : Time → Set (Fin sp.n)} (hanti : Antitone H)
    {p : EnvPoint (Fin sp.n)} (hb : RunPointBinding tr H p)
    {cm : Time → Finset (Fin sp.n)} {η c : Time} (hη0 : 0 < η)
    (hjoin : ∀ y t, y ∈ H t → 0 ≤ t →
      (∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t)
    (hK : ∀ δ, 0 ≤ δ → δ ≤ η →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) (1 / 2) η c
        (5 * sp.Δ) 0 p.horizon)
    {b : Time} (hbh : b ≤ p.horizon) {s : Nat} (hne : (cm (sp.ts s)).Nonempty)
    {δ d : Time} (hδ0 : 0 ≤ δ) (hδη : δ ≤ η) (htd : sp.ts s + δ ≤ d) (hdb : d ≤ b)
    (hdl : d ≤ sp.ts s + δ + 5 * sp.Δ) :
    ((cm (sp.ts s) : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard <
      ((cm (sp.ts s) : Set (Fin sp.n)) ∩
        {y | y ∈ H d ∧ tr.awake y (sp.ts s + δ) ∧ tr.JoinedAt y (sp.ts s + δ)}).ncard := by
  have hs0 := ts_natCast_nonneg (sp := sp) s
  have ht0 : 0 ≤ sp.ts s + δ := add_nonneg hs0 hδ0
  have hsel : max 0 (sp.ts s + δ - δ) = sp.ts s := by
    simp only [add_sub_cancel_right, max_eq_right hs0]
  have h := hK δ hδ0 hδη (sp.ts s + δ) ht0 (htd.trans (hdb.trans hbh))
    (by simpa only [hsel] using hne)
  dsimp only at h
  rw [ite_eq_right (not_le.mpr hη0), hsel] at h
  exact outage_retained_count hanti hb htd (fun y hy hw => hjoin y _ hy ht0 hw)
    (le_min hdl (hdb.trans hbh)) (cm (sp.ts s)) h

variable {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Time → Set (Fin sp.n)} {p : EnvPoint (Fin sp.n)}

/-- The shifted outage family supplies the ordinary population and slot-committee bounds.
No constancy of the time-indexed committee inside a slot is assumed. -/
theorem outage_bounds {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hb : RunPointBinding tr H p)
    {cm : Time → Finset (Fin sp.n)} (hpos : 0 < sp.committeeSize)
    (hsize : ∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize)
    {η c : Time} (hη : sp.Δ ≤ η) (hc : Regimes.catchUp sp ≤ c)
    (hp : p.EtaSleepyOn (1 / 2) η c (5 * sp.Δ) 0 p.horizon)
    (hK : ∀ δ, 0 ≤ δ → δ ≤ η →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) (1 / 2) η c
        (5 * sp.Δ) 0 p.horizon)
    {b : Time} (hbh : b ≤ p.horizon) :
    SleepyBoundsFrom tr H 0 b ∧ CommitteeBoundsFrom tr H (dictOfTime sp cm) 0 b := by
  classical
  have hΔ := sp.toParams.hΔ
  have hpop : ∀ t d, 0 ≤ t → t ≤ d → d ≤ b → d ≤ t + 5 * sp.Δ →
      tr.FaultBoundAt H t d := by
    intro t d ht htd hdb hdl
    have h := ((hp t ht (htd.trans (hdb.trans hbh))).readyAbove (by norm_num)).retain_mono
      (le_min hdl (hdb.trans hbh)) (by norm_num) (by norm_num)
    have h' := SleepyLayer1.retained_count hrun hb hc ht htd Finset.univ
      (by simpa only [Finset.inter_univ, EnvPoint.ReadyAbove, EnvPoint.faultCount,
        EnvPoint.retain, Nat.cast_add] using h)
    simpa only [RunTrace.FaultBoundAt, Finset.coe_univ, Set.univ_inter] using h'
  have hB : SleepyBoundsFrom tr H 0 b := by
    apply Obligations.Growing.sleepyBoundsFrom_of_faultBoundAt hrun.antitone
      (a := 0) (add_nonneg (ts_natCast_nonneg (sp := sp) 0) hΔ.le) (le_max_right b 0)
    intro t ht _ htb
    exact hpop t (min (t + 5 * sp.Δ) b) ht
      (le_min (by linarith) htb) (min_le_right _ _) (min_le_left _ _)
  have hne : ∀ s : Nat, (cm (sp.ts s)).Nonempty := by
    intro s
    have hs : (cm (sp.ts s) : Set (Fin sp.n)).ncard = sp.committeeSize := by
      simpa only [dictOfTime, sp.slotTime_eq, AC.ACParams.ts] using hsize s
    exact Finset.card_pos.mp (by simpa using (hpos.trans_eq hs.symm))
  have hjoin : ∀ y t, y ∈ H t → 0 ≤ t →
      (∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t := fun _ _ hy ht hw =>
    Obligations.Growing.ready_implies_joined_at hrun.toLocalRun hy ht
      (SleepyLayer1.join_le_of_catchUp hc) hw
  have hη0 : 0 < η := by linarith
  refine ⟨hB, ?_, ?_⟩
  · intro s d _ htd hdb h6
    have h := outage_committee_count hrun.antitone hb hη0 hjoin hK hbh (hne s) hΔ.le hη htd hdb
      (by linarith)
    simp only [AC.FaultBoundK, dictOfTime, sp.slotTime_eq]
    simp only [AC.ACParams.ts] at h
    apply h.trans_le
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro y hy
    exact ⟨hy.1, hy.2.1, (mem_awakeJoined_projAC hrun).mpr hy.2.2⟩
  · intro s d _ htd hdb h2
    have h := outage_committee_count hrun.antitone hb hη0 hjoin hK hbh (hne s) le_rfl hη0.le
      (by simpa using htd) hdb (by linarith)
    simp only [add_zero] at h
    simp only [dictOfTime, sp.slotTime_eq]
    exact two_mul_inter_compl_lt (fun _ hy => hy.1) h

/-- Population bounds from precisely the local supplier's L9 participation premises. -/
theorem outage_bounds_of_local
    {C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val)}
    {sign : Fin sp.n → Time → Bool} {G : Nat}
    (hC : GoldilocksLocalData sp ro C sign G) {cm : Time → Finset (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    (hrun : C.run.Run cm proposer dg H tr) (hb : RunPointBinding tr H p)
    (hp : p.EtaSleepyOn C.θ C.outageEta (max C.catchUp (C.outageEta - 1))
      C.look 0 p.horizon)
    (hK : ∀ δ, 0 ≤ δ → δ ≤ C.outageEta →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) C.θ C.outageEta
        (max C.catchUp (C.outageEta - 1)) C.committeeLook 0 p.horizon)
    {b : Time} (hbh : b ≤ p.horizon) :
    SleepyBoundsFrom tr H 0 b ∧ CommitteeBoundsFrom tr H (dictOfTime sp cm) 0 b := by
  have hdata := hC.healing.1.1
  rw [hdata] at hrun
  obtain ⟨hrun, hpos, hsize, -⟩ := hrun
  have hη : sp.Δ ≤ C.outageEta := by
    rw [hC.outageEta]
    have hcoeff : (1 : Time) ≤ ((12 * sp.k + 7 : Nat) : Time) := by
      have : 1 ≤ 12 * sp.k + 7 := by omega
      exact_mod_cast this
    linarith [mul_le_mul_of_nonneg_right hcoeff sp.toParams.hΔ.le]
  have hcatch : Regimes.catchUp sp ≤ C.catchUp := by
    rw [hC.catchUp]
    exact le_refl _
  apply outage_bounds hrun hb hpos hsize hη
    (hcatch.trans (le_max_left _ _))
    (by simpa only [hC.θ, hC.look] using hp)
    (by simpa only [hC.θ, hC.committeeLook] using hK) hbh

end Consensus.Goldilocks.Compose.Growing

end
