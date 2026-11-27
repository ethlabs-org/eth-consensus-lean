module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Leaves
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportFollow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow reset rounds (interface-only)

The induction is the existing growing reset-round argument with the P-U window and calendar.
The warm-crossing wrapper uses the concrete leaf in `Leaves`; its remaining proof gap is the
delayed report-follow supplier, not an independent warm-crossing stub.
-/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

private theorem faults_lt_quorum {f n : Nat} (hn : 1 ≤ n) (hf : 3 * f ≤ n - 1) :
    f < 2 * ((2 * n + 2) / 3) - n := by omega

/-- Leaf 11's wrapper for the reset induction, through the delayed report-follow interface. -/
theorem round_of_warm_within_interface
    {g ΔF b T D t₀ : Time} {s₀ u x N M Gs : Nat} {isTop : Prop}
    {J P X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + (D + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) < T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hdx : p = proposer x)
    (hX : tr.ProposesAt p kX X) (hXs : X.slot = x)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h :=
  round_of_warm_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm hδ hlat
    hD hΔF hux hxN hmb hTb hna hT hz hdes hP hPs hp hdx hX hXs hcal hgap ht₀ hδG hK

/-- Proposal acceptance, read in the proposer's prefix rather than a stock run. -/
theorem proposal_mem_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : P ∈ (tr.state p (k + 1)).fg.tree := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hm := (Coherence.accept_of_proposesAt hr (hnc.upTo _) hp hP').2.1
  rwa [Trace.upTo_state tr p (fun q hq => hrun.time_mono (by omega))] at hm

/-- V-B3's induction. Unresolved through warm crossing and proposal report-follow. -/
theorem rise_reset_rounds_within_at
    {g ΔF b T D t₀ : Time} {s₀ N G M Gs : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ) M
      isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + (D + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ +
      (D + (Gs : Time) * sp.Δ) ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ +
        (D + (Gs : Time) * sp.Δ) := by
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  induction r generalizing u z kP P with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_within_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm
        (by simpa using hN) hmb hH hlat hD
        (by simpa only [Nat.zero_mul, Nat.add_zero] using hT.trans hTb)
        hz hdes hP hPs (by simpa using hrise) hcal hgap ht₀ hK
  | succ r ih =>
    let ρ := sp.toParams.fg.δt + G - 1
    have hρ : 3 ≤ ρ := by dsimp [ρ]; omega
    have hmul : (r + 1) * ρ = r * ρ + ρ := Nat.succ_mul r ρ
    change u + (r + 1) * ρ + 1 ≤ N at hN
    change sp.ts (u + (r + 1) * ρ + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) ≤ T at hT
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
      (AC.ts_le_iff sp).2 (by exact_mod_cast h)
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h
    · have hle := hts (show u + 1 ≤ u + (r + 1) * ρ + 1 by omega)
      obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_within_at hframe hrun hnc hsvc hawake hf
        hcatch hnr hm hwarm (by omega) hmb hH hlat hD (by linarith) hz hdes hP hPs hh hcal hgap
        ht₀ hK
      exact ⟨a, ha, hat.trans (by linarith)⟩
    obtain ⟨x, hxl, hxr, hpx, kX, X, hX, hXs⟩ := proposalGap_iff.mp hgp
      (u + sp.toParams.fg.δt) (by omega) (by
        have hδρ : sp.toParams.fg.δt + G ≤ ρ + 1 := by dsimp [ρ]; omega
        omega)
    have htime : tr.time kX = sp.ts x := by
      simpa only [sp.slotTime_eq, hXs, ACParams.ts] using hX.2.2
    have hpx0 : proposer x ∈ H (tr.time kX) := hrun.antitone (by rw [htime]; linarith) hpx
    have hnext : x + r * ρ + 1 ≤ u + (r + 1) * ρ + 1 := by
      have hδρ : sp.toParams.fg.δt + G ≤ ρ + 1 := by dsimp [ρ]; omega
      omega
    have hstrict : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) < T := by
      have hlt : sp.ts (u + 1 : Nat) < sp.ts (u + (r + 1) * ρ + 1 : Nat) :=
        (AC.ts_lt_iff sp).2 (by exact_mod_cast (show u + 1 < u + (r + 1) * ρ + 1 by omega))
      linarith
    obtain ⟨hPX, _, hcross⟩ := round_of_warm_within_interface (N := N)
      (hframe.mono le_rfl (by linarith)) hrun hnc hsvc hawake hf hcatch hnr hm hwarm hδ hlat
      hD hΔF hxl (by omega) (by linarith) hTb hna hstrict hz hdes hP hPs hpx0 rfl hX hXs hcal
      hgap ht₀ hδG hK
    have htP : tr.time kP = sp.ts u := by
      simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
    have hz0 : z ∈ H (tr.time kP) := hrun.antitone (by rw [htP]; linarith) hz
    have hPm := proposal_mem_at hrun hnc hz0 hP
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
      (fun q hq => hrun.time_mono (by omega)) hz0 (hrun.time_nonneg kX)
      (fun q hq => hrun.time_mono (by omega)) hpx0 hPm hPX
    rw [← hσ] at hcross
    have hxN : x + r * ρ + 1 ≤ N := hnext.trans hN
    obtain ⟨a, ha, hat⟩ := ih (u := x) (by omega) hxN
      (by linarith [hts hnext]) hpx rfl hX hXs (by omega)
    exact ⟨a, ha, hat.trans (by linarith [hts hnext])⟩

/-- Same-tick specialization. The zero-latency run supplier is still an explicit premise. -/
theorem rise_reset_rounds_at
    {g ΔF b T t₀ : Time} {s₀ N G M Gs : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ) M
      isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hlat : Generic.VoteLatencyAt tr H 0)
    (hΔF : 6 * sp.Δ + (Gs : Time) * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ +
      (Gs : Time) * sp.Δ ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ +
        (Gs : Time) * sp.Δ := by
  simpa only [zero_add] using rise_reset_rounds_within_at hframe hrun hnc hsvc hawake hf hcatch
    hnr hm hδ hG hlat le_rfl (by simpa only [zero_add] using hΔF) hgp hmb hH hTb hna r
    hwarm hN (by simpa only [zero_add] using hT) hz hdes hP hPs hrise hcal hgap ht₀ hδG hK

/-- Four P-U attempts retain the six rise rounds of the stock five-attempt budget. -/
theorem sum_riseLen_four (d ρ s lam : Time) (HZ : Nat) :
    ∑ j ∈ Finset.range 4, (riseLen d ρ s HZ (2 * HZ + j) + lam) =
      4 * (d + s + lam) + 6 * ρ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, riseLen_eq, riseRounds_eq,
    Nat.add_sub_cancel_left]
  norm_num
  ring

/-- A warm proposal supplier on P-U windows. This is a premise, not a claimed drain proof. -/
structure DrainOutputs (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n)
    (H : Time → Set (Fin sp.n)) (g : Time) (G Ld : Nat) (b : Time) : Prop where
  warm : ∀ {s₀ N M : Nat} {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))},
    Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) M isTop J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → s₀ + Ld ≤ N → sp.ts N + 2 * sp.Δ ≤ b →
    (∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k ≤ sp.ts N + 2 * sp.Δ → att.h ≤ HZ tr H g) →
    ProposalGap tr H proposer G s₀ N →
    ∃ u, s₀ + 2 * sp.k ≤ u ∧ u ≤ s₀ + Ld ∧
      ∃ z kP P, z ∈ H (sp.ts u + sp.Δ) ∧ z = proposer u ∧
        tr.ProposesAt z kP P ∧ P.slot = u ∧
          HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1

/-- Assemble a reset from a supplied constant-key window and a warm drain proposal.
This separates the round argument from the window-search budget, without assuming a reset. -/
theorem exists_reset_in_window
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b af len D t₀ : Time}
    {s₀ N G Ld M v Gs : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H af (af + len) M isTop J)
    (hkey : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      Generic.frameKey'' (goldilocksNode sp ro) (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v)
    (hslo : af ≤ sp.ts s₀)
    (hfit : sp.ts N + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) ≤ af + len)
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + (D + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : af + len ≤ b) (hH : (H b).Nonempty)
    (hna : ∀ w k att, w ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt w k att →
      tr.time k ≤ af + len → att.h ≤ HZ tr H g)
    (hN : s₀ + Ld + riseRounds (HZ tr H g) v * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧ a ≤ af + len := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hΔ)
  have hts {x y : Nat} (h : x ≤ y) : sp.ts x ≤ sp.ts y :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast h)
  have hframe : Generic.FrameWindow tr H (sp.ts s₀)
      (sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ) M isTop J :=
    hwin.mono hslo (by linarith)
  obtain ⟨u, hwarm, huLd, z, kP, P, hz, hdes, hP, hPs, _⟩ := hdrain.warm
    (hframe.mono le_rfl (by linarith)) hm (by omega) (by linarith)
    (fun w k att hw hs hk => hna w k att hw hs (by linarith)) hgp
  have huN : u + riseRounds (HZ tr H g) v * (sp.toParams.fg.δt + G - 1) + 1 ≤ N := by omega
  have hz0 : z ∈ H (sp.ts u) := hrun.antitone (by linarith) hz
  have hulo : af ≤ sp.ts u := hslo.trans (hts (by omega))
  have huhi : sp.ts u ≤ af + len := by linarith [hts (show u ≤ N by omega)]
  have hrise := rounds_le_warm_proposal_at hrun hnc hwin hkey hv hulo huhi hz0 hdes hP hPs
    (faults_lt_quorum sp.toParams.hn
      (hf (sp.ts u) (by change 0 ≤ 4 * sp.Δ * (u : Time); positivity) (huhi.trans hmb)))
  obtain ⟨a, ha, hat⟩ := rise_reset_rounds_within_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hm hδ hG hlat hD hΔF hgp (by linarith) hH hmb
    (fun w k att hw hs hk => hna w k att hw hs hk.le)
    (riseRounds (HZ tr H g) v) hwarm huN
    (by linarith [hts huN]) hz hdes hP hPs hrise hcal hgap ht₀ hδG hK
  exact ⟨a, ha, hat.trans (by linarith [hts huN])⟩

/-- Reset assembly from the four-attempt search. Range and relay calls remain explicit
until the generic snapshot/awake wrappers are ported; no reset is assumed in either premise. -/
theorem exists_reset
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b lo D t₀ : Time} {G Ld Gs : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hΔF : 6 * sp.Δ + (D + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hlo0 : 0 ≤ lo) (hlo : gbar g + 4 * sp.Δ ≤ lo)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < b →
      HZ tr H g ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ tr H g + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + 2 * sp.Δ ≤ tr.time m → tr.time m < b →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hbudget : lo + ∑ j ∈ Finset.range 4,
      (riseLen (4 * sp.Δ * ((Ld : Time) + 2))
        (4 * sp.Δ * ((sp.toParams.fg.δt + G - 1 : Nat) : Time))
        (2 * sp.Δ - 1 + (D + (Gs : Time) * sp.Δ)) (HZ tr H g)
        (2 * HZ tr H g + j) + 2 * sp.Δ) < b)
    (hna : ∀ w k att, w ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt w k att →
      tr.time k ≤ b → att.h ≤ HZ tr H g)
    (hgp : ∀ s₀ N : Nat, lo ≤ sp.ts s₀ → sp.ts N + 2 * sp.Δ ≤ b →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ lo)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) : ∃ a, IsReset tr H g a ∧ a ≤ b := by
  let d := 4 * sp.Δ * ((Ld : Time) + 2)
  let rt := 4 * sp.Δ * ((sp.toParams.fg.δt + G - 1 : Nat) : Time)
  let slack := 2 * sp.Δ - 1 + (D + (Gs : Time) * sp.Δ)
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hΔ)
  have hlen := riseLen_nonneg (show 0 ≤ d by dsimp [d]; positivity)
    (show 0 ≤ rt by dsimp [rt]; positivity)
    (show 0 ≤ slack by dsimp [slack]; linarith) (HZ tr H g)
  obtain ⟨v, hv, hvhi, af, haf, hend, hkey, M, isTop, J, hwin⟩ :=
    exists_frameWindow'_seq_of_service_proof_at hrun hnc
      (fun t ht htb => faults_lt_quorum sp.toParams.hn (hf t ht htb))
      hsvc hcatch (riseLen d rt slack (HZ tr H g)) hlen (by linarith)
      (by linarith) le_rfl hrange hcall hbudget
  let len := riseLen d rt slack (HZ tr H g) v
  have hsub : ∑ j ∈ Finset.range (v - 2 * HZ tr H g + 1),
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * sp.Δ) ≤
      ∑ j ∈ Finset.range 4,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * sp.Δ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) (by linarith))
  have hwinb : af + len ≤ b := by linarith
  obtain ⟨s₀, hslo, hshi⟩ := Generic.exists_slot_align_of_grid (P := sp.toParams)
    (fun s => by rw [sp.slotTime_eq]; ring) af (by linarith)
  replace hslo : af ≤ sp.ts s₀ := by rw [sp.slotTime_eq] at hslo; exact hslo
  let rr := riseRounds (HZ tr H g) v
  let ρ := sp.toParams.fg.δt + G - 1
  let N := s₀ + Ld + rr * ρ + 1
  have hNtime : sp.ts N = 4 * sp.Δ * ((s₀ : Time) + Ld + (rr : Time) * (ρ : Time) + 1) := by
    change 4 * sp.Δ * (N : Time) = _
    dsimp [N]
  have hlenEq : len = 4 * sp.Δ * ((Ld : Time) + (rr : Time) * (ρ : Time) + 2) + slack := by
    dsimp [len, rr]
    rw [riseLen_eq]
    dsimp [d, rt, ρ]
    ring
  have hfit : sp.ts N + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) ≤ af + len := by
    rw [hNtime, hlenEq]
    change 4 * sp.Δ * (s₀ : Time) < af + 4 * sp.Δ at hshi
    have halign := Int.le_sub_one_of_lt hshi
    dsimp [slack]
    linarith only [halign]
  obtain ⟨a, ha, hat⟩ := exists_reset_in_window hrun hnc hwin hkey hv hslo hfit hsvc hawake hf
    hcatch hnr (by linarith) hδ hG hlat hD hΔF
    (hgp s₀ N (by linarith) (by linarith)) hwinb hH
    (fun w k att hw hs hk => hna w k att hw hs (hk.trans hwinb))
    (show s₀ + Ld + rr * ρ + 1 ≤ N from le_rfl) hdrain hcal hgap (by linarith) hδG hK
  exact ⟨a, ha, hat.trans hwinb⟩

end Consensus.Goldilocks.Healing.Growing.Shadow
