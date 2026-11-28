module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.GenericReset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportFollow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal viability and height leaves for shadow P-U execution -/

namespace Consensus.Goldilocks.Healing

open Consensus.Goldilocks.Generic (riseRounds)

variable {P : Params} {ACP : Type} {st : Store P ACP}

/-- Transported parent viability bounds the proposal and its top-window ancestry. -/
theorem proposal_viable_of_parent {Q B : NodeBlock P ACP}
    (hv : st.IsViable Q) (hh : (st.σ Q.root).h ≤ (st.σ B.root).h)
    (hQB : st.Anc Q B) :
    st.hmax - 1 ≤ (st.σ B.root).h ∧
      (st.hmax = st.hj + 1 → (st.σ B.root).h = st.hmax - 1 → st.Anc st.J B) := by
  rw [Store.isViable_iff] at hv
  constructor
  · rcases hv with hv | ⟨hv, -⟩ <;> omega
  · intro htop hB
    rcases hv with hv | ⟨hv, hgap | hJ⟩
    · omega
    · omega
    · exact hJ.trans hQB

/-- At equal height a proposal's top-window J clause transfers to its report. -/
theorem report_kind_of_proposal_viable {B R : NodeBlock P ACP}
    (hj : st.hj < st.hmax)
    (hB : st.hmax - 1 ≤ (st.σ B.root).h ∧
      (st.hmax = st.hj + 1 → (st.σ B.root).h = st.hmax - 1 → st.Anc st.J B))
    (hBR : st.Anc B R) (heq : (st.σ R.root).h = (st.σ B.root).h) :
    st.hj < (st.σ R.root).h ∨
      ((st.σ R.root).h = st.hj ∧ st.Anc st.J R) := by
  by_cases hlt : st.hj < (st.σ R.root).h
  · exact Or.inl hlt
  · have htop : st.hmax = st.hj + 1 := by omega
    exact Or.inr ⟨by omega, (hB.2 htop (by omega)).trans hBR⟩

/-- The unchanged rise count covers the P-U proposal's height deficit. -/
theorem pred_add_riseRounds_frameKey'' {A : NodeAC P} {st : Store P A.Payload} {HZ : Nat}
    (hkey : 2 * HZ ≤ Generic.frameKey'' A st) :
    HZ + 1 ≤ st.hmax - 1 + riseRounds HZ (Generic.frameKey'' A st) := by
  classical
  by_cases htop : st.hmax = st.hj + 1
  · simp only [riseRounds_eq, Generic.frameKey''_eq, ite_eq_left htop] at hkey ⊢
    omega
  · simp only [riseRounds_eq, Generic.frameKey''_eq, ite_eq_right htop] at hkey ⊢
    omega

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open Consensus.Goldilocks.Generic (riseRounds)

open AC (ACParams Payload)

variable {sp : ACParams}

/-- V-B5's full growing contract. Unresolved while proposal extraction and transfer
suppliers are being assembled; no stock execution premise replaces the shadow run. -/
theorem proposal_viable_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {lo hi : Time} {M u : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (isTop → ((tr.state z (kB + 1)).fg.σ B.root).h = M - 1 →
        Anc (tr.HonestBlocksAt H) J B) := by
  exact KernelProof.proposal_window_witness hrun hnc hwin hz hdes hB hBs hlo hhi hf

/-- Leaf 8's arithmetic assembly, conditional on actual proposal viability. -/
private theorem rounds_le_of_proposal_viable
    {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}
    {lo hi : Time} {M v HZ : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (tr.time kB))
    (hlo : lo ≤ tr.time kB) (hhi : tr.time kB ≤ hi)
    (hkey : Generic.frameKey'' (goldilocksNode sp) (tr.state z kB).fg = v) (hv : 2 * HZ ≤ v)
    (hB : M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h) :
    HZ + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds HZ v := by
  have h := pred_add_riseRounds_frameKey'' (A := goldilocksNode sp) (st := (tr.state z kB).fg)
    (HZ := HZ) (by rw [hkey]; exact hv)
  rw [hkey, hwin.M_eq z kB hz hlo hhi] at h
  exact h.trans (Nat.add_le_add_right hB _)

/-- The shadow key bounds the height deficit at an honest proposal cut. -/
theorem rounds_le_warm_proposal_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g af len : Time} {u M v : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H af (af + len) M isTop J)
    (hK : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      Generic.frameKey'' (goldilocksNode sp) (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v) (hlo : af ≤ sp.ts u) (hhi : sp.ts u ≤ af + len)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds (HZ tr H g) v := by
  have ht : tr.time kB = sp.ts u := by
    simpa only [sp.slotTime_eq, hBs, ACParams.ts] using hB.2.2
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  exact rounds_le_of_proposal_viable hwin hzk (ht ▸ hlo) (ht ▸ hhi)
    (hK z kB hzk (ht ▸ hlo) (ht ▸ hhi)) hv
    (proposal_viable_at hrun hnc hwin hz hdes hB hBs hlo hhi hf).1

section Reset

open AC (gbar)
open Consensus.Goldilocks.Shadow.PU.Growing (proposal_report_follow_delayed_at)

variable {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {hold : Time}

/-- The latency deadline of a high report is also a reset deadline for a shadow run. -/
private theorem reset_of_high_report_within_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {g D : Time}
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    {y : Fin sp.n} {i : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)))
    (hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i + D := by
  have hy := hrun.antitone ((le_add_of_nonneg_right hD).trans (le_max_right _ _)) hyz
  obtain ⟨hc, hto, hres⟩ := hR
  apply Generic.Shadow.reset_of_high_report_within_from hrun hlat hyz hq ?_ hh
  refine ⟨ell, Compose.projAC_callAt.mp hc, hto, ?_⟩
  change (AC.acToFG sp (tr.state y i).ac ell.frame (tr.time i)).2 = some R
  rw [← Goldilocks.Shadow.PU.Growing.projAC_state_at hrun hy]
  exact hres

/-- A high proposal yields a reset by its delayed report and vote-latency deadline. -/
theorem reset_of_high_proposal_within_at
    {g ΔF b D t₀ : Time} {s₀ u N M Gs : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ) M
      isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤ b)
    (hH : (H b).Nonempty)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hDb : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  have hts : sp.ts (u + 1 : Nat) ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast hN)
  have hs₀ : sp.ts s₀ ≤ sp.ts (u + 1 : Nat) :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ u + 1 by omega))
  have hmax : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (Gs : Time) * sp.Δ) ≤
      sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ := max_le (by linarith) (by linarith)
  obtain ⟨y, hy⟩ := hH
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, _⟩ :=
    proposal_report_follow_delayed_at (hframe.mono le_rfl hmax) hrun hnc hsvc hawake hf
      hcatch hnr hm hwarm hN (hmax.trans hmb) hz hdes hP hPs hcal hgap (by linarith)
      (hrun.antitone (by linarith) hy) hK
  have hcz : cutZ sp.toParams g ≤ tr.time i := by
    have h4 : sp.ts (s₀ + 4 : Nat) ≤ sp.ts u :=
      (AC.ts_le_iff sp).2 (by exact_mod_cast (show s₀ + 4 ≤ u by have := sp.two_le_k; omega))
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    linarith [cutZ_le sp g]
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hPm := (Coherence.accept_of_proposesAt hr (hnc.upTo _) hzk hP').2.1
  rw [Trace.upTo_state tr z (fun q hq => hrun.time_mono (by omega))] at hPm
  have hRm : R ∈ (tr.state y i).fg.tree := by
    have hsource := (AC.toFG_source hR.2.2).1.1
    rw [Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hyi hR.1,
      Node.frame_eq, Store.toFrame_tree] at hsource
    exact hsource.1
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hPy := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg i) hle hyi hPm hPy
  rw [hσ] at hh
  have hhR := hh.trans (Store.h_le_of_store_anc_with Store.finalitySpec_updateFinality
    (Compose.Growing.reachable_at hrun (hrun.time_nonneg i) hyi hle).reachableWith
    (store_anc_of_honest_anc_at hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm))
  have hiD : tr.time i + D ≤ b := by linarith
  have hcD : max (cutZ sp.toParams g) (tr.time i + D) = tr.time i + D :=
    max_eq_right (by linarith)
  have hyD : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)) := by
    rw [hcD]; exact hrun.antitone hiD hy
  have hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q := by
    have hf' := hf _ (by linarith [hrun.time_nonneg i]) hiD
    have hn := sp.toParams.hn
    rw [hcD]
    change (H (tr.time i + D))ᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_within_at hrun hlat hD hyD hq hR hhR
  exact ⟨a, ha, by linarith⟩

/-- Leaf 11 over the P-U window. The proof must use `proposal_viable_at`: its height
bound is `M - 1`, and in a top window equality supplies `J` ancestry. The shared
row-or-high, later-head and delayed report-follow suppliers are proved. The stock-window
version also needs stock later-head transfer. -/
theorem round_of_warm_within_at
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
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast h)
  have htX : tr.time kX = sp.ts x := by
    simpa only [sp.slotTime_eq, hXs, ACParams.ts] using hX.2.2
  have huN : u + 1 ≤ N := by omega
  have hu0 := hts (show s₀ ≤ u by omega)
  have hcu : cutZ sp.toParams g ≤ sp.ts u := by
    have h4 := hts (show s₀ + 4 ≤ u by have := sp.two_le_k; omega)
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    linarith [cutZ_le sp g]
  have hv : gbar g ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) := by
    have := hts (show s₀ ≤ u + 1 by omega)
    linarith
  have hvx : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) + ΔF ≤
      tr.time kX := by
    have h1 := hts hux
    have h2 : sp.ts (u + sp.toParams.fg.δt : Nat) =
        sp.ts (u + 1 : Nat) + 4 * sp.Δ * (sp.toParams.fg.δt : Time) - 4 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    rw [htX]
    linarith
  have hvc : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) <
      tr.time kX := by linarith [hsvc.deltaF]
  have hTx : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤ tr.time kX := by
    linarith
  have hTN : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤
      sp.ts N + 2 * sp.Δ := by linarith [hts hxN]
  have hfi : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf (sp.ts u) (by simp only [ACParams.ts]; positivity)
      (by linarith [hts (show u ≤ N by omega)])
    have hn := sp.toParams.hn
    change (H (sp.ts u))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hz0 : z ∈ H (sp.ts u) := hrun.antitone (by linarith) hz
  have htimeP : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hPm := (Coherence.accept_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
    (hnc.upTo _) (htimeP ▸ hz0) hP').2.1
  rw [Trace.upTo_state tr z (fun q hq => hrun.time_mono (by omega))] at hPm
  have hPH : P ∈ tr.HonestBlocksAt H :=
    ⟨z, kP + 1, tr.time kP, hrun.time_nonneg kP,
      fun q hq => hrun.time_mono (by omega), htimeP ▸ hz0, hPm⟩
  have hr := hrun.upTo (hrun.time_nonneg kX)
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2⟩
  obtain ⟨_, c, ellp, d, pay, hc, hcall, hd, htc, hpar, _⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hp hdx hX' hXs
  rw [← hdx] at hc hd
  have hct : tr.time c = sp.ts x := htc
  have hpc := hrun.antitone (show tr.time c ≤ tr.time kX by rw [hct, htX]) hp
  have hc' : tr.projAC.CallAt p c ellp := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hd' : (AC.acProposal sp (tr.projAC.state p c) ellp.frame (tr.time c)).2 =
      some (d, pay) := by
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC p
      (fun q hq => (hrun.time_mono hq.le).trans (by rw [hct, htX]))] at hd
    exact hd
  have hfol := fun y (hy : y ∈ H (tr.time kX)) =>
    proposal_report_follow_delayed_at (hframe.mono le_rfl (max_le le_rfl hTN)) hrun hnc
      hsvc hawake hf hcatch hnr hm hwarm huN (max_le hmb (hTN.trans hmb)) hz hdes hP hPs hcal
      hgap (by linarith [hts (show s₀ ≤ u + 1 by omega)]) (hrun.antitone hTx hy) hK
  obtain ⟨i₀, ell₀, R₀, _, _, _, _, hPR₀, hR₀d⟩ := hfol p hp
  refine Generic.Shadow.round_cross_at_from hrun
    (fun y => Compose.requirements_from sp (hrun.vstart y)) hrun.genesis_root_ok hnc
    hsvc.signedRow hsvc.hold_le hnr hPH
    (hPR₀.trans (hR₀d x (by omega) hxN p c ellp hpc hc' hcall hct d pay hd')) hpar hp hX
    (hf _ (hrun.time_nonneg kX) (by rw [htX]; linarith [hts hxN])) hv hvx
    (by rw [htX]; linarith [hts hxN]) (by
      change P.slot + sp.toParams.fg.δt ≤ X.slot
      rw [hPs, hXs]
      exact hux) ?_
  intro y hy
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, _⟩ := hfol y hy
  have hreport : Generic.ReportAt tr y i R :=
    ⟨ell, Compose.projAC_callAt.mp hR.1, hR.2.1,
      by change (AC.acToFG sp (tr.state y i).ac ell.frame (tr.time i)).2 = some R
         rw [← Goldilocks.Shadow.PU.Growing.projAC_state_at hrun hyi]
         exact hR.2.2⟩
  obtain ⟨k, hik, hk, C, s, hatt, _, hRC, j, hij, hjk, ellC, hcC, htoC, hretC⟩ :=
    hlat.attests y i R hreport (hrun.antitone (by linarith) hy)
  have hPC := hPR.trans hRC
  have htk := hrun.time_mono hik
  have htkx : tr.time k < sp.ts x := by rw [← htX]; linarith
  have hyk := hrun.antitone (htX ▸ htkx.le) hy
  have htjk := hrun.time_mono hjk
  have hyj := hrun.antitone htjk hyk
  have hC : AC.ToFGAt tr.projAC y j ellC C :=
    ⟨Compose.projAC_callAt.mpr hcC, htoC,
      by change (AC.acToFG sp (tr.projAC.state y j) ellC.frame (tr.time j)).2 = some C
         rw [Goldilocks.Shadow.PU.Growing.projAC_state_at hrun hyj]
         exact hretC⟩
  have hCj : C ∈ (tr.state y j).fg.tree := by
    have hsrc := (AC.toFG_source hC.2.2).1.1
    rw [Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hyj hC.1,
      Node.frame_eq, Store.toFrame_tree] at hsrc
    exact hsrc.1
  have hkle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hk0 := hrun.time_nonneg k
  have hCk := Compose.Growing.tree_mono_at hrun hk0 hyk hkle hjk hCj
  have hPk := mem_of_honest_anc_at hrun hnc hk0 hkle hyk hPC hCk
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) (htimeP ▸ hz0) hk0 hkle hyk hPm hPk
  obtain ⟨hfloor, htop⟩ := proposal_viable_at hrun hnc hframe hz0 hdes hP hPs hu0
    (by linarith [hts huN]) hfi
  rw [hσ] at hfloor htop
  have hjlo := hu0.trans (htil.trans (hrun.time_mono hij))
  have hklo := hjlo.trans htjk
  have hkhi : tr.time k ≤ sp.ts N + 2 * sp.Δ := by linarith [hts hxN]
  have hM := hframe.M_eq y k hyk hklo hkhi
  have hkind := hframe.top_iff y k hyk hklo hkhi
  obtain ⟨hPy, hCy, hor⟩ := Generic.Shadow.row_or_high_of_attest_at_from hrun hnc
    (fun t ht htT => hf t ht (htT.le.trans hTb)) hna
    (by rwa [max_eq_right (hcu.trans (htil.trans htk))]) hatt (by linarith) hCk hPC (fun _ => by
      right
      have hjmax := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
        (Compose.Growing.reachable_at hrun hk0 hyk hkle).reachableWith
      by_cases htop' : isTop
      · have hmax := hkind.mpr htop'
        rcases hfloor.lt_or_eq with hlt | heq
        · left; omega
        · right
          refine ⟨by omega, ?_⟩
          rw [hframe.root_eq y k hyk hklo hkhi htop']
          exact store_anc_of_honest_anc_at hrun hnc hk0 hkle hyk
            ((htop htop' heq.symm).trans hPC) hCk
      · left
        have hne : (tr.state y k).fg.hmax ≠ (tr.state y k).fg.hj + 1 :=
          fun he => htop' (hkind.mp he)
        omega)
  rcases hor with ⟨l, att, hyl, hs, hlk, hah, haT⟩ | hh
  · exact Or.inl ⟨y, k, hyk, hPy, l, att, hyl, hs, by linarith, hah, haT⟩
  · have hshort := hframe.mono le_rfl (show sp.ts N + sp.Δ ≤ sp.ts N + 2 * sp.Δ by
        linarith)
    have hChead := Goldilocks.Shadow.PU.Growing.toFG_later_proposal_head_after_at
      hshort hrun hnc hsvc hawake hf hcatch hnr hm hwarm (by linarith) hyj hC hPs hPC
      (by linarith [hts hxN]) (htjk.trans_lt htkx) hxN hpc hc' hcall hct hd' hK
    exact Or.inr ⟨C, hChead, y, k, hyk, hPy, hCy, hh⟩

end Reset

end Consensus.Goldilocks.Healing.Growing.Shadow

end
