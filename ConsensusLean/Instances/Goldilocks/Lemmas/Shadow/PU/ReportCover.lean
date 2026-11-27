module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frontier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.StaticCoreFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots

public section

/-! # Report cover over the P-U shadow frame: the `fc_root = J` branch

The stock `ReportCover.held_target_viableHeads_or_higher_report_of_cases` (and the `FastLockRenewal`
branches that read `fc_root = J`) split on the store's fork-choice root. The shadow frame
`Node.frame'` has `fcRoot := F` and P-U viability, but the store-level `Store.fcRoot`,
`Store.Contest` and `Store.headHeightFloor` are unchanged, so the stock premises keep their meaning.

`isViable'_or_lt_floor_or_below_J` is the case analysis behind the shadow restatement: a block
`P ⪰ F` compatible with the store's `fc_root` is P-U viable, or below the stock head-height floor
(the stock higher-report premise applies), or strictly below `Σ.J` (the stock `cache_ahead_report`
with `X = J` applies). The case "top-clean, `σ(P).h = h_j`, `J ⋠ P`" is the third branch: the
root premise, supplied by strictly prior row provenance (high `h_j`) and
`low_analysis_root_of_held_seed_at` (low `h_j`), forces `P ⪯ J`. No new hypothesis is needed.

The run-level statements take the shadow reset premises `ResetPremisesUpTo'` (`Shadow/PU/Run`);
the covered form discharges its root and floor premises using the before-cut source suppliers. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- **The shadow viability split.** A block compatible (in the store) with the store's fork-choice
root is P-U viable, or of state height below the stock head-height floor, or strictly below
`Σ.J`. `h_j < h_max` holds at every reachable store (`cache_invariants`). -/
theorem isViable_or_lt_floor_or_below_J {B : NodeBlock P ACP} (hjm : st.hj < st.hmax)
    (hroot : st.Anc st.fcRoot B ∨ st.Anc B st.fcRoot) :
    st.IsViable B ∨ (st.σ B.root).h < st.headHeightFloor ∨ (st.Anc B st.J ∧ B ≠ st.J) := by
  classical
  rw [isViable_iff]
  rcases Nat.lt_or_ge (st.σ B.root).h st.hmax with hlt | hge
  · rcases Nat.lt_or_ge ((st.σ B.root).h + 1) st.hmax with hlt2 | hge2
    · -- two or more below `h_max`: below either floor
      right; left
      unfold headHeightFloor
      split_ifs <;> omega
    · have heq : (st.σ B.root).h + 1 = st.hmax := by omega
      by_cases hgap : st.hj + 1 < st.hmax
      · exact Or.inl (Or.inr ⟨heq, Or.inl hgap⟩)
      by_cases hJ : st.Anc st.J B
      · exact Or.inl (Or.inr ⟨heq, Or.inr hJ⟩)
      by_cases hc : st.Contest
      · right; left
        unfold headHeightFloor
        simp only [hc, ite_true]
        omega
      · -- top-clean: the root is `Σ.J`, and `J ⋠ B` puts `B` strictly below it
        have htop : st.hmax = st.hj + 1 := by omega
        have hfc : st.fcRoot = st.J := by
          unfold fcRoot
          simp [htop, hc]
        rw [hfc] at hroot
        refine Or.inr (Or.inr ⟨hroot.resolve_left hJ, fun he => hJ (he ▸ .refl)⟩)
  · exact Or.inl (Or.inl hge)

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

variable {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time}

/-- **A held target above a high seed is P-U viable, or an earlier strictly higher report extends
it** (`ReportCover.held_target_viableHeads_or_higher_report_of_cases` over the shadow frame). The
root and floor premises are the stock ones, read from the store; the conclusion drops the stock
`Anc fcRoot P` conjunct (the shadow root is `F`). -/
theorem held_target_viableHeads_or_higher_report_of_cases
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hhighroot : ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P)
    (hfloorrep : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor →
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) :
    P ∈ (Node.frame (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hU := Coherence.honestBlocksAt_coherent hrun hnc
  have hd := hrun.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := (Compose.Growing.reachable_at' hrun hd hy hle).reachableWith
  have hfs := Store.finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  obtain ⟨hPy, hFP⟩ := Shadow.PU.mem_frame_tree.1 hPt
  have hcz := ProposalImpl.cutZ_lt_of_anc_at' hp hseed (by rwa [max_comm]) hPy hSP
  have hroot : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact hp.low_analysis_root_of_held_seed_at hy hib hseed hqb
        (mem_of_honest_anc_at' hrun hnc hd hle hy hSP hPy) hlow (Or.inr hSP)
        (fun _ => hPt)
    · exact hhighroot hlow
  have hFt := (Store.cache_invariants_with hfs hreach).1
  have hJt := (Store.cache_invariants_with hfs hreach).2.1
  have hrt : (tr.state y i).fg.fcRoot ∈ (tr.state y i).fg.tree := by
    unfold Store.fcRoot
    split_ifs <;> assumption
  have hrootS : (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot P ∨
      (tr.state y i).fg.Anc P (tr.state y i).fg.fcRoot :=
    hroot.imp (fun h => Coherence.held_anc_at hrun hnc hd hy hle h hPy)
      (fun h => Coherence.held_anc_at hrun hnc hd hy hle h hrt)
  rcases Store.isViable_or_lt_floor_or_below_J (tr.state y i).fg
      (Shadow.PU.hj_lt_hmax_at hrun hd hy hle) hrootS with hv | hfl | ⟨hPJ, hPne⟩
  · left
    rw [Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hPy, hFP, hv⟩
  · exact Or.inr (hfloorrep hfl)
  · right
    have hPR : Anc (tr.HonestBlocksAt H) P (tr.state y i).fg.J :=
      hPJ.mono fun X hX => ⟨y, i, tr.time i, hd, hle, hy, hX⟩
    have hf : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
      have hf := hp.faults _ hd hib
      have hn : 0 < sp.n := sp.toParams.hn
      change (H (tr.time i))ᶜ.ncard < (2 * sp.n + 2) / 3
      omega
    obtain ⟨x, hx, r, hri, d, _, att, ell', C, _, _, _, _, hto, _, hJx, hJC, _, hCh, hPh⟩ :=
      cache_ahead_report_at' hrun hnc hy hf (Or.inr rfl) hPy hPR hPne
    have hxle : ∀ k < r, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono (by omega)
    have hPx := mem_of_honest_anc_at' hrun hnc hd hxle hx hPR hJx
    have hσ := σ_eq_honest_at' hrun hnc hd hle hy hd hxle hx hPy hPx
    exact ⟨x, r, ell', C,
      hrun.antitone (max_le hcz.le (hrun.time_mono hri.le)) hx, hri, hto,
      hPR.trans hJC, by rw [← hσ, hCh]; exact hPh⟩

private theorem high_root_of_held_seed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPy : P ∈ (tr.state y i).fg.tree) (hseed : HighOrigin tr H g v q m S)
    (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y i).fg.hj) :
    Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P := by
  have hr := hp.run.toCore
  have hnc := hp.noColl
  have hy := hr.antitone (le_max_right _ _) hyz
  have hd := hr.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hr.time_mono hk.le
  have hU := hr.coherent hnc
  have hreach := hr.reachable_at hd hy hle
  have hfs := hr.finalitySpec
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, i, tr.time i, hd, hle, hy, h⟩
  have hcz := ProposalImpl.cutZ_lt_of_anc_at' hp hseed (by rwa [max_comm]) hPy hSP
  have hrow : ∀ E ∈ (tr.state y i).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ E.root).h →
      ((tr.state y i).fg.σ E.root).Th = E.root →
      ¬ Compatible (tr.HonestBlocksAt H) E P →
      ∀ W ∈ (tr.state y i).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H (tr.time i) := by
    intro E hE hEh _ hEP W hW att ha haT haH
    have hW' : W ∈ ((tr.upTo (tr.time i)).state y i).fg.tree := by
      rwa [Trace.upTo_state tr y hle]
    rcases (hr.upTo hd).tree_accepted y hy hW' with rfl | ⟨k, hki, hA⟩
    · cases ha
    obtain ⟨d, hdk, hs⟩ := hr.att_unforgeable y k att
      (hr.antitone (hle k hki) hy)
      (Or.inr ⟨W, ⟨true, ((RunTrace.upTo_acceptAt tr).mp hA).2⟩, ha⟩)
      (hr.antitone (hle k hki) haH)
    have hdi := hdk.trans hki
    have hv := hr.antitone (hle d hdi) haH
    obtain ⟨Es, hEs, hEsr, hEsh⟩ := hr.signAt_entry hv hs
    have hsubs : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hr.time_nonneg d,
        fun _ hk => hr.time_mono hk.le, hv, h⟩
    have heq : Es = E := hU.1 (hsubs hEs) (hsub hE) (hEsr.trans haT)
    subst Es
    have hσ := hr.σ_eq_honest_at hnc (hr.time_nonneg d)
      (fun _ hk => hr.time_mono hk.le) hv hd hle hy hEs hE
    have hhh : HZ tr H g + 1 ≤ att.h := by rw [← hEsh, hσ]; exact hEh
    have hvz := hr.antitone (max_le hcz.le (hle d hdi)) haH
    rcases hp.quarantine_or_cover_at hib with hpre | hc
    · obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hEO, hEr, -⟩ :=
        Outcome.high_row_source_at_core hr hnc hvz hs hhh
          (hp.snapshot.imp fun _ h => h.1) fun D hD => (hle d hdi).trans (hpre D hD)
      have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
        fun _ h => ⟨att.val, r, tr.time r, hr.time_nonneg r,
          fun _ hk => hr.time_mono hk.le, hr.antitone (le_max_right _ _) ho.1, h⟩
      obtain rfl : E₀ = E := hU.1 (hsub₀ hE₀) (hsub hE) (hEr.trans haT)
      have hEO' := hEO.mono hsub₀
      rcases (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).1
          att.val r l O (hrd.trans hdi) ho with hPO | hOP
      · exact hEP (Anc.total hU hEO' hPO)
      · exact hEP (Or.inl (hEO'.trans hOP))
    · obtain ⟨E₁, hE₁, hE₁r, hcov⟩ := Outcome.signed_row_covered_before_at
        hp.run hnc hvz hs hhh (hp.snapshot.imp fun _ h => h.1) hc ((hle d hdi).trans hib)
      obtain rfl : E₁ = E := hU.1 hE₁ (hsub hE) (hE₁r.trans haT)
      obtain ⟨-, C, s, hC, hsl, hEC⟩ := coveredBefore_iff.1 hcov
      rcases (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).2 hc C s
          (hC.mono hdi.le) (hsl.trans (AC.slot_mono sp (hr.time_nonneg d) (hle d hdi))) with
        hPC | hCP
      · exact hEP (Anc.total hU hEC hPC)
      · exact hEP (Or.inl (hEC.trans hCP))
  have hf := hp.faults _ hd hib
  have hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change 3 * (H (tr.time i))ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H (tr.time i))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  have hcache := Store.cache_invariants_with hfs hreach
  obtain ⟨Bj, hBj, hBjJ, hBjhj⟩ := hcache.2.2.2.1
  obtain ⟨E, hE, hEr, hEBj, hcase⟩ := Store.J_entry_with hfs hreach hBj
  have heq : E = (tr.state y i).fg.J :=
    hU.1 (hsub hE) (hsub hcache.2.1) (hEr.trans hBjJ)
  subst E
  have hJ : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.J P := by
    rcases hcase with he | ⟨hEh, hET⟩
    · rw [he]
      exact Or.inl
        (((Store.accepted_tree_with hfs hreach).2.2.2 P hPy).mono hsub)
    · by_contra hJP
      have hkept := (Store.entry_kept_with hfs hreach hq
        (hrow _ hE (by omega) hET hJP) hEBj hET).1
      have hlt := Store.hj_lt_h_with hfs hreach hBj
      omega
  have hF : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.F P := by
    rcases hJ with hJP | hPJ
    · exact Or.inl ((hcache.2.2.1.mono hsub).trans hJP)
    · exact Anc.total hU (hcache.2.2.1.mono hsub) hPJ
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- The covered form: the root and floor premises discharged from `CompatibleWithOrigins`
(`ReportCover.held_target_viableHeads_or_higher_report_covered_at` over the shadow frame). -/
theorem held_target_viableHeads_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ (Node.frame (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hr := hp.run.toCore
  have hy := hr.antitone (le_max_right _ _) hyz
  have hd := hr.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => hr.time_mono hk.le
  have hU := hr.coherent hp.noColl
  obtain ⟨hPy, -⟩ := Shadow.PU.mem_frame_tree.1 hPt
  apply held_target_viableHeads_or_higher_report_of_cases hp hyz hib hPt hseed hqb hSP
  · intro hh
    exact high_root_of_held_seed_at hp hyz hib hPy hseed hSP hcompare (by omega)
  intro hfloor
  have hreach := hr.reachable_at hd hy hle
  have hfs := hr.finalitySpec
  have hPh := Outcome.high_of_anc_at' hp.run hp.noColl hseed hd hle hy hPy hSP
  have hcon : ¬ (tr.state y i).fg.Contest := by
    intro hc
    have hnc := Outcome.no_high_contest_at' hp hy hib
    unfold Store.headHeightFloor at hfloor
    simp only [hc, ite_true] at hfloor
    exact hnc ⟨hc, by omega⟩
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ite_false]
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Store.cache_invariants_with hfs hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ := Store.entry_at_height_with hfs hreach hC
    (h := (tr.state y i).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, x, d, hx, hdi, hs, hT, hor⟩ :=
    hp.left_entry_origin_or_covered_before_at hd hle hy hib hE hET
      (by omega) hEC (by omega)
  have hPE : Anc (tr.HonestBlocksAt H) P E := by
    have hcomp : Compatible (tr.HonestBlocksAt H) P E := by
      rcases hor with ⟨r, hrd, l, O, ho, hEO⟩ | ⟨-, hcov⟩
      · rcases (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).1
          x r l O (hrd.trans hdi) ho with hPO | hOP
        · exact Anc.total hU hPO hEO
        · exact Or.inr (hEO.trans hOP)
      · obtain ⟨hc, M, s, hM, hsl, hEM⟩ := coveredBefore_iff.1 hcov
        rcases (ResetPremisesUpTo.compatibleWithOrigins_iff.1 hcompare).2
            hc M s hM hsl with hPM | hMP
        · exact Anc.total hU hPM hEM
        · exact Or.inr (hEM.trans hMP)
    rcases hcomp with hPE | hEP
    · exact hPE
    · have hh := Store.h_le_of_store_anc_with hfs hreach
        (hr.held_anc_at hp.noColl hd hy hle hEP hPy)
      omega
  have hxz : x ∈ H (max (cutZ sp.toParams g) (tr.time d)) := by
    rcases hor with ⟨r, hrd, l, O, ho, -⟩ | ⟨hxz, -⟩
    · rcases le_total (cutZ sp.toParams g) (tr.time d) with h | h
      · rw [max_eq_right h]
        exact hr.antitone (hle d hdi) hx
      · rw [max_eq_left h]
        exact hr.antitone (le_max_left _ _) ho.1
    · exact hr.antitone (max_le_max le_rfl (hle d hdi)) hxz
  have hxd := hr.antitone (le_max_right _ _) hxz
  obtain ⟨r, hrd, hrt, ell, D, E', hto, hD, hE', hE'r, hED, -, -, hEDh, -⟩ :=
    signAt_report_entry (hp.run.upTo (hr.time_nonneg d)) hxd
      ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  have hrt' : tr.time r = tr.time d := hrt
  have he : (tr.upTo (tr.time d)).state x r = tr.state x r :=
    RunTrace.upTo_state_of_le hr.time_mono hrt'.le
  rw [he] at hD hE' hED hEDh
  have hxr := hr.antitone hrt'.le hxd
  have hr0 := hr.time_nonneg r
  have hler : ∀ k < r, tr.time k ≤ tr.time r := fun _ hk => hr.time_mono hk.le
  obtain rfl : E' = E := hU.1 ⟨x, r, tr.time r, hr0, hler, hxr, hE'⟩
    ⟨y, i, tr.time i, hd, hle, hy, hE⟩ (hE'r.trans hT)
  have hPD := hPE.trans (hED.mono fun X hX =>
    (⟨x, r, tr.time r, hr0, hler, hxr, hX⟩ : X ∈ tr.HonestBlocksAt H))
  have hPr := hr.mem_of_honest_anc_at hp.noColl hr0 hxr hler hPD hD
  refine ⟨x, r, ell, D, by rwa [hrt'], by omega,
    (toFGAt_upTo_iff hr.time_mono hrt'.le).mp hto, hPD, ?_⟩
  rw [← hEDh, hr.σ_eq_honest_at hp.noColl hr0 hler hxr hd hle hy hPr hPy,
    hr.σ_eq_honest_at hp.noColl hr0 hler hxr hd hle hy hE' hE]
  omega

/-- The call form, read through the frame of an AC call (`Node.frame'`):
`held_target_viable_or_higher_report_covered_at` over the shadow frame. -/
theorem held_target_viable_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hy := hp.run.antitone (le_max_right _ _) hyz
  rw [Shadow.PU.Growing.frame_of_projAC_at hp.run hy hcall] at hPt ⊢
  rcases held_target_viableHeads_or_higher_report_covered_at hp hyz hib hPt hseed hqb hSP
      hcompare with hhead | hreport
  · refine Or.inl ⟨hPt, ?_, P, hPt, hhead, .refl⟩
    have hF := hhead
    rw [Node.frame_eq, Store.toFrame_viableHeads] at hF
    change Anc (Node.frame (tr.state y i)).tree (Node.frame (tr.state y i)).fcRoot P
    rw [Node.frame_eq, Store.toFrame_tree, Store.toFrame_fcRoot]
    exact Anc.restrict .refl hF.2.1
  · exact Or.inr hreport

end Consensus.Goldilocks.Healing.Growing.Shadow

end
