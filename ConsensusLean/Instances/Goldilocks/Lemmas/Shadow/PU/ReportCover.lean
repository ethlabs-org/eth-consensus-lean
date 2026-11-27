module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
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
with `X = J` applies). The open case "top-clean, `σ(P).h = h_j`, `J ⋠ P`" is the third branch: the
root premise, supplied today by `high_J_root_of_held_before_covered_at` (high `h_j`) and
`low_root_of_held_seed_at` (low `h_j`), forces `P ⪯ J`. No new hypothesis is needed.

The run-level statements take the shadow reset premises `ResetPremisesUpTo'` (`Shadow/PU/Run`);
their proofs are still open (unresolved) until the primed root suppliers land. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- **The shadow viability split.** A block compatible (in the store) with the store's fork-choice
root is P-U viable, or of state height below the stock head-height floor, or strictly below
`Σ.J`. `h_j < h_max` holds at every reachable store (`cache_invariants`). -/
theorem isViable'_or_lt_floor_or_below_J {B : NodeBlock P ACP} (hjm : st.hj < st.hmax)
    (hroot : st.Anc st.fcRoot B ∨ st.Anc B st.fcRoot) :
    st.IsViable' B ∨ (st.σ B.root).h < st.headHeightFloor ∨ (st.Anc B st.J ∧ B ≠ st.J) := by
  classical
  rw [isViable'_iff]
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

variable {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time}

/-- **A held target above a high seed is P-U viable, or an earlier strictly higher report extends
it** (`ReportCover.held_target_viableHeads_or_higher_report_of_cases` over the shadow frame). The
root and floor premises are the stock ones, read from the store; the conclusion drops the stock
`Anc fcRoot P` conjunct (the shadow root is `F`). -/
theorem held_target_viableHeads'_or_higher_report_of_cases
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame' (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hhighroot : ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P)
    (hfloorrep : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor →
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) :
    P ∈ (Node.frame' (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have hd := hrun.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := (Compose.Growing.reachable_at' hrun hd hy hle).reachableWith
  have hfs := Store.finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  obtain ⟨hPy, hFP⟩ := Shadow.PU.mem_frame'_tree.1 hPt
  have hcz := ProposalImpl.cutZ_lt_of_anc_at' hp hseed (by rwa [max_comm]) hPy hSP
  have hroot : Compatible (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact hp.low_root_of_held_seed_at' hy hib hseed hqb
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
    hroot.imp (fun h => Coherence.held_anc_at' hrun hnc hd hy hle h hPy)
      (fun h => Coherence.held_anc_at' hrun hnc hd hy hle h hrt)
  rcases Store.isViable'_or_lt_floor_or_below_J (tr.state y i).fg
      (Shadow.PU.hj_lt_hmax_at' hrun hd hy hle) hrootS with hv | hfl | ⟨hPJ, hPne⟩
  · left
    rw [Node.frame'_eq, Store.toFrame'_viableHeads]
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

/-- The covered form: the root and floor premises discharged from `CompatibleWithOrigins`
(`ReportCover.held_target_viableHeads_or_higher_report_covered_at` over the shadow frame). -/
theorem held_target_viableHeads'_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame' (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ (Node.frame' (tr.state y i)).viableHeads ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  sorry

/-- The call form, read through the frame of an AC call (`Node.frame'`):
`held_target_viable_or_higher_report_covered_at` over the shadow frame. -/
theorem held_target_viable'_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    {ell : ACLabel (goldilocksNode' sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hy := hp.run.antitone (le_max_right _ _) hyz
  rw [Shadow.PU.Growing.frame_of_projAC_at' hp.run hy hcall] at hPt ⊢
  rcases held_target_viableHeads'_or_higher_report_covered_at hp hyz hib hPt hseed hqb hSP
      hcompare with hhead | hreport
  · refine Or.inl ⟨hPt, ?_, P, hPt, hhead, .refl⟩
    have hF := hhead
    rw [Node.frame'_eq, Store.toFrame'_viableHeads] at hF
    change Anc (Node.frame' (tr.state y i)).tree (Node.frame' (tr.state y i)).fcRoot P
    rw [Node.frame'_eq, Store.toFrame'_tree, Store.toFrame'_fcRoot]
    exact Anc.restrict .refl hF.2.1
  · exact Or.inr hreport

end Consensus.Goldilocks.Healing.Growing.Shadow

end
