module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # An early-accepted block reaches a next-slot proposal, under growing faults

The growing form of `Healing.relay_source_at_proposal` (`Healing/NextVotesCore`): a block
accepted before `t_s + 2Δ` by a node honest at its acceptance reaches the frame of an honest
proposal call at `t_{s+1}`, with a finite block stamp there. Post-`ḡ` acceptances relay through
the finite service, earlier ones through Catch; the sender need not stay honest. The proposer's
restarts are bounded by the caller (from the proposal's joinedness), not by a whole-run premise.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An acceptance before `ḡ` of a node honest at it reaches a later reader through Catch, as an AC
acceptance before `ḡ + 2Δ`. -/
private theorem catch_accept_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} (hcatch : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hw : w ∈ H (tr.time kw))
    (ha : tr.projAC.AcceptAt w kw B) (hkw : tr.time kw < gbar g) {y : Fin sp.n} {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i))
    (hcy : tr.projAC.CallAt y i ell) (hi : gbar g + 2 * sp.Δ ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ i, tr.projAC.AcceptAt y k B ∧ tr.time k < gbar g + 2 * sp.Δ := by
  classical
  have hr := hrun.toLocalRun
  obtain ⟨kw', hkw', hacc₀, hti₀⟩ := Healing.fg_accept_before
    (hrun.upTo (hr.time_nonneg kw)).toLocalRun hw
    (by rw [RunTrace.upTo_projAC]; exact ACTrace.upTo_acceptAt.mpr ⟨le_rfl, ha⟩)
  have hacc : tr.AcceptAt w kw' B := ((RunTrace.upTo_acceptAt _).mp hacc₀).2
  have hti : tr.time kw' = tr.time kw := hti₀
  subst hkw'
  have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, hi⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀i : Nat.find hex ≤ i := Nat.find_min' hex hi
  have hc := Compose.projAC_callAt.mp hcy
  have hfr : ell.frame.F = (tr.state y i).fg.F := by
    rw [(hrun.cutLaw y i _ hc hy).1]
    rfl
  have hmono := Healing.run_F_mono (hrun.upTo (hr.time_nonneg i)).toLocalRun hy hj₀i
  rw [RunTrace.upTo_state_of_le hr.time_mono (hr.time_mono hj₀i),
    RunTrace.upTo_state_of_le hr.time_mono le_rfl] at hmono
  have hmono' := hmono.mono (RunTrace.honestBlocks_upTo_subset hr.time_mono (hr.time_nonneg i))
  obtain ⟨k, hk, hak⟩ := hcatch w kw' B (hti ▸ hw) hacc (by rw [hti]; exact hkw) y
    _ (hr.antitone hi hy) hj₀ (hmono'.trans (hfr ▸ hanc))
  have hki : k ≤ i := by omega
  obtain ⟨hak', htk, -⟩ := Healing.ac_block_after (hrun.upTo (hr.time_nonneg i)).toLocalRun hy
    ((RunTrace.upTo_acceptAt _).mpr ⟨hr.time_mono hki, hak⟩)
  rw [RunTrace.upTo_projAC] at hak'
  refine ⟨k + 1, by omega, (ACTrace.upTo_acceptAt.mp hak').2, ?_⟩
  change tr.time (k + 1) = tr.time k at htk
  rw [htk]
  exact hj₀.2 k hk

/-- **An early-accepted block reaches a next-slot proposal**, held with a finite stamp. -/
theorem relay_source_at_proposal_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocksAt H)
    (hsource : Q.root = sp.genesisRoot ∨ ∃ z q, z ∈ H (tr.time q) ∧
      tr.projAC.AcceptAt z q Q ∧ tr.time q < sp.ts s + 2 * sp.Δ)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ ell.frame.tree ∧ (tr.projAC.state y i).blockStamp Q.root < ⊤ := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hi : tr.time i = sp.ts s + 4 * sp.Δ := hti.trans hts
  have ht0 := hrun.time_nonneg i
  have hgg := SA.le_gbar g
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  -- the proposer's deadlines before the proposal end before `t_s + 3Δ`
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hri hrr => hrs r (hri.trans hk) hrr) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  -- the proposer accepts `Q` (or `Q` is genesis) before `t_s + 3Δ`
  have ha : Q.root = sp.genesisRoot ∨
      ∃ k ≤ i, tr.projAC.AcceptAt y k Q ∧ tr.time k < sp.ts s + 3 * sp.Δ := by
    rcases hsource with hg | ⟨z, q, hz, hq, hqt⟩
    · exact Or.inl hg
    right
    by_cases hqg : gbar g ≤ tr.time q
    · obtain ⟨k, hki, hk, hkt⟩ := (service_syncACAt hrun hsvc (lo := g) (hi := tr.time q)
        le_rfl).2 z q Q hz hq (hgg.trans hqg) le_rfl y i ell hy hc
        (by
          have := hdl i le_rfl _ hqt
          change tr.projAC.deadline y i (tr.time q) ≤ tr.time i
          linarith only [this, hi, hΔ]) hFQ
      exact ⟨k, hki, hk, hkt.trans (hdl k hki _ hqt)⟩
    · obtain ⟨k, hki, hk, hkt⟩ := catch_accept_at hrun hcatch hz hq (lt_of_not_ge hqg) hy hc
        (by linarith only [hm, hΔ, hi]) hFQ
      exact ⟨k, hki, hk, by linarith only [hm, hΔ, hkt]⟩
  -- the prefix through the proposal
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo ht0) (hnc.upTo _)
  rw [RunTrace.upTo_projAC] at hac
  have hr := hac.localRun
  have hc' : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hki, hk, -⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ell hc'
      obtain rfl : Q = G := hU.1 hQU (subU hGU) (hg.trans hGr.symm)
      obtain ⟨hPhi, -⟩ := SA.frameIn_of_callAt hr hy hc'
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hk' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k Q :=
        ACTrace.upTo_acceptAt.mpr ⟨hmono hki, hk⟩
      obtain ⟨ella, hca, hba⟩ := hk'
      have hQp := (SA.frameIn_of_callAt hr hy hca).2
        ((SA.accept_new sp hr hy ⟨ella, hca, hba⟩).1 ella hca)
      exact SA.mem_tree_of_acceptAt sp hr hy ⟨ella, hca, hba⟩ hki hc'
        (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hQp hFQ)
  have hacc : SA.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q (sp.ts s + 3 * sp.Δ) := by
    rcases ha with hg | ⟨k, hki, hk, hkt⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, ACTrace.upTo_acceptAt.mpr ⟨hmono hki, hk⟩, hkt⟩
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc' hQt hacc
    (fun k hk hrk => by
      obtain ⟨-, hrk⟩ := ACTrace.upTo_restartAt.mp hrk
      change tr.time k < _
      have := hrs k hk hrk
      linarith only [hΔ, this]) (Or.inl (by change _ ≤ tr.time i; linarith only [hΔ, hi]))
  rw [hst] at hbs
  exact ⟨hQt, lt_trans hbs (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
