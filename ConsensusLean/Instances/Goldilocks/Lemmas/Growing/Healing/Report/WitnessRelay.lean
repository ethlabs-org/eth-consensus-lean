module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Early historical frame witnesses reach the next vote's frozen tree -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
variable {hold : Time}

namespace Core

variable {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n →
    Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- A frame block has an earlier honest acceptance, or is genesis. -/
theorem frame_block_acceptance_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {x : Fin sp.n} {q : Nat} (hx : x ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt x q ell)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ∃ k < q, x ∈ H (tr.time k) ∧ tr.AcceptAt x k B := by
  have hframe := (cutStepWith_ac ell).mp
    (hrun.cutLaw x q _ (Compose.projAC_callAt.mp hc) hx) |>.1
  rw [hframe] at hB
  have ht := (hrun.frameOf_tree _ B).mp hB |>.1
  have ht' : B ∈ ((tr.upTo (tr.time q)).state x q).fg.tree := by
    rwa [Trace.upTo_state tr x (fun _ hk => hrun.time_mono hk.le)]
  rcases (hrun.upTo (hrun.time_nonneg q)).tree_accepted x hx ht' with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, hk, hrun.antitone (hrun.time_mono hk.le) hx,
      ((RunTrace.upTo_acceptAt _).mp ha).2⟩

/-- Joinedness of this cast, rather than a no-restart premise, bounds its relay deadlines. -/
theorem witness_voterBlockTree_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {w y : Fin sp.n} {a i : Nat} (hw : w ∈ H (tr.time a)) (hy : y ∈ H (tr.time i))
    {ellw ell : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQw : Q ∈ ellw.frame.tree)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = s + 1) (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (s + 1) := by
  have ht0 := hrun.time_nonneg i
  have hac := hrun.acRun hnc
  have hr := (hac.upTo ht0).localRun
  have hc' := ac_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hU := hrun.coherent hnc
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc'.1
  have hQU := (AC.frameIn_of_callAt
    ((hac.upTo (hrun.time_nonneg a)).localRun) hw
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hcw)).2 hQw
  have hslot := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hs
  change sp.slot (tr.time i) = s + 1 at hslot
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
  have hts := AC.ts_succ s (sp := sp)
  have hΔ := sp.toParams.hΔ
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hjoined := (AC.castAt_specU hr.toU hy hc').2.2.1
    have hj : AC.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAtU hr.toU hy hc']
      exact hjoined
    intro k hk hrestart
    have h := (AC.joined_awakeU sp _ ro (H (tr.time i)) _ _ hr.toU y hy i ell hc'.1 hj).2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hrun.time_mono hk, hrestart⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at h
    simpa only [hslot, show ((s + 1 : Nat) : Int) - 1 = s by omega] using h
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hr hrestart => hrs r (hr.trans hk) hrestart) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  have ha : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q (AC.freeze sp (s + 1)) := by
    rcases frame_block_acceptance_at hrun hw hcw hQw with hg | ⟨k, hka, hwk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    obtain ⟨hk', htk, -⟩ := (hrun.upTo (hrun.time_nonneg a)).ac_block_after w hw
      ((RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono hka.le, hk⟩)
    rw [RunTrace.upTo_projAC] at hk'
    have hacc := (ACTrace.upTo_acceptAt.mp hk').2
    have hwk' : w ∈ H (tr.time (k + 1)) := by
      change tr.time (k + 1) = tr.time k at htk
      rwa [htk]
    have hkt : tr.time (k + 1) < sp.ts s + 2 * sp.Δ := by
      change tr.time (k + 1) = tr.time k at htk
      rw [htk]
      exact (hrun.time_mono hka.le).trans_lt hat
    have hex : ∃ q ≤ i, tr.projAC.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hkg : gbar g ≤ tr.time (k + 1)
      · obtain ⟨q, hqi, hq, hqt⟩ :=
          (service_syncACAt hrun hsvc (lo := g) (hi := tr.time (k + 1)) le_rfl).2
            w (k + 1) Q hwk' hacc ((AC.le_gbar g).trans hkg) le_rfl y i ell hy hc.1
            (by have := hdl i le_rfl _ hkt;
                change tr.projAC.deadline y i (tr.time (k + 1)) ≤ tr.time i;
                linarith only [this, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; exact hqt.trans (hdl q hqi _ hkt)⟩
      · obtain ⟨q, hqi, hq, hqt⟩ := service_catch_at hrun hcatch hwk' hacc
          (lt_of_not_ge hkg) hy hc.1 (by linarith only [hm, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; linarith only [hqt, hm, hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := hex
    exact Or.inr ⟨q, ACTrace.upTo_acceptAt.mpr ⟨hrun.time_mono hqi, hq⟩, hqt⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy i ell hc'.1
      obtain rfl : Q = G := hU.1 hQU hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hki : k ≤ i := by
        by_contra hn
        have ht := hrun.time_mono (show i ≤ k by omega)
        change tr.time k < _ at hkt
        rw [hfz] at hkt
        linarith only [ht, hkt, hti, hts, hΔ]
      obtain ⟨ella, hca, hba⟩ := hk
      have hk : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k Q := ⟨ella, hca, hba⟩
      exact AC.mem_tree_of_acceptAtU sp hr.toU hy hk hki hc'.1
        hFQ
  have hstamp := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
    (by simpa only [hs] using ha)
    (fun k hk hrk => by
      have h := hrs k hk (ACTrace.upTo_restartAt.mp hrk).2
      change tr.time k < _
      rw [hs, hfz]
      linarith only [h, hΔ])
    (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hs, hfz];
        linarith only [hti, hts, hΔ])
  exact ⟨hQt, Or.inl (by simpa only [hs] using hstamp)⟩

end Core

/-- Joinedness of this cast bounds its relay deadlines. -/
theorem witness_voterBlockTree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {w y : Fin sp.n} {a i : Nat} (hw : w ∈ H (tr.time a)) (hy : y ∈ H (tr.time i))
    {ellw ell : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQw : Q ∈ ellw.frame.tree)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = s + 1) (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (s + 1) :=
  Core.witness_voterBlockTree_at hrun.toCore hnc hsvc hcatch hm hw hy hcw hat hQw hc hs hFQ

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
