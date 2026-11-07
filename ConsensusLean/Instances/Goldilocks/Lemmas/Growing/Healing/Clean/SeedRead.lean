module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A reset seed held at a bounded honest read

An actual earlier update receives the seed. Only that reader's finite local execution is used
to carry its tree forward to the read; the next event need not fall inside the horizon.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A reset seed is held at a later honest read whenever it extends the finalized tip. -/
theorem reset_seed_held_at_read_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} {n u : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr n t) (htb : t ≤ b) (hy : y ∈ H t)
    (hdrain : drainTime sp a ≤ sp.ts u) (hgst : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hbefore : sp.ts u + 6 * sp.Δ < t) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u ∧
      (Anc (tr.HonestBlocksAt H) (tr.state y n).fg.F S → S ∈ (tr.state y n).fg.tree) := by
  have hΔ := sp.toParams.hΔ
  have hu0 : 0 ≤ sp.ts u := by simp only [SAParams.ts]; positivity
  have ht : 0 ≤ t := by linarith
  have hm := hp.run.time_mono
  have hr := hp.run.upTo ht
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) ht
  obtain ⟨v, r, l, S, hS, hra, hrb, hheld⟩ := hp.reset_seed_held_at_call_at hc
  have hru : tr.time r < sp.ts u := by
    have hca := hp.cutZ_lt_reset_at
    have ha0 : 0 ≤ a := by linarith [Healing.lt_cutZ sp g, SA.gbar_nonneg g]
    rw [Healing.drainTime_eq] at hdrain
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).mp h
      omega
    have hts : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) :=
      (SA.ts_le_iff sp).mpr (by omega)
    linarith
  have hlu : l < u := by
    obtain ⟨CV, ell, D, hcall, hfl, _⟩ := hS.2.2.1
    have hts : sp.ts l ≤ tr.time r := by
      rcases hfl with ⟨ell', C, ⟨_, _, ht', _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
      · change tr.time r = sp.ts l + 6 * sp.Δ at ht'
        linarith
      · change sp.slot (tr.time r) = l at hsl
        exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) _).mpr (by omega)
    exact_mod_cast (SA.ts_lt_iff sp).mp (hts.trans_lt hru)
  have hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hslot := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      (sp.slot (SA.gbar g))).mpr (by omega)
    simp only [SAParams.ts] at hslot hgst ⊢
    push_cast
    linarith
  have htime : sp.ts u + 6 * sp.Δ ≤ t := hbefore.le
  obtain ⟨j, ell, ell', hup, rest⟩ := Healing.update_toFG_calls_of_awake hr hy
    ((Trace.upTo_awake _ _ _).mpr ⟨hp.awake y _ (hp.run.antitone htime hy)
      (by linarith [SA.le_gbar g]) (htime.trans htb), htime⟩) (by
      intro i hi
      have hac := (Compose.goldilocks_ac_projection sp ro dg (H t) (tr.upTo t) proposer
        hr (hp.noColl.upTo t)).localRun
      unfold SA.joined
      rcases SA.restartTime_state hac hy i with h | ⟨r, hri, hrs, h⟩
      · rw [h]; exact bot_le
      · rw [h]
        apply WithBot.coe_le_coe.mpr
        rw [RunTrace.upTo_projAC] at hrs
        obtain ⟨hrt, hrs⟩ := ACTrace.upTo_restartAt.mp hrs
        have hrestart := hp.restart_le_before_at (hp.run.antitone hrt hy)
          (Compose.projAC_restartAt.mp hrs) (hrt.trans htb)
        have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
          SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith)
            (by simp only [SAParams.ts]; push_cast; linarith)
        change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
        change tr.time i = sp.ts u + 6 * sp.Δ at hi
        rw [hi, hslot]
        simpa using hrestart.trans hjoin)
  rw [RunTrace.upTo_projAC] at hup
  have hjt : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjn : j ≤ n := by
    by_contra h
    have := hrp.2.trans (hm (show n ≤ j by omega))
    linarith
  have hstatej := RunTrace.upTo_state_of_le (y := y) hm (hjt ▸ htime)
  have hstaten := Trace.upTo_state tr y hrp.1
  refine ⟨v, r, l, S, hS, hrb, hlu, hru, fun hF => ?_⟩
  have hgrow := Compose.fg_grows hr hy hjn
  rw [hstatej, hstaten] at hgrow
  have hframe := Compose.frame_of_projAC hr hy (show (tr.upTo t).projAC.CallAt y j ell
    from by rw [RunTrace.upTo_projAC]; exact hup.1)
  rw [hstatej] at hframe
  have hFj : Anc (tr.HonestBlocksAt H) ell.frame.F S := by
    rw [hframe]
    exact (hgrow.2.mono hsub).trans hF
  have hacall : a + sp.Δ ≤ tr.time j := by
    have hca := hp.cutZ_lt_reset_at
    have ha0 : 0 ≤ a := by linarith [Healing.lt_cutZ sp g, SA.gbar_nonneg g]
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).mp h
      omega
    have hts : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts u := by
      rw [Healing.drainTime_eq] at hdrain
      exact ((SA.ts_le_iff sp).mpr (by omega)).trans hdrain
    linarith
  have hSj := hheld y j ell (hp.run.antitone (hjt ▸ htime) hy)
    ((Trace.upTo_callAt _).mp hup.1).2 hacall ((hjt ▸ htime).trans htb) hFj
  exact hgrow.1 ((frame_tree_subset_at hp.run hp.noColl
    (hp.run.antitone (hjt ▸ htime) hy) ((Trace.upTo_callAt _).mp hup.1).2).2 hSj)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
