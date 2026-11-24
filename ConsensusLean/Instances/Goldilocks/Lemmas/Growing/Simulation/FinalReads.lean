module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorRoute
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Final reads at the Goldilocks run map

`goldilocks_finalReadTransport`: `FinalReadTransport` (its cache field) at the canonical run map
and any local supplier. The last anchor's proposer covers the first anchor at its acceptance
(`cacheCoverage_of_anchor_window_upTo_at`, from the supplied ancestry and height steps), and the
reader's finalized cache covers that block (`reader_cache_covers_at`) once a reader whose cache is
below the last anchor accepts it before its read. That acceptance is read on the deadline
premises, which hold on the honest sets truncated after the deadline: relay to the reader's first
call one delay after the anchor, or catch-up when the anchor precedes GST. Every reader fact after
the deadline (honesty, the read point, the threshold and the growth of its cache) is on the run's
own honest sets. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The final read transport of the canonical run map**, at any local supplier. -/
theorem goldilocks_finalReadTransport (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (goldilocksRunMap S rho hn hv).signer) :
    FinalReadTransport (goldilocksRunMap S rho hn hv) C := by
  classical
  let sp := S.params (pubOf E) hn
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  constructor
  · -- cache
    intro βK gst query D W _ _ hP hacc hanc hheights y j t hDt hrr _ hft
    have hx := (W.ready 3).1
    have hcD := W.bounded 3
    have hp3 := W.proposals 3
    have hpD := W.publication
    rw [goldilocksRunMap_trace S rho hn hv, goldilocksRunMap_honest S rho hn hv,
      goldilocksRunMap_digest S rho hn hv, goldilocksRunMap_committee S rho hn hv,
      goldilocksRunMap_proposer S rho hn hv, goldilocksRunMap_signer S rho hn hv] at hP
    rw [goldilocksRunMap_trace S rho hn hv] at hacc hcD hp3 hpD
    rw [goldilocksRunMap_trace S rho hn hv, goldilocksRunMap_honest S rho hn hv]
      at hanc hheights hrr hx ⊢
    rw [goldilocksRunMap_honest S rho hn hv] at hft
    set tr := simTraceAt S rho hn
    set H := honestKeysAt S rho
    have hnc : Compose.NoCollRun (digestOf S rho) tr := hP.noColl
    -- the last anchor's proposer covers the first anchor at its acceptance
    set x := (W.block 3).proposer
    set c := W.cut 3
    have hc0 := hrun.time_nonneg c
    have hlc : ∀ q < c + 1, tr.time q ≤ tr.time c := fun q hq => hmono (by omega)
    obtain ⟨-, hBx, -⟩ := Obligations.Growing.accept_of_proposesAt_at hrun hnc hx hp3
    have hsl : (W.block 3).slot ≤ (W.block 0).slot + sp.toParams.fg.δt := by
      have h3 := W.slots 3
      have h0 := W.slots 0
      have hg3 : 3 * W.gap ≤ S.δt := W.gap_span
      simp only [Fin.val_zero, Fin.isValue] at h0 h3
      change (W.block 3).slot ≤ (W.block 0).slot + S.δt
      rw [h3, h0]
      change W.start + 3 * W.gap ≤ W.start + 0 * W.gap + S.δt
      omega
    obtain ⟨X, hX, hAX⟩ := Obligations.Growing.cacheCoverage_of_anchor_window_upTo_at hrun hnc
      (fun i => hanc i 3 (Fin.le_last i))
      (fun i => Obligations.Growing.anchorStepAt_iff.mpr (hheights i)) hsl hc0 hlc hx hBx
    -- the reader, on the run's own honest sets
    obtain ⟨hyt, ⟨hle, htj⟩, ht0, -⟩ := hrr.1
    refine Obligations.Growing.reader_cache_covers_at hrun hnc hx hBx hX hAX (hcD.trans hDt) hle
      hyt hft fun hFB => ?_
    -- a reader whose cache is below the last anchor accepts it on the deadline premises
    have hx' : x ∈ truncH H D (tr.time c) := ⟨hx, hcD⟩
    have hFm : ∀ m ≤ j,
        Anc (tr.HonestBlocksAt (truncH H D)) (tr.state y m).fg.F (W.block 3) := by
      intro m hm
      have hgrow : Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F (tr.state y j).fg.F := by
        have h := (Compose.fg_grows (hrun.upTo ht0) hyt hm).2
        rw [Trace.upTo_state tr y (fun q hq => hle q (by omega)), Trace.upTo_state tr y hle] at h
        exact h.mono (RunTrace.honestBlocks_upTo_subset hmono ht0)
      exact Healing.Growing.honest_anc_of_store_anc_at (H := truncH H D) hc0 hlc hx'
        (Healing.Growing.store_anc_of_honest_anc_at hrun hnc hc0 hlc hx (hgrow.trans hFB) hBx)
    by_cases hg : gst ≤ tr.time c
    · -- relay to the reader's first call one delay after the anchor
      have hts := hp3.2.2
      have hgrid : ∀ s : Nat, sp.toParams.slotTime s = (s : Time) * (4 * sp.toParams.Δ) :=
        fun s => by rw [sp.slotTime_eq]; ring
      have hyp : y ∈ H (tr.time c + sp.toParams.Δ) := hrun.antitone (hpD.trans hDt) hyt
      have hgp : AC.gbar gst ≤ tr.time c + sp.toParams.Δ :=
        max_le (by linarith) (by linarith)
      have hpub : sp.toParams.IsPublic (tr.time c + sp.toParams.Δ) :=
        ⟨4 * ((W.block 3).slot : Time) + 1, by rw [hts, hgrid]; ring⟩
      obtain ⟨j₀, xt, fgDue, hj₀⟩ := hrun.tick_of_awake y _ hyp (by linarith) hpub
        (hP.awake y _ ⟨hyp, hpD⟩ hgp hpD)
      obtain ⟨hn₀, ht₀, -, -, hl₀⟩ := hj₀.2.1 0 (List.length_pos_iff.mpr hj₀.1)
      simp only [Nat.add_zero] at hn₀ ht₀ hl₀
      have hex : ∃ i, tr.IsCall y i ∧ tr.time c + sp.toParams.Δ ≤ tr.time i :=
        ⟨j₀, ⟨_, hn₀, hl₀⟩, ht₀.ge⟩
      obtain ⟨hcs, hps⟩ := Nat.find_spec hex
      have hjs : tr.time (Nat.find hex) = tr.time c + sp.toParams.Δ :=
        le_antisymm ((hmono (Nat.find_min' hex ⟨⟨_, hn₀, hl₀⟩, ht₀.ge⟩)).trans ht₀.le) hps
      have hdl : ∀ k ≤ Nat.find hex,
          tr.deadline y k (max (tr.time c) gst) sp.toParams.Δ ≤ tr.time c + sp.toParams.Δ := by
        intro k hk
        have hrs : ∀ k' ≤ k, tr.RestartAt y k' → tr.time k' ≤ AC.gbar gst := fun k' hk' hr => by
          have hk't : tr.time k' ≤ tr.time c + sp.toParams.Δ := (hmono (hk'.trans hk)).trans hjs.le
          exact hP.noRestart y k' ⟨hrun.antitone (hk't.trans (hpD.trans hDt)) hyt,
            hk't.trans hpD⟩ hr
        have h := Compose.deadline_le_of_restarts hrs (max (tr.time c) gst) sp.toParams.Δ
        have hm : max (max (tr.time c) gst) (AC.gbar gst) = tr.time c := by
          rw [max_eq_left hg]
          exact max_eq_left (max_le hg hc0 : AC.gbar gst ≤ tr.time c)
        rwa [hm] at h
      have hFs : Anc (tr.HonestBlocksAt (truncH H D)) (tr.state y (Nat.find hex)).fg.F
          (W.block 3) := by
        rcases le_or_gt (Nat.find hex) j with h | h
        · exact hFm _ h
        · rw [Healing.state_eq_of_noCall h.le fun i hji hi hci =>
            Nat.find_min hex hi ⟨hci, hpD.trans (hDt.trans (htj.trans (hmono hji)))⟩]
          exact hFm j le_rfl
      obtain ⟨k, hks, hak, hkt⟩ := hP.sync.relay x c (W.block 3) hx' (hacc 3) hg y (Nat.find hex)
        ⟨by rw [hjs]; exact hyp, by rw [hjs]; exact hpD⟩ hcs (by rw [hjs]; exact hdl _ le_rfl) hFs
      refine ⟨k, ?_, hak⟩
      by_contra hkj
      have h1 := hmono (not_lt.mp hkj)
      have h2 := hdl k hks
      linarith
    · -- catch-up when the anchor precedes GST
      have hlt : tr.time c < AC.gbar gst := (not_le.mp hg).trans_le (le_max_left gst 0)
      obtain ⟨ks, ⟨-, hzks⟩, hksD⟩ := hP.snapshot
      have hu : AC.gbar gst + 2 * sp.toParams.Δ ≤ D := by
        have := Healing.lt_cutZ (sp := sp) gst
        change AC.gbar gst + 8 * sp.Δ < Healing.cutZ sp.toParams gst at this
        change AC.gbar gst + 2 * sp.Δ ≤ D
        have : (0 : Time) < sp.Δ := hΔ
        linarith
      obtain ⟨k, hk, hak, _⟩ := Healing.accept_before_snapshot (tr := tr)
        (show AC.gbar gst + 2 * sp.toParams.Δ ≤ tr.time j by linarith) fun q hq hfirst =>
          hP.catchUp x c (W.block 3) hx' (hacc 3) hlt y q
            ⟨hrun.antitone (hu.trans hDt) hyt, hu⟩ hfirst (hFm q hq)
      exact ⟨k, hk, hak⟩

end Consensus.Goldilocks.Simulation

end
