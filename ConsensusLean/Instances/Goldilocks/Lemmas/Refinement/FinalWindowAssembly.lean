module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowPlacement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowSeed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AnchorStepsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowFieldsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalDutyProposal

public section

/-! # Goldilocks Refinement: assembly of the route-A final window (#136)

consensus-lean#136. `final_window_extract_of` has the statement of the leaf
`final_window_extract` (Accepted.lean), from explicit premises only:

* (H1) `hreset`: the reset premises `ResetPremisesUpTo` through the horizon, at GST `Q.gst`,
  with the run proposer and digest (the M1′ reset `a`);
* (H2) `hpropose`: duty → proposal (`HonestReadyIn` at slot `s` gives `HonestProposalRun` at `s`);
* (H3) `hplace`: the placement `(P)` of the two queries, with `u_min = finalSeedMin Q a`;
* (H4) `hcarrier`: the OPEN `carrierProcessed` field of `FinalWindowData` for the last anchor.

`final_window_extract_of_gap` is the general form (workbench `two_bound_network.md` §4): an
anchor gap `c` with `2 ≤ c`, the span `3c ≤ δt`, the final pattern `[0, c, 2c, 3c]` (`hpat`),
`ΔF` a parameter (`HSSharedUpTo` at `ΔF` and `6Δ + ΔF ≤ 4Δ·c` explicit) and the latency budget
`hlat` of a span-`3c` window explicit. `final_window_extract_of_shared` is its instance at the
row gap `c = cF r` of the assumptions (latency `final_latency_gap`), and
`final_window_extract_of` instantiates the protocol row delay `ΔF := rowDelay` only there.
Proved here: `CatchRun 2Δ` (`catchRun_of_psync`), the recurrence from `Q.progress`, the
two queries (`two_query_placement`), the seed height (`seed_height_held`), the anchor steps
(`anchorSteps_gap`), the window fields (`finalWindow_data_of_honest_anchors_gap`, readiness by
`ready_transport`), the slack `ts(s₀ + 3c) + Δ ≤ deadline` from `hlat`, and the time glue. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The least seed slot of a reset at `a`: past the drain, `slot(a) + 2k + 5`. A slot count only
(#145): `ḡ + 4Δ ≤ t_u` is not part of it, the assembly reads it off the first query, which is
strictly after `ready ≥ ḡ + 18Δ + 1`. -/
noncomputable abbrev finalSeedMin (Q : FinalQuery S A V) (a : Time) : Nat :=
  Q.params.slot a + 2 * Q.params.k + 5

/-- The grid of the run's family. -/
noncomputable abbrev finalGrid (Q : FinalQuery S A V) : TimeGrid :=
  (family S (Model.pubOf Q.run.1)).skel.grid

/-- The grid's slot time is the protocol slot time. -/
theorem finalGrid_slotTime (Q : FinalQuery S A V) (s : Nat) :
    (finalGrid S A V Q).slotTime s = Q.params.ts s := by
  sorry

/-- **Seed glue.** A slot `u ≥ finalSeedMin Q a` is after the drain of `a`. -/
theorem finalSeedMin_spec (Q : FinalQuery S A V) {a : Time} {u : Nat}
    (hu : finalSeedMin S A V Q a ≤ u) :
    Healing.drainTime Q.params a ≤ Q.params.ts u := by
  have hk : Q.params.k = S.k := rfl
  have hu' : Q.params.slot a + 2 * Q.params.k + 5 ≤ u := hu
  rw [Healing.drainTime_eq]
  exact (SA.ts_le_iff Q.params).2 (by push_cast; omega)

/-- The final pattern with offsets `[0, c, 2c, 3c]` spans `3c` slots. -/
theorem finalWindow_span_of_offsets {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) : (finalWindow A).span = 3 * c := by
  unfold Pattern.span
  rw [hpat]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

/-- **The final latency budget at the row gap `c = cF r`**: `accepted_latency .final =
8(X + 3c) + 2` engine delays cover the window of span `3c` and one node delay,
`4(X + 3c)Δ + Δ`. -/
theorem final_latency_gap (Q : FinalQuery S A V) :
    Q.query + 4 * ((Q.index : Nat) + 3 * cF A.rowRatio) * Q.params.Δ + Q.params.Δ ≤ Q.deadline := by
  sorry

/-- **Final-window extraction at a gap `c` and a forwarding delay `ΔF`** (route A). From the
shared HS premises `hs` at `ΔF`, the delivery inequality `hdel : 6Δ + ΔF ≤ 4Δ·c`, the span
`3c ≤ δt`, the final pattern `[0, c, 2c, 3c]` (`hpat`) and the latency budget `hlat` of a
pattern of span `3c`: a window of four honest anchors at `start + [0, c, 2c, 3c]` (`W.gap = c`)
after the query, its route-A run premises and its three anchor steps (`anchorSteps_gap`). -/
theorem final_window_extract_of_gap (Q : FinalQuery S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c])
    {ΔR a ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon)
    (hdel : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (c : Nat))
    (hlat : Q.query + 4 * ((Q.index : Nat) + 3 * c) * Q.params.Δ + Q.params.Δ ≤ Q.deadline)
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, W.gap = c ∧
      Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * W.gap) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) := by
  sorry

/-- **Final-window extraction at a forwarding delay `ΔF`** (route A, gap `c = cF r`). The
statement of `final_window_extract`, with the shared HS premises `hs` at `ΔF` and the delivery
inequality `hdel` explicit: `final_window_extract_of_gap` at `c = cF r`, with the latency
`final_latency_gap`. -/
theorem final_window_extract_of_shared (Q : FinalQuery S A V) {ΔR a ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon)
    (hdel : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (cF A.rowRatio : Time))
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * cF A.rowRatio) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) := by
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hdl := final_latency_gap S A V Q
  obtain ⟨W, hWg, hslack, ⟨proposer, dg, g, ΔF', a', b, hp, hc, hP, hR, hb⟩, hsteps⟩ :=
    final_window_extract_of_gap S A V Q A.two_le_cF A.timeout (finalWindow_offsets A) hs hdel hdl
      hreset hpropose hplace hcarrier
  rw [hWg] at hP
  rw [hWg] at hb
  exact ⟨W, hslack, ⟨proposer, dg, g, ΔF', a', b, hp, hc, hP, hR, hb⟩, hsteps⟩

/-- **Final-window extraction from explicit premises** (route A, gap 2). The statement of
`final_window_extract`. The forwarding delay is instantiated here only: the protocol row delay
`ΔF := rowDelay`, with the shared HS premises `FinalQuery.hsSharedUpTo`. -/
theorem final_window_extract_of (Q : FinalQuery S A V) {ΔR a : Time}
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * cF A.rowRatio) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) := by
  exact final_window_extract_of_shared S A V Q Q.hsSharedUpTo Q.rowDelay_delivery
    hreset hpropose hplace hcarrier

end Consensus.Goldilocks.Refinement

end
