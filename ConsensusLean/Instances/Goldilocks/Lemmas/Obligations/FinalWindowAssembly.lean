module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowPlacement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowSeed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.AnchorStepsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowFieldsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalQueryTiming
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Obligations: assembly of the route-A final window

`final_window_extract_of` has the statement of the leaf
`final_window_extract` (Concrete.lean), from explicit premises only:

* (H1) `hreset`: the reset premises `ResetPremisesUpTo` through the horizon, at GST `Q.gst`,
  with the run proposer and digest (the reset `a` of the frame-window route, `Healing.M1`);
* (H2) `hpropose`: duty → proposal (`HonestReadyIn` at slot `s` gives `HonestProposalRun` at `s`);
* (H3) `hplace`: the placement `(P)` of the two queries, with `u_min = finalSeedMin Q a`;
* (H4) `hcarrier`: the OPEN `carrierProcessed` field of `FinalWindowData` for the last anchor.

`final_window_extract_of_gap` is the general form: an
anchor gap `c` with `2 ≤ c`, the span `3c ≤ δt`, the final pattern `[0, c, 2c, 3c]` (`hpat`),
`ΔF` a parameter (`HSSharedUpTo` at `ΔF` and `6Δ + ΔF ≤ 4Δ·c` explicit) and the latency budget
`hlat` of a span-`3c` window explicit. `final_window_extract_of_shared` is its instance at the
FG gap `c = fgSlots` of the assumptions (latency `final_latency_gap`), and
`final_window_extract_of` instantiates the protocol FG delay `ΔF := protoFGDelay` only there.
The slots of the window are `final_window_slots` (FinalQueryTiming.lean): the recurrence from
`Q.progress`, the two queries (`two_query_placement`), the time glue and the slack
`ts(s₀ + 3c) + Δ ≤ deadline` from `hlat`. Proved here: `CatchRun 2Δ` (`catchRun_of_psync`), the
seed height (`seed_height_held`), the anchor steps (`anchorSteps_gap`) and the window fields
(`finalWindow_data_of_honest_anchors_gap`, readiness by `ready_transport`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

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
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
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
  classical
  let H := honestKeys S Q.run.2
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  -- the slots of the window and their time glue
  obtain ⟨u, s₀, hu0, hus', hdu, hanc, huh, hb₀, hb3, hRu, hR, hgu, hgSu, hgS₀, hs₀q, hlast,
    h3D⟩ := final_window_slots S A V Q.run Q.hn Q.index Q.gst Q.query Q.progress Q.bounded hpat
      hlat hplace
  -- shared premises
  have hc : Healing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync S Q.run.2 Q.hn Q.constant Q.valid
      (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision) hnet
      (fun v hv t ht hb => Q.healthy.2.1.2 v t ht hb
        ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hv))
  -- the seed and the anchors
  obtain ⟨Ps, hPs⟩ := hpropose u hu0 huh hdu
  choose P hP using fun i : Fin 4 => hpropose _ (hanc i).1 (hanc i).2.1 (hanc i).2.2
  have hδ2 : 2 ≤ Q.params.toParams.fg.δt :=
    hc2.trans ((Nat.le_mul_of_pos_left c (by decide)).trans h3c)
  have hh₀ := seed_height_held hreset hc hs hδ2 hPs hu0 hRu hgu (hP 0) hus' hb₀ hgSu
  have hsteps := anchorSteps_gap hreset hc hs hc2 hdel (s₀ := s₀) (P := P) hP
    hR hb3 hgS₀ hh₀
  -- the window fields
  have hready : ∀ i, Regimes.ReadyAt Q.trace H ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      (P i).proposer (Q.params.toParams.slotTime (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
    intro i
    obtain ⟨-, hti, hr⟩ := hanc i
    have hmem : runProposer S Q.run.2 Q.hn (s₀ + ![0, c, 2 * c, 3 * c] i) ∈
        Q.run.2.sel (.proposer (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
      simp only [runProposer_eq, dite_eq_left hr.1]
      exact Finset.min'_mem _ _
    have hR' := (hr.2 _ hmem).1
    rw [finalGrid_slotTime S A V Q] at hR'
    have h0 : (0 : Time) ≤ Q.params.ts (s₀ + ![0, c, 2 * c, 3 * c] i : Nat) :=
      mul_nonneg (mul_nonneg zero_le_four hΔ.le) (Int.natCast_nonneg _)
    have hnode := ready_transport S Q.run.2 Q.hn Q.valid h0 hti hR'
    rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn _)) =
      runProposer S Q.run.2 Q.hn _ from Q.run.2.key.symm_apply_apply _] at hnode
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpr, -⟩ := hP i
    rw [hpr, Q.params.slotTime_eq]
    exact hnode
  obtain ⟨W, hWs, hWg, hWb⟩ := finalWindow_data_of_honest_anchors_gap Q hreset hc hc2 h3c s₀ hP
    hR hb3 (by rw [Q.params.slotTime_eq]; exact hs₀q)
    (by rw [Q.params.slotTime_eq]; simp only [SA.SAParams.ts] at h3D; push_cast at h3D ⊢
        linarith only [h3D, hΔ])
    hready (hcarrier _ _ (hP 3) hlast h3D)
  subst hWs hWb hWg
  refine ⟨W, rfl, ?_, ⟨runProposer S Q.run.2 Q.hn, digestOf S Q.run.2, Q.gst, ΔR, a,
    Q.run.2.horizon, hreset, hc, hP, hR, hb3⟩, hsteps⟩
  have ht3 : Q.trace.time (W.cut 3) = Q.params.ts (W.start + 3 * W.gap : Nat) := by
    rw [(W.proposals 3).2.2, W.slots 3, Q.params.slotTime_eq]
    rfl
  rw [ht3]
  exact h3D

/-- **Final-window extraction at a forwarding delay `ΔF`** (route A, gap `c = fgSlots`). The
statement of `final_window_extract`, with the shared HS premises `hs` at `ΔF` and the delivery
inequality `hdel` explicit: `final_window_extract_of_gap` at `c = fgSlots`, with the latency
`final_latency_gap`. -/
theorem final_window_extract_of_shared (Q : FinalQuery S A V) {ΔR a ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon)
    (hdel : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (A.fgSlots : Time))
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, A.fgSlots, 2 * A.fgSlots, 3 * A.fgSlots] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * A.fgSlots) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) := by
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hdl := final_latency_gap S A V Q
  obtain ⟨W, hWg, hslack, ⟨proposer, dg, g, ΔF', a', b, hp, hc, hP, hR, hb⟩, hsteps⟩ :=
    final_window_extract_of_gap S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A) hs hdel
      hdl hreset hpropose hplace hcarrier
  rw [hWg] at hP
  rw [hWg] at hb
  exact ⟨W, hslack, ⟨proposer, dg, g, ΔF', a', b, hp, hc, hP, hR, hb⟩, hsteps⟩

/-- **Final-window extraction from explicit premises** (route A, gap 2). The statement of
`final_window_extract`. The forwarding delay is instantiated here only: the protocol FG delay
`ΔF := protoFGDelay`, with the shared HS premises `FinalQuery.hsSharedUpTo`. -/
theorem final_window_extract_of (Q : FinalQuery S A V) {ΔR a : Time}
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, A.fgSlots, 2 * A.fgSlots, 3 * A.fgSlots] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * A.fgSlots) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) := by
  exact final_window_extract_of_shared S A V Q Q.hsSharedUpTo Q.protoFGDelay_delivery
    hreset hpropose hplace hcarrier

end Consensus.Goldilocks.Obligations

end
