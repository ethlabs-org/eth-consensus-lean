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
  change (s : Time) * (4 * Q.run.1.Δ) = 4 * Q.run.1.Δ * s
  ring

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
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hi : (1 : Time) ≤ ((Q.index : Nat) : Time) := by exact_mod_cast Q.index.pos
  change _ ≤ Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.Δ
  rw [show (K S A).params.latency .final Q.index = accepted_latency S A .final Q.index from
    congrFun (congrFun (accepted_coefficients_latency S A) .final) Q.index,
    accepted_latency_final]
  change _ + 4 * _ * Q.run.1.Δ + Q.run.1.Δ ≤ _
  push_cast
  nlinarith

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
  classical
  set H := honestKeys S Q.run.2
  set G := finalGrid S A V Q
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hspc := finalWindow_span_of_offsets (S := S) (A := A) hpat
  -- the recurrence of the query
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) G ⟨finalWindow A, Q.index⟩
      ((Sys (family S) V).cDur (K S A) Q.run) ((Sys (family S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using Q.progress
  have hlen : ((⟨finalWindow A, Q.index⟩ : Recurrence).len : Time) * G.slotLen =
      4 * ((Q.index : Nat) + 3 * c) * Q.params.Δ := by
    simp only [Recurrence.len, hspc]
    change _ * (4 * Q.run.1.Δ) = 4 * _ * Q.run.1.Δ
    push_cast
    ring
  have hL : (0 : Time) < G.slotLen := G.slotLen_pos
  have hi : (1 : Time) ≤ ((Q.index : Nat) : Time) := by exact_mod_cast Q.index.pos
  have hbh : Q.deadline ≤ Q.run.2.horizon := Q.bounded
  have hq : max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) 0 ≤ Q.query := by
    have h1 : G.slotLen ≤ ((((Q.index : Nat) + S.δt : Nat) : Time)) * G.slotLen := by
      have : (1 : Time) ≤ ((((Q.index : Nat) + S.δt : Nat) : Time)) := by push_cast; linarith
      nlinarith
    have := le_max_left (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
      (G.slotTime (finalSeedMin S A V Q a) - 1)
    rw [max_eq_left (le_max_right _ _)]
    linarith
  rw [max_eq_left (le_max_right _ _)] at hq
  have h3cΔ : (0 : Time) ≤ 4 * (((Q.index : Nat) : Time) + 3 * (c : Time)) * Q.params.Δ := by
    positivity
  have hstop : Q.query + ((⟨finalWindow A, Q.index⟩ : Recurrence).len : Time) * G.slotLen ≤
      Q.run.2.horizon := by rw [hlen]; linarith
  obtain ⟨u, s₀, humin, hu0, hus, hut₁, -, hdu, hs₀q, -, hspan, hds⟩ :=
    two_query_placement (δt := S.δt) hrec (by rw [hpat]; simp) hplace hq hstop hstop
  rw [hlen, hspc, finalGrid_slotTime] at hspan
  rw [finalGrid_slotTime] at hs₀q
  -- the time glue
  have hRu := finalSeedMin_spec S A V Q humin
  have hgu : gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts u := by
    have hc := final_catchUp_le_cDur S A V Q
    have hready : gbar Q.gst + 4 * Q.params.Δ <
        (Sys (family S) V).ready (K S A) Q.gst Q.run := by
      change max Q.gst 0 + 4 * Q.params.Δ <
        max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1
      simp only [Regimes.catchUp] at hc
      linarith
    have h1 := ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hut₁
    rw [finalGrid_slotTime] at h1
    linarith
  have hus' : u + Q.params.toParams.fg.δt ≤ s₀ := hus
  have hts : ∀ m n : Nat, m ≤ n → Q.params.ts m ≤ Q.params.ts n := fun m n h =>
    (SA.ts_le_iff Q.params).2 (by exact_mod_cast h)
  have hu₀ : Q.params.ts u ≤ Q.params.ts s₀ := hts _ _ ((Nat.le_add_right _ _).trans hus')
  have hR : Healing.drainTime Q.params a ≤ Q.params.ts s₀ := hRu.trans hu₀
  have hb3 : Q.params.ts (s₀ + 3 * c : Nat) ≤ Q.run.2.horizon := by
    push_cast at hspan hlat ⊢; linarith
  have hb₀ : Q.params.ts s₀ ≤ Q.run.2.horizon := (hts _ _ (by omega)).trans hb3
  have hgS₀ : gbar Q.gst ≤ Q.params.ts s₀ + 6 * Q.params.Δ := by linarith
  have hgSu : gbar Q.gst ≤ Q.params.ts u + 6 * Q.params.Δ := by linarith
  -- shared premises
  have hc : Healing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync S Q.run.2 Q.hn Q.valid
      (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision) hnet Q.healthy.2.1.2
  -- the seed and the anchors
  obtain ⟨Ps, hPs⟩ := hpropose u hu0 (hu₀.trans hb₀) hdu
  have hoff : ∀ i : Fin 4, ![0, c, 2 * c, 3 * c] i ≤ 3 * c := by
    intro i; fin_cases i <;> simp <;> omega
  have hduty : ∀ i : Fin 4, HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (s₀ + ![0, c, 2 * c, 3 * c] i)
      ((Sys (family S) V).cDur (K S A) Q.run) (G.slotTime (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
    intro i
    exact hds _ (by rw [hpat]; fin_cases i <;> simp)
  choose P hP using fun i : Fin 4 => hpropose _
    (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hu0 ((Nat.le_add_right _ _).trans hus'))
      (Nat.le_add_right _ _))
    ((hts _ _ (by have := hoff i; omega)).trans hb3) (hduty i)
  have hδ2 : 2 ≤ Q.params.toParams.fg.δt := by rw [hδeq]; omega
  have hh₀ := seed_height_held hreset hc hs hδ2 hPs hu0 hRu (by linarith) (hP 0)
    (by simpa using hus') (by simpa using hb₀) hgSu
  have hsteps := anchorSteps_gap hreset hc hs hc2 hdel (s₀ := s₀) (P := P) hP
    (by simpa using hR) hb3 (by simpa using hgS₀) hh₀
  -- the window fields
  have hready : ∀ i, Regimes.ReadyAt Q.trace H ((Sys (family S) V).cDur (K S A) Q.run)
      (P i).proposer (Q.params.toParams.slotTime (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
    intro i
    have hr := hduty i
    have hmem : runProposer S Q.run.2 Q.hn (s₀ + ![0, c, 2 * c, 3 * c] i) ∈
        Q.run.2.sel (.proposer (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
      simp only [runProposer_eq, dite_eq_left hr.1]
      exact Finset.min'_mem _ _
    have hR' := hr.2 _ hmem
    rw [finalGrid_slotTime] at hR'
    have hti : Q.params.ts (s₀ + ![0, c, 2 * c, 3 * c] i : Nat) ≤ Q.run.2.horizon :=
      (hts _ _ (by have := hoff i; omega)).trans hb3
    have h0 : (0 : Time) ≤ Q.params.ts (s₀ + ![0, c, 2 * c, 3 * c] i : Nat) := by
      simp only [SA.SAParams.ts]; positivity
    have hnode := ready_transport S Q.run.2 Q.hn Q.valid h0 hti hR'
    rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn _)) =
      runProposer S Q.run.2 Q.hn _ from Q.run.2.key.symm_apply_apply _] at hnode
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpr, -⟩ := hP i
    rw [hpr, Q.params.slotTime_eq]
    exact hnode
  have h3D : Q.params.ts (s₀ + 3 * c : Nat) + Q.params.Δ ≤ Q.deadline := by
    push_cast at hspan hlat ⊢; linarith
  have hlast : Q.query < Q.params.ts (s₀ + 3 * c : Nat) := hs₀q.trans_le (hts _ _ (by omega))
  obtain ⟨W, hWs, hWg, hWb⟩ := finalWindow_data_of_honest_anchors_gap Q hreset hc hc2 h3c s₀ hP
    hR hb3 (by rw [Q.params.slotTime_eq]; simpa [SA.SAParams.ts] using hs₀q)
    (by rw [Q.params.slotTime_eq]; simp only [SA.SAParams.ts] at h3D; push_cast at h3D ⊢
        linarith)
    hready (hcarrier _ _ (by simpa using hP 3) (by simpa using hlast) (by simpa using h3D))
  subst hWs hWb hWg
  refine ⟨W, rfl, ?_, ⟨runProposer S Q.run.2 Q.hn, digestOf S Q.run.2, Q.gst, ΔR, a,
    Q.run.2.horizon, hreset, hc, hP, hR, hb3⟩, hsteps⟩
  have ht3 : Q.trace.time (W.cut 3) = Q.params.ts (W.start + 3 * W.gap : Nat) := by
    rw [(W.proposals 3).2.2, W.slots 3, Q.params.slotTime_eq]
    simp [SA.SAParams.ts]
  rw [ht3]
  exact h3D

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
