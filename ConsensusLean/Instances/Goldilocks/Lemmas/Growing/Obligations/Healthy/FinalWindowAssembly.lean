module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowSeed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.AnchorStepsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalDutyProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowAssembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalQueryTiming
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Assembly of the route-A final window, under growing faults

The growing form of `Obligations/FinalWindowAssembly`:

* `final_latency_gap_at`: the final latency budget covers a window of span `3c` at the FG gap
  `c = fgSlots` and one node delay;
* `final_window_extract_of_gap_at`: from the shared HS premises at `ΔF`, the delivery inequality,
  the span `3c ≤ δt`, the final pattern `[0, c, 2c, 3c]`, the latency budget of a span-`3c`
  window, the finite reset premises through the horizon, duty to proposal (`hpropose`), the
  two-query placement (`hplace`) and the carrier of the last anchor (`hcarrier`): a final window
  at gap `c` with its slack `t(cut 3) + Δ ≤ deadline`, its anchor run and its three anchor steps.

The slots of the window and their time glue are the static `final_window_slots`. The catch-up
`CatchRun 2Δ` is `catchRun_of_psync_at`; readiness of the anchor proposers is
`ready_transport_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The grid's slot time is the protocol slot time. -/
theorem finalGridAt_slotTime (Q : FinalQueryAt S A V) (s : Nat) :
    (finalGridAt S A V Q).slotTime s = Q.params.ts s := by
  change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
  ring

/-- **Seed glue.** A slot `u ≥ finalSeedMinAt Q a` is after the drain of `a`. -/
theorem finalSeedMinAt_spec (Q : FinalQueryAt S A V) {a : Time} {u : Nat}
    (hu : finalSeedMinAt S A V Q a ≤ u) :
    Healing.drainTime Q.params a ≤ Q.params.ts u := by
  have hu' : Q.params.slot a + 2 * Q.params.k + 5 ≤ u := hu
  rw [Healing.drainTime_eq]
  exact (SA.ts_le_iff Q.params).2 (by exact_mod_cast hu')

/-- **The final latency budget at the FG gap `c = fgSlots`**: `contract_latency .final =
8(X + 3c) + 2` engine delays cover the window of span `3c` and one node delay. -/
theorem final_latency_gap_at (Q : FinalQueryAt S A V) :
    Q.query + 4 * ((Q.index : Nat) + 3 * A.fgSlots) * Q.params.Δ + Q.params.Δ ≤ Q.deadline := by
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hi : (1 : Time) ≤ ((Q.index : Nat) : Time) := by exact_mod_cast Q.index.pos
  change _ ≤ Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.ΔAC
  rw [show (K S A).params.latency .final Q.index = contract_latency S A .final Q.index from
    congrFun (congrFun (contract_coefficients_latency S A) .final) Q.index,
    contract_latency_final]
  change _ + 4 * _ * Q.run.1.ΔAC + Q.run.1.ΔAC ≤ _
  push_cast
  linarith only [hd, hi]

/-- **Final-window extraction at a gap `c` and a forwarding delay `ΔF`** (route A), under growing
faults. A window of four honest anchors at `start + [0, c, 2c, 3c]` (`W.gap = c`) after the query,
the slack `t(cut 3) + Δ ≤ deadline`, its anchor run and its three anchor steps. -/
theorem final_window_extract_of_gap_at (Q : FinalQueryAt S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c])
    {ΔR a ΔF : Time}
    (hs : Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔF
      Q.run.2.horizon)
    (hdel : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (c : Nat))
    (hlat : Q.query + 4 * ((Q.index : Nat) + 3 * c) * Q.params.Δ + Q.params.Δ ≤ Q.deadline)
    (hreset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
      (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔR a
          Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGridAt S A V Q).slotTime s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.Growing.HonestProposalRun Q.trace Q.keys
        (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
      Q.query + (finalGridAt S A V Q).slotLen)
    (hcarrier : ∀ s P, Healing.Growing.HonestProposalRun Q.trace Q.keys
      (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline) :
    ∃ W : FinalWindowDataAt S A V Q, W.gap = c ∧
      Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧ W.AnchorRun ∧ W.AnchorSteps := by
  classical
  let H := Q.keys
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  -- the slots of the window and their time glue
  obtain ⟨u, s₀, hu0, hus', hdu, hanc, huh, hb₀, hb3, hRu, hR, hgu, hgSu, hgS₀, hs₀q, hlast,
    h3D⟩ := final_window_slots S A V Q.run Q.hn Q.index Q.gst Q.query Q.progress Q.bounded hpat
      hlat hplace
  -- shared premises
  have hc : Healing.Growing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid
      (noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision) hnet
      (fun v t ht hb _ hv => Q.healthy.2.1.2 v t ht hb hv)
  -- the seed and the anchors
  obtain ⟨Ps, hPs⟩ := hpropose u hu0 huh hdu
  choose P hP using fun i : Fin 4 => hpropose _ (hanc i).1 (hanc i).2.1 (hanc i).2.2
  have hδ2 : 2 ≤ Q.params.toParams.fg.δt :=
    hc2.trans ((Nat.le_mul_of_pos_left c (by decide)).trans h3c)
  have hh₀ := seed_height_held_at hreset hc hs hδ2 hPs hu0 hRu hgu (hP 0) hus' hb₀ hgSu
  have hsteps := anchorSteps_gap_at hreset hc hs hc2 hdel (s₀ := s₀) (P := P) hP
    hR hb3 hgS₀ hh₀
  -- the window fields
  have hready : ∀ i, Regimes.Growing.ReadyAt Q.trace H
      ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      (P i).proposer (Q.params.toParams.slotTime (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
    intro i
    obtain ⟨-, hti, hr⟩ := hanc i
    have hmem : runProposer ⟨S, stock⟩ Q.run.2 Q.hn (s₀ + ![0, c, 2 * c, 3 * c] i) ∈
        Q.run.2.sel (.proposer (s₀ + ![0, c, 2 * c, 3 * c] i)) := by
      rw [runProposer_eq ⟨S, stock⟩ Q.run.2 Q.hn]
      split
      · exact Finset.min'_mem _ _
      · exact absurd hr.1 ‹_›
    have hR' := (hr.2 _ hmem).1
    rw [finalGridAt_slotTime S A V Q] at hR'
    have h0 : (0 : Time) ≤ Q.params.ts (s₀ + ![0, c, 2 * c, 3 * c] i : Nat) :=
      mul_nonneg (mul_nonneg zero_le_four hΔ.le) (Int.natCast_nonneg _)
    have hnode := ready_transport_at ⟨S, stock⟩ Q.run.2 Q.hn Q.valid h0 hti hR'
    erw [show Q.run.2.ownKey (Q.run.2.key (runProposer ⟨S, stock⟩ Q.run.2 Q.hn _)) =
      runProposer ⟨S, stock⟩ Q.run.2 Q.hn _ from Q.run.2.key.symm_apply_apply _] at hnode
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpr, -⟩ := hP i
    rw [hpr, Q.params.slotTime_eq]
    exact hnode
  obtain ⟨W, hWs, hWg, hWb⟩ := finalWindow_data_of_honest_anchors_gap_at Q hreset hc hc2 h3c s₀
    hP hR hb3 (by rw [Q.params.slotTime_eq]; exact hs₀q)
    (by rw [Q.params.slotTime_eq]; simp only [SA.SAParams.ts] at h3D; push_cast at h3D ⊢
        linarith only [h3D, hΔ])
    hready (hcarrier _ _ (hP 3) hlast h3D)
  subst hWs hWb hWg
  refine ⟨W, rfl, ?_, W.anchorRun_iff.mpr
      ⟨runProposer ⟨S, stock⟩ Q.run.2 Q.hn, digestOf ⟨S, stock⟩ Q.run.2,
    Q.gst, ΔR, a, Q.run.2.horizon, hreset, hc, hP, hR, hb3⟩, W.anchorSteps_iff.mpr hsteps⟩
  have ht3 : Q.trace.time (W.cut 3) = Q.params.ts (W.start + 3 * W.gap : Nat) := by
    rw [(W.proposals 3).2.2, W.slots 3, Q.params.slotTime_eq]
    rfl
  rw [ht3]
  exact h3D

end Consensus.Goldilocks.Obligations.Growing

end
