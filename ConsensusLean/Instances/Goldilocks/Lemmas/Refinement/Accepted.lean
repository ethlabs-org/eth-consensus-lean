module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Final

public section

/-! # Acceptance assembly with finite guarantee witnesses

The assumptions are fixed before choosing guarantees. The three named coefficient
holes and five direct adapter holes are joint obligations, not independent arbitrary
choices. They do not prove acceptance. Do not import into Main/Solution.
The local pattern is a fixed function of Setup's timeout; no legacy consecutive-run
formula or dependence of timeout on the outer gap is imposed here.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

/-- Four-anchor window for the one-delivery-bound model, cF=2 and δt≥4.
First-descendant row service, inherited progress and cache joins remain OPEN. -/
def finalWindow (S : Setup) : Pattern :=
  ⟨[0, S.δt - 1, S.δt + 1, S.δt + 3], by simp⟩

/-- Fixed timeout and outage assumptions. The pattern is determined by Setup,
not chosen by a caller; outer gaps never enter the timeout bound. -/
structure AcceptanceAssumptions (S : Setup) where
  timeout : 4 ≤ S.δt
  lookback : ℕ+

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure AcceptanceCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- OPEN numeric witness, chosen jointly with the adapter proofs below. -/
noncomputable def accepted_catchUp (S : Setup) (A : AcceptanceAssumptions S) : ℕ+ := by
  sorry

/-- OPEN finite healing witness; no whole-run progress premise may be added. -/
noncomputable def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- OPEN finite latency witness, at every outer gap, independent of timeout. -/
noncomputable def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- The same three witnesses are used by every adapter. -/
noncomputable def accepted_coefficients (S : Setup) (A : AcceptanceAssumptions S) :
    AcceptanceCoefficients :=
  ⟨accepted_catchUp S A, accepted_heal S A, accepted_latency S A⟩

/-- Standard fixed resilience fractions; only guarantee coefficients vary.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (8 * S.k - 8)
    (min A.lookback (4 * S.k - 6)) C.heal C.latency with η := A.lookback }
  progress := fun cap X => .recur ⟨if cap = .final then finalWindow S else Pattern.single, X⟩

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (8 * S.k - 8)
        (min A.lookback (4 * S.k - 6)) C.heal C.latency with η := A.lookback } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

/-- The fixed engine-unit coefficients imply the node arming lag and phase-sensitive (V).
This is only the time-window adapter, not network or participation transport. -/
theorem acceptance_outage_times (S : Setup) (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) (pub : Model.Public) (hn : 1 ≤ pub.n)
    (T b₀ b₁ : Time)
    (h : Consensus.OutageTimes (acceptanceContract A C).params pub.Δ T b₀ b₁) :
    Regimes.OutageWindowTimes (S.params pub hn) T b₀ b₁ := by
  obtain ⟨hT, hlag, horder, hbudget⟩ := h
  have hk : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  have hd : (1 : Int) ≤ pub.Δ := pub.Δ_pos
  have hlcast : ((8 * S.k - 8 : Nat) : Int) = 8 * (S.k : Int) - 8 := by
    omega
  have hbcast : ((4 * S.k - 6 : Nat) : Int) = 4 * (S.k : Int) - 6 := by
    omega
  have hb : ((min A.lookback (4 * S.k - 6) : Nat) : Int) ≤ 4 * (S.k : Int) - 6 := by
    rw [← hbcast]
    exact_mod_cast (min_le_right (A.lookback : Nat) (4 * S.k - 6))
  change T + ((8 * S.k - 8 : Nat) : Int) * pub.Δ ≤ b₀ at hlag
  change b₁ ≤ b₀ + ((min A.lookback (4 * S.k - 6) : Nat) : Int) * pub.Δ at hbudget
  rw [hlcast] at hlag
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt pub.Δ_pos)
  have hmod := Int.emod_lt_of_pos (b₀ - 6 * (pub.Δ + 1))
    (show 0 < 4 * (pub.Δ + 1) by linarith)
  change 0 ≤ T ∧ T + (4 * (S.k : Int) - 4) * (pub.Δ + 1) ≤ b₀ ∧
    b₀ ≤ b₁ ∧ b₁ - b₀ + (b₀ - 6 * (pub.Δ + 1)) % (4 * (pub.Δ + 1)) ≤
      (4 * (S.k : Int) - 2) * (pub.Δ + 1)
  refine ⟨hT, ?_, horder, ?_⟩ <;> nlinarith

noncomputable abbrev K (S : Setup) (A : AcceptanceAssumptions S) :=
  acceptanceContract A (accepted_coefficients S A)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- R8, claims C0.1/C0.2/F.2, node outputs_valid. NO PAPER PROOF for
engine/read transport; replacement endpoint: engine_outputValid. -/
theorem accepted_outputValid : (Sys (family S) V).HoldsAlways fun r =>
    ∀ c g, schema.output c = some g → OutputValid r.2 g := by
  exact shape_outputValid V S

/-- R8, claims C0.1/C0.2/F.2, node outputs_nested. NO PAPER PROOF for
engine chain transport; replacement endpoint: engine_nested. -/
theorem accepted_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂ := by
  exact shape_nested V S

/-- R8, claims F.2, node finalized_monotone. NO PAPER PROOF for engine
read transport; replacement endpoint: engine_finalMonotone. -/
theorem accepted_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0 := by
  exact shape_finalMonotone V S

/-- R7, claims G0.5 and G1.1–G1.5, node final_accountable.
NO PAPER PROOF for held-tree evidence/view and collision transport. Raw
GenesisFresh is not a premise here: the encoding must discharge root separation. -/
theorem accepted_finalAccountable : ∀ g, schema.output .final = some g →
    (Sys (family S) V).Holds (fun _ => True) fun r =>
      (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable
        (K S A).params.α g 0 := by
  exact shape_finalAccountable V S (K S A) (by norm_num [Params.standard])

/-- A single reader-conditional final query, with the original engine-scaled latency.
No supplier conclusion is a new premise of Healthy. -/
structure FinalQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (family S) V).Healthy (K S A) gst run
  progress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final index
    ((Sys (family S) V).ready (K S A) gst run) run.2.horizon run
  mature : (Sys (family S) V).heal (K S A) .final index gst run ≤ query
  bounded : query + ((K S A).params.latency .final index : Time) * run.1.Δ ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (family S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency .final index : Time) * run.1.Δ)

namespace FinalQuery

variable {S A V}

abbrev params (Q : FinalQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : FinalQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev deadline (Q : FinalQuery S A V) : Time :=
  Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.Δ

end FinalQuery

/-- Operational window witnesses only. The processing field is an OPEN endpoint-specific
transport budget, not acceptance or a freely chosen output delay. Source: workbench b3ca078,
four-anchor-window.md and fixed-timeout-synthesis.md. -/
structure FinalWindowData (Q : FinalQuery S A V) where
  start : Nat
  block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + (![0, S.δt - 1, S.δt + 1, S.δt + 3] a)
  proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a)
  accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a)
  ready : ∀ a, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a))
  fresh : Q.query < Q.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline
  chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (block a) (block b)
  /-- Actual canonical processing before the exact query deadline; deriving sufficient slack
  from the jointly chosen accepted_latency remains OPEN. No acceptance is assumed here. -/
  carrierProcessed : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
    ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline

namespace FinalWindowData

variable {S A V} {Q : FinalQuery S A V} (W : FinalWindowData S A V Q)

/-- Use the actual last anchor's store, not an independently chosen chain-state map. -/
noncomputable abbrev store := (Q.trace.post (W.cut 3)).fg
noncomputable abbrev state (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) := W.store.σ B.root
abbrev OnChain (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B (W.block 3)
abbrev Extends (_W : FinalWindowData S A V Q)
    (B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B C

/-- An actual entry-creating transition, whether justification or timeout. -/
def Entry (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  W.OnChain B ∧ (W.state B).Th = B.root ∧ (W.state B).ThSlot = B.slot

/-- The actual first crossing after A0, or A0's own newly created entry. -/
def Selected (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  W.Entry B ∧ W.Extends (W.block 0) B ∧
    (B = W.block 0 ∨
      (W.start + 1 ≤ B.slot ∧ B.slot ≤ W.start + (S.δt - 1) ∧
        ∀ D, W.OnChain D → W.Extends (W.block 0) D → W.Extends D B →
          W.start < D.slot → D.slot < B.slot → (W.state D).Th = (W.state (W.block 0)).Th))

/-- No crossing of the inherited entry on the serving parent's chain. -/
def Uncrossed (P : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  ∀ D, W.Extends (W.block 0) D → W.Extends D P →
    (W.state D).h = (W.state (W.block 0)).h ∧ (W.state D).Th = (W.state (W.block 0)).Th

/-- Quorum counts identities once, including previously credited rows. -/
def InheritedProgress : Prop :=
  ∀ P, (W.block 1).parent = some P.root → W.Extends (W.block 0) P →
    (W.state (W.block 0)).ThSlot < W.start → W.Uncrossed P →
    ∃ ids : Finset (Fin Q.params.n), Q.params.toParams.fg.q ≤ ids.card ∧
      ∀ x ∈ ids, x ∈ (W.state P).prog ∨
        ∃ a ∈ (Q.trace.state (W.block 1).proposer (W.cut 1)).fg.atts,
          a.val = x ∧ a.WellFormed ∧ (W.state P).validAtt a ∧
          a.h = (W.state P).h ∧ a.T = (W.state P).Th

/-- Only the selected first descendant has the d−2 exposure bound. -/
def FirstCrossing : Prop :=
  ∃ B, W.Selected B ∧
    (B = W.block 0 ∨
      (B.slot ≤ W.start + (S.δt - 1) ∧ W.start + (S.δt - 1) - B.slot ≤ S.δt - 2))

/-- A justification on the surviving chain is distinct from a timeout crossing. -/
def JustifiedBy (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (v : Nat) : Prop :=
  ∃ D, W.OnChain D ∧ W.Extends B D ∧ D.slot ≤ v ∧
    (W.state D).J = B.root ∧ (W.state D).hj = (W.state B).h

open Classical in
/-- Selected entry or its actual bound successor, at the designated exposing anchor.
An arbitrary no-timeout entry is deliberately not admitted by this domain. -/
def Protected (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (e : Nat) : Prop :=
  (W.Selected B ∧ e = if B = W.block 0 then W.start else W.start + (S.δt - 1)) ∨
  (∃ D, W.Selected D ∧ W.Entry B ∧ W.Extends D B ∧
    (W.state B).J = D.root ∧ (W.state B).bound ∧
    B.slot ≤ W.start + (S.δt + 1) ∧
    e = if B.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt - 1)
      else W.start + (S.δt + 1))

/-- Exact target rows with actual signing provenance; prior matching reports count.
Timing is only in this quorum branch, never imposed on already-justified entries.
The pair is tested against the actual parent, and identities are not multiplied. -/
def TargetRows (B P : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (e : Nat) (a : Fin 4) : Prop :=
  (W.state P).h = (W.state B).h ∧ (W.state P).Th = B.root ∧
  ∃ ids : Finset (Fin Q.params.n), Q.params.toParams.fg.q ≤ ids.card ∧
    ∀ x ∈ ids, x ∈ honestKeys S Q.run.2 ∧ ∃ row j,
      Q.trace.SignAt x j row ∧ row.val = x ∧ row.h = (W.state B).h ∧ row.T = B.root ∧
      row.timeout = false ∧ row.WellFormed ∧ (W.state P).validAtt row ∧
      Q.trace.time j ≤ Q.params.ts e + 6 * Q.params.Δ ∧
      Q.params.ts e + 7 * Q.params.Δ ≤ Q.deadline ∧
      ((x ∈ (W.state P).target ∧
          ((W.state B).bound → x ∈ (W.state P).fin (W.state B).hj ∨
            (W.state B).hj ≤ (W.state P).hF)) ∨
        (row ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.atts ∧
          ∃ k, Q.trace.ProcessAttAt (W.block a).proposer k row ∧ k < W.cut a ∧
            Q.trace.time k < Q.params.ts e + 7 * Q.params.Δ)) ∧
      ((W.state B).bound →
        row.fin = some ((W.state B).hj, (W.state B).J) ∧
        (((W.state B).hj, (W.state B).J) ∈ (W.state P).pending ∨
          (W.state B).hj ≤ (W.state P).hF))

/-- OPEN stable-entry normalization, prior-report/dedup and mandatory pool validity supplier.
No-timeout is local and must be discharged by the bounded-crossing argument. -/
def RowSupply : Prop :=
  ∀ B e, W.Protected B e → ∀ a : Fin 4,
    (e + 2 = (W.block a).slot ∨ (B = W.block 0 ∧ a = 1)) →
    ∀ P, (W.block a).parent = some P.root → W.Extends B P →
      (∀ D, W.Extends B D → W.Extends D P →
        (W.state D).h = (W.state B).h ∨ W.JustifiedBy B D.slot) →
      W.JustifiedBy B P.slot ∨ W.TargetRows B P e a

open Classical in
/-- Justification creates the actual bound successor. The birth-s branch permits w=1;
only the strictly post-A0 crossing has w≥2. Earlier successor justification finalizes B. -/
def BoundedCrossings : Prop :=
  ∃ B C, W.Selected B ∧ W.JustifiedBy B (W.start + (S.δt + 1)) ∧
    W.Entry C ∧ W.Extends B C ∧ (W.state C).J = B.root ∧ (W.state C).bound ∧
    W.start + (if B = W.block 0 then 1 else 2) ≤ C.slot ∧
    C.slot ≤ W.start + (S.δt + 1) ∧
    (let v := if C.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt + 1)
      else W.start + (S.δt + 3)
     ∀ D, W.OnChain D → W.Extends C D → D.slot < v →
       (W.state D).h = (W.state C).h ∨ (W.state B).h ≤ (W.state D).hF) ∧
    ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧ W.Extends B F

/-- Actual cache acceptance and persistence at the original endpoint, not mere delivery. -/
def CacheCoverage : Prop :=
  ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
    W.Extends (W.block 0) (Q.trace.state y j).fg.F

end FinalWindowData

/-- OPEN extraction and endpoint budget; four-anchor-window.md / fixed-timeout-synthesis.md
at workbench b3ca078. Synthesizing accepted_latency must leave enough time for actual carrier
processing by the exact engine-scaled endpoint. No numeric output delay is invented. -/
theorem final_window_extract (Q : FinalQuery S A V) : Nonempty (FinalWindowData S A V Q) := by
  sorry

/-- OPEN inherited progress, with no lower bound on inherited birth. Paper: workbench b3ca078,
four-anchor-window.md and fixed-timeout-synthesis.md, inherited-entry bootstrap. -/
theorem final_inherited_progress (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.InheritedProgress := by
  sorry

/-- OPEN first crossing, justification OR timeout; exposure d−2 applies only to the first
post-A0 descendant. Paper: workbench b3ca078, four-anchor-window.md / fixed-timeout-synthesis.md. -/
theorem final_first_crossing (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (progress : W.InheritedProgress) : W.FirstCrossing := by
  sorry

/-- OPEN exact-entry rows, including coherent prior reports and dedup; paper workbench b3ca078,
four-anchor-window.md / fixed-timeout-synthesis.md. Only designated protected entries qualify.
Deriving normalization and prior-report history from Healthy and the finite canonical simulation
remains OPEN; these conclusions are not assumed in the window context. -/
theorem final_row_supply (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.RowSupply := by
  sorry

/-- OPEN bounded crossing assembly; paper workbench b3ca078, four-anchor-window.md /
fixed-timeout-synthesis.md. Consumes the earlier suppliers; handles birth-s separately. -/
theorem final_bounded_crossings (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (crossing : W.FirstCrossing) (rows : W.RowSupply) : W.BoundedCrossings := by
  sorry

/-- OPEN acceptance, not receipt. Paper workbench b3ca078, four-anchor-window.md /
fixed-timeout-synthesis.md. The latency budget and cache timing are jointly OPEN. -/
theorem final_cache_acceptance (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  sorry

/-- OPEN payload/read projection of the finite supplier package, without old FinalPremises
or UPat. Paper workbench b3ca078, four-anchor-window.md / fixed-timeout-synthesis.md. -/
theorem final_payload_projection
    (windows : ∀ Q : FinalQuery S A V, Nonempty (FinalWindowData S A V Q))
    (coverage : ∀ (Q : FinalQuery S A V) (W : FinalWindowData S A V Q), W.CacheCoverage) :
    ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  sorry

/-- Statement-only assembly of the OPEN four-anchor suppliers; not a completed liveness proof.
Paper: workbench b3ca078, four-anchor-window.md and fixed-timeout-synthesis.md. -/
theorem accepted_healthyLive_final : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  apply final_payload_projection S A V (final_window_extract S A V)
  intro Q W
  have crossings := final_bounded_crossings S A V Q W
      (final_first_crossing S A V Q W (final_inherited_progress S A V Q W))
      (final_row_supply S A V Q W)
  obtain ⟨B, C, hB, _, _, _, _, _, _, _, _, F, hF, hBF⟩ := crossings
  exact final_cache_acceptance S A V Q W ⟨F, hF, hB.2.1.trans hBF⟩

/-- R3 available/stable inclusion; R4 FinalInclude for final.
NO PAPER PROOF for exact contract gHeal, bounded recurrence→node progress,
or repaired engine timing transport. See generic-r3-bridge-audit.md.
This field must not acquire whole-run progress before ready as a premise. -/
theorem accepted_healthyLive : ∀ cap g, schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
          ((Sys (family S) V).ready (K S A) gst r)
          ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  intro cap
  cases cap with
  | final => exact accepted_healthyLive_final S A V
  | available => sorry
  | stable => sorry

/-- R1, sleepy-record-invariant.md §§2–5.1 and sleepy-proposal-adoption.md
§§2–4 (conditional S1–S4 package). NO PAPER PROOF for engine network,
readiness and read-cut transport. Node route: sleepy_invariant and ready reads. -/
theorem accepted_sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → (Sys (family S) V).Holds
      ((Sys (family S) V).Sleepy (K S A)) fun r =>
        (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r) g 0 := by
  sorry

/-- R2 inclusion/growth, node sleepy_statements. NO PAPER PROOF yet pinned
for the exact recurrence/readiness/deadline transport; keep this gap explicit. -/
theorem accepted_sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ i : (K S A).Idx,
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Sleepy (K S A) r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            0 ((Sys (family S) V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
          g 0 ((K S A).params.latency cap i) := by
  sorry

/-- R3 healed safety. NO PAPER PROOF for bounded [ready,heal] recurrence
to current whole-run HealedPremises or the target gHeal bound. RecRet also
has no completed proof (rc-recret-induction.md §6). -/
theorem accepted_healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ (i : (K S A).Idx) (gst : Time),
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            ((Sys (family S) V).ready (K S A) gst r)
            ((Sys (family S) V).heal (K S A) cap i gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r)
          g ((Sys (family S) V).heal (K S A) cap i gst r) := by
  sorry

/-- R5 OC1–OC4: NO PAPER PROOF for composed-node outage continuation.
Blocked by lifetime (4k−1 versus 4k−2) and finite pre-outage network scope:
SyncUntil b₀ does not give unrestricted late-wake SyncRun calls. Do not
insert that false implication as an intermediate lemma. -/
theorem accepted_persists : ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys (family S) V).Holds ((Sys (family S) V).Outage (K S A) T b₀ b₁)
      fun r => (chainTrace r.2).ProtectedThrough
        ((Sys (family S) V).cDur (K S A) r) g (resilienceTarget schema g) T b₀ b₁ := by
  sorry

/-- Exact nine-field assembly; the named gaps above are not a blanket claims assumption. -/
theorem accepted_claims : ShapeClaims (family S) (K S A) := by
  intro V _ _
  exact {
    outputValid := accepted_outputValid S V
    nested := accepted_nested S V
    finalMonotone := accepted_finalMonotone S V
    finalAccountable := accepted_finalAccountable S A V
    healthyLive := accepted_healthyLive S A V
    sleepySafe := accepted_sleepySafe S A V
    sleepyLive := accepted_sleepyLive S A V
    healedSafe := accepted_healedSafe S A V
    persists := accepted_persists S A V }

/-- Selection-aware singleton duties make every recurrence fit. -/
theorem accepted_progressFits : ProgressFits (K S A) (family S) := by
  intro cap i pub s
  rfl

/-- At an outer gap beyond the local span there is room for a bad slot. -/
theorem accepted_progressTolerant : ProgressTolerant schema (K S A) := by
  intro cap _ N
  let P := if cap = .final then finalWindow S else Pattern.single
  exact ⟨⟨P.span + 2, by omega⟩, Nat.le_refl _⟩

/-- Fixed thresholds and positive finite catch-up/budget are admissible. -/
theorem accepted_admissible : (K S A).params.Admissible := by
  rw [acceptanceContract_params_eq]
  exact {
    catchUp_pos := (accepted_coefficients S A).catchUp.pos
    θ_range := by norm_num [Params.standard]
    β_range := by norm_num [Params.standard]
    cover_range := by norm_num [Params.standard]
    α_range := by norm_num [Params.standard]
    budget_pos := by have := A.lookback.pos; have := S.two_le_k; dsimp [Params.standard]; omega }

/-- Concrete existential endpoint. Every gap is a named numeric or adapter
leaf; no simulation, GenesisFresh, or desired safety premise is added. -/
theorem accepted : ∃ C : AcceptanceCoefficients,
    Accepted (family S) (acceptanceContract A C) := by
  refine ⟨accepted_coefficients S A, ?_⟩
  exact {
    claims := accepted_claims S A
    admissible := accepted_admissible S A
    serves := by simp [OutputSchema.Serves, schema]
    progressFits := accepted_progressFits S A
    progressTolerant := accepted_progressTolerant S A }

end Consensus.Goldilocks.Refinement
