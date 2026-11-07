module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport

public section

/-! # Pending interface of the growing query suppliers

Statements the confirmed and sleepy query suppliers consume whose home modules are not on this
branch yet, under their agreed names:

* `Regimes.Growing.ready_proposer_proposes_at`, home `Lemmas/Growing/Sleepy/Service/Inclusion`;
* `ready_transport_at`, `sleepy_bounds_at` (`Lemmas/Growing/Sleepy/Engine/Transport`),
  `ready_proposal_at`, `confirmed_inBy_at` (`Engine/Reads`), `sleepy_include_finite_at`
  (`Engine/Inclusion`);
* `healthy_confirmed_supply_at`, home `Lemmas/Growing/Obligations/Healthy`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A proposer ready at its slot start proposes then**, under growing faults. -/
theorem ready_proposer_proposes_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s : Nat} (hs : 0 < s)
    (hready : ReadyAt tr H (catchUp sp) (proposer s) (sp.ts s)) :
    ∃ k P, tr.ProposesAt (proposer s) k P ∧ tr.time k = sp.ts s := by
  sorry

end Consensus.Goldilocks.Regimes.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- An engine node ready at `t ∈ [0, horizon]` is ready at `t` in the canonical growing trace. -/
theorem ready_transport_at (hv : rho.ExecutionValid) {c : Time} {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c (rho.ownKey v) t := by
  sorry

/-- The two sleepy count shapes under growing faults through `b ≤ horizon`. -/
theorem sleepy_bounds_at (hv : rho.ExecutionValid) {b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 b) :
    Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b := by
  sorry

/-- An honest proposal of the canonical growing trace by a proposer ready at `τ` is an engine
proposal released at `τ` by a key ready at `τ`. -/
theorem ready_proposal_at (hv : rho.ExecutionValid) {c τ h : Time} (hτh : τ ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho) c τ h P) :
    ∃ k, rho.point.Ready c (rho.key k) τ ∧
      Shape.HonestProposal rho τ k (headerOf (S.params (pubOf E) hn) P) := by
  sorry

/-- Inclusion in every ready read at `t` is engine confirmed output at the end of `t`. -/
theorem confirmed_inBy_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {c : Time} (hc : 0 ≤ c) {τ t h : Time} (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho) c τ h P)
    (hinc : ∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t →
      Regimes.CutAfter (simTraceAt S rho hn) j t →
      Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
        (Regimes.readAfter (simTraceAt S rho hn) y j t)) :
    InBy rho c .confirmed (headerOf (S.params (pubOf E) hn) P) t := by
  sorry

/-- **Finite inclusion under growing faults** through `b`. -/
theorem sleepy_include_finite_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b)
    (hB : Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b)
    {τ t : Time} {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hP : Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) τ (Regimes.Growing.hold (S.params (pubOf E) hn))
      P)
    (hmargin : τ + 6 * (S.params (pubOf E) hn).Δ ≤ t) (htb : t ≤ b)
    {y : Fin (Fintype.card V)} {j : Nat}
    (hy : Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) y t)
    (hj : Regimes.CutAfter (simTraceAt S rho hn) j t) :
    Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
      (Regimes.readAfter (simTraceAt S rho hn) y j t) := by
  sorry

end Engine

section Healthy

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **Healthy selected-proposal service under growing faults**: a confirmed proposal after the
heal point, in the confirmed read of every node ready at the deadline. -/
theorem healthy_confirmed_supply_at (Q : ConfirmedQueryAt S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query) :
    ∃ P : ConfirmedProposalAt Q,
      ∀ y j, Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocksAt Q.keys) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) := by
  sorry

end Healthy

end Consensus.Goldilocks.Obligations.Growing

end
