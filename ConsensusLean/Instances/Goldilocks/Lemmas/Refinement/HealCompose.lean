module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.RiseGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetOfDrain

public section

/-! # Goldilocks Refinement: M1′ composition up to the reset, conditional on the drain (#136)

consensus-lean#136, workbench `heal_bound.md` §1 steps 1–7, `healing_parallel_plan.md` P7.
`reset_of_drain` is the `FinalQuery` instance of the generic kernel `exists_reset_of_drain`
(`ResetOfDrain`): the ready scalar is `max ready 0`, the gap is `G = X` (`hgp_of_query`, duty →
proposal in the leaf form (H2)), whose horizon `t_{N+6} ≤ horizon` follows from the kernel's frame
end `t_N + 2Δ < B` and `hhor`.

The only open input is the drain, `DrainOutputs` at the service horizon `b` (P5). `Δ_F` stays a
parameter (`6Δ + Δ_F ≤ 4Δ·δ_t`). The bound is `a ≤ max ready 0 + (24 L_drain + 48ρ + 64)·Δ + 6λ`,
`ρ = δ_t + X − 1`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)
open Healing

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **M1′ up to the reset, conditional on the drain** (heal_bound §1 steps 1–7). With the run
premises of `exists_frameWindow_of_noAdvance` and `FrameWindow.rise_reset` (service up to `b`,
awake on `[ḡ, b]`, catch-up `2Δ`, no restart after `ḡ`, the calls `hcallZ`/`hcall` with lag `λ`),
the duty → proposal premise (H2), and the drain (`DrainOutputs`, P5): a reset at a time
`a ≤ max ready 0 + (24 L_drain + 48ρ + 64)·Δ + 6λ`, `ρ = δ_t + X − 1`, `X = Q.index`. -/
theorem reset_of_drain (Q : FinalQuery S A V)
    {dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)}
    (hrun : GoldilocksRun (runProposer S Q.run.2 Q.hn) dg (honestKeys S Q.run.2) Q.trace)
    (hnc : Compose.NoCollRun dg Q.trace)
    (hf : 3 * (honestKeys S Q.run.2)ᶜ.ncard ≤ Q.params.n - 1)
    {g ΔF b lam : Time} {Ld : Nat}
    (hsvc : ResetService Q.trace (honestKeys S Q.run.2) g ΔF b)
    (hawake : ∀ y ∈ honestKeys S Q.run.2, ∀ t, gbar g ≤ t → t ≤ b → Q.trace.awake y t)
    (hcatch : CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ))
    (hnr : NoRestartAfter Q.trace (honestKeys S Q.run.2) (gbar g))
    (hH : (honestKeys S Q.run.2).Nonempty)
    (hsnap : ∃ j, FirstCutAfter Q.trace j (cutZ Q.params.toParams g))
    (hδ : 3 ≤ Q.params.toParams.fg.δt)
    (hΔF : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (Q.params.toParams.fg.δt : Time))
    (hlam : 0 ≤ lam)
    (hgr : gbar g ≤ max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
    (hcallZ : ∀ z ∈ honestKeys S Q.run.2, ∀ m,
      max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤ Q.trace.time m →
      Q.trace.time m ≤ b → ∃ j < m, Q.trace.IsCall z j ∧
        Q.trace.deadline z j (max (cutZ Q.params.toParams g) g) Q.params.Δ ≤ Q.trace.time j)
    (hcall : ∀ z ∈ honestKeys S Q.run.2, ∀ i m,
      max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤ Q.trace.time i →
      Q.trace.time i + lam ≤ Q.trace.time m → Q.trace.time m ≤ b → ∃ j < m,
        Q.trace.IsCall z j ∧
          Q.trace.deadline z j (max (Q.trace.time i) g) Q.params.Δ ≤ Q.trace.time j)
    (hb : resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
      Q.params.toParams.fg.δt (Q.index : Nat) Ld ≤ b)
    (hhor : resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
      Q.params.toParams.fg.δt (Q.index : Nat) Ld + 24 * Q.params.Δ ≤ Q.run.2.horizon)
    (hpropose : ∀ s, HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (family S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) (honestKeys S Q.run.2) g
      (Q.index : Nat) Ld b) :
    ∃ a, IsReset Q.trace (honestKeys S Q.run.2) g a ∧
      a ≤ resetBound (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0) Q.params.Δ lam
        Q.params.toParams.fg.δt (Q.index : Nat) Ld := by
  refine exists_reset_of_drain hrun hnc hf hsvc hawake hcatch hnr hH hsnap hδ hΔF hlam
    (le_max_right _ _) hgr Q.index.pos hcallZ hcall hb ?_ hdrain
  intro s₀ N hs hN
  refine hgp_of_query S A V Q hrun hpropose hs ?_
  have : Q.params.ts (N + 6 : Nat) = Q.params.ts N + 24 * Q.params.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hD : 0 < Q.params.Δ := Q.params.toParams.hΔ
  rw [this]; linarith

end Consensus.Goldilocks.Refinement
