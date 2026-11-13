module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainRows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.FrameWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetRounds

public section

/-! # The growing drain kernel's steps

The frame window, the warm proposals, the owed rows and the reset bound, each forwarded to its
proof (`exists_frameWindow_seq_of_service_proof_at` in `Kernel/FrameWindow`, and the
`KernelProof` forms in `Kernel/DrainWarm`, `Kernel/DrainRows` and `Kernel/ResetRounds`), and the
finite reset record they give. The finite reset lower bound is proved in `Kernel/ResetSource`.
No deadline is lengthened here.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Step 2: per-cut range and relay service produce a frame window for the warm/rise steps. -/
theorem exists_frameWindow_seq_of_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J := by
  exact exists_frameWindow_seq_of_service_proof_at hrun hnc hf hsvc hcatch len hlen hlam hlo
    hTb hrange hcall hT

/-- Step 3: service gives warm proposals without any reset lower-bound premise. -/
theorem drainOutputs_of_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {G Ld : Nat} (hLd : 2 * sp.k + G ≤ Ld + 1) :
    DrainOutputs tr proposer H g G Ld b := by
  exact KernelProof.drainOutputs_of_service_at hrun hnc hsvc hawake hf hcatch hLd

/-- Step 3: an honestly signed row remains owed after its signer is compromised. -/
theorem rows_delivered_service_at {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hv : gbar g ≤ v) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) : ∃ k' < kX, tr.ProcessAttAt p k' att := by
  exact KernelProof.rows_delivered_service_at hsvc hnr hrun hv hp hX hvx hkb hy hsig hk

/-- Step 4: the reset bound from finite service, a bounded-gap proposer stream and drain, reading
restarts only up to the service bound. This asserts existence and an upper bound; the strict lower
bound is a separate interface. -/
theorem exists_reset_of_drain_rounds_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b) (hstock : sp.committeeSize = sp.n) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld := by
  exact KernelProof.exists_reset_of_drain_rounds_awake_at hrun hnc hf hsvc hawake hcatch hnr
    hH hδ hΔF hr hgr hG hcz hb hgp hdrain hstock

/-- Step 4 packaging: a bounded reset and a snapshot supply the existing finite reset record. -/
theorem resetPremisesUpTo_of_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF a b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hreset : IsReset tr H g a) (hab : a ≤ b)
    (hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ResetPremisesUpTo tr H proposer dg g ΔF a b := by
  exact ⟨hrun, hnc, hsvc, hawake, hf, hreset, hab, hsnapshot, hstock⟩

end Consensus.Goldilocks.Healing.Growing

end
