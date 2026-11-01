module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw -- shake: keep (J5 fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.16:2924–2945, H5:3318–3325; plan J5; B1/B13/B17/B18.
DC: SAME concrete raw-result and reader consumers. Each fixture has a
pure/model or conditional package label; no all-cut producer is assumed proved. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetRaw

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- pure/model: the empty prefix contains no result tick.
example (w : HealingWitness) : PostResetRawTransfer p c E rho w 0 := by
  rw [PostResetRawTransfer_def]
  intro k hk
  exact False.elim (Nat.not_lt_zero k hk)

section Readers
variable {w : HealingWitness} {i k : Nat} {y : V} {j : Slot} {C : Block}
    (hraw : PostResetRawTransfer p c E rho w i) (hki : k < i)
    (hy : y ∈ rho.honest) (hj : w.sStar ≤ j)
    (hk : IsGateTick p c rho k y j)
    (hC : gateResult p c E rho y j = some (some C))

-- conditional package, anti-vacuity: concrete result tick and concrete HEAD read.
example {x : V} {s : Slot} {H : Block} (hx : x ∈ rho.honest)
    (hs : j + 1 ≤ s) (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i)
    (hH : headAtLabel p c E rho x s = some H) : Block.Preceq C H := by
  rw [PostResetRawTransfer_def] at hraw
  exact (hraw k hki y j C hy hj hk hC).2.1 x s H hx hs hcut hH

-- conditional package, anti-vacuity: concrete result tick and live release-state lease.
example {x : V} {nd : Node p} {lease : Block × Nat × Time}
    (hx : x ∈ rho.honest)
    (hcut : timeIdx rho (SA.releaseTime p.toParams j) ≤ i)
    (hnd : postClock E rho x (SA.releaseTime p.toParams j) = some nd)
    (hlease : lease ∈ nd.st.base.obligations) (hlive : nd.st.base.now < lease.2.2) :
    Block.Compatible lease.1 C := by
  rw [PostResetRawTransfer_def] at hraw
  exact (hraw k hki y j C hy hj hk hC).1 x nd hx hcut hnd lease hlease hlive

end Readers

-- conditional package: B consumes the all-cut field at a concrete output index.
example {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (raw : ∀ i, PostResetRawTransfer p c E rho w i)
    {y x : V} {j a : Nat} {C : Block} (hy : y ∈ rho.honest)
    (hj : w.sStar ≤ j) (hC : gateResult p c E rho y j = some (some C))
    (hx : confirmedReaderIdx p c E rho x a)
    (hhor : SA.gateTime p.toParams j + 4 * p.Δ ≤ rho.horizon)
    (ha : HealSuffix p c rho (SA.gateTime p.toParams j + 4 * p.Δ) a) :
    Block.Preceq C (S_at p c E rho a x) := by
  have h := postReset_h5RawTransfer_body p c E rho h0r raw
  have hbody : ∀ y j C, y ∈ rho.honest → w.sStar ≤ j →
      gateResult p c E rho y j = some (some C) → _ := h
  exact (hbody y j C hy hj hC).2.2.2 a x hx hhor ha

end AvailableChain.FGSA.Run.Tests.HealingPostResetRaw
end
