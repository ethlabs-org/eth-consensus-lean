module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease -- shake: keep (J4 fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.15/H.17; plan J4; B1/B13/B17/B18.
Fixtures are pure/model or conditional package. The lease HEAD consumer
has an explicit lease_safe premise: A is not claimed as a producer. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetLease
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- pure/model: no write is before the empty cut.
example (w : HealingWitness) : PostResetLeaseSafe p c E rho w 0 := by
  rw [PostResetLeaseSafe_def]
  intro k hk
  exact False.elim (Nat.not_lt_zero k hk)

-- conditional package, anti-vacuity: the exact INLINE writes producer
-- supplies a real gate; its bridge feeds lease_safe and consumes S1 HEAD.
example
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    {w : HealingWitness} {i : Nat} {y : V} {row : Block × Nat × Time}
    (hsafe : PostResetLeaseSafe p c E rho w i)
    (hrow : row ∈ (storeAt p c E rho i y).base.obligations) (hy : y ∈ rho.honest)
    (hCB : Block.Preceq w.CStar row.1) (hne : row.1 ≠ w.CStar) :
    ∃ k s C, IsGateTick p c rho k y s ∧ gateResultAt p c E rho k = some (some C) ∧
      ∀ x j H, x ∈ rho.honest → s + 1 ≤ j →
        timeIdx rho (SA.voteTime p.toParams j) ≤ i → headAtLabel p c E rho x j = some H →
        Block.Preceq row.1 H := by
  obtain ⟨k, hk, s, C, hy, ht, hp, hc, hCB, hne, hB, hgen, hBC, hg⟩ :=
    postReset_leaseSafe_antecedent_of_lastWrite p c E rho writes hrow hy hCB hne
  rw [PostResetLeaseSafe_def] at hsafe
  exact ⟨k, s, C, ht, hc,
    (hsafe k hk y s row.1 row.2.1 C hy ht hp hc hCB hne hB hgen hBC hg).2.1⟩

section Provenance
variable (hv : V2.D.ExecutionValid E rho)
    (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    (xing : RXing p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hv origin heldRows cap hhead xing h0r

-- conditional package, anti-vacuity: clause 2 produces an actual high
-- source before the reader, with its clock bound and J below its body.
example {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hh : high p w (storeAt p c E rho i x).fg.J) :
    ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
      SA.gateTime p.toParams s ≤ (storeAt p c E rho i x).base.now ∧
      Block.Preceq (J_at p c E rho i x) (eraseFG K) :=
  (postReset_rFProv_reset (hroots := hroots) p c E rho hv origin heldRows cap hhead xing h0r
      i x hx hi).2 hh

-- conditional package: B supplies both prefix fields without a prior record.
example (i : Nat) : PostResetFProv p c E rho w i :=
  postReset_fProv_all (hroots := hroots) p c E rho hv origin heldRows cap hhead xing h0r i

end Provenance
end AvailableChain.FGSA.Run.Tests.HealingPostResetLease
end
