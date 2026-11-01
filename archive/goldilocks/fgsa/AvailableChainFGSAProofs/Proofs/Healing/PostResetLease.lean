module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant -- shake: keep (J4 carrier)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J4 carrier)
public import AvailableChainFGSAProofs.Proofs.Healing.ResetTransfer
public import AvailableChainFGSAProofs.Proofs.Healing.SupportWrite -- shake: keep (gateWriteKeys)

public section

/-! Blueprint 21 H.15:2885–2923, H.17/H.18:2946–3060; plan J4;
B1/B13/B17/B18. Both RFProv clauses over H0Reset at every event cut.
DC: SAME target-source provenance; INTENTIONAL active window views.
Assembly supplies origin (sourceDiscipline_qcOrigin), heldRows
(held_chain_row_origin_before), cap (fgsa_finalityCap), hhead
(cap_finality_head), and xing (fgsa_rXing). No Foundations import.
The universal-lease successor is blocked at the arbitrary-write first
transfer; the source-only HighSrcN interface does not cover that write. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15:2887–2892, H.16:2931–2938; plan J4 item 0b;
B13/B17/B18. DC: SAME last-write key guards. The named producer of
`writes` is fgsa_leaseOrigins_lastWrite. Unfold its actual gateWriteKeys
membership to obtain every lease_safe write guard. The two `pre` terms
are identical; neither a slot bridge nor a store bridge is needed. -/
theorem postReset_leaseSafe_antecedent_of_lastWrite
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {w : HealingWitness} {i : Nat} {x : V} {row : Block × Nat × Time}
    (hrow : row ∈ (storeAt p c E rho i x).base.obligations) (hx : x ∈ rho.honest)
    (hCB : Block.Preceq w.CStar row.1) (hne : row.1 ≠ w.CStar) :
    ∃ j < i, ∃ s C, x ∈ rho.honest ∧ IsGateTick p c rho j x s ∧
      gatePassedAt p c E rho j ∧ gateResultAt p c E rho j = some (some C) ∧
      Block.Preceq w.CStar row.1 ∧ row.1 ≠ w.CStar ∧
      let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
      row.1 ∈ (actView pre).blocks ∧ row.1 ≠ .genesis ∧ Block.Preceq row.1 C ∧
      row.2.1 ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root
          (actView pre) s row.1 := by
  obtain ⟨j, hj, s, C, ht, hp, hc, _hBC, hkey, _hd, _hq, _hlast⟩ := writes i x row hrow
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy .root p.toParams.engine p.n] at hkey
  obtain ⟨B, hB, hg⟩ := List.mem_flatMap.mp hkey
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hg
  obtain ⟨heB, heg⟩ := Prod.mk.inj he
  subst B
  subst g
  obtain ⟨hmem, hfilter⟩ := List.mem_filter.mp hB
  have hguards := Bool.and_eq_true_iff.mp hfilter
  have hgen : row.1 ≠ .genesis := by simpa only [bne_iff_ne] using hguards.1
  have hBC : Block.Preceq row.1 C := hguards.2
  exact ⟨j, hj, s, C, hx, ht, hp, hc, hCB, hne, hmem, hgen, hBC, hg⟩

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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2982–2987, H.18:3073–3095; plan J4 B;
B1/B13/B17/B18. DC: SAME two provenance arms. Clause 1 uses J1's
reset-only low arm. Clause 2 uses the selected J carrier's target QC
and its actual delivery clock, without any future invariant field. -/
theorem postReset_fProv_all (i : Nat)
    (hroots : NamedRootCollisionFree p c E rho) : PostResetFProv p c E rho w i := by
  rw [PostResetFProv_def]
  intro j _hj x hx hi
  constructor
  · by_cases hgen : (storeAt p c E rho j x).fg.F = .genesis
    · left
      change Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) w.CStar
      rw [hgen]
      exact Gen.Pure.block_genesis_preceq w.CStar
    obtain ⟨D, hD, hDF, K, s, hsrc, hh, hT, htime⟩ :=
      healing_finality_source_clock_on (hroots := hroots) p c E rho hv origin heldRows cap hhead
        hx hgen
    by_cases hlow : (finalityView p D).h_F ≤ w.M
    · exact Or.inl (healing_low_finality_after_reset_on E rho hv.toScheduleWellFormed
        xing w h0r hx hi hD hDF hlow)
    · right
      have hhigh : high p w K := by
        rw [high_def, hh]
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hlow)
      refine ⟨K, s, hsrc, hhigh, htime, ?_⟩
      change Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) (eraseFG K)
      rw [← hT]
      exact eraseFG_preceq ((fgCertificateLaws p).height.entry_preceq K)
  · intro hhighJ
    obtain ⟨W, _hW, _hWF, hjW, hJW⟩ := (cstoreInv_stateBefore E rho j x).fg.pair.1
    change (storeAt p c E rho j x).fg.h_j = (heightView p W).h_j at hjW
    change (storeAt p c E rho j x).fg.J = (heightView p W).J at hJW
    have hM : 1 ≤ w.M := by
      have hmu := h0r.mu_le
      rw [muOf_def] at hmu
      exact (le_max_left _ _).trans hmu
    have hnz : (storeAt p c E rho j x).fg.h_j ≠ 0 := by
      intro hz
      have hJzero : (storeAt p c E rho j x).fg.J = .genesis := by
        rw [hJW]
        exact (fgJustificationLaws p).J_zero W (hjW.symm.trans hz)
      have hinit := (fgStoreSafety p).initial_good.hmax
      change 1 = ({.genesis} : Finset (FGBlock (Fin p.n))).sup
        (fun B => (heightView p B).h) ⊔ 1 at hinit
      rw [Finset.sup_singleton] at hinit
      rw [high_def, hJzero] at hhighJ
      have hg : (heightView p (.genesis : FGBlock (Fin p.n))).h ≤ 1 :=
        (le_sup_left : (heightView p (.genesis : FGBlock (Fin p.n))).h ≤ _).trans_eq hinit.symm
      exact (Nat.not_succ_le_self w.M) (hhighJ.trans (hg.trans hM))
    have hJh : (heightView p (storeAt p c E rho j x).fg.J).h =
        (storeAt p c E rho j x).fg.h_j := by
      rw [hJW, hjW]
      exact (fgJustificationLaws p).J_height W (by rwa [← hjW])
    obtain ⟨K, s, hsrc, hh, hT, htime⟩ :=
      healing_justified_source_clock_on (hroots := hroots) p c E rho hv origin heldRows hx hnz
    have hhigh : high p w K := by
      rw [high_def] at hhighJ ⊢
      rwa [hh, ← hJh]
    refine ⟨K, s, hsrc, hhigh, htime, ?_⟩
    change Block.Preceq (eraseFG (storeAt p c E rho j x).fg.J) (eraseFG K)
    rw [← hT]
    exact eraseFG_preceq ((fgCertificateLaws p).height.entry_preceq K)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17/H.18:2946–3095; plan J4 C; B1/B13/B17/B18.
DC: SAME RFProv body. Apply B at i + 1 to remove only its prefix guard.
J9 supplies the frozen public H0 adapter; this theorem uses H0Reset. -/
theorem postReset_rFProv_reset
    (hroots : NamedRootCollisionFree p c E rho) : ∀ i x,
    x ∈ rho.honest → afterTicksIdx rho (p.actionTime w.rStar) ≤ i →
    let t := (storeAt p c E rho i x).base.now
    (Block.Preceq (F_at p c E rho i x) w.CStar ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
        SA.gateTime p.toParams s + P p ≤ t ∧
        Block.Preceq (F_at p c E rho i x) (eraseFG K)) ∧
    (high p w (storeAt p c E rho i x).fg.J →
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
        SA.gateTime p.toParams s ≤ t ∧
        Block.Preceq (J_at p c E rho i x) (eraseFG K)) := by
  intro i x hx hi
  have h := postReset_fProv_all (hroots := hroots) p c E rho hv origin heldRows cap hhead xing
    h0r (i + 1)
  rw [PostResetFProv_def] at h
  exact h i (Nat.lt_succ_self i) x hx hi

end Provenance
end AvailableChain.FGSA.Run
end
