module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Shared.Release
public import AvailableChainFGSARun.Proofs.Emission

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.1; O-INDUCT plan §2 counts. Class (iii).
DC: INTENTIONAL; healthy-batch counts give the strict release bound.
FaultQ alone does not give this bound. -/
theorem outage_fault_lt_release (p : Params) {a h : Nat}
    (hah : a < h) (hhn : h ≤ p.n - a) : a < SA.releaseThreshold p.toParams := by
  change a < (p.n + 1) / 2
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
O-INDUCT plan §5 Release. Class (iii). DC: INTENTIONAL;
the release and gate phases are disjoint. -/
theorem outage_gate_ne_release (p : Params) (s r : Slot) :
    SA.gateTime p.toParams s ≠ SA.releaseTime p.toParams r := by
  intro he
  rw [arming_gate_eq, arming_release_eq] at he
  have hz : (4 * (s : Int) + 1 - 4 * (r : Int)) * p.Δ = 0 := by
    linear_combination he
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · exact (ne_of_gt p.deltaPos h).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.3; O-INDUCT plan §5 Release. Class (iii).
DC: INTENTIONAL; every emission of one fixed HEAD label is either the
arming in-flight label or a tick strictly before its release. -/
theorem outage_release_heads (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {j r : Slot} {B : Block}
    (hi : rho.events[i]? = some (.tick x (SA.releaseTime p.toParams r)))
    (hdr : SA.gateTime p.toParams j < SA.releaseTime p.toParams r)
    (hseed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q → HeadTargetAtEmission p c E rho y o t H →
          Block.Preceq B H)
    (hhistory : ∀ k y t o, k < i → y ∈ rho.honest → SA.gateTime p.toParams j ≤ t →
      rho.events[k]? = some (.tick y t) → o ∈ V2.D.Run.emitsAt E rho k →
      ∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) :
    ∀ y ∈ rho.honest, ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ q H, o.auth = .seat (.base (.head r)) q → HeadTargetAtEmission p c E rho y o t H →
        Block.Compatible H B := by
  intro y hy o t hem q H ha hp
  have hpay : o.payload = .head H.root := by
    obtain ⟨_, _, _, _, _, ho, _⟩ := hp
    exact congrArg (fun o : Obj p => o.payload) ho
  have ho : o = (⟨.seat (.base (.head r)) q, .head H.root⟩ : Obj p) := by
    cases o
    cases ha
    cases hpay
    rfl
  obtain ⟨k, hk, hmem⟩ := hem
  have htick := (V2.D.Run.step_tick_eq E rho hk).2
  have hmem' := hmem
  rw [htick, ho] at hmem'
  have ht := (fgsa_emits_head E rho _ y t r q H.root).mp hmem'
  have hvr : SA.voteTime p.toParams r = t := ht.2.1
  have hvq : SA.voteTime p.toParams r < SA.releaseTime p.toParams r := by
    rw [arming_vote_eq, arming_release_eq]
    have := p.deltaPos
    linarith
  have hBH : Block.Preceq B H := by
    rcases le_or_gt (SA.voteTime p.toParams r) (SA.gateTime p.toParams j) with hvd | hdv
    · have hr : r = j + 1 := arming_inflight p j r hvd hdr
      subst hr
      exact hseed y o t q H hy ⟨k, hk, hmem⟩ ha hp
    · have hki : k < i := by
        have hkl : k < V2.D.Run.idxBefore rho (SA.releaseTime p.toParams r) :=
          (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr (hvr ▸ hvq)
        have hil : V2.D.Run.idxBefore rho (SA.releaseTime p.toParams r) ≤ i := by
          by_contra hn
          have hit := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (Nat.lt_of_not_ge hn)
          exact lt_irrefl _ hit
        exact hkl.trans_le hil
      exact hhistory k y t o hki hy (hvr ▸ hdv.le) hk hmem H hp
  exact block_compatible_of_common (block_preceq_refl H) hBH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.3; O-INDUCT plan §5 Release. Class (iii).
DC: INTENTIONAL; the bounded duty history closes the global fixed-label
premise of fgsa_release_bound. -/
theorem outage_release_bound [Fintype V]
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hroots : NamedRootCollisionFree p c E rho)
    {i : Nat} {x : V} {j r : Slot} {B : Block}
    (hi : rho.events[i]? = some (.tick x (SA.releaseTime p.toParams r)))
    (hdr : SA.gateTime p.toParams j < SA.releaseTime p.toParams r)
    (hseed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q → HeadTargetAtEmission p c E rho y o t H →
          Block.Preceq B H)
    (hhistory : ∀ k y t o, k < i → y ∈ rho.honest → SA.gateTime p.toParams j ≤ t →
      rho.events[k]? = some (.tick y t) → o ∈ V2.D.Run.emitsAt E rho k →
      ∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H)
    (k : Nat) (y : V) :
    GridCO.releaseCount p.toParams.engine (FGSA.actView (storeAt p c E rho k y)) r B ≤
      (Gen.V2.Duty.faulty rho).card :=
  fgsa_release_bound (hroots := hroots) p c E rho hvalid hnr hcstar hdelta k y r B
    (outage_release_heads hvalid.toScheduleWellFormed hi hdr hseed hhistory)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5 expiry. Class (iii).
DC: INTENTIONAL; expiry retains a row strictly before its deadline. -/
theorem outage_expire_row {n : Nat} (st : GridCO.State n .root) {B : Block} {g : Nat}
    {dl t : Time} (hm : (B, g, dl) ∈ st.obligations) (ht : t < dl) :
    (B, g, dl) ∈ (GridCO.expire { st with now := t } t).obligations :=
  List.mem_filter.mpr ⟨hm, decide_eq_true ht⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5 Release. Class (iii).
DC: INTENTIONAL; release retains the row when the exact release input
count is strictly below its level. -/
theorem outage_release_row (p : Params) {n : Nat} (st : GridCO.State n .root) (r : Slot)
    {B : Block} {dl : Time} (hm : (B, SA.releaseThreshold p.toParams, dl) ∈ st.obligations)
    (hc : GridCO.releaseCount p.toParams.engine st r B < SA.releaseThreshold p.toParams) :
    (B, SA.releaseThreshold p.toParams, dl) ∈ (SA.Root.release p.toParams st r).obligations :=
  List.mem_filter.mpr ⟨hm, decide_eq_true hc⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §5 expiry/release. Class (iii).
DC: INTENTIONAL; the pre-gate clock retains a selected row. Release counts
read the same fields before and after the release, so the count premise
uses the post-clock view. Its run producer is outage_release_bound. -/
theorem outage_clockPre_row (p : Params) (st : State p.n) (t : Time)
    {B : Block} {dl : Time}
    (hm : (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations) (ht : t < dl)
    (hcounts : ∀ r, SA.releaseTime p.toParams r = t →
      GridCO.releaseCount p.toParams.engine (FGSA.actView (FGSA.clockPre p st t)) r B <
        SA.releaseThreshold p.toParams) :
    (B, SA.releaseThreshold p.toParams, dl) ∈ (FGSA.clockPre p st t).base.obligations := by
  have hrow := outage_expire_row st.base hm ht
  unfold FGSA.clockPre at hcounts ⊢
  dsimp only at hcounts ⊢
  split_ifs at hcounts ⊢ with hf he hq
  all_goals first
    | exact hrow
    | apply List.mem_filter.mpr
      refine ⟨hrow, decide_eq_true ?_⟩
      have hr : (decide (0 ≤ t - 5 * p.Δ) &&
          t == SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) = true := by
        simp_all only [Bool.and_eq_true, and_true]
      exact hcounts _ (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hr).2).symm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; the selected lease read has a release-level row.
The level follows from the existing CStoreInv field. -/
theorem outage_row_of_lease (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B : Block} {dl : Time} (hlease : FGSA.leaseOf st B = some dl) :
    (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations := by
  obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hlease
  have hm := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hB : row.1 = B := beq_iff_eq.mp hp
  have hg := hinv.leaseKeys.2 row hm
  obtain ⟨b, g, d⟩ := row
  dsimp only at hB hg hdl
  rw [hB, hg, hdl] at hm
  exact hm

end AvailableChain.FGSA.Run
end
