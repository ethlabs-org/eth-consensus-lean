module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

/-! Plan O-ARM §4 fields 7 and 8 (duty clauses), §6.2 steps 6–7. The only
honest duties in [d(l), d(l + 1)) are the label-`(l + 2)` proposal at
t(l + 2) and the label-`(l + 2)` HEAD at v(l + 2). Both read the complete
honest label-`(l + 1)` batch, which extends `D`. The batch gives a strict
majority to every prefix of `D` and dominates every conflicting block, so the
suffix walk passes `D`. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; a gate time is never a vote time. -/
theorem arming_gate_ne_vote (p : Params) (r s : Slot) :
    SA.gateTime p.toParams r ≠ SA.voteTime p.toParams s := by
  rw [arming_gate_eq, arming_vote_eq]
  intro h
  have hd := p.deltaPos
  have e : ((4 * r + 5 : Nat) : Time) * p.Δ = ((4 * s : Nat) : Time) * p.Δ := by
    push_cast
    linarith
  have := Int.natCast_inj.mp (mul_right_cancel₀ (ne_of_gt hd) e)
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; a gate time is never a
proposal time. -/
theorem arming_gate_ne_proposal (p : Params) (r s : Slot) :
    SA.gateTime p.toParams r ≠ SA.proposalTime p.toParams s := by
  rw [arming_gate_eq, arming_proposal_eq]
  intro h
  have hd := p.deltaPos
  have e : ((4 * r + 6 : Nat) : Time) * p.Δ = ((4 * s : Nat) : Time) * p.Δ := by
    push_cast
    linarith
  have := Int.natCast_inj.mp (mul_right_cancel₀ (ne_of_gt hd) e)
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 4. Class (iii). DC: INTENTIONAL; without restarts an
ancestor of F stays an ancestor of F. -/
theorem arming_F_mono {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hN : V2.D.NoRestart rho) {j i : Nat} (hji : j ≤ i) (x : V) :
    Block.Preceq (F_at p c E rho j x) (F_at p c E rho i x) := by
  apply eraseFG_preceq
  have h := fgsa_monoAlong_preceq_F p c (storeAt p c E rho j x).fg.F
  rw [Gen.V2.Duty.MonoAlong_def] at h
  exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho hji x
    (hN.restartFree x j i) (KitFG.preceq_refl _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 4. Class (iii). DC: INTENTIONAL; an ancestor of a
stored block has a stored FG lift. -/
theorem arming_lift_mem {st : State p.n} (h : CStoreInv p st) {b a : Block}
    (hb : b ∈ st.base.blocks) (ha : Block.Preceq a b) :
    ∃ A ∈ st.fg.TF, eraseFG A = a := by
  obtain ⟨B, hB, rfl⟩ := (h.baseTree _).1 hb
  exact eraseFG_ancestor_mem h.fg.closed hB ha

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §4 fields 7–8. Class (iii). DC: INTENTIONAL; an actual honest
emission is awake. -/
theorem arming_emit_awake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {y : V} {o : Obj p} {t : Time} {i : Nat}
    (hi : rho.events[i]? = some (.tick y t)) (hem : o ∈ V2.D.Run.emitsAt E rho i) :
    E.awake y t = true := by
  cases h : E.awake y t with
  | true => rfl
  | false =>
    rw [(V2.D.Run.step_tick_eq E rho hi).2,
      (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho i y) y t h).1] at hem
    exact (List.not_mem_nil hem).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §4 fields 7–8. Class (iii). DC: INTENTIONAL; an actual honest
HEAD emission is the HEAD duty of its label at its vote time. -/
theorem arming_emit_head {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (_hE : V2.D.ExecutionValid E rho) {y : V} (_hy : y ∈ rho.honest) {o : Obj p} {t : Time}
    (_he : V2.D.Run.emits E rho y o t) {H : Block}
    (hH : HeadTargetAtEmission p c E rho y o t H) :
    ∃ s q i, o.auth = .seat (.base (.head s)) q ∧ t = SA.voteTime p.toParams s ∧
      rho.events[i]? = some (.tick y t) ∧
      H = headVote p (FGSA.clock p (rho.stateBefore E i y).st t) s := by
  obtain ⟨i, s, q, hi, hm, ho, hh⟩ := hH
  have ha : o.auth = .seat (.base (.head s)) q := by rw [ho]; rfl
  rw [ho, (V2.D.Run.step_tick_eq E rho hi).2] at hm
  have ht := (fgsa_emits_head E rho _ y t s q H.root).mp hm |>.2.1
  exact ⟨s, q, i, ha, ht.symm, hi, hh⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §4 field 7. Class (iii). DC: INTENTIONAL; an actual honest
proposal emission is the proposal duty of its label; its parent is the
proposer head of the clocked store. -/
theorem arming_emit_proposal {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) {y : V} (hy : y ∈ rho.honest) {o : Obj p} {t : Time}
    (he : V2.D.Run.emits E rho y o t) {N : NamedProposal p.n} (hX : o.payload = .proposal N) :
    ∃ s i, s ≠ 0 ∧ t = SA.proposalTime p.toParams s ∧ rho.events[i]? = some (.tick y t) ∧
      N.parent.erase = proposerHead p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t) s := by
  obtain ⟨i, hi, hem⟩ := he
  have haw := arming_emit_awake hi hem
  have hw := honest_emit_wellFormed E rho hE.toDeliveryWellFormed
    hE.toScheduleWellFormed i y t hi hy haw o hem
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  rcases o with ⟨auth, m⟩
  change m = .proposal N at hX
  subst hX
  cases auth with
  | none => cases hw
  | seat l q =>
    obtain ⟨_, _, d, _, ht, ha⟩ := (V2.D.Engine.mem_tick_seat_iff E rho _ y t l q _).mp hem
    cases d with
    | headAction s =>
      change (if joinedNow p _ then some (Msg.head _) else none) = some _ at ha
      split at ha <;> cases ha
    | fgAction r =>
      change (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t)
        (V2.D.Run.stateBefore E rho i y).record ⟨0, p.nPos⟩).1.map Msg.row = some _ at ha
      obtain ⟨_, _, hm⟩ := Option.map_eq_some_iff.mp ha
      cases hm
    | propAction s =>
      change SA.proposalTime p.toParams s = t at ht
      change (if joinedNow p _ then
        (propose p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t) s).map
          (withApp p (c.app (rho.input y t))) else none) = some _ at ha
      split at ha <;> try (cases ha)
      obtain ⟨m', hm', hw'⟩ := Option.map_eq_some_iff.mp ha
      by_cases hs0 : s = 0
      · subst hs0
        cases hm'
      · rw [propose_head (p := p) _ s hs0] at hm'
        obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm'
        cases Msg.proposal.inj hw'
        exact ⟨s, i, hs0, ht.symm, hi, (namedByErase?_sound _ _ P hP).2⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 2. Class (iii). DC: INTENTIONAL; the target of an
actual honest HEAD is stored by its holder at the vote tick. -/
theorem arming_emit_head_store {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (_hE : V2.D.ExecutionValid E rho) {z : V} (_hz : z ∈ rho.honest) {r : Slot}
    {q : Fin p.n} {K : Block} {t : Time}
    (he : HeadTargetAtEmission p c E rho z (ofHead p ⟨.seat (.head r) q, K.root⟩) t K) :
    ∃ i, rho.events[i]? = some (.tick z t) ∧ K ∈ (storeAt p c E rho i z).base.blocks := by
  obtain ⟨i, s, _, hi, _, _, hK⟩ := he
  refine ⟨i, hi, ?_⟩
  have hm := headVote_stored p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i z) t) s
  rw [clock_base_blocks, ← hK] at hm
  exact hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §6.2 steps 2 and 6. Class (iii). DC: INTENTIONAL; a non-genesis
block below `D` is in the store of an honest reader at a later tick, with a
stamp before e(l + 1). The holder of a batch HEAD stores it, and the healthy
label window delivers it before e(l + 1). -/
theorem arming_ancestor_stamp {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    {l : Slot} {D : Block}
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1)))
    {y : V} {k : Nat} (hk : rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))))
    {z : V} (hz : z ∈ rho.honest) {q : Fin p.n} {K : Block}
    (hem : HeadTargetAtEmission p c E rho z (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
      (SA.voteTime p.toParams (l + 1)) K)
    (hDK : Block.Preceq D K) {ih : Nat} (hkih : k ≤ ih)
    (o : GridCO.Wire p.n .root) (ho : o ∈ (storeAt p c E rho k y).base.votes)
    (X : Block) (hne : X ≠ .genesis) (hXD : Block.Preceq X D)
    (hF : Block.Preceq (F_at p c E rho k y) X)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    X ∈ (storeAt p c E rho ih y).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho ih y).base X < SA.earlyTime p.toParams (l + 1) := by
  obtain ⟨i, hi, hKi⟩ := arming_emit_head_store hE hz hem
  obtain ⟨A, hA, hAe⟩ := arming_lift_mem (cstoreInv_stateBefore E rho i z) hKi
    (block_preceq_trans hXD hDK)
  have hXi : X ∈ (storeAt p c E rho i z).base.blocks :=
    ((cstoreInv_stateBefore E rho i z).baseTree _).2 ⟨A, hA, hAe⟩
  obtain ⟨hXk, hst⟩ := arming_block_early (hroots := hroots)
    hE hN hDelta (l + 1) hSync hk hz hi X hne hXi hF
  obtain ⟨_, hXih, _, hstamp⟩ := inclusion_stamps_kept E rho hN hkih y o X ho hXk
  exact ⟨hXih, hstamp ▸ hst⟩

end AvailableChain.FGSA.Run
end
