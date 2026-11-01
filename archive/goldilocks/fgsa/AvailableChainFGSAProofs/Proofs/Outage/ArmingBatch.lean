module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingHistory
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt

public section

/-! Plan O-ARM §4 field 6, §6.2 steps 1–2 and 4, §11 obligation 3. The last
healthy label-`(l + 1)` batch. Each honest joined HEAD of label `l + 1` extends
`D` by `htransfer`, and the healthy cut delivers it, with its block and every
stored ancestor, before e(l + 1) = d(l) ≤ b₀. The receiver epoch keeps the
votes, blocks, and stamps through the named read. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; v(r) as a multiple of Δ. -/
theorem arming_vote_nat (p : Params) (r : Slot) :
    ((4 * r + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams r := by
  rw [arming_vote_eq]
  push_cast
  ring

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; e(r) as a multiple of Δ. -/
theorem arming_early_nat (p : Params) (r : Slot) :
    ((4 * r + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams r := by
  rw [arming_early_eq]
  push_cast
  ring

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; t(r) as a multiple of Δ. -/
theorem arming_proposal_nat (p : Params) (r : Slot) :
    ((4 * r : Nat) : Time) * p.Δ = SA.proposalTime p.toParams r := by
  rw [arming_proposal_eq]
  push_cast
  ring

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §2. Class (iii). DC: INTENTIONAL; d(r) as a multiple of Δ. -/
theorem arming_gate_nat (p : Params) (r : Slot) :
    ((4 * r + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams r := by
  rw [arming_gate_eq]
  push_cast
  ring

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.2 step 1. Class (iii). DC: INTENTIONAL; an honest node ticks
at each public multiple of Δ where it is awake, inside the horizon. -/
theorem arming_tick_exists {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ) {y : V} (hy : y ∈ rho.honest)
    (m : Nat) {t : Time} (ht : (m : Time) * p.Δ = t) (hh : t ≤ rho.horizon)
    (hawake : E.awake y t = true) :
    ∃ k : Nat, rho.events[k]? = some (.tick y t) := by
  subst ht
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hΔ y hy m hh hawake
  exact ⟨k, hk⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §6.2 step 2, §11 obligation 3. Class (iii). DC: INTENTIONAL;
the block step of `inclusion_head_receipt_early` for any non-genesis block in
the store of an honest node before its v(r) tick: the healthy label window
delivers it to every honest reader before the e(r) tick. -/
theorem arming_block_early {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (r : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams r) (SA.earlyTime p.toParams r))
    {j : Nat} {x : V} (hj : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams r)))
    {k : Nat} {z : V} (hz : z ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick z (SA.voteTime p.toParams r)))
    (a : Block) (hne : a ≠ .genesis) (ha : a ∈ (storeAt p c E rho k z).base.blocks)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) a)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    a ∈ (storeAt p c E rho j x).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho j x).base a < SA.earlyTime p.toParams r := by
  have hsch := hE.toScheduleWellFormed
  have htimes : SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r :=
    arming_vote_add p r
  rw [Gen.V2.Duty.LabelSyncOn_def] at hSync
  obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, _⟩ := hSync
  have hdeadline : ∀ t, t ≤ SA.voteTime p.toParams r → dl t ≤ SA.earlyTime p.toParams r := by
    intro t ht
    have hb := hbound t
    rw [max_eq_right ht, hDelta, htimes] at hb
    exact hb
  have hm := ha
  change a ∈ (V2.D.Run.stateBefore E rho k z).st.base.blocks at hm
  rw [fgsa_preTick_eq_timeRead E rho hsch hN hk,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.voteTime p.toParams r) hsch] at hm
  rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho
    (SA.voteTime p.toParams r)) z).stampKeys] at hm
  obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  have hmem : a ∈ (storeAt p c E rho j x).base.blocks := by
    rcases fgsa_block_stamp_source E rho hN _ z a stamp hm with hgen |
      ⟨l, hl, t, o, ho, hacc, _⟩
    · exact (hne hgen.1).elim
    · obtain ⟨parent, hdel, _⟩ := hacc.1
      have htv := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hdel _).mp hl
      have hdl := hdeadline t htv.le
      exact fgsa_gateReceipt_block_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD t o a ho
        (Or.inr ⟨z, hz, l, hacc⟩) (hlt t) (hdl.trans hcut)
        (hsch.honest_only _ (List.mem_of_getElem? hj)) hj hdl hF
  refine ⟨hmem, ?_⟩
  apply fgsa_gateReceipt_block_stamp_lt E rho hsch hN hj _ a hmem
  have := p.deltaPos
  rw [arming_early_eq]
  positivity

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.1 step 6. Class (iii). DC: INTENTIONAL; `htransfer` at the
label `l` of `D`: every honest label-`(l + 1)` HEAD extends `D`. -/
theorem arming_head_ge {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hDmem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    {z : V} (hz : z ∈ rho.honest) {k : Nat}
    (hk : rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1)))) :
    Block.Preceq D (headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k z)
      (SA.voteTime p.toParams (l + 1))).st (l + 1)) := by
  obtain ⟨_, u, _, hu, _, hlb, _, hgr⟩ := arming_clean_mem hs le_rfl hDmem
  have hvh := vHead_eq_headAtIdx p c E rho hs hk
  have hread : headAtIdx p c E rho k (l + 1) = headVote p ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k z) (SA.voteTime p.toParams (l + 1))).st (l + 1) := by
    delta headAtIdx
    rw [hk]
  rw [hread] at hvh
  exact htransfer u z l D _ hu hz hlb hgr hvh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.1 step 6. Class (iii). DC: INTENTIONAL; `htransfer` at the
label `l` of `D`: every honest joined label-`(l + 1)` HEAD extends `D`. -/
theorem arming_head_ge_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hDmem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    {z : V} (hz : z ∈ rho.honest)
    (hJoined : joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1))) {k : Nat}
    (hk : rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1)))) :
    Block.Preceq D (headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k z)
      (SA.voteTime p.toParams (l + 1))).st (l + 1)) := by
  obtain ⟨_, u, _, hu, _, hlb, _, hgr⟩ := arming_clean_mem hs le_rfl hDmem
  have hvh := vHead_eq_headAtIdx p c E rho hs hk
  have hread : headAtIdx p c E rho k (l + 1) = headVote p ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k z) (SA.voteTime p.toParams (l + 1))).st (l + 1) := by
    delta headAtIdx
    rw [hk]
  rw [hread] at hvh
  exact htransfer u z l D _ hu hz hJoined hlb hgr hvh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §4 field 6, §6.2 steps 1–2, §11 obligation 3. Class (iii).
DC: INTENTIONAL; the last healthy batch at each awake honest receiver, from joined voters.
The window v(l + 1) < e(l + 1) = d(l) ≤ b₀ is inside the healthy cut. -/
theorem arming_healthy_batch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {b₀ : Time}
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hDmem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    (y : V) (hy : y ∈ rho.honest)
    (hReceiver : E.awake y (SA.earlyTime p.toParams (l + 1)) = true)
    (hEpoch : ∀ k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) →
      V2.D.restartFree rho y (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (l + 1))) k)
    (hServices : ∀ q K,
      rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
        (SA.voteTime p.toParams (l + 1)) K →
      Nonempty (FreshHeadService E rho (l + 1) q K.root
        (SA.earlyTime p.toParams (l + 1)) y) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams (l + 1)) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ q : Fin p.n,
      rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k y).base.votes ∧
        K ∈ (storeAt p c E rho k y).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k y).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
          SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k y).base K < SA.earlyTime p.toParams (l + 1) := by
  intro q hq hJoined
  have hs := hE.toScheduleWellFormed
  have he : SA.earlyTime p.toParams (l + 1) ≤ b₀ := (arming_early_next p l).trans_le hl
  have hv : SA.voteTime p.toParams (l + 1) < SA.earlyTime p.toParams (l + 1) :=
    (arming_vote_lt_early p (l + 1)).1
  obtain ⟨k, hk⟩ := arming_tick_exists hs hDelta hy (4 * (l + 1) + 2)
    (arming_early_nat p (l + 1)) (he.trans hcut.2) hReceiver
  obtain ⟨kk, hkk⟩ := arming_tick_exists hs hDelta hq (4 * (l + 1) + 1)
    (arming_vote_nat p (l + 1)) ((hv.trans_le he).le.trans hcut.2) hJoined.1
  have hDK := arming_head_ge_on hs htransfer hDmem hq hJoined hkk
  let K := headVote p ((fgsa p c).clock
    (V2.D.Run.stateBefore E rho kk (rho.seatOf (.base (.head (l + 1))) q))
      (SA.voteTime p.toParams (l + 1))).st (l + 1)
  have hEmit : ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩ ∈ V2.D.Run.emitsAt E rho kk := by
    rw [(V2.D.Run.step_tick_eq E rho hkk).2]
    exact (fgsa_emits_head E rho _ _ _ (l + 1) q K.root).mpr
      ⟨hJoined.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hkk hJoined, rfl⟩
  have hTarget : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head (l + 1))) q)
      (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) K :=
    ⟨kk, l + 1, q, hkk, hEmit, rfl, rfl⟩
  obtain ⟨⟨hHead⟩, hBlock⟩ := hServices q K hq hTarget
  obtain ⟨hem, hvm, hvs, hKm, hbs, hslot⟩ := inclusion_head_receipt_early_on
    E rho hE (l + 1) hk q hq hJoined hkk K rfl hHead hBlock (hEpoch k hk) hroots
  exact ⟨_, k, hk, hem, hDK, hslot, hvm, hKm, hvs, hbs⟩

/-- Batch construction needs the actual joined HEAD bounds, at any comparison label. -/
theorem arming_healthy_batch_heads {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {b₀ : Time}
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hHeads : ∀ z, z ∈ rho.honest →
      joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
      ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
      Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
        (SA.voteTime p.toParams (l + 1))) (l + 1)))
    (y : V) (hy : y ∈ rho.honest)
    (hReceiver : E.awake y (SA.earlyTime p.toParams (l + 1)) = true)
    (hEpoch : ∀ k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) →
      V2.D.restartFree rho y (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (l + 1))) k)
    (hServices : ∀ q K,
      rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
        (SA.voteTime p.toParams (l + 1)) K →
      Nonempty (FreshHeadService E rho (l + 1) q K.root
        (SA.earlyTime p.toParams (l + 1)) y) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams (l + 1)) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ q : Fin p.n,
      rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k y).base.votes ∧
        K ∈ (storeAt p c E rho k y).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k y).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
          SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k y).base K < SA.earlyTime p.toParams (l + 1) := by
  intro q hq hJoined
  have hs := hE.toScheduleWellFormed
  have he : SA.earlyTime p.toParams (l + 1) ≤ b₀ := (arming_early_next p l).trans_le hl
  have hv : SA.voteTime p.toParams (l + 1) < SA.earlyTime p.toParams (l + 1) :=
    (arming_vote_lt_early p (l + 1)).1
  obtain ⟨k, hk⟩ := arming_tick_exists hs hDelta hy (4 * (l + 1) + 2)
    (arming_early_nat p (l + 1)) (he.trans hcut.2) hReceiver
  obtain ⟨kk, hkk⟩ := arming_tick_exists hs hDelta hq (4 * (l + 1) + 1)
    (arming_vote_nat p (l + 1)) ((hv.trans_le he).le.trans hcut.2) hJoined.1
  have hDK := hHeads _ hq hJoined kk hkk
  let K := headVote p ((fgsa p c).clock
    (V2.D.Run.stateBefore E rho kk (rho.seatOf (.base (.head (l + 1))) q))
      (SA.voteTime p.toParams (l + 1))).st (l + 1)
  have hEmit : ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩ ∈ V2.D.Run.emitsAt E rho kk := by
    rw [(V2.D.Run.step_tick_eq E rho hkk).2]
    exact (fgsa_emits_head E rho _ _ _ (l + 1) q K.root).mpr
      ⟨hJoined.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hkk hJoined, rfl⟩
  have hTarget : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head (l + 1))) q)
      (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) K :=
    ⟨kk, l + 1, q, hkk, hEmit, rfl, rfl⟩
  obtain ⟨⟨hHead⟩, hBlock⟩ := hServices q K hq hTarget
  obtain ⟨hem, hvm, hvs, hKm, hbs, hslot⟩ := inclusion_head_receipt_early_on
    E rho hE (l + 1) hk q hq hJoined hkk K rfl hHead hBlock (hEpoch k hk) hroots
  exact ⟨_, k, hk, hem, hDK, hslot, hvm, hKm, hvs, hbs⟩

end AvailableChain.FGSA.Run
end
