module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6

public section

/-! H-REPAIR gate geometry (plan step 9; blueprint 21 H.6:965–973, 01 §6.6). The five
fields of `ExactServiceGateGeometry` at every honest gate of an exact-HEAD slot inside
the phase. Field (a) uses 01 §6.6: the finalized block at the gate has slot at most s,
from RQCOrigin and the honest row sources. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Exact gate, release and retained carrier services for one repaired label. -/
structure RepairGateScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) : Prop where
  cut : E.t_GST ≤ slotStartZ p ((s : Int) - 1)
  gates : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x s →
    enabledGateAt p c E rho i x s →
    ∀ B, GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
    GateReceiptScope E rho i x s
  first : ∀ i iq x, x ∈ rho.honest → IsGateTick p c rho i x s →
    rho.events[iq]? = some (.tick x (SA.voteTime p.toParams (s + 1))) →
    enabledGateAt p c E rho i x s →
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho i iq x x s
  carriers : ∀ iy y t, SA.voteTime p.toParams s + p.Δ ≤ t →
    t ≤ rho.horizon → HealingCarriersAt E rho s iy y t

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:367–373 (valid parent slots); plan H-REPAIR step 9.
DC: SAME along the stored ancestor path of a stored block, slots do not decrease. -/
theorem repair_stored_slot_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (v : V) :
    ∀ C : Block, C ∈ (rho.stateBefore E i v).st.base.blocks →
      ∀ B, Block.Preceq B C → B.slot ≤ C.slot := by
  have hi := cstoreInv_stateBefore E rho i v
  intro C
  induction C with
  | genesis =>
    intro _ B hB
    have he : B = .genesis := by
      simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using hB
    rw [he]
  | node P t root body ih =>
    intro hm B hB
    have hB' : B = .node P t root body ∨ Block.Preceq B P := by
      simpa only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] using hB
    rcases hB' with he | hBP
    · rw [he]
    · have hPm : P ∈ (rho.stateBefore E i v).st.base.blocks := by
        obtain ⟨X, hX, heX⟩ := (hi.baseTree _).mp hm
        have hPX : Block.Preceq P (eraseFG X) := by
          rw [heX]
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))
        obtain ⟨Y, hY, heY⟩ := eraseFG_ancestor_mem hi.fg.closed hX hPX
        exact (hi.baseTree _).mpr ⟨Y, hY, heY⟩
      have hlt := fgsa_headRead_child_slot E rho hE i v 0 P (.node P t root body)
        (by rw [clock_base_blocks]; exact hm) rfl
      exact (ih hPm B hBP).trans hlt.le

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:367–373; plan H-REPAIR step 9. DC: SAME a strict stored ancestor
has a
smaller slot. -/
theorem repair_stored_slot_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (v : V) {B C : Block}
    (hC : C ∈ (rho.stateBefore E i v).st.base.blocks) (hBC : Block.Preceq B C) (hne : B ≠ C) :
    B.slot < C.slot := by
  cases C with
  | genesis =>
    exact absurd (by simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using hBC) hne
  | node P t root body =>
    have hB' : B = .node P t root body ∨ Block.Preceq B P := by
      simpa only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] using hBC
    rcases hB' with he | hBP
    · exact absurd he hne
    · have hi := cstoreInv_stateBefore E rho i v
      have hPm : P ∈ (rho.stateBefore E i v).st.base.blocks := by
        obtain ⟨X, hX, heX⟩ := (hi.baseTree _).mp hC
        have hPX : Block.Preceq P (eraseFG X) := by
          rw [heX]
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl P))
        obtain ⟨Y, hY, heY⟩ := eraseFG_ancestor_mem hi.fg.closed hX hPX
        exact (hi.baseTree _).mpr ⟨Y, hY, heY⟩
      have hlt := fgsa_headRead_child_slot E rho hE i v 0 P (.node P t root body)
        (by rw [clock_base_blocks]; exact hC) rfl
      exact lt_of_le_of_lt (repair_stored_slot_le E rho hE i v P hPm B hBP) hlt

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 §8.4 (actual sources); plan H-REPAIR step 9. DC: SAME the actual FG action
source of an honest node is in its FG tree at the action read. -/
theorem repair_source_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {r : Nat}
    {C : FGBlock (Fin p.n)} (hj : rho.events[j]? = some (.tick x (p.actionTime r)))
    (hC : actionSourceFG p c E rho x r = some (some C)) :
    C ∈ (V2.D.Run.stateBefore E rho j x).st.fg.TF := by
  rw [actionSourceFG_eq_round p c E rho hs hj] at hC
  have hd := Option.some.inj hC
  have hmem := (Finset.mem_filter.mp (pickPair_some_spec _ _ hd).1).1
  have hTF := ((KitFG.mem_filteredFromView _ _ _ _).mp hmem).1
  change C ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r)).fg.TF at hTF
  rwa [clock_fg] at hTF

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 01 §6.6 (finality before an honest proposal gate); plan H-REPAIR step
9 (a).
DC: INTENTIONAL the finalized block of an honest store read at or before d_s has slot at
most s. RQCOrigin gives, for a non-genesis F, a justification QC with an earlier honest
row; its actual source C of round r has rR ≤ s and the row entry gives F ⪯ C. -/
theorem repair_finality_slot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (qc : RQCOrigin p c E rho)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) {ev : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) {s : Slot} (hts : ev.time ≤ SA.gateTime p.toParams s) :
    (eraseFG (storeAt p c E rho i x).fg.F).slot ≤ s := by
  have hs := hE.toScheduleWellFormed
  have hinv := cstoreInv_stateBefore E rho i x
  obtain ⟨K, hK, hKF⟩ := hinv.fg.Fcar
  have hKF' : (finalityView p K).F = (storeAt p c E rho i x).fg.F := hKF
  by_cases hg : (storeAt p c E rho i x).fg.F = .genesis
  · rw [hg]
    exact Nat.zero_le _
  have hne : (finalityView p K).F ≠ .genesis := hKF' ▸ hg
  obtain ⟨C', _, hJ, _, Q, rows, _, hrows, k, hk, y, r, wire, ⟨j, hji, ha⟩, hwire, _, C, G,
    hC, hname, hTC, _⟩ := (qc i x K hx hK).2.2 hne
  have hvote := (hrows k hk).2.2.2
  rw [hvote] at hname
  have hroot : (storeAt p c E rho i x).fg.F.root = (heightView p C).T_h.root := by
    have h := congrArg Prod.snd (Option.some.inj hname)
    rw [← hKF', ← hJ]
    exact h
  have hF : (storeAt p c E rho i x).fg.F = (heightView p C).T_h :=
    rootScope_eq hroots (rootScope_store hx hinv.fg.Fmem)
      (rootScope_entry (rootScope_source ha.1 hC)) hroot
  have hCT := repair_source_mem E rho hs ha.2.1 hC
  have hyinv := cstoreInv_stateBefore E rho j y
  have hCm : eraseFG C ∈ (V2.D.Run.stateBefore E rho j y).st.base.blocks :=
    (hyinv.baseTree _).mpr ⟨C, hCT, rfl⟩
  have hle := repair_stored_slot_le E rho hE j y (eraseFG C) hCm _
    (eraseFG_preceq (hF ▸ hTC))
  have hCslot := healing_source_slot p c E rho ha.1 hC
  have hrs : r * p.R ≤ s := by
    have hj := ha.2.1
    have htime : p.actionTime r ≤ ev.time := by
      by_contra hn
      have hlt := repair_idx_lt E rho hs hi hj (lt_of_not_ge hn)
      omega
    have hd := p.deltaPos
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤ ev.time at htime
    change ev.time ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ at hts
    have h : ((r * p.R : Nat) : Int) ≤ (s : Int) := by nlinarith
    exact_mod_cast h
  have hC' : (eraseFG C).slot ≤ s := by
    rw [eraseFG_slot]
    exact hCslot.trans hrs
  exact hle.trans hC'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:960–963; plan H-REPAIR step 7. DC: SAME an honest proposal of slot s is a
block of slot s. -/
theorem repair_proposal_slot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) s Q) : Q.slot = s := by
  obtain ⟨ip, x, N, heN, _, hip, _, hem⟩ := repair_proposal_emission E rho hp
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hem
  have hpr := (fgsa_emits_proposal E rho _ x _ s _).mp hem
  simpa only [heN] using (fgsa_scoreRun_proposal_pools p _ s _ N hpr.2.2.2.2).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 01 §6.6, 21 H.3:769–775, H.6:965–973; plan H-REPAIR step 9 (a).
DC: INTENTIONAL at an honest gate of an exact-HEAD slot s inside the phase, the gate F is
below the HEAD: the HEAD witness reaches the gate store, so F and the HEAD are comparable
(RXing or common J), and F cannot strictly pass a slot-s block (01 §6.6). -/
theorem repair_gate_finality_le [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvd : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s :=
    (le_add_of_nonneg_right hd.le).trans hvd
  have hhor : SA.voteTime p.toParams s ≤ rho.horizon := (hvg.trans hgate).trans hphase.2.1
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hx s hhor
    (hrec.awake x hx _ (hgst.trans hus) hhor)
  have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hQK := Option.some.inj ((hhead x hx (hrec.toRecovery₂.joinedAt_of_slotStart_le E rho s
      hScope.cut hhor x hx)).symm.trans hhl)
  obtain ⟨W, hW, hQW, _, hFW, _⟩ := healing_support_frame_at
    (hroots := hrec.base.receiptIdealization)
    E rho (fun _ => mono) crossing hE hDelta
    hrec.sync hgst hphase hus (hvd.trans hgate) hx hjz
    x (healing_carriers_cut_at p c E rho hrec hScope.cut
      (hScope.carriers i x _ hvd (hgate.trans hphase.2.1)) hx ht hvd jz x hx hjz)
    (B := Q) (hQK ▸ block_preceq_refl _) hx
    (healing_support_idxBefore_le p c E rho hS ht hvd)
    (healing_support_idxBefore_le p c E rho hS ht (hus.trans hvg))
    (healing_phase_lt_timeIdx p c E rho hS ht hgate).le
  rcases block_preceq_total_of_common (eraseFG_preceq hFW) hQW with hFQ | hQF
  · exact hFQ
  · by_cases heq : Q = eraseFG (storeAt p c E rho i x).fg.F
    · rw [← heq]
      exact block_preceq_refl Q
    · exfalso
      have hinv := cstoreInv_stateBefore E rho i x
      have hFm : eraseFG (storeAt p c E rho i x).fg.F ∈
          (V2.D.Run.stateBefore E rho i x).st.base.blocks :=
        (hinv.baseTree _).mpr ⟨_, hinv.fg.Fmem, rfl⟩
      have hlt := repair_stored_slot_lt E rho hE i x hFm hQF heq
      have hle := repair_finality_slot (hroots := hrec.base.idealization) E rho hE qc hx ht (s :=
        s) le_rfl
      rw [← hQs] at hle
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:965–973 (fields (a), (b)); plan H-REPAIR step 9.
DC: INTENTIONAL the gate receipt geometry of an exact-HEAD slot: every emitted honest HEAD
of label s is the exact HEAD Q, and the gate F is below Q. -/
theorem repair_gate_receipt [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hFQ := repair_gate_finality_le E rho hrec mono crossing qc hgst hphase hus hgate hQs
    hhead hx ht hScope
  have hK (q : Fin p.n) (hq : rho.seatOf (.base (.head s)) q ∈ rho.honest) (K : Block)
      (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K) : K = Q := by
    have h := healing_support_emitted_head E rho hS s q K _ he
    exact Option.some.inj (h.symm.trans (hhead _ hq
      (hrec.toRecovery₂.joinedAt_of_slotStart_le E rho s
      hScope.cut (by
        refine (show SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s by
          change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
          linarith [p.deltaPos]).trans (hgate.trans hphase.2.1)) _ hq)))
  refine ⟨?_, ?_⟩
  · intro q hq _ K he
    rw [hK q hq K he, clockPre_fg]
    exact hFQ
  · intro q hq _ K he
    rw [hK q hq K he]
    exact block_preceq_refl Q

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:965–970 (all h votes early and clean); plan H-REPAIR step 9
(c).
DC: INTENTIONAL the fast count at an honest gate of an exact-HEAD slot: the honest awake
HEAD seats are clean early supporters of Q, and their number reaches the release
threshold under the Recovery fault bound. -/
theorem repair_gate_fast_count [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {s : Slot} (hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgh : SA.gateTime p.toParams s ≤ rho.horizon) {Q : Block}
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q) :
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s Q := by
  classical
  have hE := hrec.base.valid
  have hx : x ∈ rho.honest := hE.honest_only _ (List.mem_of_getElem? ht)
  have hDelta := hrec.base.delta
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon := by
    have hd : 0 < E.Δ := hDelta.symm ▸ p.deltaPos
    linarith
  have hJoined := hrec.toRecovery₂.joinedAt_of_slotStart_le E rho s hScope.cut hvh
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd hgh
  let H : Finset (Fin p.n) := Finset.univ.filter
    (fun q => rho.seatOf (.base (.head s)) q ∈ rho.honest)
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h, hJoined _ h⟩, And.left⟩
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head s)) q) :=
    hrec.base.cstar (.base (.head s)) trivial
  have hImage : H.image (rho.seatOf (.base (.head s))) = rho.honest := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact ((hH q).mp hq).1
    · intro hz
      obtain ⟨q, hq⟩ := hbij.2 z
      have hh : rho.seatOf (.base (.head s)) q ∈ rho.honest :=
        (congrArg (fun a : V => a ∈ rho.honest) hq.symm).mp hz
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr ⟨hh, hJoined _ hh⟩, hq⟩
  have hHcard : H.card = rho.honest.card :=
    (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card hImage)
  obtain ⟨hfast, hbatch⟩ := healing_recovery_joined_counts E rho hrec s hScope.cut hgsts hvh
  rw [healing_recovery_joinedHonest E rho hrec s hScope.cut hgsts hvh, ← hHcard]
    at hfast hbatch
  obtain ⟨_, hcount, _, _⟩ := exactService_gate_raw_of_head_on
    (hroots := hrec.base.receiptIdealization) E rho hE hDelta hrec.base.cstar s Q hhead hSync
    ht hgeom (hScope.gates i x hx ht
      (healing_recovery_gate_enabled E rho hrec hx ht
        (healing_gate_cut_of_batch_cut E s hScope.cut)) Q hgeom) H hH hbatch
  exact hfast.trans hcount

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:965–970 (release at q_s; no gate in (q_s, d_s)); plan H-REPAIR
step 9 (c).
DC: INTENTIONAL every live lease at an honest gate of an exact-HEAD slot s is compatible
with Q. Its last write is a gate w < s before q_s = v_(s+1); the q_s release, counted by
the clean early votes for Q at this gate, removes every target that conflicts with Q.
`writes` is the inline last-write premise (ruling B27). -/
theorem repair_gate_guard [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) Q := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hgh : SA.gateTime p.toParams s ≤ rho.horizon := hgate.trans hphase.2.1
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := hgst.trans hus
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd hgh
  have hgeom := repair_gate_receipt E rho hrec mono crossing qc hgst hphase hus hgate hQs
    hhead hx ht hScope
  have hτ := repair_gate_fast_count E rho hrec hgsts hgh hhead ht hScope hgeom
  have hFQ := repair_gate_finality_le E rho hrec mono crossing qc hgst hphase hus hgate hQs
    hhead hx ht hScope
  have hqd : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hx (s + 1) (hqd.le.trans hgh)
    (hrec.awake x hx _ (by
      refine hgsts.trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith [p.deltaPos]) (hqd.le.trans hgh))
  have hqi : iq < i := repair_idx_lt E rho hS hiq ht hqd
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  intro lease hl
  rw [← hv] at hl
  have hl' : lease ∈ (storeAt p c E rho i x).base.obligations :=
    (clockPre_obligations_sublist p _ _).subset hl
  obtain ⟨j, hji, w, C, htj, _, _, _, _, hdl, _, _⟩ := writes i x lease hl'
  have hws : w < s := by
    have hlt := fgsa_tick_time_strict E rho hS htj ht hji
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hlt
    have h : (w : Int) < s := by nlinarith
    exact_mod_cast h
  have hjq : j < iq := by
    apply repair_idx_lt E rho hS htj hiq
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    have h : (w : Int) + 1 ≤ (s : Int) := by exact_mod_cast hws
    push_cast
    nlinarith
  have hkeep := healing_lease_persist E rho hS htj (Nat.lt_succ_of_lt hjq) hqi lease hdl hl'
  have hpost : storeAt p c E rho (iq + 1) x =
      FGSA.clock p (storeAt p c E rho iq x) (SA.voteTime p.toParams (s + 1)) := by
    change (V2.D.Run.stateBefore E rho (iq + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho hiq]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ x _
  rw [hpost] at hkeep
  have hFiq : Block.Preceq (eraseFG (storeAt p c E rho iq x).fg.F) Q :=
    block_preceq_trans (eraseFG_preceq (mono iq i x hx hqi.le).1) hFQ
  exact healing_support_release_compat (hroots := hrec.base.receiptIdealization)
    E rho hE hDelta s hSync hx hx ht hiq (hScope.first i iq x hx ht hiq
      (healing_recovery_gate_enabled E rho hrec hx ht
        (healing_gate_cut_of_batch_cut E s hScope.cut))
      (healing_recovery_joined E rho hrec hx
        (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
          healing_gate_cut_of_batch_cut E s hScope.cut)
        (by exact (hgst.trans hus).trans (by
          change 4 * p.Δ * (s : Int) + p.Δ ≤
            4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
          push_cast; linarith [p.deltaPos]))
        ((hS.in_horizon _ (List.mem_of_getElem? hiq)).2))) hτ hFiq lease hkeep

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:965–973 (old output); 01 §6.6, §7; plan H-REPAIR step 9 (d).
DC: INTENTIONAL before an honest gate of label s, the output is below the gate F or a
stored block of slot at most s: a gate before it has a label w < s and its result is the
anchor or a stored block of slot at most w + 1; a reconciliation moves S to an earlier F. -/
private theorem repair_gate_label (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have he : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hd : (4 * p.Δ : Int) ≠ 0 := by
    have hp : (0 : Int) < p.Δ := p.deltaPos
    omega
  rw [he, Int.mul_ediv_cancel_left _ hd, Int.toNat_natCast]

private theorem repair_gate_suppressed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {w : Slot}
    (hw : IsGateTick p c rho j x w)
    (hj : joinedNow p (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams w)) = false) :
    (fgsaAC E rho).output (j + 1) x = (fgsaAC E rho).output j x := by
  let st := storeAt p c E rho j x
  let pre := clockPre p st (SA.gateTime p.toParams w)
  have hpreS : pre.base.stableRecord = st.base.stableRecord := by
    unfold pre clockPre
    dsimp only
    split_ifs <;> rfl
  have hnew : GridCO.savedGenuine pre.base w = none := by
    rw [savedGenuine_congr (clockPre_genuine p st _)]
    exact fgsa_gate_fresh E rho hs hw
  have hNest : NestOK pre := by
    change Block.Preceq (eraseFG pre.fg.F) pre.base.stableRecord
    rw [clockPre_fg, hpreS]
    exact (storeBundle_stateBefore E rho j x).nest
  have hkeep := ((gateStep_unjoined p pre w hnew hj).2.2 hNest).2.2
  change (rho.stateBefore E (j + 1) x).st.base.stableRecord = _
  rw [V2.D.Run.stateBefore_succ E rho hw]
  simp only [V2.D.World.step, Function.update_self]
  have he : FGSA.clock p st (SA.gateTime p.toParams w) = gateStep p pre w := by
    change (if isGateTime p (SA.gateTime p.toParams w) then
      gateStep p pre ((SA.gateTime p.toParams w - 6 * p.Δ) / (4 * p.Δ)).toNat else pre) = _
    rw [(isGateTime_iff p _).mpr ⟨w, rfl⟩, ite_eq_left rfl, repair_gate_label]
  have hClock : (FGSA.clock p st (SA.gateTime p.toParams w)).base.stableRecord =
      st.base.stableRecord := by rw [he, hkeep, hpreS]
  exact (congrArg (fun u : State p.n => u.base.stableRecord)
    (tick_st (c := c) E rho (rho.stateBefore E j x) x (SA.gateTime p.toParams w))).trans hClock

theorem repair_output_bound (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (mono : RMonoAll p c E rho)
    {s : Slot} {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
 :
    ∀ j, j ≤ i →
      Block.Preceq ((fgsaAC E rho).output j x) (eraseFG (storeAt p c E rho i x).fg.F) ∨
        ((fgsaAC E rho).output j x ∈ (storeAt p c E rho j x).base.blocks ∧
          ((fgsaAC E rho).output j x).slot ≤ s) := by
  have hS := hE.toScheduleWellFormed
  have hFi (j : Nat) (hj : j ≤ i) :
      Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) (eraseFG (storeAt p c E rho i x).fg.F) :=
    eraseFG_preceq (mono j i x hx hj).1
  have hblk (j : Nat) (b : Block) (hb : b ∈ (storeAt p c E rho j x).base.blocks) :
      b ∈ (storeAt p c E rho (j + 1) x).base.blocks :=
    (fgsa_store_durable p c E rho (Nat.le_succ j) x).2.1.subset hb
  have hkeep (j : Nat) (hj : j + 1 ≤ i)
      (h : Block.Preceq ((fgsaAC E rho).output j x) (eraseFG (storeAt p c E rho i x).fg.F) ∨
        ((fgsaAC E rho).output j x ∈ (storeAt p c E rho j x).base.blocks ∧
          ((fgsaAC E rho).output j x).slot ≤ s)) (B : Block)
      (hB : B = (fgsaAC E rho).output j x ∨
        B = eraseFG (storeAt p c E rho j x).fg.F ∨
        B = eraseFG (storeAt p c E rho (j + 1) x).fg.F) :
      Block.Preceq B (eraseFG (storeAt p c E rho i x).fg.F) ∨
        (B ∈ (storeAt p c E rho (j + 1) x).base.blocks ∧ B.slot ≤ s) := by
    rcases hB with rfl | rfl | rfl
    · rcases h with h | ⟨hm, hsl⟩
      · exact Or.inl h
      · exact Or.inr ⟨hblk j _ hm, hsl⟩
    · exact Or.inl (hFi j (Nat.le_of_succ_le hj))
    · exact Or.inl (hFi (j + 1) hj)
  intro j
  induction j with
  | zero =>
    intro _
    left
    have h0 : (fgsaAC E rho).output 0 x = .genesis := rfl
    rw [h0]
    exact block_genesis_preceq _
  | succ j ih =>
    intro hj
    have hprev := ih (Nat.le_of_succ_le hj)
    rcases fgsaAC_output_step E rho j x with he | ⟨w, hw⟩ | ⟨o, t, b, _, _, _, ho⟩ |
        ⟨t, hr, _⟩
    · rw [he]
      exact hkeep j hj hprev _ (Or.inl rfl)
    · by_cases hJ : joinedNow p (clockPre p (storeAt p c E rho j x)
          (SA.gateTime p.toParams w)) = true
      swap
      · rw [repair_gate_suppressed E rho hS hw (Bool.eq_false_of_ne_true hJ)]
        exact hkeep j hj hprev _ (Or.inl rfl)
      have spec := fgsaAC_gate_write E rho j w x hJ hw
      have hwlt : w < s := by
        have hlt := fgsa_tick_time_strict E rho hS hw ht hj
        change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hlt
        have hd := p.deltaPos
        have h : (w : Int) < s := by nlinarith
        exact_mod_cast h
      rcases spec.effects with ⟨_, hout, _⟩ | run
      · rw [hout]
        exact hkeep j hj hprev _ (Or.inl rfl)
      · cases hr : (fgsaAC E rho).raw j w x with
        | none =>
          rw [(run.empty hr).1]
          exact hkeep j hj hprev _ (Or.inl rfl)
        | some h =>
          by_cases hall : ∀ lease ∈ ((fgsaAC E rho).gateView j x w).obligations,
              Block.Compatible (Gen.AC.Lease.target lease) h
          · rw [(run.accept h hr hall).1, Gen.AC.normalizeOutput_def]
            have hadv : GridCO.advance ((fgsaAC E rho).output j x) h =
                (fgsaAC E rho).output j x ∨ GridCO.advance ((fgsaAC E rho).output j x) h = h := by
              unfold GridCO.advance
              split
              · exact Or.inl rfl
              · exact Or.inr rfl
            have hanc : (fgsaAC E rho).anchor j x = eraseFG (storeAt p c E rho j x).fg.F := rfl
            have hcand : Block.Preceq h (eraseFG (storeAt p c E rho i x).fg.F) ∨
                (h ∈ (storeAt p c E rho (j + 1) x).base.blocks ∧ h.slot ≤ s) := by
              have hc := spec.raw_eq.symm.trans hr
              let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)
              have hpre : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w =
                  some h := by
                have hv := fgsa_clockPre_gateView p (storeAt p c E rho j x) w
                change SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho j x).fg.F)
                  (SA.Root.expire { actView (storeAt p c E rho j x) with
                    now := SA.gateTime p.toParams w } (SA.gateTime p.toParams w)) w = some h at hc
                rw [← hv] at hc
                rw [clockPre_fg]
                exact hc
              have hm' : h ∈ (storeAt p c E rho j x).base.blocks := by
                have hm := (compat_of_confirmation p pre (cstoreInv_clockPre p _
                  (cstoreInv_stateBefore E rho j x) _) hpre).2
                rwa [(clockPre_fields p _ _).2.1] at hm
              refine Or.inr ⟨hblk j h hm', ?_⟩
              have hb := (fgsa_stateBefore_bounds E rho hS j x).1 h hm'
              have hd := p.deltaPos
              have hpos : 0 < SA.gateTime p.toParams w := by
                change 0 < 4 * p.Δ * (w : Int) + 6 * p.Δ
                have := Int.natCast_nonneg w
                positivity
              have hn := fgsa_preTick_now_lt_joined E rho hS hw hpos
                ((clockPre_joined p _ _).symm ▸ hJ)
              have hsl := Internal.slotOf_mono (p := p) (le_of_lt hn)
              have he : p.slotOf (SA.gateTime p.toParams w) = w + 1 :=
                (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j x) _).2.symm.trans
                  (fgsa_gate_slot (c := c) _ w)
              exact (hb.trans (hsl.trans_eq he)).trans (Nat.succ_le_of_lt hwlt)
            split
            · rcases hadv with ha | ha <;> rw [ha]
              · exact hkeep j hj hprev _ (Or.inl rfl)
              · exact hcand
            · rw [hanc]
              exact hkeep j hj hprev _ (Or.inr (Or.inl rfl))
          · obtain ⟨lease, hl'⟩ := not_forall.mp hall
            obtain ⟨hl, hn⟩ := not_imp.mp hl'
            rw [(run.veto h hr ⟨lease, hl, hn⟩).1]
            exact hkeep j hj hprev _ (Or.inl rfl)
    · rw [ho, Gen.AC.normalizeOutput_def]
      split
      · exact hkeep j hj hprev _ (Or.inl rfl)
      · exact hkeep j hj hprev _ (Or.inr (Or.inr rfl))
    · have he : (fgsaAC E rho).output (j + 1) x = (fgsaAC E rho).output j x := by
        change (rho.stateBefore E (j + 1) x).st.base.stableRecord = _
        rw [V2.D.Run.stateBefore_succ E rho hr]
        simp only [V2.D.World.step, Function.update_self]
        exact acRestart_stableRecord p _ t
      rw [he]
      exact hkeep j hj hprev _ (Or.inl rfl)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:965–973; 01 §7; plan H-REPAIR step 9 (d). DC: INTENTIONAL the old output
at an honest gate of an exact-HEAD slot is not a strict descendant of Q. -/
theorem repair_gate_old_output [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    Block.Preceq Q ((fgsaAC E rho).output i x) → (fgsaAC E rho).output i x = Q := by
  intro hQo
  have hE := hrec.base.valid
  have hFQ := repair_gate_finality_le E rho hrec mono crossing qc hgst hphase hus hgate hQs
    hhead hx ht hScope
  rcases repair_output_bound E rho hE mono hx ht i le_rfl with h | ⟨hm, hsl⟩
  · exact block_preceq_antisymm (block_preceq_trans h hFQ) hQo
  · by_contra hne
    have hlt := repair_stored_slot_lt E rho hE i x hm hQo (Ne.symm hne)
    rw [hQs] at hlt
    exact lt_irrefl _ (lt_of_lt_of_le hlt hsl)

private theorem gate_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.9:1131–1144, H.6:965–973; plan H-REPAIR step 9 (e).
DC: INTENTIONAL at an honest gate of an exact-HEAD slot s = rR, Q has an FG
representative in the full filtered domain of the action read: the HEAD witness gives a
stored path at the floor; F is below Q (01 §6.6) and, in a top-J phase, J is below the
HEAD by H.3. -/
theorem repair_gate_opening [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    ∀ r, s = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st) := by
  intro r _
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvd : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s :=
    (le_add_of_nonneg_right hd.le).trans hvd
  have hhor : SA.voteTime p.toParams s ≤ rho.horizon := (hvg.trans hgate).trans hphase.2.1
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hx s hhor
    (hrec.awake x hx _ (hgst.trans hus) hhor)
  have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hQK := Option.some.inj ((hhead x hx (hrec.toRecovery₂.joinedAt_of_slotStart_le E rho s
      hScope.cut hhor x hx)).symm.trans hhl)
  obtain ⟨W, hW, hQW, hZW, _, hloW⟩ := healing_support_frame_at
    (hroots := hrec.base.receiptIdealization)
    E rho (fun _ => mono) crossing hE hDelta
    hrec.sync hgst hphase hus (hvd.trans hgate) hx hjz
    x (healing_carriers_cut_at p c E rho hrec hScope.cut
      (hScope.carriers i x _ hvd (hgate.trans hphase.2.1)) hx ht hvd jz x hx hjz)
    (B := Q) (hQK ▸ block_preceq_refl _) hx
    (healing_support_idxBefore_le p c E rho hS ht hvd)
    (healing_support_idxBefore_le p c E rho hS ht (hus.trans hvg))
    (healing_phase_lt_timeIdx p c E rho hS ht hgate).le
  have hFQ := repair_gate_finality_le E rho hrec mono crossing qc hgst hphase hus hgate hQs
    hhead hx ht hScope
  have hinv := cstoreInv_stateBefore E rho i x
  obtain ⟨D, hD, heD, hDW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hW hQW
  -- The root is below Q.
  have hZQ : Block.Preceq (eraseFG (R_at p c E rho i x).Z) Q := by
    have hfi := healing_settled_frame_strict p c E rho crossing u v m J contested hphase i x
      (healing_support_idxBefore_le p c E rho hS ht (hus.trans hvg))
      (healing_phase_lt_timeIdx p c E rho hS ht hgate).le hx
    cases J with
    | some J0 =>
      have hfz := healing_settled_frame_strict p c E rho crossing u v m (some J0) contested
        hphase jz x (healing_support_idxBefore_le p c E rho hS hjz hus)
        (healing_phase_lt_timeIdx p c E rho hS hjz (hvg.trans hgate)).le hx
      obtain ⟨_, _, hZi, _⟩ := hfi.2.2.2.1
      obtain ⟨_, _, hZz, _⟩ := hfz.2.2.2.1
      obtain ⟨K, hK, hKe, _⟩ := healing_full_witness_all p c E rho hS crossing hx hjz
      have hZK := ((KitFG.mem_filteredFromView _ _ _ _).mp hK).2.2.1
      change FGBlock.Preceq (controls p ((fgsa p c).clock (rho.stateBefore E jz x)
        (SA.voteTime p.toParams s)).st).Z K at hZK
      have hcz : controls p ((fgsa p c).clock (rho.stateBefore E jz x)
          (SA.voteTime p.toParams s)).st = controls p (storeAt p c E rho jz x) :=
        repair_controls_clock _ _
      rw [hcz, hZz] at hZK
      change Block.Preceq (eraseFG (controls p (storeAt p c E rho i x)).Z) Q
      rw [hZi, hQK]
      have h := eraseFG_preceq hZK
      rw [hKe] at h
      exact h
    | none =>
      obtain ⟨_, hZi, _⟩ := hfi.2.2.2.1
      change Block.Preceq (eraseFG (controls p (storeAt p c E rho i x)).Z) Q
      rw [hZi]
      exact hFQ
  refine ⟨D, heD, ?_⟩
  have hc : frameR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st =
      R_at p c E rho i x := repair_controls_clock _ _
  have hfg : ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st.fg =
      (storeAt p c E rho i x).fg := clock_fg p _ _
  rw [domainR_def, treeT_def, hc, hfg]
  exact (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hD, gate_lift (heD ▸ hFQ),
    gate_lift (heD ▸ hZQ), W, hW, hDW, hloW⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:965–973, 01 §6.6; plan H-REPAIR step 9 (R3).
DC: INTENTIONAL all five ExactServiceGateGeometry fields at every honest gate tick of an
exact-HEAD slot s inside the phase (u ≤ v_s, d_s ≤ v). Hypotheses: Recovery₂ (standing),
RMono, RXing, RQCOrigin (FGFoundation field), and the inline last-write premise (B27). -/
theorem repair_gate_geometry [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hus : u ≤ SA.voteTime p.toParams s) (hgate : SA.gateTime p.toParams s ≤ v)
    {Q : Block} (hQs : Q.slot = s)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hScope : RepairGateScope E rho s) :
    ExactServiceGateGeometry E rho i x s Q :=
  { toGateReceiptGeometry := repair_gate_receipt E rho hrec mono crossing qc hgst hphase hus
      hgate hQs hhead hx ht hScope
    guard := repair_gate_guard E rho hrec mono crossing qc writes hgst hphase hus hgate hQs
      hhead hx ht hScope
    old_output := repair_gate_old_output E rho hrec mono crossing qc hgst hphase hus hgate
      hQs hhead hx ht hScope
    opening_domain := repair_gate_opening E rho hrec mono crossing qc hgst hphase hus hgate
      hQs hhead hx ht hScope }

end AvailableChain.FGSA.Run
end
