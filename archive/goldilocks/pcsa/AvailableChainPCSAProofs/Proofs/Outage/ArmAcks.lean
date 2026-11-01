module
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun
public import AvailableChainPCSAProofs.Proofs.Outage.Choice
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Shared.HeadSupport
public import AvailableChainPCSAProofs.Proofs.Shared.RunEvidence
public import AvailableChainPCSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainPCSAProofs.Proofs.Shared.Walk
public import AvailableChainPCSAClaims.Statements.LaneReads

public section

/-! Honest acks, HEADs and PCs in the Outage lane (pcsa34-r4.3 §5.1, §5.4.1
steps 3–5). A PC seen at an honest node by time `T` has an honest ack emitted
by `T`; an honest ack names the exact HEAD of an honest voter of its slot;
honest acks of one slot name one block. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-! ### Duty reads at a tick -/

/-- The tick index of a node and time is the index of that tick event. -/
theorem pcsa_tickIdx_of_event (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) : V2.D.Run.tickIdx? rho y t = some k := by
  have hkl := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨j, hj⟩ : ∃ j, V2.D.Run.tickIdx? rho y t = some j := by
    rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
    refine ⟨rho.events[k], List.getElem_mem hkl, ?_⟩
    rw [(List.getElem?_eq_some_iff.mp hk).2]
    simp
  have hje := V2.D.Run.tickIdx?_spec hj
  rw [hj, (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp hje).1 hs.nodup).mp
    (hje.trans hk.symm)]

/-- The post-clock read of a node's tick is the clock of the pre-tick state. -/
theorem pcsa_postClock_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) :
    pcsa_postClock E rho y t =
      some ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k y) t) := by
  rw [pcsa_postClock_def, pcsa_preTick_def, pcsa_tickIdx_of_event E rho hs hk]
  rfl

/-- A post-clock read comes from a tick of the node at that time. -/
theorem pcsa_postClock_some (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {y : V} {t : Time} {nd : Node p} (h : pcsa_postClock E rho y t = some nd) :
    ∃ k, rho.events[k]? = some (.tick y t) ∧
      nd.st = clock p (V2.D.Run.stateBefore E rho k y).st t := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at h
  cases hk : V2.D.Run.tickIdx? rho y t with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h
    have he := Option.some.inj h
    exact ⟨k, V2.D.Run.tickIdx?_spec hk, by rw [← he]; rfl⟩

/-- A resolved HEAD is a block of the resolving view. -/
theorem pcsa_resolvedHead_mem (v : GridCO.State p.n .root) (o : GridCO.Wire p.n .root)
    (b : Block) (h : GridCO.resolvedHead? v o = some b) : b ∈ v.blocks := by
  delta GridCO.resolvedHead? at h
  obtain ⟨tg, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨B, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hB
    cases Option.some.inj h
    exact hB
  · contradiction

/-- An N target is a stored block. -/
theorem pcsa_nTarget_mem_blocks (st : State p.n) (s : Slot) (b : Block)
    (h : nTarget? p st s = some b) : b ∈ st.base.blocks := by
  have hm := List.mem_of_find?_eq_some h
  obtain ⟨o, -, ho⟩ := List.mem_filterMap.mp hm
  exact (List.mem_filter.mp (pcsa_resolvedHead_mem _ o b ho)).1

/-- An ack decision is an N target. -/
theorem pcsa_ackFor_nTarget (st : State p.n) (s : Slot) (b : Block)
    (h : ackFor p st s = some b) : nTarget? p st s = some b :=
  (Option.filter_eq_some_iff.mp h).1

/-- An emitted ack is the honest ack decision of its tick. -/
theorem pcsa_ack_emission_read (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (y : V) (s : Slot) (i : Fin p.n) (r : BlockId)
    (t : Time) (k : Nat) (hk : rho.events[k]? = some (.tick y t))
    (ho : ackObj p s i r ∈ V2.D.Run.emitsAt E rho k) :
    t = SA.earlyTime p.toParams s ∧ E.awake y t = true ∧
      ∃ X, X.root = r ∧ ackAt p c E rho y s = some (some X) ∧
        X ∈ (clock p (V2.D.Run.stateBefore E rho k y).st t).base.blocks := by
  obtain ⟨ht, ha⟩ := ack_emission_duty p c m E rho y s i r t k hk ho
  have ho' := ho
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho'
  obtain ⟨haw, -⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ y t (.base (.ack s)) i (.ack r)).mp ho'
  have heq := actWith_def m p c ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k y) t)
    (.ackAction s) (rho.input y t)
  rw [heq] at ha
  change (ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st t) s).map
    (fun b => Msg.ack b.root) = some (.ack r) at ha
  obtain ⟨X, hX, hr⟩ := Option.map_eq_some_iff.mp ha
  refine ⟨ht, haw, X, Msg.ack.inj hr, ?_, pcsa_nTarget_mem_blocks _ s X
    (pcsa_ackFor_nTarget _ s X hX)⟩
  rw [pcsa_ackAt_def, ← ht, pcsa_postClock_tick E rho hs hk]
  change some (ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st t) s) = _
  rw [hX]

/-- An emitted HEAD is the HEAD read of its tick. -/
theorem pcsa_head_emission_read (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (y : V) (s : Slot) (i : Fin p.n) (r : BlockId)
    (t : Time) (k : Nat) (hk : rho.events[k]? = some (.tick y t))
    (ho : (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) ∈ V2.D.Run.emitsAt E rho k) :
    t = SA.voteTime p.toParams s ∧ E.awake y t = true ∧
      (headVote p (clock p (V2.D.Run.stateBefore E rho k y).st t) s).root = r ∧
      voteHeadAt p c E rho y s =
        some (headVote p (clock p (V2.D.Run.stateBefore E rho k y).st t) s) := by
  obtain ⟨ht, ha⟩ := head_emission_duty p c m E rho y s i r t k hk ho
  have ho' := ho
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho'
  obtain ⟨haw, -⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ y t (.base (.head s)) i (.head r)).mp ho'
  have heq := actWith_def m p c ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k y) t)
    (.headAction s) (rho.input y t)
  rw [heq] at ha
  change some (Msg.head (headVote p (clock p (V2.D.Run.stateBefore E rho k y).st t) s).root) =
    some (.head r) at ha
  refine ⟨ht, haw, Msg.head.inj (Option.some.inj ha), ?_⟩
  rw [pcsa_voteHeadAt_def, ← ht, pcsa_postClock_tick E rho hs hk]
  rfl

/-! ### Run blocks -/

/-- Under a vacuous frame every HEAD of a store with the Outage invariant is a
block with the run property. -/
theorem pcsa_headVote_prop (R : Block → Prop) (st : State p.n) (s : Slot)
    (h : OutageStore R st) (hv : FrameVacuous p st) (hg : R .genesis) :
    R (headVote p st s) := by
  have hT := pcsa_fullTree_vacuous p st hv
  have hZ : eraseFG (controls p st).Z = .genesis := by
    rw [((FrameVacuous_def p st).mp hv).2.1]
    rfl
  have hTF : ∀ b, (∃ B ∈ fullTree p st, eraseFG B = b) → R b := by
    rintro b ⟨B, hB, rfl⟩
    rw [hT] at hB
    exact h.tf B hB
  delta headVote
  split
  · exact hg
  · rcases pcsa_headInTree_mem_or_root p st (voterPC p st s) _ _ _ with he | hm
    · rw [he]
      rcases pcsa_liveRoot_origin p st (voterPC p st s) with hb | hb
      · rw [hb]
        cases voterPC p st s with
        | none => change R (eraseFG (controls p st).Z); rw [hZ]; exact hg
        | some v =>
          change R (if frameActive p st v then v.target else eraseFG (controls p st).Z)
          split
          · rename_i ha
            exact hTF _ (of_decide_eq_true ha)
          · rw [hZ]; exact hg
      · obtain ⟨-, -, -, -, hin, -⟩ := (pcsa_walkLocks_mem p st _ _).mp hb
        exact hTF _ hin
    · rw [erasedList_def] at hm
      obtain ⟨B, hB, he⟩ := h.lift _ (List.mem_filter.mp hm).1
      have hR := h.tf B hB
      rw [he] at hR
      exact hR

/-- A block of an honest clocked store is in the run's named scope. -/
theorem pcsa_clocked_block_rootBlock (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (y : V) (hy : y ∈ rho.honest) (k : Nat) (t : Time) (b : Block)
    (hb : b ∈ (clock p (V2.D.Run.stateBefore E rho k y).st t).base.blocks) :
    RootBlockInRun p c E rho b := by
  have h := pcsa_clock_outageStore p _ _ t (pcsa_outageStore_stateBefore E rho k y hy)
  obtain ⟨B, hB, rfl⟩ := h.lift b hb
  exact h.tf B hB

/-- A HEAD read of an honest node is in the run's named scope (stage 1). -/
theorem pcsa_clocked_head_rootBlock (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hfr : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest) (k : Nat) (t : Time)
    (s : Slot) :
    RootBlockInRun p c E rho (headVote p (clock p (V2.D.Run.stateBefore E rho k y).st t) s) := by
  have h := pcsa_clock_outageStore p _ _ t (pcsa_outageStore_stateBefore E rho k y hy)
  have hv : FrameVacuous p (clock p (V2.D.Run.stateBefore E rho k y).st t) := by
    have h0 := hfr y hy k
    rw [FrameVacuous_def] at h0 ⊢
    rw [controls_def, (pcsa_clock_frame p _ t).2.2.2.1, ← controls_def]
    exact h0
  have hg : RootBlockInRun p c E rho .genesis := by
    refine ⟨.genesis, ⟨.genesis, Or.inr ⟨y, hy, 0, ?_⟩, ?_⟩, rfl⟩
    · dsimp only [V2.D.Run.stateBefore, pcsaWith]
      dsimp only [initial]
      simp [State.namedBodies]
    · simp [NamedProposal.Preceq, NamedProposal.preceq]
  exact pcsa_headVote_prop _ _ s h hv hg

/-! ### Honest acks -/

variable [Fintype V]

omit [Fintype V] in
/-- An honest ack has a `q_N` HEAD support: every honest seat in it emitted
the exact HEAD of the ack's root, and the ack block is in the named scope. -/
theorem pcsa_honest_ack_support (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (x : V) (j : Slot) (X : Block)
    (hack : HonestAckAt p c E rho x j X) :
    RootBlockInRun p c E rho X ∧
    ∃ S : Finset (Fin p.n), Gen.Pure.qN p.n ≤ S.card ∧ ∀ i ∈ S,
      rho.seatOf (.base (.head j)) i ∈ rho.honest →
      ∃ a, V2.D.Run.emits E rho (rho.seatOf (.base (.head j)) i)
        (⟨.seat (.base (.head j)) i, .head X.root⟩ : Obj p) a := by
  obtain ⟨hx, -, hread⟩ := hack
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, hX⟩ := Option.map_eq_some_iff.mp hread
  obtain ⟨k, -, hst⟩ := pcsa_postClock_some E rho hnd
  have hX' : ackFor p (clock p (V2.D.Run.stateBefore E rho k x).st
      (SA.earlyTime p.toParams j)) j = some X := by
    rw [← hst]; exact hX
  have hN := pcsa_ackFor_nTarget _ j X hX'
  refine ⟨pcsa_clocked_block_rootBlock E rho x hx k _ X (pcsa_nTarget_mem_blocks _ j X hN), ?_⟩
  obtain ⟨S, hS, hs⟩ := nTarget_support p _ j X hN
  have he := clock_evidence p (RootBlockInRun p c E rho) (HeadAuthentic E rho)
    (V2.D.Run.stateBefore E rho k x).st (SA.earlyTime p.toParams j)
    (evidence_stateBefore E rho h.valid.toUnforgeableSignatures k _ hx)
  rw [StoreEvidence_def] at he
  refine ⟨S, hS, ?_⟩
  intro i hi hh
  have ha := he.2.2 _ (hs i hi)
  rw [HeadAuthentic_def] at ha
  exact ha j i X.root rfl hh

/-- Honest acks of one slot name one block. -/
theorem pcsa_honest_ack_unique (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (x y : V) (j : Slot) (X Y : Block)
    (hX : HonestAckAt p c E rho x j X) (hY : HonestAckAt p c E rho y j Y) : X = Y := by
  classical
  obtain ⟨hrX, S, hS, hsent⟩ := pcsa_honest_ack_support E rho h x j X hX
  obtain ⟨hrY, T, hT, hsent'⟩ := pcsa_honest_ack_support E rho h y j Y hY
  apply pcsa_outage_rootBlock_eq E rho h hrX hrY
  obtain ⟨i, hi, hh⟩ := pcsa_n_inter_honest rho h.cstar hf j S T hS hT
  obtain ⟨t, ht⟩ := hsent i (Finset.mem_inter.mp hi).1 hh
  obtain ⟨u, hu⟩ := hsent' i (Finset.mem_inter.mp hi).2 hh
  exact (head_emission_unique p c m E rho h.valid.nodup _ j i _ _ t u ht hu).1

/-- An honest ack names the exact HEAD of an honest awake voter of its slot (stage 1). -/
theorem pcsa_honest_ack_head (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    (x : V) (j : Slot) (X : Block) (hX : HonestAckAt p c E rho x j X) :
    ∃ y, HonestHeadAt p c E rho y j X := by
  obtain ⟨hrX, S, hS, hsent⟩ := pcsa_honest_ack_support E rho h x j X hX
  have hS' : pcQuorum p.n ≤ S.card := by
    have : pcQuorum p.n ≤ Gen.Pure.qN p.n := by
      change (p.n + 1) / 2 ≤ (3 * p.n + 3) / 4
      omega
    omega
  obtain ⟨i, hi, hh⟩ := pcsa_quorum_honest rho (.base (.head j))
    (h.cstar (.base (.head j)) trivial).injective hf S rfl hS'
  obtain ⟨a, k, hk, ho⟩ := hsent i hi hh
  obtain ⟨ha, haw, hroot, hread⟩ := pcsa_head_emission_read E rho h.valid.toScheduleWellFormed
    _ j i X.root a k hk ho
  have hy : rho.seatOf (.base (.head j)) i ∈ rho.honest := hh
  refine ⟨rho.seatOf (.base (.head j)) i, hy, ha ▸ haw, ?_⟩
  rw [hread]
  congr 1
  exact pcsa_outage_rootBlock_eq E rho h
    (pcsa_clocked_head_rootBlock E rho hfr _ hy k a j) hrX hroot

end AvailableChain.PCSA.Run
end
