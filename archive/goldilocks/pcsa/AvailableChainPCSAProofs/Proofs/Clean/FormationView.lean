module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationProposal
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRelay
public import AvailableChainPCSAProofs.Proofs.Shared.BodyReceipt
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView

public section

/-! Formation metadata, receipt and early views (pcsa34-r4.3b §5.3).
Every admitted slot-s proposal has the honest emitted body and vote lists.
F1 handles an old accepted PC before t_s, including at an asleep receiver.
Frozen identity receipt and carried-PC presence fix every early view and A2.
The metadata scope and voter-view lemmas are the Shared/VoterView ones.
FormationOrigins supplies hFrozenPCOrigin at the actual early read.
The view proof names hFrozenPCReceipt and hCarriedPresence.
Root-mode vote transport preserves counts and scores under explicit receipt
and resolution inputs. In stage 1 the low-parent eligibility arm is false.
OPEN: derive receipt-to-collection, proposal presence and retained input
producers from the run. Retained receipt and terminal child inputs give
the exact honest HEAD. No whole Formation or FormationSource claim is exported. -/

open AvailableChain
namespace AvailableChain.PCSA
variable {n : Nat}

private theorem metadata_normalize (st : State n) :
    (normalizeS st).proposals = st.proposals := by
  delta normalizeS
  split <;> rfl

private theorem metadata_reconcile (st : State n) :
    (reconcile st).proposals = st.proposals := by
  delta reconcile
  rw [metadata_normalize]

private theorem metadata_collect (st : State n) :
    (collectPCs st).proposals = st.proposals := by
  apply collectPCs_preserves
  intro acc C
  delta installPC
  split <;> rfl

private theorem metadata_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals := by
  delta admitRow
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem metadata_rows (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).proposals = st.proposals := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, metadata_row]

private theorem metadata_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem metadata_raws (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).proposals = st.proposals := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, metadata_raw]

private theorem metadata_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).proposals = st.proposals := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some val =>
    rcases val with ⟨s, i, r⟩
    dsimp only
    split_ifs <;> rfl

private theorem metadata_gate (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).proposals = st.proposals := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some result =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State p.n => acc.proposals = st.proposals)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc' : State p.n => acc'.proposals = st.proposals)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem metadata_clock (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  have hp : (clockPre p st t).proposals = st.proposals := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, metadata_normalize]
    split
    · exact hp
    · rw [metadata_gate]; exact hp
  · exact hp

private theorem metadata_process_accepted (p : Params) (st : State p.n) (o : Wire p.n)
    (P : Wire p.n → Prop) (h : ∀ w ∈ st.proposals, P w)
    (ho : ∀ s N B, o.decode = some (.block s N) → namedParentHeld st N = true →
      parentFG st N.erase = some B → blockAccepted p st s N B = true →
      P ⟨.proposer s, .proposal N⟩) :
    ∀ w ∈ (process p st o).proposals, P w := by
  cases hd : o.decode with
  | none => delta process; rw [hd]; exact h
  | some d =>
    cases d with
    | vote s i r => delta process; rw [hd]; exact h
    | row i body => delta process; rw [hd, metadata_row]; exact h
    | ack s i r =>
      delta process
      rw [hd]
      change ∀ w ∈ (collectPCs (poolAck p st ⟨o.auth, r⟩)).proposals, P w
      rw [metadata_collect, metadata_pool]
      exact h
    | pc C =>
      delta process
      rw [hd]
      change ∀ w ∈ (admitPC st C).proposals, P w
      delta admitPC
      split
      · rw [metadata_collect, metadata_raws]; exact h
      · exact h
    | block s N =>
      delta process
      rw [hd]
      change ∀ w ∈ (admitBlock p st s N).proposals, P w
      delta admitBlock
      split
      · exact h
      · rename_i hNamed
        cases hp : parentFG st N.erase with
        | none => exact h
        | some B =>
          dsimp only
          split
          · rename_i hAcc
            rw [metadata_rows, metadata_collect, metadata_raws]
            have hh : ∀ w ∈ st.proposals ++ [⟨.proposer s, .proposal N⟩], P w := by
              intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · exact h w hw
              · exact List.mem_singleton.mp hw ▸
                  ho s N B hd (by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hNamed)
                    hp hAcc
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | exact hh
              | (rw [metadata_reconcile]; exact hh)
          · exact h

/-- Stored proposal metadata has its body in the same reachable store. -/
theorem pcsa_formation_metadata_body (p : Params) (st : State p.n) (hReach : Reachable p st) :
    ∀ s N, (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals → N.erase ∈ st.base.blocks := by
  induction hReach with
  | init =>
    intro s N hm
    change _ ∈ ([] : List (Wire p.n)) at hm
    exact (List.not_mem_nil hm).elim
  | tick t hr ih =>
    intro s N hm
    rw [metadata_clock] at hm
    exact pcsa_body_clock_keep p _ t hr (ih s N hm)
  | @deliver st o hr ih =>
    have hAll := metadata_process_accepted p st o
      (fun w => ∀ s N, w = ⟨.proposer s, .proposal N⟩ → N.erase ∈ (process p st o).base.blocks)
      (fun w hw s N he => pcsa_body_process_keep p st o hr (ih s N (he ▸ hw)))
      (by
        intro s N B hd hn hp ha s' N' he
        cases he
        have hpr : process p st o = admitBlock p st s N := by
          delta process
          rw [hd]
        rw [hpr]
        exact pcsa_admitBlock_body_mem p st s N B (pcsa_tree_correspondence p st hr) hn hp ha)
    intro s N hm
    exact hAll _ hm s N rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem metadata_decoded (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta toWire toAuth Wire.decode at hd <;> cases hd
  | seat l i =>
    cases l with
    | prop k =>
      have hi : i = ⟨0, Nat.one_pos⟩ := by
        apply Fin.ext
        change i.val = 0
        have hh : i.val < 1 := i.isLt
        omega
      subst i
      cases payload <;> delta toWire toAuth Wire.decode at hd
      all_goals cases hd
      rfl
    | base l =>
      cases l <;> cases payload <;>
        delta toWire toAuth Wire.decode Label.ackSlot? at hd <;> cases hd

variable [Fintype V]

/-- Every delivered proposal signed for slot s is its honest emitted proposal. -/
theorem pcsa_formation_delivered_proposal_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (j : Nat) (y : V) (o : Obj p) (t : Time)
    (M : NamedProposal p.n) (he : rho.events[j]? = some (.deliver y o t))
    (hd : (toWire p o).decode = some (.block s M)) : M = N := by
  obtain rfl := metadata_decoded o s M hd
  have hx : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ ∈ rho.honest := h.proposal.1
  obtain ⟨u, _, k, hk, hm⟩ := h.base.valid.unforgeable y _ t ⟨j, he⟩ _ hx rfl
  obtain ⟨i, hi, hn⟩ := h.proposal.2
  have hD : Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.prop s) := by
    refine ⟨.propAction s, rfl, ?_⟩
    intro d hd
    exact (pcsa_signLabel_prop d s).mp hd
  have ho := Gen.V2.Duty.emitted_unique_of_singleDuty E rho h.base.valid.nodup
    (.prop s) hD ⟨0, Nat.one_pos⟩ _ k i u _ _ _ hk hi hm hn rfl rfl
  exact Msg.proposal.inj (congrArg V2.Signed.payload ho.2)

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Stored proposal metadata retains the signed slot and the unique slot-s body. -/
theorem pcsa_formation_metadata_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x : V) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho x t = some nd) :
    ∀ w ∈ nd.st.proposals, ∀ k M, w.decode = some (.block k M) →
      M.erase.slot = k ∧ (k = s → M = N) := by
  apply pcsa_metadata_read_scope E rho
    (fun w => ∀ k M, w.decode = some (.block k M) →
      M.erase.slot = k ∧ (k = s → M = N)) ?_ x t nd hr
  intro j y o u k M he hd hs l D hw
  change some (Input.block k M) = some (Input.block l D) at hw
  cases Option.some.inj hw
  refine ⟨hs, ?_⟩
  intro hk
  rw [hk] at hd
  exact pcsa_formation_delivered_proposal_unique E rho s N ΔF h j y o u M he hd

/-- Every PC carried by stored slot-s metadata is the honest proposal's PC. -/
theorem pcsa_formation_carried_pc_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x : V) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho x t = some nd) (C : PC p.n)
    (hm : C ∈ carriedPCs nd.st s) : N.pc = some C := by
  have hmeta := pcsa_formation_metadata_unique E rho s N ΔF h x t nd hr
  delta carriedPCs at hm
  obtain ⟨w, hw, hf⟩ := List.mem_filterMap.mp (List.mem_filter.mp hm).1
  cases hd : w.decode with
  | none => rw [hd] at hf; cases hf
  | some d =>
    rw [hd] at hf
    cases d with
    | vote k i r => cases hf
    | row i body => cases hf
    | ack k i r => cases hf
    | pc D => cases hf
    | block k M =>
      dsimp only at hf
      split at hf
      · rename_i hs
        have hslot : M.erase.slot = M.slot := by cases M <;> rfl
        have hinfo := hmeta w hw k M hd
        have hk : k = s := hinfo.1.symm.trans (hslot.trans hs)
        obtain rfl := hinfo.2 hk
        exact hf
      · cases hf

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [Fintype V] in
/-- Active PC targets at an honest read inherit the run's root injectivity. -/
theorem pcsa_formation_read_pc_root_injective (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (t : Time) (nd : Node p)
    (hx : x ∈ rho.honest) (hr : pcsa_postClock E rho x t = some nd) :
    ∀ A ∈ nd.st.pcs.filter (frameActive p nd.st),
      ∀ B ∈ nd.st.pcs.filter (frameActive p nd.st), A.target.root = B.target.root →
      A.target = B.target := by
  have hReach : Reachable p nd.st := by
    rw [pcsa_postClock_def] at hr
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hp
    subst pre
    subst nd
    exact Reachable.tick t (pcsa_reachable_stateBefore E rho k x)
  have hf := pcsa_formation_frame_read E rho hFrame x t nd hx hr
  have hTree := pcsa_tree_correspondence p nd.st hReach
  have hm : ∀ C ∈ nd.st.pcs.filter (frameActive p nd.st),
      C.target ∈ erasedList nd.st (fullTree p nd.st) := by
    intro C hC
    have ha := (List.mem_filter.mp hC).2
    rw [frameActive_def] at ha
    obtain ⟨D, hD, he⟩ := of_decide_eq_true ha
    rw [erasedList_def]
    refine List.mem_filter.mpr ⟨(hTree _).mpr ⟨D, ?_, he⟩, decide_eq_true ⟨D, hD, he⟩⟩
    rw [pcsa_fullTree_of_frame p nd.st hf] at hD
    exact hD
  have hi := pcsa_formation_read_root_injective E rho h x t nd hx hr (fullTree p nd.st)
  intro A hA B hB he
  exact hi A.target (hm A hA) B.target (hm B hB) he

/-- Receipt bounds every early view, including a node asleep at the vote time. -/
theorem pcsa_formation_early_view_of_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (dst : Node p)
    (_hy : y ∈ rho.honest)
    (hr : pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some dst)
    (hFrozenPCReceipt : ∀ src, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      ∀ C ∈ pcSnapshotAt dst.st (s - 1), frameActive p dst.st C = true →
        ∃ A ∈ src.st.pcs.filter (frameActive p src.st), A.slot = C.slot ∧ A.target = C.target)
    (hCarriedPresence : ∀ D, N.pc = some D →
      D ∈ (pcSnapshotAt dst.st (s - 1) ++ carriedPCs dst.st s).filter (frameActive p dst.st)) :
    (voterPC p dst.st s).map PC.target = N.pc.map PC.target ∧
      ∀ C, voterPC p dst.st s = some C → Block.Preceq C.target N.erase := by
  obtain ⟨src, hs, _, hp, hb⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  have he := pcsa_view_of_frozen_receipt p src.st dst.st s N.pc hp.symm
    (hFrozenPCReceipt src hs)
    (fun C hC => pcsa_formation_carried_pc_unique E rho s N ΔF h y _ dst hr C hC)
    hCarriedPresence (pcsa_formation_read_pc_root_injective E rho h.base h.frame _ _ src
      h.proposal.1 hs)
  refine ⟨he, ?_⟩
  intro C hC
  have hv : N.pc.map PC.target = some C.target := he.symm.trans (by rw [hC]; rfl)
  rw [hv] at hb
  have hParent : Block.Preceq N.erase.parent N.erase := by
    cases N with
    | genesis => rfl
    | node P slot root body raw support rows pc =>
      change (decide (P.erase = _) || Block.preceq P.erase P.erase) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl _))
  exact Gen.Pure.block_preceq_trans hb hParent

/-- Frozen receipt and a passing N count give the all-awake-early A2 ack. -/
theorem pcsa_formation_early_ack_of_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (dst : Node p)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.earlyTime p.toParams s) = true)
    (hr : pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some dst)
    (hN : holdsN p (actView dst.st) s N.erase = true)
    (hFrozenPCReceipt : ∀ src, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      ∀ C ∈ pcSnapshotAt dst.st (s - 1), frameActive p dst.st C = true →
        ∃ A ∈ src.st.pcs.filter (frameActive p src.st), A.slot = C.slot ∧ A.target = C.target)
    (hCarriedPresence : ∀ D, N.pc = some D →
      D ∈ (pcSnapshotAt dst.st (s - 1) ++ carriedPCs dst.st s).filter (frameActive p dst.st)) :
    HonestAckAt p c E rho y s N.erase := by
  obtain ⟨src, hs, hslot, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  exact pcsa_formation_honestAck E rho s N ΔF h y dst hy haw hr hslot hN
    (pcsa_formation_early_view_of_receipt E rho s N ΔF h y dst hy hr
      hFrozenPCReceipt hCarriedPresence).2
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- The honest proposal carries the proposer's raw and support lists unchanged. -/
theorem pcsa_formation_propose_lists (p : Params) (st : State p.n) (s app : Nat)
    (N : NamedProposal p.n)
    (h : (propose p st s).map (Run.withApp p app) = some (.proposal N)) :
    N.raw = (proposerVotes st s).filterMap liftHead? ∧
      N.support = (proposerSupport st s).filterMap liftHead? := by
  obtain ⟨M, hm, hn⟩ := Option.map_eq_some_iff.mp h
  delta propose at hm
  split at hm
  · cases hm
  · obtain ⟨P, hp, he⟩ := Option.map_eq_some_iff.mp hm
    subst M
    change Msg.proposal (namedProposal p P s app _ _ _ _) = Msg.proposal N at hn
    obtain rfl := Msg.proposal.inj hn
    exact ⟨rfl, rfl⟩

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The emitted raw and support lists come from the actual post-clock read. -/
theorem pcsa_formation_emitted_lists (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (x : V) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho k) :
    let st := clock p (V2.D.Run.stateBefore E rho k x).st t
    N.raw = (proposerVotes st s).filterMap liftHead? ∧
      N.support = (proposerSupport st s).filterMap liftHead? := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s) ⟨0, Nat.one_pos⟩
      (.proposal N)).mp ho
  obtain rfl := (pcsa_signLabel_prop d s).mp hl
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
      (withApp p (c.app (rho.input x t))) = some (.proposal N) at ha
  all_goals exact pcsa_formation_propose_lists p _ s _ N ha

variable [Fintype V]

/-- Every admitted slot-s raw/support pair is the honest proposer's pair. -/
theorem pcsa_formation_proposalsAt_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x : V) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho x t = some nd) :
    ∀ pair ∈ proposalsAt nd.st s, pair = (N.raw, N.support) := by
  have hmeta := pcsa_formation_metadata_unique E rho s N ΔF h x t nd hr
  intro pair hp
  delta proposalsAt at hp
  obtain ⟨w, hw, hf⟩ := List.mem_filterMap.mp hp
  cases hd : w.decode with
  | none => rw [hd] at hf; cases hf
  | some d =>
    rw [hd] at hf
    cases d with
    | vote k i r => cases hf
    | row i body => cases hf
    | ack k i r => cases hf
    | pc C => cases hf
    | block k M =>
      dsimp only at hf
      split at hf
      · rename_i hs
        have hslot : M.erase.slot = M.slot := by cases M <;> rfl
        have hinfo := hmeta w hw k M hd
        have hk : k = s := hinfo.1.symm.trans (hslot.trans hs)
        obtain rfl := hinfo.2 hk
        exact (Option.some.inj hf).symm
      · cases hf
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- Stage 1 reduces eligibility to majority support or the current slot. -/
theorem pcsa_formation_eligible_stage1 (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hFrame : Run.FrameVacuous p st) :
    eligible p st raw support B =
      (decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support B) ||
        B.slot == st.slot p) := by
  delta eligible
  rw [hFrame.2.2]
  have hLow : (decide (∃ P ∈ st.fg.TF, eraseFG P = B.parent ∧
      (FGSA.heightView p P).h < 0) : Bool) = false := by
    apply decide_eq_false
    rintro ⟨P, _, _, hP⟩
    exact Nat.not_lt_zero _ hP
  rw [hLow, Bool.false_or]

/-- Equal resolved scores and voter counts give equal stage-1 eligibility. -/
theorem pcsa_formation_eligible_eq_of_scores (p : Params) (src dst : State p.n)
    (rs ss rt st : List (GridCO.Wire p.n .root))
    (hSrc : Run.FrameVacuous p src) (hDst : Run.FrameVacuous p dst)
    (hSlot : src.slot p = dst.slot p)
    (hCount : GridCO.voterCount rs = GridCO.voterCount rt)
    (hScore : GridCO.goldfishScore src.base.blocks rs ss =
      GridCO.goldfishScore dst.base.blocks rt st) :
    eligible p src rs ss = eligible p dst rt st := by
  funext B
  rw [pcsa_formation_eligible_stage1 p src rs ss B hSrc,
    pcsa_formation_eligible_stage1 p dst rt st B hDst, hCount, hScore, hSlot]

end AvailableChain.PCSA

namespace AvailableChain.PCSA

/-- Root-mode receipt keeps counts and scores even with extra equivocation copies. -/
theorem pcsa_formation_root_merge_counts (p : Params) (src dst : State p.n)
    (rs ss rt st : List (GridCO.Wire p.n .root))
    (hRawKeep : rs ⊆ rt)
    (hRawBack : ∀ o ∈ rt, ∀ i, GridCO.headSeat? o = some i →
      o ∈ rs ∨ GridCO.equivocates rs i = true)
    (hSupportKeep : ss ⊆ st)
    (hSupportBack : ∀ o ∈ st, ∀ i, GridCO.headSeat? o = some i →
      o ∈ ss ∨ GridCO.equivocates rs i = true)
    (hResolution : ∀ o ∈ ss, ∀ B,
      Gen.AC.Root.voteSupports src.base.blocks B o =
        Gen.AC.Root.voteSupports dst.base.blocks B o) :
    GridCO.voterCount rs = GridCO.voterCount rt ∧
      GridCO.goldfishScore src.base.blocks rs ss =
        GridCO.goldfishScore dst.base.blocks rt st := by
  have hSeats : (GridCO.seats p.n rs).toFinset = (GridCO.seats p.n rt).toFinset :=
    Finset.Subset.antisymm (Gen.AC.Root.vote_pool_seats_subset rs rt hRawKeep)
      (Gen.AC.Root.vote_pool_seats_backward rs rt hRawBack)
  have hEq : ∀ i, GridCO.equivocates rs i = GridCO.equivocates rt i := by
    intro i
    cases he : GridCO.equivocates rs i with
    | true => exact (Gen.AC.Root.vote_pool_equivocates_mono rs rt i hRawKeep he).symm
    | false =>
      apply Eq.symm
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨a, ha, b, hb, hne, hi, hj⟩ := (Gen.AC.Root.cap_pair rt i).mp ht
      have har := (hRawBack a ha i hi).resolve_right (by rw [he]; exact Bool.false_ne_true)
      have hbr := (hRawBack b hb i hj).resolve_right (by rw [he]; exact Bool.false_ne_true)
      have hh := (Gen.AC.Root.cap_pair rs i).mpr ⟨a, har, b, hbr, hne, hi, hj⟩
      rw [he] at hh
      cases hh
  constructor
  · rw [Gen.AC.Root.vote_pool_voterCount_card, Gen.AC.Root.vote_pool_voterCount_card, hSeats]
  · funext B
    rw [Gen.AC.Root.vote_pool_score_card, Gen.AC.Root.vote_pool_score_card]
    congr 1
    ext i
    simp only [Finset.mem_filter, hSeats, hEq i]
    cases ht : GridCO.equivocates rt i with
    | true => simp
    | false =>
      simp only [Bool.false_or]
      apply and_congr Iff.rfl
      rw [Gen.AC.Root.vote_pool_support_witness, Gen.AC.Root.vote_pool_support_witness]
      constructor
      · rintro ⟨o, ho, hi, hv⟩
        exact ⟨o, hSupportKeep ho, hi, (hResolution o ho B) ▸ hv⟩
      · rintro ⟨o, ho, hi, hv⟩
        have hs := (hSupportBack o ho i hi).resolve_right
          (by rw [hEq i, ht]; exact Bool.false_ne_true)
        exact ⟨o, hs, hi, (hResolution o hs B).symm ▸ hv⟩

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A duty read at a slot offset uses that exact store slot. -/
theorem pcsa_formation_read_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (s : Slot)
    (offset : Int) (nd : Node p) (hr : pcsa_postClock E rho x t = some nd)
    (hTime : t = 4 * p.Δ * (s : Int) + offset)
    (hOffset : 0 ≤ offset) (hOffsetLt : offset < 4 * p.Δ) : nd.st.slot p = s := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  subst nd
  change p.slotOf (clock p pre.st t).base.now = s
  rw [pcsa_clock_now, hTime]
  exact pcsa_slotOf_offset p s offset hOffset hOffsetLt

variable [Fintype V]

/-- The unique proposer read fixes the parent, PC and both carried vote lists. -/
theorem pcsa_formation_proposer_read_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src : Node p)
    (hr : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src) :
    N.erase.slot = s ∧
      N.erase.parent = getHead p src.st (proposerPC p src.st)
        (proposerVotes src.st s) (proposerSupport src.st s) ∧
      N.pc = proposerPC p src.st ∧
      N.raw = (proposerVotes src.st s).filterMap liftHead? ∧
      N.support = (proposerSupport src.st s).filterMap liftHead? := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst src
  have hTick := V2.D.Run.tickIdx?_spec hk
  obtain ⟨i, hi, hem⟩ := h.proposal.2
  have hik : i = k := (List.Nodup.getElem?_inj
    (List.getElem?_eq_some_iff.mp hi).1 h.base.valid.nodup).mp (hi.trans hTick.symm)
  subst i
  have hb := pcsa_emitted_parent E rho s N _ _ k hTick hem
  have hl := pcsa_formation_emitted_lists E rho s N _ _ k hTick hem
  exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2, hl⟩

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- An old accepted PC is held before the proposal or has a strict earlier handler. -/
theorem pcsa_formation_pc_receipt_before_proposal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (j : Nat) (x y : V) (t : Time) (C : PC p.n)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (ht : t ≤ SA.freezeTime p.toParams (s - 1))
    (hAccept : V2.D.Run.acceptsAt E rho j x (⟨.none, .pc C⟩ : Obj p) t) :
    (∃ A ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st.pcs,
      A.slot = C.slot ∧ A.target = C.target) ∨
      ∃ u, t ≤ u ∧ u < SA.proposalTime p.toParams s ∧
        ∃ k, V2.D.Run.handlesAt E rho k y (⟨.none, .pc C⟩ : Obj p) u := by
  by_cases hDone : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y)
      (⟨.none, .pc C⟩ : Obj p) = true
  · left
    change ((V2.D.Run.stateBefore E rho (j + 1) y).st.pcs.any
      (fun A => A.slot == C.slot && A.target == C.target)) = true at hDone
    obtain ⟨A, hA, hid⟩ := List.any_eq_true.mp hDone
    simp only [Bool.and_eq_true, beq_iff_eq] at hid
    obtain ⟨o, he, _⟩ := hAccept.1
    have hz : SA.freezeTime p.toParams (s - 1) < SA.proposalTime p.toParams s := by
      have hs0 : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
        exact_mod_cast Nat.sub_add_cancel (Nat.one_le_of_lt h.slotPos)
      have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      have hd : (0 : Int) < p.Δ := p.deltaPos
      change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ < 4 * p.Δ * (s : Int)
      rw [hs]
      nlinarith
    have hj : j < V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed he _).mpr
        (ht.trans_lt hz)
    have hm := pcsa_run_pcs_mono E rho h.frame h.base.noRestart y hy
      (j + 1) _ (Nat.succ_le_of_lt hj) hA
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hm
    exact ⟨A, hm, hid⟩
  · right
    exact pcsa_formation_old_pc_relay E rho s N ΔF h j x y t C hx hy ht hAccept
      (Bool.eq_false_iff.mpr hDone)

/-- An origin input supplies the generic frozen-PC receipt boundary.
FormationOrigins supplies it from the run at the actual early read. -/
theorem pcsa_formation_frozen_pc_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x y : V) (nd : Node p) (C : PC p.n)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hFrozen : C ∈ pcSnapshotAt nd.st (s - 1))
    (hFrozenPCOrigin : ∀ A ∈ pcSnapshotAt nd.st (s - 1),
      ∃ j t D, t ≤ SA.freezeTime p.toParams (s - 1) ∧
        D.slot = A.slot ∧ D.target = A.target ∧
        V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t) :
    (∃ A ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st.pcs,
      A.slot = C.slot ∧ A.target = C.target) ∨
      ∃ D u k, D.slot = C.slot ∧ D.target = C.target ∧
        u < SA.proposalTime p.toParams s ∧
        V2.D.Run.handlesAt E rho k y (⟨.none, .pc D⟩ : Obj p) u := by
  obtain ⟨j, t, D, ht, hs, hb, ha⟩ := hFrozenPCOrigin C hFrozen
  rcases pcsa_formation_pc_receipt_before_proposal E rho s N ΔF h j x y t D hx hy ht ha
      with hHeld | ⟨u, _, hu, k, hk⟩
  · left
    obtain ⟨A, hm, has, hab⟩ := hHeld
    exact ⟨A, hm, has.trans hs, hab.trans hb⟩
  · exact Or.inr ⟨D, u, k, hs, hb, hu, hk⟩
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

private theorem formation_view_base (p : Params) (st : State p.n) (pc : Option (PC p.n))
    (ha : ∀ C, pc = some C → frameActive p st C = true) :
    walkBase p st pc = (pc.map PC.target).getD (eraseFG (controls p st).Z) := by
  cases pc with
  | none => rfl
  | some C =>
    change (if frameActive p st C then C.target else _) = C.target
    rw [ite_eq_left (ha C rfl)]
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- F4 and retained root-mode receipt inputs give coverage of the proposal parent. -/
theorem pcsa_formation_parent_cover_of_retained_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.voteTime p.toParams s) = true)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hRawKeep : proposerVotes src.st s ⊆ headVotes p dst.st s)
    (hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hSupportKeep : proposerSupport src.st s ⊆ headSupport p dst.st s)
    (hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hResolution : ∀ o ∈ proposerSupport src.st s, ∀ B,
      Gen.AC.Root.voteSupports src.st.base.blocks B o =
        Gen.AC.Root.voteSupports dst.st.base.blocks B o)
    (hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)))
    (hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))) :
    Block.Preceq N.erase.parent (headVote p dst.st s) := by
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hsFrame := pcsa_formation_frame_read E rho h.frame _ _ src h.proposal.1 hSrc
  have htFrame := pcsa_formation_frame_read E rho h.frame y _ dst hy hDst
  have hbSrc := formation_view_base p src.st (proposerPC p src.st) (by
    intro C hC
    exact (List.mem_filter.mp (bestPC_mem _ C hC)).2)
  have hbDst := formation_view_base p dst.st (voterPC p dst.st s) (by
    intro C hC
    exact (List.mem_filter.mp (bestPC_mem _ C hC)).2)
  have hv := h.commonView y hy haw
  rw [pcsa_viewAt_def, hDst] at hv
  have hTarget : (voterPC p dst.st s).map PC.target = N.pc.map PC.target :=
    Option.some.inj hv
  have hBase : walkBase p src.st (proposerPC p src.st) =
      walkBase p dst.st (voterPC p dst.st s) := by
    rw [hbSrc, hbDst, ← hInputs.2.2.1, hTarget, hsFrame.2.1, htFrame.2.1]
  have hReach := h.proposerRootReachable src hSrc
  change Block.Preceq (liveRoot p src.st (proposerPC p src.st))
    (GridCO.ghost (((proposerPC p src.st).map PC.target).getD (eraseFG (controls p src.st).Z))
      (erasedList src.st (fullTree p src.st))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))) at hReach
  rw [← hbSrc] at hReach
  have hScores := (pcsa_formation_root_merge_counts p src.st dst.st
    (proposerVotes src.st s) (proposerSupport src.st s) (headVotes p dst.st s)
    (headSupport p dst.st s) hRawKeep hRawBack hSupportKeep hSupportBack hResolution).2
  have hCover := pcsa_formation_parent_covers_of_inputs p src.st dst.st
    (proposerPC p src.st) (voterPC p dst.st s) _ _
    (proposerVotes src.st s) (proposerSupport src.st s)
    (headVotes p dst.st s) (headSupport p dst.st s) N.erase.parent rfl
    (pcsa_formation_read_root_injective E rho h.base _ _ src h.proposal.1 hSrc (fullTree p src.st))
    (pcsa_formation_read_root_injective E rho h.base y _ dst hy hDst
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)))
    hReach hInputs.2.1.symm hBase
    (pcsa_formation_voter_root_below_parent E rho s N ΔF h y dst hy haw hDst)
    hKeep hReflect (by
      intro X C _ _ _ _ _
      exact (congrFun hScores C).symm)
  change Block.Preceq N.erase.parent (if s = 0 then Block.genesis else _)
  rw [ite_eq_right (Nat.ne_of_gt h.slotPos)]
  exact hCover
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Retained receipt inputs and the terminal child facts give the exact honest HEAD. -/
theorem pcsa_formation_head_exact_of_retained_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.voteTime p.toParams s) = true)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hRawKeep : proposerVotes src.st s ⊆ headVotes p dst.st s)
    (hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hSupportKeep : proposerSupport src.st s ⊆ headSupport p dst.st s)
    (hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hResolution : ∀ o ∈ proposerSupport src.st s, ∀ B,
      Gen.AC.Root.voteSupports src.st.base.blocks B o =
        Gen.AC.Root.voteSupports dst.st.base.blocks B o)
    (hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)))
    (hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)))
    (hChild : N.erase ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)))
    (hUnique : ∀ B ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
      B.parent? = some N.erase.parent →
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
      B = N.erase)
    (hStop : Gen.Pure.NoEligibleChild
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)) N.erase) :
    headVote p dst.st s = N.erase := by
  have hCover := pcsa_formation_parent_cover_of_retained_inputs E rho s N ΔF h
    src dst y hSrc hy haw hDst hRawKeep hRawBack hSupportKeep hSupportBack
    hResolution hKeep hReflect
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hSlot : dst.st.slot p = s := pcsa_formation_read_slot E rho y _ s p.Δ dst hDst
    rfl (le_of_lt p.deltaPos) (by have hd : (0 : Int) < p.Δ := p.deltaPos; omega)
  have hParent : N.erase.parent? = some N.erase.parent := by
    cases N with
    | genesis =>
      have hs : 0 = s := hInputs.1
      exact ((Nat.ne_of_gt h.slotPos) hs.symm).elim
    | node P slot root body raw support rows pc => rfl
  exact pcsa_formation_headVote_exact_of_parent p dst.st s N.erase (Nat.ne_of_gt h.slotPos)
    (pcsa_formation_voter_root_below_parent E rho s N ΔF h y dst hy haw hDst) hCover
    (pcsa_formation_read_root_injective E rho h.base y _ dst hy hDst
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)))
    hParent hChild (hInputs.1.trans hSlot.symm) hUnique hStop

end AvailableChain.PCSA.Run

end
