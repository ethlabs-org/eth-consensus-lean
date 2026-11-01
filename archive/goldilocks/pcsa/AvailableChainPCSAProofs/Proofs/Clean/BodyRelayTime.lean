module
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps

public section

/-! C6 exact body stamp origin, cutoff acceptance, and timed receiver relay. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem body_grid_vote_stamp (v : GridCO.State p.n .root)
    (o : GridCO.Wire p.n .root) :
    (GridCO.admitVote p.toParams.engine v o).blockStamp = v.blockStamp := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem body_grid_stamp_origin (v : GridCO.State p.n .root)
    (o : GridCO.Wire p.n .root) (B : Block) (raw : List (GridCO.HeadWire p.n .root))
    (X : Block) (stamp : Time)
    (hm : (X, stamp) ∈ (GridCO.admitProposal p.toParams.engine v o B raw).blockStamp) :
    (X, stamp) ∈ v.blockStamp ∨ X = B ∧ stamp = v.now := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> delta GridCO.admitProposal at hm <;> dsimp only at hm <;> split at hm
  all_goals first
    | exact Or.inl hm
    | (rw [(FGSA.foldVotes_fields p.toParams.engine raw _).2.1] at hm
       rcases List.mem_append.mp hm with hm | hm
       · exact Or.inl hm
       · have he := List.mem_singleton.mp hm
         exact Or.inr ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩)
private theorem body_origin_norm (st : State p.n) :
    (normalizeS st).base.blockStamp = st.base.blockStamp := by
  delta normalizeS
  split <;> rfl
private theorem body_origin_reconcile (st : State p.n) :
    (reconcile st).base.blockStamp = st.base.blockStamp := by
  delta reconcile
  rw [body_origin_norm]
private theorem body_origin_row (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.blockStamp = st.base.blockStamp := by
  delta admitRow
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem body_origin_collect (st : State p.n) :
    (collectPCs st).base.blockStamp = st.base.blockStamp := by
  apply collectPCs_preserves (fun st => st.base.blockStamp)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem body_origin_raw (st : State p.n) (a : AckWire p.n) :
    (poolAckRaw st a).base.blockStamp = st.base.blockStamp := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
/-- A new body stamp identifies a direct proposal that passed its handler tests. -/
theorem pcsa_process_body_stamp_origin (st : State p.n) (parent : Obj p)
    (X : Block) (stamp : Time)
    (hm : (X, stamp) ∈ (process p st (toWire p parent)).base.blockStamp) :
    (X, stamp) ∈ st.base.blockStamp ∨
      ∃ s N P, (toWire p parent).decode = some (.block s N) ∧
        parentFG st N.erase = some P ∧ blockAccepted p st s N P = true ∧
        N.erase = X ∧ stamp = st.base.now := by
  have ha (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).base.blockStamp = st.base.blockStamp := by
    apply List.foldlRecOn
      (motive := fun acc : State p.n => acc.base.blockStamp = st.base.blockStamp)
    · rfl
    · intro acc hh a _
      rw [body_origin_raw]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).base.blockStamp = st.base.blockStamp := by
    apply List.foldlRecOn
      (motive := fun acc : State p.n => acc.base.blockStamp = st.base.blockStamp)
    · rfl
    · intro acc hh a _
      rw [body_origin_row]
      exact hh
  delta process at hm
  cases hd : (toWire p parent).decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some msg =>
    rw [hd] at hm
    cases msg with
    | vote s i r =>
      change _ ∈ (GridCO.admitVote p.toParams.engine st.base
        ⟨.seat s i, .head r⟩).blockStamp at hm
      rw [body_grid_vote_stamp] at hm
      exact Or.inl hm
    | row i body => rw [body_origin_row] at hm; exact Or.inl hm
    | ack s i r =>
      change _ ∈ (collectPCs (poolAck p st
        (⟨(toWire p parent).auth, r⟩ : AckWire p.n))).base.blockStamp at hm
      rw [body_origin_collect] at hm
      delta poolAck at hm
      cases hd' : AckWire.decode? (⟨(toWire p parent).auth, r⟩ : AckWire p.n) with
      | none => rw [hd'] at hm; exact Or.inl hm
      | some a =>
        rw [hd'] at hm
        rcases a with ⟨_, _, _⟩
        dsimp only at hm
        split at hm
        · exact Or.inl hm
        · split at hm <;> exact Or.inl hm
    | pc C =>
      dsimp only at hm
      delta admitPC at hm
      split at hm
      · rw [body_origin_collect, ha] at hm; exact Or.inl hm
      · exact Or.inl hm
    | block s N =>
      dsimp only at hm
      delta admitBlock at hm
      cases hn : namedParentHeld st N with
      | false => rw [hn] at hm; exact Or.inl hm
      | true =>
        rw [hn] at hm
        change _ ∈ (match parentFG st N.erase with
          | none => st
          | some P => if blockAccepted p st s N P then _ else st).base.blockStamp at hm
        generalize hp : parentFG st N.erase = parent at hm
        cases parent with
        | none => exact Or.inl hm
        | some P =>
          dsimp only at hm
          split at hm
          · rename_i hacc
            rw [hr, body_origin_collect, ha] at hm
            have hbase : (X, stamp) ∈
                (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s N.erase N.raw N.support) N.erase
                  (N.raw.map baseHead)).blockStamp := by
              generalize hc : N.pc = pc at hm
              cases pc <;> dsimp only at hm
              all_goals split_ifs at hm <;> first
                | exact hm
                | (rw [body_origin_reconcile] at hm; exact hm)
            rcases body_grid_stamp_origin st.base _ N.erase _ X stamp hbase with hm | ⟨hx, ht⟩
            · exact Or.inl hm
            · exact Or.inr ⟨s, N, P, rfl, hp, hacc, hx.symm, ht⟩
          · exact Or.inl hm
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A non-genesis body stamp has an earlier direct delivery that passed admission. -/
theorem pcsa_body_stamp_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (B : Block) (stamp : Time) (hg : B ≠ .genesis)
    (hm : (B, stamp) ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp) :
    ∃ j < k, ∃ t parent s N P,
      rho.events[j]? = some (.deliver x parent t) ∧
      (toWire p parent).decode = some (.block s N) ∧ N.erase = B ∧
      parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true ∧
      stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
  induction k with
  | zero =>
    have hb : B = .genesis := congrArg Prod.fst (List.mem_singleton.mp hm)
    exact (hg hb).elim
  | succ k ih =>
    have carry (hm : (B, stamp) ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp) :
        ∃ j < k + 1, ∃ t parent s N P,
          rho.events[j]? = some (.deliver x parent t) ∧
          (toWire p parent).decode = some (.block s N) ∧ N.erase = B ∧
          parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
          blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true ∧
          stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
      obtain ⟨j, hj, rest⟩ := ih hm
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    cases he : rho.events[k]? with
    | none =>
      have hs : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      exact carry (hs ▸ hm)
    | some e =>
      rw [V2.D.Run.stateBefore_succ E rho he] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blockStamp at hm
          rw [Function.update_self] at hm
          have hb : B = .genesis := congrArg Prod.fst (List.mem_singleton.mp hm)
          exact (hg hb).elim
        | tick y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blockStamp at hm
          rw [Function.update_self] at hm
          have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
          rw [ht, pcsa_clock_bodyStamps] at hm
          exact carry hm
        | deliver y parent t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blockStamp at hm
          rw [Function.update_self] at hm
          rcases pcsa_process_body_stamp_origin _ parent B stamp hm with
            hm | ⟨s, N, P, hd, hp, ha, hb, ht⟩
          · exact carry hm
          · exact ⟨k, Nat.lt_succ_self k, t, parent, s, N, P, he, hd, hb, hp, ha, ht⟩
      · apply carry
        have hn := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hx
        rwa [hn] at hm
private theorem body_stamp_entry (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (B : Block)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    (B, GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base B) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.blockStamp := by
  obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho k x B hm
  have he : row.1 = B := beq_iff_eq.mp
    (List.find?_some (p := fun r : Block × Time => r.1 == B) hr)
  have hh := List.mem_of_find?_eq_some hr
  rcases row with ⟨A, t⟩
  dsimp only at he
  subst A
  delta GridCO.stampBlock
  rw [hr]
  exact hh
/-- An exact body stamp before a public cutoff gives a passed admission before it. -/
theorem pcsa_body_admitted_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (k : Nat) (x : V) (B : Block) (cut : Time)
    (hpub : V2.PublicTime E cut) (hzero : 0 ≤ cut) (hg : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks)
    (ht : GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base B < cut) :
    ∃ j < k, ∃ t parent s N P,
      rho.events[j]? = some (.deliver x parent t) ∧ t < cut ∧
      (toWire p parent).decode = some (.block s N) ∧ N.erase = B ∧
      parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true := by
  obtain ⟨j, hj, t, parent, s, N, P, he, hd, hb, hp, ha, hs⟩ :=
    pcsa_body_stamp_source E rho k x B _ hg (body_stamp_entry E rho k x B hm)
  refine ⟨j, hj, t, parent, s, N, P, he, ?_, hd, hb, hp, ha⟩
  by_contra hlate
  have hc := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS hn
    he hpub hzero (le_of_not_gt hlate)
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hc
  rw [hs] at ht
  exact (not_lt.mpr hc) ht
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem stamped_body_wire (o : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (hd : o.decode = some (.block s N)) : o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at hd <;> cases hd
  | proposer k =>
    cases payload <;> delta Wire.decode at hd <;> cases hd
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at hd <;> cases hd
private theorem stamped_body_object (parent : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p parent).decode = some (.block s N)) :
    parent = ofWire p ⟨.proposer s, .proposal N⟩ :=
  ((toWireEquiv p).left_inv parent).symm.trans
    (congrArg (ofWire p) (stamped_body_wire (toWire p parent) s N hd))
/-- A passed direct body handler is an actual fresh acceptance in a valid execution. -/
theorem pcsa_passed_body_accepts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (j : Nat) (x : V) (parent : Obj p) (t : Time) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (he : rho.events[j]? = some (.deliver x parent t))
    (hd : (toWire p parent).decode = some (.block s N))
    (hp : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P)
    (ha : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true) :
    V2.D.Run.acceptsAt E rho j x parent t := by
  have hobj := stamped_body_object parent s N hd
  have hdeps := hv.deps j x parent t he
  rw [hobj] at hdeps
  change (namedParentHeld (V2.D.Run.stateBefore E rho j x).st N && _) = true at hdeps
  have hbody := pcsa_admitBlock_body_mem p _ s N P
    (pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho j x))
    (Bool.and_eq_true_iff.mp hdeps).1 hp ha
  have hpost := V2.D.Run.stateBefore_succ E rho he
  have hm : N.erase ∈ (V2.D.Run.stateBefore E rho (j + 1) x).st.base.blocks := by
    rw [hpost]
    change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.blocks
    rw [Function.update_self]
    change _ ∈ (process p (V2.D.Run.stateBefore E rho j x).st (toWire p parent)).base.blocks
    delta process
    rw [hd]
    exact hbody
  refine ⟨⟨parent, he, Or.inl rfl⟩, hv.fresh j x parent t he, ?_⟩
  change processedS p (V2.D.Run.stateBefore E rho (j + 1) x).st parent = true
  delta processedS
  rw [hd]
  apply decide_eq_true
  obtain ⟨D, hD, hErase⟩ := (pcsa_tree_correspondence p _
    (pcsa_reachable_stateBefore E rho (j + 1) x) N.erase).mp hm
  have hr : (eraseFG D).root = D.root := by cases D <;> rfl
  have hn : N.erase.root = N.root := by cases N <;> rfl
  exact ⟨D, hD, hr.symm.trans (congrArg Block.root hErase |>.trans hn)⟩
/-- A non-genesis exact body stamped before a public cutoff was accepted before it. -/
theorem pcsa_body_accepted_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (B : Block) (cut : Time) (hpub : V2.PublicTime E cut)
    (hzero : 0 ≤ cut) (hg : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks)
    (ht : GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base B < cut) :
    ∃ j < k, ∃ t parent s N P,
      rho.events[j]? = some (.deliver x parent t) ∧ t < cut ∧
      (toWire p parent).decode = some (.block s N) ∧ N.erase = B ∧
      parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true ∧
      V2.D.Run.acceptsAt E rho j x parent t := by
  obtain ⟨j, hj, t, parent, s, N, P, he, htc, hd, hb, hp, ha⟩ :=
    pcsa_body_admitted_before E rho h.valid.toScheduleWellFormed h.noRestart
      k x B cut hpub hzero hg hm ht
  exact ⟨j, hj, t, parent, s, N, P, he, htc, hd, hb, hp, ha,
    pcsa_passed_body_accepts E rho h.valid j x parent t s N P he hd hp ha⟩
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
omit [DecidableEq V] in
private theorem pcsa_body_idx_mono (rho : V2.D.Run V (pcsaWith m p c)) {a b : Time}
    (hab : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hab))
/-- A held non-genesis body in a pre-cut indexed read has a strictly earlier first stamp. -/
theorem pcsa_body_stamp_lt_of_index_cut (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (k : Nat) (x : V) (B : Block) (cut : Time)
    (hk : k ≤ V2.D.Run.idxBefore rho cut) (hg : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBefore E rho k x).st.base B < cut := by
  obtain ⟨j, hj, t, parent, s, N, P, he, _, _, _, _, hs⟩ :=
    pcsa_body_stamp_source E rho k x B _ hg (body_stamp_entry E rho k x B hm)
  have ht : t < cut := (Gen.V2.Duty.index_lt_idxBefore_iff hS he cut).mp (lt_of_lt_of_le hj hk)
  have hc := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho hS hn he x
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hc
  change (V2.D.Run.stateBefore E rho j x).st.base.now ≤ t at hc
  rw [hs]
  exact lt_of_le_of_lt hc ht
/-- From the window floor, a body first stamped before a public cutoff is held and timely
at each later honest read. -/
theorem pcsa_body_before_public_cut_relay_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (B : Block) (bound : Time) (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hT : T₀ ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (hg : B ≠ .genesis) (hm : B ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks)
    (hs : GridCO.stampBlock (V2.D.Run.stateBefore E rho a x).st.base B < bound) :
    B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base B < bound + E.Δ := by
  obtain ⟨j, _, t, parent, s, N, P, he, ht, hd, hb, hp, ha, hacc⟩ :=
    pcsa_body_accepted_before E rho h a x B bound hpub hzero hg hm hs
  obtain ⟨dl, _, hdl, _, hrecv⟩ := pcsa_body_relay_from E rho h hF hD j x hx t parent s N P
    he hd hp ha hacc
  have hdeadline : dl ≤ bound + E.Δ :=
    hdl.trans (Int.add_le_add_right (max_le ht.le hT) E.Δ)
  have hmem := hrecv y hy (hdeadline.trans hc)
  rw [hb, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hmem
  have hidx : V2.D.Run.idxBefore rho dl ≤ k := (pcsa_body_idx_mono rho hdeadline).trans hk
  have hstamp := pcsa_body_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed
    h.noRestart _ y B dl (le_refl _) hg hmem
  have hlate := pcsa_body_stateBefore_mono E rho h.noRestart y hidx hmem
  refine ⟨hlate, ?_⟩
  rw [pcsa_body_stamp_stateBefore_eq E rho h.noRestart y hidx B hmem]
  exact lt_of_lt_of_le hstamp hdeadline
/-- A body first stamped before a public cutoff is held and timely at each later honest read. -/
theorem pcsa_body_before_public_cut_relay (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (B : Block) (bound : Time) (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (hg : B ≠ .genesis) (hm : B ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks)
    (hs : GridCO.stampBlock (V2.D.Run.stateBefore E rho a x).st.base B < bound) :
    B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base B < bound + E.Δ :=
  pcsa_body_before_public_cut_relay_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y
    hx hy B bound hpub hzero hzero hc hk hg hm hs
end AvailableChain.PCSA.Run

end
