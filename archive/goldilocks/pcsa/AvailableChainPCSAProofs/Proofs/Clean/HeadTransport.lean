module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadReceipt

public section

/-! C6 actual HEAD admission and receipt transport into late denominators. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem head_grid (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (i : Fin n) (r : BlockId)
    (hlo : (v.now / (4 * q.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (v.now / (4 * q.Δ)).toNat) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire n .root) ∈
        (GridCO.admitVote q v ⟨.seat s i, .head r⟩).votes ∨
      GridCO.equivocates (GridCO.votesAt
        (GridCO.admitVote q v ⟨.seat s i, .head r⟩) s) i = true := by
  delta GridCO.admitVote
  dsimp only
  by_cases hc : GridCO.equivocates (GridCO.votesAt v s) i = true
  · simp only [hc, Bool.or_true, ite_true]
    exact Or.inr trivial
  · by_cases hm : (⟨.seat s i, .head r⟩ : GridCO.Wire n .root) ∈ v.votes
    · simp only [hm, decide_true, Bool.or_true, Bool.true_or, ite_true]
      exact Or.inl trivial
    · have hlo' : ¬s < (v.now / (4 * q.Δ)).toNat - 1 := Nat.not_lt.mpr hlo
      have hhi' : ¬(v.now / (4 * q.Δ)).toNat < s := Nat.not_lt.mpr hhi
      simp only [hlo', hhi', decide_false, Bool.false_or, hm, hc,
        Bool.false_eq_true, ite_false]
      exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
private theorem head_fold (p : Params) (raw : List (HeadWire p.n))
    (v : GridCO.State p.n .root) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hlo : (v.now / (4 * p.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (v.now / (4 * p.Δ)).toNat)
    (ho : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ raw.map baseVote) :
    let post := (raw.map baseHead).foldl
      (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row)) v
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ post.votes ∨
      GridCO.equivocates (GridCO.votesAt post s) i = true := by
  induction raw generalizing v with
  | nil => cases ho
  | cons a raw ih =>
    dsimp only
    rw [List.map_cons, List.foldl_cons]
    rcases List.mem_cons.mp ho with he | ho
    · have h := head_grid p.toParams.engine v s i r hlo hhi
      rw [he] at h
      rcases h with hm | hc
      · rw [he]
        exact Or.inl (FGSA.Run.Internal.grid_fold_votes_subset (raw.map baseHead) _ hm)
      · exact Or.inr (FGSA.Run.Internal.grid_equivocates_mono _ _ i
          (FGSA.Run.Internal.grid_votesAt_subset _ _ s
            (FGSA.Run.Internal.grid_fold_votes_subset (raw.map baseHead) _)) hc)
    · exact ih _ (by simpa only [FGSA.Run.Internal.grid_admitVote_now] using hlo)
        (by simpa only [FGSA.Run.Internal.grid_admitVote_now] using hhi) ho
private theorem head_proposal (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hp : parentFG st N.erase = some P) (ha : blockAccepted p st s N P = true)
    (j : Slot) (i : Fin p.n) (r : BlockId)
    (hlo : st.slot p - 1 ≤ j) (hhi : j ≤ st.slot p)
    (ho : (⟨.seat j i, .head r⟩ : GridCO.Wire p.n .root) ∈ N.raw.map baseVote) :
    let v := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
    (⟨.seat j i, .head r⟩ : GridCO.Wire p.n .root) ∈ v.votes ∨
      GridCO.equivocates (GridCO.votesAt v j) i = true := by
  have hb : (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks =
      st.base.blocks ++ [N.erase] := (pcsa_body_insert_data p st s N P hTree hp ha).1
  dsimp only
  delta GridCO.admitProposal baseProposal at hb
  delta GridCO.admitProposal baseProposal
  dsimp only at hb ⊢
  split at hb
  · rename_i hg
    have hlen := congrArg List.length hb
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  · rename_i hg
    rw [ite_eq_right hg]
    exact head_fold p N.raw _ j i r hlo hhi ho
private theorem head_norm (st : State n) : (normalizeS st).base.votes = st.base.votes := by
  delta normalizeS
  split <;> rfl
private theorem head_reconcile (st : State n) : (reconcile st).base.votes = st.base.votes := by
  delta reconcile
  rw [head_norm]
private theorem head_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.votes = st.base.votes := by
  delta admitRow
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem head_collect (st : State n) : (collectPCs st).base.votes = st.base.votes := by
  apply collectPCs_preserves (fun st => st.base.votes)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem head_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.votes = st.base.votes := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem head_admitBlock_votes (p : Params) (st : State p.n)
    (s : Slot) (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (hn : namedParentHeld st N = true) (hp : parentFG st N.erase = some P)
    (ha : blockAccepted p st s N P = true) :
    (admitBlock p st s N).base.votes =
      (GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).votes := by
  have ha' (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).base.votes = st.base.votes := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.votes = st.base.votes)
    · rfl
    · intro acc h a _
      rw [head_raw]
      exact h
  have hr (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).base.votes = st.base.votes := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.votes = st.base.votes)
    · rfl
    · intro acc h a _
      rw [head_row]
      exact h
  delta admitBlock
  cases hnamed : namedParentHeld st N with
  | false => rw [hnamed] at hn; contradiction
  | true =>
    dsimp only
    cases hparent : parentFG st N.erase with
    | none => rw [hparent] at hp; contradiction
    | some Q =>
      have he : Q = P := Option.some.inj (hparent.symm.trans hp)
      subst Q
      dsimp only
      cases hacc : blockAccepted p st s N P with
      | false => rw [hacc] at ha; contradiction
      | true =>
        change (N.rows.foldl (admitRow p)
          (collectPCs (N.pcAcks.foldl poolAckRaw _))).base.votes = _
        rw [hr, head_collect, ha']
        cases N.pc <;> dsimp only
        all_goals split_ifs <;> first | rfl | (rw [head_reconcile] <;> rfl)
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem head_wire_exact (a : HeadWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : ofHead p a = (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p)) :
    baseVote a = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) := by
  have he : (⟨a.auth, .head a.payload⟩ : Wire p.n) = ⟨.seat (.head s) i, .head r⟩ :=
    (toWireEquiv p).symm.injective h
  have ha := congrArg (fun w : Wire p.n => w.auth) he
  have hr := Msg.head.inj (congrArg (fun w : Wire p.n => w.payload) he)
  cases a
  cases ha
  cases hr
  rfl
/-- Within its receipt window, a handled HEAD leaves its exact copy or a capped seat. -/
theorem pcsa_handled_head_mem_or_cap (st : State p.n) (parent : Obj p)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hlo : st.slot p - 1 ≤ s) (hhi : s ≤ st.slot p)
    (hh : handlesS p st parent (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (process p st (toWire p parent)).base.votes ∨
      GridCO.equivocates (GridCO.votesAt (process p st (toWire p parent)).base s) i = true := by
  rcases hh with he | hh | hh
  · subst parent
    exact head_grid p.toParams.engine st.base s i r hlo hhi
  · cases hd : (toWire p parent).decode with
    | none => rw [hd] at hh; exact hh.elim
    | some msg => cases msg with
      | vote j a root => rw [hd] at hh; exact hh.elim
      | row a body => rw [hd] at hh; exact hh.elim
      | ack j a root => rw [hd] at hh; exact hh.elim
      | pc C =>
        rw [hd] at hh
        obtain ⟨a, _, he⟩ := List.mem_map.mp hh
        have he' := congrArg (fun o : Obj p => o.payload) he
        cases he'
      | block j N =>
        rw [hd] at hh
        obtain ⟨⟨hn, P, hp, ha⟩, hh⟩ := hh
        rcases hh with hh | hh | hh
        · obtain ⟨a, ham, he⟩ := List.mem_map.mp hh
          have hraw : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ N.raw.map baseVote :=
            List.mem_map.mpr ⟨a, ham, head_wire_exact a s i r he⟩
          delta process
          rw [hd]
          dsimp only
          change _ ∈ (admitBlock p st j N).base.votes ∨
            GridCO.equivocates ((admitBlock p st j N).base.votes.filter
              (fun o => GridCO.headLabel? o == some s)) i = true
          rw [head_admitBlock_votes p st j N P hn hp ha]
          exact head_proposal p st j N P hTree hp ha s i r hlo hhi hraw
        · obtain ⟨a, _, he⟩ := List.mem_map.mp hh
          have he' := congrArg (fun o : Obj p => o.payload) he
          cases he'
        · obtain ⟨a, _, he⟩ := List.mem_map.mp hh
          have he' := congrArg (fun o : Obj p => o.payload) he
          cases he'
  · obtain ⟨_, C, he, _, _⟩ := hh
    have hp := congrArg (fun o : Obj p => o.payload) he
    cases hp

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A HEAD receipt before its gate reads one of its two admissible store slots. -/
theorem pcsa_head_receipt_window (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (j : Nat) (y : V) (parent : Obj p) (t : Time) (s : Slot)
    (hj : rho.events[j]? = some (.deliver y parent t))
    (ht : GridCO.proposalTime p.toParams.engine s ≤ t) (hu : t < SA.gateTime p.toParams s) :
    (V2.D.Run.stateBefore E rho j y).st.slot p - 1 ≤ s ∧
      s ≤ (V2.D.Run.stateBefore E rho j y).st.slot p := by
  have hpub : V2.PublicTime E (GridCO.proposalTime p.toParams.engine s) := by
    refine ⟨4 * s, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ GridCO.proposalTime p.toParams.engine s := by
    have := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int)
    positivity
  have hn := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho
    h.valid.toScheduleWellFormed h.noRestart hj hpub hzero ht
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j y)] at hn
  have hb := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho
    h.valid.toScheduleWellFormed h.noRestart hj y
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j y)] at hb
  change (V2.D.Run.stateBefore E rho j y).st.base.now ≤ t at hb
  have hd := p.deltaPos
  have hlo : (s : Int) ≤ (V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ) := by
    apply (Int.le_ediv_iff_mul_le (by positivity)).mpr
    change 4 * p.Δ * (s : Int) ≤ _ at hn
    nlinarith
  have hhi : (V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ) < (s : Int) + 2 := by
    apply (Int.ediv_lt_iff_lt_mul (by positivity)).mpr
    change t < 4 * p.Δ * (s : Int) + 6 * p.Δ at hu
    nlinarith
  have hlow : s ≤ ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat := by
    exact_mod_cast (le_trans hlo (Int.self_le_toNat _))
  have hupp : ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat < s + 2 := by
    apply (Int.toNat_lt' (n := s + 2) (by omega)).mpr
    exact_mod_cast hhi
  change ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat - 1 ≤ s ∧
    s ≤ ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat
  exact ⟨by omega, hlow⟩
/-- An actual timely handler leaves the exact HEAD or equivocation evidence. -/
theorem pcsa_handled_head_stateBefore_mem_or_cap (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (j : Nat) (y : V) (t : Time) (s : Slot) (i : Fin p.n) (r : BlockId)
    (ht : GridCO.proposalTime p.toParams.engine s ≤ t) (hu : t < SA.gateTime p.toParams s)
    (hh : V2.D.Run.handlesAt E rho j y
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.base.votes ∨
      GridCO.equivocates (GridCO.votesAt
        (V2.D.Run.stateBefore E rho (j + 1) y).st.base s) i = true := by
  obtain ⟨parent, hj, hhandle⟩ := hh
  obtain ⟨hlo, hhi⟩ := pcsa_head_receipt_window E rho h j y parent t s hj ht hu
  have htree := pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho j y)
  have hp := pcsa_handled_head_mem_or_cap (V2.D.Run.stateBefore E rho j y).st
    parent s i r htree hlo hhi hhandle
  rw [V2.D.Run.stateBefore_succ E rho hj]
  change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.base.votes ∨
    GridCO.equivocates (GridCO.votesAt
      (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.base s) i = true
  rw [Function.update_self]
  exact hp
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem read_stamp_entry (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (o : GridCO.Wire p.n .root) (hm : o ∈ (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    (o, GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base o) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho k x o hm
  have he : row.1 = o := beq_iff_eq.mp
    (List.find?_some (p := fun r : GridCO.Wire p.n .root × Time => r.1 == o) hr)
  have hh := List.mem_of_find?_eq_some hr
  rcases row with ⟨a, t⟩
  dsimp only at he
  subst a
  delta GridCO.stampVote
  rw [hr]
  exact hh
/-- Every HEAD in an indexed read before a cutoff has a strictly earlier stamp. -/
theorem pcsa_head_stamp_lt_of_index_cut (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (k : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (cut : Time) (hk : k ≤ V2.D.Run.idxBefore rho cut)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base ⟨.seat s i, .head r⟩ < cut := by
  obtain ⟨j, hj, t, ha, he⟩ := pcsa_head_stamp_source E rho k x s i r _
    (read_stamp_entry E rho k x _ hm)
  obtain ⟨parent, hd, _⟩ := ha.1
  have ht : t < cut := (Gen.V2.Duty.index_lt_idxBefore_iff hS hd cut).mp (lt_of_lt_of_le hj hk)
  have hb := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho hS hn hd x
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hb
  change (V2.D.Run.stateBefore E rho j x).st.base.now ≤ t at hb
  rw [he]
  exact lt_of_le_of_lt hb ht
/-- A post-clock read keeps the strict stamp bound of the underlying pooled HEAD. -/
theorem pcsa_head_stamp_lt_at_clocked_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (k : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (cut u : Time) (hk : k ≤ V2.D.Run.idxBefore rho cut)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho k x).st u).base.votes) :
    GridCO.stampVote (actView (clock p (V2.D.Run.stateBefore E rho k x).st u))
      ⟨.seat s i, .head r⟩ < cut := by
  rw [pcsa_clock_heads] at hm
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho k x ⟨.seat s i, .head r⟩ hm
  have hp : (V2.D.Run.stateBefore E rho k x).st.base.voteStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)).voteStamp := by
    change _ <+: (clock p (V2.D.Run.stateBefore E rho k x).st u).base.voteStamp
    rw [pcsa_clock_headStamps]
  rw [pcsa_stampVote_eq_of_prefix _ _ ⟨.seat s i, .head r⟩ row hp hr]
  exact pcsa_head_stamp_lt_of_index_cut E rho hS hn k x s i r cut hk hm
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An exact pooled HEAD before a cutoff stays in every later clocked late denominator. -/
theorem pcsa_head_before_cut_mem_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (a b : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (cut u : Time) (hab : a ≤ b) (ha : a ≤ V2.D.Run.idxBefore rho cut)
    (hc : cut ≤ SA.gateTime p.toParams s)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho b x).st u)) s := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho a x ⟨.seat s i, .head r⟩ hm
  have hp : (V2.D.Run.stateBefore E rho a x).st.base.voteStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho b x).st u)).voteStamp := by
    change _ <+: (clock p (V2.D.Run.stateBefore E rho b x).st u).base.voteStamp
    rw [pcsa_clock_headStamps]
    exact pcsa_headStamps_stateBefore_prefix E rho hn x hab
  have hs := pcsa_stampVote_eq_of_prefix _ _ ⟨.seat s i, .head r⟩ row hp hr
  refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · change _ ∈ (clock p (V2.D.Run.stateBefore E rho b x).st u).base.votes
    rw [pcsa_clock_heads]
    exact pcsa_heads_stateBefore_mono E rho hn x hab hm
  · change (some s == some s) = true
    exact beq_self_eq_true _
  · change decide (GridCO.stampVote
      (actView (clock p (V2.D.Run.stateBefore E rho b x).st u))
      ⟨.seat s i, .head r⟩ < SA.gateTime p.toParams s) = true
    apply decide_eq_true
    rw [hs]
    exact lt_of_lt_of_le (pcsa_head_stamp_lt_of_index_cut E rho hS hn a x s i r cut ha hm) hc
private theorem late_head_shape (o : GridCO.Wire p.n .root) (s : Slot) (i : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hi : GridCO.headSeat? o = some i) :
    ∃ r, o = ⟨.seat s i, .head r⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;>
    (delta GridCO.headLabel? GridCO.headSeat? at hl hi; cases hl <;> cases hi)
  exact ⟨_, rfl⟩
/-- Both witnesses of a capped seat before a cutoff stay in the later late denominator. -/
theorem pcsa_cap_before_cut_mem_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (a b : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (cut u : Time) (hab : a ≤ b) (ha : a ≤ V2.D.Run.idxBefore rho cut)
    (hc : cut ≤ SA.gateTime p.toParams s)
    (he : GridCO.equivocates (GridCO.votesAt (V2.D.Run.stateBefore E rho a x).st.base s) i = true) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho b x).st u)) s) i = true := by
  obtain ⟨v, hv, w, hw, hne, hvi, hwi⟩ := (Gen.AC.Root.cap_pair _ i).mp he
  have hvl : GridCO.headLabel? v = some s := beq_iff_eq.mp (List.mem_filter.mp hv).2
  have hwl : GridCO.headLabel? w = some s := beq_iff_eq.mp (List.mem_filter.mp hw).2
  obtain ⟨r, rfl⟩ := late_head_shape v s i hvl hvi
  obtain ⟨r', rfl⟩ := late_head_shape w s i hwl hwi
  apply (Gen.AC.Root.cap_pair _ i).mpr
  exact ⟨_, pcsa_head_before_cut_mem_late E rho hS hn a b x s i r cut u hab ha hc
      (List.mem_filter.mp hv).1,
    _, pcsa_head_before_cut_mem_late E rho hS hn a b x s i r' cut u hab ha hc
      (List.mem_filter.mp hw).1, hne, hvi, hwi⟩
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A timely handler supplies the exact HEAD or a capped seat to the later late pool. -/
theorem pcsa_handled_head_late_or_cap (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (j k : Nat) (x : V) (t cut u : Time) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hj : j + 1 ≤ k) (ht : GridCO.proposalTime p.toParams.engine s ≤ t)
    (hc : t < cut) (hcut : cut ≤ SA.gateTime p.toParams s)
    (hh : V2.D.Run.handlesAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) s) i = true := by
  have hresult := pcsa_handled_head_stateBefore_mem_or_cap E rho h j x t s i r ht
    (lt_of_lt_of_le hc hcut) hh
  obtain ⟨parent, hparent, _⟩ := hh
  have hidx : j + 1 ≤ V2.D.Run.idxBefore rho cut := Nat.succ_le_of_lt
    ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hparent cut).mpr hc)
  rcases hresult with hm | he
  · exact Or.inl (pcsa_head_before_cut_mem_late E rho h.valid.toScheduleWellFormed
      h.noRestart (j + 1) k x s i r cut u hj hidx hcut hm)
  · exact Or.inr (pcsa_cap_before_cut_mem_late E rho h.valid.toScheduleWellFormed
      h.noRestart (j + 1) k x s i cut u hj hidx hcut he)
end AvailableChain.PCSA.Run
end
