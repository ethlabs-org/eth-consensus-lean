module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody
public import AvailableChainPCSAProofs.Proofs.Foundations.Proposals

public section

/-! C6 proposal-pool provenance and the exact admission tests. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem proposals_normalize (st : State n) :
    (normalizeS st).proposals = st.proposals := by
  delta normalizeS
  split <;> rfl
private theorem proposals_reconcile (st : State n) :
    (reconcile st).proposals = st.proposals := by
  delta reconcile
  rw [proposals_normalize]
private theorem proposals_collect (st : State n) :
    (collectPCs st).proposals = st.proposals := by
  apply collectPCs_preserves State.proposals
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem proposals_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
private theorem proposals_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
private theorem proposals_gate (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).proposals = st.proposals := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State n => acc.proposals = st.proposals)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.proposals = st.proposals)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- A proposal delivery adds only the named wire that passed all admission tests. -/
theorem pcsa_process_proposal_pred (p : Params) (Q : Wire p.n → Prop)
    (st : State p.n) (o : Wire p.n) (h : ∀ w ∈ st.proposals, Q w)
    (ho : ∀ s N P, o.decode = some (.block s N) → namedParentHeld st N = true →
      parentFG st N.erase = some P → blockAccepted p st s N P = true →
      Q ⟨.proposer s, .proposal N⟩) :
    ∀ w ∈ (process p st o).proposals, Q w := by
  have ha (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).proposals = st.proposals := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.proposals = st.proposals)
    · rfl
    · intro acc hh a _
      exact (proposals_raw acc a).trans hh
  have hr (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).proposals = st.proposals := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.proposals = st.proposals)
    · rfl
    · intro acc hh a _
      exact (proposals_row p acc a).trans hh
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact h
    | row i body => rw [proposals_row]; exact h
    | ack s i r =>
      change ∀ w ∈ (collectPCs (poolAck p st _)).proposals, Q w
      rw [proposals_collect]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [proposals_collect, ha]
        exact h
      · exact h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · rename_i hn
        have hn' : namedParentHeld st N = true := by
          cases ht : namedParentHeld st N <;> simp_all
        cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · rename_i hb
            rw [hr, proposals_collect, ha]
            have hq : ∀ w ∈ st.proposals ++ [⟨.proposer s, .proposal N⟩], Q w := by
              intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · exact h w hw
              · obtain rfl := List.mem_singleton.mp hw
                exact ho s N P hd hn' hp hb
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact hq
              | (rw [proposals_reconcile]; exact hq)
          · exact h
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Each stored proposal has an earlier delivery with the exact handler checks. -/
theorem pcsa_proposal_receipt_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (w : Wire p.n)
    (hm : w ∈ (V2.D.Run.stateBefore E rho k x).st.proposals) :
    ∃ j < k, ∃ (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
      (P : SimplexFG.FGBlock (Fin p.n)),
      rho.events[j]? = some (.deliver x o t) ∧
      (toWire p o).decode = some (.block s N) ∧ w = ⟨.proposer s, .proposal N⟩ ∧
      namedParentHeld (V2.D.Run.stateBefore E rho j x).st N = true ∧
      parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true := by
  induction k with
  | zero => exact (List.not_mem_nil hm).elim
  | succ k ih =>
    by_cases hold : w ∈ (V2.D.Run.stateBefore E rho k x).st.proposals
    · obtain ⟨j, hj, rest⟩ := ih hold
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    · cases hk : rho.events[k]? with
      | none =>
        have he : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
          delta V2.D.Run.stateBefore
          rw [List.take_add_one, hk]
          simp only [Option.toList_none, List.append_nil]
        exact (hold (he ▸ hm)).elim
      | some e =>
        rw [V2.D.Run.stateBefore_succ E rho hk] at hm
        by_cases hx : e.node = x
        · cases e with
          | restart y t =>
            change y = x at hx
            subst y
            change w ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.proposals at hm
            rw [Function.update_self] at hm
            exact (List.not_mem_nil hm).elim
          | tick y t =>
            change y = x at hx
            subst y
            change w ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.proposals at hm
            rw [Function.update_self] at hm
            have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
            rw [ht, pcsa_clock_proposals] at hm
            exact (hold hm).elim
          | deliver y o t =>
            change y = x at hx
            subst y
            change w ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.proposals at hm
            rw [Function.update_self] at hm
            have ho := pcsa_process_proposal_pred p
              (fun w => w ∈ (V2.D.Run.stateBefore E rho k x).st.proposals ∨
                ∃ s N P, (toWire p o).decode = some (.block s N) ∧
                  w = ⟨.proposer s, .proposal N⟩ ∧
                  namedParentHeld (V2.D.Run.stateBefore E rho k x).st N = true ∧
                  parentFG (V2.D.Run.stateBefore E rho k x).st N.erase = some P ∧
                  blockAccepted p (V2.D.Run.stateBefore E rho k x).st s N P = true)
              _ (toWire p o) (fun _ h => Or.inl h)
              (fun s N P hd hn hp hb => Or.inr ⟨s, N, P, hd, rfl, hn, hp, hb⟩) w hm
            obtain ⟨s, N, P, hd, hw, hn, hp, hb⟩ := ho.resolve_left hold
            exact ⟨k, Nat.lt_succ_self k, t, o, s, N, P, hk, hd, hw, hn, hp, hb⟩
        · have he := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hx
          exact (hold (he ▸ hm)).elim

private theorem proposal_decoded_wire (o : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (h : o.decode = some (.block s N)) : o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at h <;> cases h
  | proposer k =>
    cases payload <;> delta Wire.decode at h <;> cases h
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at h <;> cases h
/-- Every proposal in the indexed pool passed the wire check at its delivery. -/
theorem pcsa_proposal_pool_wellFormed (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.DeliveryWellFormed E rho)
    (k : Nat) (x : V) (w : Wire p.n)
    (hm : w ∈ (V2.D.Run.stateBefore E rho k x).st.proposals) :
    wellFormed p w = true := by
  obtain ⟨j, _, t, o, s, N, _, he, hd, hw, _⟩ :=
    pcsa_proposal_receipt_origin E rho k x w hm
  have h := hv.wire j x o t he
  change wellFormed p (toWire p o) = true at h
  rw [proposal_decoded_wire _ s N hd, ← hw] at h
  exact h
/-- Declared support in a stored proposal is a subset of its raw HEADs. -/
theorem pcsa_proposal_support_raw (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.DeliveryWellFormed E rho)
    (k : Nat) (x : V) (s : Slot) (N : NamedProposal p.n)
    (hm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k x).st.proposals) : N.support ⊆ N.raw := by
  have hw := pcsa_proposal_pool_wellFormed E rho hv k x _ hm
  change (N.erase != .genesis && s == N.erase.slot &&
    decide (N.erase.parent.slot < N.erase.slot) &&
    N.raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == N.erase.slot
      | none => false) &&
    N.support.all (fun v => decide (v ∈ N.raw)) && _ && _ && _) = true at hw
  have h8 := (Bool.and_eq_true_iff.mp hw).1
  have h7 := (Bool.and_eq_true_iff.mp h8).1
  have h6 := (Bool.and_eq_true_iff.mp h7).1
  have hs := (Bool.and_eq_true_iff.mp h6).2
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp hs a ha)
/-- Each raw HEAD in a stored proposal has the proposal's preceding label. -/
theorem pcsa_proposal_raw_label (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.DeliveryWellFormed E rho)
    (k : Nat) (x : V) (s : Slot) (N : NamedProposal p.n)
    (hm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k x).st.proposals) (a : HeadWire p.n) (ha : a ∈ N.raw) :
    ∃ r i b, a.decode? = some (r, i, b) ∧ r + 1 = N.erase.slot := by
  have hw := pcsa_proposal_pool_wellFormed E rho hv k x _ hm
  change (N.erase != .genesis && s == N.erase.slot &&
    decide (N.erase.parent.slot < N.erase.slot) &&
    N.raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == N.erase.slot
      | none => false) && _ && _ && _ && _) = true at hw
  have h8 := (Bool.and_eq_true_iff.mp hw).1
  have h7 := (Bool.and_eq_true_iff.mp h8).1
  have h6 := (Bool.and_eq_true_iff.mp h7).1
  have h5 := (Bool.and_eq_true_iff.mp h6).1
  have hr := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h5).2 a ha
  cases hd : a.decode? with
  | none => rw [hd] at hr; cases hr
  | some v =>
    rcases v with ⟨r, i, b⟩
    rw [hd] at hr
    exact ⟨r, i, b, rfl, beq_iff_eq.mp hr⟩

/-- A carried raw HEAD had a handler at the proposal's earlier accepting delivery. -/
theorem pcsa_proposal_raw_handled (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (s : Slot) (N : NamedProposal p.n)
    (hm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k x).st.proposals) (a : HeadWire p.n) (ha : a ∈ N.raw) :
    ∃ j < k, ∃ t, V2.D.Run.handlesAt E rho j x (ofHead p a) t := by
  obtain ⟨j, hj, t, o, s', N', P, he, hd, hw, hn, hp, hb⟩ :=
    pcsa_proposal_receipt_origin E rho k x _ hm
  have hN : N = N' := Msg.proposal.inj (congrArg (fun w : Wire p.n => w.payload) hw)
  subst N'
  refine ⟨j, hj, t, o, he, ?_⟩
  change handlesS p (V2.D.Run.stateBefore E rho j x).st o (ofHead p a)
  right
  left
  rw [hd]
  exact ⟨⟨hn, P, hp, hb⟩, Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)⟩
end AvailableChain.PCSA.Run

end
