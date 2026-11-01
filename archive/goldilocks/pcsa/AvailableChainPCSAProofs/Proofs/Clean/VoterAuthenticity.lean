module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs

public section

/-! C6 VoterAuthenticity: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- Every raw voter input has the preceding HEAD label. -/
theorem pcsa_headVotes_label (p : Params) (st : State p.n) (s : Slot)
    (o : GridCO.Wire p.n .root) (ho : o ∈ headVotes p st s) :
    GridCO.headLabel? o = some (s - 1) := by
  delta headVotes at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hf | hc
  · exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hf).1).2
  · exact beq_iff_eq.mp (List.mem_filter.mp hc).2
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem voter_baseVote_exact (a : HeadWire p.n) (s : Slot) (i : Fin p.n)
    (r : BlockId) (he : baseVote a = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root)) :
    a = ⟨.seat (.head s) i, r⟩ := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases he
  | proposer t => cases he
  | seat l j =>
    cases l <;> delta baseVote baseHead HeadWire.decode? GridCO.fromHead at he <;> cases he
    rfl
private theorem voter_proposal_wire (w : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (hd : w.decode = some (.block s N)) : w = ⟨.proposer s, .proposal N⟩ := by
  rcases w with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at hd <;> cases hd
  | proposer t =>
    cases payload <;> delta Wire.decode at hd <;> cases hd
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at hd <;> cases hd
/-- Every raw voter HEAD of an honest seat has an exact signed emission. -/
theorem pcsa_voter_input_emission (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hU : V2.D.UnforgeableSignatures E rho)
    (k : Nat) (x : V) (t : Time) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      headVotes p (clock p (V2.D.Run.stateBefore E rho k x).st t) (s + 1)) :
    ∃ u, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) i)
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) u := by
  rcases pcsa_headVotes_mem p _ (s + 1) _ hm with hf | ⟨w, hw, q, N, a, hd, _, ha, he, _⟩
  · have hp := (List.mem_filter.mp hf.1).1
    change (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ (clock p _ t).base.votes at hp
    rw [pcsa_clock_heads] at hp
    exact pcsa_pool_head_emission E rho hU k x s i r hi hp
  · obtain rfl := voter_baseVote_exact a s i r he
    rw [pcsa_clock_proposals] at hw
    rw [voter_proposal_wire w q N hd] at hw
    obtain ⟨j, _, u, parent, hj, hh⟩ := pcsa_proposal_raw_handled E rho k x q N hw _ ha
    change handlesS p (V2.D.Run.stateBefore E rho j x).st parent
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) at hh
    rcases pcsa_handles_carried _ parent _ hh with hdir | hcar
    · rw [← hdir] at hj
      obtain ⟨u', _, hemit⟩ := hU.unforgeable x _ u ⟨j, hj⟩ _ hi rfl
      exact ⟨u', hemit⟩
    · obtain ⟨u', _, hemit⟩ := hU.carried x parent u ⟨j, hj⟩ _ hcar _ hi rfl
      exact ⟨u', hemit⟩
/-- Honest seats cannot be capped in a voter input list, without any healthy-cut premise. -/
theorem pcsa_voter_honest_not_capped_unconditional (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (x : V) (t : Time) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k x).st t) (s + 1)) i =
      false := by
  apply Bool.eq_false_iff.mpr
  intro hcap
  obtain ⟨o, ho, o', ho', hne, hoi, ho'i⟩ := (Gen.AC.Root.cap_pair _ i).mp hcap
  have hl := pcsa_headVotes_label p _ (s + 1) o ho
  have hl' := pcsa_headVotes_label p _ (s + 1) o' ho'
  rw [Nat.add_sub_cancel] at hl hl'
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
  obtain ⟨r', rfl⟩ := pcsa_count_head_shape o' s i hl' ho'i
  obtain ⟨u, a, ha, hma⟩ := pcsa_voter_input_emission E rho hv.toUnforgeableSignatures k x t s i r
    hi ho
  obtain ⟨v, b, hb, hmb⟩ := pcsa_voter_input_emission E rho hv.toUnforgeableSignatures k x t s i
    r' hi ho'
  have heq := (Gen.V2.Duty.emitted_unique_of_singleDuty E rho hv.nodup (.base (.head s))
    (pcsa_head_single_duty p c m s) i _ a b u v _ _ ha hb hma hmb rfl rfl).2
  have hr : r = r' := Msg.head.inj (congrArg (fun o : Obj p => o.payload) heq)
  subst r'
  exact hne rfl
end AvailableChain.PCSA.Run

end
