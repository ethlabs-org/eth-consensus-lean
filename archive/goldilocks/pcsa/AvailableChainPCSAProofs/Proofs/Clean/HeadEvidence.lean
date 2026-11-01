module
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures

public section

/-! C6 HeadEvidence: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A HEAD signing label has exactly one duty. -/
theorem pcsa_head_single_duty (p : Params) {In : Type} (c : AppCodec In) (m : FGMode)
    (s : Slot) : Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.base (.head s)) := by
  refine ⟨.headAction s, rfl, ?_⟩
  intro d hd
  change d.signLabel = .base (.head s) at hd
  cases d <;> cases hd
  rfl
/-- Every pooled HEAD has an earlier handler with the exact signed wire. -/
theorem pcsa_pool_head_handled (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    ∃ j < k, ∃ t, V2.D.Run.handlesAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho k x ⟨.seat s i, .head r⟩ hm
  have he : row.1 = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) :=
    beq_iff_eq.mp (List.find?_some
      (p := fun row : GridCO.Wire p.n .root × Time =>
        row.1 == (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root)) hr)
  have hh := List.mem_of_find?_eq_some hr
  rcases row with ⟨o, stamp⟩
  dsimp only at he
  subst o
  obtain ⟨j, hj, t, ha, _⟩ := pcsa_head_stamp_source E rho k x s i r stamp hh
  exact ⟨j, hj, t, ha.1⟩
/-- A pooled HEAD of an honest seat has an emission with the same slot and root. -/
theorem pcsa_pool_head_emission (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hU : V2.D.UnforgeableSignatures E rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) i)
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t := by
  obtain ⟨j, _, t, parent, he, hh⟩ := pcsa_pool_head_handled E rho k x s i r hm
  rcases pcsa_handles_carried _ parent _ hh with hdir | hcar
  · rw [← hdir] at he
    obtain ⟨t', _, ht⟩ := hU.unforgeable x _ t ⟨j, he⟩ _ hi rfl
    exact ⟨t', ht⟩
  · obtain ⟨t', _, ht⟩ := hU.carried x parent t ⟨j, he⟩ _ hcar _ hi rfl
    exact ⟨t', ht⟩
/-- An honest pooled HEAD agrees with any emission of that seat and label. -/
theorem pcsa_honest_pool_head_eq_emitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (r r' : BlockId) (t' : Time)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) i)
      (⟨.seat (.base (.head s)) i, .head r'⟩ : Obj p) t') : r = r' := by
  obtain ⟨t, a, ha, ho⟩ := pcsa_pool_head_emission E rho hv.toUnforgeableSignatures k x s i r hi hm
  obtain ⟨b, hb, ho'⟩ := he
  have heq := (Gen.V2.Duty.emitted_unique_of_singleDuty E rho hv.nodup (.base (.head s))
    (pcsa_head_single_duty p c m s) i _ a b t t' _ _ ha hb ho ho' rfl rfl).2
  exact Msg.head.inj (congrArg (fun o : Obj p => o.payload) heq)
/-- Honest seats cannot be capped in any indexed HEAD pool. -/
theorem pcsa_honest_head_pool_not_capped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (GridCO.votesAt (V2.D.Run.stateBefore E rho k x).st.base s) i = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨o, ho, o', ho', hne, hoi, ho'i⟩ := (Gen.AC.Root.cap_pair _ i).mp he
  have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp ho).2
  have hl' : GridCO.headLabel? o' = some s := beq_iff_eq.mp (List.mem_filter.mp ho').2
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
  obtain ⟨r', rfl⟩ := pcsa_count_head_shape o' s i hl' ho'i
  obtain ⟨t, hem⟩ := pcsa_pool_head_emission E rho hv.toUnforgeableSignatures
    k x s i r' hi (List.mem_filter.mp ho').1
  have heq := pcsa_honest_pool_head_eq_emitted E rho hv k x s i r r' t hi
    (List.mem_filter.mp ho).1 hem
  exact hne (by rw [heq])
/-- The single HEAD duty fixes the time and awake status of each emission. -/
theorem pcsa_head_emission_time_awake (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (t : Time)
    (he : V2.D.Run.emits E rho x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    t = SA.voteTime p.toParams s ∧ E.awake x (SA.voteTime p.toParams s) = true := by
  obtain ⟨k, hk, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨hw, ht, _, _⟩ := (Gen.V2.Duty.mem_tick_singleDuty_iff E rho _ x t
    (.base (.head s)) (pcsa_head_single_duty p c m s) (.headAction s) rfl i (.head r)).mp ho
  have heq : t = SA.voteTime p.toParams s := ht.symm
  exact ⟨heq, heq ▸ hw⟩
end AvailableChain.PCSA.Run

end
