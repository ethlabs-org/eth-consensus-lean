module
public import AvailableChainPCSAProofs.Proofs.Clean.NHeads

public section

/-! C6 ReleaseCount: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
private def releaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B)))).toFinset

private theorem pcsa_release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : GridCO.releaseCount q v s B = (releaseSeats q v s B).card := by
  have hp : (fun o : GridCO.Wire n .root => match GridCO.resolvedHead? v o with
      | some C => !Block.compatible C B
      | none => false) = (fun o => (GridCO.resolvedHead? v o).any
        (fun C => !Block.compatible C B)) := by
    funext o
    cases GridCO.resolvedHead? v o <;> rfl
  unfold GridCO.releaseCount releaseSeats
  dsimp only
  refine Eq.trans ?_ (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup (α := Fin n) _))).symm
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext k
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ k).any f)
  exact hp

private theorem pcsa_release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) (k : Fin n) : k ∈ releaseSeats q v s B ↔
      GridCO.equivocates (GridCO.votesAt v s) k = false ∧
      ∃ o ∈ GridCO.votesAt v s,
        GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true ∧
        GridCO.headSeat? o = some k ∧
        (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B) = true := by
  dsimp only [releaseSeats]
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq]
  constructor
  · rintro ⟨_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact ⟨he, o, ho, hr, hk, hc⟩
  · rintro ⟨he, o, ho, hr, hk, hc⟩
    refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hk⟩)

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Only faulty seats count against a block compatible with every honest HEAD. -/
theorem pcsa_release_count_fault_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (a : Nat) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (s : Slot) (B : Block)
    (hheads : ∀ y H, HonestHeadAt p c E rho y s H → Block.Compatible H B) :
    GridCO.releaseCount p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st t)) s B ≤
        (Gen.V2.Duty.faulty rho).card := by
  classical
  rw [pcsa_release_card]
  apply Finset.card_le_card_of_injOn (fun i : Fin p.n => rho.seatOf (.base (.head s)) i)
  · intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hhonest
    obtain ⟨_, o, ho, _, hseat, hconf⟩ := (pcsa_release_mem _ _ _ _ _).mp hi
    have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp ho).2
    obtain ⟨H, hr, hc⟩ : ∃ H,
        GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st t)) o =
          some H ∧ (!Block.compatible H B) = true := by
      cases hh : GridCO.resolvedHead?
          (actView (clock p (V2.D.Run.stateBefore E rho a x).st t)) o with
      | none => simp only [hh, Option.any_none, Bool.false_eq_true] at hconf
      | some H => exact ⟨H, rfl, by simpa only [hh, Option.any_some] using hconf⟩
    have hH := pcsa_honest_pool_head_source E rho h hF a x hx t s H o i hhonest
      (List.mem_filter.mp ho).1 hl hseat hr
    have hyes : Block.compatible H B = true := hheads _ H hH
    rw [hyes] at hc
    cases hc
  · intro i _ k _ he
    exact (h.cstar (.base (.head s)) trivial).1 he
end AvailableChain.PCSA.Run

end
