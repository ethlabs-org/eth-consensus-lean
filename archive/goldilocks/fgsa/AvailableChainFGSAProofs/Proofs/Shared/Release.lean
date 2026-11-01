module
public import AvailableChainFGSARun.Proofs.HeadIdentity
public import AvailableChainFGSARun.Proofs.HeadHistory
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.V2.Duty.Counts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def releaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B)))).toFinset

private theorem release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
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

private theorem release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
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

private theorem resolved_active_base {n : Nat} (st : State n) (o : GridCO.Wire n .root)
    (t : Time) (h : GridCO.resolvedBefore (actView st) o t = true) :
    GridCO.resolvedBefore st.base o t = true := active_resolvedBefore_base st o t h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.3: restricting the block domain to actView can only decrease release.
Class (iii), store instance. DC counterpart: none; INTENTIONAL, SA adds the
lease lifecycle (spec/fgsa-protocol.tex:2514–2515; blueprint 01 §5). -/
theorem fgsa_releaseCount_antitone (p : Params) (st : State p.n) (s : Slot) (B : Block) :
    GridCO.releaseCount p.toParams.engine (actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B := active_releaseCount_le p st s B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.3, bp.release.v1(a,c), blueprint 01 §5 item 6: both store laws.
Class (iii), store instance. DC counterpart: none; INTENTIONAL, SA adds the
lease lifecycle (spec/fgsa-protocol.tex:2514–2515). -/
theorem fgsa_release_store (p : Params) (st : State p.n) :
    ∀ s B, GridCO.releaseCount p.toParams.engine (actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B ∧
      (Block.Preceq B (eraseFG st.fg.F) →
        GridCO.releaseCount p.toParams.engine (actView st) s B = 0) := by
  intro s B
  exact ⟨fgsa_releaseCount_antitone p st s B, actView_releaseCount_zero st _ s⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.3, bp.release.v1(b): only faulty HEAD holders count against B.
Class (ii), FG-SA instance of v2 signature authenticity and CStar, with
finite-set injection. DC counterpart: none; INTENTIONAL, SA adds release
(spec/fgsa-protocol.tex:2514–2515; blueprint 02 §2, 21 H.1).
The local compatibility premise keeps the emitted HEAD label. -/
theorem fgsa_release_bound_restart (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (_hDelta : E.Δ = p.Δ)
    (hroots : NamedRootCollisionFree p c E rho)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hheads : ∀ y ∈ rho.honest, ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ k C, o.auth = .seat (.base (.head s)) k → HeadTargetAtEmission p c E rho y o t C →
        Block.Compatible C B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B ≤
      (Gen.V2.Duty.faulty rho).card := by
  rw [release_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    change rho.seatOf (.base (.head s)) k ∈ Gen.V2.Duty.faulty rho
    rw [Gen.V2.Duty.faulty_def]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hhonest
    obtain ⟨_, o, ho, _, hseat, hconf⟩ := (release_mem _ _ _ _ _).mp hk
    have hl : GridCO.headLabel? o = some s := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp ho).2
    have hstored : o ∈ (storeAt p c E rho i x).base.votes :=
      (List.mem_filter.mp ho).1
    obtain ⟨D, hresolve, hConflict⟩ : ∃ D,
        GridCO.resolvedHead? (actView (storeAt p c E rho i x)) o = some D ∧
        (!Block.compatible D B) = true := by
      cases hR : GridCO.resolvedHead? (actView (storeAt p c E rho i x)) o with
      | none => simp only [hR, Option.any_none, Bool.false_eq_true] at hconf
      | some D => exact ⟨D, rfl, by simpa only [hR, Option.any_some] using hconf⟩
    obtain ⟨auth, payload⟩ := o
    cases auth with
    | none => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
    | proposer r => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
    | seat r j =>
      cases payload with
      | proposal C raw support =>
          change (none : Option Slot) = some s at hl
          contradiction
      | head C =>
        have hrs : r = s := Option.some.inj hl
        have hjk : j = k := Option.some.inj hseat
        subst r; subst j
        have hv := hstored
        change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at hv
        rw [← fgsa_vote_stamp_keys E rho i x] at hv
        obtain ⟨⟨wire, stamp⟩, hv, he⟩ := List.mem_map.mp hv
        dsimp only at he
        subst wire
        have horigin : ∃ (j : Nat) (parent : Obj p) (u : Time),
            rho.events[j]? = some (.deliver x parent u) ∧
            (parent = ofHead p ⟨.seat (.head s) k, C⟩ ∨
              (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) k, C⟩)) := by
          rcases fgsa_vote_stamp_source_or_restart E rho i x s k C stamp hv with
            ⟨j, _, u, ha, _⟩ | ⟨j, _, wake, _, _, hr⟩
          · obtain ⟨parent, hd, hh⟩ := ha.1
            exact ⟨j, parent, u, hd, (fgsaHooks p c).handles_carries _ parent _ hh⟩
          · obtain ⟨j', _, parent, u, hd, hc⟩ :=
              fgsa_replayed_head_delivery_origin E rho j x wake s k C hr
            exact ⟨j', parent, u, hd, Or.inr hc⟩
        obtain ⟨j, parent, u, hd, hc⟩ := horigin
        have hem : ∃ t, t ≤ u ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
            (ofHead p ⟨.seat (.head s) k, C⟩) t := by
          rcases hc with rfl | hc
          · exact hE.unforgeable x _ u ⟨j, hd⟩ _ hhonest rfl
          · exact hE.carried x parent u ⟨j, hd⟩ _ hc _ hhonest rfl
        obtain ⟨u, _, hem⟩ := hem
        obtain ⟨H, hH⟩ := headTargetAtEmission_exists E rho hem rfl
        have hcompat := hheads _ hhonest _ u hem k H rfl hH
        have hCH : C = H.root := by
          obtain ⟨_, _, _, _, _, ho, _⟩ := hH
          exact Msg.head.inj (congrArg (fun o : Obj p => o.payload) ho)
        have hTarget : GridCO.headTarget? (⟨.seat s k, .head C⟩ : GridCO.Wire p.n .root) =
            some H.root := congrArg some hCH
        have hDH := headTargetAtEmission_receiver_eq E rho hroots hH i x
          (actView (storeAt p c E rho i x)) ⟨.seat s k, .head C⟩
          (fun _ h => (List.mem_filter.mp h).1) hTarget hresolve
        rw [hDH, show Block.compatible H B = true from hcompat] at hConflict
        contradiction
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- The legacy release API follows from the restarted signature-origin proof. -/
theorem fgsa_release_bound (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (_hN : V2.D.NoRestart rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hDelta : E.Δ = p.Δ)
    (hroots : NamedRootCollisionFree p c E rho)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hheads : ∀ y ∈ rho.honest, ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ k C, o.auth = .seat (.base (.head s)) k → HeadTargetAtEmission p c E rho y o t C →
        Block.Compatible C B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B ≤
      (Gen.V2.Duty.faulty rho).card :=
  fgsa_release_bound_restart p c E rho hE hC hDelta hroots i x s B hheads

/-- Bound release by an explicit set of senders of conflicting resolved HEADs.
The caller supplies only the actual release witnesses in this view. -/
theorem fgsa_releaseCount_le_senders {n : Nat} {V : Type}
    (q : GridCO.Params) (v : GridCO.State n .root) (s : Slot) (B : Block)
    (sender : Fin n → V) (hinj : Function.Injective sender) (bad : Finset V)
    (hbad : ∀ k o, o ∈ GridCO.votesAt v s →
      GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true →
      GridCO.headSeat? o = some k →
      (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B) = true →
      sender k ∈ bad) : GridCO.releaseCount q v s B ≤ bad.card := by
  classical
  rw [release_card]
  apply Finset.card_le_card_of_injOn sender
  · intro k hk
    obtain ⟨_, o, ho, hr, hs, hc⟩ := (release_mem q v s B k).mp hk
    exact hbad k o ho hr hs hc
  · intro k _ j _ he
    exact hinj he

end AvailableChain.FGSA.Run
end
