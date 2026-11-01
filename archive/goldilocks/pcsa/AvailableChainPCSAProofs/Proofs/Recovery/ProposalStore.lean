module
public import AvailableChainPCSAProofs.Proofs.Shared.RunEvidence
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Recovery.LockOrigin
public import AvailableChainPCSAProofs.Proofs.Shared.Walk
public import AvailableChainPCSAClaims.Statements.Premises

public section

/-! Named parent lookup and honest proposal construction in recovery. -/
namespace AvailableChain.PCSA
variable {n : Nat}

private theorem normalize_names (st : State n) : (normalizeS st).namedBodies = st.namedBodies := by
  delta normalizeS
  split <;> rfl

private theorem reconcile_names (st : State n) : (reconcile st).namedBodies = st.namedBodies := by
  delta reconcile
  rw [normalize_names]
  rfl

private theorem collect_names (st : State n) : (collectPCs st).namedBodies = st.namedBodies := by
  apply collectPCs_preserves State.namedBodies
  intro st pc
  rw [installPC_def]
  split <;> rfl

private theorem raw_names (st : State n) (a : AckWire n) :
    (poolAckRaw st a).namedBodies = st.namedBodies := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem acks_names (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).namedBodies = st.namedBodies := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, raw_names]

private theorem row_names (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).namedBodies = st.namedBodies := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem rows_names (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).namedBodies = st.namedBodies := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, row_names]

private theorem append_names (st : State n) (s : Slot) (N : NamedProposal n)
    (base : GridCO.State n .root) (fg : SimplexFG.Store (Fin n)) :
    ({ st with
      base := base
      fg := fg
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } : State n).namedBodies =
      st.namedBodies ++ [N] := by
  change (NamedProposal.genesis : NamedProposal n) ::
    (st.proposals ++ [(⟨.proposer s, .proposal N⟩ : Wire n)]).filterMap Wire.proposal? = _
  rw [List.filterMap_append]
  rfl

private theorem block_names (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n) :
    admitBlock p st s N = st ∨ (admitBlock p st s N).namedBodies = st.namedBodies ++ [N] := by
  delta admitBlock
  split
  · exact Or.inl rfl
  · cases hp : parentFG st N.erase with
    | none => exact Or.inl rfl
    | some P =>
      dsimp only
      split
      · right
        rw [rows_names, collect_names, acks_names]
        cases N.pc <;> dsimp only <;> split_ifs <;> first
          | exact append_names st s N _ _
          | (rw [reconcile_names]; exact append_names st s N _ _)
      · exact Or.inl rfl

/-- Processing only adds named bodies. -/
theorem recovery_process_names_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.namedBodies ⊆ (process p st o).namedBodies := by
  delta process
  cases hd : o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body => rw [row_names]
    | block s N =>
      dsimp only
      rcases block_names p st s N with he | he
      · rw [he]
      · rw [he]; exact List.subset_append_left _ _
    | ack s i r =>
      dsimp only
      delta admitAck
      rw [collect_names]
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact List.Subset.refl _
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact List.Subset.refl _
        · split <;> exact List.Subset.refl _
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · rw [collect_names, acks_names]
      · exact List.Subset.refl _

private theorem process_block_name (p : Params) (st : State p.n) (o : Wire p.n)
    (hne : process p st o ≠ st) (s : Slot) (N : NamedProposal p.n)
    (hd : o.decode = some (.block s N)) : N ∈ (process p st o).namedBodies := by
  have he : process p st o = admitBlock p st s N := by
    delta process
    rw [hd]
  rw [he] at hne ⊢
  rcases block_names p st s N with hh | hh
  · exact (hne hh).elim
  · rw [hh]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem gate_names (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).namedBodies = st.namedBodies := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some C =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State p.n => acc.namedBodies = st.namedBodies)
      · rfl
      · intro acc hh b _
        apply List.foldlRecOn (motive := fun acc : State p.n => acc.namedBodies = st.namedBodies)
        · exact hh
        · intro acc' hh' g _
          exact hh'

/-- The clock keeps the authoritative named bodies. -/
theorem recovery_clock_names (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).namedBodies = st.namedBodies := by
  have hc : (clockPre p st t).namedBodies = st.namedBodies := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    rw [normalize_names]
    split
    · exact hc
    · rw [gate_names]
      exact hc
  · exact hc

private def NamedCover (st : State n) : Prop :=
  StoreEvidence (fun B => ∃ N ∈ st.namedBodies, N.erase = B) (fun _ => True) st

private theorem process_namedCover (p : Params) (st : State p.n) (o : Wire p.n)
    (h : NamedCover st) : NamedCover (process p st o) := by
  by_cases he : process p st o = st
  · rw [he]; exact h
  · apply process_evidence
    · change StoreEvidence _ _ st at h
      rw [StoreEvidence_def] at h ⊢
      refine ⟨?_, ?_, h.2.2⟩
      · intro B hb
        obtain ⟨N, hn, he⟩ := h.1 B hb
        exact ⟨N, recovery_process_names_mono p st o hn, he⟩
      · intro pc hp
        obtain ⟨N, hn, he⟩ := h.2.1 pc hp
        exact ⟨N, recovery_process_names_mono p st o hn, he⟩
    · intro s i r hd
      trivial
    · intro s N hd
      exact ⟨⟨N, process_block_name p st o he s N hd, rfl⟩, by intros; trivial⟩

private theorem clock_namedCover (p : Params) (st : State p.n) (t : Time)
    (h : NamedCover st) : NamedCover (clock p st t) := by
  delta NamedCover
  rw [recovery_clock_names]
  exact clock_evidence p _ _ st t h

/-- Every stored block and PC target has a local named body. -/
theorem recovery_reachable_named_bodies (p : Params) (st : State p.n) (h : Reachable p st) :
    (∀ B ∈ st.base.blocks, ∃ N ∈ st.namedBodies, N.erase = B) ∧
      (∀ pc ∈ st.pcs, ∃ N ∈ st.namedBodies, N.erase = pc.target) := by
  have hn : NamedCover st := by
    induction h with
    | init =>
      delta NamedCover
      rw [StoreEvidence_def]
      refine ⟨?_, ?_, ?_⟩
      · intro B hb
        have he : B = .genesis := List.mem_singleton.mp hb
        subst B
        exact ⟨.genesis, List.mem_cons_self, rfl⟩
      · intro pc hp
        exact (List.not_mem_nil hp).elim
      · intros; trivial
    | tick t _ ih => exact clock_namedCover p _ t ih
    | deliver o _ ih => exact process_namedCover p _ o ih
  delta NamedCover at hn
  rw [StoreEvidence_def] at hn
  exact ⟨hn.1, hn.2.1⟩

private theorem clock_lock_property (p : Params) (st : State p.n) (t : Time)
    (Q : Block → Prop) (ht : ∀ B ∈ st.base.blocks, Q B)
    (hl : ∀ row ∈ st.base.obligations, Q row.1) :
    ∀ row ∈ (clock p st t).base.obligations, Q row.1 := by
  have hc : ∀ row ∈ (clockPre p st t).base.obligations, Q row.1 := by
    intro row hr
    obtain ⟨old, ho, he⟩ := List.mem_map.mp
      (clockPre_lock_targets_subset p st t (List.mem_map.mpr ⟨row, hr, rfl⟩))
    exact he ▸ hl old ho
  have hct : ∀ B ∈ (clockPre p st t).base.blocks, Q B := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  have hg (st : State p.n) (a : Block) (cs : List (PC p.n)) (rank : Option PCRank)
      (s : Slot) (ht : ∀ B ∈ st.base.blocks, Q B)
      (hl : ∀ row ∈ st.base.obligations, Q row.1) :
      ∀ row ∈ (gateFrom p a cs rank st s).base.obligations, Q row.1 := by
    rw [gateFrom_def]
    dsimp only
    cases SA.Root.confirmationFrom p.toParams a (actView st) s with
    | none => exact hl
    | some C =>
      dsimp only
      split
      · exact hl
      · apply List.foldlRecOn (motive := fun acc : State p.n =>
          ∀ row ∈ acc.base.obligations, Q row.1)
        · exact hl
        · intro acc hh b hb
          have hq := ht b (List.mem_filter.mp (List.mem_filter.mp hb).1).1
          apply List.foldlRecOn (motive := fun acc : State p.n =>
            ∀ row ∈ acc.base.obligations, Q row.1)
          · exact hh
          · intro acc' hh' g _ row hr
            change row ∈ (GridCO.writeObligation acc'.base b g _).obligations at hr
            delta GridCO.writeObligation at hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hh' row (List.mem_filter.mp hr).1
            · cases List.mem_singleton.mp hr
              exact hq
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    have hn (st : State p.n) (h : ∀ row ∈ st.base.obligations, Q row.1) :
        ∀ row ∈ (normalizeS st).base.obligations, Q row.1 := by
      delta normalizeS
      split <;> exact h
    apply hn
    split
    · exact hc
    · exact hg _ _ _ _ _ hct hc
  · exact hc

/-- Every stored lock target also has a local named body. -/
theorem recovery_lock_named_body (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.obligations, ∃ N ∈ st.namedBodies, N.erase = row.1 := by
  induction h with
  | init => intro row hr; exact (List.not_mem_nil hr).elim
  | deliver o _ ih =>
    intro row hr
    obtain ⟨old, ho, he⟩ := List.mem_map.mp
      (process_lock_targets_subset p _ o (List.mem_map.mpr ⟨row, hr, rfl⟩))
    obtain ⟨N, hn, hN⟩ := ih old ho
    exact ⟨N, recovery_process_names_mono p _ o hn, hN.trans he⟩
  | tick t hh ih =>
    rw [recovery_clock_names]
    exact clock_lock_property p _ t _ (recovery_reachable_named_bodies p _ hh).1 ih

/-- The proposer head has a named body when Z is genesis. -/
theorem recovery_head_named_body (p : Params) (st : State p.n) (h : Reachable p st)
    (hz : (controls p st).Z = .genesis) (s : Slot) :
    ∃ N ∈ st.namedBodies,
      N.erase = getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s) := by
  have hc := recovery_reachable_named_bodies p st h
  have hg : ∃ N ∈ st.namedBodies, N.erase = eraseFG (controls p st).Z := by
    rw [hz]
    exact ⟨.genesis, List.mem_cons_self, rfl⟩
  have hr : ∃ N ∈ st.namedBodies, N.erase = liveRoot p st (proposerPC p st) := by
    rcases pcsa_liveRoot_origin p st (proposerPC p st) with he | hm
    · rw [he]
      cases hp : proposerPC p st with
      | none => exact hg
      | some pc =>
        change ∃ N ∈ st.namedBodies,
          N.erase = if frameActive p st pc then pc.target else eraseFG (controls p st).Z
        split
        · have hm := bestPC_mem (st.pcs.filter (frameActive p st)) pc hp
          exact hc.2 pc (List.mem_filter.mp hm).1
        · exact hg
    · obtain ⟨row, hm, he, _⟩ := (pcsa_walkLocks_mem p st (proposerPC p st) _).mp hm
      obtain ⟨N, hn, hN⟩ := recovery_lock_named_body p st h row hm
      exact ⟨N, hn, hN.trans he⟩
  rcases pcsa_headInTree_mem_or_root p st (proposerPC p st)
    (erasedList st (fullTree p st)) (proposerVotes st s) (proposerSupport st s) with he | hm
  · have he' : getHead p st (proposerPC p st) (proposerVotes st s)
        (proposerSupport st s) = liveRoot p st (proposerPC p st) := he
    rw [he']
    exact hr
  · exact hc.1 _ (List.mem_filter.mp hm).1

/-- A unique local named body is returned by the lookup. -/
theorem recovery_named_lookup (st : State n) (H : Block) (N : NamedProposal n)
    (hn : N ∈ st.namedBodies) (he : N.erase = H)
    (hu : ∀ M ∈ st.namedBodies, M.erase = H → M = N) : namedByErase? st H = some N := by
  have singleton {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α)
      (ha : a ∈ xs) (hall : ∀ b ∈ xs, b = a) : xs.eraseDups = [a] := by
    cases xs with
    | nil => exact (List.not_mem_nil ha).elim
    | cons b bs =>
      have hb := hall b (List.mem_cons_self)
      subst b
      rw [List.eraseDups_cons]
      have hf : bs.filter (fun b => !b == a) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simp only [hall b (List.mem_cons_of_mem _ hb), beq_self_eq_true, Bool.not_true,
          Bool.false_eq_true, not_false_eq_true]
      rw [hf]
      rfl
  have hs : (st.namedBodies.filter (fun M => M.erase == H)).eraseDups = [N] := by
    apply singleton
    · exact List.mem_filter.mpr ⟨hn, beq_iff_eq.mpr he⟩
    · intro M hm
      exact hu M (List.mem_filter.mp hm).1 (beq_iff_eq.mp (List.mem_filter.mp hm).2)
  delta namedByErase?
  rw [hs]

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Collision freedom makes the local parent lookup unambiguous. -/
theorem recovery_run_named_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hi : NamedRootCollisionFree p c E rho)
    (x : V) (hx : x ∈ rho.honest) (i : Nat) (s : Slot)
    (hz : (controls p (V2.D.Run.stateBefore E rho i x).st).Z = .genesis) :
    ∃ N, namedByErase? (V2.D.Run.stateBefore E rho i x).st
      (getHead p (V2.D.Run.stateBefore E rho i x).st
        (proposerPC p (V2.D.Run.stateBefore E rho i x).st)
        (proposerVotes (V2.D.Run.stateBefore E rho i x).st s)
        (proposerSupport (V2.D.Run.stateBefore E rho i x).st s)) = some N := by
  obtain ⟨N, hn, he⟩ := recovery_head_named_body p _ (pcsa_reachable_stateBefore E rho i x) hz s
  refine ⟨N, recovery_named_lookup _ _ N hn he ?_⟩
  intro M hm hM
  have scope (A : NamedProposal p.n) (ha : A ∈ (V2.D.Run.stateBefore E rho i x).st.namedBodies) :
      NamedProposalInRun p c E rho A :=
    ⟨A, Or.inr ⟨x, hx, i, ha⟩, pcsa_named_preceq_refl A⟩
  apply hi.root_injective N M (scope N hn) (scope M hm) M N
    (Or.inr (pcsa_named_preceq_refl M)) (Or.inl (pcsa_named_preceq_refl N))
  rw [← pcsa_named_erase_root M, ← pcsa_named_erase_root N]
  exact congrArg Block.root (hM.trans he.symm)

private theorem act_proposal_of_parent (p : Params) {In : Type} (c : AppCodec In)
    (m : FGMode) (nd : Node p) (s : Slot) (x : In) (hs : 0 < s)
    (N : NamedProposal p.n)
    (hn : namedByErase? nd.st (getHead p nd.st (proposerPC p nd.st)
      (proposerVotes nd.st s) (proposerSupport nd.st s)) = some N) :
    ∃ P, actWith m p c nd (.propAction s) x = some (.proposal P) := by
  rw [actWith_def]
  change ∃ P, (propose p nd.st s).map (withApp p (c.app x)) = some (.proposal P)
  delta propose
  rw [ite_eq_right (Nat.ne_of_gt hs)]
  dsimp only
  rw [hn]
  exact ⟨_, rfl⟩


/-- An honest awake positive slot emits a named proposal in stage one. -/
theorem recovery_named_proposal_exists (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hbase : Base₂ p c E rho)
    (hframe : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s)
    (hp : Gen.V2.Duty.HonestAwakeProposer E (pcsaInterface p c (m := m)).toInterface rho s)
    (hh : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ N : NamedProposal p.n, HonestNamedProposal p c E rho s N := by
  let x := V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s
  let t := SA.proposalTime p.toParams s
  have hpublic : V2.PublicTime E t := by
    refine ⟨4 * s, ?_⟩
    rw [hbase.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have ht0 : 0 ≤ t := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int)
    positivity
  obtain ⟨i, hit⟩ := List.mem_iff_getElem?.mp
    (hbase.valid.tick_total x hp.1 t hpublic ht0 hh)
  have hstore : (V2.D.Run.stateBefore E rho (i + 1) x).st =
      clock p (V2.D.Run.stateBefore E rho i x).st t := by
    rw [V2.D.Run.stateBefore_succ E rho hit]
    change (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st = _
    rw [Function.update_self]
    exact pcsa_tick_st E rho _ x t
  obtain ⟨N, hn⟩ := recovery_run_named_parent E rho hbase.idealization x hp.1 (i + 1) s
    (hframe x hp.1 (i + 1)).2.1
  rw [hstore] at hn
  obtain ⟨P, ha⟩ := act_proposal_of_parent p c m
    ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho i x) t) s (rho.input x t) hs N hn
  refine ⟨P, hp.1, i, hit, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho hit).2]
  apply (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s)
    (V2.D.propSeat (pcsaInterface p c (m := m)).toInterface s) (.proposal P)).mpr
  exact ⟨hp.2, rfl, .propAction s, rfl, rfl, ha⟩

end AvailableChain.PCSA.Run
end
