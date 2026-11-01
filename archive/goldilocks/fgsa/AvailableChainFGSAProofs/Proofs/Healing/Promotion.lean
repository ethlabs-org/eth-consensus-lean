module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGCompose.Proofs.Healing.Promotion
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule
public import AvailableChainFGSAProofs.Proofs.Healing.FrameSource
public import AvailableChainFGSAClaims.Statements.Fold

public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private def p0d3_fixed_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d3_fixed_core (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }
private def p0d3_fixed_safety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

omit [Fintype V] in
private theorem p0d3_fixed_frame_mem (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    {nd : Node p} (hnd : postClock E rho x (p.actionTime r) = some nd)
    (hK : actionSourceFG p c E rho x r = some (some K)) : K ∈ fullTree p nd.st := by
  rw [actionSourceFG_def, hnd] at hK
  have hs : fgSource p nd.st = some K := Option.some.inj hK
  exact (Finset.mem_filter.mp (pickPair_some_spec _ _ hs).1).1

omit [Fintype V] in
private theorem p0d3_fixed_covered_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (r : Nat) (Q : Block) :
    FGCompose.OpeningCovered (p0d3_fixed_core p c) (p0d3_fixed_safety p c) E rho
      (heightView p) (p0d3_fixed_timing p) (fun a => a.payload.height_pair) r Q =
        OpeningCovered p c E rho r Q := by
  apply propext
  constructor
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hr, ha, hn⟩ := h x hx
    exact ⟨K, nd, j, rSent, a, hnd, hK, p0d3_fixed_frame_mem E rho hnd hK,
      hQ, hr, ha, hn⟩
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d3_fixed_batch_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (r height : Nat) (Q : Block) (U : FGBlock (Fin p.n)) :
    FGCompose.FixedRows (p0d3_fixed_core p c) (p0d3_fixed_safety p c) E rho
      (heightView p) (p0d3_fixed_timing p) (fun a => a.payload.height_pair) r height Q U =
    (∀ x ∈ rho.honest, ∃ K nd j rSent a,
      postClock E rho x (p.actionTime r) = some nd ∧
      actionSourceFG p c E rho x r = some (some K) ∧ K ∈ fullTree p nd.st ∧
      Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
      (heightView p K).h = height ∧ (heightView p K).T_h = U ∧ rSent ≤ r ∧
      HonestRowAt p c E rho j x rSent a ∧ NamesEntry p .progress a height U) := by
  apply propext
  constructor
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hUK, hs, hh, he, hr, ha, hn⟩ := h x hx
    exact ⟨K, nd, j, rSent, a, hnd, hK, p0d3_fixed_frame_mem E rho hnd hK,
      hQ, hUK, hs, hh, he, hr, ha, hn⟩
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hUK, hs, hh, he, hr, ha, hn⟩ := h x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hUK, hs, hh, he, hr, ha, hn⟩

private theorem promotion_honest_nonempty (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hf := hrec.fault
  rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
  have := p.nPos
  omega

omit [Fintype V] in
private theorem promotion_stored_parent_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, N, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : N.erase = eraseFG W := Option.some.inj hb
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [hQ, eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem promotion_stored_ancestor_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s root body rows ih =>
      by_cases he : U = .node P s root body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (promotion_stored_parent_slot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d3_fixed_ancestor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hUK : FGBlock.Preceq U K) : U.slot ≤ K.slot := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact promotion_stored_ancestor_slot E rho hrec.base.valid i x hs hUK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1356–1384; plan §3.2 step 1.
DC: INTENTIONAL choose the starting action's SO-COV witnesses once.
The sources can differ. Their actual entries agree by root injectivity.
The source path, source slot and original send round remain in the result. -/
theorem healing_promotion_fixed_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {Q : Block} (hentry : OpeningEntry p c E rho r height)
    (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U := by
  have hcov := (p0d3_fixed_covered_eq E rho r Q).mpr hcovered
  have h := FGCompose.healing_promotion_fixed_rows
    (p0d3_fixed_core p c) (p0d3_fixed_safety p c) E rho
    (heightView p) (p0d3_fixed_timing p) (fun a => a.payload.height_pair)
    p.E (fgCertificateLaws p).height (promotion_honest_nonempty E rho hrec)
    hentry hcov
    (fun x y K L hx hy hK hL he =>
      rootScope_eq hrec.base.idealization
        (rootScope_entry (rootScope_source hx hK))
        (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
  simp only [p0d3_fixed_batch_eq] at h
  delta FGCompose.EntryAt at h
  exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1356–1384; plan §3.2 steps 1 and 5.
DC: SAME the common entry's slot is at most the starting action label.
The equality is supplied by the fixed starting rows. -/
theorem healing_promotion_entry_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hU : (heightView p K).T_h = U) : U.slot ≤ r * p.R := by
  exact FGCompose.healing_promotion_entry_slot
    (p0d3_fixed_core p c) E rho (heightView p) (p0d3_fixed_timing p)
    p.E (fgCertificateLaws p).height hx hK hU
    (fun y L hy hL => healing_source_slot p c E rho hy hL)
    (fun y L A _ hL hAL => p0d3_fixed_ancestor E rho hrec hL hAL)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1356–1384; plan §3.2 step 1.
DC: SAME the fixed batch keeps the common entry and its action-slot bound.
No starting row or source is replaced. -/
theorem healing_promotion_bounded_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {Q : Block} (hentry : OpeningEntry p c E rho r height)
    (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U := by
  have h := FGCompose.healing_promotion_bounded_rows
    (p0d3_fixed_core p c) (p0d3_fixed_safety p c) E rho
    (heightView p) (p0d3_fixed_timing p) (fun a => a.payload.height_pair)
    p.E (fgCertificateLaws p).height (promotion_honest_nonempty E rho hrec)
    hentry ((p0d3_fixed_covered_eq E rho r Q).mpr hcovered)
    (fun x y K L hx hy hK hL he =>
      rootScope_eq hrec.base.idealization
        (rootScope_entry (rootScope_source hx hK))
        (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d3_fixed_ancestor E rho hrec hK hAK)
  simp only [p0d3_fixed_batch_eq] at h
  delta FGCompose.EntryAt at h
  exact h

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1385–1396; plan §3.2 step 4.
DC: SAME an actual starting source is a fast PhaseBody at its own opening.
No later source or row is selected. -/
theorem healing_promotion_source_body (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K)) :
    PhaseBody p c E rho (r * p.R) (eraseFG K) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    let nd := (fgsa p c).clock (rho.stateBefore E i x) (p.actionTime r)
    have hround : p.round (nd.st.slot p) = r := (fgsa_action_slot_round (c := c) _ r).2
    have hfw := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).2
    change (decide (eraseFG K ∈ (fastWriteAt nd.st (p.round (nd.st.slot p) * p.R)).getD []) &&
      _) = true at hfw
    have hmem := of_decide_eq_true (Bool.and_eq_true_iff.mp hfw).1
    rw [hround] at hmem
    refine ⟨x, hx, Or.inl ⟨nd, ?_, hmem⟩⟩
    rw [← fgsa_grid_action_gate, fgsa_grid_action_time, postClock_def, preTick_def, hi]
    rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1385–1396; plan §3.2 step 4.
DC: SAME TPerm transfers each fixed source to the new proposal's parent.
The phase premise includes the proposal read; service after phase termination
is not required. -/
theorem healing_promotion_source_parent (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (perm : TPerm p c E rho)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r : Nat} {s : Slot} {x : V} {K : FGBlock (Fin p.n)} {Q : Block}
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s)
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K))
    (hs : r * p.R + 2 ≤ s) (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    Block.Preceq (eraseFG K) Q.parent := by
  have hg : SA.gateTime p.toParams (r * p.R) ≤ SA.proposalTime p.toParams s := by
    rwa [← fgsa_grid_action_gate, fgsa_grid_action_time]
  have ht := perm u _ m J contested (r * p.R) (eraseFG K) hready hphase hu hg
    (healing_promotion_source_body E rho hx hK)
  exact ht.2.1 s Q hs le_rfl hQ

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1410–1424; plan §3.2 step 6.
DC: SAME service is conditional on the old phase through the new gate.
This adapter uses the persistent RepairAfter premise of the frozen boundary. -/
theorem healing_promotion_continuing_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {l s : Slot} {Q : Block}
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hafter : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
      ExactService p c E rho s Q := by
  intro hphase
  exact hrepair _ hphase s Q hafter le_rfl hQ

end AvailableChain.FGSA.Run
end
