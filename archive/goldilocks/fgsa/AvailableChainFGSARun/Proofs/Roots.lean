module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSARun.Proofs.NamedHistory
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.CrossNode
public import AvailableChainFGSA.Proofs.Head -- shake: keep (re-export)
public import AvailableChainFGSARun.Statements.Interface -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]




/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedRootCollisionFree] Stored content agrees on scoped roots.
This geometric helper projects equality; namedProposal_eq gives full identity. -/
theorem stored_content_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho)
    {b b' : Block} {raw support raw' support' : List (HeadWire p.n)}
    {rows rows' : List (RowWire p.n)}
    (hb : RootBlockInRun p c E rho b) (hb' : RootBlockInRun p c E rho b')
    (hc : contentOk p b raw support rows = true)
    (hc' : contentOk p b' raw' support' rows' = true)
    (he : b.root = b'.root) : b = b' ∧ rows = rows' := by
  have hbb := rootBlockInRun_eq E rho hr hb hb' he
  subst b'
  exact ⟨rfl, rows_eq_of_rowsOk (contentOk_rowsOk hc) (contentOk_rowsOk hc')⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] An app update recomputes the full content digest. -/
theorem contentOk_withApp (H : NamedProposal p.n) (s : Slot) (r : BlockId) (body app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p app (.proposal (.node H s r body raw support rows)) =
      .proposal (namedProposal p H s app raw support rows) ∧
    namedContentOk p (namedProposal p H s app raw support rows) = true :=
  ⟨rfl, by
    unfold namedContentOk
    rw [namedProposal_erase]
    exact contentOk_proposalBlock p H.erase s app raw support rows⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] A zero app update preserves the zero-app proposal. -/
theorem withApp_zero_proposalBlock (H : NamedProposal p.n) (s : Slot)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p 0 (.proposal (namedProposal p H s 0 raw support rows)) =
      .proposal (namedProposal p H s 0 raw support rows) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] An app update preserves BODY validity. -/
theorem rowsOk_withApp_proposalBlock (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    rowsOk (proposalBlock p H s app raw support rows) rows = true :=
  contentOk_rowsOk (contentOk_proposalBlock p H s app raw support rows)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Direct delivery puts the proposal body in scope. -/
theorem rootBlockInRun_delivered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {N : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events)
    (ho : o.payload = .proposal N) : RootBlockInRun p c E rho N.erase :=
  ⟨N, namedScope_delivered E rho hd ho, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. An honest prefix body is a direct scope seed. -/
theorem rootBlockInRun_held (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} (hx : x ∈ rho.honest) (i : Nat) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
    RootBlockInRun p c E rho b := by
  obtain ⟨N, hN, he⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho i x)
    (metaInv_stateBefore E rho i x) b).mp hb
  exact ⟨N, namedScope_held E rho hx i hN, he⟩




/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Scope for each inserted-tree member supplies StoreStepRoots. -/
theorem storeStepRoots_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (st : Store (Fin p.n))
    (B : FGBlock (Fin p.n))
    (hs : ∀ W ∈ insert B st.TF, RootBlockInRun p c E rho (eraseFG W)) :
    KitFG.StoreStepRoots st B := by
  rintro A D ⟨K, hK, hAK⟩ ⟨W, hW, hDW⟩ he
  exact rootInjectiveOn_run E rho hr (hs K hK) (hs W hW)
    A D (Or.inl hAK) (Or.inr hDW) he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. A stored non-genesis FG body has an earlier direct delivery.
This origin proof uses local invariants only, with no root premise or Base₂. -/
theorem stored_fg_body_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (V2.D.Run.stateBefore E rho i x).st.fg.TF) (hne : W ≠ .genesis) :
    ∃ s N, N.erase = eraseFG W ∧ W.rows = N.rows.filterMap RowWire.toRow? ∧
      ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver x o t) ∧
        o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  have hs := storeBundle_stateBefore E rho i x
  obtain ⟨s, N, hw, he, hr⟩ := stored_wire_of_block p _ hs.cstore hs.«meta» hW hne
  obtain ⟨j, o, t, hji, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hw
  refine ⟨s, N, he, hr, j, o, t, hji, hd, ?_⟩
  apply toWire_injective
  rw [toWire_ofWire, ho]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Any stored non-genesis body is a directly delivered proposal. -/
theorem stored_body_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) (hne : b ≠ .genesis) :
    ∃ j o t N, j < i ∧ rho.events[j]? = some (.deliver x o t) ∧
      o.payload = .proposal N ∧ N.erase = b := by
  obtain ⟨N, hN, he⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho i x)
    (metaInv_stateBefore E rho i x) b).mp hb
  have hn : N ≠ .genesis := by
    intro hn
    exact hne (he.symm.trans (congrArg NamedProposal.erase hn))
  obtain ⟨j, o, t, hj, hd, ho⟩ := stored_named_body_delivery E rho i x hN hn
  exact ⟨j, o, t, N, hj, hd, ho, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Non-genesis bodies at arbitrary nodes have delivery scope. -/
theorem rootBlockInRun_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) (hne : b ≠ .genesis) :
    RootBlockInRun p c E rho b := by
  obtain ⟨_, _, _, N, _, hd, ho, rfl⟩ := stored_body_delivery E rho i x hb hne
  exact rootBlockInRun_delivered E rho (List.mem_of_getElem? hd) ho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Every stored proposal body is in scope, at any node. -/
theorem rootBlockInRun_stored_proposal (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V)
    {s : Slot} {N : NamedProposal p.n}
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (rho.stateBefore E i x).st.proposals) : RootBlockInRun p c E rho N.erase :=
  ⟨N, namedScope_stored_proposal E rho i x hw, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Every ancestor of a prefix-held body is in that body store. -/
theorem stored_body_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {A B : Block}
    (hB : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks)
    (hAB : Block.Preceq A B) : A ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
  have hs := cstoreInv_stateBefore E rho i x
  obtain ⟨W, hW, rfl⟩ := (hs.baseTree B).mp hB
  obtain ⟨C, hC, he, _⟩ := eraseFG_ancestor_preceq hs.fg.closed hW hAB
  exact (hs.baseTree A).mpr ⟨C, hC, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. ROOT-DIGEST W2. An emitted proposal's parent was already in the emitter's
store.
The emitted tip itself need not be in the body scope. -/
theorem emitted_proposal_parent_stored (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V) (t : Time) (s : Slot)
    (N : NamedProposal p.n)
    (hi : rho.events[i]? = some (.tick x t))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E i) :
    N.parent ∈ (rho.stateBefore E i x).st.namedBodies := by
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hp := (fgsa_emits_proposal E rho _ x t s _).mp hem |>.2.2.2.2
  unfold propose at hp
  split at hp
  · cases hp
  · simp only [Option.map_map] at hp
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hp
    have hparent : N.parent = P := by
      have h := congrArg (fun m : Msg p.n =>
        match m with | .proposal M => M.parent | _ => .genesis) he
      exact h.symm
    have hm := (namedByErase?_sound _ _ P hP).1
    change P ∈ (clock p (rho.stateBefore E i x).st t).namedBodies at hm
    rw [clock_namedBodies] at hm
    simpa only [hparent] using hm


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. An emitted proposal with a slot digest has that small root. -/
theorem emitted_proposal_slot_root (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hdigest : ∀ d, p.digest d = ⟨d.slot + 1⟩)
    (i : Nat) (x : V) (t : Time) (s : Slot)
    (N : NamedProposal p.n)
    (hi : rho.events[i]? = some (.tick x t))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E i) :
    N.root = ⟨N.slot + 1⟩ := by
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hp := (fgsa_emits_proposal E rho _ x t s _).mp hem |>.2.2.2.2
  obtain ⟨H, raw, sup, rows, he, _, _⟩ := rowsOk_withApp _ _ _ hp
  cases Msg.proposal.inj he
  exact hdigest _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Delivery-parent origin closes the full body scope.
For NV, emitted_proposal_parent_stored supplies hparents. No root premise is used. -/
theorem rootBlockInRun_genesis_or_delivered (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → ∃ i y, N.parent ∈ (rho.stateBefore E i y).st.namedBodies)
    {A : Block} (hA : RootBlockInRun p c E rho A) :
    A = .genesis ∨ ∃ x o t N, V2.Event.deliver x o t ∈ rho.events ∧
      o.payload = .proposal N ∧ N.erase = A := by
  obtain ⟨N, hN, rfl⟩ := hA
  rcases namedProposalInRun_genesis_or_delivered E rho hparents hN with rfl | hd
  · exact Or.inl rfl
  · obtain ⟨x, o, t, hd, ho⟩ := hd
    exact Or.inr ⟨x, o, t, N, hd, ho, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. A predicate on genesis and delivered bodies covers the run scope.
NV can take Q to mean genesis or an actual fixture emission. -/
theorem rootBlockInRun_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → ∃ i y, N.parent ∈ (rho.stateBefore E i y).st.namedBodies)
    (Q : Block → Prop) (hgen : Q .genesis)
    (hdel : ∀ x o t N, V2.Event.deliver x o t ∈ rho.events →
      o.payload = .proposal N → Q N.erase)
    {A : Block} (hA : RootBlockInRun p c E rho A) : Q A := by
  obtain ⟨N, hN, rfl⟩ := hA
  exact namedProposalInRun_origin E rho hparents (fun N => Q N.erase) hgen hdel hN

end AvailableChain.FGSA.Run
end
