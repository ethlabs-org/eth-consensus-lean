module
public import AvailableChainFGCompose.Proofs.HistoricalReads
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGSA.Proofs.NamedReachable
public import AvailableChainFGSA.Proofs.Restart

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0HistoricalReads
open AvailableChain.SimplexFG

private def p0c4_reads (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoricalReads (fgsa p c).State (NamedProposal p.n) where
  acceptedBlocks nd := nd.st.base.blocks.toFinset
  acceptedBodies nd := nd.st.namedBodies
  erase := NamedProposal.erase
  root := NamedProposal.root
  parent := NamedProposal.parent
  slot := NamedProposal.slot
  readBlock nd r := FGCompose.historicalLookup NamedProposal.root nd.st.namedBodies r
  preceq b c := Block.Preceq b.erase c.erase
  depth b := b.erase.depth
  lca b c := Block.meet b.erase c.erase

private theorem p0c4_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoricalLaws (fgsaCoreReads p c) (p0c4_reads p c)
      (fun nd => Reachable p nd.st) where
  blocks_eq nd hg := by
    rw [fgsaCoreReads_def]
    ext B
    simp only [p0c4_reads, List.mem_toFinset, Finset.mem_image]
    exact (storeInvariant p nd.st hg).baseTree B
  bodies_eq nd hg B := by
    simpa only [p0c4_reads, List.mem_toFinset] using (reachable_named_store p hg).2.1 B
  root_eq b := (named_erase_root b).symm
  parent_eq b := (named_erase_parent b).symm
  slot_eq b := (named_erase_slot b).symm
  parent_closed nd hg := (reachable_named_store p hg).1
  read_iff nd r b := FGCompose.historicalLookup_spec _ _ r b
  reachable_unique nd hg := (reachable_named_store p hg).2.2.2.1
  geometry_eq := ⟨fun _ _ => Iff.rfl, fun _ => rfl, fun _ _ => rfl⟩
  step_keep nd nd' step b hb := by
    change b ∈ nd.st.namedBodies at hb
    cases step with
    | process o =>
      rcases (mem_namedBodies nd.st b).mp hb with h | ⟨s, hs⟩
      · exact (mem_namedBodies _ b).mpr (Or.inl h)
      · exact (mem_namedBodies _ b).mpr (Or.inr ⟨s,
          (process_cumulative p nd.st (toWire p o)).2.2.2.2.1.subset hs⟩)
    | own o => exact hb
    | clock t =>
      change b ∈ (clock p nd.st t).namedBodies
      rwa [clock_namedBodies]
    | restore t =>
      change b ∈ (acRestart p nd.st t).namedBodies
      simpa only [State.namedBodies, acRestart_proposals] using hb
  restore_eq nd t := by
    change (acRestart p nd.st t).namedBodies = nd.st.namedBodies ∧
      (acRestart p nd.st t).base.blocks.toFinset = nd.st.base.blocks.toFinset
    simp only [State.namedBodies, acRestart_proposals, acRestart_blocks, and_self]
  frame_independent nd nd' he r := by
    exact congrArg (fun bs => FGCompose.historicalLookup NamedProposal.root bs r) he

private def p0c4_row : RowWire 4 :=
  ⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩

private def p0c4_inputs : List (DigestInput 4) :=
  [⟨genesisRoot, 1, 0, [], [], []⟩,
   ⟨⟨1⟩, 2, 1, [p0c4_row], [], []⟩,
   ⟨⟨1⟩, 3, 2, [], [], []⟩]

private def p0c4_digest (d : DigestInput 4) : BlockId :=
  ⟨p0c4_inputs.findIdx (fun e => e == d) + 1⟩

private abbrev p0c4_params : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := p0c4_digest }

private def p0c4_P : NamedProposal 4 :=
  .node .genesis 1 ⟨1⟩ (packBody (n := 4) 0 []) [] [] []
private def p0c4_B : NamedProposal 4 :=
  .node p0c4_P 2 ⟨2⟩ (packBody 1 [p0c4_row]) [] [] [p0c4_row]
private def p0c4_C : NamedProposal 4 :=
  .node p0c4_P 3 ⟨3⟩ (packBody (n := 4) 2 []) [] [] []

private def p0c4_wire (b : NamedProposal 4) : Wire 4 := ⟨.proposer b.slot, .proposal b⟩
private def p0c4_store : State 4 :=
  process p0c4_params (process p0c4_params (process p0c4_params
    (clock p0c4_params (initial 4) 20) (p0c4_wire p0c4_P))
      (p0c4_wire p0c4_B)) (p0c4_wire p0c4_C)
private def p0c4_node : Node p0c4_params := ⟨p0c4_store, RecordOnce.initial⟩

private theorem p0c4_reachable : Reachable p0c4_params p0c4_store :=
  .deliver _ (.deliver _ (.deliver _ (.tick _ .init)))

/-- The digest table is injective on the finite admitted full inputs only. -/
private theorem p0c4_finite_digest : p0c4_inputs.Nodup ∧
    (∀ d ∈ p0c4_inputs, ∀ e ∈ p0c4_inputs, p0c4_digest d = p0c4_digest e → d = e) := by
  decide +kernel

private theorem p0c4_valid_payload :
    RowWire.valid p0c4_row = true ∧
    wellFormed p0c4_params (p0c4_wire p0c4_B) = true ∧
    appOf p0c4_B.body = 1 ∧ p0c4_B.rows = [p0c4_row] ∧
    p0c4_B.parent = p0c4_P ∧ p0c4_B.slot = 2 := by decide +kernel

private theorem p0c4_members :
    p0c4_P ∈ p0c4_store.namedBodies ∧ p0c4_B ∈ p0c4_store.namedBodies ∧
    p0c4_C ∈ p0c4_store.namedBodies := by decide +kernel

private theorem p0c4_exact_read :
    (p0c4_reads p0c4_params unitCodec).readBlock p0c4_node p0c4_B.root = some p0c4_B :=
  FGCompose.historical_read_complete (p0c4_laws p0c4_params unitCodec)
    (st := p0c4_node) (b := p0c4_B) p0c4_reachable p0c4_members.2.1

/-- This changes frame controls on the reachable accepted store, not its storage. -/
private def p0c4_filtered : Node p0c4_params :=
  { p0c4_node with st := { p0c4_store with
      fg := { p0c4_store.fg with h_max := 100, h_j := 100 } } }

private theorem p0c4_frame_excludes :
    (∃ B ∈ p0c4_store.fg.TF, eraseFG B = p0c4_B.erase) ∧
      ¬ (∃ B ∈ fullTree p0c4_params p0c4_filtered.st, eraseFG B = p0c4_B.erase) := by
  decide +kernel

private theorem p0c4_frame_read :
    (p0c4_reads p0c4_params unitCodec).readBlock p0c4_filtered p0c4_B.root =
      some p0c4_B := by
  rw [FGCompose.historical_read_frame_eq (p0c4_laws p0c4_params unitCodec)
    (st := p0c4_filtered) (st' := p0c4_node) rfl]
  exact p0c4_exact_read

private theorem p0c4_restart_read (t : Time) :
    (p0c4_reads p0c4_params unitCodec).readBlock
      ((fgsa p0c4_params unitCodec).restore
        ((fgsa p0c4_params unitCodec).durable p0c4_filtered) t) p0c4_B.root =
      some p0c4_B := by
  rw [FGCompose.historical_read_restore_eq (p0c4_laws p0c4_params unitCodec)
    p0c4_filtered t p0c4_B.root]
  exact p0c4_frame_read

private theorem p0c4_parent_read :
    (p0c4_reads p0c4_params unitCodec).readBlock p0c4_node p0c4_B.parent.root =
      some p0c4_P :=
  (FGCompose.historical_parent_held (p0c4_laws p0c4_params unitCodec)
    (st := p0c4_node) (b := p0c4_B) p0c4_reachable p0c4_members.2.1).2

private theorem p0c4_depth_and_meet :
    (p0c4_reads p0c4_params unitCodec).depth p0c4_B = 2 ∧
    Block.Preceq p0c4_P.erase p0c4_B.erase ∧
    (p0c4_reads p0c4_params unitCodec).lca p0c4_B p0c4_C = p0c4_P.erase ∧
    p0c4_P.erase ≠ .genesis := by decide +kernel

private theorem p0c4_lca_read :
    ∃ d ∈ p0c4_store.namedBodies, d.erase = p0c4_P.erase ∧
      (p0c4_reads p0c4_params unitCodec).readBlock p0c4_node d.root = some d := by
  have h := FGCompose.historical_lca_held (p0c4_laws p0c4_params unitCodec)
    (st := p0c4_node) (b := p0c4_B) (c := p0c4_C)
    p0c4_reachable p0c4_members.2.1 p0c4_members.2.2
  rw [p0c4_depth_and_meet.2.2.1] at h
  exact h

private theorem p0c4_clock_read (t : Time) :
    (p0c4_reads p0c4_params unitCodec).readBlock
      ((fgsa p0c4_params unitCodec).clock p0c4_node t) p0c4_B.root = some p0c4_B := by
  apply FGCompose.historical_read_step (p0c4_laws p0c4_params unitCodec)
    (.clock p0c4_node t) (.tick t p0c4_reachable) p0c4_exact_read

private def p0c4_alias : NamedProposal 4 :=
  .node .genesis 2 p0c4_B.root (packBody (n := 4) 2 []) [] [] []
private def p0c4_malformed : Node p0c4_params :=
  ⟨{ initial 4 with proposals := [p0c4_wire p0c4_B, p0c4_wire p0c4_alias] },
    RecordOnce.initial⟩

private theorem p0c4_named_ambiguity :
    p0c4_B ≠ p0c4_alias ∧ p0c4_B.root = p0c4_alias.root ∧
      (p0c4_reads p0c4_params unitCodec).readBlock p0c4_malformed p0c4_B.root = none := by
  decide +kernel

private theorem p0c4_named_frame_ambiguity (nd : Node p0c4_params)
    (he : nd.st.namedBodies = p0c4_malformed.st.namedBodies) :
    (p0c4_reads p0c4_params unitCodec).readBlock nd p0c4_B.root = none := by
  rw [FGCompose.historical_read_frame_eq (p0c4_laws p0c4_params unitCodec) he]
  exact p0c4_named_ambiguity.2.2

private theorem p0c4_named_missing_repeated :
    (p0c4_reads p0c4_params unitCodec).readBlock p0c4_node ⟨99⟩ = none ∧
      FGCompose.historicalLookup NamedProposal.root [p0c4_B, p0c4_B] p0c4_B.root =
        some p0c4_B := by decide +kernel

private theorem p0c4_process_read (o : Obj p0c4_params) :
    (p0c4_reads p0c4_params unitCodec).readBlock
      ((fgsa p0c4_params unitCodec).process p0c4_node o) p0c4_B.root = some p0c4_B := by
  apply FGCompose.historical_read_step (p0c4_laws p0c4_params unitCodec)
    (.process p0c4_node o) ?_ p0c4_exact_read
  exact .deliver (toWire p0c4_params o) p0c4_reachable

private theorem p0c4_own_read (o : Obj p0c4_params) :
    (p0c4_reads p0c4_params unitCodec).readBlock
      ((fgsa p0c4_params unitCodec).recordOwn p0c4_node o) p0c4_B.root = some p0c4_B := by
  apply FGCompose.historical_read_step (p0c4_laws p0c4_params unitCodec)
    (.own p0c4_node o) ?_ p0c4_exact_read
  exact p0c4_reachable

private theorem p0c4_restart_geometry (t : Time) :
    (acRestart p0c4_params p0c4_store t).fg = p0c4_store.fg ∧
      (p0c4_reads p0c4_params unitCodec).acceptedBlocks
        ((fgsa p0c4_params unitCodec).restore
          ((fgsa p0c4_params unitCodec).durable p0c4_node) t) =
        (p0c4_reads p0c4_params unitCodec).acceptedBlocks p0c4_node :=
  ⟨acRestart_fg _ _ _,
    (FGCompose.historical_geometry_restore_eq (p0c4_laws p0c4_params unitCodec)
      p0c4_node t).2⟩

#print axioms p0c4_named_ambiguity
#print axioms p0c4_named_frame_ambiguity
#print axioms p0c4_named_missing_repeated
#print axioms p0c4_process_read
#print axioms p0c4_own_read
#print axioms p0c4_restart_geometry

#print axioms p0c4_reads
#print axioms p0c4_laws
#print axioms p0c4_reachable
#print axioms p0c4_finite_digest
#print axioms p0c4_valid_payload
#print axioms p0c4_members
#print axioms p0c4_exact_read
#print axioms p0c4_frame_excludes
#print axioms p0c4_frame_read
#print axioms p0c4_restart_read
#print axioms p0c4_parent_read
#print axioms p0c4_depth_and_meet
#print axioms p0c4_lca_read
#print axioms p0c4_clock_read

end AvailableChain.FGSA.Run.Tests.P0HistoricalReads
end
