module
public import AvailableChainPCSAProofs.Proofs.Shared.FGStore
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
public import AvailableChainPCSA.Statements.Invariants
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.StoreLaws

public section
namespace AvailableChain.PCSA
open AvailableChain.SimplexFG
variable {n : Nat}

/-- The carried-PC deletion is before the FG update and changes only leases. -/
theorem pcsa_safety_delete_core (st : State n) (cert : PC n) :
    (deleteConflictingLeases st cert).fg = st.fg ∧
    (deleteConflictingLeases st cert).proposals = st.proposals ∧
    (deleteConflictingLeases st cert).rowPool = st.rowPool := by
  rw [deleteConflictingLeases_def]
  exact ⟨rfl, rfl, rfl⟩

/-- The parent lookup selects a stored block with the exact erased parent. -/
theorem pcsa_safety_parentFG_spec {n : Nat} (st : State n) (b : Block)
    (P : FGBlock (Fin n)) (h : parentFG st b = some P) :
    P ∈ st.fg.TF ∧ eraseFG P = b.parent := by
  change pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent)) = some P at h
  unfold pickPair at h
  split at h
  · next hu =>
    cases h
    obtain ⟨hm, he⟩ :=
      Finset.choose_spec (fun P => decide (eraseFG P = b.parent) = true) st.fg.TF hu
    exact ⟨hm, of_decide_eq_true he⟩
  · cases h

/-- Admission checks freshness and the exact packed proposal content. -/
theorem pcsa_safety_blockAccepted_facts {p : Params} {st : State p.n} {s : Slot}
    {N : NamedProposal p.n} {P : FGBlock (Fin p.n)}
    (h : blockAccepted p st s N P = true) :
    N.erase ≠ .genesis ∧ (¬ ∃ Y ∈ st.fg.TF, Y.root = N.erase.root) ∧
      namedContentOk p N = true := by
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.2⟩

/-- Packed signed rows reconstruct the delivered geometric body exactly. -/
theorem pcsa_safety_eraseFG_fgBlock {p : Params} {P : FGBlock (Fin p.n)}
    {N : NamedProposal p.n} (hne : N.erase ≠ .genesis)
    (hP : eraseFG P = N.erase.parent) (hc : namedContentOk p N = true) :
    eraseFG (fgBlock P N.erase N.rows) = N.erase := by
  change (N.erase.body == packBody (appOf N.erase.body) N.rows &&
    N.erase.root == digestOf p (proposalInput N.erase N.raw N.support N.rows N.pc)) = true at hc
  have hb := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
  generalize he : N.erase = b at *
  cases b with
  | genesis => exact (hne rfl).elim
  | node q s r x =>
    change Block.node (eraseFG P) s r (packBody (appOf x) N.rows) = Block.node q s r x
    change x = packBody (appOf x) N.rows at hb
    rw [hP, ← hb]
    rfl

/-- Admission proves root uniqueness on the inserted tree from local store facts. -/
theorem pcsa_safety_storeStepRoots (p : Params) (st : State p.n)
    (h : KitFG.FGStoreInvariant (FGSA.heightView p) (pcsa_finalityView p) st.fg)
    (hi : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y)
    (s : Slot) (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hp : parentFG st N.erase = some P) (ha : blockAccepted p st s N P = true) :
    KitFG.StoreStepRoots st.fg (fgBlock P N.erase N.rows) := by
  have hm := (pcsa_safety_parentFG_spec st N.erase P hp).1
  have hf := (pcsa_safety_blockAccepted_facts ha).2.1
  apply FGSA.viewRootInj_of_rootInj
  · intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_insert_of_mem hm
    · exact Finset.mem_insert_of_mem (h.closed X hX)
  · intro X hX Y hY hr
    rcases Finset.mem_insert.mp hX with rfl | hX <;>
      rcases Finset.mem_insert.mp hY with rfl | hY
    · rfl
    · exact False.elim (hf ⟨Y, hY, hr.symm⟩)
    · exact False.elim (hf ⟨X, hX, hr⟩)
    · exact hi X hX Y hY hr

/-- The window either keeps TF or inserts the supplied block. -/
theorem pcsa_safety_window_TF_cases (p : Params) (st : Store (Fin p.n))
    (B : FGBlock (Fin p.n)) :
    (FGSA.Window.on_block p p.K_W st B).TF = st.TF ∨
      (FGSA.Window.on_block p p.K_W st B).TF = insert B st.TF := by
  rw [FGSA.Window.on_block_def]
  split
  · exact Or.inl rfl
  · exact Or.inr (FGSA.Window.window_update_finality_TF p p.K_W _ B)

/-- Reachability supplies both the FG invariant and local root uniqueness. -/
theorem pcsa_safety_storeInvariant (p : Params) (st : State p.n) (hr : Reachable p st) :
    KitFG.FGStoreInvariant (FGSA.heightView p) (pcsa_finalityView p) st.fg ∧
      (∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y) := by
  induction hr with
  | init =>
    refine ⟨(FGSA.fgStoreSafety p).initial_good, ?_⟩
    intro X hX Y hY _
    exact (Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hY).symm
  | tick t hr ih =>
    rw [pcsa_clock_fg]
    exact ih
  | @deliver st o hr ih =>
    rcases pcsa_safety_process_fg_cases p st o with he | ⟨s, N, P, _, hp, ha, he⟩
    · rw [he]
      exact ih
    · rw [he]
      have hs := pcsa_safety_storeStepRoots p st ih.1 ih.2 s N P hp ha
      refine ⟨(FGSA.fgStoreSafety p).step_good st.fg _ ih.1 hs, ?_⟩
      intro X hX Y hY heq
      rcases pcsa_safety_window_TF_cases p st.fg (fgBlock P N.erase N.rows) with ht | ht
      · rw [ht] at hX hY
        exact ih.2 X hX Y hY heq
      · rw [ht] at hX hY
        exact hs X Y ⟨X, hX, KitFG.preceq_refl X⟩ ⟨Y, hY, KitFG.preceq_refl Y⟩ heq

/-- A new TF member has the exact delivered proposal and decoded row list. -/
theorem pcsa_safety_process_TF_new (p : Params) (st : State p.n) (o : Wire p.n)
    (B : FGBlock (Fin p.n)) (hb : B ∈ (process p st o).fg.TF) (hold : B ∉ st.fg.TF) :
    ∃ s N, o.decode = some (.block s N) ∧
      eraseFG B = N.erase ∧ B.rows = N.rows.filterMap RowWire.toRow? := by
  rcases pcsa_safety_process_fg_cases p st o with he | ⟨s, N, P, hd, hp, ha, he⟩
  · exact (hold (he ▸ hb)).elim
  · rw [he] at hb
    rcases pcsa_safety_window_TF_cases p st.fg (fgBlock P N.erase N.rows) with ht | ht
    · exact (hold (ht ▸ hb)).elim
    · rw [ht] at hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · have hf := pcsa_safety_blockAccepted_facts ha
        exact ⟨s, N, hd, pcsa_safety_eraseFG_fgBlock hf.1
          (pcsa_safety_parentFG_spec st N.erase P hp).2 hf.2.2, rfl⟩
      · exact (hold hb).elim

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose
variable {p : Params}

theorem pcsa_safety_finalityView_eq (p : Params) :
    pcsa_finalityView p = FGSA.finalityView p := rfl

theorem pcsaSafetyCertificateLaws (p : Params) :
    KitFG.FGCertificateLaws p.E (FGSA.heightView p) (pcsa_finalityView p) := by
  rw [pcsa_safety_finalityView_eq]
  exact FGSA.fgCertificateLaws p

theorem pcsa_safety_initial_tf (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (B : FGBlock (Fin p.n)) (h : B ∈ ((pcsaCoreReadsWith m p c).core (pcsaWith m p c).init).fg.TF) :
    B = .genesis := by
  rw [pcsaCoreReadsWith_def] at h
  change B ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at h
  exact Finset.mem_singleton.mp h

theorem pcsa_safety_restart_tf (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith m p c).core
      ((pcsaWith m p c).restore ((pcsaWith m p c).durable nd))).fg.TF) : B = .genesis := by
  rw [pcsaCoreReadsWith_def] at h
  change B ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at h
  exact Finset.mem_singleton.mp h

/-- The two independent order fields remain valid in both modes. -/
theorem pcsa_safety_erase_prefix (A B : FGBlock (Fin p.n)) (h : FGBlock.Preceq A B) :
    Block.Preceq (PCSA.eraseFG A) (PCSA.eraseFG B) := by
  rw [pcsa_eraseFG_eq]
  exact FGSA.eraseFG_preceq h

theorem pcsa_safety_output_eq (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) : (pcsaSafetyReads m p c).finalizedOut nd =
      (pcsaCoreReadsWith m p c).erase ((pcsaCoreReadsWith m p c).core nd).fg.F := by
  rw [pcsaSafetyReads_def, pcsaCoreReadsWith_def]

/-- Store processing is independent of the honest FG duty mode. -/
theorem pcsa_safety_process_F (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) :
    FGBlock.Preceq ((pcsaCoreReadsWith m p c).core nd).fg.F
      ((pcsaCoreReadsWith m p c).core ((pcsaWith m p c).process nd o)).fg.F := by
  rw [pcsaCoreReadsWith_def]
  change FGBlock.Preceq nd.st.fg.F (PCSA.process p nd.st (toWire p o)).fg.F
  exact pcsa_process_F_mono p nd.st (toWire p o)

/-- All three order fields hold in both FG duty modes. -/
theorem pcsaSafetyOrderLaws (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) where
  process_F := pcsa_safety_process_F m p c
  erase_prefix := by
    intro A B h
    rw [pcsaCoreReadsWith_def]
    exact pcsa_safety_erase_prefix (p := p) A B h
  output_eq := pcsa_safety_output_eq m p c

/-- All core laws hold for either honest FG duty mode. -/
theorem pcsaCoreLawsWith (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (pcsaCoreReadsWith m p c) where
  clock_fg := by
    intro nd t
    rw [pcsaCoreReadsWith_def]
    exact pcsa_clock_fg p nd.st t
  clock_proposals := by
    intro nd t
    rw [pcsaCoreReadsWith_def]
    exact (pcsa_safety_clock_metadata p nd.st t).1
  clock_rowPool := by
    intro nd t
    rw [pcsaCoreReadsWith_def]
    exact (pcsa_safety_clock_metadata p nd.st t).2
  process_tf := by
    intro nd o
    rw [pcsaCoreReadsWith_def]
    exact pcsa_safety_process_TF p nd.st (toWire p o)
  process_proposals := by
    intro nd o
    rw [pcsaCoreReadsWith_def]
    exact (pcsa_safety_process_metadata p nd.st (toWire p o)).1
  process_rowPool := by
    intro nd o
    rw [pcsaCoreReadsWith_def]
    exact (pcsa_safety_process_metadata p nd.st (toWire p o)).2
  own_core := pcsa_safety_own_core m p c
  source_mem := by
    intro nd B h
    rw [pcsaCoreReadsWith_def]
    exact pcsa_safety_source_mem m p c nd B h
  erase_inj := by
    rw [pcsaCoreReadsWith_def, pcsa_eraseFG_eq]
    exact FGSA.eraseFG_injective

/-- New FG tree members use the delivered raw proposal and its exact rows. -/
theorem pcsa_safety_process_new (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) (B : FGBlock (Fin p.n))
    (hb : B ∈ ((pcsaCoreReadsWith m p c).core ((pcsaWith m p c).process nd o)).fg.TF)
    (hold : B ∉ ((pcsaCoreReadsWith m p c).core nd).fg.TF) :
    (pcsaSafetyReads m p c).proposalErase o = some ((pcsaCoreReadsWith m p c).erase B) ∧
      B.rows = ((pcsaSafetyReads m p c).proposalRows o).filterMap
        (pcsaSafetyReads m p c).decode := by
  rw [pcsaCoreReadsWith_def] at hb hold
  obtain ⟨s, N, hd, he, hr⟩ := pcsa_safety_process_TF_new p nd.st (toWire p o) B hb hold
  have hp : o.payload = .proposal N := pcsa_safety_decode_block_payload (toWire p o) s N hd
  rw [pcsaSafetyReads_def, pcsaCoreReadsWith_def]
  change safetyProposalErase p o = some (PCSA.eraseFG B) ∧
    B.rows = (safetyProposalRows p o).filterMap RowWire.toRow?
  rw [pcsa_safetyProposalErase_def, pcsa_safetyProposalRows_def, hp]
  exact ⟨congrArg some he.symm, hr⟩

/-- Reachability supplies the store laws without any run or root premise. -/
theorem pcsaSafetyStoreLaws (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyStoreLaws (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c)
      (FGSA.heightView p) (pcsa_finalityView p) (fun nd => Reachable p nd.st) where
  initial_good := Reachable.init
  clock_good := fun _ t h => Reachable.tick t h
  process_good := fun _ o h => Reachable.deliver (toWire p o) h
  own_good := fun _ _ h => h
  restart_good := fun _ _ => Reachable.init
  invariant := by
    intro nd h
    rw [pcsaCoreReadsWith_def]
    exact (pcsa_safety_storeInvariant p nd.st h).1
  initial_tf := pcsa_safety_initial_tf m p c
  restart_tf := fun nd B _ => pcsa_safety_restart_tf m p c nd B
  process_new := fun nd o B _ => pcsa_safety_process_new m p c nd o B


end AvailableChain.PCSA.Run
end
