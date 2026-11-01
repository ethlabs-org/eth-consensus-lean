module
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
public import AvailableChainPCSAProofs.Proofs.Foundations.NamedScope
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! PC-SA scope laws and scoped roots for the generic FG safety lift (FG
finality safety, step S5b). Both FG modes. The scope is `RootBlockInRun`. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A parent precedes its block. -/
theorem pcsa_block_parent_preceq (A : Block) : Block.Preceq A.parent A := by
  cases A with
  | genesis => exact block_preceq_refl _
  | node P s r x =>
      have h : Block.preceq P P = true := block_preceq_refl P
      change (decide (P = Block.node P s r x) || Block.preceq P P) = true
      rw [h, Bool.or_true]

/-- Ancestry is kept by the parent step. -/
theorem pcsa_block_parent_preceq_parent {A B : Block} (h : Block.Preceq A B) :
    Block.Preceq A.parent B.parent := by
  cases B with
  | genesis =>
      change decide (A = Block.genesis) = true at h
      simp only [decide_eq_true_eq] at h
      subst h
      exact block_preceq_refl _
  | node P s r x =>
      change (decide (A = Block.node P s r x) || Block.preceq A P) = true at h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | h
      · exact block_preceq_refl _
      · exact block_preceq_trans (pcsa_block_parent_preceq A) h

/-- The PC-SA erasure commutes with the parent step. -/
theorem pcsa_eraseFG_parent (K : FGBlock (Fin p.n)) : (eraseFG K).parent = eraseFG K.parent := by
  rw [AvailableChain.PCSA.pcsa_eraseFG_eq, AvailableChain.PCSA.pcsa_eraseFG_eq]
  exact FGSA.eraseFG_parent K

/-- The core reads erase with the PC-SA erasure. -/
theorem pcsa_coreReadsWith_erase (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    (pcsaCoreReadsWith m p c).erase = eraseFG := by
  rw [pcsaCoreReadsWith_def]

/-- The safety reads take the raw proposal geometry. -/
theorem pcsa_safetyReads_proposalErase (m : FGMode) (p : Params) {In : Type}
    (c : AppCodec In) : (pcsaSafetyReads m p c).proposalErase = safetyProposalErase p := by
  rw [pcsaSafetyReads_def]

/-- A tick object carries one duty payload under that duty's own seat. -/
theorem pcsa_tick_mem (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (nd : Node p) (v : V) (t : Time) (o : Obj p) (h : o ∈ (V2.D.tick E rho nd v t).2) :
    ∃ d j q, o = (⟨.seat (RunDuty.signLabel d) j, q⟩ : Obj p) ∧
      actWith m p c ⟨PCSA.clock p nd.st t, nd.record⟩ d (rho.input v t) = some q := by
  have h' : o ∈ (if E.awake v t then
      (duties p t).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) v).filterMap
        (fun j => (actWith m p c ⟨PCSA.clock p nd.st t, nd.record⟩ d (rho.input v t)).map
          (fun q => (⟨.seat (RunDuty.signLabel d) j, q⟩ : Obj p)))) ++ []
      else ([] : List (Obj p))) := h
  split at h'
  · rw [List.append_nil] at h'
    obtain ⟨d, -, hd⟩ := List.mem_flatMap.mp h'
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hd
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hj
    exact ⟨d, j, q, rfl, hq⟩
  · exact (List.not_mem_nil h').elim

/-- An emitted proposal names a parent that its emitter held before the tick. -/
theorem pcsa_emits_proposal_parent (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {x : V} {o : Obj p} {t : Time}
    {N : NamedProposal p.n} (hem : V2.D.Run.emits E rho x o t)
    (ho : o.payload = .proposal N) :
    ∃ k, N.parent ∈ (V2.D.Run.stateBefore E rho k x).st.namedBodies := by
  obtain ⟨k, hk, hemit⟩ := hem
  have hmem := hemit
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at hmem
  obtain ⟨d, j, q, rfl, hq⟩ := pcsa_tick_mem m E rho _ x t o hmem
  change q = .proposal N at ho
  subst q
  cases d with
  | headAction s => cases m <;> cases hq
  | fgAction r =>
      cases m with
      | idle => cases hq
      | on =>
          obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hq
          cases he
  | ackAction s =>
      cases m <;>
      · obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hq
        cases he
  | propAction s =>
      have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim (α := Fin 1) _ _
      subst hj
      exact ⟨k, pcsa_emitted_proposal_parent E rho k x t s N hk hemit⟩

/-- Genesis is in the scope at an honest node. -/
theorem pcsa_safety_genesis_scope (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (hx : x ∈ rho.honest) :
    RootBlockInRun p c E rho ((pcsaCoreReadsWith m p c).erase .genesis) := by
  rw [pcsa_coreReadsWith_erase]
  exact ⟨.genesis, pcsa_namedScope_genesis E rho hx, rfl⟩

/-- A raw proposal read is a named proposal payload. -/
theorem pcsa_safetyProposalErase_some (o : Obj p) (b : Block)
    (h : safetyProposalErase p o = some b) :
    ∃ N, o.payload = .proposal N ∧ N.erase = b := by
  rw [pcsa_safetyProposalErase_def] at h
  cases hp : o.payload with
  | proposal N =>
      rw [hp] at h
      exact ⟨N, rfl, Option.some.inj h⟩
  | head r => rw [hp] at h; cases h
  | row a => rw [hp] at h; cases h
  | ack r => rw [hp] at h; cases h
  | pc d => rw [hp] at h; cases h

/-- Every delivered proposal, even a refused one, is in the scope. -/
theorem pcsa_safety_delivered_scope (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (o : Obj p) (t : Time) (b : Block)
    (hd : V2.Event.deliver x o t ∈ rho.events)
    (hb : (pcsaSafetyReads m p c).proposalErase o = some b) :
    RootBlockInRun p c E rho b := by
  rw [pcsa_safetyReads_proposalErase] at hb
  obtain ⟨N, hp, rfl⟩ := pcsa_safetyProposalErase_some o b hb
  exact ⟨N, pcsa_namedScope_delivered E rho hd hp, rfl⟩

/-- The parent of a run finality block is in the scope. -/
theorem pcsa_safety_parent_scope (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (K : FGBlock (Fin p.n))
    (hK : safetyRunBlock (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) E rho K)
    (hne : K.parent ≠ .genesis) :
    RootBlockInRun p c E rho ((pcsaCoreReadsWith m p c).erase K.parent) := by
  rw [pcsa_coreReadsWith_erase]
  obtain ⟨o, b, hb, hsrc, hKb⟩ := hK
  rw [pcsa_safetyReads_proposalErase] at hb
  rw [pcsa_coreReadsWith_erase] at hKb
  obtain ⟨N, hp, rfl⟩ := pcsa_safetyProposalErase_some o b hb
  rcases hsrc with ⟨x, t, hem⟩ | ⟨x, t, hd⟩
  · obtain ⟨k, hk⟩ := pcsa_emits_proposal_parent m E rho hem hp
    have hparent : Block.Preceq (eraseFG K.parent) N.parent.erase := by
      have h := pcsa_block_parent_preceq_parent hKb
      rwa [pcsa_eraseFG_parent, pcsa_named_erase_parent] at h
    rcases pcsa_namedBody_delivered E rho k x _ hk with hg | ⟨o', t', hd', hp'⟩
    · exfalso
      rw [hg] at hparent
      change decide (eraseFG K.parent = Block.genesis) = true at hparent
      have he : eraseFG K.parent = .genesis := of_decide_eq_true hparent
      rw [AvailableChain.PCSA.pcsa_eraseFG_eq] at he
      exact hne (FGSA.eraseFG_eq_genesis.mp he)
    · exact pcsa_rootBlockInRun_ancestor E rho
        ⟨N.parent, pcsa_namedScope_delivered E rho hd' hp', rfl⟩ hparent
  · have hPK : Block.Preceq (eraseFG K.parent) (eraseFG K) := by
      rw [← pcsa_eraseFG_parent]
      exact pcsa_block_parent_preceq _
    exact pcsa_rootBlockInRun_ancestor E rho ⟨N, pcsa_namedScope_delivered E rho hd hp, rfl⟩
      (block_preceq_trans hPK hKb)

/-- The PC-SA scope laws, in both FG modes. -/
theorem pcsaSafetyScopeLaws (m : FGMode) (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) :
    FGSafetyScopeLaws (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) E rho
      (RootBlockInRun p c E rho) where
  genesis_scope := pcsa_safety_genesis_scope m E rho
  delivered_scope := pcsa_safety_delivered_scope m E rho
  parent_scope := pcsa_safety_parent_scope m E rho

/-- Root collision freedom gives the scoped-roots law, in both FG modes. -/
theorem pcsa_safetyScopedRoots (m : FGMode) (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hr : NamedRootCollisionFree p c E rho) :
    safetyScopedRoots (pcsaCoreReadsWith m p c) (RootBlockInRun p c E rho) := by
  rw [safetyScopedRoots_def, pcsa_coreReadsWith_erase]
  intro K W hK hW
  exact pcsa_rootInjectiveOn_run E rho hr hK hW

end AvailableChain.PCSA.Run
end
