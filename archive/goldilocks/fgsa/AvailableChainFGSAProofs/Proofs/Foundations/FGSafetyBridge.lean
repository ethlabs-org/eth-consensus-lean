module
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGCompose.Proofs.SafetyCount
public import AvailableChainFGCompose.Proofs.SafetyMonotone
public import AvailableChainFGCompose.Proofs.SafetySlashing
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope
public import AvailableChainFGSARun.Statements.Slashing

public section

/-! FG finality safety, steps S4a and S4b: the generic results (fields 3 to 8)
at the FG-SA reads. `Accountable` imports this module, so the statements
expand `FinalityRunBlock` and `FinalityCarriage` instead of naming them. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem bridge_proposalErase_some {o : Obj p} {b : Block}
    (h : safetyProposalErase p o = some b) :
    ∃ N, o.payload = .proposal N ∧ N.erase = b := by
  rw [fgsa_safetyProposalErase_def] at h
  cases hp : o.payload with
  | proposal N =>
      simp only [hp, Option.some.injEq] at h
      exact ⟨N, rfl, h⟩
  | _ => simp [hp] at h

private theorem bridge_proposalErase_of {o : Obj p} {N : NamedProposal p.n}
    (ho : o.payload = .proposal N) : safetyProposalErase p o = some N.erase := by
  rw [fgsa_safetyProposalErase_def, ho]

/-- The Compose run block at the FG-SA reads is the body of `FinalityRunBlock`. -/
private theorem bridge_runBlock_iff (K : FGBlock (Fin p.n)) :
    safetyRunBlock (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho K ↔
      ∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase := by
  rw [safetyRunBlock_def, fgsaCoreReads_def, fgsaSafetyReads_def]
  constructor
  · rintro ⟨o, b, he, hrun, hKb⟩
    obtain ⟨N, ho, rfl⟩ := bridge_proposalErase_some p he
    exact ⟨o, N, ho, hrun, hKb⟩
  · rintro ⟨o, N, ho, hrun, hKb⟩
    refine ⟨o, N.erase, ?_, hrun, hKb⟩
    exact bridge_proposalErase_of p ho

/-- Field 3 (Compose form) at the FG-SA reads. -/
private theorem bridge_wholeAccountable (hroots : NamedRootCollisionFree p c E rho) :
    SafetyWholeAccountable (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E (finalityView p)
      E rho :=
  safety_run_accountable _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c) (fgsaSafetyStoreLaws p c)
    (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots)

/-- The all-run bound in expanded FG-SA form is the Compose bound. -/
private theorem bridge_bound_of
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) :
    safetyBound (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E E rho := by
  rw [safetyBound_def]
  exact fun K W hK hW => hb K W ((bridge_runBlock_iff p c E rho K).1 hK)
    ((bridge_runBlock_iff p c E rho W).1 hW)

/-- Two run blocks: slashable weight between their chains, or compatible
finalized targets. -/
theorem fgsa_bridge_runAccountable (hroots : NamedRootCollisionFree p c E rho)
    {K W : FGBlock (Fin p.n)}
    (hK : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG K) N.erase)
    (hW : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG W) N.erase) :
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible (finalityView p K).F (finalityView p W).F = true :=
  safety_runBlock_accountable (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) ((bridge_runBlock_iff p c E rho K).2 hK)
    ((bridge_runBlock_iff p c E rho W).2 hW)

/-- A non-genesis parent of a run block is in the named scope of the run. -/
theorem fgsa_bridge_parent_scope {K : FGBlock (Fin p.n)}
    (hK : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG K) N.erase)
    (hne : K.parent ≠ .genesis) :
    RootBlockInRun p c E rho (eraseFG K.parent) := by
  have h := (fgsaSafetyScopeLaws p c E rho).parent_scope K
    ((bridge_runBlock_iff p c E rho K).2 hK) hne
  rw [fgsaCoreReads_def] at h
  exact h

/-- Every block of an honest time read is in the named scope of the run. -/
theorem fgsa_bridge_read_scope (t : Time) (x : V) (hx : x ∈ rho.honest)
    (K : FGBlock (Fin p.n)) (hK : K ∈ (V2.D.Run.readAt E rho t x).st.fg.TF) :
    RootBlockInRun p c E rho (eraseFG K) := by
  have h := safety_read_scope (fgsaCoreLaws p c) (fgsaSafetyStoreLaws p c)
    (fgsaSafetyScopeLaws p c E rho) t x hx K (by rw [fgsaCoreReads_def]; exact hK)
  rw [fgsaCoreReads_def] at h
  exact h

/-- Field 3, event prefixes: two honest stores before any events. -/
theorem fgsa_bridge_stores_accountable (hroots : NamedRootCollisionFree p c E rho)
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (i j : Nat) :
    HasSlashableWeightBetween p.E
        ((V2.D.Run.stateBefore E rho i u).st.fg.TF.biUnion chainRows)
        ((V2.D.Run.stateBefore E rho j v).st.fg.TF.biUnion chainRows) ∨
      FGBlock.compatible (V2.D.Run.stateBefore E rho i u).st.fg.F
        (V2.D.Run.stateBefore E rho j v).st.fg.F = true := by
  have h := bridge_wholeAccountable p c E rho hroots
  rw [SafetyWholeAccountable_def] at h
  have h' := h.2.1 u hu v hv i j
  rw [safetyRows_def, safetyRows_def, fgsaCoreReads_def] at h'
  exact h'

/-- Field 3, reads: two honest time reads. -/
theorem fgsa_bridge_reads_accountable (hroots : NamedRootCollisionFree p c E rho)
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (t t' : Time) :
    HasSlashableWeightBetween p.E
        ((V2.D.Run.readAt E rho t u).st.fg.TF.biUnion chainRows)
        ((V2.D.Run.readAt E rho t' v).st.fg.TF.biUnion chainRows) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true := by
  have h := bridge_wholeAccountable p c E rho hroots
  rw [SafetyWholeAccountable_def] at h
  have h' := h.2.2 u hu v hv t t'
  rw [safetyRows_def, safetyRows_def, fgsaCoreReads_def] at h'
  exact h'

/-- Field 5: under the all-run bound, any two event prefixes agree. -/
theorem fgsa_bridge_event_agreement (hroots : NamedRootCollisionFree p c E rho)
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W))
    (i j : Nat) (x y : V) :
    FGBlock.compatible (V2.D.Run.stateBefore E rho i x).st.fg.F
      (V2.D.Run.stateBefore E rho j y).st.fg.F = true := by
  have h := safety_event_agreement _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c)
    (fgsaSafetyStoreLaws p c) (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) (bridge_bound_of p c E rho hb) i j x y
  rw [fgsaCoreReads_def] at h
  exact h

/-- Field 4, reads: under the all-run bound, two honest time reads agree. -/
theorem fgsa_bridge_read_agreement (hroots : NamedRootCollisionFree p c E rho)
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W))
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (t t' : Time) :
    FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
      (V2.D.Run.readAt E rho t' v).st.fg.F = true := by
  have h := safety_run_agreement _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c)
    (fgsaSafetyStoreLaws p c) (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) (bridge_bound_of p c E rho hb)
  rw [SafetyWholeAgreement_def] at h
  have h' := h.2 u hu v hv t t'
  rw [fgsaCoreReads_def] at h'
  exact h'

/-! S4b: client safety, fault count, finalized monotonicity and slashing. -/

private theorem bridge_fg_linked : (fgsaFamilies p c).linked (fgsaSafetyReads p c).fgLabel := by
  rw [fgsaSafetyReads_def]
  trivial

omit [DecidableEq V] in
private theorem bridge_holder (i : Fin p.n) :
    safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem bridge_emits_iff (x : V) (a : RowWire p.n) :
    safetyEmits (fgsaSafetyReads p c) E rho x a ↔ EmitsRow p c E rho x a := by
  rw [safetyEmits_def, fgsaSafetyReads_def]
  exact Iff.rfl

/-- The Compose no-slash read at the FG-SA reads is `EmittedRowsNoSlash`. -/
private theorem bridge_noSlash_iff (x : V) :
    safetyNoSlash (fgsaSafetyReads p c) E rho x ↔ EmittedRowsNoSlash p c E rho x := by
  rw [safetyNoSlash_def, fgsaSafetyReads_def]
  exact Iff.rfl

/-- A set of rows with signed wires that their honest signers emitted is carried. -/
private theorem bridge_carriage_of (A : Finset (Row (Fin p.n)))
    (h : ∀ u ∈ A, ∃ a : RowWire p.n, a.toRow? = some u ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a) :
    safetyCarriage (fgsaSafetyReads p c) E rho A := by
  rw [safetyCarriage_def]
  intro u hu
  obtain ⟨a, hau, hem⟩ := h u hu
  have hsign : RowSigner p c rho a (rho.seatOf (.base .fg) u.signer) := by
    rw [RowSigner_def]
    exact ⟨u.signer, row_auth_of_toRow a u hau, rfl⟩
  have hdec : (fgsaSafetyReads p c).decode a = some u := by
    rw [fgsaSafetyReads_def]
    exact hau
  refine ⟨a, hdec, fun hh => ?_⟩
  rw [bridge_holder] at hh ⊢
  exact (bridge_emits_iff p c E rho _ a).2 (hem _ hsign hh)

/-- Two carried row sets with slashable weight have at least `2 q_F − n`
faulty holders. -/
theorem fgsa_bridge_pool_count [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (A B : Finset (Row (Fin p.n)))
    (hA : ∀ u ∈ A, ∃ a : RowWire p.n, a.toRow? = some u ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a)
    (hB : ∀ u ∈ B, ∃ a : RowWire p.n, a.toRow? = some u ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a)
    (hev : HasSlashableWeightBetween p.E A B) :
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.Duty.faulty rho).card :=
  safety_slashable_faulty_count (fgsaSafetyReads p c) p.E E rho (fgsaSafetyUnitLaws p)
    (fgsaFamilies p c).linked (bridge_fg_linked p c) hL
    (fun z hz => (bridge_noSlash_iff p c E rho z).2 (hC z hz))
    (bridge_carriage_of p c E rho A hA) (bridge_carriage_of p c E rho B hB) hev

/-- Field 6: carriage of every run block, client safety and the one-third
fault bound exclude slashable weight between run blocks. -/
theorem fgsa_bridge_slashableBound_of_faults [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hbot : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (hcar : ∀ K,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      ∀ u ∈ chainRows K, ∃ a : RowWire p.n, a.toRow? = some u ∧
        ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a)
    (K W : FGBlock (Fin p.n))
    (hK : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG K) N.erase)
    (hW : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG W) N.erase) :
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) := by
  have hb := safety_fault_count_bound (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E E rho
    (fgsaSafetyUnitLaws p) (fgsaFamilies p c).linked (bridge_fg_linked p c) hL
    (fun B hB => bridge_carriage_of p c E rho _
      (hcar B ((bridge_runBlock_iff p c E rho B).1 hB)))
    (fun z hz => (bridge_noSlash_iff p c E rho z).2 (hC z hz)) hbot
  rw [safetyBound_def] at hb
  exact hb K W ((bridge_runBlock_iff p c E rho K).2 hK) ((bridge_runBlock_iff p c E rho W).2 hW)

/-- Field 7: sorted inclusive time reads inherit the order of the local F. -/
theorem fgsa_bridge_finalizedMonotone (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  have h := safety_finalized_monotone (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
    (fgsaCoreLaws p c) (fgsaSafetyOrderLaws p c) hs hnr
  rw [fgsaSafetyReads_def] at h
  exact h

/-- Sorted inclusive time reads preserve finalized output through restarts. -/
theorem fgsa_bridge_finalizedMonotone_restart
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key)) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  have h := safety_finalized_monotone_all (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
    (fgsaCoreLaws p c) (fgsaSafetyOrderLaws p c) (fgsaSafetyRestartLaws p c) hs
  rw [fgsaSafetyReads_def] at h
  exact h

/-- Client safety: an honest node's emitted rows contain no slashable pair. -/
theorem fgsa_bridge_clientSafeAll (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x :=
  fun x _ => (bridge_noSlash_iff p c E rho x).1
    (safety_emitted_noSlash (fgsaSafetyReads p c) p.E p.cfg E rho (fgsaSafetyWireLaws p c)
      (fgsaSafetyClientLaws p c) (fgsaFamilies p c).linked (bridge_fg_linked p c) hL x)

/-- Each row of a time-read chain has a signed wire at its FG seat; the honest
holder of that seat emitted the wire. -/
theorem fgsa_bridge_read_row_origin (hU : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (V2.D.Run.readAt E rho t x).st.fg.TF)
    (u : Row (Fin p.n)) (hu : u ∈ chainRows W) :
    ∃ a : RowWire p.n,
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a := by
  have hc := safety_read_carriage (fgsaCoreLaws p c) (fgsaSafetyStoreLaws p c)
    (fgsaSafetyWireLaws p c) hU t x
  rw [safetyCarriage_def] at hc
  have hmem : u ∈ safetyRows (fgsaCoreReads p c) (V2.D.Run.readAt E rho t x) := by
    rw [safetyRows_def, fgsaCoreReads_def]
    exact Finset.mem_biUnion.mpr ⟨W, hW, hu⟩
  obtain ⟨a, hdec, hem⟩ := hc u hmem
  rw [bridge_holder] at hem
  have hau : RowWire.toRow? a = some u := by
    rw [fgsaSafetyReads_def] at hdec
    exact hdec
  have har := row_auth_of_toRow a u hau
  refine ⟨a, hau, har, fun z hz hzh => ?_⟩
  rw [RowSigner_def] at hz
  obtain ⟨i, hi, hiz⟩ := hz
  rw [har] at hi
  cases hi
  subst hiz
  exact (bridge_emits_iff p c E rho _ a).1 (hem hzh)

/-- The Compose slashing read at the FG-SA reads is `fgsaSlashing`. -/
theorem fgsa_safetySlashesRead (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (fgsa p c)) :
    safetySlashesRead (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (fgsaSlashing p c E) := by
  rw [safetySlashesRead_def, fgsaCoreReads_def, fgsaSafetyReads_def]
  intro v
  exact Iff.rfl

/-- Field 8: under Linked and unforgeable signatures, `fgsaSlashing` never
names an honest node. -/
theorem fgsa_bridge_honestNeverSlashed (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho :=
  safety_honest_never_slashed (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E (heightView p)
    (finalityView p) p.cfg E rho (fun nd => Reachable p nd.st) (fgsaCoreLaws p c)
    (fgsaSafetyWireLaws p c) (fgsaSafetyStoreLaws p c) (fgsaSafetyClientLaws p c)
    (fgsaFamilies p c).linked (bridge_fg_linked p c) (fgsaSlashing p c E)
    (fgsa_safetySlashesRead p c E rho) hU hL

end AvailableChain.FGSA.Run
end
