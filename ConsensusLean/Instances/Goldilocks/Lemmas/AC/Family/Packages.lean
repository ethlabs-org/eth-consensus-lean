module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Votes
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Records
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Retention
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Dominance
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Source
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

/-! # Independent Goldilocks component fact suppliers -/

public section

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {o : SATrace sp FGP ro}
  {proposer : Nat → Fin sp.n}

theorem goldilocksVoteObservation (hr : ACRun proposer o H U) :
    FamilyFacts.VoteObservation (goldilocksFamily sp FGP ro) o H := by
  constructor
  · simp only [proj_goldilocks]
    intro y hy i s
    exact state_pool_slot sp hr.localRun hy i s
  · simpa only [proj_goldilocks] using hr.honest.pool_vote
  · simp only [proj_goldilocks]
    intro x hx i e he
    have hs := (vote_signer_slot hr.localRun hx he).2
    exact ⟨hs ▸ (ts_le_iff_le_slot sp (hr.localRun.time_nonneg i) _).mpr le_rfl,
      hs ▸ vote_time_le hr.localRun hx he⟩
  · simp only [proj_goldilocks]
    intro x hx i ℓ e he
    obtain ⟨B, hB, hr, _⟩ := honest_head_frame hr.localRun hx he
    exact ⟨B, hB, hr⟩

private theorem call_lockInv (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : o.CallAt y i ℓ) : LockInv U (o.state y i) ℓ.frame := by
  rcases hr.frameLaw y hy i ℓ hc with
    ⟨hn, Φ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
  · rw [o.state_of_noCall hn, hr.init y hy]
    exact (lockInv_of_reachable (x := y) hr.coherent (.init Φ hi hf)).2.2.callOK hr.coherent hf hok
  · rw [o.state_of_lastCall hc' hj hn]
    obtain ⟨hf, _, hv⟩ := lockInv_of_reachable hr.coherent
      (localRun_reachable _ _ _ _ _ o hr y hy j ℓ' hc')
    exact hv.callOK hr.coherent hf hok

theorem goldilocksCallFrameInvariant (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.CallFrameInvariant (goldilocksFamily sp FGP ro) o H U := by
  simp only [FamilyFacts.CallFrameInvariant, proj_goldilocks]
  intro y hy i ℓ hc
  exact lockInv_iff.mp (call_lockInv hr hy hc)

theorem goldilocksRecordAboveLive (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.RecordAboveLive (goldilocksFamily sp FGP ro) o H := by
  simp only [FamilyFacts.RecordAboveLive, proj_goldilocks]
  intro y hy i s ℓ hu L hL
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hu.1
  exact (call_lockInv hr hy hu.1).liveBlock_anc hr.coherent hΦ hΦU hL

theorem goldilocksReadPointOrigin (hr : ACRun proposer o H U) :
    FamilyFacts.ReadPointOrigin (goldilocksFamily sp FGP ro) o H := by
  simp only [FamilyFacts.ReadPointOrigin, proj_goldilocks]
  intro y hy i ℓ e hc hp l hl
  obtain ⟨B', hB', hr', h | ⟨B, CV, he, hv, hanc⟩⟩ :=
    readPoint_locks_provenance_strict hr hy hc hp l hl
  · exact ⟨B', hB', hr', Or.inl h⟩
  · exact ⟨B', hB', hr', Or.inr ⟨B, CV, ⟨rfl, he⟩, hv, hanc⟩⟩

/-- The concrete parent unlock condition; not a condition imposed on other families. -/
def goldilocksK (o : SATrace sp FGP ro) (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) (B : Blk sp.n FGP) : Prop :=
  unlockTarget sp ℓ.frame (unlockView (o.state x i) ℓ.frame (o.time i) ℓ.call)
    ((sp.slot (o.time i) : Int) - 1) B = B

theorem goldilocksK_iff (o : SATrace sp FGP ro) (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) (B : Blk sp.n FGP) :
    goldilocksK o x i ℓ B ↔
      unlockTarget sp ℓ.frame (unlockView (o.state x i) ℓ.frame (o.time i) ℓ.call)
        ((sp.slot (o.time i) : Int) - 1) B = B := by rfl

/-- The parent dominance supplier covers every exact observation index. -/
def goldilocksDomain (_x : Fin sp.n) (_i : Nat) (_ℓ : ACLabel (goldilocksSA sp FGP ro))
    (_e : Em sp FGP) (_B _C : Blk sp.n FGP) (_t : Time) : Prop := True

theorem goldilocksDomain_iff (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP) (B C : Blk sp.n FGP)
    (t : Time) : goldilocksDomain x i ℓ e B C t ↔ True := by rfl

theorem goldilocksRetention (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.Retention (goldilocksFamily sp FGP ro) o H (goldilocksK o) := by
  constructor
  · simp only [proj_goldilocks]
    intro x hx i ℓ B j m hc hf ht hB hv hu
    have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1] at he
    have h := exists_step_locks_floor x ℓ.call (frameIn_of_callAt hr hx hc).1
      (hr.time_nonneg i) hB hv ht hu hf
    have hp := congrArg (fun p : SAState sp.n × List (Em sp FGP) => p.1.locks) he
    exact hp ▸ h
  · simp only [proj_goldilocks]
    intro x hx i ℓ e B j m hc hB hv ht hu hf
    exact exists_readPoint_liveLockBlocks_floor hr hx hc hB hv ht hu hf

theorem goldilocksScopedDominance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.ScopedDominance (goldilocksFamily sp FGP ro) o H
      (goldilocksDomain (ro := ro)) := by
  constructor
  simp only [proj_goldilocks]
  intro x hx i ℓ e B C hc _ hC hBC
  have hΦ := (frameIn_of_callAt hr hx hc.1).1
  obtain ⟨ha, hanc⟩ := anc_getAnchor hΦ
    (castAt_liveLockBlocks_chain hr (fun _ => voteStart_initial _) hx hc (o.time i))
  obtain ⟨_, _, _, hh⟩ := castAt_spec hr hx hc
  refine ⟨_, getHead_mem hΦ (fun _ h => voteDomain_subset_tree h.1) _ _ _ _, hh.symm, ?_⟩
  exact hBC.trans ((hanc C (Or.inl hC)).trans
    (anc_ghost (fun _ h => voteDomain_subset_tree h.1) _ ha))

/-- The full eligible set is the parent's toFGCandidates, not just successful outputs. -/
noncomputable def goldilocksSourceData :
    FamilyFacts.SourceData (goldilocksOperations sp FGP ro) where
  evidence := fun _ _ _ => False
  eligible := fun x i ℓ => toFGCandidates sp (o.state x i) ℓ.frame (o.time i)

theorem goldilocksSourceData_evidence (x : Fin sp.n) (i : Nat) (C : Blk sp.n FGP) :
    (goldilocksSourceData (o := o)).evidence x i C ↔ False := by rfl

theorem goldilocksSourceData_eligible (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) :
    (goldilocksSourceData (o := o)).eligible x i ℓ =
      toFGCandidates sp (o.state x i) ℓ.frame (o.time i) := by rfl

theorem goldilocksSourceViability :
    FamilyFacts.SourceViability (goldilocksFamily sp FGP ro) o H := by
  intro x hx i ℓ C hc
  exact (toFG_candidate hc.2.2).1

theorem goldilocksSourceLockOrEvidence :
    FamilyFacts.SourceLockOrEvidence (goldilocksFamily sp FGP ro) o H
      (goldilocksSourceData (o := o)) := by
  simp only [FamilyFacts.SourceLockOrEvidence, proj_goldilocks]
  intro x hx i ℓ C hc
  exact Or.inl (toFG_candidate hc.2.2)

theorem goldilocksSourceReport (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.SourceReport (goldilocksFamily sp FGP ro) o H := by
  simp only [FamilyFacts.SourceReport, proj_goldilocks]
  intro x hx i ℓ C hc
  obtain ⟨hcall, hkind, hout⟩ := hc
  change (acToFG sp (o.state x i) ℓ.frame (o.time i)).2 = some C at hout
  have he := hr.exec i ℓ hcall.2 (hcall.1 ▸ hx)
  rw [hcall.1, hkind] at he
  have hp : (acToFG sp (o.state x i) ℓ.frame (o.time i)).1 = o.post i :=
    congrArg (fun p : SAState sp.n × List (Em sp FGP) => p.1) he
  unfold acToFG at hout hp
  split_ifs at hout hp; split at hout <;> simp_all
  split_ifs at hout hp; simp_all
  cases Option.some.inj hout
  exact ⟨hp.symm, by assumption⟩

theorem goldilocksSourceEvidenceCompatibility :
    FamilyFacts.SourceEvidenceCompatibility (goldilocksFamily sp FGP ro) o H U
      (goldilocksSourceData (o := o)) := by
  intro s m w x i₀ i P C CV ℓ hw he hs hc hf hx ho hd
  exact False.elim hd

/-- The family's lock threshold counts the population, so this holds for population-sized
committees (`hstock : committeeSize = n`). -/
theorem goldilocksLockWrites (hr : ACRun proposer o H U) (hstock : sp.committeeSize = sp.n) :
    FamilyFacts.LockWrites (goldilocksFamily sp FGP ro) o H U := by
  constructor
  · simp only [proj_goldilocks]
    intro y hy i l hl hf
    obtain ⟨j, hj, B, CV, he, hL⟩ := fast_lock_provenance hr.localRun hy i l hl hf
    exact ⟨j, hj, B, CV, he.elim (fun h => Or.inl ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩), hL⟩
  · simp only [proj_goldilocks]
    intro y hy i s B CV he
    obtain ⟨hn, hcv⟩ :=
      fastLock_counted hr hy (he.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
    rw [hstock] at hn
    exact ⟨hn, hcv⟩
  · simp only [proj_goldilocks]
    intro y hy i s B CV he v hv hh
    rcases he with ⟨_, ℓ, C, hu, hC, hd, rfl⟩ | ⟨_, he⟩
    · obtain ⟨j, hj, e, hem⟩ := hr.honest.pool_vote y hy i s v hv.1 hh
      exact ⟨j, hj.le, e, hem⟩
    · obtain ⟨_, _, ℓ, A, _, _, _, ha, -⟩ :=
        optimisticLockAt_spec hr hy he (CommitteeDict.full sp.n) (fun _ _ _ => mem_full _ _)
      exact ha v hv hh

theorem goldilocksSourceCandidates (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    FamilyFacts.SourceCandidates (goldilocksFamily sp FGP ro) o H
      (goldilocksSourceData (o := o)) := by
  constructor
  · intro x hx i ℓ C hc
    exact toFG_candidate hc.2.2
  · intro x hx i ℓ hc hk B hB C hC
    have hΦ := (frameIn_of_callAt hr hx hc).1
    have hinv := call_lockInv hr hx hc
    exact hinv.liveBlocks_chain hr.coherent hΦ (frameIn_of_callAt hr hx hc).2 B
      ⟨hB.1.1, hB.2.choose, hB.2.choose_spec.1, hB.2.choose_spec.2.1⟩ C
      ⟨hC.1.1, hC.2.choose, hC.2.choose_spec.1, hC.2.choose_spec.2.1⟩
  · intro x hx i ℓ hc hk C hC
    exact hC.1
  · intro x hx i ℓ hc hk C hC
    exact Or.inl (by rw [proj_goldilocks]; exact hC)

theorem goldilocksUnlocksRel (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time)
    (s : Int) (V : View sp.n) (hΦ : FrameOK Φ) :
    FamilyFacts.UnlocksRel sp L Φ t s V (unlock sp L Φ t s V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨a, ha, B, hB, hBr, he⟩ := hl
    refine ⟨l, ⟨a, ha, B, hB, hBr, he⟩, rfl, rfl, rfl, ?_⟩
    split_ifs at he with hs
    · subst l
      have hb := unlockTarget_anc sp hΦ V s hB
      exact ⟨_, hb.1, rfl, _, hb.1, rfl, .refl⟩
    · subst l
      exact ⟨B, hB, hBr, B, hB, hBr, .refl⟩
  · intro l hl; exact ⟨l, hl, rfl, rfl, rfl⟩
  · intro l hl hs
    obtain ⟨a, ha, B, hB, hBr, ht, he⟩ := hl
    have hb := (viableAncestor_anc hΦ hB).1
    refine ⟨l, ⟨a, ha, B, hB, hBr, ht, he⟩, Φ.viableAncestor B, hb, ?_, ?_⟩
    · exact congrArg Lock.block he.symm
    · exact (ite_eq_right (not_lt.mpr hs)).symm

end Consensus.Goldilocks.SA

end
