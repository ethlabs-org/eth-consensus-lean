module
public import AvailableChainPCSAProofs.Proofs.Clean.Export
public import AvailableChainPCSAProofs.Proofs.Outage.Export
public import AvailableChainPCSAProofs.Proofs.PC.Export

public section

/-! Assembly entry for the Outage lane (pcsa34-r4.3 §5.4.1). -/

namespace AvailableChain.PCSA.Run

/-- C8 is available independently of the unfinished claim record. -/
theorem pcsa_armPersistenceClaim (p : Params) : ArmPersistenceClaim p := pcsa_armPersistence p

/-- [pcsa34-r4.3 §5.2.3] C9, strong inclusion, with no open hypothesis. The Clean-lane
producer `pcsa_clean_honestProposal_stamped` stamps the proposal PC before `z_u`; C8
persistence (`pcsa_armPersistence`) with `j₀ = u + 1` (empty later-ack interval) keeps it below
the strong output from `z_u` on. -/
theorem pcsa_strongIncludedClaim (p : Params) : StrongIncludedClaim p := by
  have hArm : ArmPersistenceClaim p := pcsa_armPersistence p
  rw [ArmPersistenceClaim_def] at hArm
  rw [StrongIncludedClaim_def]
  intro V _ _ In c m E rho b₀ ΔF hClean hQuarter hFrame u P hProposal hQuorum x hx t hzt ht
  obtain ⟨hw, N, hErase, he⟩ := pcsa_honest_proposal_named E rho u P hProposal
  obtain ⟨_, _, hPos, _⟩ := pcsa_emitted_proposal_inputs E rho _ u N he
  have hFault := pcsa_c9_faultsBelowQA_of_quarterCap rho hQuarter
  have hStamp := pcsa_clean_honestProposal_stamped p c m E rho b₀ ΔF hClean hQuarter hFrame u N
    hPos ⟨hw, he⟩ hQuorum (hzt.trans ht)
  have hArmPrem : Arm p c E rho u P (u + 1) := by
    constructor
    · simpa only [Nat.add_sub_cancel, hErase] using hStamp
    · intro y s' X hlo hhi _
      exact (Nat.not_lt_of_ge hlo hhi).elim
  have hPersist := hArm c m E rho u P (u + 1) hClean.base hFault hFrame (Nat.lt_succ_self u)
    hArmPrem
  have hAt := hStamp x hx
  rw [pcsa_PCStampedBefore_def] at hAt
  obtain ⟨A, hA, hSlot, hTarget⟩ := hAt
  have hHeld := pcsa_c9_afterTicks_pcs_storeAt E rho hClean.base hFrame x hx
    (SA.freezeTime p.toParams u) hA
  exact (hPersist.2.2 x hx (SA.freezeTime p.toParams u) t hzt
    ⟨A, hHeld, hSlot, hTarget.trans hErase⟩).1

/-- [pcsa34-r4.3 §5.2.2, §5.2.3, §5.5 step 1] The Clean facts at the pending
labels from the Clean facts at the cut. `pcsa_cleanCutItems_of_cone` gives
the facts at the cut from the HEAD cone. -/
theorem pcsa_cleanCutChainItems_of (p : Params) (hK : CleanCutItems p) :
    CleanCutChainItems p := by
  rw [CleanCutChainItems_def]
  rw [CleanCutItems_def] at hK
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact (hK c m E rho b₀ ΔF hC hf hfr).toCutChain

/-- [pcsa34-r4.3 §5.2.2, §5.2.3, §5.5 steps 1–2] The Clean facts at the cut
from the HEAD cone (`hcone`; `pcsa_cleanConeItems`). The other fields are Clean-lane theorems:
`nonempty` (M1, `pcsa_clean_results_nonempty`), `chain` (M2,
`pcsa_clean_results_chain_pending`), `dis` (M3,
`pcsa_clean_dissemination_pending`), `same` (CI (i), `pcsa_clean_invariant`),
`rows` (`pcsa_clean_lock_below_record_cut`) and `bridge` (the clean-gate
successor, `pcsa_clean_head_above_past_at_early` at label `j + 1`). -/
theorem pcsa_cleanCutItems_of_cone (p : Params) (hcone : CleanConeItems p) :
    CleanCutItems p := by
  have hne : CleanResultsNonemptyClaim p := pcsa_clean_results_nonempty p
  have hch : CleanResultsChainPendingClaim p := pcsa_clean_results_chain_pending p
  have hdis : CleanDisseminationPendingClaim p := pcsa_clean_dissemination_pending p
  have hci : CleanInvariantClaim p := pcsa_clean_invariant p
  rw [CleanCutItems_def]
  rw [CleanConeItems_def] at hcone
  rw [CleanResultsNonemptyClaim_def] at hne
  rw [CleanResultsChainPendingClaim_def] at hch
  rw [CleanDisseminationPendingClaim_def] at hdis
  rw [CleanInvariantClaim_def] at hci
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact {
    nonempty := hne c m E rho b₀ ΔF hC hf hfr
    chain := hch c m E rho b₀ ΔF hC hf hfr
    cone := hcone c m E rho b₀ ΔF hC hf hfr
    dis := hdis c m E rho b₀ ΔF hC hf hfr
    same := fun j hj x hx y hy X Y hX hY =>
      ((hci c m E rho b₀ ΔF hC hf hfr j hj).resultsChain x hx y hy j j X Y (le_refl j)
        (le_refl j) hX hY).2 rfl
    rows := fun x hx t _ ht row hr _ =>
      pcsa_clean_lock_below_record_cut E rho hC hfr hf x hx t ht row hr
    bridge := fun j u x A H hj hu hA hH =>
      pcsa_clean_head_above_past_at_early E rho hC hfr hf (j + 1)
        (by rw [earlyTime_succ_eq_gateTime]; exact hj) x H hH u hu j A (Nat.lt_succ_self j) hA }

/-- [pcsa34-r4.3 §5.2.3] CLEAN block receipt, proved in the Outage lane. -/
theorem pcsa_cleanBlockReceipt (p : Params) : CleanBlockReceiptClaim p := by
  rw [CleanBlockReceiptClaim_def]
  intro V _ _ In c m E rho b₀ ΔF hC _ hfr v hv T B _ hTb hB y hy t ht
  exact pcsa_healthy_block_receipt E rho hC hfr v hv T B hTb hB y hy t ht

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (a)] The relay item from block receipt
(`pcsa_cleanBlockReceipt`). -/
theorem pcsa_cleanRelayItems_of (p : Params) : CleanRelayItems p := by
  have hrecv : CleanBlockReceiptClaim p := pcsa_cleanBlockReceipt p
  rw [CleanRelayItems_def]
  rw [CleanBlockReceiptClaim_def] at hrecv
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact pcsa_heldPCRelay_of E rho hC hfr (hrecv c m E rho b₀ ΔF hC hf hfr)

/-- [pcsa34-r4.3 §5.4.2] The two ARM items from the relay item, pending-label
dissemination (M3, `pcsa_clean_dissemination_pending`) and the vote-time
HEAD cone (`hvcone`; `pcsa_cleanVoteConeItems`). -/
theorem pcsa_cleanArmItems_of_vcone (p : Params) (hvcone : CleanVoteConeItems p) :
    CleanArmItems p := by
  have hrel : CleanRelayItems p := pcsa_cleanRelayItems_of p
  have hdis : CleanDisseminationPendingClaim p := pcsa_clean_dissemination_pending p
  rw [CleanArmItems_def]
  rw [CleanRelayItems_def] at hrel
  rw [CleanDisseminationPendingClaim_def] at hdis
  rw [CleanVoteConeItems_def] at hvcone
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact ⟨hrel c m E rho b₀ ΔF hC hf hfr,
    pcsa_cleanArmAcks_of_vote E rho hC hf hfr
      (fun s y B hB => (hdis c m E rho b₀ ΔF hC hf hfr s y B hB).1)
      (hvcone c m E rho b₀ ΔF hC hf hfr)⟩

/-- [pcsa34-r4.3 §5.4.2] C8, ARM-healthy, from the vote-time HEAD cone
(`hvcone`; `pcsa_armHealthyClaim` supplies it). The relay item follows from block receipt
(`pcsa_cleanBlockReceipt`, `pcsa_cleanRelayItems_of`); pending-label
dissemination is M3 (`pcsa_clean_dissemination_pending`). -/
theorem pcsa_armHealthy_of_claims (p : Params) (hvcone : CleanVoteConeItems p) :
    ArmHealthyClaim p :=
  pcsa_armHealthy p (pcsa_cleanArmItems_of_vcone p hvcone)

/-- [pcsa34-r4.3 §5.5] C10, slow P1, from the HEAD cone (`hcone`; `pcsa_slowP1Claim` supplies it).
The ARM items use its vote-time form (`pcsa_cleanVoteConeItems_of_cone`); the
slow boundary facts come from the Clean facts at the cut
(`pcsa_cleanCutItems_of_cone`, `pcsa_cleanSlowItems_of`). -/
theorem pcsa_slowP1_of_claims (p : Params) (hcone : CleanConeItems p) : PCSASlowP1Claim p :=
  pcsa_slowP1 p (pcsa_cleanArmItems_of_vcone p (pcsa_cleanVoteConeItems_of_cone p hcone))
    (pcsa_cleanSlowItems_of p (pcsa_cleanCutItems_of_cone p hcone))

/-- [pcsa34-r4.3 §5.5 step 2] The full HEAD cone (`pcsa_clean_heads_cone_past_cut`). -/
theorem pcsa_cleanConeItems (p : Params) : CleanConeItems p := by
  rw [CleanConeItems_def]
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact pcsa_clean_heads_cone_past_cut (p := p) (c := c) (m := m) E rho
    (cut := b₀) (ΔF := ΔF) hC hf hfr

/-- [pcsa34-r4.3 §5.4.2] The vote-time HEAD cone (`pcsa_clean_heads_cone_at_vote`). -/
theorem pcsa_cleanVoteConeItems (p : Params) : CleanVoteConeItems p := by
  rw [CleanVoteConeItems_def]
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact pcsa_clean_heads_cone_at_vote (p := p) (c := c) (m := m) E rho
    (cut := b₀) (ΔF := ΔF) hC hf hfr

/-- [pcsa34-r4.3 §5.4.2] C8, ARM-healthy, with no open hypothesis. -/
theorem pcsa_armHealthyClaim (p : Params) : ArmHealthyClaim p :=
  pcsa_armHealthy_of_claims p (pcsa_cleanVoteConeItems p)

/-- [pcsa34-r4.3 §5.5] C10, slow P1, with no open hypothesis. -/
theorem pcsa_slowP1Claim (p : Params) : PCSASlowP1Claim p :=
  pcsa_slowP1_of_claims p (pcsa_cleanConeItems p)

end AvailableChain.PCSA.Run
end
