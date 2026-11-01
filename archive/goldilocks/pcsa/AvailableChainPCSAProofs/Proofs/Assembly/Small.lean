module
public import AvailableChainPCSAProofs.Proofs.PC.Export
public import AvailableChainPCSAProofs.Proofs.Clean.Export

public section

/-! The proved small claims. The full PCSAClaims record remains separate. -/

namespace AvailableChain.PCSA.Run

/-- C2, C4, and the snapshot claim, for every FG mode. -/
theorem pcsa_smallClaims (p : Params) :
    OneAckPerSlotClaim p ∧ OutputNestingClaim p ∧ PCSnapshotStampClaim p :=
  ⟨pcsa_oneAckPerSlot p, pcsa_outputNesting p, pcsa_snapshotStamp p⟩

end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run

/-- C3: positive-slot honest ack quorums disseminate an exact PC before the freeze. -/
theorem pcsa_pcDissemination (p : Params) : PCDisseminationClaim p := by
  rw [PCDisseminationClaim_def]
  intro V _ _ In c m E rho cut ΔF h _ hF s r hs hz hQ
  obtain ⟨Q, hcard, hacks⟩ := hQ
  have hpos : 0 < pcQuorum p.n := by
    change 0 < (p.n + 1) / 2
    have hn := p.nPos
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos hcard)
  obtain ⟨B, hslot, hroot, hbody⟩ := pcsa_ack_target_body_before_freeze E rho h.base hF h.healthy
    s i r hs (hacks i hi).1 (hacks i hi).2 hz
  apply pcsa_dissemination_of_store_facts E rho h.healthy h.base.valid.toScheduleWellFormed
    h.base.delta s r Q hcard hacks hz
  · intro y hy i hi j t het _ hh
    exact pcsa_honest_ack_admitted E rho h.base y hy s i r j t (hacks i hi).1 het hh
  · intro y _ j k hjk
    exact pcsa_ackPool_stateBefore_mono E rho h.base.noRestart y hjk
  · intro y hy
    dsimp only
    intro hp hc
    have hj := Gen.V2.Duty.stateBefore_idxBefore E rho (SA.freezeTime p.toParams s)
      h.base.valid.toScheduleWellFormed
    have hb := hbody y hy
    rw [← hj] at hp hb ⊢
    obtain ⟨C, hC, hCs, hCB⟩ := pcsa_collect_held_target E rho h.base hF _ y hy s B hs hslot hb
      Q hc (by simpa only [hroot] using hp)
    exact ⟨C, hC, hCs, hCB ▸ hroot⟩
  · intro y hy
    exact pcsa_collectPCs_after_freeze E rho h.base.valid.toScheduleWellFormed h.base.noRestart
      h.base.delta y hy s (hz.trans h.cut.2)
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
/-- C5: the available output is monotone through the full healthy prefix. -/
theorem pcsa_available_monotone (p : Params) : AvailableMonotoneClaim p := by
  intro V _ _ In c m E rho cut ΔF h hFault hF x hx t t' _ htt hc
  exact pcsa_clean_available_mono_cut E rho h hF hFault x hx t t' htt hc
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
/-- M5: every retained lock is below S and compatible with every held PC through the cut. -/
theorem pcsa_lock_below_record (p : Params) : LeaseBelowRecordClaim p := by
  intro V _ _ In c m E rho cut ΔF h hFault hF x hx t _ ht row hr _
  constructor
  · exact pcsa_clean_lock_below_record_cut E rho h hF hFault x hx t ht row hr
  · obtain ⟨_, i, X, -, hi, hX, hrowX⟩ :=
      pcsa_lock_storeAt_timed_origin E rho h.base x t row hr
    intro C hC
    obtain ⟨_, y, hy, htime⟩ := pcsa_pc_storeAt_timed_ack E rho h.base hFault x hx t C hC
    have hc := pcsa_clean_ack_result_cut E rho h hF hFault C.slot (htime.trans ht) y C.target hy
      i (hi.trans ht) x hx X hX
    rcases Bool.or_eq_true_iff.mp hc with hCX | hXC
    · exact Gen.Pure.block_compatible_of_common hrowX hCX
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_trans hrowX hXC))
end AvailableChain.PCSA.Run

end
