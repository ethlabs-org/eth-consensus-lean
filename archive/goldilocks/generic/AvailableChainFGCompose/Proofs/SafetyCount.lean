module
public import AvailableChainFGCompose.Statements.SafetyClaims -- shake: keep (re-export)

public section

/-! S3a field 6: fault counting for the all-run slashable bound.
Ports F/Accountable.lean:336-385 (slashable_pool_count) and :444-453
(fgsa_slashableBound_of_faults). Linked gives an injective FG holder map. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n))
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Slashable evidence between two carried row sets has distinct faulty holders
of total weight at least `2 q_F − n`. -/
theorem safety_slashable_faulty_count [Fintype V] (U : FGSafetyUnitLaws Ef)
    (linked : P.Label → Prop) (hfg : linked S.fgLabel) (hl : V2.D.Linked linked rho)
    (he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    {A B : Finset (Row (Fin n))} (hA : safetyCarriage S E rho A)
    (hB : safetyCarriage S E rho B) (hev : HasSlashableWeightBetween Ef A B) :
    2 * Gen.Pure.qF n - n ≤ (Gen.V2.Duty.faulty rho).card := by
  classical
  obtain ⟨I, hw, hs⟩ := hev
  have hsub : I.image (safetyHolder S rho) ⊆ Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, hui, hvi, huv⟩ := hs i hi
    obtain ⟨a, hau, hea⟩ := hA u hu
    obtain ⟨b, hbv, heb⟩ := hB v hv
    subst hui
    have hz : safetyHolder S rho u.signer ∉ rho.honest := by
      intro hzh
      have hzh' : safetyHolder S rho v.signer ∈ rho.honest := by rw [hvi]; exact hzh
      have heb' := heb hzh'
      rw [hvi] at heb'
      exact he _ hzh a b (hea hzh) heb' u v hau hbv huv
    rw [Gen.V2.Duty.faulty_def]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩
  have hinj : Function.Injective (safetyHolder S rho) := by
    intro i j h
    rw [safetyHolder_def, safetyHolder_def] at h
    exact S.fgSeats.injective ((hl.toCStar S.fgLabel hfg).1 h)
  have hcard : I.card ≤ (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective I hinj).symm.trans_le (Finset.card_le_card hsub)
  change 2 * Ef.q ≤ Ef.totalWeight + Ef.weightOf I at hw
  rw [U.quorum, U.total, U.weight] at hw
  omega

/-- Field 6. Carriage of every run block, honest client safety and the
one-third fault bound exclude slashable evidence between run blocks. -/
theorem safety_fault_count_bound [Fintype V]
    (U : FGSafetyUnitLaws Ef) (linked : P.Label → Prop)
    (hfg : linked S.fgLabel) (hL : V2.D.Linked linked rho)
    (hc : ∀ B, safetyRunBlock R S E rho B → safetyCarriage S E rho (chainRows B))
    (he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3) :
    safetyBound R S Ef E rho := by
  rw [safetyBound_def]
  intro K W hK hW hev
  have hcount := safety_slashable_faulty_count S Ef E rho U linked hfg hL he
    (hc K hK) (hc W hW) hev
  have hn := U.n_pos
  rw [Gen.Pure.qF_def] at hcount
  omega

/-- DC: SAME. The strict paper threshold excludes accountable evidence. -/
theorem safety_fault_count_bound_lt [Fintype V]
    (U : FGSafetyUnitLaws Ef) (linked : P.Label → Prop)
    (hfg : linked S.fgLabel) (hL : V2.D.Linked linked rho)
    (hc : ∀ B, safetyRunBlock R S E rho B → safetyCarriage S E rho (chainRows B))
    (he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    (hf : (Gen.V2.Duty.faulty rho).card < 2 * Gen.Pure.qF n - n) :
    safetyBound R S Ef E rho := by
  intro K W hK hW hev
  exact Nat.not_lt_of_ge
    (safety_slashable_faulty_count S Ef E rho U linked hfg hL he
      (hc K hK) (hc W hW) hev) hf

/-- DC: INTENTIONAL. Count FG evidence seats, independently of other run nodes.
Each evidence seat has a faulty holder. No population identification is needed. -/
theorem safety_slashable_fg_faulty_count (U : FGSafetyUnitLaws Ef)
    (he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    {A B : Finset (Row (Fin n))} (hA : safetyCarriage S E rho A)
    (hB : safetyCarriage S E rho B) (hev : HasSlashableWeightBetween Ef A B) :
    2 * Gen.Pure.qF n - n ≤
      (Finset.univ.filter (fun i : Fin n => safetyHolder S rho i ∉ rho.honest)).card := by
  classical
  obtain ⟨I, hw, hs⟩ := hev
  have hsub : I ⊆ Finset.univ.filter (fun i : Fin n => safetyHolder S rho i ∉ rho.honest) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨u, hu, v, hv, hui, hvi, huv⟩ := hs i hi
    obtain ⟨a, hau, hea⟩ := hA u hu
    obtain ⟨b, hbv, heb⟩ := hB v hv
    intro hh
    have hhu : safetyHolder S rho u.signer ∈ rho.honest := by rw [hui]; exact hh
    have hhv : safetyHolder S rho v.signer ∈ rho.honest := by rw [hvi]; exact hh
    have hemv := heb hhv
    rw [hvi, ← hui] at hemv
    exact he _ hhu a b (hea hhu) hemv u v hau hbv huv
  have hcard := Finset.card_le_card hsub
  change 2 * Ef.q ≤ Ef.totalWeight + Ef.weightOf I at hw
  rw [U.quorum, U.total, U.weight] at hw
  omega

/-- DC: INTENTIONAL. The paper fault premise concerns only the finite FG seats. -/
theorem safety_fault_count_bound_fg_lt
    (U : FGSafetyUnitLaws Ef)
    (hc : ∀ B, safetyRunBlock R S E rho B → safetyCarriage S E rho (chainRows B))
    (he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    (hf : (Finset.univ.filter (fun i : Fin n => safetyHolder S rho i ∉ rho.honest)).card <
      2 * Gen.Pure.qF n - n) : safetyBound R S Ef E rho := by
  intro K W hK hW hev
  exact Nat.not_lt_of_ge
    (safety_slashable_fg_faulty_count S Ef E rho U he (hc K hK) (hc W hW) hev) hf

end AvailableChain.FGCompose
end
