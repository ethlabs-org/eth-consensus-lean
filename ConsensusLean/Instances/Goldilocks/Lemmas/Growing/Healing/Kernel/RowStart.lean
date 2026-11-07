module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowPools

public section

/-! # A slot-start signing follows only the signer's own current-slot votes

This local execution lemma has no reset or retention invariant. Consumers apply
it only to the signer's finite honest prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem restart_emits
    (hr : ACLocalRun (goldilocksNode sp ro) H (tr.HonestBlocks H) tr.projAC)
    {v : Fin sp.n} (hv : v ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt v i ell) (hcl : ell.call = .restart) : ell.emits = [] := by
  have he := hr.exec i ell hc.2 (hc.1 ▸ hv)
  rw [hc.1, hcl] at he
  have h' : ell.emits = (((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step v
      (tr.projAC.state v i) ell.frame (tr.projAC.time i) .restart)).2 := by rw [he]
  rw [h']
  exact ((SA.restart_state sp) _ ro v (tr.projAC.state v i) ell.frame (tr.projAC.time i)
    (SA.frameIn_of_callAt hr hv hc).1 (hr.time_nonneg i)).1

/-- An optimistic write before a slot-start signing counts only the signer's own vote. -/
theorem slot_start_optimistic
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) {m : Nat} (hdt : tr.time d = sp.ts m)
    {r : Nat} (hrd : r < d) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC v r m D CV) :
    sp.n = 1 ∧ ∃ j' ≤ r, ∃ e', SA.VoteAt tr.projAC v j' e' ∧ e'.msg.slot = m := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ellv, A, hpt, hsl, hsel, -⟩ := hopt
  have hslm : sp.slot (sp.ts m) = m := SA.slot_of_mem sp m le_rfl
    ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  have hrt : tr.time r = sp.ts m := by
    refine le_antisymm (hdt ▸ hrun.time_mono hrd.le) ?_
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) (m : Int)).2 (by rw [hsl])
  obtain ⟨C, hcd⟩ := hs
  obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Compose.call_in_group hrun.toLocalRun hv hcd
  obtain ⟨x, rfl⟩ := @Compose.signed_only_in_ticks sp.toParams (goldilocksNode sp ro)
    proposer dg v _ _ _ C att (List.mem_of_getElem? hk)
  have hkk : kk < (Node.exec proposer dg v (tr.state v j) (tr.time d) (.tick x)).2.length := by
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hk
    cases hk
  have hnomsg : ∀ i, j ≤ i → i ≤ d → ∀ ell, tr.projAC.CallAt v i ell →
      ∀ mm, ell.call ≠ .message mm := by
    intro i h1 h2 ell hc mm hmm
    have hl := (hg.2.1 (i - j) (by omega)).2.2.2.2
    rw [Nat.add_sub_cancel' h1, (Compose.projAC_callAt.mp hc).2] at hl
    have hmem := List.getElem_mem
      (l := (Node.exec proposer dg v (tr.state v j) (tr.time d) (.tick x)).2)
      (n := i - j) (by omega)
    rw [← Option.some.inj hl] at hmem
    cases (exec_ac_call v _ _ _ hmem).2 mm hmm
  have hpre : ∀ i < j, ∀ ell, tr.projAC.CallAt v i ell →
      tr.time i = sp.ts m → ell.call = .restart := by
    intro i hi ell hc ht
    obtain ⟨ell', he, hr'⟩ := Compose.before_tick hrun.toLocalRun hv ⟨x, hg⟩
      (Compose.projAC_callAt.mp hc) hi (by rw [ht, hdt])
    cases he
    exact hr'
  have hjr : j ≤ r := by
    by_contra hlt
    have hcl := hpre r (by omega) ellv hpt.1 hrt
    rcases hpt.2 with ⟨mm, hmm, -⟩ | ⟨B, hB, -⟩ | ⟨e₀, he₀, -⟩
    · rw [hcl] at hmm; cases hmm
    · rw [hcl] at hB; cases hB
    · rw [restart_emits hr hv hpt.1 hcl] at he₀; cases he₀
  have hQ : ∀ c ≤ d, ∀ w ∈ (tr.projAC.state v c).pool m, w.val = v := by
    intro c hc w hw
    have hws : w.slot = m := SA.state_pool_slot sp hr hv c m w hw
    have hle : ∀ k₁, k₁ < c → sp.slot (tr.projAC.time k₁) ≤ m := fun k₁ hk₁ => by
      rw [← hslm, ← hdt]
      exact SA.slot_mono sp (hr.time_nonneg k₁) (hrun.time_mono (by omega))
    rcases SA.pool_origin hr hv c w (by rw [hws]; exact hw) with
      ⟨k₁, hk₁, hsend, -, hsl₁⟩ | ⟨k₁, hk₁, ell₁, hc₁, -, -, B, hB, hwB⟩
    · have hsk : sp.slot (tr.projAC.time k₁) = m := le_antisymm (hle k₁ hk₁) (by omega)
      have htk : tr.time k₁ = sp.ts m := le_antisymm (hdt ▸ hrun.time_mono (by omega))
        ((SA.ts_le_iff_le_slot sp (hr.time_nonneg k₁) _).2 (by rw [hsk]))
      obtain ⟨ell₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨hnr, hn, hh⟩⟩ := hsend
      · exact (SA.castAt_spec hr hv ⟨hc₁, he₁⟩).1
      · have hjk : j ≤ k₁ := by
          by_contra h
          exact hnr (hpre k₁ (by omega) ell₁ hc₁ htk)
        have he := hr.exec k₁ ell₁ hc₁.2 (hc₁.1 ▸ hv)
        rw [hc₁.1] at he
        change w ∈ (tr.projAC.post k₁).pool w.slot at hh
        have hpost : tr.projAC.post k₁ = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step v
            (tr.projAC.state v k₁) ell₁.frame (tr.projAC.time k₁) ell₁.call).1 := by rw [he]
        rw [hpost] at hh
        have hts : tr.projAC.time k₁ = sp.ts (sp.slot (tr.projAC.time k₁)) := by
          rw [hsk]; exact htk
        rcases step_pool_new v _ ell₁.frame hts hΔ ell₁.call
          (hnomsg k₁ hjk (by omega) ell₁ hc₁) hnr hh with h | h | ⟨B, hB, hwB⟩
        · exact absurd h hn
        · exact h
        · exfalso
          have hBt := (SA.accept_new sp hr hv ⟨ell₁, hc₁, hB⟩).1 ell₁ hc₁
          have h₁ := (SA.frame_validPayload sp hr hv hc₁ B hBt).1 w hwB
          have h₂ := SA.frame_slot_le sp hr hv hc₁ B hBt
          omega
    · exfalso
      have h₁ := (SA.frame_validPayload sp hr hv hc₁ B hB).1 w hwB
      have h₂ := SA.frame_slot_le sp hr hv hc₁ B hB
      have h₃ := hle k₁ hk₁
      omega
  have hP : ∀ w ∈ A.pool m, w.val = v := by
    intro w hw
    have hws := SA.optimisticPoint_pool_slot hr hv hpt hw
    obtain ⟨hcv, hcase⟩ := hpt
    rcases hcase with ⟨mm, hmm, -⟩ | ⟨B, hB, rfl⟩ | ⟨e₀, he₀, rfl⟩
    · exact absurd hmm (hnomsg r hjr hrd.le ellv hcv mm)
    · rcases receipt_pool_mem hw with hw | hwB
      · exact hQ r hrd.le w hw
      · exfalso
        have hBt := (SA.accept_new sp hr hv ⟨ellv, hcv, hB⟩).1 ellv hcv
        have h₁ := (SA.frame_validPayload sp hr hv hcv B hBt).1 w hwB
        have h₂ := SA.frame_slot_le sp hr hv hcv B hBt
        have h₃ : sp.slot (tr.projAC.time r) = m := hsl
        omega
    · rcases admit_pool_mem hw with hw | rfl
      · exact hQ (r + 1) hrd w (SA.readPoint_pool hr hv ⟨hcv, he₀⟩ hw).1
      · exact (SA.castAt_spec hr hv ⟨hcv, he₀⟩).1
  have h34 : 3 * sp.n ≤ 4 * (SA.optimisticVoters sp A ellv.frame m D).ncard := by
    have h := hsel
    unfold SA.optimisticSelect at h
    dsimp only at h
    split_ifs at h
    have := (SA.deepest_mem h).1.2.1
    rwa [hsl] at this
  have hsub : SA.optimisticVoters sp A ellv.frame m D ⊆ {v} := by
    rintro i ⟨w, hw, rfl, -⟩
    exact hP w hw
  have hle1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton] at hle1
  have hn := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  refine ⟨by omega, ?_⟩
  obtain ⟨i, w, hw, rfl, -⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := SA.optimisticVoters sp A ellv.frame m D) (by omega)
  have hwv := hP w hw
  obtain ⟨hws, j', hj', e', hve', he'⟩ := SA.optimisticPoint_pool_vote hrun' hv hpt hw (hwv ▸ hv)
  exact ⟨j', hj', e', hwv ▸ hve', by rw [he', hws]⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
