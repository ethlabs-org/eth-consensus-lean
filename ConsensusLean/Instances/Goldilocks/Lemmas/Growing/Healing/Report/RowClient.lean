module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RowGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts

public section

/-! # Client progress at an honest read

All honesty and quorum bounds belong to the reading time. The post-report attestation
cut may have a larger index without requiring honesty at a later time.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- No honest advance implies no finality lock at the frontier before the deadline. -/
theorem lock_none_of_noAdvance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {T t : Time} {h : Nat}
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att → tr.time k < T → att.h ≤ h)
    {y : Fin sp.n} {i : Nat} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (htT : t < T) : (tr.state y i).record.lock h = none := by
  rcases hl : (tr.state y i).record.lock h with _ | r
  · rfl
  obtain ⟨k, hk, att, hs, hfin⟩ := (record_facts_at hrun ht hle hy).2.2 h r hl
  have hwf := Healing.signAt_wellFormed (hrun.upTo ht) hy
    ((RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hs⟩)
  have hbound := hna y k att (hrun.antitone (hle k hk) hy) hs ((hle k hk).trans_lt htT)
  have := hwf.2 (h, r) (by simp [hfin])
  omega

/-- In kind F the source-height lock is free; in kind J it is free or the entry. -/
theorem lock_free_or_entry_of_frame_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ i < k, tr.time i ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {C E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hkind : (tr.state y k).fg.hj < h ∨
      ((tr.state y k).fg.hj = h ∧ (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root := by
  rcases hkind with hlt | ⟨hj, hJC⟩
  · left
    rcases hl : (tr.state y k).record.lock h with _ | r
    · rfl
    · have := hj_ge_of_lock_at hrun ht hle hy hf hl
      omega
  rcases hl : (tr.state y k).record.lock h with _ | r
  · exact Or.inl rfl
  refine Or.inr (congrArg some ?_)
  rw [lock_root_eq_J_at hrun hnc ht hle hy hf hl hj]
  have hr := fg_reachable_at hrun ht hle hy
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hr
  have hJh := Store.J_height_le hr hBj hJm hBjJ.symm
  have hJCh := h_le_of_store_anc hr hJC
  obtain ⟨E', hE', hE'r, -, hE'g⟩ := Store.J_entry_of_reachable hr hBj
  have hE'J : E' = (tr.state y k).fg.J := by
    have h1 : (tr.state y k).fg.blocks E'.root = some E' := hE'
    have h2 : (tr.state y k).fg.blocks (tr.state y k).fg.J.root = some (tr.state y k).fg.J := hJm
    rw [hE'r, hBjJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  subst hE'J
  have hJTh : ((tr.state y k).fg.σ (tr.state y k).fg.J.root).Th = (tr.state y k).fg.J.root := by
    rcases hE'g with he | ⟨-, hTh⟩
    · have hg : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
          sp.toParams.genesisRoot := rfl
      rw [he, hg, Store.σ_genesis hr]
      rfl
    · exact hTh
  have hJeq : ((tr.state y k).fg.σ C.root).h =
      ((tr.state y k).fg.σ (tr.state y k).fg.J.root).h := by omega
  have h1 := Th_eq_of_anc hr hJC hJeq
  have h2 := Th_eq_of_anc hr hEC (hCh.trans hEh.symm)
  rw [hJTh] at h1
  rw [hETh] at h2
  exact h1.symm.trans h2

/-- Client progress uses only its own serialized prefix, with no global origin invariant. -/
theorem client_progress_of_lock_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ i < k, tr.time i ≤ t) (hkt : tr.time k ≤ t) (hy : y ∈ H t)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {signed : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed)))
    {E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hlock : (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  have hs := Trace.upTo_state tr y hle
  have hE' : EntryOf ((tr.upTo t).state y k).fg C E h := by rwa [hs]
  have hCh' : (((tr.upTo t).state y k).fg.σ C.root).h = h := by rwa [hs]
  have hl' : ((tr.upTo t).state y k).record.lock h = none ∨
      ((tr.upTo t).state y k).record.lock h = some E.root := by rwa [hs]
  rcases Healing.client_progress_of_lock (hrun.upTo ht) hy
      ((Trace.upTo_callAt tr).mpr ⟨hkt, hc⟩) hE' hCh' hl' with hnow | ⟨j, hj, a, ha, hh, hT⟩
  · exact Or.inl hnow
  · exact Or.inr ⟨j, hj, a, ((RunTrace.upTo_signAt tr).mp ha).2, hh, hT⟩

end Consensus.Goldilocks.Healing.Growing

end
