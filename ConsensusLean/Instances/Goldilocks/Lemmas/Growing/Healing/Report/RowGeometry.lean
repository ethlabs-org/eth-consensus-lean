module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSignedAt
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache

public section

/-! # Lock geometry at one honest observation

The client record and every state used here belong to the same node's prefix through
its reading time. Certificate provenance is recovered at that observation, not from
an invariant for a terminal honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The durable client record only contains signatures made before this honest read. -/
theorem record_facts_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    Client.SentOK (tr.state y i).record ∧
    (∀ b ∈ (tr.state y i).record.sent,
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b) ∧
    ∀ h r, (tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r) := by
  have hs := Trace.upTo_state tr y hle
  obtain ⟨hok, hsent, hlock⟩ := Healing.record_facts (hrun.upTo ht) hy i
  rw [hs] at hok hsent hlock
  exact ⟨hok, fun b hb => let ⟨k, hk, a, ha, he⟩ := hsent b hb
    ⟨k, hk, a, ((RunTrace.upTo_signAt tr).mp ha).2, he⟩,
    fun h r hl => let ⟨k, hk, a, ha, he⟩ := hlock h r hl
      ⟨k, hk, a, ((RunTrace.upTo_signAt tr).mp ha).2, he⟩⟩

/-- Two signatures made before an honest reading cannot be slashable. -/
private theorem not_slashable_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {t : Time} (ht : 0 ≤ t)
    {v : Fin sp.n} (hv : v ∈ H t) {k l : Nat} {a b : FG.Att sp.n}
    (hk : tr.time k ≤ t) (hl : tr.time l ≤ t)
    (ha : tr.SignAt v k a) (hb : tr.SignAt v l b) : ¬ FG.slashable a b := by
  have hr := hrun.upTo ht
  obtain ⟨inputs, hin, hs⟩ := Store.signed_run_of_exec
    (Compose.fg_exec hr.toLocalRun) hv (max k l + 1)
  have ha' := (RunTrace.upTo_signAt tr).mpr ⟨hk, ha⟩
  have hb' := (RunTrace.upTo_signAt tr).mpr ⟨hl, hb⟩
  exact FG.client_safety sp.toParams.fg v inputs hin a
    (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr ha'.choose_spec⟩) b
    (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hb'.choose_spec⟩)

/-- Attestations on blocks held at one honest observation, with a signer honest there, are not
slashable: both were signed before the cut (`held_att_signed_at`). -/
private theorem held_atts_safe_one
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state y i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at hrun ht hle hy ha hav
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at hrun ht hle hy hb (hab.1 ▸ hav)
  rw [← hab.1] at hlb
  exact not_slashable_at hrun ht hav (hle k hk) (hle l hl) hka hlb hab

/-- A store's finalized cache lies below a held block above its justified height. -/
private theorem F_anc_of_hj_lt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree)
    (hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F B :=
  have hR := fg_reachable_at hrun ht hle hy
  Store.F_anc_of_hj_lt_of_safe hR hR (Store.accepted_tree _ _ _ _ hR).2.1 subset_rfl subset_rfl
    hf (held_atts_safe_one hrun ht hle hy) hB hlt

/-- A finality lock cannot be above the node's own justification cache. -/
theorem hj_ge_of_lock_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) : h ≤ (tr.state y i).fg.hj := by
  have hr := hrun.upTo ht
  have hs := Trace.upTo_state tr y hle
  obtain ⟨k, hk, att, hsa, hfin⟩ := (record_facts_at hrun ht hle hy).2.2 h r hl
  have hsa' := (RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hsa⟩
  obtain ⟨B, hB, hBj, -⟩ := Healing.signed_fin_justified hr hy hsa' hfin
  have hsk := Trace.upTo_state tr y (fun q hq => hle q (hq.trans hk))
  rw [hsk] at hB hBj
  have hmono : (tr.state y k).fg.hj ≤ (tr.state y i).fg.hj := by
    simpa only [hs, hsk] using Healing.hj_mono hr hy hk.le
  refine le_trans ?_ hmono
  have hR := fg_reachable_at hrun ht (fun q hq => hle q (hq.trans hk)) hy
  by_contra hlt
  have hlt' : (tr.state y k).fg.hj < ((tr.state y k).fg.σ B.root).h := by
    have := Store.hj_lt_h hR hB
    omega
  have hFB := F_anc_of_hj_lt_at hrun ht (fun q hq => hle q (hq.trans hk)) hy hf hB hlt'
  obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hR hB
  have hEh := Store.J_height_le hR hB hE hEr
  have hjmax := (jMax_iff _).1 (jMax_of_reachable hR) B hB E hE hEr
  obtain ⟨-, hcoh, -, hgen⟩ := Store.accepted_tree _ _ _ _ hR
  rcases Anc.total hcoh hFB hEB with hFE | hEF
  · have := hjmax hFE
    omega
  · obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj', hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
    obtain ⟨E', hE', hEr', -, hEg⟩ := Store.J_entry_of_reachable hR hBj'
    have hEJ : E'.root = (tr.state y k).fg.J.root := hEr'.trans hBjJ
    have hFh := h_le_of_store_anc hR hFJ
    rcases hEg with rfl | ⟨hEh', -⟩
    · have he := hcoh.1 hE' hJm hEJ
      rw [← he] at hFJ
      have hFg := Anc.antisymm hcoh hFJ (hgen _ hFm)
      have := hjmax (hFg ▸ hgen E hE)
      omega
    · rw [← hEJ, hEh', hBjhj] at hFh
      have := h_le_of_store_anc hR hEF
      omega

/-- Replay states in one honest store agree on equal-height justifications. -/
private theorem J_eq_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree)
    (hB' : B' ∈ (tr.state y i).fg.tree)
    (he : ((tr.state y i).fg.σ B.root).hj = ((tr.state y i).fg.σ B'.root).hj) :
    ((tr.state y i).fg.σ B.root).J = ((tr.state y i).fg.σ B'.root).J :=
  Store.J_eq_of_hj_eq_of_safe (fg_reachable_at hrun ht hle hy) (fg_reachable_at hrun ht hle hy)
    hf (held_atts_safe_one hrun ht hle hy) hB hB' he

/-- A lock at the cache's justified height names the cache's justified root. -/
theorem lock_root_eq_J_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) (hj : (tr.state y i).fg.hj = h) :
    r = (tr.state y i).fg.J.root := by
  have hr := hrun.upTo ht
  have hs := Trace.upTo_state tr y hle
  obtain ⟨k, hk, att, hsa, hfin⟩ := (record_facts_at hrun ht hle hy).2.2 h r hl
  obtain ⟨B, hB, hBj, hBJ⟩ := Healing.signed_fin_justified hr hy
    ((RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hsa⟩) hfin
  have hB' := Compose.tree_mono hr.toLocalRun hy hk.le hB
  have hσ := Healing.σ_eq_honest hr (hnc.upTo _) hy hy hB hB'
  rw [hσ, hs] at hBj hBJ
  rw [hs] at hB'
  obtain ⟨-, -, -, ⟨Bj, hBjt, hBjJ, hBjhj⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ (fg_reachable_at hrun ht hle hy)
  have he := J_eq_at hrun ht hle hy hf hB' hBjt (by omega)
  exact hBJ.symm.trans (he.trans hBjJ)

end Consensus.Goldilocks.Healing.Growing

end
