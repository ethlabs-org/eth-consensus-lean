module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

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

/-- A held chain supplies genuine signatures from validators honest at its reading time. -/
private theorem held_chain_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree) :
    ∃ c : List (SA.Blk sp.n (List (FG.Att sp.n))),
      sp.toParams.fg.chainState (c.map Block.fgView) = some ((tr.state y i).fg.σ B.root) ∧
      (∀ r ∈ sp.toParams.fg.roots (c.map Block.fgView),
        ∃ Y ∈ (tr.state y i).fg.tree, Y.root = r ∧ (tr.state y i).fg.Anc Y B) ∧
      ∀ a ∈ sp.toParams.fg.chainAtts (c.map Block.fgView), a.val ∈ H t →
        ∃ k < i, tr.SignAt a.val k a := by
  have hR := fg_reachable_at hrun ht hle hy
  obtain ⟨c, hc, hl, hlast, hσ⟩ := Store.chain_state_of_chain _ _ _ _ hR B hB
  obtain ⟨-, -, hg, -⟩ := Store.accepted_tree _ _ _ _ hR
  have hanc := Store.anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨c, hσ, fun r hr => ?_, fun a ha hav => ?_⟩
  · obtain ⟨Y, hY, hYr⟩ : ∃ Y ∈ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :: c,
        Y.root = r := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hr
    refine ⟨Y, ?_, hYr, hanc Y hY⟩
    rcases List.mem_cons.mp hY with rfl | h
    exacts [hg, hc _ h]
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.mp ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.mp hX
    have hs := Trace.upTo_state tr y hle
    have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [hs]; exact hc X hXc
    rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hXt with rfl | ⟨k, hk, hacc⟩
    · cases haX
    · obtain ⟨k', hk', hs'⟩ := hrun.toLocalRun.att_unforgeable y k a
        (hrun.antitone (hle k hk) hy)
        (Or.inr ⟨X, ⟨true, ((Trace.upTo_callAt tr).mp hacc).2⟩, haX⟩)
        (hrun.antitone (hle k hk) hav)
      exact ⟨k', hk'.trans hk, hs'⟩

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

/-- In one honest store a finalized replay target precedes every higher state. -/
private theorem finalized_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    (hFt : F ∈ (tr.state y i).fg.tree) (hFr : F.root = ((tr.state y i).fg.σ X.root).F)
    (hW : W ∈ (tr.state y i).fg.tree)
    (hlt : ((tr.state y i).fg.σ X.root).hF < ((tr.state y i).fg.σ W.root).h) :
    (tr.state y i).fg.Anc F W := by
  have hR := fg_reachable_at hrun ht hle hy
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain_at hrun ht hle hy hX
  obtain ⟨c₂, h₂, hr₂, ha₂⟩ := held_chain_at hrun ht hle hy hW
  obtain ⟨-, -, -, -, hF0, -⟩ := FG.chain_invariants sp.toParams.fg _ _ h₁
  suffices hmem : F.root ∈ sp.toParams.fg.roots (c₂.map Block.fgView) by
    obtain ⟨Y, hY, hYr, hYW⟩ := hr₂ _ hmem
    rwa [hcoh.1 hY hFt hYr] at hYW
  rw [hFr]
  rcases Nat.eq_zero_or_pos ((tr.state y i).fg.σ X.root).hF with h0 | h0
  · rw [hF0 h0]
    exact List.mem_cons_self
  by_contra hnot
  obtain ⟨S, hS, hSv⟩ := sp.toParams.fg.finalization_meets_crossing h₁ h₂ h0 hlt hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H t := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard (s := (S : Set (Fin sp.toParams.fg.n))) (t := (H t)ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : sp.toParams.fg.n = sp.n := rfl
    have : ((H t)ᶜ : Set (Fin sp.toParams.fg.n)).ncard = ((H t)ᶜ : Set (Fin sp.n)).ncard := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  obtain ⟨k, hk, hka⟩ := ha₁ a ha hv
  obtain ⟨l, hl, hlb⟩ := ha₂ b hb (hab.1 ▸ hv)
  rw [← hab.1] at hlb
  exact not_slashable_at hrun ht hv (hle k hk) (hle l hl) hka hlb hab

/-- A store's finalized cache lies below a held block above its justified height. -/
private theorem F_anc_of_hj_lt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree)
    (hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F B := by
  have hR := fg_reachable_at hrun ht hle hy
  obtain ⟨-, hcoh, hg, hgen⟩ := Store.accepted_tree _ _ _ _ hR
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Store.cache_invariants _ _ _ _ hR
  have hgF := hgen _ hFm
  have hgenF : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      (tr.state y i).fg.Anc (tr.state y i).fg.F B := fun he => by
    rw [hcoh.1 hFm hg he]
    exact hgen B hB
  rcases Store.fin_pair_entry hR hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgenF (hBfF.symm.trans he)
  obtain rfl : W = (tr.state y i).fg.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := Store.J_entry_of_reachable hR hBj
  obtain rfl : E = (tr.state y i).fg.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · rw [hEg] at hFJ
    exact hgenF (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc hR hFJ
  exact finalized_anc_at hrun ht hle hy hf hBf hFm hBfF.symm hB (by omega)

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

private theorem mem_foldl_target {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

private theorem justification_quorum (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ : FG.ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hT ⊢
  dsimp only at hT
  have ht₀ : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]),
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
    intro v hv
    rcases hT v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := ht v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hq₀ : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]),
        a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false := fun h1 =>
    let ⟨Q, hQ, hv⟩ := hq h1
    ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  obtain ⟨F, hF', σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨⟨hq', -⟩, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨by simp [FG.ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [FG.ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩

/-- Replay states in one honest store agree on equal-height justifications. -/
private theorem J_eq_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree)
    (hB' : B' ∈ (tr.state y i).fg.tree)
    (he : ((tr.state y i).fg.σ B.root).hj = ((tr.state y i).fg.σ B'.root).hj) :
    ((tr.state y i).fg.σ B.root).J = ((tr.state y i).fg.σ B'.root).J := by
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain_at hrun ht hle hy hB
  obtain ⟨c₂, h₂, -, ha₂⟩ := held_chain_at hrun ht hle hy hB'
  rcases Nat.eq_zero_or_pos ((tr.state y i).fg.σ B.root).hj with h0 | h0
  · rw [(FG.chain_invariants sp.toParams.fg _ _ h₁).2.2.2.1 h0,
      (FG.chain_invariants sp.toParams.fg _ _ h₂).2.2.2.1 (he ▸ h0)]
  by_contra hne
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (justification_quorum sp.toParams.fg h₁).2 h0
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (justification_quorum sp.toParams.fg h₂).2 (he ▸ h0)
  obtain ⟨v, hvQ, hv⟩ : ∃ v ∈ Q₁ ∩ Q₂, v ∈ H t := by
    by_contra! hS
    have h1 := (FG.quorum_intersection sp.toParams.fg Q₁ Q₂ hQ₁ hQ₂).1
    have hcard := Set.ncard_le_ncard
      (s := ((Q₁ ∩ Q₂ : Finset _) : Set (Fin sp.toParams.fg.n))) (t := (H t)ᶜ) hS
    rw [Set.ncard_coe_finset] at hcard
    have : ((H t)ᶜ : Set (Fin sp.toParams.fg.n)).ncard = ((H t)ᶜ : Set (Fin sp.n)).ncard := rfl
    have : sp.toParams.fg.n = sp.n := rfl
    omega
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hvQ).1
  obtain ⟨b, hb, hvb, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hvQ).2
  obtain ⟨k, hk, hka⟩ := ha₁ a ha hv
  obtain ⟨l, hl, hlb⟩ := ha₂ b hb (hvb ▸ hv)
  rw [hvb] at hlb
  exact not_slashable_at hrun ht hv (hle k hk) (hle l hl) hka hlb
    ⟨hvb.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, he], hat, hbt, by rw [haT, hbT]; exact hne⟩)⟩

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
