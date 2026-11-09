module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyRetention
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilySources
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Prot

public section

namespace Consensus.Goldilocks.FamilySafety

set_option backward.isDefEq.respectTransparency false

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}
  {D : OutageLockPremises F tr H proposer dg sg}

private theorem prev_update_time (D : OutageLockPremises F tr H proposer dg sg)
    {x : Fin sp.n} {c : Nat} {ℓ}
    (hu : SA.UpdateAt (F.proj tr.projAC) x c (D.j₀ - 1) ℓ) :
    tr.time c = sp.ts D.j₀ + 2 * sp.Δ := by
  have ht : tr.time c = sp.ts ((D.j₀ - 1 : Nat) : Int) + 6 * sp.Δ := by
    simpa only [F.time, RunTrace.projAC] using hu.2.2.1
  have h : sp.ts ((D.j₀ - 1 + 1 : Nat) : Int) =
      sp.ts ((D.j₀ - 1 : Nat) : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rw [Nat.sub_add_cancel (by have := D.hσ; omega)] at h
  linarith

private theorem prev_mem
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (D : OutageLockPremises F tr H proposer dg sg) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) x c D.j₀ ℓ)
    (hFP : Anc (tr.HonestBlocks H) (tr.state x c).fg.F D.P) :
    D.P ∈ (Node.frame (tr.state x c)).tree := by
  have hxH := D.hA₀ hx
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := by
    simpa only [F.time, RunTrace.projAC] using hu.2.2.1
  by_cases hg : D.P.root = sp.genesisRoot
  · obtain ⟨hFt, -⟩ := Store.cache_invariants _ _ _ _
      (Compose.fg_reachable D.hrun.toLocalRun hxH c)
    have he := Anc.antisymm D.coherent hFP (D.anc_of_genesis hg ⟨x, hxH, c, hFt⟩)
    rw [← he]
    exact (Compose.frameOK_state D.hrun.toLocalRun hxH c).rooted.1
  have hcall : tr.IsCall x c := by
    have hn : tr.node c = x := by simpa only [F.node, RunTrace.projAC] using hu.1.1
    obtain ⟨ℓ', hl', -⟩ := F.frame tr.projAC c ℓ hu.1.2
    exact ⟨_, Compose.projAC_callAt.mp ⟨hn, hl'⟩⟩
  obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg ⟨x, hxH, c, hcall, by linarith⟩
  have ht₁ := prev_update_time D hu₁
  have hc₁ : c₁ ≤ c := by
    by_contra h
    have hh := D.hrun.time_mono (show c ≤ c₁ by omega)
    linarith
  have hP₁ : D.P ∈ (tr.state x c₁).fg.tree := by
    rcases prevBase_iff.mp hbase with hroot | ⟨L, f, hL, hPL, -⟩
    · obtain ⟨hFt, -⟩ := Store.cache_invariants _ _ _ _
        (Compose.fg_reachable D.hrun.toLocalRun hxH c₁)
      have h := honest_held_anc D.hrun.toLocalRun hfg hxH hroot hFt
      by_cases hne : D.P = (tr.state x c₁).fg.F
      · exact hne ▸ hFt
      · exact (h.mem hne).1
    · have hm := SA.mem_of_anc hPL hL
      rw [frame_of_observation D.hrun hxH hu₁.1] at hm
      exact hm.1
  have hPt := Compose.tree_mono D.hrun.toLocalRun hxH hc₁ hP₁
  exact ⟨hPt, honest_held_anc D.hrun.toLocalRun hfg hxH hFP hPt⟩

namespace OutageLockInv

theorem cover_base (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hh : VoteHead (F.proj tr.projAC) H (tr.HonestBlocks H))
    {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} (hci : c ≤ i) {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) x c D.j₀ ℓ)
    (hcond : Compatible (tr.HonestBlocks H) (tr.state x c).fg.F D.P →
     (Anc (tr.HonestBlocks H) (tr.state x c).fg.F D.P → ℓ.frame.AncestorCandidate D.P) →
     (∀ y ∈ D.A₀, ∀ j e, SA.VoteAt (F.proj tr.projAC) y j e →
        e.msg.slot = D.j₀ + 1 → j < c → SA.VoteExtends (tr.HonestBlocks H) e.msg D.P) →
     CoverBase F tr H D.P D.j₀ x c ℓ) : CoverBase F tr H D.P D.j₀ x c ℓ := by
  have hxH := D.hA₀ hx
  have hfr := frame_of_observation D.hrun hxH hu.1
  have hK := sp.two_le_k
  refine hcond (hinv.caches x hxH c hci).1 (fun hFP => ?_) fun y hy j e hv hs hjc => ?_
  · rw [hfr]
    exact hinv.viable x hxH c hci (prev_mem hfg D hx hu hFP)
  · by_cases hj : tr.time j ≤ D.b₀
    · exact D.vote_extends_pre hh (D.hA₀ hy) hv hj (by have := D.hσ; omega)
    · exact hinv.votes y (D.hA₀ hy) j (by omega) e hv (by have := D.hσ; omega)
        (by omega) (Or.inr hy)

theorem cohort_vote_extends (hr : RetentionFacts F tr H) (hd : VoteDominance F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H)
    (hh : VoteHead (F.proj tr.projAC) H (tr.HonestBlocks H))
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (F.proj tr.projAC) x i e)
    (hsK : e.msg.slot ≤ D.j₀ + sp.k) (hb : D.b₀ < tr.time i) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hxH := D.hA₀ hx
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hK := sp.two_le_k
  have hσ := D.hσ
  obtain ⟨hts, hte⟩ := OutageVoteInv.ts_le_cast D ht hxH hv
  have hsl : e.msg.slot = sp.slot (tr.time i) := by
    symm
    apply SA.slot_of_mem sp e.msg.slot hts
    simp only [SAParams.ts] at hte ⊢
    push_cast
    linarith
  have hslot_prev : sp.slot (tr.time (i - 1)) ≤ e.msg.slot := by
    rw [hsl]
    exact SA.slot_mono sp (D.hrun.time_nonneg _) (D.hrun.time_mono (Nat.sub_le i 1))
  have hs : D.j₀ + 1 ≤ e.msg.slot := by
    by_contra h
    have hh := Compose.ts_le_ts (sp := sp) (show e.msg.slot ≤ D.j₀ by omega)
    linarith [D.hj₀.1]
  have hva := hinv.viable x hxH i le_rfl
  by_cases hg : D.P.root = sp.genesisRoot
  · exact D.vote_extends_of_genesis hh hg hxH hv
  have hcall : tr.IsCall x i := by
    obtain ⟨ℓ, hc, -⟩ := hv
    have hn : tr.node i = x := by simpa only [F.node, RunTrace.projAC] using hc.1
    obtain ⟨ℓ', hl', -⟩ := F.frame tr.projAC i ℓ hc.2
    exact ⟨_, Compose.projAC_callAt.mp ⟨hn, hl'⟩⟩
  by_cases hprev : e.msg.slot ≤ D.j₀ - 1 + sp.k
  · obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
      ⟨x, hxH, i, hcall, by linarith [D.hj₀.1]⟩
    have ht₁ := prev_update_time D hu₁
    have hc₁ : c₁ < i := by
      by_contra h
      have hh := D.hrun.time_mono (show i ≤ c₁ by omega)
      linarith [D.hj₀.1]
    exact hinv.toOutageVoteInv.vote_extends_of_prot hr hd ht hxH (by omega) (by omega) hva
      (hinv.protPrev x hx c₁ ℓ₁ hu₁ hbase i hc₁ le_rfl (by omega)) hv
  · have h2 := Compose.ts_le_ts (sp := sp) (show D.j₀ + 2 ≤ e.msg.slot by omega)
    have h3 : sp.ts ((D.j₀ + 2 : Nat) : Int) = sp.ts (D.j₀ : Int) + 8 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    obtain ⟨c, ℓ, hu, -, hcond⟩ := D.lockCover x hx hg ⟨x, hxH, i, hcall, by linarith⟩
    have htc : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := by
      simpa only [F.time, RunTrace.projAC] using hu.2.2.1
    have hc : c < i := by
      by_contra h
      have hh := D.hrun.time_mono (show i ≤ c by omega)
      linarith
    exact hinv.toOutageVoteInv.vote_extends_of_prot hr hd ht hxH (by omega) (by omega) hva
      (hinv.protCover x hx c ℓ hu (hinv.cover_base hfg hh hx hc.le hu hcond) i hc le_rfl
        (by omega)) hv

end OutageLockInv

private theorem prot_of_lock
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (D : OutageLockPremises F tr H proposer dg sg) {x : Fin sp.n} (hx : x ∈ H)
    {c q : Nat} {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) x c q ℓ)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    {l : SA.Lock} (hl : l ∈ ((F.proj tr.projAC).state x (c + 1)).locks)
    {j m : Nat} (hlj : l.slot = j) (hle : m ≤ l.expiry)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ℓ.frame.tree)
    (hLr : L.root = l.block) (hPL : ℓ.frame.Anc D.P L) : Prot D x (c + 1) j m := by
  by_cases hroot : Anc (tr.HonestBlocks H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.mpr (Or.inr hroot)
  have hfr := frame_of_observation D.hrun hx hu.1
  rw [hfr] at hL hPL
  have hP := SA.mem_of_anc hPL hL
  have hPt := Compose.tree_mono D.hrun.toLocalRun hx (Nat.le_succ c) hP.1
  have hP' := honest_held_anc D.hrun.toLocalRun hfg hx (hF.resolve_right hroot) hPt
  have hsub := Compose.tree_mono D.hrun.toLocalRun hx (Nat.le_succ c)
  have h1 : Anc (tr.state x (c + 1)).fg.tree D.P L := (hPL.mono fun _ h => h.1).mono hsub
  exact prot_iff.mpr (Or.inl ⟨l, hl, hlj, hle, L, ⟨hsub hL.1, hP'.trans h1⟩,
    hLr, Anc.restrict hP' h1⟩)

private theorem prot_of_prevBase
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (D : OutageLockPremises F tr H proposer dg sg) {x : Fin sp.n} (hx : x ∈ H)
    {c j : Nat} {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) x c j ℓ)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D.P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ ((F.proj tr.projAC).state x (c + 1)).locks) :
    Prot D x (c + 1) j (j + sp.k) := by
  obtain ⟨L, f, hL, hPL, hl⟩ := hbase
  exact prot_of_lock hfg D hx hu hF hl rfl le_rfl hL rfl hPL

private theorem prot_of_coverBase
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (D : OutageLockPremises F tr H proposer dg sg) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) x c D.j₀ ℓ)
    (hFc : Compatible (tr.HonestBlocks H) (tr.state x c).fg.F D.P)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : CoverBase F tr H D.P D.j₀ x c ℓ) : Prot D x (c + 1) D.j₀ (D.j₀ + sp.k) := by
  have hxH := D.hA₀ hx
  have hFm := Healing.run_F_mono D.hrun.toLocalRun hxH (Nat.le_succ c)
  have hfr := frame_of_observation D.hrun hxH hu.1
  by_cases hroot : Anc (tr.HonestBlocks H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.mpr (Or.inr hroot)
  rcases coverBase_iff.mp hbase with hroot₀ | ⟨L, f, hPL, hl⟩
  · exact absurd (hroot₀.trans hFm) hroot
  · have hFcP := hFc.resolve_right fun h => hroot (h.trans hFm)
    have hP := prev_mem hfg D hx hu hFcP
    rw [← hfr] at hP
    have hL : L ∈ ℓ.frame.tree := by
      by_cases hne : D.P = L
      · exact hne ▸ hP
      · exact (hPL.mem hne).2
    exact prot_of_prevBase hfg D hxH hu hF ⟨L, f, hL, hPL, hl⟩

/-- The whole cut induction uses only observations and named milestone exits.
Evidence sources have an explicit compatibility premise; keep and dominance are not
silently assumed consequences of backward unlock. -/
theorem outage_lock_inv_family (D : OutageLockPremises F tr H proposer dg sg)
    (hp : PoolFacts (F.proj tr.projAC) H) (ht : VoteTiming (F.proj tr.projAC) H)
    (hh : VoteHead (F.proj tr.projAC) H (tr.HonestBlocks H)) (hv : Participants F tr H)
    (hl : LockFacts F tr H) (hr : RetentionFacts F tr H) (hd : VoteDominance F tr H)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hs5 : SourceViableAt tr H) (hsl : SourceLockAt F tr H)
    (he : ∀ y ∈ H, ∀ k C, F.sourceEvidence tr.projAC y k C →
      Compatible (tr.HonestBlocks H) C D.P) (hS5 : OutageS5StepAt D) :
    ∀ i, OutageLockInv D i := by
  have hcand : ∀ n, (∀ x ∈ H, ∀ k < n, ∀ ℓ C, ACToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C D.P) → ∀ y ∈ H,
      (Compatible (tr.HonestBlocks H) (tr.state y n).fg.F D.P ∧
        Compatible (tr.HonestBlocks H) (tr.state y n).fg.J D.P) ∧
      (D.P ∈ (Node.frame (tr.state y n)).tree →
        (Node.frame (tr.state y n)).AncestorCandidate D.P) := fun n hsrc y hy =>
    ⟨caches_compatible_family D.hrun.toLocalRun hfg D.two_faults_lt hy D.hP.1
      (rows_sourced_family D.hrun hfg hs5 hsrc hy),
      fun hPt => held_candidate_of_rows_family D.hrun.toLocalRun hfg D.two_faults_lt hy n
        (rows_sourced_family D.hrun hfg hs5 hsrc hy) (fun _ h => h) hPt⟩
  intro i
  induction i with
  | zero =>
    have hv0 : OutageVoteInv D 0 := ⟨fun _ _ k hk => absurd hk (Nat.not_lt_zero k),
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    refine ⟨hv0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k), fun y hy k hk l hl' => ?_,
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k), fun y hy k hk => ?_, fun y hy k hk => ?_,
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _)⟩
    · obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact hv0.locks_compatible hl ht (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) hy hl'
    · obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact (hcand 0 (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) y hy).1
    · obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact (hcand 0 (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) y hy).2
  | succ i hinv =>
    have hvotes : ∀ x ∈ H, ∀ e, SA.VoteAt (F.proj tr.projAC) x i e → D.σ < e.msg.slot →
        e.msg.slot ≤ D.j₀ + sp.k → (tr.time i ≤ D.b₀ ∨ x ∈ D.A₀) →
        SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
      intro x hx e hv' hs hsK hpre
      by_cases hb : tr.time i ≤ D.b₀
      · exact D.vote_extends_pre hh hx hv' hb hs
      · exact hinv.cohort_vote_extends hr hd ht hh hfg (hpre.resolve_left hb) hv' hsK (not_le.mp hb)
    have hvi : OutageVoteInv D (i + 1) :=
      ⟨fun x hx k hk e hv' hs hsK hpre => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact hinv.votes x hx k hk e hv' hs hsK hpre
          · exact hvotes x hx e hv' hs hsK hpre,
        fun x hx k hk e hv' hs => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact hinv.late x hx k hk e hv' hs
          · exact (outageS5StepAt_iff.mp hS5) k hinv x hx e hv' hs⟩
    have hres : ∀ y ∈ H, ∀ k < i + 1, ∀ m C CV, SA.ResultAt (F.proj tr.projAC) y k m C CV →
        (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P := by
      intro y hy k hk m C CV hR hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hinv.results y hy k hk m C CV hR hm
      · exact hinv.toOutageVoteInv.result_compatible hp ht hv hy hR hm
    have hlocks : ∀ y ∈ H, ∀ k ≤ i + 1, ∀ l ∈ ((F.proj tr.projAC).state y k).locks,
        ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
      intro y hy k hk l hl'
      rcases Nat.le_succ_iff.mp hk with hk | rfl
      · exact hinv.locks y hy k hk l hl'
      · exact hvi.locks_compatible hl ht hres hy hl'
    have hsrc : ∀ y ∈ H, ∀ k < i + 1, ∀ ℓ C, ACToFGAt tr.projAC y k ℓ C →
        Compatible (tr.HonestBlocks H) C D.P := by
      intro y hy k hk ℓ C h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hinv.sources y hy k hk ℓ C h
      · exact source_compatible_family D.hrun hsl hy (hinv.locks y hy k le_rfl) (he y hy k) h
    have hnew := hcand (i + 1) hsrc
    have hcaches : ∀ y ∈ H, ∀ k ≤ i + 1,
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F D.P ∧
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J D.P := by
      intro y hy k hk
      rcases Nat.le_succ_iff.mp hk with hk | rfl
      · exact hinv.caches y hy k hk
      · exact (hnew y hy).1
    have hviable : ∀ y ∈ H, ∀ k ≤ i + 1, D.P ∈ (Node.frame (tr.state y k)).tree →
        (Node.frame (tr.state y k)).AncestorCandidate D.P := by
      intro y hy k hk
      rcases Nat.le_succ_iff.mp hk with hk | rfl
      · exact hinv.viable y hy k hk
      · exact (hnew y hy).2
    have hslot := SA.slot_mono sp (D.hrun.time_nonneg _) (D.hrun.time_mono (Nat.sub_le i 1))
    refine ⟨hvi, hres, hlocks, hsrc, hcaches, hviable, ?_, ?_⟩
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.mp hk with hk | rfl
      · exact hinv.protPrev x hx c ℓ hu hbase k hck hk hkK
      have hxH := D.hA₀ hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hck with hci | rfl
      · exact hinv.toOutageVoteInv.prot_step hr ht hfg hxH (by omega) hkK
          (hinv.viable x hxH i le_rfl) (hcaches x hxH (i + 1) le_rfl).1
          (hinv.protPrev x hx c ℓ hu hbase i hci le_rfl (hslot.trans hkK))
      · rcases prevBase_iff.mp hbase with hroot | hlock
        · exact prot_iff.mpr (Or.inr (hroot.trans
            (Healing.run_F_mono D.hrun.toLocalRun hxH (Nat.le_succ c))))
        · exact prot_of_prevBase hfg D hxH hu (hcaches x hxH (c + 1) le_rfl).1 hlock
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.mp hk with hk | rfl
      · exact hinv.protCover x hx c ℓ hu hbase k hck hk hkK
      have hxH := D.hA₀ hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hck with hci | rfl
      · exact hinv.toOutageVoteInv.prot_step hr ht hfg hxH (by omega) hkK
          (hinv.viable x hxH i le_rfl) (hcaches x hxH (i + 1) le_rfl).1
          (hinv.protCover x hx c ℓ hu hbase i hci le_rfl (hslot.trans hkK))
      · exact prot_of_coverBase hfg D hx hu (hinv.caches x hxH c le_rfl).1
          (hcaches x hxH (c + 1) le_rfl).1 hbase

/-- The original outage package already supplies the collision premise. -/
theorem outage_lock_inv_instance {tr : GoldilocksTrace sp ro}
    (D : Compose.OutageLockPremises tr H proposer dg) (hS5 : Compose.OutageS5StepAt D) :
    ∀ i, Compose.OutageLockInv D i := by
  have hs : OutageS5StepAt D.family := outageS5StepAt_iff.mpr (by
    intro i hi y hy e hv he
    simpa only [Compose.OutageLockPremises.family_P] using
      (Compose.outageS5StepAt_iff.mp hS5) i
      (Compose.OutageLockInv.family_iff.mp hi) y hy e hv
      (by simpa only [Compose.OutageLockPremises.family_j₀] using he))
  have hi := outage_lock_inv_family D.family (poolFacts_goldilocks D.hrun D.hnc)
    (voteTiming_goldilocks D.hrun D.hnc) (voteHead_goldilocks D.hrun D.hnc)
    (participants_goldilocks D.hrun D.hnc) (lockFacts_goldilocks D.hrun D.hnc)
    (retentionFacts_goldilocks D.hrun D.hnc
      (fun _ hf _ hx _ _ hB hv => Compose.unlockKeeps_of_voteCompat D.hrun D.hnc hf hx hB hv))
    (voteDominance_goldilocks D.hrun D.hnc)
    (Compose.projFG_localRun D.hrun D.hnc) (sourceViableAt_goldilocks D.hrun)
    (sourceLockAt_goldilocks D.hrun D.hnc) (fun _ _ _ _ h => False.elim h) hs
  exact fun i => Compose.OutageLockInv.family_iff.mp (hi i)

end Consensus.Goldilocks.FamilySafety

end
