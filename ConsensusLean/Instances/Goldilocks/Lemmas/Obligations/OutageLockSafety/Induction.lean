module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: the cut induction

`outage_lock_inv`: from the premise package and the S5 step `hS5`, the outage lock invariant
holds at every cut. The step from `i` to `i + 1` proves, in order: (H) for the casts at cut `i`
(pre-`b₀` by S2, `A₀` by the protection at `i`, §7.2), S5V at cut `i` (`hS5 i`), (R) for the
results at cut `i` (§5.1), (i) at `i + 1` (§5.2), (SRC) at `i` (§6.1), OB-F and (VA) at `i + 1`
(§6.2, §6.3), and the protections at `i + 1` (§7.1), with their bases from the arming inputs: the
label-`(j₀ − 1)` lock, and the label-`j₀` cover with (F), (VA) and (N) discharged from the
invariant at the update's cut (§7.3). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

private theorem ts_add (a b : Nat) :
    sp.ts ((a + b : Nat) : Int) = sp.ts (a : Int) + 4 * sp.Δ * b := by
  simp only [SAParams.ts]; push_cast; ring

/-- The time of the label-`(j₀ − 1)` update is `t_{j₀} + 2Δ ≤ b₀`. -/
private theorem prev_update_time (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c (D.j₀ - 1) ℓ) : tr.time c = sp.ts D.j₀ + 2 * sp.Δ := by
  have ht : tr.time c = sp.ts ((D.j₀ - 1 : Nat) : Int) + 6 * sp.Δ := hu.2.2.1
  have h := ts_add (sp := sp) (D.j₀ - 1) 1
  rw [Nat.sub_add_cancel (by have := D.hσ; omega)] at h
  push_cast at h
  linarith

/-- The protected block is in `x`'s frame at its label-`j₀` update when `Σ.F ⪯ P` there: the
label-`(j₀ − 1)` base (`lockPrev`) put it in the tree earlier (§7.3, VA). -/
private theorem prev_mem (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hFP : Anc (tr.HonestBlocks H) (tr.state x c).fg.F D.P) :
    D.P ∈ (Node.frame (tr.state x c)).tree := by
  have hxH := D.hA₀ hx
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
  by_cases hg : D.P.root = sp.genesisRoot
  · -- a genesis `P` below `Σ.F` is `Σ.F`
    obtain ⟨hFt, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable D.hrun.toLocalRun hxH c)
    have := Anc.antisymm D.coherent hFP (D.anc_of_genesis hg ⟨x, hxH, c, hFt⟩)
    rw [← this]
    exact (frameOK_state D.hrun.toLocalRun hxH c).rooted.1
  obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
    ⟨x, hxH, c, ⟨_, projAC_callAt.1 hu.1⟩, by linarith⟩
  have ht₁ := prev_update_time D hu₁
  have hc₁ : c₁ ≤ c := by
    by_contra h
    have := D.hrun.time_mono (show c ≤ c₁ by omega)
    linarith
  have hP₁ : D.P ∈ (tr.state x c₁).fg.tree := by
    rcases prevBase_iff.1 hbase with hroot | ⟨L, f, hL, hPL, -⟩
    · obtain ⟨hFt, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable D.hrun.toLocalRun hxH c₁)
      have h := honest_held_anc D.hrun D.hnc hxH hroot hFt
      by_cases hne : D.P = (tr.state x c₁).fg.F
      · exact hne ▸ hFt
      · exact (h.mem hne).1
    · have hfr : ℓ₁.frame = Node.frame (tr.state x c₁) :=
        (D.hrun.cutLaw x hxH c₁ _ (projAC_callAt.1 hu₁.1)).1
      have := SA.mem_of_anc hPL hL
      rw [hfr] at this
      exact this.1
  have hPt := tree_mono D.hrun.toLocalRun hxH hc₁ hP₁
  exact frame_mem_of_tree D.hrun hxH le_rfl hPt (honest_held_anc D.hrun D.hnc hxH hFP hPt)

namespace OutageLockInv

/-- **The arming inputs (F), (VA), (N) at the label-`j₀` update** (§7.3): from the invariant at a
cut `≥ c`, the cover base holds at `x`'s label-`j₀` update at cut `c`. -/
theorem cover_base {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} (hci : c ≤ i) {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hcond : Compatible (tr.HonestBlocks H) (tr.state x c).fg.F D.P →
     (Anc (tr.HonestBlocks H) (tr.state x c).fg.F D.P → ℓ.frame.AncestorCandidate D.P) →
     (∀ y ∈ D.A₀, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = D.j₀ + 1 → j < c →
        SA.VoteExtends (tr.HonestBlocks H) e.msg D.P) →
     CoverBase tr H D.P D.j₀ x c ℓ) :
    CoverBase tr H D.P D.j₀ x c ℓ := by
  have hxH := D.hA₀ hx
  have hfr : ℓ.frame = Node.frame (tr.state x c) :=
    (D.hrun.cutLaw x hxH c _ (projAC_callAt.1 hu.1)).1
  have hK := sp.two_le_k
  refine hcond (hinv.caches x hxH c hci).1 (fun hFP => ?_) fun y hy j e hv hs hjc => ?_
  · rw [hfr]
    exact hinv.viable x hxH c hci (prev_mem D hx hu hFP)
  · by_cases hj : tr.time j ≤ D.b₀
    · exact D.vote_extends_pre (D.hA₀ hy) hv hj (by have := D.hσ; omega)
    · exact hinv.votes y (D.hA₀ hy) j (by omega) e hv (by have := D.hσ; omega) (by omega)
        (Or.inr hy)

/-- **(H) for a cast of `A₀` after `b₀`** (§7.2): through the label-`(j₀ − 1)` protection for
slots `≤ j₀ − 1 + k`, and through the cover protection for slot `j₀ + k`. -/
theorem cohort_vote_extends {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x i e)
    (hsK : e.msg.slot ≤ D.j₀ + sp.k) (hb : D.b₀ < tr.time i) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hxH := D.hA₀ hx
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hK := sp.two_le_k
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hσ := D.hσ
  obtain ⟨hts, hte⟩ := OutageVoteInv.ts_le_cast D hxH hv
  have hsl : e.msg.slot = sp.slot (tr.time i) := by
    obtain ⟨ℓ, hc, he⟩ := hv
    exact (SA.castAt_spec hr hxH ⟨hc, he⟩).2.1
  have hslot_prev : sp.slot (tr.time (i - 1)) ≤ e.msg.slot := by
    rw [hsl]
    exact SA.slot_mono sp (D.hrun.time_nonneg _) (D.hrun.time_mono (Nat.sub_le i 1))
  -- the slot is after `j₀`
  have hs : D.j₀ + 1 ≤ e.msg.slot := by
    by_contra h
    have := ts_le_ts (sp := sp) (show e.msg.slot ≤ D.j₀ by omega)
    linarith [D.hj₀.1]
  have hva := hinv.viable x hxH i le_rfl
  by_cases hg : D.P.root = sp.genesisRoot
  · exact D.vote_extends_of_genesis hg hxH hv
  have hcall : tr.IsCall x i := by
    obtain ⟨ℓ, hc, -⟩ := hv
    exact ⟨_, projAC_callAt.1 hc⟩
  by_cases hprev : e.msg.slot ≤ D.j₀ - 1 + sp.k
  · obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
      ⟨x, hxH, i, hcall, by linarith [D.hj₀.1]⟩
    have ht₁ := prev_update_time D hu₁
    have hc₁ : c₁ < i := by
      by_contra h
      have := D.hrun.time_mono (show i ≤ c₁ by omega)
      linarith [D.hj₀.1]
    have hp := hinv.protPrev x hx c₁ ℓ₁ hu₁ hbase i hc₁ le_rfl (by omega)
    exact hinv.vote_extends_of_prot hxH (by omega) (by omega) hva hp hv
  · have h2 := ts_le_ts (sp := sp) (show D.j₀ + 2 ≤ e.msg.slot by omega)
    have h3 : sp.ts ((D.j₀ + 2 : Nat) : Int) = sp.ts (D.j₀ : Int) + 8 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    obtain ⟨c, ℓ, hu, -, hcond⟩ := D.lockCover x hx hg ⟨x, hxH, i, hcall, by linarith⟩
    have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
    have hc : c < i := by
      by_contra h
      have := D.hrun.time_mono (show i ≤ c by omega)
      have h2 := ts_le_ts (sp := sp) (show D.j₀ + 2 ≤ e.msg.slot by omega)
      have h3 : sp.ts ((D.j₀ + 2 : Nat) : Int) = sp.ts (D.j₀ : Int) + 8 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    have hp := hinv.protCover x hx c ℓ hu (hinv.cover_base hx hc.le hu hcond) i hc le_rfl
      (by omega)
    exact hinv.vote_extends_of_prot hxH (by omega) (by omega) hva hp hv

end OutageLockInv

/-- A lock of label `j` and expiry at least `m` on a frame block above `P`, held after an update
at cut `c`, gives the protection at `c + 1` when `Σ.F` there is compatible with `P`. -/
private theorem prot_of_lock (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n}
    (hx : x ∈ H) {c q : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c q ℓ)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    {l : SA.Lock} (hl : l ∈ (tr.state x (c + 1)).ac.locks) {j m : Nat} (hlj : l.slot = j)
    (hle : m ≤ l.expiry) {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ℓ.frame.tree)
    (hLr : L.root = l.block) (hPL : ℓ.frame.Anc D.P L) :
    Prot D x (c + 1) j m := by
  by_cases hroot : Anc (tr.HonestBlocks H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot)
  have hfr : ℓ.frame = Node.frame (tr.state x c) :=
    (D.hrun.cutLaw x hx c _ (projAC_callAt.1 hu.1)).1
  rw [hfr] at hL hPL
  have hP : D.P ∈ (tr.state x c).fg.toFrame.tree := SA.mem_of_anc hPL hL
  have hPt := tree_mono D.hrun.toLocalRun hx (Nat.le_succ c) hP.1
  have hP' : D.P ∈ (tr.state x (c + 1)).fg.toFrame.tree :=
    frame_mem_of_tree D.hrun hx le_rfl hPt
      (honest_held_anc D.hrun D.hnc hx (hF.resolve_right hroot) hPt)
  obtain ⟨hL', hPL'⟩ := floor_frame_transport D.hrun hx (Nat.le_succ c) hP' hL hPL
  exact prot_iff.2 (Or.inl ⟨l, hl, hlj, hle, L, hL', hLr, hPL'⟩)

/-- The label-`(j₀ − 1)` base gives the protection at the cut after the update, when `Σ.F` there
is compatible with `P`. -/
private theorem prot_of_prevBase (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n}
    (hx : x ∈ H) {c j : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c j ℓ)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D.P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks) :
    Prot D x (c + 1) j (j + sp.k) := by
  obtain ⟨L, f, hL, hPL, hl⟩ := hbase
  exact prot_of_lock D hx hu hF hl rfl le_rfl hL rfl hPL

/-- **The base of the cover protection** (§7.3): the cover base at `x`'s label-`j₀` update at cut
`c`, with the caches at `c` and `c + 1`, gives the label-`j₀` protection at `c + 1`. -/
private theorem prot_of_coverBase (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hFc : Compatible (tr.HonestBlocks H) (tr.state x c).fg.F D.P)
    (hF : Compatible (tr.HonestBlocks H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : CoverBase tr H D.P D.j₀ x c ℓ) : Prot D x (c + 1) D.j₀ (D.j₀ + sp.k) := by
  have hxH := D.hA₀ hx
  have hFm := Healing.run_F_mono D.hrun.toLocalRun hxH (Nat.le_succ c)
  have hfr : ℓ.frame = Node.frame (tr.state x c) :=
    (D.hrun.cutLaw x hxH c _ (projAC_callAt.1 hu.1)).1
  by_cases hroot : Anc (tr.HonestBlocks H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot)
  rcases coverBase_iff.1 hbase with hroot₀ | ⟨L, f, hPL, hl⟩
  · exact absurd (hroot₀.trans hFm) hroot
  · -- a fresh label-`j₀` lock above `P`
    have hFcP : Anc (tr.HonestBlocks H) (tr.state x c).fg.F D.P :=
      hFc.resolve_right fun h => hroot (h.trans hFm)
    have hP := prev_mem D hx hu hFcP
    rw [← hfr] at hP
    have hL : L ∈ ℓ.frame.tree := by
      by_cases hne : D.P = L
      · exact hne ▸ hP
      · exact (hPL.mem hne).2
    exact prot_of_prevBase D hxH hu hF ⟨L, f, hL, hPL, hl⟩

/-- **The outage lock invariant at every cut**: from the premise package and the S5
step at each cut. -/
theorem outage_lock_inv (D : OutageLockPremises tr H proposer dg) (hS5 : OutageS5StepAt D) :
    ∀ i, OutageLockInv D i := by
  have hU := D.coherent
  have hf := D.two_faults_lt
  have hK := sp.two_le_k
  have hσ := D.hσ
  have hcand : ∀ n, (∀ x ∈ H, ∀ k < n, ∀ ℓ C, SA.ToFGAt tr.projAC x k ℓ C →
      Compatible (tr.HonestBlocks H) C D.P) → ∀ y ∈ H,
      (Compatible (tr.HonestBlocks H) (tr.state y n).fg.F D.P ∧
        Compatible (tr.HonestBlocks H) (tr.state y n).fg.J D.P) ∧
      (D.P ∈ (Node.frame (tr.state y n)).tree →
        (Node.frame (tr.state y n)).AncestorCandidate D.P) := fun n hsrc y hy =>
    ⟨caches_compatible D.hrun D.hnc hf hy D.hP.1 (rows_sourced D.hrun D.hnc hsrc hy),
      fun hPt => held_candidate_of_rows D.hrun D.hnc hf hy n (rows_sourced D.hrun D.hnc hsrc hy)
        (fun _ h => h) hPt⟩
  intro i
  induction i with
  | zero =>
    have hv0 : OutageVoteInv D 0 := ⟨fun _ _ k hk => absurd hk (Nat.not_lt_zero k),
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    refine ⟨hv0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k), fun y hy k hk l hl => ?_,
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k), fun y hy k hk => ?_, fun y hy k hk => ?_,
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _)⟩
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact hv0.locks_compatible (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) hy hl
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact (hcand 0 (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) y hy).1
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact (hcand 0 (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) y hy).2
  | succ i hinv =>
    -- 1. (H) and 1′. S5V at cut `i`
    have hvotes : ∀ x ∈ H, ∀ e, SA.VoteAt tr.projAC x i e → D.σ < e.msg.slot →
        e.msg.slot ≤ D.j₀ + sp.k → (tr.time i ≤ D.b₀ ∨ x ∈ D.A₀) →
        SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
      intro x hx e hv hs hsK hpre
      by_cases hb : tr.time i ≤ D.b₀
      · exact D.vote_extends_pre hx hv hb hs
      · exact hinv.cohort_vote_extends (hpre.resolve_left hb) hv hsK (not_le.1 hb)
    have hvi : OutageVoteInv D (i + 1) :=
      ⟨fun x hx k hk e hv hs hsK hpre => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.votes x hx k hk e hv hs hsK hpre
          · exact hvotes x hx e hv hs hsK hpre,
        fun x hx k hk e hv hs => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.late x hx k hk e hv hs
          · exact outageS5StepAt_iff.1 hS5 k hinv x hx e hv hs⟩
    -- 2. (R) at cut `i`
    have hres : ∀ y ∈ H, ∀ k < i + 1, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
        (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P := by
      intro y hy k hk m C CV hR hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hinv.results y hy k hk m C CV hR hm
      · exact hinv.toOutageVoteInv.result_compatible hy hR hm
    -- 3. (i) at `i + 1`
    have hlocks : ∀ y ∈ H, ∀ k ≤ i + 1, ∀ l ∈ (tr.state y k).ac.locks,
        ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
      intro y hy k hk l hl
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.locks y hy k hk l hl
      · exact hvi.locks_compatible hres hy hl
    -- 4. (SRC) at `i`
    have hsrc : ∀ y ∈ H, ∀ k < i + 1, ∀ ℓ C, SA.ToFGAt tr.projAC y k ℓ C →
        Compatible (tr.HonestBlocks H) C D.P := by
      intro y hy k hk ℓ C h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hinv.sources y hy k hk ℓ C h
      · exact source_compatible D.hrun D.hnc hy (hinv.locks y hy k le_rfl) h
    -- 5. OB-F and (VA) at `i + 1`
    have hnew := hcand (i + 1) hsrc
    have hcaches : ∀ y ∈ H, ∀ k ≤ i + 1, Compatible (tr.HonestBlocks H) (tr.state y k).fg.F D.P ∧
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J D.P := by
      intro y hy k hk
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.caches y hy k hk
      · exact (hnew y hy).1
    have hviable : ∀ y ∈ H, ∀ k ≤ i + 1, D.P ∈ (Node.frame (tr.state y k)).tree →
        (Node.frame (tr.state y k)).AncestorCandidate D.P := by
      intro y hy k hk
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.viable y hy k hk
      · exact (hnew y hy).2
    have hslot_mono : sp.slot (tr.time (i - 1)) ≤ sp.slot (tr.time i) :=
      SA.slot_mono sp (D.hrun.time_nonneg _) (D.hrun.time_mono (Nat.sub_le i 1))
    -- 6. the protections at `i + 1`
    refine ⟨hvi, hres, hlocks, hsrc, hcaches, hviable, ?_, ?_⟩
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protPrev x hx c ℓ hu hbase k hck hk hkK
      have hxH := D.hA₀ hx
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ - 1 + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · exact hinv.prot_step hxH (by omega) hkK (hinv.viable x hxH i le_rfl)
          (hcaches x hxH (i + 1) le_rfl).1
          (hinv.protPrev x hx c ℓ hu hbase i hci le_rfl (hslot_mono.trans hkK))
      · rcases prevBase_iff.1 hbase with hroot | hlock
        · exact prot_iff.2 (Or.inr (hroot.trans
            (Healing.run_F_mono D.hrun.toLocalRun hxH (Nat.le_succ c))))
        · exact prot_of_prevBase D hxH hu (hcaches x hxH (c + 1) le_rfl).1 hlock
    · intro x hx c ℓ hu hbase k hck hk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protCover x hx c ℓ hu hbase k hck hk hkK
      have hxH := D.hA₀ hx
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · have hva := hinv.viable x hxH i le_rfl
        have hF := (hcaches x hxH (i + 1) le_rfl).1
        exact hinv.prot_step hxH (by omega) hkK hva hF (hinv.protCover x hx c ℓ hu hbase i hci
          le_rfl (hslot_mono.trans hkK))
      · exact prot_of_coverBase D hx hu (hinv.caches x hxH c le_rfl).1
          (hcaches x hxH (c + 1) le_rfl).1 hbase

end Consensus.Goldilocks.Compose

end
