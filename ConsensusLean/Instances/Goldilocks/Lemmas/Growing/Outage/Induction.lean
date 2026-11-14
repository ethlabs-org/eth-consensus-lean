module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety under growing faults: the cut induction

`outage_lock_inv_at`: from the premise package and the step `hS5` (`OutageS5StepAt`), the outage
lock invariant holds at every cut. The step from `i` to `i + 1` proves, in order: (H) for the casts
at cut `i` by nodes honest then (pre-`b₀` by `vote_extends_pre`, `A₀` by the protection at `i`),
S5V at cut `i` (`hS5 i`), (R) for the results at cut `i`, (i) at `i + 1`, (SRC) at `i`, OB-F and
(VA) at `i + 1`, and the protections at `i + 1`.

The per-node fields are read at a time `t` at which the node is honest, after every cut before
the state's cut. OB-F and (VA) at cut `i + 1` are counted at the time of the node's call at `i`
(an honest call, so `2 f_{t_i} < n`), reading the node's state at `i + 1` at `t_i ≤ t`; with no
call of the node at `i` its state is the one at `i`. At cut `0` the store is genesis. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
  {D : OutageLockPremises tr H proposer dg ini}

private theorem ts_add (a b : Nat) :
    sp.ts ((a + b : Nat) : Int) = sp.ts (a : Int) + 4 * sp.Δ * b := by
  simp only [SAParams.ts]; push_cast; ring

/-- The time of the label-`(j₀ − 1)` update is `t_{j₀} + 2Δ ≤ b₀`. -/
private theorem prev_update_time (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c (D.j₀ - 1) ℓ) : tr.time c = sp.ts D.j₀ + 2 * sp.Δ := by
  have ht : tr.time c = sp.ts ((D.j₀ - 1 : Nat) : Int) + 6 * sp.Δ := hu.2.2.1
  have h := ts_add (sp := sp) (D.j₀ - 1) 1
  rw [Nat.sub_add_cancel (by have := D.hσ; omega)] at h
  push_cast at h
  linarith

/-- The cuts before `c + 1` are at times `≤ t_c`. -/
private theorem before_succ (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (c : Nat) : ∀ k < c + 1, tr.time k ≤ tr.time c :=
  fun _ hk => hrun.time_mono (Nat.lt_succ_iff.1 hk)

/-- The cuts before `c` are at times `≤ t_c`. -/
private theorem before (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (c : Nat) : ∀ k < c, tr.time k ≤ tr.time c :=
  fun _ hk => hrun.time_mono hk.le

/-- The protected block is in the frame of `x ∈ A₀` at its label-`j₀` update, at which `x` is
honest, when `Σ.F ⪯ P` there: the label-`(j₀ − 1)` base put it in the tree earlier. -/
private theorem prev_mem (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    (hx : x ∈ D.A₀)
    {c : Nat} (hxc : x ∈ H (tr.time c)) {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hFP : Anc (tr.HonestBlocksAt H) (tr.state x c).fg.F D.P) :
    D.P ∈ (Node.frame (tr.state x c)).tree := by
  have hrun := D.hrun
  have hd := hrun.time_nonneg c
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
  by_cases hg : D.P.root = sp.genesisRoot
  · obtain ⟨hFt, -⟩ := Store.cache_invariants _ _ _ _ (reachable_at hrun hd hxc (before hrun c))
    have := Anc.antisymm D.coherent hFP
      (D.anc_of_genesis hg (tree_held_at hd hxc (before hrun c) hFt))
    rw [← this]
    exact (frameOK_at hrun hd hxc (before hrun c)).rooted.1
  obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
    ⟨x, c, hxc, ⟨_, projAC_callAt.1 hu.1⟩, by linarith⟩
  have ht₁ := prev_update_time D hu₁
  have hc₁ : c₁ ≤ c := by
    by_contra h
    have := hrun.time_mono (show c ≤ c₁ by omega)
    linarith
  have hxc₁ : x ∈ H (tr.time c₁) := hrun.antitone (hrun.time_mono hc₁) hxc
  have hd₁ := hrun.time_nonneg c₁
  have hP₁ : D.P ∈ (tr.state x c₁).fg.tree := by
    rcases prevBaseAt_iff.1 hbase with hroot | ⟨L, f, hL, hPL, -⟩
    · obtain ⟨hFt, -⟩ :=
        Store.cache_invariants _ _ _ _ (reachable_at hrun hd₁ hxc₁ (before hrun c₁))
      have h := held_anc_at hrun D.hnc hd₁ hxc₁ (before hrun c₁) hroot hFt
      by_cases hne : D.P = (tr.state x c₁).fg.F
      · exact hne ▸ hFt
      · exact (h.mem hne).1
    · have hfr := frame_of_projAC_at hrun hxc₁ hu₁.1
      have := SA.mem_of_anc hPL hL
      rw [hfr] at this
      exact this.1
  have hPt := tree_mono_at hrun hd hxc (before hrun c) hc₁ hP₁
  exact frame_mem_of_tree_at hrun D.hnc hd hxc (before hrun c) hPt hFP

namespace OutageLockInv

/-- **The arming inputs (F), (VA), (N) at the label-`j₀` update**: from the invariant at a
cut `≥ c`, the cover base holds at the label-`j₀` update at cut `c` of `x ∈ A₀`, honest then. -/
theorem cover_base_at {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} (hxc : x ∈ H (tr.time c)) (hci : c ≤ i)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hcond : Compatible (tr.HonestBlocksAt H) (tr.state x c).fg.F D.P →
     (Anc (tr.HonestBlocksAt H) (tr.state x c).fg.F D.P → ℓ.frame.AncestorCandidate D.P) →
     (∀ y ∈ D.A₀, ∀ j e, HVoteAt tr H y j e → e.msg.slot = D.j₀ + 1 → j < c →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P) →
     CoverBaseAt tr H D.P D.j₀ x c ℓ) :
    CoverBaseAt tr H D.P D.j₀ x c ℓ := by
  have hfr := frame_of_projAC_at D.hrun hxc hu.1
  have hK := sp.two_le_k
  refine hcond (hinv.caches_at_cut hci hxc).1 (fun hFP => ?_) fun y hy j e hv hs hjc => ?_
  · rw [hfr]
    exact hinv.viable_at_cut hci hxc (prev_mem D hx hxc hu hFP)
  · by_cases hj : tr.time j ≤ D.b₀
    · exact D.vote_extends_pre hv hj (by have := D.hσ; omega)
    · exact hinv.votes y j (by omega) e hv (by have := D.hσ; omega) (by omega) (Or.inr hy)

/-- **(H) for a cast of `A₀` after `b₀`**, by a node honest at its cast: through the
label-`(j₀ − 1)` protection for slots `≤ j₀ − 1 + k`, and through the cover protection for slot
`j₀ + k`. -/
theorem holder_vote_extends_at {i : Nat} (hinv : OutageLockInv D i) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x i e)
    (hsK : e.msg.slot ≤ D.j₀ + sp.k) (hb : D.b₀ < tr.time i) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  have hrun := D.hrun
  have hxi := (hVoteAt_iff.1 hv).1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hK := sp.two_le_k
  have hσ := D.hσ
  obtain ⟨hts, hte⟩ := hv.ts_le_cast hrun D.hnc
  have hsl : e.msg.slot = sp.slot (tr.time i) := by
    obtain ⟨-, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
    exact (castAt_spec_at hrun D.hnc hxi ⟨hc, he⟩).2.1
  have hslot_prev : sp.slot (tr.time (i - 1)) ≤ e.msg.slot := by
    rw [hsl]
    exact SA.slot_mono sp (hrun.time_nonneg _) (hrun.time_mono (Nat.sub_le i 1))
  have hs : D.j₀ + 1 ≤ e.msg.slot := by
    by_contra h
    have := ts_le_ts (sp := sp) (show e.msg.slot ≤ D.j₀ by omega)
    linarith [D.hj₀.1]
  have hva := hinv.viable_at_cut le_rfl hxi
  by_cases hg : D.P.root = sp.genesisRoot
  · exact D.vote_extends_of_genesis hg hv
  have hcall := hv.isCall
  by_cases hprev : e.msg.slot ≤ D.j₀ - 1 + sp.k
  · obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
      ⟨x, i, hxi, hcall, by linarith [D.hj₀.1]⟩
    have ht₁ := prev_update_time D hu₁
    have hc₁ : c₁ < i := by
      by_contra h
      have := hrun.time_mono (show i ≤ c₁ by omega)
      linarith [D.hj₀.1]
    have hp := hinv.protPrev x hx c₁ ℓ₁ hu₁ hbase i hc₁ le_rfl hxi (by omega)
    exact hinv.toOutageVoteInv.vote_extends_of_prot_at (by omega) (by omega) (by omega) hva hp hv
  · have h2 := ts_le_ts (sp := sp) (show D.j₀ + 2 ≤ e.msg.slot by omega)
    have h3 : sp.ts ((D.j₀ + 2 : Nat) : Int) = sp.ts (D.j₀ : Int) + 8 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    obtain ⟨c, ℓ, hu, -, hcond⟩ := D.lockCover x hx hg ⟨x, i, hxi, hcall, by linarith⟩
    have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
    have hc : c < i := by
      by_contra h
      have := hrun.time_mono (show i ≤ c by omega)
      linarith
    have hxc : x ∈ H (tr.time c) := hrun.antitone (hrun.time_mono hc.le) hxi
    have hp := hinv.protCover x hx c ℓ hu (hinv.cover_base_at hx hxc hc.le hu hcond) i hc le_rfl
      hxi (by omega)
    exact hinv.toOutageVoteInv.vote_extends_of_prot_at (by omega) (by omega) (by omega) hva hp hv

end OutageLockInv

/-- A lock of label `j` and expiry at least `m` on a frame block above `P`, held after an update
at cut `c` of a node honest then, gives the protection at `c + 1` when `Σ.F` there is compatible
with `P`. -/
private theorem prot_of_lock (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    {c q : Nat}
    (hxc : x ∈ H (tr.time c)) {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c q ℓ)
    (hF : Compatible (tr.HonestBlocksAt H) (tr.state x (c + 1)).fg.F D.P)
    {l : SA.Lock} (hl : l ∈ (tr.state x (c + 1)).ac.locks) {j m : Nat} (hlj : l.slot = j)
    (hle : m ≤ l.expiry) {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ℓ.frame.tree)
    (hLr : L.root = l.block) (hPL : ℓ.frame.Anc D.P L) :
    Prot D x (c + 1) j m := by
  have hrun := D.hrun
  have hd := hrun.time_nonneg c
  by_cases hroot : Anc (tr.HonestBlocksAt H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot)
  have hfr := frame_of_projAC_at hrun hxc hu.1
  rw [hfr] at hL hPL
  have hP : D.P ∈ (tr.state x c).fg.toFrame.tree := SA.mem_of_anc hPL hL
  have hPt := tree_mono_at hrun hd hxc (before_succ hrun c) (Nat.le_succ c) hP.1
  have hP' : D.P ∈ (tr.state x (c + 1)).fg.toFrame.tree :=
    frame_mem_of_tree_at hrun D.hnc hd hxc (before_succ hrun c) hPt (hF.resolve_right hroot)
  obtain ⟨hL', hPL'⟩ :=
    floor_frame_transport_at hrun hd hxc (before_succ hrun c) (Nat.le_succ c) hP' hL hPL
  exact prot_iff.2 (Or.inl ⟨l, hl, hlj, hle, L, hL', hLr, hPL'⟩)

/-- The label-`j` base gives the protection at the cut after the update, when `Σ.F` there is
compatible with `P`. -/
private theorem prot_of_prevBase (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    {c j : Nat} (hxc : x ∈ H (tr.time c))
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c j ℓ)
    (hF : Compatible (tr.HonestBlocksAt H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D.P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks) :
    Prot D x (c + 1) j (j + sp.k) := by
  obtain ⟨L, f, hL, hPL, hl⟩ := hbase
  exact prot_of_lock D hxc hu hF hl rfl le_rfl hL rfl hPL

/-- **The base of the cover protection**: the cover base at the label-`j₀` update at cut `c` of
`x ∈ A₀`, honest then, with the caches at `c` and `c + 1`, gives the label-`j₀` protection at
`c + 1`. -/
private theorem prot_of_coverBase (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {c : Nat} (hxc : x ∈ H (tr.time c))
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC x c D.j₀ ℓ)
    (hFc : Compatible (tr.HonestBlocksAt H) (tr.state x c).fg.F D.P)
    (hF : Compatible (tr.HonestBlocksAt H) (tr.state x (c + 1)).fg.F D.P)
    (hbase : CoverBaseAt tr H D.P D.j₀ x c ℓ) : Prot D x (c + 1) D.j₀ (D.j₀ + sp.k) := by
  have hrun := D.hrun
  have hFm := F_mono_at hrun (hrun.time_nonneg c) hxc (before_succ hrun c) (Nat.le_succ c)
  have hfr := frame_of_projAC_at hrun hxc hu.1
  by_cases hroot : Anc (tr.HonestBlocksAt H) D.P (tr.state x (c + 1)).fg.F
  · exact prot_iff.2 (Or.inr hroot)
  rcases coverBaseAt_iff.1 hbase with hroot₀ | ⟨L, f, hPL, hl⟩
  · exact absurd (hroot₀.trans hFm) hroot
  · have hFcP : Anc (tr.HonestBlocksAt H) (tr.state x c).fg.F D.P :=
      hFc.resolve_right fun h => hroot (h.trans hFm)
    have hP := prev_mem D hx hxc hu hFcP
    rw [← hfr] at hP
    have hL : L ∈ ℓ.frame.tree := by
      by_cases hne : D.P = L
      · exact hne ▸ hP
      · exact (hPL.mem hne).2
    exact prot_of_prevBase D hxc hu hF ⟨L, f, hL, hPL, hl⟩

/-- At cut `0` the store of a node honest then is genesis: the caches are compatible with `P`
and `P`, when in the frame, is a candidate. -/
private theorem caches_zero (D : OutageLockPremises tr H proposer dg ini) {y : Fin sp.n} {t : Time}
    (hd : 0 ≤ t) (hy : y ∈ H t) :
    (Compatible (tr.HonestBlocksAt H) (tr.state y 0).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y 0).fg.J D.P) ∧
    (D.P ∈ (Node.frame (tr.state y 0)).tree →
      (Node.frame (tr.state y 0)).AncestorCandidate D.P) := by
  have hrun := D.hrun
  have h0 : ∀ k < 0, tr.time k ≤ t := fun _ hk => absurd hk (Nat.not_lt_zero _)
  have hst := Trace.upTo_state tr y h0
  have hgen : ∀ X ∈ (tr.state y 0).fg.tree,
      X = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := fun X hX => by
    rcases tree_cases (hrun.upTo hd).toLocalRun hy (i := 0) (by rw [hst]; exact hX) with
      h | ⟨k, hk, -⟩
    · exact h
    · exact absurd hk (Nat.not_lt_zero k)
  obtain ⟨hFt, hJt, -⟩ := Store.cache_invariants _ _ _ _ (reachable_at hrun hd hy h0)
  have hG := (honestAt_genesis_anc hrun D.hP.1).2
  refine ⟨⟨Or.inl (by rw [hgen _ hFt]; exact hG), Or.inl (by rw [hgen _ hJt]; exact hG)⟩,
    fun hPt => Or.inl ?_⟩
  have hfc : (Node.frame (tr.state y 0)).fcRoot = D.P := by
    rw [hgen _ hPt.1]
    change (tr.state y 0).fg.fcRoot = _
    unfold Store.fcRoot
    split_ifs
    · exact hgen _ hJt
    · exact hgen _ hFt
  rw [hfc]
  exact Relation.ReflTransGen.refl

/-- **The outage lock invariant at every cut**: from the premise package and the step
`OutageS5StepAt` at each cut. -/
theorem outage_lock_inv_at (D : OutageLockPremises tr H proposer dg ini) (hS5 : OutageS5StepAt D) :
    ∀ i, OutageLockInv D i := by
  have hrun := D.hrun
  have hK := sp.two_le_k
  have hσ := D.hσ
  have hcand : ∀ n (t : Time), (∀ x k, k < n → x ∈ H (tr.time k) → ∀ ℓ C,
      SA.ToFGAt tr.projAC x k ℓ C → Compatible (tr.HonestBlocksAt H) C D.P) →
      ∀ y, 0 ≤ t → (∀ k < n, tr.time k ≤ t) → y ∈ H t → 2 * (H t)ᶜ.ncard < sp.n →
      (Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F D.P ∧
        Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.J D.P) ∧
      (D.P ∈ (Node.frame (tr.state y n)).tree →
        (Node.frame (tr.state y n)).AncestorCandidate D.P) :=
    fun n t hsrc y ht0 ht hy hf =>
      ⟨caches_compatible_by hrun D.hnc ht0 ht hy hf D.hP.1
        (rows_sourced_by hrun D.hnc hsrc ht0 ht hy),
        fun hPt => held_candidate_of_rows_by hrun D.hnc ht0 ht hy hf
          (rows_sourced_by hrun D.hnc hsrc ht0 ht hy) (fun _ h => h) hPt⟩
  intro i
  induction i with
  | zero =>
    have hv0 : OutageVoteInv D 0 := ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k),
      fun _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    refine ⟨hv0, fun _ k hk => absurd hk (Nat.not_lt_zero k), fun y k t hk ht0 ht hy l hl => ?_,
      fun _ k hk => absurd hk (Nat.not_lt_zero k), fun y k t hk ht0 ht hy => ?_,
      fun y k t hk ht0 ht hy => ?_,
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ k hck hk => absurd (hck.trans_le hk) (Nat.not_lt_zero _)⟩
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact hv0.locks_compatible_at (fun _ k hk => absurd hk (Nat.not_lt_zero k)) ht0 ht hy hl
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact (caches_zero D ht0 hy).1
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact (caches_zero D ht0 hy).2
  | succ i hinv =>
    -- 1. (H) and 1′. S5V at cut `i`
    have hvotes : ∀ x e, HVoteAt tr H x i e → D.σ < e.msg.slot →
        e.msg.slot ≤ D.j₀ + sp.k → (tr.time i ≤ D.b₀ ∨ x ∈ D.A₀) →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
      intro x e hv hs hsK hpre
      by_cases hb : tr.time i ≤ D.b₀
      · exact D.vote_extends_pre hv hb hs
      · exact hinv.holder_vote_extends_at (hpre.resolve_left hb) hv hsK (not_le.1 hb)
    have hvi : OutageVoteInv D (i + 1) :=
      ⟨fun x k hk e hv hs hsK hpre => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.votes x k hk e hv hs hsK hpre
          · exact hvotes x e hv hs hsK hpre,
        fun x k hk e hv hs => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact hinv.late x k hk e hv hs
          · exact outageS5StepAt_iff.1 hS5 k hinv x e hv hs⟩
    -- 2. (R) at cut `i`
    have hres : ∀ y k, k < i + 1 → y ∈ H (tr.time k) → ∀ m C CV,
        SA.ResultAt tr.projAC y k m C CV → (m ≤ D.j₀ ∨ D.r ≤ m) →
        Compatible (tr.HonestBlocksAt H) C D.P :=
      fun y k hk hy m C CV hR hm => hvi.result_compatible_at hk.le hy hR hm
    -- 3. (i) at `i + 1`
    have hlocks : ∀ y k t, k ≤ i + 1 → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
        ∀ l ∈ (tr.state y k).ac.locks, ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧
          Compatible (tr.HonestBlocksAt H) L D.P := by
      intro y k t hk ht0 ht hy l hl
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.locks y k t hk ht0 ht hy l hl
      · exact hvi.locks_compatible_at hres ht0 ht hy hl
    -- 4. (SRC) at `i`
    have hsrc : ∀ y k, k < i + 1 → y ∈ H (tr.time k) → ∀ ℓ C, SA.ToFGAt tr.projAC y k ℓ C →
        Compatible (tr.HonestBlocksAt H) C D.P := by
      intro y k hk hy ℓ C h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hinv.sources y k hk hy ℓ C h
      · exact source_compatible_at hrun D.hnc hy (hinv.locks_at_cut le_rfl hy) h
    -- 5. OB-F and (VA) at `i + 1`, counted at the node's call at `i`
    have hnew : ∀ y (t : Time), 0 ≤ t → (∀ k < i + 1, tr.time k ≤ t) → y ∈ H t →
        (Compatible (tr.HonestBlocksAt H) (tr.state y (i + 1)).fg.F D.P ∧
          Compatible (tr.HonestBlocksAt H) (tr.state y (i + 1)).fg.J D.P) ∧
        (D.P ∈ (Node.frame (tr.state y (i + 1))).tree →
          (Node.frame (tr.state y (i + 1))).AncestorCandidate D.P) := by
      intro y t ht0 ht hy
      have hy' : y ∈ H (tr.time i) := hrun.antitone (ht i (Nat.lt_succ_self i)) hy
      by_cases hc : ∃ c, tr.CallAt y i c
      · exact hcand (i + 1) (tr.time i) hsrc y (hrun.time_nonneg i) (before_succ hrun i) hy'
          (D.two_faults_lt_at hy' hc)
      · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
        have ht' : ∀ k < i, tr.time k ≤ t := fun k hk => ht k (by omega)
        exact ⟨hinv.caches y i t le_rfl ht0 ht' hy, hinv.viable y i t le_rfl ht0 ht' hy⟩
    have hcaches : ∀ y k t, k ≤ i + 1 → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
        Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P ∧
          Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P := by
      intro y k t hk ht0 ht hy
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.caches y k t hk ht0 ht hy
      · exact (hnew y t ht0 ht hy).1
    have hviable : ∀ y k t, k ≤ i + 1 → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
        D.P ∈ (Node.frame (tr.state y k)).tree →
        (Node.frame (tr.state y k)).AncestorCandidate D.P := by
      intro y k t hk ht0 ht hy
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.viable y k t hk ht0 ht hy
      · exact (hnew y t ht0 ht hy).2
    have hcachesC : ∀ y k, k ≤ i + 1 → y ∈ H (tr.time k) →
        Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P :=
      fun y k hk hy => (hcaches y k (tr.time k) hk (hrun.time_nonneg k)
        (fun _ hk' => hrun.time_mono hk'.le) hy).1
    have hslot_mono : sp.slot (tr.time (i - 1)) ≤ sp.slot (tr.time i) :=
      SA.slot_mono sp (hrun.time_nonneg _) (hrun.time_mono (Nat.sub_le i 1))
    -- 6. the protections at `i + 1`
    refine ⟨hvi, hres, hlocks, hsrc, hcaches, hviable, ?_, ?_⟩
    · intro x hx c ℓ hu hbase k hck hk hxk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protPrev x hx c ℓ hu hbase k hck hk hxk hkK
      have hxi : x ∈ H (tr.time i) := hrun.antitone (hrun.time_mono (Nat.le_succ i)) hxk
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ - 1 + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · exact hinv.toOutageVoteInv.prot_step_at hxi (by omega) hkK (by omega)
          (hinv.viable_at_cut le_rfl hxi) (hcachesC x (i + 1) le_rfl hxk)
          (hinv.protPrev x hx c ℓ hu hbase i hci le_rfl hxi (hslot_mono.trans hkK))
      · rcases prevBaseAt_iff.1 hbase with hroot | hlock
        · exact prot_iff.2 (Or.inr (hroot.trans
            (F_mono_at hrun (hrun.time_nonneg c) hxi (before_succ hrun c) (Nat.le_succ c))))
        · exact prot_of_prevBase D hxi hu (hcachesC x (c + 1) le_rfl hxk) hlock
    · intro x hx c ℓ hu hbase k hck hk hxk hkK
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact hinv.protCover x hx c ℓ hu hbase k hck hk hxk hkK
      have hxi : x ∈ H (tr.time i) := hrun.antitone (hrun.time_mono (Nat.le_succ i)) hxk
      replace hkK : sp.slot (tr.time i) ≤ D.j₀ + sp.k := hkK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hck with hci | rfl
      · exact hinv.toOutageVoteInv.prot_step_at hxi (by omega) hkK le_rfl
          (hinv.viable_at_cut le_rfl hxi) (hcachesC x (i + 1) le_rfl hxk)
          (hinv.protCover x hx c ℓ hu hbase i hci le_rfl hxi (hslot_mono.trans hkK))
      · exact prot_of_coverBase D hx hxi hu (hinv.caches_at_cut le_rfl hxi).1
          (hcachesC x (c + 1) le_rfl hxk) hbase

end Consensus.Goldilocks.Compose.Growing

end
