module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Views
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U regular classification and result supporters

The run-level `regular_later_heads_at'` is unresolved. No reachable counterexample is
claimed. The stock proof's viable-head branch used `fcRoot = J` twice: to compare the
origin D with J, and to put D above the reader's fork-choice root. Neither use transfers
to a top contest. In particular, leaf 9 concerns reports, not arbitrary lock origins D.

The existing early-witness argument admits a different geometric route. At each reader,
keep Q viable and establish F ⪯ Q. Totality of D ⪯ Q and F ⪯ Q then puts D below F,
or puts D on the viable path rooted at F. The second case is precisely the input used
by `WitnessUnanimity.witness_frame_at`; no ancestry J ⪯ D is required.

The theorem below proves that geometric step. Its coherent ambient tree is an explicit
premise, not inferred from a stock run. Instantiation over a shadow run still requires
the shadow cache/coherence and relay/early-witness suppliers. It does not certify V-B8.

There is also a signature constraint: the stock early-witness supplier assumes only a
height floor for Q, not source viability. Removing its `hJ` premise literally does not
supply the P-U J clause at height M−1. The regular-later viable-head branch does supply
source viability. Any shadow instantiation must use that evidence rather than quietly
assume that a height bound makes every held Q viable in a top contest.

The run declarations below are interface-only, each with a named unfinished proof.
The classification drops the stock common-J disjunct: a shadow frame is rooted at F.
The literal stock-minus-`hJ` early-witness form is not claimed. Its shared replacement,
carrying source viability, belongs in `EarlyWitness` and is shared with report renewal.
The direct regular-later viable branch has `hv.2`; the optimistic branch obtains `hvQ`
from the viable-tree witness in `SupporterLater`. `FollowWrite` is not changed here.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (Blk Frm)

/-- The frame-level step of the existing witness argument when the root is F.
The ambient coherence premise must come from the shadow run, not a stock-run cast. -/
theorem regular_witness_frame_of_root_F
    {n : Nat} {FGP : Type} {U : Set (Blk n FGP)} {Φ : Frm n FGP}
    (hU : Coherent U) (hΦ : FrameOK Φ) (hsub : Φ.tree ⊆ U)
    (hroot : Φ.fcRoot = Φ.F) {D Q : Blk n FGP}
    (hvQ : Q ∈ Φ.viableHeads) (hDQ : Anc U D Q) :
    Anc U D Φ.F ∨
      (Anc U Φ.F D ∧ D ∈ Φ.tree ∧ Φ.Anc Φ.fcRoot D ∧
        Q ∈ Φ.tree ∧ Q ∈ Φ.viableHeads ∧ Φ.Anc D Q) := by
  have hQt := hΦ.viableHeads_subset hvQ
  have hFQ := (hΦ.rooted.2 Q hQt).mono hsub
  rcases AC.anc_total hU hFQ hDQ with hFD | hDF
  · have hmiddle : ∀ {W}, Φ.Anc Φ.F W → Anc U D W → D ∈ Φ.tree := by
      intro W hpath
      induction hpath with
      | refl =>
        intro hDF
        have he := Anc.antisymm hU hFD hDF
        exact he ▸ hΦ.rooted.1
      | @tail A B hFA hAB ih =>
        intro hDB
        rcases Relation.ReflTransGen.cases_tail hDB with he | ⟨C, hDC, hCB⟩
        · exact he ▸ hAB.2.1
        · have he : C = A := hU.1 hCB.1 (hsub hAB.1)
            (Option.some.inj (hCB.2.2.symm.trans hAB.2.2))
          subst C
          exact ih hDC
    have hDframe := hmiddle (hΦ.rooted.2 Q hQt) hDQ
    have hFDf := AC.anc_tree_of_anc_U hU hΦ hsub hΦ.rooted.1 hFD hDframe
    exact Or.inr ⟨hFD, hDframe, hroot ▸ hFDf, hQt, hvQ,
      AC.anc_tree_of_anc_U hU hΦ hsub hDframe hDQ hQt⟩
  · exact Or.inl hDF

open AC (ACParams ReplayOrder Payload gbar)
open _root_.Consensus.Goldilocks.Growing
open _root_.Consensus.Goldilocks.Healing.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/- R2 interface handoff: these exact signatures belong in Shadow/PU/RegularVotes.lean.
They are comments, not declarations in this file. The shared variables and namespace
are those above. R2 also owns their next-supporter and early-base dependencies.

theorem regular_fast_next_votes_at' {s₀ s M : Nat}
    {isTop : Prop} {J X D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hfast : AC.FastUpdateAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X

theorem regular_slow_next_votes_at' {s₀ s M : Nat}
    {isTop : Prop} {J D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : AC.SlowLockAt tr.projAC x c s D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg D
-/

/-- Temporary interface owned by the shadow service supplier in `Window`. -/
private theorem healthy_base_before_at_pending {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    AC.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  sorry

/-- Temporary static-prefix interface owned by the shadow Compose projection family. -/
private theorem honest_participants_window_before_pending
    {H : Set (Fin sp.n)} {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {K : AC.CommitteeDict sp.n} {a b : Time} {s : Nat}
    (hsync : AC.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ell : ACLabel (goldilocksNode' sp ro)} (hu : AC.UpdateAt tr.projAC X i₀ s ell)
    (hib : tr.time i₀ ≤ b)
    (hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ))
    (hmv : ∀ y ∈ H, y ∈ K.committee s → ∀ i, (tr.state y i).ac.mayVote s = true)
    (hP : ∀ v ∈ (tr.projAC.state X i₀).pool s, v.val ∈ K.committee s)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard) :
    2 * (Hᶜ ∩ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard <
      (AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard := by
  sorry

/-- Actual result provenance supplies an independently honest supporter.
This port still depends on the two named temporary supplier interfaces above. -/
theorem result_honest_supporter_before_at'
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x c s C CV) (hcb : tr.time c ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ z q, z ∈ H (tr.time q) ∧ q < c ∧ ∃ e, AC.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hΔ := sp.toParams.hΔ
  have hd0 := hrun.time_nonneg c
  have hm' := hrun.time_mono
  have hpre := hrun.upTo hd0
  have hS := healthy_base_before_at_pending hK hrun hnc hsvc hawake hf hcatch hd0 hcb
  have hres' := (AC.upTo_resultAt hm').mpr ⟨le_rfl, hres⟩
  obtain ⟨ell, hu, hconf, hCV⟩ := hres'
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ tr.time c := by rw [ht]; linarith
  have hgs : gbar g ≤ sp.ts s := by linarith
  have hs0 : 0 < s := by
    by_contra hn
    have he : s = 0 := by omega
    rw [he] at hm
    simp only [ACParams.ts, Nat.cast_zero, mul_zero] at hm
    linarith [AC.gbar_nonneg g]
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    AC.slot_of_mem sp s (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  have hready : ∀ y ∈ H (tr.time c), (tr.upTo (tr.time c)).awake y (sp.ts s + sp.Δ) ∧
      (tr.upTo (tr.time c)).JoinedAt y (sp.ts s + sp.Δ) := by
    intro y hy
    refine ⟨(Trace.upTo_awake _ _ _).mpr
      ⟨hawake y _ (hrun.antitone hsb hy) (by linarith) (hsb.trans hcb), hsb⟩, ?_⟩
    intro k hk hkt
    have hk₀ := (RunTrace.upTo_restartAt tr).mp hk |>.2
    have hyt := hrun.antitone (hkt.trans hsb) hy
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    refine ⟨hs0, (hnr y k hyt hk₀).trans ?_⟩
    have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
    rw [hcast]
    simp only [ACParams.ts] at hm
    linarith
  have hparts := honest_participants_window_before_pending hpre (hnc.upTo _) (K := K)
    (by rw [RunTrace.upTo_projAC]; exact AC.serviceWindowBefore_of_sync hS.sync)
    hgs hx (by rwa [RunTrace.upTo_projAC]) le_rfl hready
    (fun y hy hyK i => by
      rw [← Compose.projAC_state' hpre.toLocalRun' hy i]
      exact (AC.trace_mayVote_iff (Compose.goldilocks_ac_projection_from' hpre
        (hnc.upTo _)).localRun hy i s).2 hyK)
    (fun v hv => hK.facts.hP.1 _ x hx c (fun _ hk => hm' hk.le) s v (by
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm' hk.le)] at hv))
    (by
      rw [hK.facts.hsize s]
      exact hK.cs2 s hgs (by linarith) _ hd0 hcb)
  rw [RunTrace.upTo_projAC] at hparts
  obtain ⟨z, hz, q, hqc, e, he, hmem, hes, R, hR, hroot, hCR⟩ :=
    AC.result_honest_supporter_of_participants sp hS.run hx ⟨ell, hu, hconf, hCV⟩
      (B := C) .refl hparts.le
  obtain ⟨hqt, he⟩ := AC.upTo_voteAt.mp he
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg c)
  exact ⟨z, q, hrun.antitone hqt hz, hqc, e, he, hmem, hes,
    R, hsub hR, hroot, hCR.mono hsub⟩

/-- Interface-only: the F-rooted classification has no common-J alternative. -/
theorem vote_head_classification_of_service_at' {s₀ M : Nat} {hi : Time}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) hi M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi) (hib : tr.time i ≤ b)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hs₀ : s₀ ≤ e.msg.slot - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((e.msg.slot - 1 : Nat) : Int))
    (hgf : gbar g < AC.freeze sp e.msg.slot) (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      ((Hd ∈ AC.voteDomain sp e.readPoint ell.frame e.msg.slot ∧ Hd ∈ ell.frame.viableHeads) ∨
      (Hd = AC.getAnchor sp e.readPoint ell.frame (tr.time i) ∧
        ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
        ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          AC.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
          sp.ts e.msg.slot ≤ tr.time a ∧ tr.time a < sp.ts e.msg.slot + 2 * sp.Δ ∧
          3 * sp.committeeSize ≤ 4 * (AC.voters CV).ncard ∧ ell.frame.Anc Hd D)) := by
  sorry

end Consensus.Goldilocks.Healing.PU

end
