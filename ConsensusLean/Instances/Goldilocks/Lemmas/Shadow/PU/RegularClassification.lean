module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Views
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.StaticCoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Participants
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
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

The run declarations below have no direct unfinished proofs, but their upstream shadow
suppliers remain uncertified. The classification drops the stock common-J disjunct:
a shadow frame is rooted at F. The earlier-call root witness rules out an empty viable
domain at the root; stored older locks use the existing AC write-provenance argument.
The literal stock-minus-`hJ` early-witness form is not claimed. Its shared replacement,
carrying source viability, belongs in `EarlyWitness` and is shared with report renewal.
The direct regular-later viable branch has `hv.2`; the optimistic branch obtains `hvQ`
from the viable-tree witness in `SupporterLater`. `FollowWrite` is not changed here.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (Blk Frm)

open AC (ACParams Payload gbar)
open _root_.Consensus.Goldilocks.Growing
open _root_.Consensus.Goldilocks.Healing.Growing

section Static

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g : Time}

/-- The old stored-lock argument uses only F-root monotonicity and persistence of a
write-frame viable witness; its AC write provenance is unchanged. -/
private theorem old_lock_witness {s₀ M : Nat} {hi : Time}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) (sp.ts s₀) hi M isTop J)
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : Healing.NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hgf : gbar g < AC.freeze sp e.msg.slot)
    {l : AC.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hlabel : s₀ ≤ l.slot) (hold : l.slot < e.msg.slot)
    {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    ∃ a < i, ∃ ell₀ D Q,
      tr.projAC.CallAt y a ell₀ ∧ sp.ts s₀ ≤ tr.time a ∧
      tr.time a < AC.freeze sp e.msg.slot ∧
      ((∃ CV, AC.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        ∃ ell', AC.UpdateAt tr.projAC y a l.slot ell') ∧
      Q ∈ ell₀.frame.viableHeads ∧ Anc (tr.HonestBlocks H) L Q ∧
      Q ∈ ell.frame.viableHeads ∧
      Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have htvote := AC.vote_time_leU hr.toU hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at htvote
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_specU hr.toU hy hc).2.1
  rw [← hslot] at htvote
  obtain ⟨a, hai, ell₀, D, A, ha, hD, hAeq, ho, ⟨B, hB, hBr, hBA⟩, hcase⟩ :=
    AC.lock_write_witness hr hrun.vstart hy hl
  have hPhiU := (AC.frameIn_of_callAt hr hy hc.1).2
  have hPhi₀ := AC.frameIn_of_callAt hr hy ha
  obtain rfl : B = L := hr.coherent.1 hB (hPhiU hL) (hBr.trans hLr.symm)
  have htime : sp.ts s₀ ≤ tr.time a ∧ tr.time a < AC.freeze sp e.msg.slot := by
    rcases ho with ⟨CV, ell', B, hp, hs, hsel, -⟩ | ⟨ell', hu⟩
    · have hlo := (AC.ts_le_iff_le_slot sp (hr.time_nonneg a) (s₀ : Int)).mpr
        (by rw [hs]; exact_mod_cast hlabel)
      have hlt : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
        unfold AC.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel with hn
        exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (Or.inl (hs ▸ ht)))))
      have hts := (AC.ts_le_iff sp).mpr (show (l.slot : Int) ≤ (e.msg.slot : Int) - 1 by omega)
      refine ⟨hlo, ?_⟩
      unfold AC.freeze
      exact hlt.trans_le
        (add_le_add hts (mul_le_mul_of_nonneg_right (by norm_num) sp.toParams.hΔ.le))
    · have ht := hu.2.2.1
      change tr.time a = _ at ht
      have hts₀ := (AC.ts_le_iff sp).mpr (show (s₀ : Int) ≤ l.slot by exact_mod_cast hlabel)
      have hlabel' : l.slot + 2 ≤ e.msg.slot :=
        Compose.ts_add_two_le ((ht.symm.trans_le (hrun.time_mono hai.le)).trans htvote)
      refine ⟨hts₀.trans ((le_add_of_nonneg_right
        (mul_nonneg (by norm_num) sp.toParams.hΔ.le)).trans_eq ht.symm), ?_⟩
      have hts := (AC.ts_le_iff sp).mpr
        (show (l.slot : Int) + 1 ≤ (e.msg.slot : Int) - 1 by omega)
      unfold AC.freeze
      simp only [ACParams.ts] at ht hts ⊢
      linarith [sp.toParams.hΔ]
  rcases hcase with hbelow | ⟨Q, hQ, hv, hAQ⟩
  · exfalso
    apply hstrict
    have hroot := Healing.fcRoot_mono hrun hy hai.le
    rw [← Compose.frame_of_projAC hrun hy ha,
      ← Compose.frame_of_projAC hrun hy hc.1] at hroot
    exact hBA.trans ((hbelow.mono hPhi₀.2).trans hroot)
  · obtain ⟨hQt, -, hvQ⟩ :=
      hframe.viableHead_persists' hrun hnc hf hy hai.le htime.1 hihi ha hv
    rw [← Compose.frame_of_projAC hrun hy hc.1] at hQt hvQ
    refine ⟨a, hai, ell₀, D, Q, ha, htime.1, htime.2, ho, hv,
      hBA.trans (hAQ.mono hPhi₀.2), hvQ, hQt, Or.inl ?_⟩
    apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQ hQt htime.2
    intro r _ hrs
    exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf

/-- A live old read-point lock inherits the frozen viable witness of its stored origin. -/
private theorem live_old_lock_witness {s₀ M : Nat} {hi : Time}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr (fun _ => H) (sp.ts s₀) hi M isTop J)
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : Healing.NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hwarm : s₀ + sp.k ≤ e.msg.slot) (hpos : 0 < e.msg.slot)
    (hgf : gbar g < AC.freeze sp e.msg.slot)
    {l : AC.Lock} (hl : l ∈ AC.liveLocks sp e.readPoint.locks ell.frame (tr.time i))
    (hold : l.slot < e.msg.slot)
    {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc L Q := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hs := (AC.castAt_specU hr.toU hy hc).2.1
  change e.msg.slot = sp.slot (tr.time i) at hs
  obtain ⟨l₀, hl₀, B, hB, hBr, hlive, heq⟩ := hl
  have hrecent : sp.slot (tr.time i) ≤ l₀.slot + sp.k :=
    hlive.trans ((AC.castAt_readPoint_locksWF hr hrun.vstart hy hc).cap hl₀)
  have hsl : l.slot = l₀.slot := by simpa only using congrArg AC.Lock.slot heq
  have hne : l₀.slot ≠ sp.slot (tr.time i) := by rw [← hs]; omega
  obtain ⟨l₁, hl₁, hs₁, C, hC, hCr, B', hB', hB'r, hBC⟩ :=
    AC.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time i); rwa [← hs]) l₀ hl₀ hne
  have hPhi := AC.frameIn_of_callAt hr hy hc.1
  have hBB : B' = B := hPhi.1.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [hBB] at hBC
  have hLB : ell.frame.Anc L B := by
    have he : L = ell.frame.viableAncestor B := hPhi.1.coherent.1 hL
      (AC.viableAncestor_anc hPhi.1 hB).1 (hLr.trans (congrArg AC.Lock.block heq))
    rw [he]; exact (AC.viableAncestor_anc hPhi.1 hB).2
  have hlabel : s₀ ≤ l₁.slot := by rw [← hs₁, ← hsl]; rw [← hs] at hrecent; omega
  have hstrictC : ¬ Anc (tr.HonestBlocks H) C ell.frame.fcRoot := by
    intro h
    exact hstrict ((Anc.mono hPhi.2 (hLB.trans hBC)).trans h)
  obtain ⟨a, hai, ell₀, D, Q, -, -, -, -, -, hCQ, hvQ, hQv⟩ :=
    old_lock_witness hframe hrun hnc hf hnr hy hc hihi hgf hl₁ hlabel
      (by rw [← hs₁, ← hsl]; exact hold) hC hCr hstrictC
  refine ⟨Q, hQv, hvQ, ?_⟩
  exact hLB.trans (hBC.trans (AC.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hC hCQ hQv.1))

private theorem vote_head_classification_core
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    (hpos : 0 < e.msg.slot)
    (hrootWitness : ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q)
    (holdWitness : ∀ l ∈ AC.liveLocks sp e.readPoint.locks ell.frame (tr.time i),
      l.slot < e.msg.slot → ∀ L ∈ ell.frame.tree, L.root = l.block →
      ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot →
      ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc L Q) :
    ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      ((Hd ∈ AC.voteDomain sp e.readPoint ell.frame e.msg.slot ∧
        Hd ∈ ell.frame.viableHeads) ∨
      (Hd = AC.getAnchor sp e.readPoint ell.frame (tr.time i) ∧
        ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
        ∃ a ≤ i, ∃ D CV, AC.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
          sp.ts e.msg.slot ≤ tr.time a ∧
          ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧
            ell.frame.Anc Hd L ∧ Anc (tr.HonestBlocks H) L D)) := by
  classical
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := AC.frameIn_of_callAt hr hy hc.1
  let A := AC.getAnchor sp e.readPoint ell.frame (tr.time i)
  let S := AC.voteDomain sp e.readPoint ell.frame e.msg.slot
  let Hd := AC.getHead sp e.readPoint ell.frame (tr.time i) (ell.frame.viableTree S)
    (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)
  obtain ⟨hAt, hanc⟩ := AC.anc_getAnchor hPhi.1
    (AC.castAt_liveLockBlocks_chain hr hrun.vstart hy hc _)
  have hroot := hanc _ (Or.inr rfl)
  have hwalk := AC.getHead_viable_dichotomy hPhi.1 (fun _ h => AC.voteDomain_subset_tree h)
    (AC.voteDomain_ancU hr.toU hrun.vstart hy hc) e.readPoint (tr.time i)
    (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) hAt hroot
  refine ⟨Hd, AC.getHead_mem hPhi.1 (fun _ h => AC.voteDomain_subset_tree h.1) _ _ _ _,
    (AC.castAt_specU hr.toU hy hc).2.2.2.symm, ?_⟩
  by_cases hd : ∃ Q ∈ S, Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc A Q
  · exact Or.inl (hwalk.1 hd)
  have hHd : Hd = A := hwalk.2 hd
  apply Or.inr
  by_cases heq : A = ell.frame.fcRoot
  · exfalso
    obtain ⟨Q, hQ, hv, hrQ⟩ := hrootWitness
    exact hd ⟨Q, AC.voterBlockTree_subset_voteDomain hQ, hv, heq ▸ hrQ⟩
  have hAm : A ∈ AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) := by
    unfold A
    rw [AC.getAnchor_eq_deepest_union hPhi.1]
    cases hh : AC.deepest ell.frame
        (AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) ∪ {ell.frame.fcRoot}) with
    | none => exact (heq (by
        unfold A
        rw [AC.getAnchor_eq_deepest_union hPhi.1, hh]
        rfl)).elim
    | some B =>
      rcases (AC.deepest_mem hh).1 with h | h
      · exact h
      · exact (heq (by
          unfold A
          rw [AC.getAnchor_eq_deepest_union hPhi.1, hh]
          exact h)).elim
  obtain ⟨hA, l, hl, hlr⟩ := hAm
  have hstrict : ¬ Anc (tr.HonestBlocks H) A ell.frame.fcRoot := by
    intro h
    apply heq
    exact Anc.antisymm hr.coherent h (hroot.mono hPhi.2)
  by_cases hold : l.slot < e.msg.slot
  · exfalso
    obtain ⟨Q, hQ, hv, hAQ⟩ := holdWitness l hl hold A hA hlr.symm hstrict
    exact hd ⟨Q, AC.voterBlockTree_subset_voteDomain hQ, hv, hAQ⟩
  obtain ⟨l₀, hl₀, B, hB, hBr, -, hleq⟩ := hl
  have hsl : l.slot = l₀.slot := by simpa only using congrArg AC.Lock.slot hleq
  obtain ⟨hs, c, hci, D, CV, ho, ht, L, hL, hLr, hLD⟩ :=
    AC.current_lock_write_readPoint hr hrun.vstart hy hc hpos hl₀ (by omega)
  have hBL : B = L := hr.coherent.1 (hPhi.2 hB) hL (hBr.trans hLr.symm)
  refine ⟨hHd, l₀, hl₀, hs, c, hci, D, CV, ho, ht, L, hL, hLr, ?_, hLD⟩
  have hAB : A = ell.frame.viableAncestor B := hPhi.1.coherent.1 hA
    (AC.viableAncestor_anc hPhi.1 hB).1 (hlr.symm.trans (congrArg AC.Lock.block hleq))
  rw [hHd, hAB, ← hBL]
  exact (AC.viableAncestor_anc hPhi.1 hB).2

private theorem prior_vote_call_before_freeze {K : AC.CommitteeDict sp.n} {b : Time}
    (hS : AC.HealthyBaseUpTo K tr.projAC H (tr.HonestBlocks H) proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hpos : 0 < e.msg.slot)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((e.msg.slot - 1 : Nat) : Int))
    (hmb : sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ ≤ b)
    {s₀ : Nat} (hs₀ : s₀ ≤ e.msg.slot - 1) :
    ∃ a ≤ i, ∃ ell₀, tr.projAC.CallAt y a ell₀ ∧
      sp.ts s₀ ≤ tr.time a ∧ tr.time a < AC.freeze sp e.msg.slot := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  have hcast : ((e.msg.slot - 1 : Nat) : Int) = (e.msg.slot : Int) - 1 := by omega
  obtain ⟨a, ell₀, ha, -, ht⟩ := hS.driven.tick y hy
    (sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ) (by linarith)
    ⟨4 * ((e.msg.slot - 1 : Nat) : Int) + 1, by simp only [AC.ACParams.ts]; ring⟩
    (hS.awake y hy _ (by linarith) hmb)
  change tr.time a = _ at ht
  have hislot := (AC.castAt_specU hr.toU hy hc).2.1
  have hti := (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) (e.msg.slot : Int)).mpr
    (by rw [hislot])
  change sp.ts (e.msg.slot : Int) ≤ tr.time i at hti
  have hlt : tr.time a < tr.time i := by
    simp only [AC.ACParams.ts] at ht hti
    rw [hcast] at ht
    linarith
  refine ⟨a, (le_of_not_gt fun h => hlt.not_ge (hr.time_mono h.le)), ell₀, ha, ?_, ?_⟩
  · rw [ht]
    have := (AC.ts_le_iff sp).mpr (show (s₀ : Int) ≤ ((e.msg.slot - 1 : Nat) : Int) by
      exact_mod_cast hs₀)
    linarith
  · unfold AC.freeze
    rw [ht, hcast]
    linarith

end Static

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {hold : Time}

theorem vote_head_classification_of_service_at {s₀ M : Nat} {hi : Time}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) hi M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
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
  have hd := hrun.time_nonneg i
  have hS := hK.healthy_base_before_at' hrun hnc hsvc hawake hf hcatch hd hib
  have hr := hrun.upTo hd
  have hframe' : Generic.FrameWindow (tr.upTo (tr.time i)) (fun _ => H (tr.time i))
      (sp.ts s₀) (tr.time i) M isTop J := by
    refine ⟨?_, ?_, ?_⟩
    · intro z j hz hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.M_eq z j (hrun.antitone hhi hz) hlo (hhi.trans hihi)
    · intro z j hz hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.top_iff z j (hrun.antitone hhi hz) hlo (hhi.trans hihi)
    · intro z j hz hlo hhi hk
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.root_eq z j (hrun.antitone hhi hz) hlo (hhi.trans hihi) hk
  have hc' : AC.CastAt (tr.upTo (tr.time i)).projAC y i ell e := by
    rw [RunTrace.upTo_projAC]
    exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hS' : AC.HealthyBaseUpTo K (tr.upTo (tr.time i)).projAC
      (H (tr.time i)) ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
      proposer g (tr.time i) := by
    rwa [RunTrace.upTo_projAC]
  have hmargin : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hbound := hf _ hd hib
    have hn : 0 < sp.n := sp.toParams.hn
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hAC := hS'.run
  have hslot := (AC.castAt_specU hAC.localRun.toU hy hc').2.1
  change e.msg.slot = sp.slot (tr.time i) at hslot
  have hprev : sp.ts ((e.msg.slot - 1 : Nat) : Int) + sp.Δ ≤ tr.time i := by
    have hti := (AC.ts_le_iff_le_slot sp hd (e.msg.slot : Int)).mpr (by rw [hslot])
    have hpred : ((e.msg.slot - 1 : Nat) : Int) = (e.msg.slot : Int) - 1 := by omega
    rw [hpred, AC.ts_sub_one]
    linarith only [hti, sp.toParams.hΔ]
  obtain ⟨a, hai, ell₀, ha, halo, hat⟩ :=
    prior_vote_call_before_freeze hS' hy hc' hpos hm hprev hs₀
  have hnr' : Healing.NoRestartAfter (tr.upTo (tr.time i)) (H (tr.time i)) (gbar g) := by
    intro z hz j hj
    obtain ⟨hjt, hj⟩ := (RunTrace.upTo_restartAt tr).mp hj
    exact hnr z j (hrun.antitone hjt hz) hj
  obtain ⟨Hd, hHd, hHDr, hv | ⟨hA, l, hl, hs, c, hci, D, CV, ho, ht,
      L, hL, hLr, hHL, hLD⟩⟩ :=
    vote_head_classification_core hr (hnc.upTo _) hy hc' hpos
      (hframe'.root_witness_of_earlier_call' hr (hnc.upTo _) hmargin hnr'
        hy hai ha hc' halo le_rfl hat hgf)
      (fun l hl hold L hL hLr hstrict => live_old_lock_witness hframe' hr
        (hnc.upTo _) hmargin hnr' hy hc' le_rfl hwarm hpos hgf hl hold hL hLr hstrict)
  · exact ⟨Hd, hHd, hHDr, Or.inl hv⟩
  obtain ⟨htop, hcount, -⟩ := AC.optimisticLockAt_spec hAC hy ho K
    (fun σ v hv => hS'.hP.1 y hy _ σ v hv)
  have hPhi := AC.frameIn_of_callAt hAC.localRun hy hc'.1
  have hD : D ∈ ell.frame.tree := by
    obtain ⟨ellw, Aw, hp, hslots, hsel, -⟩ := ho
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have hDw := (AC.deepest_mem hsel).1.1
    rw [Compose.frame_of_projAC hr hy hp.1,
      Node.frame_eq, Store.toFrame_tree] at hDw
    have hDi := Compose.tree_mono hr.toLocalRun hy hci hDw.1
    have hHD := (hHL.mono hPhi.2).trans hLD
    have hHdi := hHd
    rw [Compose.frame_of_projAC hr hy hc'.1,
      Node.frame_eq, Store.toFrame_tree] at hHdi
    have hFD : Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        ((tr.upTo (tr.time i)).state y i).fg.F D :=
      (Anc.mono (show ((tr.upTo (tr.time i)).state y i).fg.tree ⊆
        (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) from
        fun B hB => ⟨y, hy, i, hB⟩) hHdi.2).trans hHD
    rw [Compose.frame_of_projAC hr hy hc'.1,
      Node.frame_eq, Store.toFrame_tree]
    exact ⟨hDi, Compose.honest_held_anc hr (hnc.upTo _) hy hFD hDi⟩
  have hLt : L ∈ ell.frame.tree := by
    by_cases he : Hd = L
    · exact he ▸ hHd
    · exact (Anc.mem hHL he).2
  have hanc := hHL.trans (AC.anc_tree_of_anc_U hAC.localRun.coherent
    hPhi.1 hPhi.2 hLt hLD hD)
  rw [RunTrace.upTo_projAC] at ho
  obtain ⟨hct, ho⟩ := (AC.upTo_optimisticLockAt hrun.time_mono).mp ho
  exact ⟨Hd, hHd, hHDr, Or.inr ⟨hA, l, hl, hs, c, hci, D, CV,
    hrun.antitone hct hy, ho, ht, htop, hcount, hanc⟩⟩

end Consensus.Goldilocks.Healing.PU

end
