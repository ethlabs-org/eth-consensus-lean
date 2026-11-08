module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Viable
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.LockChain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the joint invariant over AC traces: the protection and the counts

The lemmas of `Obligations/OutageLockSafety/{Count,Prot,Induction}` that one cut of the joint
induction reads, over an AC trace with the unlock given by `u` at the write mode `wm`, under
trivial frames. The oracle is read only through the keep `FloorKeepAC` and the unlock relation
(the given locks move back from the unlock input, so they are on frame blocks).

* package facts: `P` is above the shared genesis `Φ.F` of the honest frames
  (`OutagePremisesAC.F_ancAC`); a stored lock above `P` is on a block of the call's frame, with
  `P` (`lock_mem_treeAC`, from the lock invariant); every frame block is its own viable ancestor
  (`trivial_viableAncestorAC`); the frames of a node grow (`trivial_tree_monoAC`);
* OL-W (`voteExtends_of_not_lateWakerAC`, `voteCompat_of_not_lateWakerAC`): an honest vote of a
  slot `≥ j₀ − 1` (extension, up to `j₀ + k`) or `≥ j₀` (compatibility) at a cut before `i` by a
  validator outside `W` is compatible with `P`;
* (R) at cut `i` (`result_compatibleAC`): R-pre from the frontier, R-j₀ from the deadline-cut
  service before `b₀` and the fault bound, R-mid from the cohort, R-late from S5V and the fault
  bound; the participants vote by the tick duty (`vote_of_awake_joinedAC`);
* `prot_stepAC`: the protection carries over one cut within its life, by the keep at the cut's
  call and `floor_stepWithM`;
* `vote_extends_of_protAC`: a cohort cast under the protection extends `P`: the read point's locks
  are `u k`, which hold the kept floor, and (i) at the read point
  (`readPoint_liveLockBlocks_compatible_atAC`) puts the anchor above `P`;
* the bases (`prot_of_prevBaseAC`, `prot_of_coverBaseAC`), the cover inputs (VA) and (N)
  (`cover_baseAC`) and (H) for a cohort cast after `b₀` (`cohort_vote_extendsAC`). -/

namespace Consensus.Goldilocks.Comparison

open SA
open Compose (VoteCompat voteCompat_iff)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-! ### Package facts -/

/-- An origin is a block of the frame of an honest call. -/
theorem origin_frameAC {C : Blk sp.n FGP} {s : Nat} {b : Time}
    (h : OriginWithinAC tr H C s b) :
    ∃ y ∈ H, ∃ k ℓ, tr.CallAt y k ℓ ∧ C ∈ ℓ.frame.tree := by
  obtain ⟨y, hy, k, CV, -, hR | hO⟩ := originWithinAC_iff.1 h
  · obtain ⟨ℓ, hu, hC, -⟩ := hR
    exact ⟨y, hy, k, ℓ, hu.1, (deepest_mem hC).1.1⟩
  · obtain ⟨ℓ, A, hpt, -, hsel, -⟩ := hO
    refine ⟨y, hy, k, ℓ, hpt.1, ?_⟩
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (deepest_mem hsel).1.1

namespace OutagePremisesAC

variable (D : OutagePremisesAC wm u proposer tr H U)
include D

theorem coherent : Coherent U := D.hrun.localRun.coherent

/-- **N6**: `2·|Hᶜ ∪ W| < n`. -/
theorem two_mul_lt : 2 * (Hᶜ ∪ D.W).ncard < sp.n := two_mul_ltAC D.hA₀ D.hW.2 D.hcohort

/-- `P` is above the finalized tip of every honest call's frame (genesis, under trivial
frames). -/
theorem F_ancAC {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y k ℓ) : Anc U ℓ.frame.F D.P := by
  have hr := D.hrun.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  rcases D.hP.2 with hg | hO
  · rw [hr.coherent.1 (hΦU hΦ.rooted.1) D.hP.1 ((D.htriv y hy k ℓ hc).1.trans hg.symm)]
    exact Relation.ReflTransGen.refl
  · obtain ⟨z, hz, k', ℓ', hc', hP'⟩ := origin_frameAC hO
    obtain ⟨hΦ', hΦU'⟩ := frameIn_of_callAtU hr hz hc'
    rw [trivial_F_eqAC hr D.htriv hy hz hc hc']
    exact (hΦ'.rooted.2 _ hP').mono hΦU'

/-- A genesis `P` is below every block of an honest call's frame. -/
theorem genesis_ancAC (hg : D.P.root = sp.genesisRoot) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y k ℓ) {C : Blk sp.n FGP}
    (hC : C ∈ ℓ.frame.tree) : Anc U D.P C := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU D.hrun.localRun hy hc
  rw [← D.coherent.1 (hΦU hΦ.rooted.1) D.hP.1 ((D.htriv y hy k ℓ hc).1.trans hg.symm)]
  exact (hΦ.rooted.2 C hC).mono hΦU

/-- A genesis `P` is extended by every honest vote. -/
theorem vote_extends_of_genesisAC (hg : D.P.root = sp.genesisRoot) {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e : Em sp FGP} (hv : VoteAt tr x k e) : VoteExtends U e.msg D.P := by
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frameU D.hrun.localRun hx ⟨hc, he⟩
  exact ⟨Hd, (frameIn_of_callAtU D.hrun.localRun hx hc).2 hHd, hHdr,
    D.genesis_ancAC hg hx hc hHd⟩

/-- **An origin within `b₀` is compatible with `P`.** -/
theorem compatible_of_withinAC {C : Blk sp.n FGP} {s : Nat}
    (hC : OriginWithinAC tr H C s D.b₀) : Compatible U C D.P := by
  rcases D.hP.2 with hg | hP
  · obtain ⟨y, hy, k, ℓ, hc, hCt⟩ := origin_frameAC hC
    exact Or.inr (D.genesis_ancAC hg hy hc hCt)
  · exact D.hpre.origins_compatible C s D.P D.σ hC hP

/-- **An honest vote at a time `≤ b₀` of a slot after `σ` extends `P`.** -/
theorem vote_extends_preAC {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x k e) (hk : tr.time k ≤ D.b₀) (hs : D.σ < e.msg.slot) :
    VoteExtends U e.msg D.P := by
  rcases D.hP.2 with hg | hP
  · exact D.vote_extends_of_genesisAC hg hx hv
  · exact D.hpre.vote_extends D.P D.σ hP x hx k e hv hk hs

/-- Under trivial frames every block of an honest call's frame is viable. -/
theorem trivial_viableAncestorAC {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y k ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) :
    B ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ ℓ.frame.viableAncestor B = B := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU D.hrun.localRun hy hc
  obtain ⟨-, hfc, hvh, -⟩ := D.htriv y hy k ℓ hc
  have hv : B ∈ ℓ.frame.viableTree ℓ.frame.tree := by
    refine ⟨hB, ?_, B, hB, ?_, Relation.ReflTransGen.refl⟩
    · rw [hfc]; exact hΦ.rooted.2 B hB
    · rw [hvh]; exact hB
  exact ⟨hv, viableAncestor_self hΦ hB (Or.inl hv)⟩

/-- Under trivial frames the frames of a node's calls grow. -/
theorem trivial_tree_monoAC {y : Fin sp.n} (hy : y ∈ H) {c c' : Nat}
    {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y c ℓ) (hc' : tr.CallAt y c' ℓ')
    (hcc : c ≤ c') : ℓ.frame.tree ⊆ ℓ'.frame.tree := by
  obtain ⟨-, -, -, ht⟩ := D.htriv y hy c ℓ hc
  obtain ⟨-, -, -, ht'⟩ := D.htriv y hy c' ℓ' hc'
  rw [ht, ht', trivial_F_eqAC D.hrun.localRun D.htriv hy hy hc hc']
  exact Set.insert_subset_insert fun B ⟨k, hk, hB⟩ => ⟨k, hk.trans hcc, hB⟩

/-- **A stored lock above `P` is on a block of the call's frame**, and so is `P`: the record
names a block of `U` above the lock's block (the lock invariant), in the frame once it is above
`Φ.F`, which `P` is. -/
theorem lock_mem_treeAC {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y k ℓ) {l : Lock}
    (hl : l ∈ (tr.state y k).locks) {Z : Blk sp.n FGP} (hZ : Z ∈ U) (hZr : Z.root = l.block)
    (hPZ : Anc U D.P Z) : Z ∈ ℓ.frame.tree ∧ D.P ∈ ℓ.frame.tree := by
  have hU := D.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU D.hrun.localRun hy hc
  obtain ⟨E, -, -, hEt, hlE⟩ := lockInv_iff.1 (lockInv_stateAC D.hrun.localRun hy hc)
  have hFP := D.F_ancAC hy hc
  have hZE := hlE l hl Z hZ hZr
  have hZt := frame_mem_of_between sp hU hΦ hΦU (hEt ((hFP.trans hPZ).trans hZE)) hZE
    (hFP.trans hPZ)
  exact ⟨hZt, frame_mem_of_between sp hU hΦ hΦU hZt hPZ hFP⟩

/-- The floor at an honest call, in the call's frame. -/
theorem floor_frameAC {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x k ℓ) {j m : Nat}
    (hfl : FloorAtAC tr U x k D.P j m) :
    D.P ∈ ℓ.frame.tree ∧ ∃ l ∈ (tr.state x k).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc D.P B := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU D.hrun.localRun hx hc
  obtain ⟨l, hl, hlj, hle, Z, hZ, hZr, hPZ⟩ := floorAtAC_iff.1 hfl
  obtain ⟨hZt, hPt⟩ := D.lock_mem_treeAC hx hc hl hZ hZr hPZ
  exact ⟨hPt, l, hl, hlj, hle, Z, hZt, hZr, anc_tree_of_anc_U D.coherent hΦ hΦU hPt hPZ hZt⟩

/-- The kept floor of the given locks at an honest call, in the call's frame: the given locks
move back from the call's unlock input (the unlock relation), so they are on frame blocks. -/
theorem oracle_floor_frameAC {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x k ℓ) {j m : Nat}
    (hP : D.P ∈ ℓ.frame.tree)
    (h : ∃ l ∈ u k, l.slot = j ∧ m ≤ l.expiry ∧ ∃ Z ∈ U, Z.root = l.block ∧ Anc U D.P Z) :
    ∃ l ∈ u k, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc D.P B := by
  have hr := D.hrun.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  obtain ⟨l, hl, hlj, hle, Z, hZ, hZr, hPZ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, B', hB', hB'r, -⟩ := (hr.lawfulAt hx hc hΦ).movesBack hΦ l hl
  obtain rfl : Z = B' := D.coherent.1 hZ (hΦU hB') (hZr.trans hB'r.symm)
  exact ⟨l, hl, hlj, hle, Z, hB', hZr, anc_tree_of_anc_U D.coherent hΦ hΦU hP hPZ hB'⟩

end OutagePremisesAC

variable {D : OutagePremisesAC wm u proposer tr H U}

/-! ### Slot arithmetic of updates -/

theorem ts_succAC (s : Nat) : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
  simp only [SAParams.ts]; push_cast; ring

/-- An update of label `s` is at `t_{s+1} + 2Δ`. -/
theorem update_timeAC {x : Fin sp.n} {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hu : UpdateAt tr x c s ℓ) : tr.time c = sp.ts (s + 1 : Nat) + 2 * sp.Δ := by
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  rw [ts_succAC]
  linarith

/-- Every cut from an update of label `s` on is of a slot after `s`. -/
theorem slot_after_updateAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} {c s k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x c s ℓ) (hck : c ≤ k) :
    s + 1 ≤ sp.slot (tr.time k) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht := update_timeAC hu
  have := (ts_le_iff_le_slot sp (hr.time_nonneg k) ((s + 1 : Nat) : Int)).1
    (by linarith [hr.time_mono hck])
  omega

/-! ### OL-W -/

namespace OutageVoteInvAC

/-- **OL-W, extension**: at a cut before `i`, an honest vote of a slot in `[j₀ − 1, j₀ + k]`
whose voter is not a late waker extends `P`: a vote of slot `j₀ − 1` is cast within `b₀`, and a
later one after `b₀` would put its voter, awake in the no-sleep window, outside `A₀ ∪ W`. -/
theorem voteExtends_of_not_lateWakerAC {i : Nat} (hvi : OutageVoteInvAC D i) {x : Fin sp.n}
    (hx : x ∈ H) (hxW : x ∉ D.W) {k : Nat} (hk : k < i) {e : Em sp FGP}
    (hv : VoteAt tr x k e) (hs : D.j₀ ≤ e.msg.slot + 1) (hsK : e.msg.slot ≤ D.j₀ + sp.k) :
    VoteExtends U e.msg D.P := by
  have hσ := D.hσ
  have hK := sp.two_le_k
  by_cases hpre : tr.time k ≤ D.b₀ ∨ x ∈ D.A₀
  · exact hvi.votes x hx k hk e hv (by omega) hsK hpre
  exfalso
  push Not at hpre
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hts, hte⟩ := ts_le_castAC D.hrun.localRun hx hv
  rcases Nat.lt_or_ge e.msg.slot D.j₀ with hlt | hge
  · have h1 := ts_le_tsAC (sp := sp) (show e.msg.slot + 1 ≤ D.j₀ by omega)
    rw [ts_succAC] at h1
    linarith [D.hj₀.1, hpre.1]
  · obtain ⟨ℓ, hc, -⟩ := hv
    have hjs : sp.ts D.j₀ ≤ sp.ts e.msg.slot := ts_le_tsAC hge
    have hsK' : sp.ts e.msg.slot ≤ sp.ts (D.j₀ + sp.k : Nat) := ts_le_tsAC hsK
    have hz := D.hz (tr.time k) (by linarith) ⟨x, hx, k, ℓ, hc, le_rfl⟩
    have haw := D.hrun.localRun.awake_of_call x hx k ℓ hc
    rcases D.hawake x hx (tr.time k) (by linarith [D.ha]) hz haw with h | h
    · exact hpre.2 h
    · exact hxW h

/-- **OL-W**: at a cut before `i`, an honest vote of a slot `≥ j₀` whose voter is not a late
waker has a head compatible with `P`. -/
theorem voteCompat_of_not_lateWakerAC {i : Nat} (hvi : OutageVoteInvAC D i) {x : Fin sp.n}
    (hx : x ∈ H) (hxW : x ∉ D.W) {k : Nat} (hk : k < i) {e : Em sp FGP}
    (hv : VoteAt tr x k e) (hs : D.j₀ ≤ e.msg.slot) : VoteCompat U e.msg D.P := by
  by_cases hlate : D.j₀ + sp.k < e.msg.slot
  · exact hvi.late x hx k hk e hv hlate
  · exact (hvi.voteExtends_of_not_lateWakerAC hx hxW hk hv (by omega) (by omega)).voteCompat

/-! ### (R) -/

/-- The awake joined validators participate in an honest update of slot `s` when the votes'
deadline `t_s + 2Δ` is within the service before `b` (the update itself may be after `b`). -/
private theorem awake_participant_earlyAC (hr : ACLocalRunU wm u H U tr)
    (htick : TickDuty tr H) {b : Time} (hsv : ServiceWindowBefore H U 0 b tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hu : UpdateAt tr X i₀ s ℓX) (hb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : JoinedAt tr y (sp.ts s + sp.Δ)) :
    y ∈ voters {v | v ∈ (tr.state X i₀).pool s} := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joinedAC hr htick hy hw hj
  obtain ⟨hval, hsl', -, -⟩ := castAt_specU hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.time k :=
    (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have := sync_window_before_forwardU hr hsv hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (hr.time_nonneg k) (by linarith) hX hu.1
    (fun k' hk' hr' => (update_restartsAC hr hX hu k' hk' hr').trans hsk) (by linarith)
    fun t h₁ h₂ => by
      have : sp.slot t = s := slot_of_mem sp s (hsk.trans h₁) (by rw [ts_succ]; linarith)
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- **(R) at cut `i`**: the result of an honest update at cut `i` of an unpolluted label is
compatible with `P`. -/
theorem result_compatibleAC {i : Nat} (hinv : OutageVoteInvAC D i) {y : Fin sp.n} (hy : y ∈ H)
    {m : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr y i m C CV)
    (hm : m ≤ D.j₀ ∨ D.r ≤ m) : Compatible U C D.P := by
  have hr := D.hrun.localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓ, hu, -, -⟩ := id hR
  have ht : tr.time i = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hcall : ∃ x ∈ H, ∃ i' ℓ', tr.CallAt x i' ℓ' ∧ sp.ts m + sp.Δ ≤ tr.time i' :=
    ⟨y, hy, i, ℓ, hu.1, by linarith⟩
  have hj₀ := D.hj₀
  have hrk := D.hrk
  have hσ := D.hσ
  -- a counted honest vote compatible with `P` makes `C` compatible with `P`
  have finish : ∀ v ∈ CV, v.val ∈ H →
      (∀ j < i, ∀ e, VoteAt tr v.val j e → e.msg = v → e.msg.slot = m →
        VoteCompat U e.msg D.P) → Compatible U C D.P := by
    intro v hv hvH hcompat
    obtain ⟨j, hj, e, hve, rfl, hvs, R, hRU, hRr, hCR⟩ := counted_honest_voteAC D.hrun hy hR hv hvH
    exact compatible_of_voteCompatAC hU hRU hRr hCR (hcompat j hj e hve rfl hvs)
  have hvoter : ∀ x ∈ H, tr.awake x (sp.ts m + sp.Δ) → JoinedAt tr x (sp.ts m + sp.Δ) →
      D.r ≤ m → x ∈ voters {v | v ∈ (tr.state y i).pool m} := by
    intro x hx haw hjn hrm
    obtain ⟨k, e, hve, hes, -⟩ := vote_of_awake_joinedAC hr D.htick hx haw hjn
    have := D.PG y hy i m ℓ hu hrm x hx k e hve hes
    obtain ⟨ℓ', hc', he'⟩ := hve
    exact ⟨e.msg, this, (castAt_specU hr hx ⟨hc', he'⟩).1⟩
  rcases lt_or_ge m D.j₀ with hlt | hge
  · -- R-pre: the update is within `b₀`
    have hmj : sp.ts m + 6 * sp.Δ ≤ D.b₀ := by
      have := ts_le_tsAC (sp := sp) (show m + 1 ≤ D.j₀ by omega)
      rw [ts_succAC] at this
      linarith
    exact D.compatible_of_withinAC (originWithinAC_iff.2 ⟨y, hy, i, CV, ht ▸ hmj, Or.inl hR⟩)
  rcases hm with hm | hm
  · -- R-j₀: the honest slot-`j₀` voters reach the update by the early cutoff `≤ b₀`
    have hmeq : m = D.j₀ := le_antisymm hm hge
    have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ JoinedAt tr x (sp.ts m + sp.Δ)} ⊆
        voters {v | v ∈ (tr.state y i).pool m} := fun x hx =>
      awake_participant_earlyAC hr D.htick D.hpreSvc.service hy hu (hmeq ▸ hj₀.1) hx.1 hx.2.1
        hx.2.2
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participantsAC hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he hs => ?_
    obtain ⟨-, hte⟩ := ts_le_castAC hr hvH hve
    rw [hs, hmeq] at hte
    exact (hinv.votes v.val hvH j hj e hve (by omega) (by omega)
      (Or.inl (by linarith))).voteCompat
  rcases le_or_gt m (D.j₀ + sp.k) with hmK | hmK
  · -- R-mid: `A₀` votes in slot `m` and extends `P`; the counted set is in `Hᶜ ∪ W`
    have hT : D.A₀ ⊆ voters {v | v ∈ (tr.state y i).pool m} := by
      intro x hx
      obtain ⟨haw, hjn⟩ := cohort_readyAC D.hA₀awake D.hA₀join D.ha D.hz hx (by omega) hmK hcall
      exact hvoter x (D.hA₀ hx) haw hjn hm
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participantsAC hR hT D.hcohort
    have hvH : v.val ∈ H := by
      rcases hvT with h | h
      · exact D.hA₀ h
      · by_contra hn; exact h (Or.inl hn)
    refine finish v hv hvH fun j hj e hve he hs => ?_
    rcases hvT with hA | hQ
    · exact (hinv.votes v.val hvH j (by omega) e hve (by omega) (by omega)
        (Or.inr hA)).voteCompat
    · exact hinv.voteCompat_of_not_lateWakerAC hvH (fun h => hQ (Or.inr h)) (by omega) hve
        (by omega)
  · -- R-late: every honest slot-`m` vote is compatible with `P` (S5V), and reaches the update
    have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ JoinedAt tr x (sp.ts m + sp.Δ)} ⊆
        voters {v | v ∈ (tr.state y i).pool m} := fun x hx =>
      hvoter x hx.1 hx.2.1 hx.2.2 hm
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participantsAC hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    exact finish v hv hvH fun j hj e hve he hs => hinv.late v.val hvH j hj e hve (by omega)

end OutageVoteInvAC

/-! ### The protection over one cut and at a cast -/

/-- The keep's vote input at a cut `k` with `j₀ ≤ slot(t_k) ≤ j₀ + k`: the honest votes of slot
`slot(t_k) − 1` before `k` by validators outside `W` extend `P` (OL-W). -/
private theorem keep_votesAC {k : Nat} (hvi : OutageVoteInvAC D k)
    (hk : sp.slot (tr.time k) ≤ D.j₀ + sp.k) (hk' : D.j₀ ≤ sp.slot (tr.time k)) :
    ∀ y ∈ H, y ∉ D.W → ∀ k' < k, ∀ e, VoteAt tr y k' e →
      (e.msg.slot : Int) = (sp.slot (tr.time k) : Int) - 1 → VoteExtends U e.msg D.P :=
  fun _ hy hyW _ hk'' _ hv hes =>
    hvi.voteExtends_of_not_lateWakerAC hy hyW hk'' hv (by omega) (by omega)

/-- **One step of the protection**: `ProtAC x k j (j + k)` for `j ∈ {j₀ − 1, j₀}`, within the
lock's life (`slot(t_k) ≤ j + k`) and from `j₀` on, gives `ProtAC x (k + 1) j (j + k)`: the keep
puts the floor in the given locks of `x`'s call at `k`, and the call keeps it
(`floor_stepWithM`). -/
theorem prot_stepAC (hkeep : FloorKeepAC D) {k : Nat} (hvi : OutageVoteInvAC D k)
    {x : Fin sp.n} (hx : x ∈ D.A₀) {j : Nat} (hj : j = D.j₀ - 1 ∨ j = D.j₀)
    (hk : sp.slot (tr.time k) ≤ j + sp.k) (hk' : D.j₀ ≤ sp.slot (tr.time k))
    (hp : ProtAC D x k j (j + sp.k)) : ProtAC D x (k + 1) j (j + sp.k) := by
  rcases protAC_iff.1 hp with hfl | hg
  swap
  · exact protAC_iff.2 (Or.inr hg)
  refine protAC_iff.2 (Or.inl ?_)
  have hxH := D.hA₀ hx
  have hr := D.hrun.localRun
  by_cases hcall : ∃ ℓ, tr.CallAt x k ℓ
  swap
  · push Not at hcall
    rw [floorAtAC_iff, Trace.state_succ_of_not tr hcall]
    exact floorAtAC_iff.1 hfl
  obtain ⟨ℓ, hc⟩ := hcall
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hxH hc
  obtain ⟨hP, hA⟩ := D.floor_frameAC hxH hc hfl
  have hva0 := (D.trivial_viableAncestorAC hxH hc hP).2
  have hL := D.oracle_floor_frameAC hxH hc hP (floorKeepAC_iff.1 hkeep x hx k ℓ hc j hj hfl hk
    (keep_votesAC hvi (by omega) hk') D.two_mul_lt)
  have hstep := floor_stepWithM wm x ℓ.call hΦ (hr.time_nonneg k) hP hva0 hk hA hL
  have he := hr.exec k ℓ hc.2 (hc.1 ▸ hxH)
  rw [hc.1] at he
  rw [he] at hstep
  rw [floorAtAC_iff, Trace.state_succ_of_call tr hc]
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := hstep
  exact ⟨l, hl, hlj, hle, B, hΦU hB, hBr, hPB.mono hΦU⟩

/-- **A cohort cast under the protection extends `P`**: at a cast of `x ∈ A₀` at cut `k`, within
the life of `ProtAC x k j (j + k)` (`j ∈ {j₀ − 1, j₀}`) and from `j₀` on, the read point's locks
are the given locks `u k`, which hold the kept floor; every live lock block of the read point is
compatible with `P` ((i) at the read point), so the anchor and the head are above `P`. -/
theorem vote_extends_of_protAC (hkeep : FloorKeepAC D) {k : Nat} (hinv : OutageInvAC D k)
    {x : Fin sp.n} (hx : x ∈ D.A₀) {j : Nat} (hj : j = D.j₀ - 1 ∨ j = D.j₀)
    (hk : sp.slot (tr.time k) ≤ j + sp.k) (hk' : D.j₀ ≤ sp.slot (tr.time k))
    (hp : ProtAC D x k j (j + sp.k)) {e : Em sp FGP} (hv : VoteAt tr x k e) :
    VoteExtends U e.msg D.P := by
  have hxH := D.hA₀ hx
  rcases protAC_iff.1 hp with hfl | hg
  swap
  · exact D.vote_extends_of_genesisAC hg hxH hv
  have hr := D.hrun.localRun
  have hU := D.coherent
  have hσ := D.hσ
  obtain ⟨ℓ, hc, he⟩ := hv
  have hcast : CastAt tr x k ℓ e := ⟨hc, he⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hxH hc
  obtain ⟨hP, -⟩ := D.floor_frameAC hxH hc hfl
  have hva0 := (D.trivial_viableAncestorAC hxH hc hP).2
  obtain ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩ := D.oracle_floor_frameAC hxH hc hP
    (floorKeepAC_iff.1 hkeep x hx k ℓ hc j hj hfl hk
      (keep_votesAC hinv.toOutageVoteInvAC (by omega) hk') D.two_mul_lt)
  have hpos : 0 < sp.slot (tr.time k) := by omega
  have hrp : e.readPoint.locks = u k := by
    obtain ⟨Q, heQ, -⟩ := vote_tryVote_inputU hr hxH hcast
    rw [tryVote_readPoint_locks_eqWith heQ]
    simp only [hpos, ↓reduceIte]
  obtain ⟨l', hl', -, -, C, hC, hCr, hPC⟩ :=
    floor_liveLocks (t := tr.time k) hΦ hP hva0 hk ⟨l, hl, hlj, hle, B, hB, hBr, hPB⟩
  have hCl : C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time k) := by
    rw [hrp]; exact ⟨hC, l', hl', hCr.symm⟩
  have hcomp := readPoint_liveLockBlocks_compatible_atAC D.hrun D.hj₀.1
    (fun _ _ hC' _ => D.compatible_of_withinAC hC')
    (fun _ hy hyW _ hk'' _ hve hs =>
      hinv.voteCompat_of_not_lateWakerAC hy hyW hk'' hve hs)
    D.two_mul_lt hxH (hinv.locks x hxH k le_rfl) hcast hpos Relation.ReflTransGen.refl
  have hcomp' : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time k),
      Compatible ℓ.frame.tree L D.P := fun L hL =>
    (hcomp L hL).imp (fun h => anc_tree_of_anc_U hU hΦ hΦU hL.1 h hP)
      (fun h => anc_tree_of_anc_U hU hΦ hΦU hP h hL.1)
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hr hxH hcast
  have hT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot) ⊆
      ℓ.frame.tree := fun X hX => voteDomain_subset_tree hX.1
  exact ⟨_, hΦU (getHead_mem hΦ hT _ _ _ _), hhead.symm,
    (anc_getHead_of_floorAC hΦ hCl hPC hcomp' hT _ _).mono hΦU⟩

/-! ### The bases -/

/-- The label-`(j₀ − 1)` base gives the protection at the cut after the update. -/
theorem prot_of_prevBaseAC {x : Fin sp.n} (hx : x ∈ H) {c j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x c j ℓ)
    (hbase : PrevBaseAC tr D.P j x c ℓ) : ProtAC D x (c + 1) j (j + sp.k) := by
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU D.hrun.localRun hx hu.1
  obtain ⟨L, f, hL, hPL, hl⟩ := prevBaseAC_iff.1 hbase
  exact protAC_iff.2 (Or.inl (floorAtAC_iff.2 ⟨_, hl, rfl, le_rfl, L, hΦU hL, rfl,
    hPL.mono hΦU⟩))

/-- The cover base gives the label-`j₀` protection at the cut after the update. -/
theorem prot_of_coverBaseAC {x : Fin sp.n} (hx : x ∈ H) {c j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x c j ℓ)
    (hbase : CoverBaseAC tr D.P j x c ℓ) : ProtAC D x (c + 1) j (j + sp.k) := by
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU D.hrun.localRun hx hu.1
  obtain ⟨L, f, hPL, hl⟩ := coverBaseAC_iff.1 hbase
  have hLU : L ∈ U := by
    by_cases hne : D.P = L
    · exact hne ▸ D.hP.1
    · exact hΦU (hPL.mem hne).2
  exact protAC_iff.2 (Or.inl (floorAtAC_iff.2 ⟨_, hl, rfl, le_rfl, L, hLU, rfl,
    hPL.mono hΦU⟩))

namespace OutageInvAC

/-- **The cover inputs (VA) and (N) at the label-`j₀` update**: from the invariant at a cut
`≥ c`, the cover base holds at `x`'s label-`j₀` update at cut `c`. (VA): `P` is in the update's
frame, put there by the label-`(j₀ − 1)` base (the frames of `x` grow), and every frame block is
viable; (N): the cohort's slot-`(j₀ + 1)` votes before `c` extend `P` (within `b₀` by the
frontier, after it by (H)). -/
theorem cover_baseAC {i : Nat} (hinv : OutageInvAC D i) {x : Fin sp.n} (hx : x ∈ D.A₀)
    {c : Nat} (hci : c ≤ i) {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hu : UpdateAt tr x c D.j₀ ℓ)
    (hcond : ℓ.frame.AncestorCandidate D.P →
      (∀ y ∈ D.A₀, ∀ j e, VoteAt tr y j e → e.msg.slot = D.j₀ + 1 → j < c →
        VoteExtends U e.msg D.P) →
      CoverBaseAC tr D.P D.j₀ x c ℓ) :
    CoverBaseAC tr D.P D.j₀ x c ℓ := by
  have hxH := D.hA₀ hx
  have hr := D.hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hK := sp.two_le_k
  have hσ := D.hσ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hxH hu.1
  have hPt : D.P ∈ ℓ.frame.tree := by
    by_cases hg : D.P.root = sp.genesisRoot
    · rw [D.coherent.1 D.hP.1 (hΦU hΦ.rooted.1) (hg.trans (D.htriv x hxH c ℓ hu.1).1.symm)]
      exact hΦ.rooted.1
    have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
    obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg ⟨x, hxH, c, ℓ, hu.1, by linarith⟩
    have ht₁ := update_timeAC hu₁
    rw [Nat.sub_add_cancel (by omega)] at ht₁
    have hc₁ : c₁ ≤ c := by
      by_contra h
      have := hr.time_mono (show c ≤ c₁ by omega)
      linarith
    obtain ⟨L, f, hL, hPL, -⟩ := prevBaseAC_iff.1 hbase
    exact D.trivial_tree_monoAC hxH hu₁.1 hu.1 hc₁ (mem_of_anc hPL hL)
  refine hcond (Or.inr (D.trivial_viableAncestorAC hxH hu.1 hPt).1) fun y hy j e hv hs hjc => ?_
  by_cases hj : tr.time j ≤ D.b₀
  · exact D.vote_extends_preAC (D.hA₀ hy) hv hj (by omega)
  · exact hinv.votes y (D.hA₀ hy) j (by omega) e hv (by omega) (by omega) (Or.inr hy)

/-- **(H) for a cast of `A₀` after `b₀`**: through the label-`(j₀ − 1)` protection for slots
`≤ j₀ − 1 + k`, and through the cover protection for slot `j₀ + k`. -/
theorem cohort_vote_extendsAC (hkeep : FloorKeepAC D) {i : Nat} (hinv : OutageInvAC D i)
    {x : Fin sp.n} (hx : x ∈ D.A₀) {e : Em sp FGP} (hv : VoteAt tr x i e)
    (hsK : e.msg.slot ≤ D.j₀ + sp.k) (hb : D.b₀ < tr.time i) :
    VoteExtends U e.msg D.P := by
  have hxH := D.hA₀ hx
  have hr := D.hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hK := sp.two_le_k
  have hσ := D.hσ
  obtain ⟨hts, hte⟩ := ts_le_castAC hr hxH hv
  have hsl : e.msg.slot = sp.slot (tr.time i) := by
    obtain ⟨ℓ, hc, he⟩ := hv
    exact (castAt_specU hr hxH ⟨hc, he⟩).2.1
  have hslot_prev : sp.slot (tr.time (i - 1)) ≤ e.msg.slot := by
    rw [hsl]
    exact slot_mono sp (hr.time_nonneg _) (hr.time_mono (Nat.sub_le i 1))
  -- the slot is after `j₀`
  have hs : D.j₀ + 1 ≤ e.msg.slot := by
    by_contra h
    have := ts_le_tsAC (sp := sp) (show e.msg.slot ≤ D.j₀ by omega)
    linarith [D.hj₀.1]
  by_cases hg : D.P.root = sp.genesisRoot
  · exact D.vote_extends_of_genesisAC hg hxH hv
  obtain ⟨ℓi, hci, -⟩ := id hv
  by_cases hprev : e.msg.slot ≤ D.j₀ - 1 + sp.k
  · obtain ⟨c₁, ℓ₁, hu₁, hbase⟩ := D.lockPrev x hx hg
      ⟨x, hxH, i, ℓi, hci, by linarith [D.hj₀.1]⟩
    have ht₁ := update_timeAC hu₁
    rw [Nat.sub_add_cancel (by omega)] at ht₁
    have hc₁ : c₁ < i := by
      by_contra h
      have := hr.time_mono (show i ≤ c₁ by omega)
      linarith [D.hj₀.1]
    have hp := hinv.protPrev x hx c₁ ℓ₁ hu₁ hbase i hc₁ le_rfl (by omega)
    exact vote_extends_of_protAC hkeep hinv hx (Or.inl rfl) (by omega) (by omega) hp hv
  · have h2 := ts_le_tsAC (sp := sp) (show D.j₀ + 2 ≤ e.msg.slot by omega)
    rw [ts_succ₂AC] at h2
    obtain ⟨c, ℓ, hu, -, hcond⟩ := D.lockCover x hx hg ⟨x, hxH, i, ℓi, hci, by linarith⟩
    have ht : tr.time c = sp.ts D.j₀ + 6 * sp.Δ := hu.2.2.1
    have hc : c < i := by
      by_contra h
      have := hr.time_mono (show i ≤ c by omega)
      linarith
    have hp := hinv.protCover x hx c ℓ hu (hinv.cover_baseAC hx hc.le hu hcond) i hc le_rfl
      (by omega)
    exact vote_extends_of_protAC hkeep hinv hx (Or.inr rfl) (by omega) (by omega) hp hv

end OutageInvAC

end Consensus.Goldilocks.Comparison

end
