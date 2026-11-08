module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtACEnv
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Delivery
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Viable
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the joint invariant over AC traces: the restored votes

The restored-vote step of `Obligations/OutageS5/Step` over an AC trace with the unlock given by
`u` at the write mode `wm` (`ACRunU wm u`), under trivial frames, with the service from `b₁`
(`PSyncAC tr H U b₁`) as hypothesis. At an honest vote of slot `q + 1 > r` at cut `i`, from
`OutageInvAC D i`:

* the composite splits on root cover (`P ⪯ Σ.F`), Hi (`Σ.J` strictly above `P`) and Lo. Under
  trivial frames `Φ.F = fc_root` is genesis and below `P` (`OutagePremisesAC.F_ancAC`), and there
  are no FG caches, so only the Lo walk remains, read without the split: a genesis `P` is viable
  at the vote as `fc_root`, and the walk extends it as any other `P`;
* G4 (`viable_at_vote_afterAC`): a block of `U` above `Φ.F` that an honest vote of a slot `≤ q`
  extends is viable at the vote. The composite reads the FG rows (no contest, the `h_max`
  carrier's floor entry above `P`, `rows_supported`); under trivial frames every accepted block is
  a viable head (`viable_of_acceptedAC`), and the block is accepted before the freeze `t_q + 3Δ`
  with the witness head (`honest_head_accepted_afterAC`, `frame_anc_acceptedU`);
* `outage_s5_innerAC` (INV): the batch walk, `vote_extends_of_batchAC` for `q > r` by strong
  induction on the cut, `vote_extends_of_counted_batchAC` with the cohort `A₀` for `q = r`, with
  the carry `carryAt_afterAC` and the read point's live locks compatible with `P`
  (`readPoint_liveLockBlocks_compatible_atAC` at the cast cut). It reads the invariant at `i`
  only: its fields are stated at the cuts before `i` (or at `i`), which cover every earlier cast
  cut, so the composite's `OutageLockInv.mono` is not needed;
* `outage_s5_stepAC` (the step `OutageS5StepAC`), `restored_votes_extendAC`,
  `restored_majorityAC` (`ExtendingMajorityAC` at every restored label). -/

namespace Consensus.Goldilocks.Comparison

open SA
open Compose (VoteCompat)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {g : Time}

/-! ### Viability at a restored vote -/

/-- **G4 under trivial frames**: at an honest vote of slot `q + 1`, under the service from
`g ≤ t_q + Δ`, a block `B` of `U` above the call's `Φ.F` that an honest vote of a slot `≤ q`
extends is viable at the vote (or is `fc_root`): the witness head is accepted before the freeze
`t_q + 3Δ`, and with it `B`, which is then a viable head of the trivial frame. -/
theorem viable_at_vote_afterAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    (hS : PSyncAC tr H U g) {y : Fin sp.n} (hy : y ∈ H) {q : Nat} (hg : g ≤ sp.ts q + sp.Δ)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = q + 1) {B : Blk sp.n FGP} (hBU : B ∈ U) (hFB : Anc U ℓ.frame.F B)
    (hB : ∃ x ∈ H, ∃ k e', VoteAt tr x k e' ∧ e'.msg.slot ≤ q ∧ VoteExtends U e'.msg B) :
    ViableAtVote ℓ e (q + 1) B := by
  have hU := hr.coherent
  obtain ⟨x, hx, k, e', hv, hs', Hd, hHd, hHdr, hBHd⟩ := hB
  refine viable_of_acceptedAC hr htriv hy hc hs hBU ?_
  rcases honest_head_accepted_afterAC hr hS hy hg hc hs hx hv hs' hHd hHdr (hFB.trans hBHd) with
    hgen | ⟨ky, hacc, hkyt⟩
  · -- a genesis head: `B` below it is genesis
    left
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy i ℓ hc.1
    obtain rfl : Hd = G := hU.1 hHd hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBHd with rfl | ⟨Q, -, hQ⟩
    · exact hGr
    · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
  · obtain ⟨ℓk, hck, hcall⟩ := id hacc
    rcases Compose.frame_anc_acceptedU hr hy ky ℓk hck Hd
        ((accept_newU sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) B hBHd with hgen | ⟨k', hk', hk'B⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k', hk'B, lt_of_le_of_lt (hr.time_mono hk') hkyt⟩

/-! ### Cut and caster facts -/

/-- A vote of slot `q` is cast at a cut before a cast of slot `q + 1`. -/
private theorem cut_lt_of_slotAC (hr : ACLocalRunU wm u H U tr) {x y : Fin sp.n} (hx : x ∈ H)
    (hy : y ∈ H) {k k' : Nat} {e e' : Em sp FGP} (hv : VoteAt tr y k e) (hv' : VoteAt tr x k' e')
    {q : Nat} (hs : e.msg.slot = q + 1) (hs' : e'.msg.slot = q) : k' < k := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨h1, -⟩ := ts_le_castAC hr hy hv
  obtain ⟨-, h2⟩ := ts_le_castAC hr hx hv'
  rw [hs] at h1
  rw [hs'] at h2
  have hts := ts_succAC (sp := sp) q
  by_contra hle
  have := hr.time_mono (show k ≤ k' by omega)
  linarith only [h1, h2, hts, this, hΔ]

/-- An honest slot-`r` caster is in the cohort `A₀` or a late waker. -/
private theorem caster_mem_rAC (D : OutagePremisesAC wm u proposer tr H U) {x : Fin sp.n}
    (hx : x ∈ H) {k : Nat} {e : Em sp FGP} (hv : VoteAt tr x k e) (hs : e.msg.slot = D.r) :
    x ∈ D.A₀ ∪ D.W := by
  have hr := D.hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := D.ha
  have hrk := D.hrk
  obtain ⟨hts, hte⟩ := ts_le_castAC hr hx hv
  rw [hs] at hts hte
  obtain ⟨ℓ, hc, -⟩ := id hv
  have hrK := ts_le_tsAC (sp := sp) hrk.2
  have hjr := ts_le_tsAC (sp := sp) (show D.j₀ ≤ D.r by omega)
  have hz := D.hz (tr.time k) (by linarith only [hts, hte, hrK, hjr, hΔ])
    ⟨x, hx, k, ℓ, hc, le_rfl⟩
  exact D.hawake x hx (tr.time k) (by linarith only [ha, hts, hte, hrK, hjr, hΔ]) hz
    (hr.awake_of_call x hx k ℓ hc)

/-! ### The restored votes -/

/-- **INV, the inner cut induction**: from the invariant at the cuts before `i` and the service
from `b₁`, every honest vote at a cut `≤ i` of a slot after `r` extends `P`. The Lo walk of the
composite (root cover and Hi do not arise under trivial frames): the honest slot-`q` votes, all
extending `P` by induction, or `A₀`'s for `q = r`, are carried, make `P` viable and outnumber the
rest, and the read point's live locks are compatible with `P`. -/
theorem outage_s5_innerAC (D : OutagePremisesAC wm u proposer tr H U)
    (hS : PSyncAC tr H U D.b₁) (i : Nat) (hinv : OutageInvAC D i) :
    ∀ k ≤ i, ∀ y ∈ H, ∀ e, VoteAt tr y k e → D.r < e.msg.slot → VoteExtends U e.msg D.P := by
  have hr := D.hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hki y hy e hv hrs
  obtain ⟨q, hs⟩ : ∃ q, e.msg.slot = q + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hrq : D.r ≤ q := by omega
  obtain ⟨ℓ, hc⟩ := id hv
  have hcast : CastAt tr y k ℓ e := hc
  have hsl := (castAt_specU hr hy hcast).2.1
  have hFP : Anc U ℓ.frame.F D.P := D.F_ancAC hy hcast.1
  -- the read point's live locks are compatible with `P`
  have hL := readPoint_liveLockBlocks_compatible_atAC D.hrun D.hj₀.1
    (fun _ _ hC _ => D.compatible_of_withinAC hC)
    (fun x hx hxW k' hk' e' hv' hs' =>
      hinv.toOutageVoteInvAC.voteCompat_of_not_lateWakerAC hx hxW (hk'.trans_le hki) hv' hs')
    D.two_mul_lt hy (hinv.locks y hy k hki) hcast (by omega) .refl
  have htk := (ts_le_castAC hr hy hv).1
  rw [hs, ts_succAC] at htk
  have hcallq : ∃ x ∈ H, ∃ j ℓ', tr.CallAt x j ℓ' ∧ sp.ts q + sp.Δ ≤ tr.time j :=
    ⟨y, hy, k, ℓ, hcast.1, by linarith only [htk, hΔ]⟩
  have hg : D.b₁ ≤ sp.ts q + sp.Δ := by
    have := ts_le_tsAC (sp := sp) hrq
    linarith only [this, D.hr.1]
  -- a carried honest batch extending `P`
  have hcarry : ∀ SX ⊆ H, (∀ x ∈ SX, ∀ j e', VoteAt tr x j e' → e'.msg.slot = q →
      VoteExtends U e'.msg D.P) →
      CarryAt tr U y k e q {v | ∃ x ∈ SX, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = q} := by
    intro SX hSX hall
    refine carryAt_afterAC hr hS hy hg hcast hs fun v hv' => ?_
    obtain ⟨x, hx, j, e', hve, rfl, hvs⟩ := hv'
    obtain ⟨Hd, hHd, hHdr, hPHd⟩ := hall x hx j e' hve hvs
    exact ⟨x, hSX hx, j, e', hve, rfl, hvs, Hd, hHd, hHdr, hFP.trans hPHd⟩
  have hviab : (∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = q ∧
      VoteExtends U e'.msg D.P) → ViableAtVote ℓ e (q + 1) D.P :=
    fun ⟨x, hx, j, e', hve, hvs, hext⟩ => viable_at_vote_afterAC hr D.htriv hS hy hg hcast hs
      D.hP.1 hFP ⟨x, hx, j, e', hve, hvs.le, hext⟩
  rcases hrq.lt_or_eq with hrq' | rfl
  · -- `q > r`: every honest slot-`q` vote extends `P` (induction)
    have hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = q →
        VoteExtends U e'.msg D.P := fun x hx j e' hve hvs =>
      have hjk := cut_lt_of_slotAC hr hx hy hv hve hs hvs
      ih j hjk (hjk.le.trans hki) x hx e' hve (by omega)
    have hfb := D.hFB q hcallq
    have hsub : {x | x ∈ H ∧ tr.awake x (sp.ts q + sp.Δ) ∧ JoinedAt tr x (sp.ts q + sp.Δ)} ⊆
        {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = q} := by
      rintro x ⟨hx, haw, hjn⟩
      obtain ⟨j, e', hve, hvs, -⟩ := vote_of_awake_joinedAC hr D.htick hx haw hjn
      exact ⟨hx, j, e', hve, hvs⟩
    have hcount : Hᶜ.ncard <
        {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = q}.ncard :=
      lt_of_lt_of_le hfb (Set.ncard_le_ncard hsub (Set.toFinite _))
    obtain ⟨x, hx, j, e', hve, hvs⟩ : ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = q := by
      by_contra hno
      push Not at hno
      have : {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = q} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x ⟨hx, j, e', hve, hvs⟩ => hno x hx j e' hve hvs
      rw [this, Set.ncard_empty] at hcount
      omega
    exact vote_extends_of_batchAC D.hrun hy hcast hs
      (hviab ⟨x, hx, j, e', hve, hvs, hall x hx j e' hve hvs⟩) hall hcount
      (hcarry H subset_rfl hall) hL
  · -- `q = r`: the cohort `A₀` casts and extends `P`; the others are in `Hᶜ ∪ W`
    have hσ := D.hσ
    have hrk := D.hrk
    have hall : ∀ x ∈ D.A₀, ∀ j e', VoteAt tr x j e' → e'.msg.slot = D.r →
        VoteExtends U e'.msg D.P := fun x hx j e' hve hvs =>
      hinv.votes x (D.hA₀ hx) j ((cut_lt_of_slotAC hr (D.hA₀ hx) hy hv hve hs hvs).trans_le hki)
        e' hve (by omega) (by omega) (Or.inr hx)
    have hSXv : ∀ x ∈ D.A₀, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = D.r := by
      intro x hx
      obtain ⟨haw, hjn⟩ :=
        cohort_readyAC D.hA₀awake D.hA₀join D.ha D.hz hx hrk.1 hrk.2 hcallq
      obtain ⟨j, e', hve, hvs, -⟩ := vote_of_awake_joinedAC hr D.htick (D.hA₀ hx) haw hjn
      exact ⟨j, e', hve, hvs⟩
    have hW : voters (mergedVoteView sp e.readPoint ℓ.frame (D.r + 1)).votes ⊆
        D.A₀ ∪ (Hᶜ ∪ D.W) := by
      rintro w ⟨v, hvm, rfl⟩
      by_cases hw : v.val ∈ H
      · obtain ⟨j, -, e', hve, he'⟩ := honest_merged_voteU D.hrun hy hcast hvm hw
        have hvs : e'.msg.slot = D.r := by
          rw [he']; exact merged_vote_slotU hr hy hcast v hvm
        rcases caster_mem_rAC D hw hve hvs with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hw)
    have hcount : (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard < 2 * D.A₀.ncard := by
      have := Set.ncard_union_le D.A₀ (Hᶜ ∪ D.W)
      have := D.hcohort
      omega
    obtain ⟨x, hx⟩ : D.A₀.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      have := D.hcohort
      rw [h, Set.ncard_empty] at this
      omega
    obtain ⟨j, e', hve, hvs⟩ := hSXv x hx
    exact vote_extends_of_counted_batchAC D.hrun hy hcast hs
      (hviab ⟨x, D.hA₀ hx, j, e', hve, hvs, hall x hx j e' hve hvs⟩) D.hA₀ hSXv hall hW hcount
      (hcarry D.A₀ D.hA₀ hall) hL

/-- **The restored-vote step** (`OutageS5StepAC`): compatibility past the lock lifetime, from the
inner induction at the cast cut. -/
theorem outage_s5_stepAC (D : OutagePremisesAC wm u proposer tr H U)
    (hS : PSyncAC tr H U D.b₁) : OutageS5StepAC D := by
  rw [outageS5StepAC_iff]
  intro i hinv y hy e hv hs
  have hrk := D.hrk
  exact (outage_s5_innerAC D hS i hinv i le_rfl y hy e hv (by omega)).voteCompat

/-- **INV at all cuts**: every honest vote of a slot after `r` extends `P`. -/
theorem restored_votes_extendAC (D : OutagePremisesAC wm u proposer tr H U)
    (hS : PSyncAC tr H U D.b₁) (hinv : ∀ i, OutageInvAC D i) :
    ∀ y ∈ H, ∀ k e, VoteAt tr y k e → D.r < e.msg.slot → VoteExtends U e.msg D.P :=
  fun y hy k e hv hs => outage_s5_innerAC D hS k (hinv k) k le_rfl y hy e hv hs

/-- **`ExtendingMajorityAC` at every restored label**: `q = r` by the cohort count
(`restored_majority_at_rAC`, with (H) for `A₀`), `q > r` by INV and the fault bound
(`extendingMajorityAC_of_all`). -/
theorem restored_majorityAC (D : OutagePremisesAC wm u proposer tr H U)
    (hS : PSyncAC tr H U D.b₁) (hinv : ∀ i, OutageInvAC D i) (q : Nat) (hq : D.r ≤ q)
    (hcall : ∃ x ∈ H, ∃ i ℓ, tr.CallAt x i ℓ ∧ sp.ts q + sp.Δ ≤ tr.time i) :
    ExtendingMajorityAC tr H U D.P q := by
  have hr := D.hrun.localRun
  rcases hq.lt_or_eq with hq | rfl
  · exact extendingMajorityAC_of_all hr D.htick
      (fun x hx k e hv hs => restored_votes_extendAC D hS hinv x hx k e hv (by omega))
      (D.hFB q hcall)
  · have hσ := D.hσ
    have hrk := D.hrk
    exact restored_majority_at_rAC hr D.htick D.hrk D.hA₀ D.hcohort D.hawake D.hA₀awake
      D.hA₀join D.ha D.hz (fun x hx k e hv hs => (hinv (k + 1)).votes x (D.hA₀ hx) k
        (Nat.lt_succ_self k) e hv (by omega) (by omega) (Or.inr hx)) hcall

end Consensus.Goldilocks.Comparison

end
