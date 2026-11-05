module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety: the counts

* `OutageLockPremises.two_mul_lt` (N6): `2·|Hᶜ ∪ W| < n`.
* `OutageLockPremises.compatible_of_within`: an origin within `b₀` is compatible with `P` (§4.2).
* `OutageLockInv.voteCompat_of_not_lateWaker` (OL-W, §5.0): an honest vote of a slot `≥ j₀` at a
  cut before `i` by a validator that is not a late waker has a head compatible with `P`.
* `OutageLockInv.result_compatible` (R, §5.1): the result of an honest update of an unpolluted
  label at cut `i` is compatible with `P`; the three counts R-j₀ (pre-`b₀` service), R-mid (the
  cohort `A₀` against `Hᶜ ∪ W`) and R-late (S5 and the fault bound). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A block above another block compatible with `B` and below a block compatible with `B`: the
head of a vote extending `C`, compatible with `B`, makes `C` compatible with `B`. -/
theorem compatible_of_head_anc (hU : Coherent (tr.HonestBlocks H))
    {C R B : SA.Blk sp.n (List (FG.Att sp.n))} (hCR : Anc (tr.HonestBlocks H) C R)
    (hR : Compatible (tr.HonestBlocks H) R B) : Compatible (tr.HonestBlocks H) C B := by
  rcases hR with h | h
  · exact Or.inl (hCR.trans h)
  · exact Anc.total hU hCR h

/-- A vote compatible with `B` whose head extends `C` makes `C` compatible with `B`. -/
theorem compatible_of_voteCompat (hU : Coherent (tr.HonestBlocks H)) {v : Vote sp.n}
    {C R B : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ tr.HonestBlocks H) (hRr : R.root = v.head)
    (hCR : Anc (tr.HonestBlocks H) C R) (hv : VoteCompat (tr.HonestBlocks H) v B) :
    Compatible (tr.HonestBlocks H) C B := by
  obtain ⟨Hd, hHd, hHdr, hHdB⟩ := voteCompat_iff.1 hv
  obtain rfl : Hd = R := hU.1 hHd hR (hHdr.trans hRr.symm)
  exact compatible_of_head_anc hU hCR hHdB

/-- An ancestor of a block compatible with `B` is compatible with `B`. -/
theorem compatible_of_anc (hU : Coherent (tr.HonestBlocks H))
    {L C B : SA.Blk sp.n (List (FG.Att sp.n))} (hLC : Anc (tr.HonestBlocks H) L C)
    (hC : Compatible (tr.HonestBlocks H) C B) : Compatible (tr.HonestBlocks H) L B :=
  compatible_of_head_anc hU hLC hC

namespace OutageLockPremises

theorem coherent (D : OutageLockPremises tr H proposer dg) : Coherent (tr.HonestBlocks H) :=
  (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun.coherent

/-- **N6**: `2·|Hᶜ ∪ W| < n`. -/
theorem two_mul_lt (D : OutageLockPremises tr H proposer dg) : 2 * (Hᶜ ∪ D.W).ncard < sp.n := by
  have hdisj : Disjoint D.A₀ (Hᶜ ∪ D.W) := by
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (D.hA₀ hx), D.hW.2⟩
  have h1 := Set.ncard_union_eq hdisj
  have h2 : (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard ≤ sp.n := by
    calc (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard ≤ (Set.univ : Set (Fin sp.n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = sp.n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := D.hcohort
  omega

theorem two_faults_lt (D : OutageLockPremises tr H proposer dg) : 2 * Hᶜ.ncard < sp.n :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard Set.subset_union_left)) D.two_mul_lt

/-- A genesis `P` is below every honest block. -/
theorem anc_of_genesis (D : OutageLockPremises tr H proposer dg) (hg : D.P.root = sp.genesisRoot)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocks H) :
    Anc (tr.HonestBlocks H) D.P C := by
  obtain ⟨-, hgC⟩ := honest_genesis_anc D.hrun hC
  obtain ⟨hgU', -⟩ := honest_genesis_anc D.hrun D.hP.1
  have : sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload = D.P :=
    D.coherent.1 hgU' D.hP.1 (by rw [hg]; rfl)
  exact this ▸ hgC

/-- A genesis `P` is extended by every honest vote. -/
theorem vote_extends_of_genesis (D : OutageLockPremises tr H proposer dg)
    (hg : D.P.root = sp.genesisRoot) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨Hd, hHd, hHdr, -⟩ := SA.honest_head_frame hr hx ⟨hc, he⟩
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hx hc
  exact ⟨Hd, hΦU hHd, hHdr, D.anc_of_genesis hg (hΦU hHd)⟩

/-- A block of the honest blocks is compatible with `P` when `P` is genesis, and otherwise when
it is compatible with every origin `P` of label `σ` within `b₀`. -/
theorem compatible_of (D : OutageLockPremises tr H proposer dg)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocks H)
    (h : OriginWithin tr H D.P D.σ D.b₀ → Compatible (tr.HonestBlocks H) C D.P) :
    Compatible (tr.HonestBlocks H) C D.P := by
  rcases D.hP.2 with hg | hP
  · exact Or.inr (D.anc_of_genesis hg hC)
  · exact h hP

/-- **§4.2**: an origin within `b₀` is compatible with `P`. -/
theorem compatible_of_within (D : OutageLockPremises tr H proposer dg)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s D.b₀) (hCU : C ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) C D.P :=
  D.compatible_of hCU fun hP => D.hpre.origins_compatible C s D.P D.σ hC hP

/-- **§4.1**: an honest vote at a time `≤ b₀` of a slot after `σ` extends `P`. -/
theorem vote_extends_pre (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x k e) (hk : tr.time k ≤ D.b₀) (hs : D.σ < e.msg.slot) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  rcases D.hP.2 with hg | hP
  · exact D.vote_extends_of_genesis hg hx hv
  · exact D.hpre.vote_extends D.P D.σ hP x hx k e hv hk hs

end OutageLockPremises

variable {D : OutageLockPremises tr H proposer dg}

namespace OutageVoteInv

/-- The cast of an honest vote is at or after the start of its slot. -/
theorem ts_le_cast (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e) :
    sp.ts e.msg.slot ≤ tr.time k ∧ tr.time k ≤ sp.ts e.msg.slot + sp.Δ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  have hsl := (SA.castAt_spec hr hx ⟨hc, he⟩).2.1
  refine ⟨(SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [hsl]), ?_⟩
  have := SA.vote_time_le hr hx ⟨ℓ, hc, he⟩
  rw [hsl]
  exact this

/-- **OL-W** (§5.0): at a cut before `i`, an honest vote of a slot `≥ j₀` whose voter is not a
late waker has a head compatible with `P`. -/
theorem voteCompat_of_not_lateWaker {i : Nat} (hinv : OutageVoteInv D i) {x : Fin sp.n}
    (hx : x ∈ H) (hxW : x ∉ D.W) {k : Nat} (hk : k < i) {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x k e) (hs : D.j₀ ≤ e.msg.slot) :
    VoteCompat (tr.HonestBlocks H) e.msg D.P := by
  by_cases hlate : D.j₀ + sp.k < e.msg.slot
  · exact hinv.late x hx k hk e hv hlate
  have hσ := D.hσ
  by_cases hpre : tr.time k ≤ D.b₀ ∨ x ∈ D.A₀
  · exact (hinv.votes x hx k hk e hv (by omega) (by omega) hpre).voteCompat
  exfalso
  push Not at hpre
  obtain ⟨hts, hte⟩ := ts_le_cast D hx hv
  have hcall : tr.IsCall x k := by
    obtain ⟨ℓ, hc, -⟩ := hv
    exact ⟨_, projAC_callAt.1 hc⟩
  have hjs : sp.ts D.j₀ ≤ sp.ts e.msg.slot := ts_le_ts hs
  have hsK : sp.ts e.msg.slot ≤ sp.ts (D.j₀ + sp.k : Nat) := ts_le_ts (by omega)
  have hz := D.hz (tr.time k) (by linarith) ⟨x, hx, k, hcall, le_rfl⟩
  have haw := D.hrun.awake_of_call x hx k hcall
  rcases D.hawake x hx (tr.time k) (by linarith [D.ha, sp.toParams.hΔ]) hz haw with h | h
  · exact hpre.2 h
  · exact hxW h

end OutageVoteInv

/-- **A result's counted validators meet a participant set.** At an honest update with result
`C`, if `T` are voters of the update's pool and `|Q| < |T|`, some counted vote is of a validator in
`T` or outside `Q`. -/
theorem exists_counted_of_participants {X : Fin sp.n} {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {T Q : Set (Fin sp.n)}
    (hT : T ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s}) (hQT : Q.ncard < T.ncard) :
    ∃ v ∈ CV, v.val ∈ T ∨ v.val ∉ Q := by
  by_contra hno
  push Not at hno
  have hmaj := SA.result_majority hR
  obtain ⟨ℓ, -, -, hCV⟩ := hR
  have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
    rintro w ⟨v, hv, rfl⟩
    rw [hCV] at hv
    exact ⟨v, hv.1, rfl⟩
  have hdisj : Disjoint T {w | ∃ v ∈ CV, v.val = w} :=
    Set.disjoint_left.2 fun w hwT ⟨v, hv, hvw⟩ => (hno v hv).1 (hvw ▸ hwT)
  have h1 := Set.ncard_union_eq hdisj
  have h2 := Set.ncard_le_ncard (Set.union_subset hT hSV)
  have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Q.ncard :=
    Set.ncard_le_ncard fun w ⟨v, hv, hvw⟩ => hvw ▸ (hno v hv).2
  omega

/-- A counted vote of an honest validator at an honest update was cast at an earlier cut, of the
update's slot, and its head extends the result inside the honest blocks. -/
theorem counted_honest_vote (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC X i₀ s C CV) {v : Vote sp.n} (hv : v ∈ CV)
    (hvH : v.val ∈ H) :
    ∃ j < i₀, ∃ e, SA.VoteAt tr.projAC v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ tr.HonestBlocks H, R.root = v.head ∧ Anc (tr.HonestBlocks H) C R := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  obtain ⟨ℓ, hu, -, hCV⟩ := hR
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, hj, e, hve, he⟩ := hrun'.honest.pool_vote X hX i₀ s v hvp hvH
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hX hu.1
  exact ⟨j, hj, e, hve, he, SA.state_pool_slot sp hr hX i₀ s v hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- The result of an honest update is an honest block. -/
theorem result_mem (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC X i₀ s C CV) : C ∈ tr.HonestBlocks H := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨ℓ, hu, hC, -⟩ := hR
  exact (SA.frameIn_of_callAt hr hX hu.1).2 (SA.deepest_mem hC).1.1

namespace OutageVoteInv

/-- The time of an honest update of slot `m` and the slot point `t_m + Δ` before it. -/
private theorem update_after {X : Fin sp.n}
    (hX : X ∈ H) {i₀ m : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC X i₀ m ℓ) :
    tr.time i₀ = sp.ts m + 6 * sp.Δ ∧
      ∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts m + sp.Δ ≤ tr.time i := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time i₀ = sp.ts m + 6 * sp.Δ := hu.2.2.1
  exact ⟨ht, X, hX, i₀, ⟨_, projAC_callAt.1 hu.1⟩, by linarith⟩

/-- A member of `A₀` is awake and joined at `t_m + Δ` for a label `m ∈ [j₀ + 1, j₀ + k]` whose
update some honest call reaches. -/
theorem cohort_ready (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {m : Nat} (hm : D.j₀ + 1 ≤ m) (hmK : m ≤ D.j₀ + sp.k)
    (hcall : ∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts m + sp.Δ ≤ tr.time i) :
    tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj := ts_le_ts (sp := sp) (show D.j₀ ≤ m - 1 by omega)
  have hmK' := ts_le_ts (sp := sp) hmK
  have hm1 : sp.ts (m - 1 : Nat) + 4 * sp.Δ = sp.ts m := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hz := D.hz (sp.ts m + sp.Δ) (by linarith) hcall
  refine ⟨D.hA₀awake x hx _ (by linarith [D.ha, sp.toParams.hΔ]) hz, fun k hk hkt => ?_⟩
  have hslot : sp.slot (sp.ts m + sp.Δ) = m :=
    SA.slot_of_mem sp m (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  change 0 < sp.slot (sp.ts m + sp.Δ) ∧
    tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
  rw [hslot, sp.slotTime_eq]
  refine ⟨by omega, ?_⟩
  have := (D.hA₀join x hx k hk (hkt.trans hz)).trans D.ha
  have h' : sp.ts (m - 1 : Nat) = 4 * sp.Δ * ((m - 1 : Nat) : Int) := rfl
  rw [← h']
  linarith

/-- **(R) at cut `i`** (§5.1): the result of an honest update at cut `i` of an unpolluted label
is compatible with `P`. -/
theorem result_compatible {i : Nat} (hinv : OutageVoteInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {m : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC y i m C CV) (hm : m ≤ D.j₀ ∨ D.r ≤ m) :
    Compatible (tr.HonestBlocks H) C D.P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hr := hrun'.localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hCU := result_mem D.hrun D.hnc hy hR
  obtain ⟨ℓ, hu, -, -⟩ := id hR
  obtain ⟨ht, hcall⟩ := update_after hy hu
  have hj₀ := D.hj₀
  have hrk := D.hrk
  have hσ := D.hσ
  -- a counted honest vote compatible with `P` makes `C` compatible with `P`
  have finish : ∀ v ∈ CV, v.val ∈ H →
      (∀ j < i, ∀ e, SA.VoteAt tr.projAC v.val j e → e.msg = v →
        VoteCompat (tr.HonestBlocks H) e.msg D.P) →
      Compatible (tr.HonestBlocks H) C D.P := by
    intro v hv hvH hcompat
    obtain ⟨j, hj, e, hve, rfl, -, R, hRU, hRr, hCR⟩ :=
      counted_honest_vote D.hrun D.hnc hy hR hv hvH
    exact compatible_of_voteCompat hU hRU hRr hCR (hcompat j hj e hve rfl)
  rcases lt_or_ge m D.j₀ with hlt | hge
  · -- R-pre: the update is within `b₀`
    have hmj : sp.ts m + 6 * sp.Δ ≤ D.b₀ := by
      have := ts_le_ts (sp := sp) (show m + 1 ≤ D.j₀ by omega)
      have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    exact D.compatible_of_within (originWithin_iff.2 ⟨y, hy, i, CV, ht ▸ hmj, Or.inl hR⟩) hCU
  rcases hm with hm | hm
  · -- R-j₀: the honest slot-`j₀` voters reach the update by the early cutoff `≤ b₀`
    have hmeq : m = D.j₀ := le_antisymm hm hge
    have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state y i).pool m} := fun x hx =>
      awake_participant_early D.hrun D.hnc D.hpreSvc.ac (hmeq ▸ hj₀.1) hy hu hx.1 hx.2.1 hx.2.2
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote D.hrun D.hnc hy hR hv hvH
      rw [he]; exact hvs
    obtain ⟨-, hte⟩ := ts_le_cast D hvH hve
    rw [hs, hmeq] at hte
    exact (hinv.votes v.val hvH j hj e hve (by omega) (by omega) (Or.inl (by linarith))).voteCompat
  rcases le_or_gt m (D.j₀ + sp.k) with hmK | hmK
  · -- R-mid: `A₀` votes in slot `m` and extends `P`; the counted set is in `Hᶜ ∪ W`
    have hT : D.A₀ ⊆ SA.voters {v | v ∈ (tr.projAC.state y i).pool m} := by
      intro x hx
      obtain ⟨haw, hjn⟩ := cohort_ready D hx (by omega) hmK hcall
      obtain ⟨k, e, hve, hes, -⟩ := vote_of_awake_joined D.hrun D.hnc (D.hA₀ hx) haw hjn
      have := D.PG y hy i m ℓ hu hm x (D.hA₀ hx) k e hve hes
      rw [← projAC_state D.hrun.toLocalRun hy] at this
      obtain ⟨ℓ', hc', he'⟩ := hve
      exact ⟨e.msg, this, (SA.castAt_spec hr (D.hA₀ hx) ⟨hc', he'⟩).1⟩
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants hR hT D.hcohort
    have hvH : v.val ∈ H := by
      rcases hvT with h | h
      · exact D.hA₀ h
      · by_contra hn; exact h (Or.inl hn)
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote D.hrun D.hnc hy hR hv hvH
      rw [he]; exact hvs
    rcases hvT with hA | hQ
    · exact (hinv.votes v.val hvH j (by omega) e hve (by omega) (by omega) (Or.inr hA)).voteCompat
    · exact hinv.voteCompat_of_not_lateWaker hvH (fun h => hQ (Or.inr h)) (by omega) hve
        (by omega)
  · -- R-late: every honest slot-`m` vote is compatible with `P` (S5), and reaches the update
    have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state y i).pool m} := by
      intro x hx
      obtain ⟨k, e, hve, hes, -⟩ := vote_of_awake_joined D.hrun D.hnc hx.1 hx.2.1 hx.2.2
      have := D.PG y hy i m ℓ hu hm x hx.1 k e hve hes
      rw [← projAC_state D.hrun.toLocalRun hy] at this
      obtain ⟨ℓ', hc', he'⟩ := hve
      exact ⟨e.msg, this, (SA.castAt_spec hr hx.1 ⟨hc', he'⟩).1⟩
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote D.hrun D.hnc hy hR hv hvH
      rw [he]; exact hvs
    exact hinv.late v.val hvH j hj e hve (by omega)

end OutageVoteInv

end Consensus.Goldilocks.Compose

end
