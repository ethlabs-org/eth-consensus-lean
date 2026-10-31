module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainCommon
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch

public section

/-! # Goldilocks Healing, HS.2: the proposal boundary

`hs234-exact-interface.md` §2.2 (last paragraph) and §3 (last paragraph), under the settled
context `Γ` of §1 (`DrainCommon`): the honest proposal `P` of a slot `s` follows a clean origin
`(B, j)` with `j < s` whose writer wrote before an in-phase honest slot-`s` vote, when every
honest vote of a slot `> j` before that vote extends `B`.

* The proposal's cut precedes the vote's cut (`proposal_cut_lt`): a late vote is after `t_s`,
  and an early one holds a slot-`s` block of the honest proposer, which it accepted after the
  proposer's own block call (`block_unforgeable`; HS.3's `proposal_before_holder`, private
  there and repeated here). So the proposer reads in the phase, and every honest vote it reads is
  before the vote.
* For `s ≥ j + 2` (`proposal_extends_of_batch`): `B` is viable in the proposer's full tree
  (`clean_vote_frame`: the aligned witness of an honest clean vote, relayed by `t_j + 3Δ`,
  HS.1 (c)), the honest slot-`(s−1)` votes extend `B` and reach the proposer
  (`late_vote_held_of_frame`), its locks of a label `≥ s − 1` are optimistic over earlier honest
  votes (`lock_below_origin`, `origin_compatible`), and ProposalCore's `batch_proposal` applies.
* A regular write of label `j` is at `t_j + 6Δ`, after every honest vote of slot `j + 1`, so a
  slow origin and a regular fast origin have `s ≥ j + 2` (`clean_slow_proposal`); an optimistic
  origin of label `j = s − 1` needs the first proposal transfer (`clean_fast_proposal`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ### The proposal precedes the votes of its slot -/

/-- **The proposal's cut precedes every honest holder of a slot-`s` block of its proposer**: the
holder accepted the block after its proposer's own block call (unforgeable blocks), which is the
cut after the `ac_proposal` cut (one tick per node and time). HS.3's private
`proposal_before_holder` (`AgreeFrozen`), over the proposal's data. -/
private theorem proposal_before_holder (hrun : GoldilocksRun dg H tr) {p : Fin sp.n}
    (hpH : p ∈ H) {kP s : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hcP : tr.projAC.CallAt p kP ℓp) (hcall : ℓp.call = .proposal)
    (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPs : P.slot = s) (hPprop : P.proposer = p) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    (hPz : P ∈ (tr.state z k).fg.tree) : kP < k := by
  have hl := hrun.toLocalRun
  rcases Compose.tree_cases hl hz hPz with hg | ⟨a, hak, ha⟩
  · have := congrArg (·.slot) hg
    simp only [Params.genesisBlock] at this
    omega
  obtain ⟨j', hj'a, hown⟩ := hl.block_unforgeable z hz a P ⟨true, ha⟩ (hPprop ▸ hpH)
  rw [hPprop] at hown
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  rcases Compose.blockCall_cases hl hpH hc with hg |
    ⟨j'', x, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hcP) hcall
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [htP, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by rw [← ht]; exact ⟨x, hg⟩)
  omega

/-- **The proposal's cut precedes every honest vote of its slot**: a vote after `t_s` is at a
later cut; an early vote holds a slot-`s` block (`cast_ready`), of the slot's proposer
(`HonestObjects.proposer`), so it is after the proposal (`proposal_before_holder`). -/
theorem proposal_cut_lt (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {kP s : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hpH : sp.toParams.proposer s ∈ H) (hcP : tr.projAC.CallAt (sp.toParams.proposer s) kP ℓp)
    (hcall : ℓp.call = .proposal) (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) : kP < k := by
  have hl := hrun.toLocalRun
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hac.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_cases hearly : tr.time k < sp.ts s + sp.Δ
  · obtain ⟨P', hP', hP's, -⟩ := SA.cast_ready hr hy hv (by rw [he]; exact hearly)
    rw [he] at hP's
    have hfU := (SA.frameIn_of_callAt hr hy hv.1).2
    have hroot : P'.root ≠ sp.genesisRoot := by
      intro hg
      have hG := Store.genesis_mem (Compose.fg_reachable hl hy k)
      obtain rfl := hU.1 (hfU hP') ⟨y, hy, k, hG⟩ hg
      simp [Params.genesisBlock] at hP's
      omega
    have hprop := hac.honest.proposer P' ⟨y, hy, k, ℓ, hv.1, hP'⟩ hroot
    exact proposal_before_holder hrun hpH hcP hcall htP hs1 hP's (by rw [hprop, hP's]) hy
      (mem_tree_of_frame hrun hy hv.1 hP')
  · by_contra hn
    have := hl.time_mono (not_lt.1 hn)
    linarith

/-! ### The first proposal after an optimistic origin, for an ancestor (general frames) -/

section General

open SA

variable {FGP : Type} {ro' : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)}
  {T : SATrace sp FGP ro'}

/-- **A1.4 (a) at the proposal duty, for an ancestor `B ⪯ D` of the optimistic selection**
(ProposalCore's `optimistic_first_proposal` with its hypotheses and conclusion about `B`, as
`result_transfer_anc` is for A1.8): for an honest optimistic lock of slot `σ` on `D` and
`B ⪯ D`, under (V) and (L-high) for `B`, (P) for the counted votes and `f < n/2`, the head of an
honest proposal of slot `σ + 1` extends `B`: the `3n/4` optimistic voters of `D` reach the
proposer, each as a supporter of `D`, hence of `B`, or an equivocator. -/
theorem optimistic_first_proposal_anc (hrun : ACRun T H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {D B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt T X i₀ σ D CV) (hBD : Anc U B D) {x : Fin sp.n} (hx : x ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro')} (hc : T.CallAt x i ℓ)
    (hslot : sp.slot (T.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (T.state x i) ℓ.frame (T.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (T.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (T.state x i) (T.time i) σ B) :
    Anc U B d.head := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨ℓX, A, hpt, hslX, hsel, rfl⟩ := id hopt
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hr hX hpt.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  obtain ⟨-, h34, -⟩ := (deepest_mem hsel').1
  rw [hslX] at h34
  set V := View.ofLists (voteViewList (T.state x i) ℓ.frame σ ⊤) with hV'
  set SX := optimisticVoters sp A ℓX.frame σ D
  -- every optimistic voter of `D` supports `B` at the proposal, or equivocates there
  have hcover : SX ⊆ supporters ℓ.frame V σ B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R', hR', hR'r, hDR'⟩
    have hvs := optimisticPoint_pool_slot hr hX hpt hv
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := heldAtProposal_iff.1 (hP v ⟨hv, R', hR', hR'r, hDR'⟩)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
    have hheld : v ∈ (T.state x i).pool σ := hheld.resolve_right fun h =>
      heq (equivocators_mono (fun u hu => (mem_proposalView_votes hr hx i σ ℓ.frame u).2 hu) h)
    have hRs : R.slot ≤ σ := by
      have := frame_slot_le sp hr hX hpt.1 R hR'
      omega
    exact proposal_supporter hr hx hc hvs hheld hR hRr hRs
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 (hBD.trans (Anc.mono hΦXU hDR')) hR) hbs heq
  -- counting: the equivocators are faulty, the other voters are outside `SX`
  have hE : (equivocators V.votes).ncard ≤ Hᶜ.ncard := Set.ncard_le_ncard fun w hw =>
    fun hwH => honest_not_equivocator_proposal hrun hx i σ ℓ.frame hwH hw
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ ((voters V.votes \ SX) ∪ SX))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_union_eq Set.disjoint_sdiff_left] at this
    exact this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  refine proposal_walk hr hx hc hslot hprop hV.2
    (unlocked_compatible hU hΦ hΦU hV.1 (Or.inl ⟨SX, fun w hw => ?_, by omega⟩)
      fun l hl hlive hlσ X hX hXr =>
        highLocksCompatible_iff.1 hhigh l hl hlive (by exact_mod_cast hlσ) X hX hXr)
    fun X' Cx hCx hp hCxB => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover h3 hCx hp hCxB
  rcases hcover hw with ⟨-, v, hv, hvw, hvs, hva⟩ | h
  · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · exact Or.inl h

end General

/-! ### The proposal after a clean origin -/

/-- **The proposer's high locks** at a proposal of slot `σ + 1` before an honest vote `k`: a lock
of a label `≥ σ` is optimistic (a result of such a label is written after `t_{σ+1}`), over honest
votes before the proposal; one of a label `> j` is compatible with `B` by the earlier votes, one
of label `j` by `hsame`. -/
private theorem proposer_high_locks (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) g)
    {p : Fin sp.n} (hpH : p ∈ H) {kP σ : Nat} (htP : tr.time kP = sp.ts (σ + 1 : Nat)) {k : Nat}
    (hkPk : kP < k) {j : Nat} (hjσ : j ≤ σ) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hsame : σ = j → ∀ k' CV O, SA.OptimisticLockAt tr.projAC p k' j O CV →
      Compatible (tr.HonestBlocks H) O B) :
    SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p kP) (tr.time kP) σ B := by
  have hrun' := hS.run
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
  obtain ⟨L, hL, hLr, O, hLO, k', hk', CV, hO⟩ := SA.lock_below_origin hr hpH kP l hl
  obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
  have hO' : Compatible (tr.HonestBlocks H) O B := by
    rcases hO with ⟨ℓ', ⟨-, -, htk', -⟩, -⟩ | hopt
    · exfalso
      have h1 := hr.time_mono hk'.le
      have h2 : sp.ts σ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hlσ)
      change tr.time k' ≤ tr.time kP at h1
      change tr.time k' = _ at htk'
      rw [htk', htP, hσ] at h1
      linarith
    rcases (show l.slot = j ∨ j < l.slot by omega) with hlj | hlj
    · rw [hlj] at hopt
      exact hsame (by omega) k' CV O hopt
    obtain ⟨ℓo, A, hpt, hsl, hsel, -⟩ := hopt
    obtain ⟨-, hΦoU⟩ := SA.frameIn_of_callAt hr hpH hpt.1
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (SA.deepest_mem hsel).1.2.1
    rw [hsl] at h34
    refine SA.origin_compatible hU hΦoU h34 hS.two_faulty_lt fun v hv hvH => ?_
    obtain ⟨hvs, j', hj', e'', hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hpH hpt hv hvH
    exact hprior _ hvH j' (by omega) e'' hve (by rw [hvs]; omega)
  rcases hO' with h | h
  · exact Or.inl (hLO.trans h)
  · exact SA.anc_total hU hLO h

/-- **The proposal follows `B` when its duty does** (`hs234-exact-interface.md` §2.2, the
proposal boundary): under `Γ` (without `Prop⁺`), let an honest vote of a clean slot `j` extend
`B`, and `y` cast an in-phase honest vote of a slot `s > j`. The proposal of slot `s` precedes
that vote (`proposal_cut_lt`); if its head extends `B` whenever (V) holds for `B` there and
`Σ.F ⪯ B` (`hcore`), then `P` extends `B`: when `B ⪯ Σ.F` the head extends `Σ.F`; otherwise `B`
is viable in the proposer's full tree (`clean_vote_frame`, at `t_s ≥ t_j + 4Δ`). -/
private theorem proposal_follows (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hes : e'.msg.slot = j) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H s P) (hjs : j < s)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hcore : ∀ {kP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
      {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n},
      tr.projAC.CallAt (sp.toParams.proposer s) kP ℓp → ℓp.call = .proposal →
      (SA.acProposal sp (tr.projAC.state (sp.toParams.proposer s) kP) ℓp.frame
        (tr.time kP)).2 = some (d, pay) →
      tr.time kP = sp.ts s → kP < k →
      B ∈ ℓp.frame.tree ∧
        (B ∈ ℓp.frame.viableTree ℓp.frame.tree ∨ ℓp.frame.Anc B ℓp.frame.fcRoot) →
      Anc (tr.HonestBlocks H) ℓp.frame.F B → Anc (tr.HonestBlocks H) B d.head) :
    Anc (tr.HonestBlocks H) B P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hpH, kP, ℓp, d, pay, hcP, hcall, hprop, htP, hpar, -, -, -, jA, -, hacc, -⟩ := hP
  have htP' : tr.time kP = sp.ts s := htP
  have hkPk : kP < k := proposal_cut_lt hrun hs.noColl hpH hcP hcall htP' (by omega) hy hv he
  have hkP : PhaseOn tr.projFG H i₀ kP m c := hk.mono_right hkPk.le
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hcP
  have hjs' : sp.ts (j + 1 : Nat) ≤ sp.ts s := (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hj1 : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- the parent edge `d.head → P`
  have hdt : d.head ∈ ℓp.frame.tree := by
    rw [(SA.acProposal_head hprop).2]
    exact SA.getHead_mem hΦ (fun _ hX => hX.1) _ _ _ _
  have hPU : P ∈ tr.HonestBlocks H := by
    obtain ⟨ℓA, hcA, hcallA⟩ := hacc
    exact (SA.frameIn_of_callAt hr hpH hcA).2
      ((SA.accept_new sp hr hpH ⟨ℓA, hcA, hcallA⟩).1 ℓA hcA)
  suffices hBd : Anc (tr.HonestBlocks H) B d.head from hBd.tail ⟨hΦU hdt, hPU, hpar⟩
  by_cases hBF : Anc (tr.HonestBlocks H) B ℓp.frame.F
  · exact hBF.trans ((hΦ.rooted.2 _ hdt).mono hΦU)
  -- (V) at the proposer
  have hVq := clean_vote_frame hrun hs hc hw hz hvz hj hes hext hpH hkP
    (by rw [htP']; linarith) B .refl
  rw [← Compose.frame_of_projAC hrun hpH hcP] at hVq
  rcases hVq with h | h
  · have hFB := (SA.anc_total hU h ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU)).resolve_left hBF
    have hBt := SA.mem_tree_of_between hU hΦ hΦU hFB h hΦ.fcRoot_mem
    exact hcore hcP hcall hprop htP' hkPk
      ⟨hBt, Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hBt h hΦ.fcRoot_mem)⟩ hFB
  · exact hcore hcP hcall hprop htP' hkPk ⟨h.1, Or.inl h⟩ ((hΦ.rooted.2 B h.1).mono hΦU)

/-- **The proposal of slot `σ + 1` follows `B`, at its own cut** (`hs234-exact-interface.md`
§2.2, keyed on the in-phase proposal cut; `proposal_extends_of_batch` keys it on a vote): under
`Γ` (without `Prop⁺`), let an honest vote of a clean slot `jw ≤ σ` extend `B`, and let every
honest vote of a slot `≥ σ` before the proposal's `ac_proposal` cut extend `B`. Then its head
extends `B`: unless `B ⪯ Σ.F`, `B` is viable in the proposer's full tree (`clean_vote_frame`),
the honest slot-`σ` votes reach it (`late_vote_held_of_frame`), its locks of a label `≥ σ` are
optimistic over earlier honest votes (a result of such a label is written after `t_{σ+1}`), and
`batch_proposal` applies. -/
theorem proposal_head_of_batch (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {jw : Nat} (hjw : w + 4 * sp.Δ ≤ sp.ts jw)
    (hes : e'.msg.slot = jw) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {σ : Nat} (hjσ : jw ≤ σ)
    {p : Fin sp.n} (hpH : p ∈ H) {kP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcP : tr.projAC.CallAt p kP ℓp)
    (hprop : (SA.acProposal sp (tr.projAC.state p kP) ℓp.frame (tr.time kP)).2 = some (d, pay))
    (htP : tr.time kP = sp.ts (σ + 1 : Nat)) (hkP : PhaseOn tr.projFG H i₀ kP m c)
    (hprior : ∀ z ∈ H, ∀ k' < kP, ∀ e', SA.VoteAt tr.projAC z k' e' → σ ≤ e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthyBase_of_hs hrun hs hc
  have hrun' := hS.run
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hcP
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hjσ' : sp.ts jw ≤ sp.ts σ := (SA.ts_le_iff sp).2 (by exact_mod_cast hjσ)
  have hdt : d.head ∈ ℓp.frame.tree := by
    rw [(SA.acProposal_head hprop).2]
    exact SA.getHead_mem hΦ (fun _ hX => hX.1) _ _ _ _
  by_cases hBF : Anc (tr.HonestBlocks H) B ℓp.frame.F
  · exact hBF.trans ((hΦ.rooted.2 _ hdt).mono hΦU)
  -- (V) at the proposer
  have hVq := clean_vote_frame hrun hs hc hw hz hvz hjw hes hext hpH hkP
    (by rw [htP, hσ]; linarith) B .refl
  rw [← Compose.frame_of_projAC hrun hpH hcP] at hVq
  obtain ⟨hV, hFB⟩ : (B ∈ ℓp.frame.tree ∧
      (B ∈ ℓp.frame.viableTree ℓp.frame.tree ∨ ℓp.frame.Anc B ℓp.frame.fcRoot)) ∧
      Anc (tr.HonestBlocks H) ℓp.frame.F B := by
    rcases hVq with h | h
    · have hFB := (SA.anc_total hU h ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU)).resolve_left hBF
      have hBt := SA.mem_tree_of_between hU hΦ hΦU hFB h hΦ.fcRoot_mem
      exact ⟨⟨hBt, Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hBt h hΦ.fcRoot_mem)⟩, hFB⟩
    · exact ⟨⟨h.1, Or.inl h⟩, (hΦ.rooted.2 B h.1).mono hΦU⟩
  -- the honest slot-`σ` votes are before the proposal, so they extend `B`
  have hB : ∀ x ∈ H, ∀ j' e'', SA.VoteAt tr.projAC x j' e'' → e''.msg.slot = σ →
      SA.VoteExtends (tr.HonestBlocks H) e''.msg B := by
    intro x hx j' e'' hv'' hs''
    refine hprior x hx j' ?_ e'' hv'' hs''.ge
    obtain ⟨ℓ'', hc'', he''⟩ := hv''
    have h1 := (Compose.cast_head_fcRoot hr hx ⟨hc'', he''⟩).2
    rw [hs''] at h1
    change tr.time j' ≤ _ at h1
    by_contra hn
    have := hr.time_mono (not_lt.1 hn)
    change tr.time kP ≤ tr.time j' at this
    linarith
  have hσg : gbar g + 4 * sp.Δ ≤ sp.ts σ := by linarith
  have hPv : ∀ x ∈ H, ∀ j' e'', SA.VoteAt tr.projAC x j' e'' → e''.msg.slot = σ →
      SA.HeldAtProposal (tr.projAC.state p kP) ℓp.frame σ e''.msg := by
    intro x hx j' e'' hv'' hs''
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hB x hx j' e'' hv'' hs''
    obtain ⟨Hd, hHdt, hHdr, -, hh⟩ := SA.late_vote_held_of_frame hS hpH hcP hσg
      (by change _ ≤ tr.time kP; rw [htP, hσ]; linarith) hx hv'' hs'' fun Hd hHd hHdr => by
        rw [hU.1 hHd hHd' (hHdr.trans hHd'r.symm)]
        exact hFB.trans hBHd'
    obtain ⟨hmem, -, hbs⟩ := hh kP (Or.inl rfl)
    exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHdt, hHdr,
      (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩
  -- (L-high): the proposer's locks of a label `≥ σ` are optimistic over earlier honest votes
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p kP) (tr.time kP)
      σ B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, k', hk', CV, hO⟩ := SA.lock_below_origin hr hpH kP l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hO' : Compatible (tr.HonestBlocks H) O B := by
      rcases hO with ⟨ℓ', ⟨-, -, htk', -⟩, -⟩ | ⟨ℓo, A, hpt, hsl, hsel, -⟩
      · exfalso
        have h1 := hr.time_mono hk'.le
        have h2 : sp.ts σ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hlσ)
        change tr.time k' ≤ tr.time kP at h1
        change tr.time k' = _ at htk'
        rw [htk', htP, hσ] at h1
        linarith
      · obtain ⟨-, hΦoU⟩ := SA.frameIn_of_callAt hr hpH hpt.1
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦoU h34 hS.two_faulty_lt fun v hv hvH => ?_
        obtain ⟨hvs, j', hj', e'', hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hpH hpt hv hvH
        exact hprior _ hvH j' (by omega) e'' hve (by rw [hvs]; omega)
    rcases hO' with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  exact SA.batch_proposal hrun' hS.two_faulty_lt (SA.honest_voters_half hS hσg) hB hpH hcP
    (SA.proposal_slot htP) hprop hV hPv hhigh

/-- **The proposal of a slot `s ≥ j + 2` follows `B`** (`hs234-exact-interface.md` §2.2, "for
subsequent slots use the unanimous honest batch"): under `Γ` (without `Prop⁺`), let an honest
vote of a clean slot `j` extend `B`, and let every honest vote of a slot `> j` before an in-phase
honest slot-`s` vote extend `B`. Then the honest slot-`s` proposal `P` extends `B`: its
`ac_proposal` cut precedes the vote (`proposal_follows`), so `proposal_head_of_batch` applies at
it. -/
theorem proposal_extends_of_batch (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hes : e'.msg.slot = j) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H s P) (hjs : j + 2 ≤ s)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P := by
  refine proposal_follows hrun hs hc hw hz hvz hj hes hext hP (by omega) hy hv he hk
    fun {kP ℓp d pay} hcP hcall hprop htP hkPk _ _ => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 1 := ⟨s - 1, by omega⟩
  exact proposal_head_of_batch hrun hs hc hw hz hvz hj hes hext (by omega) hP.1 hcP hprop htP
    (hk.mono_right hkPk.le) fun z hz k' hk' e' hv' hs' => hprior z hz k' (hk'.trans hkPk) e' hv'
      (by omega)

/-- **The proposal of slot `j + 1` follows an optimistic origin** (`hs234-exact-interface.md`
§2.2 "the same proof at a proposal boundary", §3): under `Γ` (without `Prop⁺`), let an honest
optimistic lock of a clean label `j` select `D ⪰ B`, and let every honest vote of a slot `> j`
before an in-phase honest slot-`(j+1)` vote extend `B`. Then the honest slot-`(j+1)` proposal
extends `B` (`proposal_follows`): the counted votes and their heads reach the proposer (relay
after `ḡ`, `Catch(2Δ)` before; `heldAtProposal_of_writer`), its locks of label `j` compare with
`D` by TSQ (`fastLock_fastLock_compatible`), hence with `B`, those of label `j + 1` by the
earlier votes (`proposer_high_locks`): `optimistic_first_proposal_anc`. -/
theorem proposal_extends_of_optimistic (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ))
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {D B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x i j D CV) (hBD : Anc (tr.HonestBlocks H) B D)
    (hj : w + 4 * sp.Δ ≤ sp.ts j) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : HonestProposalRun tr H (j + 1) P) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = j + 1)
    (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthyBase_of_hs hrun hs hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  have hU := hr.coherent
  obtain ⟨z, hz, kz, e', hvz, hes, Hd, hHd, hHdr, hDHd⟩ :=
    SA.fastLock_honest_vote hS.run hS.two_faulty_lt hx (Or.inr hopt)
  refine proposal_follows hrun hs hc hw hz hvz hj hes ⟨Hd, hHd, hHdr, hBD.trans hDHd⟩ hP
    (by omega) hy hv he hk fun {kP ℓp d pay} hcP hcall hprop htP hkPk hV hFB => ?_
  have hpH := hP.1
  have htP' : tr.time kP = sp.ts (j + 1 : Nat) := htP
  have hgj : gbar g ≤ sp.ts j := by linarith
  have hj1 : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- (P): the counted votes reach the proposer
  have hPv : ∀ v ∈ CV, SA.HeldAtProposal (tr.projAC.state (sp.toParams.proposer (j + 1)) kP)
      ℓp.frame j v := by
    intro v hv'
    obtain ⟨h₁, h₂, Hv, hHv, hHvr, hDHv, h₃⟩ := fastLock_writer hr hx (Or.inr hopt) v hv'
    have hFHv := hFB.trans (hBD.trans hDHv)
    refine SA.heldAtProposal_of_writer hr (hS.syncAC le_rfl (sp.ts j + 2 * sp.Δ)) hgj le_rfl hx
      hpH hcP htP' (fun k' _ hrk => lt_of_le_of_lt (hS.restart_le hpH hrk) (by linarith)) h₁ h₂
      ⟨Hv, hHv, hHvr, hFHv, ?_⟩
    rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
    · exact Or.inl hgen
    by_cases hkg : gbar g ≤ tr.time kw
    · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
    · obtain ⟨k', hk', hacc', hk't⟩ := hS.catchUp x hx kw Hv hkw (not_le.1 hkg)
        (sp.toParams.proposer (j + 1)) hpH kP ℓp hcP
        (by change _ ≤ tr.time kP; rw [htP', hj1]; linarith) hFHv
      exact Or.inr (Or.inr ⟨k', hk', hacc', by change tr.time k' < _ at hk't ⊢; linarith⟩)
  exact optimistic_first_proposal_anc hS.run hS.two_faulty_lt hx hopt hBD hpH hcP
    (SA.proposal_slot htP') hprop hV hPv
    (proposer_high_locks hS hpH htP' hkPk le_rfl hprior fun _ k' CV' O hopt' => by
      rcases SA.fastLock_fastLock_compatible hS hpH (Or.inr hopt') hx (Or.inr hopt) hgj with
        h | h
      · exact SA.anc_total hU h hBD
      · exact Or.inr (hBD.trans h))

/-- A regular write of label `j` (at `t_j + 6Δ`) before an honest vote of slot `s` (cast by
`t_s + Δ`) has `s ≥ j + 2`. -/
private theorem two_le_of_update (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {ℓx : ACLabel (goldilocksNode sp ro)}
    (hupd : SA.UpdateAt tr.projAC x i j ℓx) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (hik : i < k) : j + 2 ≤ e.msg.slot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h1 := hr.time_mono hik.le
  have h2 := (Compose.cast_head_fcRoot hr hy hv).2
  have h3 : tr.time i = sp.ts j + 6 * sp.Δ := hupd.2.2.1
  change tr.time i ≤ tr.time k at h1
  change tr.time k ≤ _ at h2
  by_contra hlt
  have h4 : sp.ts e.msg.slot ≤ sp.ts (j + 1 : Nat) := (SA.ts_le_iff sp).2 (by push_cast; omega)
  have h5 : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  linarith

/-! ### HS.2 (3) at the proposal boundary -/

/-- **Proposal-boundary transfer of a clean slow origin** (`hs234-exact-interface.md` §2.2 last
paragraph, §3 last paragraph): under `Γ` (without `Prop⁺`), let `x` write a slow lock of label
`j` (`t_{j−k+1} ≥ w + 4Δ`) with stored block `B` before an in-phase honest vote of slot `s > j`,
before which every honest vote of a slot `> j` extends `B`. Then the honest slot-`s` proposal
extends `B`: the write is at `t_j + 6Δ`, so `s ≥ j + 2`, and an honest supporter of the update's
result `C ⪰ B` (`result_extended`) gives `proposal_extends_of_batch`. -/
theorem clean_slow_proposal (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : StoredSlowLockAt tr x i j B) (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H s P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c) (hik : i < k)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthyBase_of_hs hrun hs hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj' : w + 4 * sp.Δ ≤ sp.ts j :=
    hj.trans ((SA.ts_le_iff sp).2 (by have := sp.two_le_k; omega))
  have hw8 := gbar_add_le_of_settled hw
  obtain ⟨ℓw, D, hcw, ⟨ℓX, C, hupd, hconf, -, hdeep, -⟩, rfl⟩ := ho
  obtain rfl : ℓX = ℓw := Option.some.inj (hupd.1.2.symm.trans hcw.2)
  have hΦU := (SA.frameIn_of_callAt hr hx hcw).2
  have hBC : Anc (tr.HonestBlocks H) (ℓX.frame.viableAncestor D) C :=
    Anc.mono hΦU ((SA.anc_viableAncestor _ D).trans (SA.deepest_mem hdeep).1.1.2.2)
  obtain ⟨z, hz, kz, e', hvz, hes, Hd, hHd, hHdr, hCHd⟩ :=
    SA.result_extended hS (by linarith) hx hupd.1 (by rw [hupd.2.2.1]; linarith) hconf
  exact proposal_extends_of_batch hrun hs hc hw hz hvz hj' hes ⟨Hd, hHd, hHdr, hBC.trans hCHd⟩
    hP (he ▸ two_le_of_update hrun hs.noColl hupd hy hv hik) hy hv he hk hprior

/-- **Proposal-boundary transfer of a clean fast origin** (`hs234-exact-interface.md` §2.2 last
paragraph, §3 last paragraph): under `Γ` (without `Prop⁺`), let `x` write a fast lock of a clean
label `j` with stored block `B` before an in-phase honest vote of slot `s > j`, before which every
honest vote of a slot `> j` extends `B`. Then the honest slot-`s` proposal extends `B`: an honest
counted vote extends the selection `D ⪰ B` (`fastLock_honest_vote`); for `s ≥ j + 2` the honest
batch (`proposal_extends_of_batch`); for `s = j + 1` the write is optimistic (a regular write is
at `t_j + 6Δ`, after the vote), and `proposal_extends_of_optimistic` applies. -/
theorem clean_fast_proposal (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H s P) (hjs : j < s)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c) (hik : i < k)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthyBase_of_hs hrun hs hc
  have hr := hS.run.localRun
  obtain ⟨ℓw, D, hcw, hfl, rfl⟩ := ho
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (SA.frameIn_of_callAt hr hx hcw).2 (SA.anc_viableAncestor _ D)
  by_cases hjs2 : j + 2 ≤ s
  · obtain ⟨z, hz, kz, e', hvz, hes, Hd, hHd, hHdr, hDHd⟩ :=
      SA.fastLock_honest_vote hS.run hS.two_faulty_lt hx hfl
    exact proposal_extends_of_batch hrun hs hc hw hz hvz hj hes
      ⟨Hd, hHd, hHdr, hBD.trans hDHd⟩ hP hjs2 hy hv he hk hprior
  obtain rfl : s = j + 1 := by omega
  rcases hfl with ⟨ℓX, C, hupd, -⟩ | hopt
  · exact absurd (he ▸ two_le_of_update hrun hs.noColl hupd hy hv hik) hjs2
  · exact proposal_extends_of_optimistic hrun hs hc hw hx hopt hBD hj hP hy hv he hk hprior

end Consensus.Goldilocks.Healing

end
