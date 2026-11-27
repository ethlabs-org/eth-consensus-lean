module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal-start lock origins in the shadow handler -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp}
  {ini : Fin sp.n → (goldilocksNode' sp).State}

private theorem proposal_call_tick' (h : Node.LocalRun' proposer dg H
    (fun v : Vote sp.n => v.val) tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode' sp)}
    (hc : tr.CallAt y i (.ac ell)) (hp : ell.call = .proposal) :
    ∃ j, i = j + 1 ∧ tr.TickAt' proposer dg y j (tr.time i) := by
  obtain ⟨j, e, q, hg, rfl, hq⟩ := Coherence.call_in_group' h hy hc
  have hm := List.mem_of_getElem? hq
  cases e with
  | tick x fgDue =>
    have hq1 : q = 1 := by
      have hnblock (st : NodeState (goldilocksNode' sp)) (B) :
          ∀ ell, Cut.ac ell ∈ (Node.onBlock' y st (tr.time (j + q)) B).2 →
            ell.call ≠ .proposal := by
        intro ell hm
        simp only [Node.onBlock'_eq] at hm
        split_ifs at hm
        · simp at hm
        · split at hm
          · simp at hm
          · simp only [Node.acCall'_eq, List.mem_cons, reduceCtorEq, false_or,
              Cut.ac.injEq, List.not_mem_nil, or_false] at hm
            subst hm
            simp
      have hnatt (st : NodeState (goldilocksNode' sp)) (B) :
          Cut.ac ell ∉ (Node.attest y st B).2 := by
        simp only [Node.attest]
        split <;> simp
      have hnfg (st : NodeState (goldilocksNode' sp)) :
          Cut.ac ell ∈ (Node.tickStep' proposer dg y st (tr.time (j + q)) x .fgUpdate).2 →
            ell.call ≠ .proposal := by
        simp only [Node.tickStep'_eq]
        split
        · simp only [List.mem_singleton, Node.acToFG'_eq, Cut.ac.injEq]
          rintro rfl
          simp
        · simp only [List.mem_cons]
          rintro (he | hm)
          · simp only [Node.acToFG'_eq, Cut.ac.injEq] at he
            subst he
            simp
          · exact (hnatt _ _ hm).elim
      have hprop (st : NodeState (goldilocksNode' sp)) {r : Nat}
          (hr : (Node.tickStep' proposer dg y st (tr.time (j + q)) x .proposal).2[r]? =
            some (.ac ell)) : r = 0 := by
        simp only [Node.tickStep'_eq] at hr
        split_ifs at hr
        · split at hr
          · cases r with
            | zero => rfl
            | succ r => simp at hr
          · cases r with
            | zero => rfl
            | succ r =>
              simp only [List.getElem?_cons_succ, Node.proposeBlock'_eq] at hr
              exact (hnblock _ _ ell (List.mem_of_getElem? hr) hp).elim
        · simp at hr
      have he : (Node.exec' proposer dg y (tr.state y j) (tr.time (j + q))
          (.tick x fgDue)).2 =
          [(Node.acCall' y (tr.state y j) (tr.time (j + q)) .tick).2] ++
          (Node.tickStep' proposer dg y
            (Node.tickStep' proposer dg y (tr.state y j) (tr.time (j + q)) x .acTick).1
            (tr.time (j + q)) x .proposal).2 ++
          (if fgDue then (Node.tickStep' proposer dg y
            (Node.tickStep' proposer dg y
              (Node.tickStep' proposer dg y (tr.state y j) (tr.time (j + q)) x .acTick).1
              (tr.time (j + q)) x .proposal).1 (tr.time (j + q)) x .fgUpdate).2 else []) := by
        cases fgDue <;> simp [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq,
          Node.tickSteps, Node.tickStep'_eq]
      rw [he] at hq
      cases q with
      | zero =>
        simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
          Option.some.injEq, Node.acCall'_eq, Cut.ac.injEq] at hq
        subst hq
        cases hp
      | succ q =>
        simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ] at hq
        by_cases hlt : q < (Node.tickStep' proposer dg y
            (Node.tickStep' proposer dg y (tr.state y j) (tr.time (j + (q + 1))) x .acTick).1
            (tr.time (j + (q + 1))) x .proposal).2.length
        · rw [List.getElem?_append_left hlt] at hq
          have := hprop _ hq
          omega
        · rw [List.getElem?_append_right (by omega)] at hq
          cases fgDue
          · simp at hq
          · exact (hnfg _ (List.mem_of_getElem? hq) hp).elim
    exact ⟨j, by omega, (RunTrace.tickAt'_iff ..).2 ⟨x, fgDue, hg⟩⟩
  | block B =>
    exfalso
    simp only [Node.exec'_eq, Node.onBlock'_eq] at hm
    split_ifs at hm
    · simp at hm
    · split at hm
      · simp at hm
      · simp only [Node.acCall'_eq, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
          List.not_mem_nil, or_false] at hm
        subst hm
        cases hp
  | message m =>
    exfalso
    simp only [Node.exec'_eq, Node.onMessage'_eq, Node.acCall'_eq,
      List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    cases hp
  | attestation a => simp [Node.exec'_eq, Node.onAttestation] at hm
  | restart =>
    exfalso
    simp only [Node.exec'_eq, Node.restart'_eq, Node.acCall'_eq,
      List.mem_singleton, Cut.ac.injEq] at hm
    subst hm
    cases hp

private theorem proposal_before_holder' (hrun : GoldilocksRun' proposer dg H tr ini)
    {p : Fin sp.n} (hpH : p ∈ H) {kP s : Nat} {ell : ACLabel (goldilocksNode' sp)}
    (hcP : tr.projAC.CallAt p kP ell) (hcall : ell.call = .proposal)
    (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPs : P.slot = s) (hPprop : P.proposer = p) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    (hPz : P ∈ (tr.state z k).fg.tree) : kP < k := by
  have hl := hrun.toLocalRun'
  rcases Coherence.tree_cases' hl hz hPz with hg | ⟨a, hak, ha⟩
  · have := congrArg (·.slot) hg
    simp only [Params.genesisBlock] at this
    omega
  obtain ⟨j', hj'a, hown⟩ := hl.block_unforgeable z hz a P ⟨true, ha⟩ (hPprop ▸ hpH)
  rw [hPprop] at hown
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hown
  rcases Coherence.blockCall_cases' hl hpH hc with hg |
    ⟨j'', x, fgDue, rfl, hg, hpr, d', pay', -, hB, -, -, -, -⟩
  · rw [RunTrace.groupAt'_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick' hl hpH (Compose.projAC_callAt.1 hcP) hcall
  have hslot : P.slot = sp.toParams.slotOf (tr.time (j'' + 2)) := by rw [hB]; rfl
  have ht : tr.time (j'' + 2) = tr.time (j₀ + 1) := by
    rw [htP, hpr.2.1, ← hslot, hPs, sp.slotTime_eq]; rfl
  have := hl.tick_unique p hpH j₀ j'' _ h₀ (by
    rw [← ht]
    exact (RunTrace.tickAt'_iff ..).2 ⟨x, fgDue, hg⟩)
  omega

private theorem frame_tree' (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode' sp)}
    (hc : tr.projAC.CallAt y i ell) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) : B ∈ (tr.state y i).fg.tree := by
  have hf := ((Node.cutStep'_ac _ _ _ _ _).1
    (hrun.cutLaw y hy i _ (Compose.projAC_callAt.1 hc))).1
  rw [hf, Node.frame'_eq, Store.toFrame'_tree] at hB
  exact hB.1

/-- The shadow proposal cut precedes every honest vote of its slot. -/
theorem proposal_cut_lt' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {kP s : Nat} {ellp : ACLabel (goldilocksNode' sp)}
    (hpH : proposer s ∈ H) (hcP : tr.projAC.CallAt (proposer s) kP ellp)
    (hcall : ellp.call = .proposal) (htP : tr.time kP = sp.ts s) (hs1 : 1 ≤ s)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode' sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.CastAt tr.projAC y k ell e)
    (he : e.msg.slot = s) : kP < k := by
  have hl := hrun.toLocalRun'
  have hac := Compose.goldilocks_ac_projection_from' hrun hnc
  have hr := hac.localRun
  have hU := Coherence.honest_blocks_coherent' hl hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_cases hearly : tr.time k < sp.ts s + sp.Δ
  · obtain ⟨⟨P', hP', hP's, -⟩, -⟩ := AC.cast_readyU hr.toU hy hv (by rw [he]; exact hearly)
    rw [he] at hP's
    have hfU := (AC.frameIn_of_callAt hr hy hv.1).2
    have hroot : P'.root ≠ sp.genesisRoot := by
      intro hg
      have hG := Store.genesis_mem_with Store.finalitySpec_updateFinality'
        (Node.fg_reachable_at' hl hy k).reachableWith
      obtain rfl := hU.1 (hfU hP') ⟨y, hy, k, hG⟩ hg
      simp [Params.genesisBlock] at hP's
      omega
    have hprop := hac.honest.proposer P' ⟨y, hy, k, ell, hv.1, hP'⟩ hroot
    exact proposal_before_holder' hrun hpH hcP hcall htP hs1 hP's (by rw [hprop, hP's]) hy
      (frame_tree' hrun hy hv.1 hP')
  · by_contra hn
    have := hl.time_mono (not_lt.1 hn)
    linarith only [htP, hΔ, hearly, this]

private theorem stored_lock_lt_at_proposal' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H)
    {s i : Nat} (hs1 : 1 ≤ s) (hcs2 : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize)
    {ell : ACLabel (goldilocksNode' sp)}
    (hz : proposer s ∈ H) (hc : tr.projAC.CallAt (proposer s) i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts s)
    {l : AC.Lock} (hl : l ∈ (tr.projAC.state (proposer s) i).locks) : l.slot < s := by
  have hac := Compose.goldilocks_ac_projection_from' hrun hnc
  have hr := hac.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hls
  have hreg : ∀ {r : Nat} {ellX : ACLabel (goldilocksNode' sp)}, r < i →
      ¬ AC.UpdateAt tr.projAC (proposer s) r l.slot ellX := by
    intro r ellX hri hu
    have h1 := hrun.time_mono hri.le
    have h2 : tr.time r = sp.ts l.slot + 6 * sp.Δ := hu.2.2.1
    have h3 : sp.ts s ≤ sp.ts l.slot := (AC.ts_le_iff sp).2
      (by exact_mod_cast not_lt.1 hls)
    linarith only [hti, hΔ, h1, h2, h3]
  obtain ⟨r, hri, D, horigin, -⟩ := AC.lock_provenanceU (hr := hr.toU) hrun.vstart hz i l hl
  rcases horigin with ⟨CV, ello, A, hpt, hsl, hsel, -⟩ | ⟨ellX, hu⟩
  swap
  · exact hreg hri hu
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (AC.deepest_mem hsel).1.2.1
  change sp.slot (tr.time r) = _ at hsl
  have hrs : sp.slot (tr.time r) ≤ s := by
    have ht := AC.slot_mono sp (hr.time_nonneg r) ((hrun.time_mono hri.le).trans hti.le)
    rwa [AC.slot_of_mem sp s le_rfl (by
      simp only [ACParams.ts]; push_cast; linarith only [hΔ])] at ht
  have hrs' : sp.slot (tr.time r) = s := by omega
  replace h34 : 3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A ello.frame s D).ncard := by
    rw [← hrs']; exact h34
  obtain ⟨x, ⟨v, hv, rfl, -⟩, hxH⟩ :
      ∃ x ∈ AC.optimisticVoters sp A ello.frame s D, x ∈ H := by
    obtain ⟨x, hx, hxK⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (s := K.committee s ∩ Hᶜ) (t := AC.optimisticVoters sp A ello.frame s D) (by omega)
    refine ⟨x, hx, not_not.1 fun h => hxK ⟨?_, h⟩⟩
    obtain ⟨v, hv, rfl, -⟩ := hx
    exact hPK.2 _ hz r ello A hpt s v hv
  obtain ⟨hvs, j, hj, e, hvote, rfl⟩ := AC.optimisticPoint_pool_voteU hac.toU hz hpt hv hxH
  obtain ⟨ellv, hcv, hev⟩ := hvote
  have hcut := proposal_cut_lt' hrun hnc hz hc hcall hti hs1 hxH ⟨hcv, hev⟩ hvs
  clear * - hri hj hcut
  omega

private theorem actual_proposal_start_cases {A : AC.ACState sp.n}
    {Phi : AC.Frm sp.n (List (FG.Att sp.n))} {t : Time}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp A Phi t).2 = some (d, pay)) :
    d.start = Phi.fcRoot ∨
      d.start ∈ AC.liveLockBlocks sp
        (AC.unlock sp A.locks Phi t ((sp.slot t : Int) - 1)
          (AC.View.ofLists (AC.voteViewList A Phi ((sp.slot t : Int) - 1) ⊤))) Phi t := by
  unfold AC.acProposal at hd
  split_ifs at hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, -⟩ := hd
  change AC.getAnchor sp _ Phi t = _ ∨ AC.getAnchor sp _ Phi t ∈ _
  exact (Compose.anchor_mem Phi _ t).elim Or.inr
    (fun h => Or.inl (Set.mem_singleton_iff.mp h))

private theorem unlocked_live_preimage {Phi : AC.Frm sp.n (List (FG.Att sp.n))}
    (hPhi : FrameOK Phi) {L : Set AC.Lock} (hwf : AC.LocksWF sp L) {t : Time} {s : Int}
    {V : AC.View sp.n} {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ AC.liveLockBlocks sp (AC.unlock sp L Phi t s V) Phi t) :
    ∃ l ∈ AC.liveLocks sp L Phi t, ∃ B ∈ Phi.tree, B.root = l.block ∧
      sp.slot t ≤ l.slot + sp.k ∧ Phi.Anc X B := by
  obtain ⟨l', ⟨l, hl, B, hB, hBr, heq⟩, E, hE, hEr, hlive, rfl⟩ :=
    AC.mem_liveLockBlocks_of_wf hPhi (hwf.unlock Phi t s V) hX
  have hs : l'.slot = l.slot := by
    rw [heq]; split_ifs <;> rfl
  refine ⟨l, hl, B, hB, hBr, hs ▸ hlive, ?_⟩
  have hEB : Phi.Anc E B := by
    rw [heq] at hEr
    split_ifs at hEr with hlt
    · have he : E = AC.unlockTarget sp Phi V s B :=
        hPhi.coherent.1 hE (AC.unlockTarget_anc sp hPhi V s hB).1 hEr
      rw [he]
      exact (AC.unlockTarget_anc sp hPhi V s hB).2
    · have he : E = B := hPhi.coherent.1 hE hB (hEr.trans hBr.symm)
      rw [he]
      exact .refl
  exact (AC.viableAncestor_anc hPhi hE).2.trans hEB

/-- Expiry and proposal causality put every non-root shadow proposal anchor in the
warm older-label range, retaining the actual pre-unlock live lock. -/
theorem actual_proposal_start_live_origin' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H)
    {s₀ p i : Nat} (hp : 1 ≤ p) (hcs2 : 2 * (K.committee p ∩ Hᶜ).ncard < sp.committeeSize)
    (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode' sp)} (hz : proposer p ∈ H)
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ AC.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  rcases actual_proposal_start_cases hd with hroot | hlock
  · exact Or.inl hroot
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have hPhi := (AC.frameIn_of_callAt hr hz hc).1
  obtain ⟨l, hl, B, hB, hBr, hlive, hstart⟩ :=
    unlocked_live_preimage hPhi (AC.locksWF_state hr hrun.vstart hz i) hlock
  have hslot : sp.slot (tr.time i) = p := by
    rw [hti]
    exact AC.slot_of_mem sp p le_rfl (by
      simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  rw [hslot] at hlive
  obtain ⟨l₀, hl₀, hs, -⟩ := (AC.liveLocks_movesBack sp hPhi _ _) l hl
  have hold := stored_lock_lt_at_proposal' hrun hnc hPK hp hcs2 hz hc hcall hti hl₀
  exact Or.inr ⟨l, hl, by clear * - hmargin hlive; omega,
    by clear * - hs hold; omega, B, hB, hBr, hstart⟩

end Consensus.Goldilocks.Healing

end
