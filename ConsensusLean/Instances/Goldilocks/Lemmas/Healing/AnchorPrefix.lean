module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # Finite proposal-anchor prefix suppliers

The actual proposal cut precedes honest votes of its slot. Its stored locks
therefore have older labels, without a settled-phase premise. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The actual proposer's stored locks are older than its proposal slot.
An optimistic write would require an honest vote before the proposal cut;
a regular write is later even in time. The counted voters are members of the slot-`s` committee
(P), fewer than half of whose members are faulty. -/
private theorem stored_lock_lt_at_proposal (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H)
    {s i : Nat} (hs1 : 1 ≤ s) (hcs2 : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hz : proposer s ∈ H) (hc : tr.projAC.CallAt (proposer s) i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts s)
    {l : AC.Lock} (hl : l ∈ (tr.projAC.state (proposer s) i).locks) : l.slot < s := by
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hac.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hls
  have hreg : ∀ {r : Nat} {ellX : ACLabel (goldilocksNode sp ro)}, r < i →
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
  obtain ⟨hvs, j, hj, e, hvote, rfl⟩ := AC.optimisticPoint_pool_vote hac hz hpt hv hxH
  obtain ⟨ellv, hcv, hev⟩ := hvote
  have hcut := proposal_cut_lt hrun hnc hz hc hcall hti hs1 hxH ⟨hcv, hev⟩ hvs
  clear * - hri hj hcut; omega

/-- The actual proposal start is the current root or a live image of its
own unlocked locks. No phase or cross-node ancestry is assumed. -/
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
  unfold AC.getAnchor
  rcases hD : AC.deepest Phi (AC.liveLockBlocks sp _ Phi t ∪ {Phi.fcRoot}) with _ | D
  · exact Or.inl rfl
  · rcases (AC.deepest_mem hD).1 with h | h
    · exact Or.inr h
    · exact Or.inl (Set.mem_singleton_iff.1 h)

/-- Keep the live preimage before unlock, so its actual writer origin can
be classified without replacing it by an arbitrary optimistic lock. -/
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

/-- At the actual proposal start, expiry and proposal causality put every
non-root anchor in the warm older-label range. The returned lock is the
pre-unlock live lock. -/
theorem actual_proposal_start_live_origin (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H)
    {s₀ p i : Nat} (hp : 1 ≤ p) (hcs2 : 2 * (K.committee p ∩ Hᶜ).ncard < sp.committeeSize)
    (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H)
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
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := (AC.frameIn_of_callAt hr hz hc).1
  obtain ⟨l, hl, B, hB, hBr, hlive, hstart⟩ :=
    unlocked_live_preimage hPhi (AC.locksWF_state hr hrun.vstart hz i) hlock
  have hslot : sp.slot (tr.time i) = p := by
    rw [hti]
    exact AC.slot_of_mem sp p le_rfl (by
      simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  rw [hslot] at hlive
  obtain ⟨l₀, hl₀, hs, -⟩ := (AC.liveLocks_movesBack sp hPhi _ _ ) l hl
  have hold := stored_lock_lt_at_proposal hrun hnc hPK hp hcs2 hz hc hcall hti hl₀
  exact Or.inr ⟨l, hl, by clear * - hmargin hlive; omega, by clear * - hs hold; omega, B, hB,
    hBr, hstart⟩

/-- If the strict-cut induction already places the vote anchor at P, the
walk cannot move further: every frame child would have a later slot. -/
theorem vote_head_eq_of_anchor_eq (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = e.msg.slot)
    (hPt : P ∈ ell.frame.tree)
    (haP : AC.getAnchor sp e.readPoint ell.frame (tr.time i) = P) :
    e.msg.head = P.root := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := (AC.frameIn_of_callAt hr hy hc.1).1
  have hslot := AC.frame_slot_le sp hr hy hc.1
  have hs := (AC.castAt_spec hr hy hc).2.1
  have hstop : ¬ ∃ C, AC.IsBest sp
      (AC.headScore sp ell.frame (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot)
        ((e.msg.slot : Int) - 1))
      (AC.eligibleChildren
        (ell.frame.viableTree (AC.voteDomain sp e.readPoint ell.frame e.msg.slot))
        (AC.headEligible sp ell.frame (tr.time i)
          (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) P)
      C := by
    rintro ⟨C, ⟨⟨hC, hCP, -⟩, -⟩⟩
    have hlt := hPhi.coherent.2 P hPt C (AC.voteDomain_subset_tree hC.1) hCP
    have hle := hslot C (AC.voteDomain_subset_tree hC.1)
    omega
  have heq : AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voteDomain sp e.readPoint ell.frame e.msg.slot))
      (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) = P := by
    unfold AC.getHead
    rw [haP]
    exact AC.ghost_fuel_stable (Nat.zero_le _) hstop
  exact (AC.castAt_spec hr hy hc).2.2.2.trans (congrArg Block.root heq)

/-- Any point between the actual voter anchor and a frozen viable block is
itself frozen-viable. In head equality the upper block is P, not a transported
lock witness. -/
theorem frozen_viable_of_anchor_path (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {X P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (haX : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXP : Anc (tr.HonestBlocks H) X P) :
    X ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := AC.frameIn_of_callAt hr hy hc.1
  have hrootX := (Anc.mono hPhi.2
    (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))).trans haX
  have hXt := AC.frame_mem_of_between sp hr.coherent hPhi.1 hPhi.2 hP.1.1 hXP
    ((Anc.mono hPhi.2 hPhi.1.F_anc_fcRoot).trans hrootX)
  have hXPf := AC.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hXt hXP hP.1.1
  have hrootXf := AC.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2
    hPhi.1.fcRoot_mem hrootX hXt
  obtain ⟨Y, hY, hvY, hPY⟩ := hP.2.2
  exact ⟨AC.voterBlockTree_ancU hr.toU hrun.vstart hy hc P hP.1 X hXPf, hrootXf,
    Y, hY, hvY, hXPf.trans hPY⟩

/-- Actual pre-unlock live locks have genuine selection origins. Retain
the selected candidate, rather than an update-call-only residue. -/
theorem live_lock_selection_origin (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt x i ell)
    {l : AC.Lock}
    (hl : l ∈ AC.liveLocks sp (tr.projAC.state x i).locks ell.frame (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) :
    ∃ a < i, ∃ ellw D, tr.projAC.CallAt x a ellw ∧ D ∈ ellw.frame.tree ∧
      Anc (tr.HonestBlocks H) B (ellw.frame.viableAncestor D) ∧
      ((∃ CV, AC.FastUpdateAt tr.projAC x a l.slot D CV) ∨
        AC.SlowLockAt tr.projAC x a l.slot D ∨
        ∃ CV, AC.OptimisticLockAt tr.projAC x a l.slot D CV) := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := AC.frameIn_of_callAt hr hx hc
  obtain ⟨l₀, hl₀, E, hE, hEr, -, heq⟩ := hl
  have hs : l.slot = l₀.slot := by rw [heq]
  have hBE : ell.frame.Anc B E := by
    have he : B = ell.frame.viableAncestor E := hPhi.1.coherent.1 hB
      (AC.viableAncestor_anc hPhi.1 hE).1 (hBr.trans (congrArg AC.Lock.block heq))
    rw [he]
    exact (AC.viableAncestor_anc hPhi.1 hE).2
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    AC.lock_selection_candidate_provenance hr hrun.vstart hx i l₀ hl₀
  have he : M = E := hr.coherent.1 hM (hPhi.2 hE) (hMr.trans hEr.symm)
  rw [← hs] at ho
  refine ⟨a, hai, ellw, D, ha, hD, (Anc.mono hPhi.2 hBE).trans (he ▸ hMA), ?_⟩
  rcases ho with ⟨_, CV, hf | hop⟩ | ⟨_, hslow⟩
  · exact Or.inl ⟨CV, hf⟩
  · exact Or.inr (Or.inr ⟨CV, hop⟩)
  · exact Or.inr (Or.inl hslow)

/-- At an actual honest call, every ToFG candidate is compatible with any
other candidate of that same read. Candidacy itself is not inferred here. -/
theorem toFG_candidates_compatible_at_call (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
    ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Compatible (tr.HonestBlocks H) C P := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := AC.frameIn_of_callAt hr hy hc
  obtain ⟨Phi, t, hreach, _, hok⟩ := Compose.pre_reachable hr hy hc
  obtain ⟨hin, _, hinv⟩ := AC.lockInv_of_reachable hr.coherent (hrun.vstart y) hreach
  have hinv' := hinv.callOK hr.coherent hin hok
  have hlock {B : AC.Blk sp.n (List (FG.Att sp.n))}
      (hB : B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
      B ∈ AC.liveLockBlocks sp (tr.projAC.state y i).locks ell.frame (tr.time i) := by
    obtain ⟨hv, l, hl, hr, _⟩ := hB
    exact ⟨hv.1, l, hl, hr⟩
  intro C hC
  exact (hinv'.liveBlocks_chain hr.coherent hPhi.1 hPhi.2 C (hlock hC) P (hlock hP)).elim
    (fun h => Or.inl (Anc.mono hPhi.2 h)) (fun h => Or.inr (Anc.mono hPhi.2 h))

/-- The raw fast selection's block is no newer than its lock label. An
honest counted head supplies the bound even when the selection is optimistic. The counted voters
are members of the slot-`j` committee (P), fewer than half of whose members are faulty. -/
theorem fast_selection_slot_le (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H)
    {x : Fin sp.n} (hx : x ∈ H) {a j : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : AC.FastLockAt tr.projAC x a j D CV)
    (hcs2 : 2 * (K.committee j ∩ Hᶜ).ncard < sp.committeeSize) : D.slot ≤ j := by
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  obtain ⟨y, hy, i, e, hv, hs, W, hW, hWr, hDW⟩ :=
    AC.fastLock_honest_vote hac K hPK hx ho hcs2
  obtain ⟨W', hW', hW'r, hWs⟩ := AC.honest_head hac hy hv
  obtain rfl : W' = W := hac.localRun.coherent.1 hW' hW (hW'r.trans hWr.symm)
  exact (Anc.slot_le hac.localRun.coherent hDW).1.trans (hWs.trans_eq hs)

/-- The fresh lock remains a ToFG candidate at the adjacent read once its
full-frame viability and unchanged viable ancestor have been transported. -/
theorem fresh_lock_toFG_candidate {A : AC.ACState sp.n}
    {Phi : AC.Frm sp.n (List (FG.Att sp.n))} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    {u : Nat} {t : Time} (hv : P ∈ Phi.viableTree Phi.tree)
    (hva : Phi.viableAncestor P = P)
    {e : Nat} (hl : (⟨P.root, u, true, e⟩ : AC.Lock) ∈ A.locks) (he : u + 2 ≤ e)
    (ht : t = sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ AC.toFGCandidates sp A Phi t := by
  have hslot : sp.slot t = u + 1 := by
    rw [ht]
    apply AC.slot_of_mem sp (u + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  refine ⟨hv, ⟨P.root, u, true, e⟩, ?_, rfl, rfl, ?_⟩
  · refine ⟨⟨P.root, u, true, e⟩, hl, P, hv.1, rfl, ?_, ?_⟩
    · change sp.slot t ≤ e
      rw [hslot]
      omega
    · simp only [hva]
  · change sp.slot t ≤ u + 2
    rw [hslot]
    omega

end Consensus.Goldilocks.Healing

end
