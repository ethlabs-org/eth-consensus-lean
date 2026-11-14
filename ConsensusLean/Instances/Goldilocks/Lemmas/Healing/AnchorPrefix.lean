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

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The actual proposer's stored locks are older than its proposal slot.
An optimistic write would require an honest vote before the proposal cut;
a regular write is later even in time. -/
theorem stored_lock_lt_at_proposal (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {s i : Nat} (hs1 : 1 ≤ s) {ell : ACLabel (goldilocksNode sp ro)}
    (hz : proposer s ∈ H) (hc : tr.projAC.CallAt (proposer s) i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts s)
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state (proposer s) i).locks)
    (hstock : sp.committeeSize = sp.n) : l.slot < s := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hls
  have hreg : ∀ {r : Nat} {ellX : ACLabel (goldilocksNode sp ro)}, r < i →
      ¬ SA.UpdateAt tr.projAC (proposer s) r l.slot ellX := by
    intro r ellX hri hu
    have h1 := hrun.time_mono hri.le
    have h2 : tr.time r = sp.ts l.slot + 6 * sp.Δ := hu.2.2.1
    have h3 : sp.ts s ≤ sp.ts l.slot := (SA.ts_le_iff sp).2
      (by exact_mod_cast not_lt.1 hls)
    linarith only [hti, hΔ, h1, h2, h3]
  obtain ⟨r, hri, D, horigin, -⟩ := SA.lock_provenance hr hz i l hl
  rcases horigin with ⟨CV, ello, A, hpt, hsl, hsel, -⟩ | ⟨ellX, hu⟩
  swap
  · exact hreg hri hu
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hstock] at h34
  change 3 * sp.n ≤
    4 * (SA.optimisticVoters sp A ello.frame (sp.slot (tr.time r)) D).ncard at h34
  change sp.slot (tr.time r) = _ at hsl
  obtain ⟨x, ⟨v, hv, rfl, -⟩, hxH⟩ :
      ∃ x ∈ SA.optimisticVoters sp A ello.frame (sp.slot (tr.time r)) D, x ∈ H := by
    by_contra hno
    push Not at hno
    have hle : (SA.optimisticVoters sp A ello.frame (sp.slot (tr.time r)) D).ncard ≤
        Hᶜ.ncard := Set.ncard_le_ncard fun x hx => hno x hx
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  obtain ⟨hvs, j, hj, e, hvote, rfl⟩ := SA.optimisticPoint_pool_vote hac hz hpt hv hxH
  have hrs : sp.slot (tr.time r) ≤ s := by
    have ht := SA.slot_mono sp (hr.time_nonneg r) ((hrun.time_mono hri.le).trans hti.le)
    rwa [SA.slot_of_mem sp s le_rfl (by
      simp only [SAParams.ts]; push_cast; linarith only [hΔ])] at ht
  obtain ⟨ellv, hcv, hev⟩ := hvote
  have hcut := proposal_cut_lt hrun hnc hz hc hcall hti hs1 hxH ⟨hcv, hev⟩
    (by rw [hvs]; omega)
  clear * - hri hj hcut; omega

/-- The actual proposal start is the current root or a live image of its
own unlocked locks. No phase or cross-node ancestry is assumed. -/
theorem actual_proposal_start_cases {A : SA.SAState sp.n}
    {Phi : SA.Frm sp.n (List (FG.Att sp.n))} {t : Time}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp A Phi t).2 = some (d, pay)) :
    d.start = Phi.fcRoot ∨
      d.start ∈ SA.liveLockBlocks sp
        (SA.unlock sp A.locks Phi t ((sp.slot t : Int) - 1)
          (SA.View.ofLists (SA.voteViewList A Phi ((sp.slot t : Int) - 1) ⊤))) Phi t := by
  unfold SA.acProposal at hd
  split_ifs at hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, -⟩ := hd
  change SA.getAnchor sp _ Phi t = _ ∨ SA.getAnchor sp _ Phi t ∈ _
  unfold SA.getAnchor
  rcases hD : SA.deepest Phi (SA.liveLockBlocks sp _ Phi t ∪ {Phi.fcRoot}) with _ | D
  · exact Or.inl rfl
  · rcases (SA.deepest_mem hD).1 with h | h
    · exact Or.inr h
    · exact Or.inl (Set.mem_singleton_iff.1 h)

/-- Keep the live preimage before unlock, so its actual writer origin can
be classified without replacing it by an arbitrary optimistic lock. -/
theorem unlocked_live_preimage {Phi : SA.Frm sp.n (List (FG.Att sp.n))}
    (hPhi : FrameOK Phi) {L : Set SA.Lock} (hwf : SA.LocksWF sp L) {t : Time} {s : Int}
    {V : SA.View sp.n} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ SA.liveLockBlocks sp (SA.unlock sp L Phi t s V) Phi t) :
    ∃ l ∈ SA.liveLocks sp L Phi t, ∃ B ∈ Phi.tree, B.root = l.block ∧
      sp.slot t ≤ l.slot + sp.k ∧ Phi.Anc X B := by
  obtain ⟨l', ⟨l, hl, B, hB, hBr, heq⟩, E, hE, hEr, hlive, rfl⟩ :=
    SA.mem_liveLockBlocks_of_wf hPhi (hwf.unlock Phi t s V) hX
  have hs : l'.slot = l.slot := by
    rw [heq]; split_ifs <;> rfl
  refine ⟨l, hl, B, hB, hBr, hs ▸ hlive, ?_⟩
  have hEB : Phi.Anc E B := by
    rw [heq] at hEr
    split_ifs at hEr with hlt
    · have he : E = SA.unlockTarget sp Phi V s B :=
        hPhi.coherent.1 hE (SA.unlockTarget_anc sp hPhi V s hB).1 hEr
      rw [he]
      exact (SA.unlockTarget_anc sp hPhi V s hB).2
    · have he : E = B := hPhi.coherent.1 hE hB (hEr.trans hBr.symm)
      rw [he]
      exact .refl
  exact (SA.viableAncestor_anc hPhi hE).2.trans hEB

/-- At the actual proposal start, expiry and proposal causality put every
non-root anchor in the warm older-label range. The returned lock is the
pre-unlock live lock. -/
theorem actual_proposal_start_live_origin (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {s₀ p i : Nat} (hp : 1 ≤ p) (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H)
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) (hstock : sp.committeeSize = sp.n) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ SA.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  rcases actual_proposal_start_cases hd with hroot | hlock
  · exact Or.inl hroot
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := (SA.frameIn_of_callAt hr hz hc).1
  obtain ⟨l, hl, B, hB, hBr, hlive, hstart⟩ :=
    unlocked_live_preimage hPhi (SA.locksWF_state hr hz i) hlock
  have hslot : sp.slot (tr.time i) = p := by
    rw [hti]
    exact SA.slot_of_mem sp p le_rfl (by
      simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  rw [hslot] at hlive
  obtain ⟨l₀, hl₀, hs, -⟩ := (SA.liveLocks_movesBack sp hPhi _ _ ) l hl
  have hold := stored_lock_lt_at_proposal hrun hnc hf hp hz hc hcall hti hl₀ hstock
  exact Or.inr ⟨l, hl, by clear * - hmargin hlive; omega, by clear * - hs hold; omega, B, hB,
    hBr, hstart⟩

/-- If the strict-cut induction already places the vote anchor at P, the
walk cannot move further: every frame child would have a later slot. -/
theorem vote_head_eq_of_anchor_eq (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = e.msg.slot)
    (hPt : P ∈ ell.frame.tree)
    (haP : SA.getAnchor sp e.readPoint ell.frame (tr.time i) = P) :
    e.msg.head = P.root := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := (SA.frameIn_of_callAt hr hy hc.1).1
  have hslot := SA.frame_slot_le sp hr hy hc.1
  have hs := (SA.castAt_spec hr hy hc).2.1
  have hstop : ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot)
        ((e.msg.slot : Int) - 1))
      (SA.eligibleChildren
        (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame e.msg.slot))
        (SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) P)
      C := by
    rintro ⟨C, ⟨⟨hC, hCP, -⟩, -⟩⟩
    have hlt := hPhi.coherent.2 P hPt C (SA.voteDomain_subset_tree hC.1) hCP
    have hle := hslot C (SA.voteDomain_subset_tree hC.1)
    omega
  have heq : SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame e.msg.slot))
      (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) = P := by
    unfold SA.getHead
    rw [haP]
    exact SA.ghost_fuel_stable (Nat.zero_le _) hstop
  exact (SA.castAt_spec hr hy hc).2.2.2.trans (congrArg Block.root heq)

/-- Any point between the actual voter anchor and a frozen viable block is
itself frozen-viable. In head equality the upper block is P, not a transported
lock witness. -/
theorem frozen_viable_of_anchor_path (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {X P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (haX : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXP : Anc (tr.HonestBlocks H) X P) :
    X ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hrootX := (Anc.mono hPhi.2
    (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))).trans haX
  have hXt := SA.frame_mem_of_between sp hr.coherent hPhi.1 hPhi.2 hP.1.1 hXP
    ((Anc.mono hPhi.2 hPhi.1.F_anc_fcRoot).trans hrootX)
  have hXPf := SA.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hXt hXP hP.1.1
  have hrootXf := SA.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2
    hPhi.1.fcRoot_mem hrootX hXt
  obtain ⟨Y, hY, hvY, hPY⟩ := hP.2.2
  exact ⟨SA.voterBlockTree_anc hr hy hc P hP.1 X hXPf, hrootXf,
    Y, hY, hvY, hXPf.trans hPY⟩

/-- Actual pre-unlock live locks have genuine selection origins. Retain
the selected candidate, rather than an update-call-only residue. -/
theorem live_lock_selection_origin (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt x i ell)
    {l : SA.Lock}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state x i).locks ell.frame (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) :
    ∃ a < i, ∃ ellw D, tr.projAC.CallAt x a ellw ∧ D ∈ ellw.frame.tree ∧
      Anc (tr.HonestBlocks H) B (ellw.frame.viableAncestor D) ∧
      ((∃ CV, SA.FastUpdateAt tr.projAC x a l.slot D CV) ∨
        SA.SlowLockAt tr.projAC x a l.slot D ∨
        ∃ CV, SA.OptimisticLockAt tr.projAC x a l.slot D CV) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hx hc
  obtain ⟨l₀, hl₀, E, hE, hEr, -, heq⟩ := hl
  have hs : l.slot = l₀.slot := by rw [heq]
  have hBE : ell.frame.Anc B E := by
    have he : B = ell.frame.viableAncestor E := hPhi.1.coherent.1 hB
      (SA.viableAncestor_anc hPhi.1 hE).1 (hBr.trans (congrArg SA.Lock.block heq))
    rw [he]
    exact (SA.viableAncestor_anc hPhi.1 hE).2
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    SA.lock_selection_candidate_provenance hr hx i l₀ hl₀
  have he : M = E := hr.coherent.1 hM (hPhi.2 hE) (hMr.trans hEr.symm)
  rw [← hs] at ho
  refine ⟨a, hai, ellw, D, ha, hD, (Anc.mono hPhi.2 hBE).trans (he ▸ hMA), ?_⟩
  rcases ho with ⟨_, CV, hf | hop⟩ | ⟨_, hslow⟩
  · exact Or.inl ⟨CV, hf⟩
  · exact Or.inr (Or.inr ⟨CV, hop⟩)
  · exact Or.inr (Or.inl hslow)

/-- At an actual honest call, every ToFG candidate is compatible with any
other candidate of that same read. Candidacy itself is not inferred here. -/
theorem toFG_candidates_compatible_at_call (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
    ∀ C ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Compatible (tr.HonestBlocks H) C P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc
  obtain ⟨Phi, t, hreach, _, hok⟩ := Compose.pre_reachable hr hy hc
  obtain ⟨hin, _, hinv⟩ := SA.lockInv_of_reachable hr.coherent hreach
  have hinv' := hinv.callOK hr.coherent hin hok
  have hlock {B : SA.Blk sp.n (List (FG.Att sp.n))}
      (hB : B ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
      B ∈ SA.liveLockBlocks sp (tr.projAC.state y i).locks ell.frame (tr.time i) := by
    obtain ⟨hv, l, hl, hr, _⟩ := hB
    exact ⟨hv.1, l, hl, hr⟩
  intro C hC
  exact (hinv'.liveBlocks_chain hr.coherent hPhi.1 hPhi.2 C (hlock hC) P (hlock hP)).elim
    (fun h => Or.inl (Anc.mono hPhi.2 h)) (fun h => Or.inr (Anc.mono hPhi.2 h))

/-- An actual report comes from an earlier fast selection of a label no
later than the report's slot, retaining ancestry through lock remapping. -/
theorem toFG_fast_origin (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y i ell R) :
    ∃ a < i, ∃ j D CV, SA.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocks H) R D ∧ j ≤ sp.slot (tr.time i) := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hto.1
  have hRc : R ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i) := by
    have h := hto.2.2
    change (SA.acToFG sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some R at h
    unfold SA.acToFG at h
    split_ifs at h
    split at h
    · cases h
    · rename_i C hC
      split_ifs at h
      cases h
      exact (SA.deepest_mem hC).1
  obtain ⟨hv, l, hl, hlr, hlf, _⟩ := hRc
  obtain ⟨l₀, hl₀, B, hB, hBr, _, heq⟩ := hl
  have hf₀ : l₀.fast = true := by rw [heq] at hlf; exact hlf
  obtain ⟨a, hai, D, CV, ho, L, hL, hLr, hLD⟩ :=
    SA.fast_lock_provenance hr hy i l₀ hl₀ hf₀
  have hRB : Anc (tr.HonestBlocks H) R B := by
    have he : R = ell.frame.viableAncestor B := hPhi.1.coherent.1 hv.1
      (SA.viableAncestor_anc hPhi.1 hB).1 (hlr.symm.trans (congrArg SA.Lock.block heq))
    rw [he]
    exact Anc.mono hPhi.2 (SA.viableAncestor_anc hPhi.1 hB).2
  obtain rfl : L = B := hr.coherent.1 hL (hPhi.2 hB) (hLr.trans hBr.symm)
  refine ⟨a, hai, l₀.slot, D, CV, ho, hRB.trans hLD, ?_⟩
  have ht := hrun.time_mono hai.le
  rcases ho with ⟨ellw, C, hu, _⟩ | ⟨ellw, A, hp, hs, _⟩
  · have hlow : sp.ts l₀.slot ≤ tr.time a := by
      have htime : tr.time a = sp.ts l₀.slot + 6 * sp.Δ := hu.2.2.1
      linarith only [sp.toParams.hΔ, htime]
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).1 (hlow.trans ht)
    exact_mod_cast this
  · have hs' : l₀.slot = sp.slot (tr.time a) := hs.symm
    rw [hs']
    exact SA.slot_mono sp (hr.time_nonneg a) ht

/-- The raw fast selection's block is no newer than its lock label. An
honest counted head supplies the bound even when the selection is optimistic. -/
theorem fast_selection_slot_le (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {x : Fin sp.n} (hx : x ∈ H) {a j : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : SA.FastLockAt tr.projAC x a j D CV) (hstock : sp.committeeSize = sp.n) : D.slot ≤ j := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hf' : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  obtain ⟨y, hy, i, e, hv, hs, W, hW, hWr, hDW⟩ :=
    SA.fastLock_honest_vote hac hf' hx ho hstock
  obtain ⟨W', hW', hW'r, hWs⟩ := SA.honest_head hac hy hv
  obtain rfl : W' = W := hac.localRun.coherent.1 hW' hW (hW'r.trans hWr.symm)
  exact (Anc.slot_le hac.localRun.coherent hDW).1.trans (hWs.trans_eq hs)

/-- The fresh lock remains a ToFG candidate at the adjacent read once its
full-frame viability and unchanged viable ancestor have been transported. -/
theorem fresh_lock_toFG_candidate {A : SA.SAState sp.n}
    {Phi : SA.Frm sp.n (List (FG.Att sp.n))} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    {u : Nat} {t : Time} (hv : P ∈ Phi.viableTree Phi.tree)
    (hva : Phi.viableAncestor P = P)
    {e : Nat} (hl : (⟨P.root, u, true, e⟩ : SA.Lock) ∈ A.locks) (he : u + 2 ≤ e)
    (ht : t = sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ SA.toFGCandidates sp A Phi t := by
  have hslot : sp.slot t = u + 1 := by
    rw [ht]
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ]
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
