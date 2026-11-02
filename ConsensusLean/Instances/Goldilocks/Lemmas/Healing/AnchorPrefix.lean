module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.RegularBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal

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
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state (proposer s) i).locks) : l.slot < s := by
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
    linarith
  obtain ⟨r, hri, D, horigin, -⟩ := SA.lock_provenance hr hz i l hl
  rcases horigin with ⟨CV, ello, A, hpt, hsl, hsel, -⟩ | ⟨ellX, hu⟩
  swap
  · exact hreg hri hu
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 : 3 * sp.n ≤
      4 * (SA.optimisticVoters sp A ello.frame (sp.slot (tr.time r)) D).ncard :=
    (SA.deepest_mem hsel).1.2.1
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
      simp only [SAParams.ts]; push_cast; linarith)] at ht
  obtain ⟨ellv, hcv, hev⟩ := hvote
  have hcut := proposal_cut_lt hrun hnc hz hc hcall hti hs1 hxH ⟨hcv, hev⟩
    (by rw [hvs]; omega)
  omega

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

/-- A live unlocked anchor image has an actual stored preimage. Both
unlock and viableAncestor move backwards, and preserve the label. -/
theorem unlocked_anchor_preimage {Phi : SA.Frm sp.n (List (FG.Att sp.n))}
    (hPhi : FrameOK Phi) {L : Set SA.Lock} {t : Time} {s : Int} {V : SA.View sp.n}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ SA.liveLockBlocks sp (SA.unlock sp L Phi t s V) Phi t) :
    ∃ l ∈ L, ∃ B₀ ∈ Phi.tree, B₀.root = l.block ∧ sp.slot t ≤ l.slot + sp.k ∧
      Phi.Anc B B₀ := by
  obtain ⟨l, hl, E, hE, hEr, hlive, rfl⟩ := SA.mem_liveLockBlocks hPhi hB
  obtain ⟨l₀, hl₀, hs, _, B₀, hB₀, hB₀r, B₁, hB₁, hB₁r, hB₁B₀⟩ :=
    ((SA.locks_move_back sp) _ Phi L t hPhi).2.2 s V l hl
  obtain rfl : B₁ = E := hPhi.coherent.1 hB₁ hE (hB₁r.trans hEr.symm)
  exact ⟨l₀, hl₀, B₀, hB₀, hB₀r, hs ▸ hlive,
    (SA.viableAncestor_anc hPhi hE).2.trans hB₁B₀⟩

/-- Keep the live preimage before unlock, so its actual writer origin can
be classified without replacing it by an arbitrary optimistic lock. -/
theorem unlocked_live_preimage {Phi : SA.Frm sp.n (List (FG.Att sp.n))}
    (hPhi : FrameOK Phi) {L : Set SA.Lock} {t : Time} {s : Int} {V : SA.View sp.n}
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ SA.liveLockBlocks sp (SA.unlock sp L Phi t s V) Phi t) :
    ∃ l ∈ SA.liveLocks sp L Phi t, ∃ B ∈ Phi.tree, B.root = l.block ∧
      sp.slot t ≤ l.slot + sp.k ∧ Phi.Anc X B := by
  obtain ⟨l', ⟨l, hl, B, hB, hBr, heq⟩, E, hE, hEr, hlive, rfl⟩ :=
    SA.mem_liveLockBlocks hPhi hX
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

/-- The below-write-root optimistic branch stays below the writer's current
root, even after unlock and viableAncestor. This is not a cross-node root bound. -/
theorem FrameWindow.unlocked_image_below_write_root {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ellw ell : ACLabel (goldilocksNode sp ro)}
    (hcw : tr.projAC.CallAt y a ellw) (hc : tr.projAC.CallAt y i ell)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {L B A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hLB : ell.frame.Anc L B) (hBA : Anc (tr.HonestBlocks H) B A)
    (hroot : ellw.frame.Anc A ellw.frame.fcRoot) :
    Anc (tr.HonestBlocks H) L ell.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hAw := Anc.mono (SA.frameIn_of_callAt hr hy hcw).2 hroot
  have hmono := hframe.fcRoot_mono hrun hy hai halo hihi
  rw [Compose.frame_of_projAC hrun hy hcw] at hAw
  have hbound : Anc (tr.HonestBlocks H) L (tr.state y i).fg.fcRoot :=
    (Anc.mono (SA.frameIn_of_callAt hr hy hc).2 hLB).trans (hBA.trans (hAw.trans hmono))
  rw [Compose.frame_of_projAC hrun hy hc]
  exact hbound

/-- A write-held viable witness supplies the frozen domain for a boundary
optimistic prefix. The receiver-root split is explicit; this branch is used
only when the receiver's finalized root is below the target. -/
theorem FrameWindow.optimistic_prefix_of_early_witness {s floor : Nat}
    {contest kindJ : Prop} {J B Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {x w y : Fin sp.n} (hx : x ∈ H) (hw : w ∈ H) (hy : y ∈ H)
    {c a i : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocks H) B D)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw ell : ACLabel (goldilocksNode sp ro)}
    (hcw : tr.projAC.CallAt w a ellw) (hQw : Q ∈ ellw.frame.tree)
    (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J B)
    (hBQ : Anc (tr.HonestBlocks H) B Q)
    {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hFB : Anc (tr.HonestBlocks H) (tr.state y i).fg.F B)
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hw hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨w, hw, a, hQ⟩
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  have hslot := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have hlo : sp.ts s ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change (s : Int) ≤ sp.slot (tr.time i)
      rw [hslot]; omega)
  have hhi := SA.vote_time_le hr hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
  rw [hslot] at hhi
  have hFQ : Anc (tr.HonestBlocks H) ell.frame.F Q := by
    rw [Compose.frame_of_projAC hrun hy hc.1]
    exact hFB.trans hBQ
  have hQdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hw hy hQU
    (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hc
    (by omega) (hhi.trans hmb) (by
      rw [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]
      linarith) hFQ
  obtain ⟨-, hroot, -, hvQ, hBQf⟩ := hframe.witness_path hrun hnc hmf hy hw hc.1
    hlo hhi hQ hh hJ hBQ (mem_tree_of_frame hrun hy hc.1 hQdom.1) hFB
  have hdomA := SA.voterBlockTree_anc hr hy hc
  rw [hes] at hQdom hdomA
  have hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) :=
    ⟨hdomA Q hQdom B hBQf, hroot, Q, hQdom, hvQ, hBQf⟩
  have hFD : Anc (tr.HonestBlocks H) ell.frame.F D := by
    rw [Compose.frame_of_projAC hrun hy hc.1]
    exact hFB.trans hBD
  exact optimistic_prefix_before hrun hnc hsvc hawake hf hcatch hm hx hy hopt hBD hc hes
    (hhi.trans hmb) hFD hB haB

/-- Older-lock dominance supplies a finite voter prefix. The prior heads
extend the lock image, not the proposal parent; actual delivery is derived. -/
theorem FrameWindow.honest_prefix_before {s floor : Nat}
    {contest kindJ : Prop} {J B Q : SA.Blk sp.n (List (FG.Att sp.n))}
    {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hQ : Q ∈ (tr.state w a).fg.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J Q)
    (hheads : ∀ x ∈ H, ∀ j ev, SA.VoteAt tr.projAC x j ev → ev.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) ev.msg Q)
    (hBQ : Anc (tr.HonestBlocks H) B Q)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hslot := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have hlo : sp.ts s ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change (s : Int) ≤ sp.slot (tr.time i)
      rw [hslot]; omega)
  have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
  rw [hslot] at ht
  have hstart : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
      rw [hslot])
  have hstep : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hcarry := hframe.honest_batch_carry hrun hnc hmf hS hy hw hc hes hm
    (by rw [hstep] at hstart; linarith) (ht.trans hmb) hlo ht
    (fun k hk t ht => by
      apply deadline_le_restarts (a := sp.ts s)
      intro r _ hrs
      have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ _
      linarith)
    (fun k hk hrs => by
      have := hnr y hy k (Compose.projAC_restartAt.mp hrs)
      change tr.time k < _
      linarith) hQ hh hJ hheads
  have hex : ∀ x ∈ H, ∃ j ev, SA.VoteAt tr.projAC x j ev ∧ ev.msg.slot = s := by
    intro x hx
    obtain ⟨j, ev, hv, hs, -⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
      hcatch hnr hm (by rw [hstep] at hmb; linarith) x hx
    exact ⟨j, ev, hv, hs⟩
  have hf' : 3 * Hᶜ.ncard < sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  exact SA.honest_prefix_of_carry sp hS.run hf' hy hc hes
    (fun x hx j ev hv hs => by
      obtain ⟨R, hR, hRr, hQR⟩ := hheads x hx j ev hv hs
      exact ⟨R, hR, hRr, hBQ.trans hQR⟩) hex hcarry hB haB

/-- At the actual proposal start, expiry and proposal causality put every
non-root anchor in the warm older-label range. The returned lock is the
pre-unlock live lock, ready for live_lock_write_origin. -/
theorem actual_proposal_start_live_origin (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 3 * Hᶜ.ncard ≤ sp.n - 1)
    {s₀ p i : Nat} (hp : 1 ≤ p) (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H)
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ SA.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  rcases actual_proposal_start_cases hd with hroot | hlock
  · exact Or.inl hroot
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := (SA.frameIn_of_callAt hr hz hc).1
  obtain ⟨l, hl, B, hB, hBr, hlive, hstart⟩ := unlocked_live_preimage hPhi hlock
  have hslot : sp.slot (tr.time i) = p := by
    rw [hti]
    exact SA.slot_of_mem sp p le_rfl (by
      simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
  rw [hslot] at hlive
  obtain ⟨l₀, hl₀, hs, -⟩ := (SA.liveLocks_movesBack sp hPhi _ _ ) l hl
  have hold := stored_lock_lt_at_proposal hrun hnc hf hp hz hc hcall hti hl₀
  exact Or.inr ⟨l, hl, by omega, by omega, B, hB, hBr, hstart⟩

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
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) P)
      C := by
    rintro ⟨C, ⟨⟨hC, hCP, -⟩, -⟩⟩
    have hlt := hPhi.coherent.2 P hPt C hC.1.1 hCP
    have hle := hslot C hC.1.1
    omega
  have heq : SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
      (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) = P := by
    unfold SA.getHead
    rw [haP]
    exact SA.ghost_fuel_stable (Nat.zero_le _) hstop
  exact (SA.castAt_spec hr hy hc).2.2.2.trans (congrArg Block.root heq)

/-- The deeper-anchor join: only a voter strictly below the proposal start
needs a prefix supplier. A deeper voter anchor is already on the proposal
path, unless it equals P, where the slot bound stops it. -/
theorem FrameWindow.vote_head_eq_of_start_prefix {s₀ s floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))} {g b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1) (hpH : P.proposer ∈ H)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haP : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) P)
    (hprefix : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) d.start →
      ell.frame.Anc d.start (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)) : e.msg.head = P.root := by
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  obtain ⟨hst, _, hw⟩ := proposal_walk_end hrun hnc hz hcp hpay
  have hstartQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hstartQ he).2
  have hQP : Anc (tr.HonestBlocks H) d.head P :=
    .single ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  let A := SA.getAnchor sp e.readPoint ell.frame (tr.time i)
  have hAt : A ∈ ell.frame.tree := by
    by_cases he : ell.frame.fcRoot = A
    · exact he ▸ hPhi.1.fcRoot_mem
    · exact (Anc.mem (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  by_cases he : A = P
  · exact vote_head_eq_of_anchor_eq hrun hnc hy hc (hPs.trans hes.symm) hPv.1.1 he
  have hAQ : Anc (tr.HonestBlocks H) A d.head := by
    rcases Relation.ReflTransGen.cases_tail haP with heq | ⟨Y, hAY, hYP⟩
    · exact (he heq.symm).elim
    have hYQ : Y = d.head := hr.coherent.1 hYP.1 (hPhip.2 hQt)
      (Option.some.inj (hYP.2.2.symm.trans hparent))
    exact hYQ ▸ hAY
  rcases Anc.total hr.coherent hAQ (Anc.mono hPhip.2 hstartQ) with hAS | hSA
  · have hSt := SA.frame_mem_of_between sp hr.coherent hPhi.1 hPhi.2 hPv.1.1
      ((Anc.mono hPhip.2 hstartQ).trans hQP)
      ((Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans
        (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)))).trans hAS)
    have hASf := SA.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hAt hAS hSt
    exact hframe.vote_head_eq_of_path hrun hnc hS hnr hf hm hs₀ hz hdesignated hactual
      hPs hpH hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      .refl hstartQ hASf (hprefix hASf)
  · have hApt := SA.frame_mem_of_between sp hr.coherent hPhip.1 hPhip.2 hQt hAQ
      (Anc.mono hPhip.2 (hPhip.1.F_anc_fcRoot.trans
        (proposal_walk_end hrun hnc hz hcp hpay).2.1) |>.trans hSA)
    have hSAf := SA.anc_tree_of_anc_U hr.coherent hPhip.1 hPhip.2 hst hSA hApt
    have hAQf := SA.anc_tree_of_anc_U hr.coherent hPhip.1 hPhip.2 hApt hAQ hQt
    have hAE : ell.frame.Anc A (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
      unfold SA.getHead
      exact SA.anc_ghost (fun X hX => hX.1.1) _ hAt
    exact hframe.vote_head_eq_of_path hrun hnc hS hnr hf hm hs₀ hz hdesignated hactual
      hPs hpH hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      hSAf hAQf .refl hAE

/-- A voter below another honest fcRoot reaches it. In kind J the roots
agree; otherwise V forces the prefix to the other finalized block. -/
theorem FrameWindow.fcRoot_anc_head_at_cast {lo hi : Time} {floor : Nat}
    {contest kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {z y : Fin sp.n} (hz : z ∈ H) (hy : y ∈ H) {c i : Nat}
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ellz ell : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z c ellz)
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ell e)
    {Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i))
      ellz.frame.fcRoot) :
    Anc (tr.HonestBlocks H) ellz.frame.fcRoot
      (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  by_cases hk : kindJ
  · have hroots : ellz.frame.fcRoot = ell.frame.fcRoot := by
      rw [Compose.frame_of_projAC hrun hz hcz, Compose.frame_of_projAC hrun hy hc.1]
      change (tr.state z c).fg.fcRoot = (tr.state y i).fg.fcRoot
      rw [show (tr.state z c).fg.fcRoot = (tr.state z c).fg.J from
        ite_eq_left ((hframe.kind_iff z hz c hclo hchi).mpr hk),
        show (tr.state y i).fg.fcRoot = (tr.state y i).fg.J from
        ite_eq_left ((hframe.kind_iff y hy i hilo hihi).mpr hk),
        hframe.root_eq z hz c hclo hchi hk, hframe.root_eq y hy i hilo hihi hk]
    rw [hroots]
    exact Anc.mono hPhi.2 (SA.anc_getHead_of_compat hPhi.1 (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi.1 hL).elim
        (fun h => Or.inr h.2.1) Or.inl) (fun _ h => h.1.1)
      _ _ (.refl : ell.frame.Anc ell.frame.fcRoot ell.frame.fcRoot))
  · have hroot : ellz.frame.fcRoot = (tr.state z c).fg.F := by
      rw [Compose.frame_of_projAC hrun hz hcz]
      exact ite_eq_right (fun h => hk ((hframe.kind_iff z hz c hclo hchi).mp h))
    rw [hroot] at haF ⊢
    exact hframe.finalized_anc_head_at_cast hrun hnc hf hz hy hclo hchi hilo hihi hc
      hY hvY haF

/-- Once a concrete lock image is frozen-viable, honest prior-head
dominance needs only receiver-local finality ancestry for transport. No
additional floor witness for that image is required. -/
theorem honest_prefix_of_finality_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hheads : ∀ x ∈ H, ∀ j ev, SA.VoteAt tr.projAC x j ev → ev.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) ev.msg B)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hΔ := sp.toParams.hΔ
  have hslot := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
  rw [hslot] at ht
  have hstart : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time i)
      rw [hslot])
  have hstep : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcarry := SA.honest_batch_carry_before hS hy hc hes hm
    (by
      change sp.ts s + 2 * sp.Δ ≤ tr.time i
      rw [hstep] at hstart
      linarith) (ht.trans hmb)
    (fun k hk t ht => by
      apply deadline_le_restarts (a := sp.ts s)
      intro r _ hrs
      have := hnr y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ _
      linarith)
    (fun k hk hrs => by
      have := hnr y hy k (Compose.projAC_restartAt.mp hrs)
      change tr.time k < _
      linarith) (fun x hx j ev hv hs R hR hRr => by
      obtain ⟨R', hR', hR'r, hBR⟩ := hheads x hx j ev hv hs
      have he : R' = R := hr.coherent.1 hR' hR (hR'r.trans hRr.symm)
      exact (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hB.2.1)).trans (he ▸ hBR))
  have hex : ∀ x ∈ H, ∃ j ev, SA.VoteAt tr.projAC x j ev ∧ ev.msg.slot = s := by
    intro x hx
    obtain ⟨j, ev, hv, hs, -⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
      hcatch hnr hm (by rw [hstep] at hmb; linarith) x hx
    exact ⟨j, ev, hv, hs⟩
  have hf' : 3 * Hᶜ.ncard < sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  exact SA.honest_prefix_of_carry sp hS.run hf' hy hc hes hheads hex hcarry hB haB

/-- Any point between the actual voter anchor and a frozen viable block is
itself frozen-viable. In Step 5 the upper block is P, not a transported
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

/-- A warm actual proposal lock supplies exactly one of the three prefix
mechanisms: the writer root, prior honest heads, or a boundary optimistic CV. -/
theorem FrameWindow.proposal_lock_prefix_cases {s₀ s floor : Nat}
    {contest kindJ : Prop} {J X B : SA.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    {l : SA.Lock}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state z i).locks ell.frame (tr.time i))
    (hwarm : s₀ + sp.k ≤ l.slot) (hpos : 0 < l.slot)
    (hpred : s₀ ≤ l.slot - 1) (hold : l.slot < s + 1)
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l.block) (hXB : ell.frame.Anc X B) :
    Anc (tr.HonestBlocks H) X ell.frame.fcRoot ∨
      (∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X) ∨
      ∃ a < i, ∃ D CV, SA.OptimisticLockAt tr.projAC z a s D CV ∧
        Anc (tr.HonestBlocks H) X D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := SA.frameIn_of_callAt hr hz hc
  have hΔ := sp.toParams.hΔ
  have hi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith
  obtain ⟨a, hai, ellw, D, ha, hD, hBA, ho⟩ :=
    live_lock_selection_origin hrun hnc hz hc hl hB hBr
  let A := ellw.frame.viableAncestor D
  have hXA : Anc (tr.HonestBlocks H) X A := (Anc.mono hPhi.2 hXB).trans hBA
  have hW := SA.frameIn_of_callAt hr hz ha
  have hAD : Anc (tr.HonestBlocks H) A D :=
    Anc.mono hW.2 (SA.viableAncestor_anc hW.1 hD).2
  have hregular (ho : (∃ CV, SA.FastUpdateAt tr.projAC z a l.slot D CV) ∨
      SA.SlowLockAt tr.projAC z a l.slot D) :
      ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
    obtain ⟨ell', hu⟩ : ∃ ell', SA.UpdateAt tr.projAC z a l.slot ell' := by
      rcases ho with ⟨CV, ell', C, hu, -⟩ | ⟨ell', C, hu, -⟩ <;> exact ⟨ell', hu⟩
    have hgap : l.slot + 2 ≤ s + 1 := by
      have ht := hu.2.2.1
      change tr.time a = _ at ht
      have htime := hrun.time_mono hai.le
      rw [hti] at htime
      by_contra hn
      have he : s + 1 = l.slot + 1 := by omega
      rw [he] at htime
      simp only [SAParams.ts] at ht htime
      push_cast at htime
      linarith
    have hall := (hframe.regular_later_heads hrun hnc hsvc hawake hf hcatch hnr
      hwarm hpos hpred hm hgap hmb hz ho s (by omega) (by omega)).1
    intro y hy j e hv hs
    obtain ⟨R, hR, hRr, hDR⟩ := hall y hy j e hv hs
    exact ⟨R, hR, hRr, (hXA.trans hAD).trans hDR⟩
  rcases ho with hfast | hslow | ⟨CV, hop⟩
  · exact Or.inr (Or.inl (hregular (Or.inl hfast)))
  · exact Or.inr (Or.inl (hregular (Or.inr hslow)))
  by_cases hs : l.slot = s
  · exact Or.inr (Or.inr ⟨a, hai, D, CV, hs ▸ hop, hXA.trans hAD⟩)
  have hlabel : s₀ ≤ l.slot := by omega
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hlabel)
  have halo : sp.ts s₀ ≤ tr.time a := by
    obtain ⟨_, _, _, hsl, -⟩ := hop
    exact hts.trans ((SA.ts_le_iff_le_slot sp (hr.time_nonneg a) _).2 (by rw [hsl]))
  rcases (SA.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
  · exact Or.inl (hframe.unlocked_image_below_write_root hrun hnc hz hai.le ha hc
      halo hi hXB hBA hbelow)
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hvQ' := hvQ
  rw [Compose.frame_of_projAC hrun hz ha] at hvQ'
  have hh : floor ≤ ((tr.state z a).fg.σ Q.root).h := by
    rw [← hframe.floor_eq z hz a halo ((hrun.time_mono hai.le).trans hi)]
    exact hvQ'.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocks H) J A := by
    intro hk
    have hkind := (hframe.kind_iff z hz a halo ((hrun.time_mono hai.le).trans hi)).mpr hk
    have hroot := Anc.mono hW.2 hAv.2.1
    change Anc (tr.HonestBlocks H) ellw.frame.fcRoot A at hroot
    rw [Compose.frame_of_projAC hrun hz ha] at hroot
    change Anc (tr.HonestBlocks H) (tr.state z a).fg.fcRoot A at hroot
    rwa [show (tr.state z a).fg.fcRoot = (tr.state z a).fg.J from ite_eq_left hkind,
      hframe.root_eq z hz a halo ((hrun.time_mono hai.le).trans hi) hk] at hroot
  have hsub : FrameWindow (tr := tr) (H := H) (sp.ts l.slot)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J :=
    ⟨fun y hy j hlo hhi => hframe.floor_eq y hy j (hts.trans hlo) hhi,
     fun y hy j hlo hhi => hframe.contest_iff y hy j (hts.trans hlo) hhi,
     fun y hy j hlo hhi => hframe.kind_iff y hy j (hts.trans hlo) hhi,
     fun y hy j hlo hhi => hframe.root_eq y hy j (hts.trans hlo) hhi⟩
  have hall := (optimistic_later_heads_of_witness hrun hnc hsvc hawake hf hcatch hnr
    (by linarith) hmb hsub hz hop hAD ha hQ hh hJ (Anc.mono hW.2 hAQ)
    s (by omega) (by omega)).1
  refine Or.inr (Or.inl ?_)
  intro y hy j e hv hes
  obtain ⟨R, hR, hRr, hAR⟩ := hall y hy j e hv hes
  exact ⟨R, hR, hRr, hXA.trans hAR⟩

/-- The actual proposal start is reached by every shallower voter. The
three origin cases use distinct suppliers; no honest heads above the
proposal parent, settled phase, or head-equality premise is used. -/
theorem FrameWindow.proposal_start_prefix {s₀ s floor : Nat}
    {contest kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hk : 0 < sp.k)
    (hmargin : s₀ + 2 * sp.k ≤ s + 1)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1)) {ip : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (hvP : P ∈ ell.frame.viableHeads)
    (haS : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) d.start) :
    ell.frame.Anc d.start (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  have hΔ := sp.toParams.hΔ
  have hf' : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨hst, _, hw⟩ := proposal_walk_end hrun hnc hz hcp hpay
  have hSQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hSQ he).2
  have hSP : Anc (tr.HonestBlocks H) d.start P :=
    (Anc.mono hPhip.2 hSQ).tail ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hPv' := hPv
  rw [← hes] at hPv'
  have hSv := frozen_viable_of_anchor_path hrun hnc hy hc hPv'
    (Anc.mono hPhi.2 haS) hSP
  rw [hes] at hSv
  have hslot := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have hlo : sp.ts s₀ ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      change (s₀ : Int) ≤ sp.slot (tr.time i)
      rw [hslot]; omega)
  have hhi := SA.vote_time_le hr hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
  rw [hslot] at hhi
  have hplo : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by omega)
  have hphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith
  have hroot (hSr : Anc (tr.HonestBlocks H) d.start ellp.frame.fcRoot) := by
    have hrootE := hframe.fcRoot_anc_head_at_cast hrun hnc hf' hz hy hplo hphi hlo hhi
      hcp hc (hes ▸ hPv.1) hvP ((Anc.mono hPhi.2 haS).trans hSr)
    have hSE := hSr.trans hrootE
    rw [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hSE
    exact SA.anc_tree_of_anc_U hr.coherent hPhi.1 hPhi.2 hSv.1.1 hSE
      (SA.getHead_mem hPhi.1 (fun X hX => hX.1.1) _ _ _ _)
  rcases actual_proposal_start_live_origin hrun hnc hf (by omega)
    (by omega : s₀ + sp.k ≤ s + 1) (hdesignated ▸ hz)
    (hdesignated ▸ hcp) hcall hti (hdesignated ▸ hpay) with he | ⟨l, hl, _, hold, B, hB, hBr, hSB⟩
  · exact hroot (he ▸ .refl)
  have hlive : s + 1 ≤ l.slot + sp.k := by
    obtain ⟨l₀, _, E, _, _, hlive, heq⟩ := hl
    have hs : l.slot = l₀.slot := by rw [heq]
    have hsl : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
    rw [hsl, ← hs] at hlive
    exact hlive
  rcases hframe.proposal_lock_prefix_cases hrun hnc hsvc hawake hf hcatch hnr hm hmb hz
    hcp hti (hdesignated.symm ▸ hl) (by omega) (by omega) (by omega) hold hB hBr hSB with
    hbelow | hheads | ⟨a, _, D, CV, hop, hSD⟩
  · exact hroot hbelow
  · exact honest_prefix_of_finality_before hrun hnc hsvc hawake hf hcatch hnr
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
        linarith) hmb hheads hy hc hes hSv haS
  · have hFD : Anc (tr.HonestBlocks H) ell.frame.F D :=
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hSv.2.1)).trans hSD
    exact optimistic_prefix_before hrun hnc hsvc hawake hf hcatch
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
        linarith) hz hy hop hSD hc hes (hhi.trans hmb) hFD hSv haS

/-- Finite Step 5/6: every honest vote of the warm honest proposal's slot
has exactly its root. Current-slot optimistic residues use only strictly
earlier actual casts in the global-cut induction. -/
theorem FrameWindow.honest_vote_heads_eq {s₀ s floor : Nat}
    {contest kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hk : 0 < sp.k)
    (hmargin : s₀ + 2 * sp.k ≤ s + 1)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1)) {k : Nat}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      e.msg.head = P.root := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hf' : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn : 0 < sp.n := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hsp : s₀ ≤ s + 1 := by omega
  have hms : gbar g + 2 * sp.Δ ≤ sp.ts s := by
    have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
    linarith
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hpay, hti, hparent, _, hp, hpayload, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  have hpH : P.proposer ∈ H := hp ▸ (hdesignated ▸ hz)
  rw [← hdesignated] at hcp hpay
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → e.msg.head = P.root by
    exact fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e hv hes
    obtain ⟨ell, hc, he⟩ := hv
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hhigh := SA.vote_time_le hr hy ⟨ell, hcast⟩
    have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hes
    change sp.slot (tr.time i) = s + 1 at hslot
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhigh
    rw [hslot] at hhigh
    obtain ⟨hvP, hPv⟩ := hframe.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr
      (by linarith) hsp (by omega) hmb hz hdesignated hactual hPs hy hcast hes
    have haP := hframe.vote_anchor_below_of_earlier_heads hrun hnc hsvc hawake hf hcatch
      hnr hm hsp (by omega) hmb hz hdesignated hactual hPs hy hcast hes hmargin
      (fun x hx j hji ev hv hs => ih j hji x hx ev hv hs)
    apply hframe.vote_head_eq_of_start_prefix hrun hnc hS hnr hf' hms hsp hz hdesignated
      hactual hPs hpH hcp hcall hti hpay hpayload hparent hy hcast hes hhigh
      (hhigh.trans hmb) hPv haP
    exact fun haS => hframe.proposal_start_prefix hrun hnc hsvc hawake hf hcatch hnr
      hm hk hmargin hmb hz hdesignated hcp hcall hti hpay hparent hy hcast hes hPv hvP haS

/-- Finite L1.5(ii): iterate U through the last used vote slot. The source
floor and kind-J ancestry are explicit, with no whole-run frame premise. -/
theorem FrameWindow.vote_extends_through {u last floor : Nat}
    {contest kindJ : Prop} {J X : SA.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts u) (sp.ts last + sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts u) (hmb : sp.ts last + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hbase : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X)
    {m : Nat} (hum : u ≤ m) (hml : m ≤ last) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  induction m, hum using Nat.le_induction with
  | base => exact hbase
  | succ m hum ih =>
    have ht : sp.ts u ≤ sp.ts m := (SA.ts_le_iff sp).2 (by omega)
    have ht' : sp.ts (m + 1 : Nat) ≤ sp.ts last := (SA.ts_le_iff sp).2 (by omega)
    have hsub : FrameWindow (tr := tr) (H := H) (sp.ts m)
        (sp.ts (m + 1 : Nat) + sp.Δ) floor contest kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i (ht.trans hlo) (by linarith),
        fun y hy i hlo hhi => hframe.contest_iff y hy i (ht.trans hlo) (by linarith),
        fun y hy i hlo hhi => hframe.kind_iff y hy i (ht.trans hlo) (by linarith),
        fun y hy i hlo hhi hk => hframe.root_eq y hy i (ht.trans hlo) (by linarith) hk⟩
    exact unanimous_next_votes hrun hnc hsvc hawake hf hcatch hnr (by linarith)
      (by linarith) hsub hz hX hh hJ (ih (by omega))

end Consensus.Goldilocks.Healing

end
