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

end Consensus.Goldilocks.Healing

end
