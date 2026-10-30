module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore

public section

/-! # Goldilocks Persist, part 2: the vote step of C1.1

At an honest vote of a slot `σ ∈ (s, m]` (a cut of the run's AC projection), with the caches of
the voter compatible with `B`: (i) `B` is in the viable voter block tree or at or below `fc_root`
(`vote_viable`: the voter's `fc_root` is its `Σ.J` or `Σ.F`, then (K2)), and (ii) the vote
extends `B` (`vote_extends`: below `fc_root` by requirement 1, otherwise by A1.2 for
`σ = s + 1` and A1.3 after). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

/-! ### Honest votes on an AC trace of the SA -/

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- Every emission of a call has a duty head whose root is the vote's head, and is cast no later
than `Δ` after the start of the call's slot. -/
private def EmitsHeads (t : Time) (r : SA.SAState sp.n × List (SA.Em sp FGP)) : Prop :=
  ∀ e ∈ r.2, (∃ d, e.head = some d ∧ d.head.root = e.msg.head) ∧ t ≤ sp.ts (sp.slot t) + sp.Δ

private theorem tryVote_emitsHeads (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : EmitsHeads t (SA.tryVote sp x A Φ t) := by
  unfold SA.tryVote
  dsimp only
  split_ifs with h1
  · simp [EmitsHeads]
  · simp [EmitsHeads]
  all_goals
    simp only [EmitsHeads, List.mem_singleton, forall_eq]
    exact ⟨⟨_, rfl, rfl⟩, not_lt.1 (not_or.1 (not_or.1 h1).2).2⟩

private theorem step_emitsHeads (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SA.SAState sp.n)
    {Φ : SA.Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    EmitsHeads t ((goldilocksSA sp FGP ro).step self A Φ t c) := by
  cases c with
  | tick =>
    change EmitsHeads t (SA.acOnTick sp self A Φ t)
    unfold SA.acOnTick
    dsimp only
    split_ifs
    all_goals first
      | exact fun e he => tryVote_emitsHeads self A Φ t e he
      | simp [EmitsHeads]
  | message m => exact tryVote_emitsHeads self _ Φ t
  | block B => exact tryVote_emitsHeads self _ Φ t
  | proposal => simp [EmitsHeads, ACInterface.step]
  | toFG => simp [EmitsHeads, ACInterface.step]
  | restart =>
    intro e he
    change e ∈ (SA.acRestart sp ro self A Φ t).2 at he
    rw [(SA.restart_state sp FGP ro self A Φ t hΦ ht).1] at he
    simp at he

variable {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}

/-- The state before an honest call is reachable, with a frame and time from which the call is
lawful. -/
theorem pre_reachable (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hcall : tr.CallAt y i ℓ) :
    ∃ Φp tp, (goldilocksSA sp FGP ro).ReachableAt y U (tr.state y i) Φp tp ∧ tp ≤ tr.time i ∧
      (goldilocksSA sp FGP ro).CallOK U Φp (tr.time i) ℓ.call ℓ.frame := by
  rcases hr.frameLaw y hy i ℓ hcall with ⟨hn, Φ₀, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
  · refine ⟨Φ₀, 0, ?_, hr.time_nonneg i, hok⟩
    rw [tr.state_of_noCall hn, hr.init y hy]
    exact .init Φ₀ hi hf
  · refine ⟨ℓ'.frame, tr.time j, ?_, hr.time_mono hj.le, hok⟩
    rw [tr.state_of_lastCall hc' hj hnb]
    exact localRun_reachable _ _ _ _ _ tr hr y hy j ℓ' hc'

/-- **An honest vote's head extends `fc_root`** (requirement 1, A0.6), and the vote is cast no
later than `Δ` after the start of its slot. -/
theorem cast_head_fcRoot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ := by
  have hU := hr.coherent
  obtain ⟨hcall, he⟩ := hc
  have hx := hr.exec i ℓ hcall.2 (hcall.1 ▸ hy)
  rw [hcall.1] at hx
  obtain ⟨Φp, tp, hreach, htp, hok⟩ := pre_reachable hr hy hcall
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).2 := by
    rw [hx]; exact he
  obtain ⟨⟨d, hd, hdr⟩, hle⟩ :=
    step_emitsHeads ro y (tr.state y i) hok.1.1 (hr.time_nonneg i) ℓ.call e he'
  have hok' := (((SA.interface_requirements sp FGP ro).1 y U hU _ _ _ hreach).2.2
    (tr.time i) ℓ.call ℓ.frame htp hok e he' d hd).1
  have hs := (SA.castAt_spec hr hy ⟨hcall, he⟩).2.1
  refine ⟨⟨d.head, ?_, hdr, hok'⟩, hs ▸ hle⟩
  by_cases hne : ℓ.frame.fcRoot = d.head
  · exact hne ▸ hok.1.1.fcRoot_mem
  · exact (Anc.mem hok' hne).2

end SA

/-! ### Honest votes in a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)}

/-- The frame of an honest AC cut of a run is `fg_to_ac(Σ)` of the node's state. -/
theorem frame_of_projAC {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame = Node.frame (tr.state y k) :=
  (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).1

/-- `Sync` on a window gives it on every subwindow. -/
theorem syncAC_mono {P : Params} {FGP : Type} {A : ACInterface P FGP} {H : Set (Fin P.n)}
    {U : Set A.Blk} {a b a' b' : Time} {tr : ACTrace A} (h : SyncAC A H U a b tr) (ha : a ≤ a')
    (hb : b' ≤ b) : SyncAC A H U a' b' tr :=
  ⟨fun x hx i m hs h₁ h₂ => h.1 x hx i m hs (ha.trans h₁) (h₂.trans hb),
    fun x hx i B hB h₁ h₂ => h.2 x hx i B hB (ha.trans h₁) (h₂.trans hb)⟩

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- **C1.1 (i) at a vote**: when the voter's caches are compatible with `B` and (K2) holds at the
vote, `B` is in the viable voter block tree or at or below `fc_root` (in the honest blocks). -/
theorem vote_viable (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcache : Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hfr := frame_of_projAC hrun hy hc.1
  have hcomp : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y k).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hcache.2
    · exact hcache.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      refine Or.inl ⟨SA.voterBlockTree_anc hr hy hc D hD B hΦBD, hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- **C1.1 (ii) at a vote**: when (i) holds at an honest vote of a slot `σ ∈ (s, m]` and every
honest vote of a slot in `(s, m]` at an earlier cut extends `B`, the vote extends `B`: below
`fc_root` by requirement 1, otherwise by A1.2 for `σ = s + 1` (its stored-block form, #75) and by
A1.3 after (every slot-`(σ − 1)` vote is at an earlier cut). -/
theorem vote_extends (hrun : GoldilocksRun dg H tr) {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hs : s < e.msg.slot) (hsm : e.msg.slot ≤ m)
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ j < k, ∀ e', SA.VoteAt tr.projAC z j e' → s < e'.msg.slot →
      e'.msg.slot ≤ m → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hp.noColl
  have hr := hrun'.localRun
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := cast_head_fcRoot hr hy hc
  obtain ⟨-, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  rcases hviab with hv | hBf
  swap
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  have hspec := SA.castAt_spec hr hy hc
  have h0 := hr.time_nonneg k
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp h0 _).mpr (by rw [hspec.2.1])
  have htm : tr.time k ≤ sp.ts m + sp.Δ := by
    have := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm)
    have hle' : tr.time k ≤ sp.ts e.msg.slot + sp.Δ := hle
    linarith
  have hsk : sp.ts s < tr.time k := by
    have := (SA.ts_lt_iff sp).mpr (Int.ofNat_lt.mpr hs)
    linarith
  have hsync0 := sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr ΔF
    (sp.ts s) (sp.ts m + sp.Δ) hrun.toLocalRun hp.sync
  have hfault : SA.FaultBound tr.projAC H (tr.time k) := by
    have h := hp.faultBound y hy k e ⟨ℓ, hc.1, hc.2⟩ hsk htm
    unfold SA.FaultBound
    rw [← (joined_projection sp ro dg H tr hrun y hy (tr.time k)).2.2]
    exact h
  have hearlier : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k e.msg.slot B :=
    fun z hz j hj e' hv hsl => hprior z hz j hj e' hv (hsl ▸ hs) (hsl ▸ hsm)
  by_cases h1 : e.msg.slot = s + 1
  · obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hp.fastLock
    have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x hp.writer_honest i₀ ℓw hcw with
        ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
    refine SA.first_transfer_stored sp hrun' hp.writer_honest hflD
      (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hy hc h1
      (syncAC_mono hsync0 le_rfl htm) (hp.carry y hy k e ⟨ℓ, hc.1, hc.2⟩ h1) hfault ?_ ?_
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : s < m' := by omega
    refine SA.next_transfer sp _ ro H _ tr.projAC hrun' m' y k B ℓ e hy hc hm' ?_
      (hp.halfCommittee m' hsm' (by omega))
      (hp.carryLater m' hsm' (by omega) y hy k e ⟨ℓ, hc.1, hc.2⟩ hm') hfault
      (syncAC_mono hsync0 ((SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm'.le)) htm) ?_ ?_
    · intro z hz j e' hv hsl
      have hjk : j < k := by
        by_contra hjk
        obtain ⟨ℓ', hc', he'⟩ := hv
        have h₁ := (SA.castAt_spec hr hz ⟨hc', he'⟩).2.1
        have h₂ := SA.slot_mono sp h0 (hr.time_mono (not_lt.mp hjk))
        omega
      exact hprior z hz j hjk e' hv (by omega) (by omega)
    · rw [← hm']; exact Or.inl hv
    · rw [← hm']; exact hearlier

end Consensus.Goldilocks.Compose

end
