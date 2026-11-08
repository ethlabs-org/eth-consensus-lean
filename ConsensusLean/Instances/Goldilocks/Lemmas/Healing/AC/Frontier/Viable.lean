module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The pre-`b` frontier over AC traces: viability at votes under trivial frames

The composite frontier proves that a block an honest slot-`s` vote extends is viable at an
honest slot-`(s+1)` vote by the FG geometry of the voter's store (`Compose.vote_frame_before`:
`Σ.J`, the floor crossing, the frozen witness). Under trivial frames that geometry is trivial
(`Φ.F = fc_root` is genesis, every block of the tree is a viable head), and viability is the
acceptance of the block before the vote freeze `t_s + 3Δ`:

* `viable_of_acceptedAC`: a block of `U` that is genesis, or that the voter accepted before the
  freeze, is in the viable tree of its voter block tree, or is `fc_root`
  (after `SA.viable_of_acceptedU`, with the voter's restarts at or before `t_s` from its joined
  vote instead of `Healthy(g)`);
* `trivial_viableAC`: a block extended by an honest slot-`s` vote is viable at every honest
  slot-`(s+1)` vote at a time `≤ b` (after `SA.trivial_viableU`): the slot-`s` voter accepted it
  by `t_s + Δ`, and the deadline-cut relay delivers it to the next voter before `t_s + 2Δ`. -/

namespace Consensus.Goldilocks.SA


variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {b : Time}

/-- Under trivial frames the frames of honest calls share `Φ.F`, genesis. -/
theorem trivial_F_eqAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat}
    {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) (hc' : tr.CallAt z j ℓ') :
    ℓ.frame.F = ℓ'.frame.F := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  obtain ⟨hΦ', hΦU'⟩ := frameIn_of_callAtU hr hz hc'
  exact hr.coherent.1 (hΦU hΦ.rooted.1) (hΦU' hΦ'.rooted.1)
    ((htriv y hy i ℓ hc).1.trans (htriv z hz j ℓ' hc').1.symm)

/-- **Viability at a vote from acceptance before the freeze** (under trivial frames): a block of
`U` that is genesis, or that an honest voter of slot `σ + 1` accepted before the vote freeze
`t_σ + 3Δ`, is in the viable tree of its voter block tree (or is `fc_root`). -/
theorem viable_of_acceptedAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {σ : Nat} (hes : e.msg.slot = σ + 1) {B : Blk sp.n FGP}
    (hBU : B ∈ U) (hB : AcceptedBefore tr y B (sp.ts σ + 3 * sp.Δ)) :
    ViableAtVote ℓ e (σ + 1) B := by
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc.1
  obtain ⟨hFy, hfcy, hvhy, htreey⟩ := htriv y hy i ℓ hc.1
  obtain ⟨hrsy, hti⟩ := vote_restartsAC hr hy hc hes
  have hσ1 : ((σ + 1 : Nat) : Int) - 1 = σ := by push_cast; ring
  rcases hB with hg | ⟨k', hacc', hlt⟩
  · right
    rw [hU.1 hBU (hΦU hΦ.rooted.1) (hg.trans hFy.symm), hfcy]
    exact Relation.ReflTransGen.refl
  have hk'i : k' ≤ i := by
    by_contra h
    have := hr.time_mono (le_of_lt (not_le.1 h))
    linarith only [hΔ, hti, hlt, this]
  have hBy : B ∈ ℓ.frame.tree := by
    rw [htreey]; exact Set.mem_insert_of_mem _ ⟨k', hk'i, hacc'⟩
  have hst := blockStamp_lt_of_acceptedBeforeU sp hr hy hc.1 hBy (Or.inr ⟨k', hacc', hlt⟩)
    (fun k'' hk'' hr'' => lt_of_le_of_lt (hrsy k'' hk'' hr'') (by linarith only [hΔ]))
    (Or.inl (by linarith only [hΔ, hti]))
  have hrp : e.readPoint.blockStamp B.root = (tr.state y i).blockStamp B.root := by
    have h1 : (tr.post i).blockStamp = e.readPoint.blockStamp := by
      rw [post_of_castAtU hr hy hc, optimisticConfirmationM_keep _ SA.optimistic_blockStamp,
        SA.admitVote_blockStamp]
    rw [← h1]
    have he := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
    rw [hc.1.1] at he
    have hpost : tr.post i =
        (stepWithM sp ro wm y (u i) (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [he]
    obtain ⟨hblk, -, hoth⟩ := stepWith_blockStamp_eq (wm := wm) ro y (u i) (tr.state y i) hΦ
      (hr.time_nonneg i) ℓ.call
    rw [hpost]
    by_cases hb : ∃ B', ℓ.call = .block B'
    · obtain ⟨B', hB'⟩ := hb
      rw [hblk B' hB', Function.update_apply]
      split_ifs with hr'
      swap
      · rfl
      exfalso
      have hB'U : B' ∈ U := hΦU ((accept_newU sp hr hy ⟨ℓ, hc.1, hB'⟩).1 ℓ hc.1)
      have := hU.1 (hΦU hBy) hB'U hr'
      subst this
      have := accept_uniqueU sp hr hy hacc' ⟨ℓ, hc.1, hB'⟩
      subst this
      linarith only [hΔ, hlt, hti]
    · simp only [not_exists] at hb
      rw [hoth hb fun hrs => by
        have := hrsy i le_rfl ⟨ℓ, hc.1, hrs⟩
        linarith only [hΔ, hti, this]]
  have hvbt : B ∈ voterBlockTree sp e.readPoint ℓ.frame (σ + 1) := by
    refine ⟨hBy, Or.inl ?_⟩
    rw [hrp, freeze, hσ1]
    exact hst
  left
  refine ⟨hvbt, ?_, B, hvbt, by rw [hvhy]; exact hBy, Relation.ReflTransGen.refl⟩
  rw [hfcy]
  exact hΦ.rooted.2 B hBy

/-- **Viability under trivial frames** at an honest slot-`(σ+1)` vote at a time `≤ b`: a block
`B` extended by an honest vote of slot `σ` is in the viable voter block tree of the vote, or is
genesis (`Φ.fc_root`): the slot-`σ` voter accepted it by its vote, at or before `t_σ + Δ`, and the
relay of `SyncUntilAC` (the receiver's deadline at most `t_σ + 2Δ ≤ b`) delivers it before the
freeze `t_σ + 3Δ`. -/
theorem trivial_viableAC (hr : ACLocalRunU wm u H U tr) (htriv : TrivialFrames tr H)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    (hes : e.msg.slot = σ + 1) (hib : tr.time i ≤ b) {B : Blk sp.n FGP}
    (hB : ∃ z ∈ H, ∃ j e', VoteAt tr z j e' ∧ e'.msg.slot = σ ∧ VoteExtends U e'.msg B) :
    ViableAtVote ℓ e (σ + 1) B := by
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨z, hz, j, e', ⟨ℓz, hcz, hez⟩, hs', Hd, hHdU, hHdr, hBHd⟩ := hB
  obtain ⟨hΦz, hΦzU⟩ := frameIn_of_callAtU hr hz hcz
  obtain ⟨-, -, -, htreez⟩ := htriv z hz j ℓz hcz
  obtain ⟨-, hfcy, -, -⟩ := htriv y hy i ℓ hc.1
  have hFF := trivial_F_eqAC hr htriv hz hy hcz hc.1
  obtain ⟨hrsy, hti⟩ := vote_restartsAC hr hy hc hes
  obtain ⟨-, hslz, -, hhead⟩ := castAt_specU hr hz ⟨hcz, hez⟩
  have hHdt : Hd ∈ ℓz.frame.tree := by
    have hm := getHead_mem hΦz (fun _ hX => (voteDomain_subset_tree hX.1)) e'.readPoint
      (tr.time j) (mergedVoteView sp e'.readPoint ℓz.frame e'.msg.slot)
      ((e'.msg.slot : Int) - 1)
      (T := ℓz.frame.viableTree (voteDomain sp e'.readPoint ℓz.frame e'.msg.slot))
    rwa [hU.1 hHdU (hΦzU hm) (hHdr.trans hhead)]
  have hgen : ∀ X, Anc U X ℓz.frame.F → X = ℓz.frame.F := by
    intro X hX
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hz j ℓz hcz
    have hFG : ℓz.frame.F = G :=
      hU.1 (hΦzU hΦz.rooted.1) hGU ((htriv z hz j ℓz hcz).1.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with h | ⟨c, -, hp⟩
    · exact h.symm
    · have := hp.2.2
      rw [hFG, hGp] at this
      exact absurd this (by simp)
  have hcase : B = ℓz.frame.F ∨ ∃ k ≤ j, tr.AcceptAt z k B := by
    rcases anc_total hU hBHd ((hΦz.rooted.2 Hd hHdt).mono hΦzU) with h | h
    · exact Or.inl (hgen B h)
    · have hBz := frame_mem_of_between sp hU hΦz hΦzU hHdt hBHd h
      rw [htreez] at hBz
      rcases hBz with h | h
      · exact Or.inl h
      · exact Or.inr h
  rcases hcase with hBF | ⟨k, hkj, hacc⟩
  · right
    rw [hBF, hFF, hfcy]
    exact Relation.ReflTransGen.refl
  have htk : tr.time k ≤ sp.ts σ + sp.Δ := by
    have := vote_time_leU hr hz ⟨ℓz, hcz, hez⟩
    rw [← hslz, hs'] at this
    exact (hr.time_mono hkj).trans this
  have hBz : B ∈ ℓz.frame.tree := by
    rw [htreez]; exact Set.mem_insert_of_mem _ ⟨k, hkj, hacc⟩
  have hF : Anc U ℓ.frame.F B := by
    rw [← hFF]
    exact (hΦz.rooted.2 B hBz).mono hΦzU
  have hdl : ∀ c ≤ i, tr.deadline y c (tr.time k) ≤ sp.ts σ + 2 * sp.Δ := by
    intro c hc'
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hc') hr') (tr.time k)
    have h₂ := max_le htk (show sp.ts σ ≤ sp.ts σ + sp.Δ by linarith only [hΔ])
    change tr.deadline y c (tr.time k) ≤ max (tr.time k) (sp.ts σ) + sp.Δ at h₁
    linarith only [h₁, h₂]
  obtain ⟨k', hk'i, hacc', hlt⟩ := hsy.relay z hz k B hacc y hy i ℓ hc.1
    (by linarith only [hdl i le_rfl, hti, hΔ]) (by linarith only [hdl i le_rfl, hti, hib, hΔ]) hF
  exact viable_of_acceptedAC hr htriv hy hc hes (hΦzU hBz)
    (Or.inr ⟨k', hacc', by linarith only [hdl k' hk'i, hlt, hΔ]⟩)

end Consensus.Goldilocks.SA

end
