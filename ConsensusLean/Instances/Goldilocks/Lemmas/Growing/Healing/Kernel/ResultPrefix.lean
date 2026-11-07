module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResultSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finite latest-result induction under growing faults

`late_result_prefix_votes_before_at`: every cast at a time `≤ b`, by a node honest at its cut,
of a slot after the label `s` of a result of a writer honest at its update, extends a block `B`
below the result, given the domain and stored-lock inputs. The induction is on the cast's cut;
every writer, cast and vote is read at its own cut, and ancestry is in the blocks held while
honest. The first label `s + 1` transfers the result (its counted votes carried from the writer,
honest at its update, to the voter, honest at its cast); a later label transfers the earlier
votes of nodes honest at them, all extending `B` by induction, counted at the voter's cut.

The node-local facts of the cast are read on the prefix through the cast's time. The results of
other layers are stated here under their names with the suffix `_stub`: with the shapes of their
owners (the growing AC projection, the growing next transfer), or as the growing forms of the
static facts the static proof uses. Each is an open `sorry`. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-! ### Stand-ins -/

/-- The growing AC projection (`Compose.Growing.goldilocks_ac_projection`); stand-in. -/
theorem goldilocks_ac_projection_stub : Compose.Growing.GoldilocksACProjection := by
  sorry

/-- The growing next transfer (`SA.Growing.next_transfer`); stand-in. -/
theorem next_transfer_stub (sp : SAParams) : SA.Growing.NextTransfer sp := by
  sorry

/-- The first transfer of a result into a block below it, with the live locks from the stored
locks (the growing form of `SA.result_prefix_vote_extends_of_stored`): the writer honest at its
update, the voter at its cast, `2 f < n` at the voter's cut; stand-in. -/
theorem result_prefix_vote_extends_of_stored_stub {FGP : Type} {ro : ReplayOrder sp FGP}
    {tr : SA.SATrace sp FGP ro} {U : Set (SA.Blk sp.n FGP)}
    (hrun : SA.Growing.ACRun proposer tr H U) {x y : Fin sp.n} {r s i : Nat}
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr x r s C CV) (hBC : Anc U B C)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : SA.CarryAt tr U y i e s CV) (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    (hstored : ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y B)
    (hE : SA.EarlierVotesExtendAt tr H U i (s + 1) B)
    (hmerged : ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state x r).pool s ∨ v.val ∈ SA.equivocators {w | w ∈ (tr.state x r).pool s}) :
    SA.VoteExtends U e.msg B := by
  sorry

/-- The counted votes of a result after the reset's catch-up reach a next-label cast (the growing
form of the static writer-window carry under the reset service): the writer honest at its
update, the voter at its cast; stand-in. -/
theorem result_carry_reset_stub (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hres : SA.ResultAt tr.projAC x r s C CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hcast : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hFC : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  sorry

/-- The next-label voter's merged view of label `s` is in the writer's pool or names an
equivocator of it (the growing form of the static writer-window merge under the reset service);
stand-in. -/
theorem writer_merged_reset_stub (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hx : x ∈ H (tr.time r)) (hres : SA.ResultAt tr.projAC x r s C CV) (hrb : tr.time r ≤ b)
    (hts : cutZ sp.toParams g ≤ sp.ts s) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hcast : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state x r).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state x r).pool s} := by
  sorry

/-- The label-`m` votes of nodes honest at them, all extending `B`, reach a label-`(m+1)` cast
above `B` after the reset's catch-up (the growing form of the static per-vote writer-window
carry); stand-in. -/
theorem honest_votes_carry_reset_stub (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {y : Fin sp.n} {i m : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hcast : SA.CastAt tr.projAC y i ℓ e) (hm : e.msg.slot = m + 1)
    (hib : tr.time i ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts m)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ z q e', z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e' → e'.msg.slot = m →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e m
      {v | ∃ z q e', z ∈ H (tr.time q) ∧ SA.VoteAt tr.projAC z q e' ∧ e'.msg = v ∧
        v.slot = m} := by
  sorry

/-! ### The cast's node-local facts -/

/-- A cast of a node honest at its cut, read on the prefix through its time: its frame is held
while honest, its head is in the frame above `fc_root` by the slot's `Δ`, and its slot is the
cut's. -/
private theorem cast_facts (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ℓ e) :
    (FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H) ∧
      ((∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
        tr.time i ≤ sp.ts e.msg.slot + sp.Δ) ∧
      e.msg.slot = sp.slot (tr.time i) := by
  have hd := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo hd) (hnc.upTo _)).localRun
  have hcT : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e := by
    rw [RunTrace.upTo_projAC]
    exact ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hcast.1⟩, hcast.2⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcT.1
  exact ⟨⟨hΦ, hΦU.trans (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)⟩,
    Compose.cast_head_fcRoot hr hy hcT, (SA.castAt_spec hr hy hcT).2.1⟩

/-! ### The induction -/

/-- **The finite latest-result induction**, the kernel skeleton's
`ResetPremisesUpTo.late_result_prefix_votes_before_at` with the same statement: by strong
induction on the cast's cut. -/
theorem late_result_prefix_votes_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      SA.CastAt tr.projAC y i ell e → s < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hrun' := goldilocks_ac_projection_stub sp ro dg H tr proposer hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hib y hy ell e hcast hsi
  have hprior : ∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
    intro z q e' hqi hv hse
    obtain ⟨hz, ell', hc'⟩ := Compose.Growing.hVoteAt_iff.1 hv
    exact ih q hqi ((hrun.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
  have hd := hrun.time_nonneg i
  obtain ⟨⟨hΦ, hΦU⟩, hhead, hsl⟩ := cast_facts hrun hnc hy hcast
  rcases hdomain y i ell e hy hcast hib hsi hprior with hBF | hv
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := hhead
    exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
  have hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B := (hΦ.rooted.2 B hv.1.1).mono hΦU
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have h3 := hp.faults (tr.time i) hd hib
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  by_cases hfirst : e.msg.slot = s + 1
  · exact result_prefix_vote_extends_of_stored_stub hrun' hf hx hy hres hBC hcast hfirst
      (result_carry_reset_stub hp hc hx hres hts hy hcast hfirst hib (hFB.trans hBC))
      (by rw [← hfirst]; exact Or.inl hv)
      (hstored y i ell e hy hcast hib hfirst)
      (fun z q hq hz e' he hslot => hprior z q e' hq
        (Compose.Growing.hVoteAt_iff.2 ⟨hz, he⟩) (by omega))
      (writer_merged_reset_stub hp hx hres hrb hts hy hcast hfirst)
  · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm : s < m := by omega
    have htime : sp.ts (m + 1 : Nat) ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp hd _).mpr (by rw [← hsl, hm])
    have hts1 : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hmts : cutZ sp.toParams g ≤ sp.ts m :=
      hts.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))
    -- a label-`m` vote of a node honest at it is at an earlier cut
    have hall : ∀ z q e', z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e' → e'.msg.slot = m →
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B := by
      rintro z q e' hz ⟨ell', hc'⟩ hslot
      have hqi : q < i := by
        by_contra hn
        have hq := (cast_facts hrun hnc hz hc').2.2
        have := SA.slot_mono sp hd (hrun.time_mono (Nat.le_of_not_gt hn))
        omega
      exact hprior z q e' hqi (Compose.Growing.hVoteAt_iff.2 ⟨hz, ell', hc'⟩) (by omega)
    exact next_transfer_stub sp _ ro H _ tr.projAC proposer hrun' m y i B ell e hy hcast hm hall
      (hp.half_committee_at hmts (t := tr.time i) (by linarith only [htime, hts1, hΔ]) hib)
      (honest_votes_carry_reset_stub hp hc hy hcast hm hib hmts hall hFB)
      (fault_bound_late_at hp (t := tr.time i)
        (hmts.trans (by linarith only [htime, hts1, hΔ])) hib)
      (by rw [← hm]; exact Or.inl hv)
      (fun z q hq hz e' he hslot => hprior z q e' hq
        (Compose.Growing.hVoteAt_iff.2 ⟨hz, he⟩) (by omega))

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
