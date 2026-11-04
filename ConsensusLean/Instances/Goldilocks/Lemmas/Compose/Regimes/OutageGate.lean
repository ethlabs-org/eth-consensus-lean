module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageMajority
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

public section

/-! # Goldilocks outage: the reader's gate count and read majority (O4 L1, L-gate, L3)

Workbench `notes/outage/outage_reader_bridge.md` §10.1 (rev 5). Under receiver-scoped service
after GST (`ReceiverServiceAfter`, O4 cut 2):

* `vote_held_before_early` (L1): an honest slot-`q` vote whose head extends the receiver's `Σ.F`
  is pooled, its head is framed, and the vote is resolved before `t_q + 2Δ`, at every receiver
  call from `t_q + 2Δ` without a restart after `t_q`. Cut 3's D3 with the voter's head facts
  (`honest_head_frame`, `frame_anc_accepted`);
* `gate_result_extends` (L-gate): at a joined honest update of a label from GST, with its frame
  below `B` and an extending majority for `B`, the update returns a result, and every result
  extends `B`;
* `read_majority_of_extending` (L3): the latest view's voters are fewer than twice the supporters
  of `B` when the extending casters of its label outnumber the opponents and are delivered.

The head facts are read by statement only (`honest_head_frame`, `honest_head`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A block between `Σ.F` and a block of a well-formed frame is in the frame. -/
private theorem mem_tree_between {n : Nat} {FGP : Type} {U : Set (SA.Blk n FGP)}
    (hU : Coherent U) {Φ : SA.Frm n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {B C : SA.Blk n FGP} (hFB : Anc U Φ.F B) (h : Anc U B C) : C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      obtain rfl := Anc.antisymm hU hFB (hBc.tail e)
      exact hΦ.rooted.1
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact ih hp.1

/-- **L1.** An honest slot-`q` vote whose head extends the receiver's `Σ.F` is held, its head
framed, and resolved strictly before `t_q + 2Δ` at every receiver call from `t_q + 2Δ` with no
restart after `t_q`. -/
theorem vote_held_before_early (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H)
    (hS : ReceiverServiceAfter H (tr.HonestBlocks H) g y tr.projAC)
    {q c : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x i e) (hes : e.msg.slot = q)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocks H)
    (hHdr : Hd.root = e.msg.head) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F Hd) :
    e.msg ∈ (tr.projAC.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      SA.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
        SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  obtain ⟨ℓv, hcv, hev⟩ := hv
  obtain ⟨Hd₀, hHd₀, hHd₀r, hHd₀s⟩ := SA.honest_head_frame hr hx ⟨hcv, hev⟩
  obtain ⟨-, hΦvU⟩ := SA.frameIn_of_callAt hr hx hcv
  obtain rfl : Hd₀ = Hd := hr.coherent.1 (hΦvU hHd₀) hHd (hHd₀r.trans hHdr.symm)
  have hsig := SA.vote_signer_slot hr hx ⟨ℓv, hcv, hev⟩
  have htj : tr.time i ≤ sp.ts q + sp.Δ := by
    have h := SA.vote_time_le hr hx ⟨ℓv, hcv, hev⟩
    rw [← hsig.2, hes] at h
    exact h
  have hacc : Hd₀.root = sp.genesisRoot ∨
      ∃ k, tr.projAC.AcceptAt x k Hd₀ ∧ tr.time k ≤ sp.ts q + sp.Δ := by
    rcases frame_anc_accepted hr hx i ℓv hcv Hd₀ hHd₀ Hd₀ .refl with hgen | ⟨k, hk, hak⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hak, (hr.time_mono hk).trans htj⟩
  exact vote_resolved_before_early hrun' hy hS hc hct hg hres hx ⟨ℓv, hcv, hev⟩ hes hHd hHdr
    (by rw [← hes]; exact hHd₀s) hacc hF

/-- **L-gate.** A joined honest update of a label from GST whose frame is below `B` returns a
result, and every result of it extends `B`, when the extending casters of the label outnumber
its opponents. -/
theorem gate_result_extends (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H)
    (hS : ReceiverServiceAfter H (tr.HonestBlocks H) g y tr.projAC)
    {c s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hg : g ≤ sp.ts s + sp.Δ) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hmaj : ExtendingMajority tr H B s) (hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    (∃ C CV, SA.ResultAt tr.projAC y c s C CV) ∧
      ∀ C CV, SA.ResultAt tr.projAC y c s C CV → Anc (tr.HonestBlocks H) B C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hres := update_restarts hr hy hu
  have hct : sp.ts s + 2 * sp.Δ ≤ tr.time c := by
    have : tr.projAC.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
    change sp.ts s + 2 * sp.Δ ≤ tr.projAC.time c
    linarith
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hu.1
  set A := tr.projAC.state y c
  -- every extending caster is delivered: pooled, its head framed, resolved early
  have hdel : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      ∀ Hd ∈ tr.HonestBlocks H, Hd.root = e.msg.head → Anc (tr.HonestBlocks H) B Hd →
      e.msg ∈ A.pool s ∧ Hd ∈ ℓ.frame.tree ∧
        SA.resolutionTime A ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) :=
    fun x hx k e hv hes Hd hHd hHdr hBHd =>
      vote_held_before_early hrun hnc hy hS hu.1 hct hg hres hx hv hes hHd hHdr (hFB.trans hBHd)
  -- `B` is in the frame: an extending caster exists, and its head is framed above `B`
  have hBt : B ∈ ℓ.frame.tree := by
    have hpos : 0 < (ExtendingCasters tr H B s).ncard :=
      lt_of_le_of_lt (Nat.zero_le _) (extendingMajority_iff.1 hmaj)
    obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCasters_iff.1 hxE
    exact mem_tree_between hU hΦ hΦU hFB hBHd (hdel x hx k e hv hes Hd hHd hHdr hBHd).2.1
  -- an honest validator's slot-`s` pool votes are its one slot-`s` vote
  have hone : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := hrun'.honest.pool_vote y hy c s v hvp (hvx ▸ hx)
    have hs' := SA.state_pool_slot sp hr hy c s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (SA.one_vote_per_slot sp _ ro H _ _ hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hsupp : ExtendingCasters tr H B s ⊆ SA.supporters ℓ.frame V s B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCasters_iff.1 hxE
    obtain ⟨hvp, hHdt, hrs⟩ := hdel x hx k e hv hes Hd hHd hHdr hBHd
    refine ⟨?_, e.msg, ⟨hvp, hrs⟩, (SA.vote_signer_slot hr hx hv).1, by exact_mod_cast hes,
      Hd, hHdt, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHdt⟩
    rintro ⟨v, hv1, v', hv2, hne, hvx, hv'x⟩
    exact hne ((hone x hx k e hv hes v hv1 hvx).trans (hone x hx k e hv hes v' hv2 hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆
      ExtendingCasters tr H B s ∪ Opponents tr H B s := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote y hy c s _ hv hw
      have hs := SA.state_pool_slot sp hr hy c s _ hv
      by_cases hext : SA.VoteExtends (tr.HonestBlocks H) e.msg B
      · exact Or.inl (extendingCasters_iff.2 ⟨hw, j, e, he, hs, hext⟩)
      · exact Or.inr (opponents_iff.2 (Or.inr ⟨hw, j, e, he, hs, hext⟩))
    · exact Or.inr (opponents_iff.2 (Or.inl hw))
  have hmaj' : (SA.voters {v | v ∈ A.pool s}).ncard <
      2 * SA.confirmationScore sp A ℓ.frame s B := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le (ExtendingCasters tr H B s) (Opponents tr H B s)
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    have h4 := extendingMajority_iff.1 hmaj
    change _ < 2 * (SA.supporters ℓ.frame V s B).ncard
    omega
  -- the confirmation is the deepest majority block, which `B` is below
  set S := {X | X ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F X ∧
    (SA.voters {v | v ∈ A.pool s}).ncard < 2 * SA.confirmationScore sp A ℓ.frame s X}
  have hS' : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  have hcs : ∀ X, SA.confirmationScore sp A ℓ.frame s X = (SA.supporters ℓ.frame V s X).ncard :=
    fun _ => rfl
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ X ∈ S, ∀ Y ∈ S, Compatible ℓ.frame.tree X Y := fun X hX Y hY =>
    SA.majority_chain sp _ ℓ.frame V s X Y hΦ hsub hX.1 hY.1 (hcs X ▸ hX.2.2) (hcs Y ▸ hY.2.2)
  have hBS : B ∈ S := ⟨hBt, hΦ.rooted.2 B hBt, hmaj'⟩
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hS' ⟨B, hBS⟩
  have hBD := SA.anc_deepest hΦ hS' hch hD B hBS
  have hD' : SA.getConfirmation sp A ℓ.frame s = some D := hD
  refine ⟨⟨D, _, ℓ, hu, hD', rfl⟩, ?_⟩
  rintro C CV ⟨ℓ', hu', hC, -⟩
  obtain rfl : ℓ' = ℓ := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
  have hCD : C = D := Option.some.inj (hC.symm.trans hD')
  subst hCD
  exact hBD.mono hΦU

/-- **L3.** The latest view's majority from the extending casters only: when the
extending casters of the view's label outnumber its
opponents and every extending vote is delivered, the view's voters are fewer than twice the
supporters of `B`. -/
theorem read_majority_of_extending (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {w : Fin sp.n} (hw : w ∈ H) {i : Nat} {t : Time}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 = s)
    (hmaj : ExtendingMajority tr H B s) (hBt : B ∈ (Node.frame (tr.state w i)).tree)
    (hdeliv : ∀ x ∈ H, ∀ k e, SA.VoteAt tr.projAC x k e → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B →
      e.msg ∈ (tr.state w i).ac.pool s ∧
      ∃ Hd ∈ (Node.frame (tr.state w i)).tree, Hd.root = e.msg.head ∧
        (tr.state w i).ac.blockStamp Hd.root < ⊤) :
    (SA.voters (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state w i))
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 B).ncard := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hst := projAC_state hrun.toLocalRun hw i
  have hΦ : FrameOK (Node.frame (tr.state w i)) := frameOK_state hrun.toLocalRun hw i
  have hΦU : (Node.frame (tr.state w i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨w, hw, i, hX.1⟩
  set A := (tr.state w i).ac
  set Φ := Node.frame (tr.state w i)
  set LV := SA.latestView sp A Φ t
  have hL : ((s : Nat) : Int) = LV.2 := hs.symm
  -- the latest view's votes are honest validators' slot-`s` pool votes, or faulty
  have hpool : ∀ u ∈ LV.1.votes, u ∈ (tr.projAC.state w i).pool s := by
    intro u hu
    rw [hst]
    exact ((latestView_mem hL u).1.1 hu).1
  have hsupp : ExtendingCasters tr H B s ⊆ SA.supporters Φ LV.1 LV.2 B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ := extendingCasters_iff.1 hxE
    obtain ⟨hvp, Hd', hHd't, hHd'r, hbst⟩ := hdeliv x hx k e hv hes ⟨Hd, hHdU, hHdr, hBHd⟩
    obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
    obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ := SA.honest_head hrun' hx hv
    obtain rfl : Hd' = Hd₂ := hU.1 hHdU hHd₂ (hHdr.trans hHd₂r.symm)
    have hvp' : e.msg ∈ (tr.projAC.state w i).pool s := by rw [hst]; exact hvp
    have hvotes := mem_latest_votes hrun hnc hw hL hvp'
    have hvst : A.voteStamp e.msg < ⊤ := ((latestView_mem hL e.msg).1.1 hvotes).2
    have hres : SA.resolutionTime A Φ e.msg < ⊤ := by
      unfold SA.resolutionTime
      rw [← hHdr, SA.lookup_of_mem hΦ hHd't]
      dsimp only
      simp only [not_lt.2 hHd₂s, ↓reduceIte]
      exact max_lt hvst hbst
    have hval := (SA.vote_signer_slot hr hx hv).1
    refine ⟨?_, e.msg, (latestView_mem hL e.msg).2.2 ⟨(latestView_mem hL e.msg).1.1 hvotes, hres⟩,
      hval, by rw [← hL, hes], Hd', hHd't, hHdr,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHd't⟩
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    obtain ⟨ja, -, ea, hea, hea'⟩ :=
      hrun'.honest.pool_vote w hw i s a (hpool a ha) (by rw [hav]; exact hx)
    obtain ⟨jb, -, eb, heb, heb'⟩ :=
      hrun'.honest.pool_vote w hw i s b (hpool b hb) (by rw [hbv]; exact hx)
    rw [hav] at hea
    rw [hbv] at heb
    obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp _ ro H _ _ hr x hx ja jb ea eb hea heb
      (by rw [hea', heb', SA.state_pool_slot sp hr hw i s a (hpool a ha),
        SA.state_pool_slot sp hr hw i s b (hpool b hb)])
    exact hab (hea'.symm.trans heb')
  have hvot : SA.voters LV.1.votes ⊆ ExtendingCasters tr H B s ∪ Opponents tr H B s := by
    rintro u ⟨v, hv, rfl⟩
    by_cases hu : v.val ∈ H
    · obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote w hw i s _ (hpool _ hv) hu
      have hes := SA.state_pool_slot sp hr hw i s _ (hpool _ hv)
      by_cases hext : SA.VoteExtends (tr.HonestBlocks H) e.msg B
      · exact Or.inl (extendingCasters_iff.2 ⟨hu, j, e, he, hes, hext⟩)
      · exact Or.inr (opponents_iff.2 (Or.inr ⟨hu, j, e, he, hes, hext⟩))
    · exact Or.inr (opponents_iff.2 (Or.inl hu))
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le (ExtendingCasters tr H B s) (Opponents tr H B s)
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  have h4 := extendingMajority_iff.1 hmaj
  omega

end Consensus.Goldilocks.Compose

end
