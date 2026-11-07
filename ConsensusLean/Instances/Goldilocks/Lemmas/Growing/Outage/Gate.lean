module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageGate
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the reader's gate count and read majority (L1, L-gate, L3)

The growing-fault forms of `Compose/Regimes/OutageGate`, under the receiver service after GST
(`ReceiverServiceAfterAt`):

* `vote_held_before_early_at` (L1): a slot-`q` vote of a node honest at its cast and still honest
  at the receiver call, whose head extends the receiver's `Σ.F`, is pooled, its head framed and the
  vote resolved before `t_q + 2Δ`, at every call from `t_q + 2Δ` of a receiver honest then with no
  restart after `t_q` (D3 with the voter's head facts at its cast);
* `gate_result_extends_at` (L-gate): at an update of a label from GST by a node honest at it,
  joined, with its frame below `B` and an extending majority for `B` charged at the update's cut,
  the update returns a result, and every result extends `B`;
* `read_majority_of_extending_at` (L3): at a read by a node honest at the read time `d` (every
  earlier cut at a time `≤ d`), the latest view's voters are fewer than twice the supporters of
  `B` when the extending majority charged at `d` holds and every extending vote of a validator
  honest at `d` is delivered.

Every count classifies a validator at the cut that reads it: the update's cut, or the read time. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
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

/-- **L1** under growing faults: a slot-`q` vote of a node honest at its cast and at the receiver
call, whose head extends the receiver's `Σ.F`, is held, its head framed, and resolved strictly
before `t_q + 2Δ` at every receiver call from `t_q + 2Δ` with no restart after `t_q`. -/
theorem vote_held_before_early_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {q c : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} (hc : tr.projAC.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} {i : Nat} {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x i e)
    (hx : x ∈ H (tr.time c)) (hes : e.msg.slot = q) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocksAt H) (hHdr : Hd.root = e.msg.head)
    (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    e.msg ∈ (tr.projAC.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      SA.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
        SA.ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hxi, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun
  obtain ⟨Hd₀, hHd₀, hHd₀r, hHd₀s⟩ :=
    SA.honest_head_frame hr hxi (sa_castAt_upTo.mpr ⟨le_rfl, hcv, hev⟩)
  obtain rfl : Hd₀ = Hd := (honestBlocksAt_coherent hrun hnc).1
    ((frameIn_at hrun hnc hxi hcv).2 hHd₀) hHd (hHd₀r.trans hHdr.symm)
  have htj : tr.time i ≤ sp.ts q + sp.Δ := by
    have h := (cast_head_fcRoot_at hrun hnc hxi ⟨hcv, hev⟩).2
    rw [hes] at h
    exact h
  have hacc : Hd₀.root = sp.genesisRoot ∨
      ∃ k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k Hd₀ ∧ tr.time k ≤ sp.ts q + sp.Δ := by
    rcases frame_anc_accepted_at hrun hnc hxi hcv hHd₀ .refl with hgen | ⟨k, hk, hak⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hrun.antitone (hrun.time_mono hk) hxi, hak,
        (hrun.time_mono hk).trans htj⟩
  exact vote_resolved_before_early_at hrun hnc hy hS hc hct hg hres hv hx hes hHd hHdr
    (by rw [← hes]; exact hHd₀s) hacc hF

/-- **L-gate** under growing faults: an update of a label from GST by a node honest at it, whose
frame is below `B`, returns a result, and every result of it extends `B`, when the extending
casters of the label outnumber its opponents, both charged at the update's cut. -/
theorem gate_result_extends_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hg : g ≤ sp.ts s + sp.Δ) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hmaj : ExtendingMajorityAt tr H B s (tr.time c))
    (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    (∃ C CV, SA.ResultAt tr.projAC y c s C CV) ∧
      ∀ C CV, SA.ResultAt tr.projAC y c s C CV → Anc (tr.HonestBlocksAt H) B C := by
  have hm := hrun.time_mono
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg c)).localRun
  have hres : ∀ k ≤ c, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := fun k hk hrk =>
    Compose.update_restarts hr hy ((sa_updateAt_upTo hm).2 ⟨le_rfl, hu⟩) k hk
      ((ac_restartAt_upTo tr.projAC).2 ⟨hm hk, hrk⟩)
  have hct : sp.ts s + 2 * sp.Δ ≤ tr.time c := by
    have : tr.projAC.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
    change sp.ts s + 2 * sp.Δ ≤ tr.projAC.time c
    linarith
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hu.1
  set A := tr.projAC.state y c
  -- every extending caster still honest at the update is delivered
  have hdel : ∀ x k e, HVoteAt tr H x k e → x ∈ H (tr.time c) → e.msg.slot = s →
      ∀ Hd ∈ tr.HonestBlocksAt H, Hd.root = e.msg.head → Anc (tr.HonestBlocksAt H) B Hd →
      e.msg ∈ A.pool s ∧ Hd ∈ ℓ.frame.tree ∧
        SA.resolutionTime A ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) :=
    fun x k e hv hx hes Hd hHd hHdr hBHd =>
      vote_held_before_early_at hrun hnc hy hS hu.1 hct hg hres hv hx hes hHd hHdr
        (hFB.trans hBHd)
  -- `B` is in the frame: an extending caster exists, and its head is framed above `B`
  have hBt : B ∈ ℓ.frame.tree := by
    have hpos : 0 < (ExtendingCastersAt tr H B s (tr.time c)).ncard :=
      lt_of_le_of_lt (Nat.zero_le _) (extendingMajorityAt_iff.1 hmaj)
    obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    exact mem_tree_between hU hΦ hΦU hFB hBHd (hdel x k e hv hx hes Hd hHd hHdr hBHd).2.1
  -- a validator honest at the update has its one slot-`s` vote in the update's pool
  have hone : ∀ x ∈ H (tr.time c), ∀ j e, HVoteAt tr H x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := pool_vote_at hrun hnc hy hvp (hvx ▸ hx)
    have hs' := state_pool_slot_at hrun hnc hy s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (one_vote_per_slot_at hrun hnc hv' hv (hs'.trans hs.symm)).2
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hsupp : ExtendingCastersAt tr H B s (tr.time c) ⊆ SA.supporters ℓ.frame V s B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    obtain ⟨hvp, hHdt, hrs⟩ := hdel x k e hv hx hes Hd hHd hHdr hBHd
    obtain ⟨hxk, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
    refine ⟨?_, e.msg, ⟨hvp, hrs⟩, (castAt_spec_at hrun hnc hxk ⟨hcv, hev⟩).1,
      by exact_mod_cast hes, Hd, hHdt, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHdt⟩
    rintro ⟨v, hv1, v', hv2, hne, hvx, hv'x⟩
    exact hne ((hone x hx k e hv hes v hv1 hvx).trans (hone x hx k e hv hes v' hv2 hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆
      ExtendingCastersAt tr H B s (tr.time c) ∪ OpponentsAt tr H B s (tr.time c) := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H (tr.time c)
    · obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hv hw
      have hs := state_pool_slot_at hrun hnc hy s _ hv
      by_cases hext : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B
      · exact Or.inl (extendingCastersAt_iff.2 ⟨hw, j, e, he, hs, hext⟩)
      · exact Or.inr (opponentsAt_iff.2 (Or.inr ⟨hw, j, e, he, hs, hext⟩))
    · exact Or.inr (opponentsAt_iff.2 (Or.inl hw))
  have hmaj' : (SA.voters {v | v ∈ A.pool s}).ncard <
      2 * SA.confirmationScore sp A ℓ.frame s B := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le (ExtendingCastersAt tr H B s (tr.time c))
      (OpponentsAt tr H B s (tr.time c))
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    have h4 := extendingMajorityAt_iff.1 hmaj
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

/-- **Lemma G at a read**: a vote of the pool of a node honest at a read time `d` (every cut
before `i` at a time `≤ d`) whose validator is honest at `d` was cast by it while honest. -/
private theorem pool_vote_read
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {w : Fin sp.n} {i : Nat} {d : Time} (hd : 0 ≤ d) (hw : w ∈ H d)
    (hi : ∀ k < i, tr.time k ≤ d) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ (tr.projAC.state w i).pool σ) (hvH : v.val ∈ H d) :
    v.slot = σ ∧ ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hr := acRun_upTo hrun hnc hd
  have hst : (tr.projAC.upTo d).state w i = tr.projAC.state w i := Trace.upTo_state _ w hi
  have hv' : v ∈ ((tr.projAC.upTo d).state w i).pool σ := by rw [hst]; exact hv
  obtain ⟨j, hj, e, hve, hev⟩ := hr.honest.pool_vote w hw i σ v hv' hvH
  obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
  exact ⟨SA.state_pool_slot sp hr.localRun hw i σ v hv', j, hj, e,
    hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, hev⟩

/-- **L3** under growing faults: at a read by a node honest at the read time `d` (every cut
before `i` at a time `≤ d`), when the extending casters of the latest view's label `s` outnumber
its opponents, both charged at `d`, and every extending vote of a validator honest at `d` is
delivered, the latest view's voters are fewer than twice the supporters of `B`. -/
theorem read_majority_of_extending_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {w : Fin sp.n} {i : Nat} {d : Time} (hd : 0 ≤ d) (hw : w ∈ H d)
    (hi : ∀ k < i, tr.time k ≤ d) {t : Time} {B : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs : (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 = s)
    (hmaj : ExtendingMajorityAt tr H B s d) (hBt : B ∈ (Node.frame (tr.state w i)).tree)
    (hdeliv : ∀ x k e, HVoteAt tr H x k e → x ∈ H d → e.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B →
      e.msg ∈ (tr.state w i).ac.pool s ∧
      ∃ Hd ∈ (Node.frame (tr.state w i)).tree, Hd.root = e.msg.head ∧
        (tr.state w i).ac.blockStamp Hd.root < ⊤) :
    (SA.voters (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state w i))
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).1
        (SA.latestView sp (tr.state w i).ac (Node.frame (tr.state w i)) t).2 B).ncard := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hstT : (tr.upTo d).state w i = tr.state w i := Trace.upTo_state tr w hi
  have hst : tr.projAC.state w i = (tr.state w i).ac := by
    have h := projAC_state (hrun.upTo hd).toLocalRun hw i
    rwa [RunTrace.upTo_projAC, hstT, Trace.upTo_state tr.projAC w hi] at h
  have hΦ : FrameOK (Node.frame (tr.state w i)) := frameOK_at hrun hd hw hi
  have hΦU : (Node.frame (tr.state w i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => tree_held_at hd hw hi hX.1
  set A := (tr.state w i).ac
  set Φ := Node.frame (tr.state w i)
  set LV := SA.latestView sp A Φ t
  have hL : ((s : Nat) : Int) = LV.2 := hs.symm
  -- the latest view's votes are slot-`s` pool votes
  have hpool : ∀ u ∈ LV.1.votes, u ∈ (tr.projAC.state w i).pool s := by
    intro u hu
    rw [hst]
    exact ((latestView_mem hL u).1.1 hu).1
  have hsupp : ExtendingCastersAt tr H B s d ⊆ SA.supporters Φ LV.1 LV.2 B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ := extendingCastersAt_iff.1 hxE
    obtain ⟨hvp, Hd', hHd't, hHd'r, hbst⟩ := hdeliv x k e hv hx hes ⟨Hd, hHdU, hHdr, hBHd⟩
    obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
    obtain ⟨hxk, ℓv, hcv, hev⟩ := hVoteAt_iff.1 hv
    obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ :=
      SA.honest_head (acRun_upTo hrun hnc (hrun.time_nonneg k)) hxk
        (sa_voteAt_upTo.mpr ⟨le_rfl, ℓv, hcv, hev⟩)
    obtain rfl : Hd' = Hd₂ :=
      hU.1 hHdU (upTo_subset hrun (hrun.time_nonneg k) hHd₂) (hHdr.trans hHd₂r.symm)
    have hvotes : e.msg ∈ LV.1.votes := by
      have hvp' : e.msg ∈ ((tr.upTo d).projAC.state w i).pool s := by
        rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w hi, hst]; exact hvp
      have h := mem_latest_votes (hrun.upTo hd) (hnc.upTo d) hw (by rw [hstT]; exact hL) hvp'
      rwa [hstT] at h
    have hvst : A.voteStamp e.msg < ⊤ := ((latestView_mem hL e.msg).1.1 hvotes).2
    have hres : SA.resolutionTime A Φ e.msg < ⊤ := by
      unfold SA.resolutionTime
      rw [← hHdr, SA.lookup_of_mem hΦ hHd't]
      dsimp only
      simp only [not_lt.2 hHd₂s, ↓reduceIte]
      exact max_lt hvst hbst
    have hval := (castAt_spec_at hrun hnc hxk ⟨hcv, hev⟩).1
    refine ⟨?_, e.msg, (latestView_mem hL e.msg).2.2 ⟨(latestView_mem hL e.msg).1.1 hvotes, hres⟩,
      hval, by rw [← hL, hes], Hd', hHd't, hHdr,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHd't⟩
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    obtain ⟨-, ja, -, ea, hea, hea'⟩ :=
      pool_vote_read hrun hnc hd hw hi (hpool a ha) (by rw [hav]; exact hx)
    obtain ⟨-, jb, -, eb, heb, heb'⟩ :=
      pool_vote_read hrun hnc hd hw hi (hpool b hb) (by rw [hbv]; exact hx)
    rw [hav] at hea
    rw [hbv] at heb
    obtain ⟨-, rfl⟩ := one_vote_per_slot_at hrun hnc hea heb
      (by rw [hea', heb', (pool_vote_read hrun hnc hd hw hi (hpool a ha) (by rw [hav]; exact hx)).1,
        (pool_vote_read hrun hnc hd hw hi (hpool b hb) (by rw [hbv]; exact hx)).1])
    exact hab (hea'.symm.trans heb')
  have hvot : SA.voters LV.1.votes ⊆ ExtendingCastersAt tr H B s d ∪ OpponentsAt tr H B s d := by
    rintro u ⟨v, hv, rfl⟩
    by_cases hu : v.val ∈ H d
    · obtain ⟨hes, j, -, e, he, rfl⟩ := pool_vote_read hrun hnc hd hw hi (hpool _ hv) hu
      by_cases hext : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B
      · exact Or.inl (extendingCastersAt_iff.2 ⟨hu, j, e, he, hes, hext⟩)
      · exact Or.inr (opponentsAt_iff.2 (Or.inr ⟨hu, j, e, he, hes, hext⟩))
    · exact Or.inr (opponentsAt_iff.2 (Or.inl hu))
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le (ExtendingCastersAt tr H B s d) (OpponentsAt tr H B s d)
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  have h4 := extendingMajorityAt_iff.1 hmaj
  omega

end Consensus.Goldilocks.Compose.Growing

end
