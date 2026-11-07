module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage arming under growing faults: Lemma P at an update

`update_result_extends_origin_at` (**Lemma P**): an update of slot `s` by a node honest at its
cut `c`, whose slot's votes are delivered by `t_s + 2Δ ≤ b`, has a result extending an origin
within `b` of an earlier label, held in its frame when `Σ.F ⪯ C`, with a supporter honest at the
update in its pool. The count is charged at the update's cut: the slot-`s` voters still honest
at `t_c` outnumber the validators compromised by `t_c` (`FaultBoundAt (t_s + Δ) (t_c)`), and each
of them is delivered to the update (the static delivery, lifted to the prefix through `t_c`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The head of a vote of a node honest at `d`, cast at a time `≤ d`, is held in the prefix
through `d` (the one block held while honest with its root). -/
private theorem head_mem_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d) {j : Nat}
    (hjd : tr.time j ≤ d) {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x j e)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocksAt H)
    (hHdr : Hd.root = e.msg.head) : Hd ∈ (tr.upTo d).HonestBlocks (H d) := by
  have hv' : SA.VoteAt (tr.upTo d).projAC x j e := by
    rw [RunTrace.upTo_projAC]; exact sa_voteAt_upTo.mpr ⟨hjd, hv⟩
  obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := SA.honest_head
    (goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer (hrun.upTo hd) (hnc.upTo d))
    hx hv'
  obtain rfl : Hd = Hd₂ := (honestBlocksAt_coherent hrun hnc).1 hHd (upTo_subset hrun hd hHd₂)
    (hHdr.trans hHd₂r.symm)
  exact hHd₂

/-- **Lemma P at an update cut**: an update of slot `s > σ` by a node honest at its cut `c`,
whose slot's votes are delivered by `t_s + 2Δ ≤ b` (the update itself may be after `b`), with the
slot count charged at `t_c`, has a result `D` extending an origin `C` within `b` of label `σ`,
held in its frame when `Σ.F ⪯ C`, and a supporter of `D` honest at its cast and at `t_c` in its
pool. -/
theorem update_result_extends_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {ΔF b : Time} (hinv : SleepyInvariantUpTo tr H b) (hsync : SleepyServiceBefore tr H ΔF b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hσs : σ < s) (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b) (hfb : tr.FaultBoundAt H (sp.ts s + sp.Δ) (tr.time c))
    (hFC : Anc (tr.HonestBlocksAt H) (tr.state y c).fg.F C) :
    C ∈ ℓ.frame.tree ∧ ∃ D, SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D ∧
      ℓ.frame.Anc C D ∧ ∃ x j e, HVoteAt tr H x j e ∧ x ∈ H (tr.time c) ∧ e.msg.slot = s ∧
        e.msg ∈ (tr.state y c).ac.pool s ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg c
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun hd
  have hst : (tr.upTo (tr.time c)).state y c = tr.state y c :=
    RunTrace.upTo_state_of_le hm le_rfl
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  set d := tr.time c with hdef
  set Hv := {x | x ∈ H d ∧ ∃ j e, HVoteAt tr H x j e ∧ e.msg.slot = s}
  have hcount : (H d)ᶜ.ncard < Hv.ncard := by
    refine lt_of_lt_of_le hfb (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨j, e, hv, hs, -⟩ :=
      vote_of_awake_joined_at hrun hnc (hrun.antitone (by rw [ht]; linarith) hx) hw hj
    exact ⟨hx, j, e, hv, hs⟩
  have hvb : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → tr.time j ≤ sp.ts s + sp.Δ := by
    rintro x j e hv hs
    obtain ⟨hx, ℓx, hc, he⟩ := hVoteAt_iff.1 hv
    have h := (cast_head_fcRoot_at hrun hnc hx ⟨hc, he⟩).2
    rwa [hs] at h
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  have hfr := frame_of_projAC_at hrun hy hu.1
  have hFeq : ℓ.frame.F = (tr.state y c).fg.F := by rw [hfr]; rfl
  have hsvc := (SleepyServiceBefore.upTo hrun hsync hd).ac
  rw [RunTrace.upTo_projAC] at hsvc
  have hacr := acRun_upTo hrun hnc hd
  -- every slot-`s` vote of a node honest at `t_c` is held and resolved at the update
  have hbatch : ∀ x ∈ H d, ∀ j e, HVoteAt tr H x j e → e.msg.slot = s →
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Anc (tr.HonestBlocksAt H) C Hd ∧
        e.msg ∈ (tr.projAC.state y c).pool s ∧
        SA.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    intro x hx j e hv hes
    have hjd : tr.time j ≤ d := by have := hvb x j e hv hes; rw [ht]; linarith
    obtain ⟨Hd, hHdU, hHdr, hCHd⟩ := hinv.vote_extends C σ hC x j e hv
      (by have := hvb x j e hv hes; linarith) (by omega)
    have hHdU' := head_mem_upTo hrun hnc hd hx hjd (hVoteAt_iff.1 hv).2 hHdU hHdr
    have h := honest_vote_at_update_early hacr hsvc (le_min hsb (by rw [ht]; linarith))
      hy ((sa_updateAt_upTo hm).mpr ⟨le_rfl, hu⟩) hHdU'
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdU' (hFeq ▸ hFC.trans hCHd)) hx
      (sa_voteAt_upTo.mpr ⟨hjd, (hVoteAt_iff.1 hv).2⟩) hes hHdr.symm
    rw [projAC_upTo_state hrun le_rfl] at h
    exact ⟨Hd, h.1, hHdr, hCHd, h.2.1, h.2.2⟩
  -- `C` is in the frame, above `Σ.F`
  have hCt : C ∈ ℓ.frame.tree := by
    obtain ⟨x, hx, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero
      (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨Hd, hHdt, -, hCHd, -⟩ := hbatch x hx j e hv hes
    rw [hfr] at hHdt ⊢
    have hHdU' : Hd ∈ (tr.upTo d).HonestBlocks (H d) := ⟨y, hy, c, by rw [hst]; exact hHdt.1⟩
    have hCHd' := honest_held_anc (hrun.upTo hd) (hnc.upTo _) hy
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdU' hCHd)
      (by rw [hst]; exact hHdt.1)
    rw [hst] at hCHd'
    have hCfg : C ∈ (tr.state y c).fg.tree := by
      by_cases hne : C = Hd
      · exact hne ▸ hHdt.1
      · exact (Goldilocks.Anc.mem hCHd' hne).1
    have hCU' : C ∈ (tr.upTo d).HonestBlocks (H d) := ⟨y, hy, c, by rw [hst]; exact hCfg⟩
    have hFC' := honest_held_anc (hrun.upTo hd) (hnc.upTo _) hy
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hCU' hFC) (by rw [hst]; exact hCfg)
    rw [hst] at hFC'
    exact ⟨hCfg, hFC'⟩
  have hFCΦ : ℓ.frame.Anc ℓ.frame.F C := hΦ.rooted.2 C hCt
  rw [← projAC_state_at hrun hy]
  set A := tr.projAC.state y c
  have hone : ∀ x ∈ H d, ∀ j e, HVoteAt tr H x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := pool_vote_at hrun hnc hy hvp (hvx ▸ hx)
    have hs' := state_pool_slot_at hrun hnc hy s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (one_vote_per_slot_at hrun hnc hv' hv (hs'.trans hs.symm)).2
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hcs : ∀ B, SA.confirmationScore sp A ℓ.frame s B = (SA.supporters ℓ.frame V s B).ncard :=
    fun _ => rfl
  have hsupp : Hv ⊆ SA.supporters ℓ.frame V s C := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨Hd, hHdt, hHdr, hCHd, hvp, hres⟩ := hbatch x hx j e hv hs
    obtain ⟨hxj, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
    have hval := (castAt_spec_at hrun hnc hxj ⟨hcx, hex⟩).1
    refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, Hd, hHdt, hHdr,
      SA.anc_tree_of_anc_U hU hΦ hHB hCt hCHd hHdt⟩
    rintro ⟨v, hv', v', hv'', hne, hvx, hv'x⟩
    exact hne ((hone x hx j e hv hs v hv' hvx).trans (hone x hx j e hv hs v' hv'' hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆ Hv ∪ (H d)ᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H d
    · obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hv hw
      exact Or.inl ⟨hw, j, e, he, state_pool_slot_at hrun hnc hy s _ hv⟩
    · exact Or.inr hw
  have hHvv : Hv ⊆ SA.voters {v | v ∈ A.pool s} := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨-, -, -, -, hvp, -⟩ := hbatch x hx j e hv hs
    obtain ⟨hxj, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
    exact ⟨e.msg, hvp, (castAt_spec_at hrun hnc hxj ⟨hcx, hex⟩).1⟩
  have hmaj : (SA.voters {v | v ∈ A.pool s}).ncard <
      2 * SA.confirmationScore sp A ℓ.frame s C := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le Hv (H d)ᶜ
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    rw [hcs]
    omega
  -- the result is the deepest majority block above `Σ.F`, which extends `C`
  set S := {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
    (SA.voters {v | v ∈ A.pool s}).ncard < 2 * SA.confirmationScore sp A ℓ.frame s B}
  have hS : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  have hsubV : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ B' ∈ S, Compatible ℓ.frame.tree B B' := fun B hB B' hB' =>
    SA.majority_chain sp _ ℓ.frame V s B B' hΦ hsubV hB.1 hB'.1 (hcs B ▸ hB.2.2)
      (hcs B' ▸ hB'.2.2)
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hS ⟨C, hCt, hFCΦ, hmaj⟩
  have hCD := SA.anc_deepest hΦ hS hch hD C ⟨hCt, hFCΦ, hmaj⟩
  have hDmaj := (SA.deepest_mem hD).1.2.2
  rw [hcs] at hDmaj
  refine ⟨hCt, D, hD, hCD, ?_⟩
  -- a supporter of `D` honest at `t_c`
  by_contra hno
  have hSpF : SA.supporters ℓ.frame V s D ⊆ (H d)ᶜ := by
    rintro i ⟨-, v, ⟨hvp, -⟩, hvi, hvs, R, hR, hRr, hDR⟩
    intro hi
    obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hvp (hvi ▸ hi)
    exact hno ⟨_, j, e, he, hvi ▸ hi, by exact_mod_cast hvs, hvp, R, hHB hR, hRr, hDR.mono hHB⟩
  have hSpv : SA.supporters ℓ.frame V s D ⊆ SA.voters {v | v ∈ A.pool s} := by
    rintro i ⟨-, v, ⟨hvp, -⟩, hvi, -⟩
    exact ⟨v, hvp, hvi⟩
  have hdisj : Disjoint Hv (SA.supporters ℓ.frame V s D) :=
    Set.disjoint_left.2 fun x hx hx' => hSpF hx' hx.1
  have h1 := Set.ncard_le_ncard (Set.union_subset hHvv hSpv) (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at h1
  have h2 := Set.ncard_le_ncard hSpF (Set.toFinite _)
  omega

end Consensus.Goldilocks.Compose.Growing

end
