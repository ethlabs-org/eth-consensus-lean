module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Adopt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
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
      vote_of_awake_joined_at hrun hnc (hrun.antitone (by rw [ht]; linarith) hx)
        (mayVote_stock_at hrun hnc (ts_add_delta_nonneg _)
          (hrun.antitone (by rw [ht]; linarith) hx)) hw hj
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

/-- **P≤ at an update cut**: an update within `b` of a node honest at it has root cover, or
Lemma P's frame conclusion. -/
theorem update_result_or_root_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {ΔF b : Time} (hinv : SleepyInvariantUpTo tr H b) (hsync : SleepyServiceBefore tr H ΔF b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCU : C ∈ tr.HonestBlocksAt H) {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hσs : σ < s) (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hcb : tr.time c ≤ b) (hfb : tr.FaultBoundAt H (sp.ts s + sp.Δ) (tr.time c)) :
    Anc (tr.HonestBlocksAt H) C (tr.state y c).fg.F ∨
      (Anc (tr.HonestBlocksAt H) (tr.state y c).fg.F C ∧ C ∈ ℓ.frame.tree ∧
        ∃ D, SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D ∧ ℓ.frame.Anc C D) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hFU : (tr.state y c).fg.F ∈ tr.HonestBlocksAt H :=
    mem_honestBlocksAt hrun hy (frameOK_state (hrun.upTo (hrun.time_nonneg c)).toLocalRun hy c |>
      fun h => by rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h; exact h.rooted.1.1)
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hCU hFU
      (onOriginChainWithin_iff.2 (Or.inr ⟨C, σ, hC, Relation.ReflTransGen.refl⟩))
      (hinv.caches y c (tr.time c) (hrun.time_nonneg c) (fun k hk => hrun.time_mono hk.le) hcb
        hy).1 with hCF | hFC
  · exact Or.inl hCF
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  obtain ⟨hCt, D, hD, hCD, -⟩ := update_result_extends_origin_at hrun hnc hinv hsync hC hy hσs hu
    (by linarith) hfb hFC
  exact Or.inr ⟨hFC, hCt, D, hD, hCD⟩

/-- **The saved attestations** at an update of slot `s ≥ k` by a node honest at its cut `c`
(lifted to the prefix through `t_c`). -/
theorem saved_rows_above_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y c s ℓ) (hks : sp.k ≤ s)
    (hFC : Anc (tr.HonestBlocksAt H) (tr.state y c).fg.F C)
    (hCt : C ∈ (tr.state y c).fg.tree)
    (hnr : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts ((s : Int) - sp.k + 1))
    (hex : ∀ q : Nat, (s : Int) - sp.k < q → q < s →
      ∃ k < c, ∃ ℓ', SA.UpdateAt tr.projAC y k q ℓ')
    (hrow : ∀ q : Nat, (s : Int) - sp.k < q → q < s → ∀ k < c, ∀ ℓ',
      SA.UpdateAt tr.projAC y k q ℓ' → ∃ R, SA.getConfirmation sp (tr.state y k).ac
        ℓ'.frame q = some R ∧ Anc (tr.HonestBlocksAt H) C R) :
    ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ ℓ.frame.tree,
      (tr.state y c).ac.saved j = some S.root ∧ ℓ.frame.Anc C S := by
  have hd := hrun.time_nonneg c
  have hm := hrun.time_mono
  have hst : ∀ k, k ≤ c → (tr.upTo (tr.time c)).state y k = tr.state y k :=
    fun k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hCU : C ∈ (tr.upTo (tr.time c)).HonestBlocks (H (tr.time c)) :=
    ⟨y, hy, c, by rw [hst c le_rfl]; exact hCt⟩
  have h := saved_rows_above (hrun.upTo hd) (hnc.upTo _) hy (C := C)
    (by rw [RunTrace.upTo_projAC]; exact (sa_updateAt_upTo hm).mpr ⟨le_rfl, hu⟩) hks
    (by rw [hst c le_rfl]; exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hCU hFC)
    (by rw [hst c le_rfl]; exact hCt)
    (fun k hk hrk => hnr k hk ((RunTrace.upTo_restartAt tr).mp hrk).2)
    (fun q hq₁ hq₂ => by
      obtain ⟨k, hk, ℓ', hu'⟩ := hex q hq₁ hq₂
      exact ⟨k, hk, ℓ', by
        rw [RunTrace.upTo_projAC]; exact (sa_updateAt_upTo hm).mpr ⟨hm hk.le, hu'⟩⟩)
    (fun q hq₁ hq₂ k hk ℓ' hu' => by
      rw [RunTrace.upTo_projAC] at hu'
      obtain ⟨hkd, hu'⟩ := (sa_updateAt_upTo hm).mp hu'
      obtain ⟨R, hR, hCR⟩ := hrow q hq₁ hq₂ k hk ℓ' hu'
      have hRU : R ∈ (tr.upTo (tr.time c)).HonestBlocks (H (tr.time c)) :=
        mem_upTo_of_frame hrun hy hkd hu'.1 (SA.deepest_mem hR).1.1
      exact ⟨R, by rw [hst k hk.le]; exact hR,
        RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hRU hCR⟩)
  intro j hj₁ hj₂
  obtain ⟨S, hS, hsv, hCS⟩ := h j hj₁ hj₂
  exact ⟨S, hS, by rw [← hst c le_rfl]; exact hsv, hCS⟩

/-- **An own optimistic selection is compatible with a later result of the same label**, at
cuts of a node honest at the result (lifted to the prefix through the result's time). -/
theorem own_optimistic_compatible_result_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {k c s : Nat} (hy : y ∈ H (tr.time c))
    {B' D : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (SA.Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC y k s B' CV) (hR : SA.ResultAt tr.projAC y c s D CV')
    (hkc : k < c) (hnr : ∀ r, k < r → r ≤ c → ¬ tr.RestartAt y r) :
    Compatible (tr.HonestBlocksAt H) B' D := by
  have hd := hrun.time_nonneg c
  have hm := hrun.time_mono
  have h := own_optimistic_compatible_result (hrun.upTo hd) (hnc.upTo _) hy
    (by rw [RunTrace.upTo_projAC]; exact (sa_optimisticLockAt_upTo hm).mpr ⟨hm hkc.le, hO⟩)
    (by rw [RunTrace.upTo_projAC]; exact (sa_resultAt_upTo hm).mpr ⟨le_rfl, hR⟩) hkc
    (fun r h₁ h₂ hrr => hnr r h₁ h₂ ((RunTrace.upTo_restartAt tr).mp hrr).2)
  exact h.imp (fun h => h.mono (upTo_subset hrun hd)) (fun h => h.mono (upTo_subset hrun hd))

/-- **The veto analysis at the cover gate**, at the first update of slot `s` by a node honest at
its cut `c`, with a result `D ⪰ C` supported by a pool vote of a node honest at its cast and at
`t_c`: every live block that vetoes `D` is that of a stored lock of slot `s + 1` and extends `C`.
The opponents `Opp` contain the validators compromised by `t_c`; the optimistic voters of a
slot-`(s + 1)` selection are classified at `t_c` (a voter honest then has a genuine vote). -/
theorem cover_gate_veto_above_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hfirst : ∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC y k s ℓ')
    (hD : SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D) (hCD : ℓ.frame.Anc C D)
    (hsupp : ∃ x j e, HVoteAt tr H x j e ∧ x ∈ H (tr.time c) ∧ e.msg.slot = s ∧
      e.msg ∈ (tr.state y c).ac.pool s ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg D)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b)
    (hnr : ∀ r ≤ c, tr.RestartAt y r → tr.time r < sp.ts s)
    (Hold Opp : Set (Fin sp.n)) (hF : (H (tr.time c))ᶜ ⊆ Opp) (hopp : 2 * Opp.ncard < sp.n)
    (hcast : ∀ x j e, HVoteAt tr H x j e → x ∈ H (tr.time c) → e.msg.slot = s + 1 → j < c →
      x ∈ Hold ∨ x ∈ Opp)
    (hN : ∀ x ∈ Hold, ∀ j e, HVoteAt tr H x j e → e.msg.slot = s + 1 → j < c →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg C) :
    ∀ V ∈ SA.liveLockBlocks sp (tr.state y c).ac.locks ℓ.frame (tr.time c),
      ¬ Compatible ℓ.frame.tree D V →
        (∃ l ∈ (tr.state y c).ac.locks, l.slot = s + 1 ∧
          ∃ B₀ ∈ ℓ.frame.tree, B₀.root = l.block ∧ V = ℓ.frame.viableAncestor B₀) ∧
        ℓ.frame.Anc C V := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg c
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun hd
  have hacr := acRun_upTo hrun hnc hd
  have hfr := frame_of_projAC_at hrun hy hu.1
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  have hDt : D ∈ ℓ.frame.tree := (SA.deepest_mem hD).1.1
  have hCt : C ∈ ℓ.frame.tree := SA.mem_of_anc hCD hDt
  have hCD' := hCD.mono hHB
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  intro V hV hconf
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hV
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB₀
  have hVB' := hVB.mono hHB
  have hnoU : ¬ Compatible (tr.HonestBlocksAt H) D (ℓ.frame.viableAncestor B₀) := by
    rintro (h | h)
    · exact hconf (Or.inl (SA.anc_tree_of_anc_U hU hΦ hHB hDt h hVt))
    · exact hconf (Or.inr (SA.anc_tree_of_anc_U hU hΦ hHB hVt h hDt))
  have hO : ∀ O, Anc (tr.HonestBlocksAt H) B₀ O → Compatible (tr.HonestBlocksAt H) O D →
      False := by
    intro O hBO h
    apply hnoU
    rcases h with h | h
    · exact Or.inr (hVB'.trans (hBO.trans h))
    · exact SA.anc_total hU h (hVB'.trans hBO)
  obtain ⟨L, hL, hLr, O, hLO, k', hk', CV, hO'⟩ := SA.lock_below_origin hacr.localRun hy c l
    (by rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hy]; exact hl)
  obtain rfl : B₀ = L := (hU.1 (hsub hL) (hHB hB₀) (hLr.trans hB₀r.symm)).symm
  have hLO' := hLO.mono hsub
  have hk'c := hm hk'.le
  have hyk' : y ∈ H (tr.time k') := hrun.antitone hk'c hy
  replace hO' : SA.ResultAt tr.projAC y k' l.slot O CV ∨
      SA.OptimisticLockAt tr.projAC y k' l.slot O CV :=
    hO'.imp (fun h => ((sa_resultAt_upTo hm).mp h).2)
      (fun h => ((sa_optimisticLockAt_upTo hm).mp h).2)
  -- an origin within `b` of a label below `s` is compatible with `D` (its supporter)
  have hearly : ∀ σ', σ' < s → OriginWithin tr H O σ' b →
      Compatible (tr.HonestBlocksAt H) O D := by
    intro σ' hσ' hOw
    obtain ⟨x, j, e, hv, -, hes, -, Hd', hHd', hHd'r, hDHd'⟩ := hsupp
    obtain ⟨hxj, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
    have hvt := (cast_head_fcRoot_at hrun hnc hxj ⟨hcx, hex⟩).2
    rw [hes] at hvt
    obtain ⟨Hd, hHd, hHdr, hOHd⟩ := hinv.vote_extends O σ' hOw x j e hv
      (by linarith) (by omega)
    obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
    exact SA.anc_total hU hOHd hDHd'
  rcases lt_trichotomy l.slot s with hls | hls | hls
  · -- (a) a label below `s`: an origin within `b`
    exfalso
    have hts := (SA.ts_le_iff sp).2 (show (l.slot : Int) + 1 ≤ s by omega)
    refine hO O hLO' (hearly l.slot hls (originWithin_iff.2 ⟨y, k', CV, hyk', ?_, hO'⟩))
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · have ht : tr.time k' = sp.ts l.slot + 6 * sp.Δ := hu'.2.2.1
      simp only [SAParams.ts] at hts ht hsb ⊢
      linarith
    · -- TEMP(C2): C3/C4 replaces
      have ht := (SA.optimisticLockAt_spec (acRun_upTo hrun hnc (hrun.time_nonneg k')) hyk'
        ((sa_optimisticLockAt_upTo hm).mpr ⟨le_rfl, hopt⟩) (SA.CommitteeDict.full sp.n)
        (fun _ _ _ => SA.mem_full _ _)).1
      change tr.time k' < _ at ht
      simp only [SAParams.ts] at hts ht hsb ⊢
      linarith
  · -- (b) label `s`: the own optimistic selection, compatible with the result
    exfalso
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · exact hfirst k' hk' ℓ' (hls ▸ hu')
    · rw [hls] at hopt
      refine hO O hLO' (own_optimistic_compatible_result_at hrun hnc hy hopt
        ⟨ℓ, hu, by rw [projAC_state_at hrun hy]; exact hD, rfl⟩ hk' ?_)
      intro r hr₁ hr₂ hrr
      have h1 := hnr r hr₂ hrr
      have h2 := hm hr₁.le
      obtain ⟨ℓo, Ao, -, hso, -⟩ := hopt
      have h3 := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k') s).2 (by
        have : sp.slot (tr.time k') = s := hso
        rw [this])
      linarith
  · -- (c) a later label: an own optimistic selection of slot `s + 1`
    have hsc : sp.slot (tr.time c) = s + 1 := by
      have h6 : tr.time c = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := by
        rw [htc]; simp only [SAParams.ts]; push_cast; ring
      exact SA.slot_of_mem sp (s + 1) (by rw [h6]; linarith)
        (by rw [h6]; simp only [SAParams.ts]; push_cast; linarith)
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · exfalso
      have ht : tr.time k' = sp.ts l.slot + 6 * sp.Δ := hu'.2.2.1
      have := (SA.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts s by linarith)
      omega
    have hls' : l.slot = s + 1 := by
      obtain ⟨ℓo, Ao, -, hso, -⟩ := hopt
      have h1 := SA.slot_mono sp (hrun.time_nonneg k') hk'c
      have hso' : sp.slot (tr.time k') = l.slot := hso
      rw [hso', hsc] at h1
      omega
    -- the optimistic voters, classified at `t_c`
    -- TEMP(C2): C3/C4 replaces
    obtain ⟨-, hcnt, ell, A, hp, -, hCV, hCVv, -⟩ := SA.optimisticLockAt_spec hacr hy
      ((sa_optimisticLockAt_upTo hm).mpr ⟨hk'c, hopt⟩) (SA.CommitteeDict.full sp.n)
      (fun _ _ _ => SA.mem_full _ _)
    rw [hacr.stock] at hcnt
    obtain ⟨-, hpc⟩ := (Trace.upTo_callAt _).mp hp.1
    have hellU := (frameIn_at hrun hnc hyk' hpc).2
    obtain ⟨v, hvCV, hvH, hvHold⟩ : ∃ v ∈ CV, v.val ∈ H (tr.time c) ∧ v.val ∈ Hold := by
      by_contra hno
      push Not at hno
      have hsub' : SA.voters CV ⊆ Opp := by
        rintro i ⟨v, hv, rfl⟩
        by_cases hvH : v.val ∈ H (tr.time c)
        · obtain ⟨a, ha, e', he', hev⟩ := hCVv v hv hvH
          obtain ⟨had, he'⟩ := sa_voteAt_upTo.mp he'
          rcases hcast _ a e' (hVoteAt_iff.2 ⟨hrun.antitone had (hev ▸ hvH), hev ▸ he'⟩)
            hvH (by rw [hev, (hCV v hv).2.1, hls']) (by omega) with h | h
          · exact absurd h (hno v hv hvH)
          · exact h
        · exact hF hvH
      have := Set.ncard_le_ncard hsub' (Set.toFinite _)
      omega
    obtain ⟨a, ha, e', he', hev⟩ := hCVv v hvCV hvH
    obtain ⟨had, he'⟩ := sa_voteAt_upTo.mp he'
    obtain ⟨Hd, hHd, hHdr, hCHd⟩ := hN v.val hvHold a e'
      (hVoteAt_iff.2 ⟨hrun.antitone had (hev ▸ hvH), hev ▸ he'⟩)
      (by rw [hev, (hCV v hvCV).2.1, hls']) (by omega)
    obtain ⟨-, -, R, hR, hRr, hOR⟩ := hCV v hvCV
    obtain rfl : R = Hd := hU.1 (hellU hR) hHd (hRr.trans (by rw [hHdr, hev]))
    rcases SA.anc_total hU (hOR.mono hellU) hCHd with hOC | hCO
    · exact (hO O hLO' (Or.inl (hOC.trans hCD'))).elim
    rcases SA.anc_total hU hCO (hVB'.trans hLO') with hCV' | hVC
    · exact ⟨⟨l, hl, hls', B₀, hB₀, hB₀r, rfl⟩, SA.anc_tree_of_anc_U hU hΦ hHB hCt hCV' hVt⟩
    · exact (hnoU (Or.inr (hVC.trans hCD'))).elim

/-! ### The armed updates of a cohort member -/

/-- (R1) Awake on `[a, z]` and honest at `z`: every restart up to `z` is at or before every
public `τ ∈ [a, z]`. -/
theorem restart_le_of_awakeOn_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {a z τ : Time} (hy : y ∈ H z) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake y u)
    (haτ : a ≤ τ) (hτz : τ ≤ z) (hτ0 : 0 ≤ τ) (hpub : sp.toParams.IsPublic τ)
    {k : Nat} (hk : tr.RestartAt y k) (hkz : tr.time k ≤ z) : tr.time k ≤ τ := by
  by_contra hgt
  push Not at hgt
  obtain ⟨u, -, huk, hs, hb⟩ := hrun.sleep_of_restart y k (hrun.antitone hkz hy) hk
  have hua : u < a := by
    by_contra hle
    exact hs (haw u (not_lt.1 hle) (by linarith))
  obtain ⟨j, x, hj⟩ := hrun.tick_of_awake y τ (hrun.antitone hτz hy) hτ0 hpub (haw τ haτ hτz)
  obtain ⟨hjc, hjt⟩ := group_call hj
  have hjk : j < k := by
    by_contra hkj
    have := hrun.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk hjc
  linarith

/-- A node awake on `[a, z]` and honest at `z`, with `a ≤ t_r`, runs the update of every slot
`q ≥ r` whose update is by `z`. -/
theorem update_of_awakeOn_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {w : Fin sp.n}
    {a z : Time} (hw : w ∈ H z) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u) {r q : Nat}
    (ha : a ≤ sp.ts r) (hrq : r ≤ q) (hqz : sp.ts q + 6 * sp.Δ ≤ z) :
    ∃ k ℓ, SA.UpdateAt tr.projAC w k q ℓ := by
  have hΔ := sp.toParams.hΔ
  have hrq' := (SA.ts_le_iff sp).2 (show (r : Int) ≤ q by exact_mod_cast hrq)
  have h0 : (0 : Time) ≤ sp.ts r := by simp only [SAParams.ts]; positivity
  have hd : 0 ≤ sp.ts q + 6 * sp.Δ := by linarith
  have hj : tr.JoinedAt w (sp.ts q + 6 * sp.Δ) := fun k hk hkt => by
    have hkr := restart_le_of_awakeOn_at hrun hw haw ha (by linarith) h0
      (show sp.toParams.IsPublic _ from
        Dvd.intro (4 * (r : Int)) (by simp only [SAParams.ts]; ring))
      hk (hkt.trans hqz)
    have hsl : sp.slot (sp.ts q + 6 * sp.Δ) = q + 1 := by
      have h6 : sp.ts q + 6 * sp.Δ = sp.ts ((q + 1 : Nat) : Int) + 2 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [h6]
      exact SA.slot_of_mem sp (q + 1) (by linarith)
        (by simp only [SAParams.ts]; push_cast; linarith)
    change 0 < sp.slot _ ∧ _ ≤ sp.toParams.slotTime (sp.slot _ - 1)
    rw [hsl, Nat.add_sub_cancel, sp.slotTime_eq]
    refine ⟨Nat.succ_pos q, ?_⟩
    change _ ≤ sp.ts q
    linarith
  obtain ⟨k, ℓ, hu⟩ := update_of_awake_joined (hrun.upTo hd) (hrun.antitone hqz hw)
    ⟨haw _ (by linarith) hqz, le_rfl⟩ (joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hu
  exact ⟨k, ℓ, ((sa_updateAt_upTo hrun.time_mono).mp hu).2⟩

/-- **The first armed update** of slot `s` of a cohort member `w` (honest at `z`, awake on
`[a, z]`): it exists, its restarts are at or before `t_{s−k+1}`, and when `Σ.F ⪯ C` the origin
`C` (of a label `σ ≤ s − k`) is in its frame below its result, which a pool vote of a node honest
at its cast and at the update supports, and every saved attestation of the slow test names a
block of the frame above `C`. The slot counts are charged at the update times (`hB` through
`b' ≥ z`). -/
theorem armed_first_update_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {ΔF b b' : Time} (hinv : SleepyInvariantUpTo tr H b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b')
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    {w : Fin sp.n} {a z : Time} (hw : w ∈ H z) (hzb : z ≤ b')
    (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ') ∧
      (∀ r ≤ c, tr.RestartAt w r → tr.time r ≤ sp.ts ((s : Int) - sp.k + 1)) ∧
      (Anc (tr.HonestBlocksAt H) (tr.state w c).fg.F C →
        C ∈ ℓ.frame.tree ∧ ∃ D, SA.getConfirmation sp (tr.state w c).ac ℓ.frame s = some D ∧
          ℓ.frame.Anc C D ∧
          (∃ x j e, HVoteAt tr H x j e ∧ x ∈ H (tr.time c) ∧ e.msg.slot = s ∧
            e.msg ∈ (tr.state w c).ac.pool s ∧
            SA.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
          ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ ℓ.frame.tree,
            (tr.state w c).ac.saved j = some S.root ∧ ℓ.frame.Anc C S) := by
  classical
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hm := hrun.time_mono
  have hrI : ((s - sp.k + 1 : Nat) : Int) = (s : Int) - sp.k + 1 := by omega
  have ha' : a ≤ sp.ts (s - sp.k + 1 : Nat) := by rw [hrI]; exact ha
  have hex₀ : ∃ c, ∃ ℓ, SA.UpdateAt tr.projAC w c s ℓ :=
    update_of_awakeOn_at hrun hw haw ha' (by omega) hsz
  obtain ⟨ℓ, hu⟩ := Nat.find_spec hex₀
  have hfirst : ∀ k < Nat.find hex₀, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ' :=
    fun k hk ℓ' h => Nat.find_min hex₀ hk ⟨ℓ', h⟩
  have htc : tr.time (Nat.find hex₀) = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hwc : w ∈ H (tr.time (Nat.find hex₀)) := hrun.antitone (htc ▸ hsz) hw
  -- the slot count of an update of a slot `q`, charged at its time `t_q + 6Δ ≤ z`
  have hfbu : ∀ {k q : Nat} {ℓ'}, SA.UpdateAt tr.projAC w k q ℓ' →
      sp.ts q + 6 * sp.Δ ≤ z → tr.FaultBoundAt H (sp.ts q + sp.Δ) (tr.time k) := by
    intro k q ℓ' hu' hqz
    have ht : tr.time k = sp.ts q + 6 * sp.Δ := hu'.2.2.1
    exact hB.slot q (tr.time k) (Nat.zero_le _) (by rw [ht]; linarith) (by rw [ht]; linarith) ht.le
  have hτs := (SA.ts_le_iff sp).2 (show (s : Int) - sp.k + 1 ≤ s by omega)
  have h0 : (0 : Time) ≤ sp.ts (s - sp.k + 1 : Nat) := by simp only [SAParams.ts]; positivity
  have hnr : ∀ r ≤ Nat.find hex₀, tr.RestartAt w r →
      tr.time r ≤ sp.ts ((s : Int) - sp.k + 1) := by
    intro r hr' hrr
    rw [← hrI]
    exact restart_le_of_awakeOn_at hrun hw haw ha' (by rw [hrI]; linarith) h0
      (show sp.toParams.IsPublic _ from Dvd.intro (4 * ((s - sp.k + 1 : Nat) : Int))
        (by simp only [SAParams.ts]; ring)) hrr ((hm hr').trans (htc ▸ hsz))
  refine ⟨Nat.find hex₀, ℓ, hu, hfirst, hnr, fun hFC => ?_⟩
  obtain ⟨hCt, D, hD, hCD, hsupp⟩ := update_result_extends_origin_at hrun hnc hinv hsync hC hwc
    (by omega) hu hsb (hfbu hu hsz) hFC
  refine ⟨hCt, D, hD, hCD, hsupp, ?_⟩
  have hCtfg : C ∈ (tr.state w (Nat.find hex₀)).fg.tree := by
    rw [frame_of_projAC_at hrun hwc hu.1] at hCt; exact hCt.1
  refine saved_rows_above_at hrun hnc hwc hu hks hFC hCtfg hnr ?_ ?_
  · intro q hq₁ hq₂
    have hqs := (SA.ts_lt_iff sp).2 (show (q : Int) < s by exact_mod_cast hq₂)
    obtain ⟨k, ℓ', hu'⟩ := update_of_awakeOn_at hrun hw haw ha' (r := s - sp.k + 1) (q := q)
      (by omega) (by linarith)
    refine ⟨k, ?_, ℓ', hu'⟩
    by_contra hck
    push Not at hck
    have h1 := hm hck
    have h2 : tr.time k = sp.ts q + 6 * sp.Δ := hu'.2.2.1
    linarith
  · intro q hq₁ hq₂ k hk ℓ' hu'
    have hqs := (SA.ts_lt_iff sp).2 (show (q : Int) < s by exact_mod_cast hq₂)
    have hwk : w ∈ H (tr.time k) := hrun.antitone (hm hk.le) hwc
    have hd := hrun.time_nonneg (Nat.find hex₀)
    have hFm := Healing.run_F_mono (hrun.upTo hd).toLocalRun hwc hk.le
    rw [RunTrace.upTo_state_of_le hm (hm hk.le),
      RunTrace.upTo_state_of_le hm le_rfl] at hFm
    have hFk : Anc (tr.HonestBlocksAt H) (tr.state w k).fg.F C :=
      (hFm.mono (upTo_subset hrun hd)).trans hFC
    obtain ⟨-, R, hR, hCR, -⟩ := update_result_extends_origin_at hrun hnc hinv hsync hC hwk
      (by omega) hu' (by linarith) (hfbu hu' (by linarith)) hFk
    exact ⟨R, hR, hCR.mono (frameIn_at hrun hnc hwk hu'.1).2⟩

/-- The post-state locks of an update by a node honest at it are those of
`update_confirmation`. -/
private theorem locks_after_update_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {w : Fin sp.n} {c s : Nat} (hw : w ∈ H (tr.time c)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC w c s ℓ) :
    (tr.state w (c + 1)).ac.locks =
      (SA.updateConfirmation sp (tr.state w c).ac ℓ.frame (tr.time c) s).locks := by
  have hd := hrun.time_nonneg c
  have hm := hrun.time_mono
  have hr := hrun.upTo hd
  have hst1 : (tr.upTo (tr.time c)).state w (c + 1) = tr.state w (c + 1) :=
    Trace.upTo_state tr w fun _ hk' => hm (Nat.lt_succ_iff.1 hk')
  have h := SA.state_after_update (acRun_upTo hrun hnc hd).localRun hw
    ((sa_updateAt_upTo hm).mpr ⟨le_rfl, hu⟩)
  rw [← RunTrace.upTo_projAC, projAC_state hr.toLocalRun hw (c + 1),
    projAC_state hr.toLocalRun hw c, hst1, RunTrace.upTo_state_of_le hm le_rfl] at h
  rw [h]
  rfl

/-- The slot of an update's time is the next slot. -/
private theorem slot_update_time {s : Nat} : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 := by
  have hΔ := sp.toParams.hΔ
  have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rw [h6]
  exact SA.slot_of_mem sp (s + 1) (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)

/-- **O1 at an update within `b`**: the first update of slot `s` of a cohort member, at a time
`≤ b`, has root cover, or stores a lock of slot `s` on a block of its frame above `C`. -/
theorem armed_lock_formed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {ΔF b b' : Time} (hinv : SleepyInvariantUpTo tr H b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b')
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCU : C ∈ tr.HonestBlocksAt H) (hCg : C.root ≠ sp.genesisRoot)
    {w : Fin sp.n} {a z : Time} (hw : w ∈ H z) (hzb : z ≤ b')
    (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 6 * sp.Δ ≤ b) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧
      (Anc (tr.HonestBlocksAt H) C (tr.state w c).fg.F ∨
        ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc C L ∧
          (⟨L.root, s, f, s + sp.k⟩ : SA.Lock) ∈ (tr.state w (c + 1)).ac.locks) := by
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  obtain ⟨c, ℓ, hu, -, -, hP⟩ := armed_first_update_at hrun hnc hinv hsync hB hC hw hzb haw hks
    hσs ha hsz (by linarith)
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hwc : w ∈ H (tr.time c) := hrun.antitone (htc ▸ hsz) hw
  refine ⟨c, ℓ, hu, ?_⟩
  rcases update_result_or_root_at hrun hnc hinv hsync hC hCU hwc (by omega) hu (htc ▸ hsb)
      (hB.slot s (tr.time c) (Nat.zero_le _) (by rw [htc]; linarith) (by rw [htc]; linarith)
        htc.le) with
      hroot | ⟨hFC, -, -⟩
  · exact Or.inl hroot
  obtain ⟨hCt, D, hD, hCD, -, hrows⟩ := hP hFC
  have hfr := frame_of_projAC_at hrun hwc hu.1
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hwc hu.1
  have hcand : ℓ.frame.AncestorCandidate C := by
    rw [hfr] at hCt ⊢
    exact hinv.viable w c (tr.time c) (hrun.time_nonneg c) (fun k hk => hrun.time_mono hk.le)
      (htc ▸ hsb) hwc C σ hC hCt
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by
    rw [htc, slot_update_time]; omega
  obtain ⟨L, f, hL, hCL, hl⟩ := SA.updateConfirmation_slow_lock_effective hΦ hD
    (result_not_vetoed_at hrun hnc ((hrun.time_nonneg _).trans (htc ▸ hsb)) hinv hwc hu
      (htc ▸ hsb) hD) hCt hCg hCD hrows hlive hcand
  exact Or.inr ⟨L, f, hL, hCL, (locks_after_update_at hrun hnc hwc hu).symm ▸ hl⟩

/-- **O1 at the cover gate**: the first update of slot `s` of a cohort member, whose slot's
votes are delivered by `t_s + 2Δ ≤ b` but which may itself be after `b`. Given (F), (VA) when
`Σ.F ⪯ C`, and (N) for the `Hold` votes of slot `s + 1` before it, it has root cover or stores a
lock of slot `s` and expiry `s + k` above `C`. The opponents `Opp` hold the validators
compromised by the update's time `t_s + 6Δ`; a slot-`(s + 1)` caster honest then is in `Hold` or
`Opp`. -/
theorem armed_lock_cover_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {ΔF b b' : Time} (hinv : SleepyInvariantUpTo tr H b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b')
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCg : C.root ≠ sp.genesisRoot)
    {w : Fin sp.n} {a z : Time} (hw : w ∈ H z) (hzb : z ≤ b')
    (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b)
    (Hold Opp : Set (Fin sp.n)) (hF : (H (sp.ts s + 6 * sp.Δ))ᶜ ⊆ Opp)
    (hopp : 2 * Opp.ncard < sp.n)
    (hcast : ∀ x j e, HVoteAt tr H x j e → x ∈ H (sp.ts s + 6 * sp.Δ) → e.msg.slot = s + 1 →
      tr.time j ≤ sp.ts s + 6 * sp.Δ → x ∈ Hold ∨ x ∈ Opp) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ') ∧
      (Compatible (tr.HonestBlocksAt H) (tr.state w c).fg.F C →
        (Anc (tr.HonestBlocksAt H) (tr.state w c).fg.F C → ℓ.frame.AncestorCandidate C) →
        (∀ x ∈ Hold, ∀ j e, HVoteAt tr H x j e → e.msg.slot = s + 1 → j < c →
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg C) →
        Anc (tr.HonestBlocksAt H) C (tr.state w c).fg.F ∨
        ∃ L f, ℓ.frame.Anc C L ∧
          (⟨L.root, s, f, s + sp.k⟩ : SA.Lock) ∈ (tr.state w (c + 1)).ac.locks) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨c, ℓ, hu, hfirst, hnr, hP⟩ := armed_first_update_at hrun hnc hinv hsync hB hC hw hzb
    haw hks hσs ha hsz hsb
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hwc : w ∈ H (tr.time c) := hrun.antitone (htc ▸ hsz) hw
  refine ⟨c, ℓ, hu, hfirst, fun hFcomp hVA hN => ?_⟩
  rcases hFcomp with hFC | hCF
  swap
  · exact Or.inl hCF
  obtain ⟨hCt, D, hD, hCD, hsupp, hrows⟩ := hP hFC
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hwc hu.1
  have hτs := (SA.ts_lt_iff sp).2 (show (s : Int) - sp.k + 1 < s by
    have := sp.two_le_k; omega)
  have hveto := cover_gate_veto_above_at hrun hnc hinv hwc hu hfirst hD hCD hsupp hsb
    (fun r hr hrr => (hnr r hr hrr).trans_lt hτs) Hold Opp (htc ▸ hF) hopp
    (fun x j e hv hx hs hj => hcast x j e hv (htc ▸ hx) hs (htc ▸ hrun.time_mono hj.le)) hN
  have hnvC : ¬ SA.conflictsWithLock sp (tr.state w c).ac.locks ℓ.frame (tr.time c) C := by
    rintro ⟨W, hW, hCW⟩
    by_cases hDW : Compatible ℓ.frame.tree D W
    · rcases hDW with h | h
      · exact hCW (Or.inl (hCD.trans h))
      · exact hCW (SA.anc_total hΦ.coherent hCD h)
    · exact hCW (Or.inl (hveto W hW hDW).2)
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by
    rw [htc, slot_update_time]; have := sp.two_le_k; omega
  obtain ⟨L, -, hCL, hl⟩ := SA.updateConfirmation_slow_lock_effective_of hΦ hD hnvC hCt hCg
    hCD hrows hlive (hVA hFC)
  exact Or.inr ⟨L, false, hCL, (locks_after_update_at hrun hnc hwc hu).symm ▸ hl⟩

end Consensus.Goldilocks.Compose.Growing

end
