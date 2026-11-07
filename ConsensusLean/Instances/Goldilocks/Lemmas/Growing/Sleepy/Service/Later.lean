module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Adopt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: a later update adopts the proposal

The growing-fault form of `Compose/Service/Later`: after the update of any slot `s' ≥ s` (at
`d = t_{s'} + 6Δ`) of a node honest then, through `b`, its record names a block extending the
proposal `P` of slot `s` (by a proposer honest at `t_s + Δ`), or its `Σ.F` extends `P`.

* `update_of_awake_joined_at`: a validator honest, awake and joined at `t_s + 6Δ` runs the update
  of slot `s` there;
* `update_adopts_origin_at` (`s' > s`, `P` an origin of label `s`): the slot-`s'` voters still
  honest at `d` extend `P` (S2), are held and resolved at the update, and outnumber the validators
  compromised by `d` (the slot count at `d`, the double-count channel), so the result extends `P`;
* `later_update_adopts_gt_at`: `P` is an origin, the result of the update of slot `s` of a node
  honest, awake and joined at `t_s + 6Δ = t_{s+1} + 2Δ` (the `2Δ` slot-point count,
  `SleepyBounds.late`);
* `later_update_adopts_at`: both cases. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **A validator honest, awake and joined at `t_s + 6Δ` runs the update of slot `s` there** (the
static `update_of_awake_joined` on the prefix through `t_s + 6Δ`). -/
theorem update_of_awake_joined_at (hrun : Growing.GoldilocksRun proposer dg H tr) {x : Fin sp.n}
    {s : Nat} (hx : x ∈ H (sp.ts s + 6 * sp.Δ)) (hw : tr.awake x (sp.ts s + 6 * sp.Δ))
    (hj : tr.JoinedAt x (sp.ts s + 6 * sp.Δ)) :
    ∃ k ℓ, SA.UpdateAt tr.projAC x k s ℓ := by
  have hd : (0 : Time) ≤ sp.ts s + 6 * sp.Δ := by
    have := ts_natCast_nonneg (sp := sp) s
    linarith [sp.toParams.hΔ]
  obtain ⟨k, ℓ, hu⟩ := Compose.update_of_awake_joined (hrun.upTo hd) hx ⟨hw, le_rfl⟩
    (joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hu
  exact ⟨k, ℓ, ((sa_updateAt_upTo hrun.time_mono).1 hu).2⟩

/-- A block held while honest below a block of the tree of a node honest at a cut is below it in
that node's store (the static `honest_held_anc` on the prefix through the cut). -/
private theorem honest_held_anc_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {A W : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocksAt H) A W)
    (hW : W ∈ (tr.state y i).fg.tree) : (tr.state y i).fg.Anc A W := by
  have hd := hrun.time_nonneg i
  have hst : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono hk.le
  have hWU : W ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := ⟨y, hy, i, hst ▸ hW⟩
  have h' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hWU h
  have := Compose.honest_held_anc (hrun.upTo hd) (hnc.upTo _) hy h' (hst ▸ hW)
  rwa [hst] at this

/-- **A later update adopts an origin within `b`** (`s' > s`), charged at the update's cut
`d = t_{s'} + 6Δ`: `Σ.F` is compatible with `P` (S1); when `P ⪯ Σ.F`, the second disjunct holds;
otherwise the slot-`s'` voters still honest at `d` have votes extending `P` (S2), held and resolved
at the update, so `P` is in the frame with a strict majority, the deepest majority block above
`Σ.F` extends it, is not vetoed, and the record moves to it or keeps a deeper one. -/
theorem update_adopts_origin_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPo : OriginWithin tr H P s b)
    (hPU : P ∈ tr.HonestBlocksAt H) {y : Fin sp.n} {k₀ s' : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time k₀)) (hss : s < s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocksAt H) P E ∨
        Anc (tr.HonestBlocksAt H) P (tr.state y (k₀ + 1)).fg.F) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg k₀
  have ht : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
  set d := tr.time k₀
  have hcount : (H d)ᶜ.ncard < (VotersAt tr H s' d).ncard :=
    faults_lt_voters hrun hnc hB (by rw [ht]; linarith) hb (by rw [ht])
  have hcut : ∀ k < k₀ + 1, tr.time k ≤ d := fun k hk => hrun.time_mono (by omega)
  have hvb : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s' → tr.time j ≤ b := by
    intro x j e hv hs
    obtain ⟨hx, ℓx, hc, he⟩ := hVoteAt_iff.1 hv
    have h := (cast_head_fcRoot_at hrun hnc hx ⟨hc, he⟩).2
    rw [hs] at h
    linarith
  -- the update's cut
  obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hu.1.2
  obtain rfl : c = .ac ℓ := by
    cases c with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨hfr, hstep, hfg, -⟩ := hrun.cutLaw y k₀ (.ac ℓ) ⟨hu.1.1, hc⟩ hy
  have hpost : tr.state y (k₀ + 1) = tr.post k₀ := by
    rw [Trace.state, ite_eq_left ⟨hu.1.1, by rw [hc]; exact Option.some_ne_none _⟩]
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  have hFeq : ℓ.frame.F = (tr.state y k₀).fg.F := by rw [hfr]; rfl
  have hFU : (tr.state y k₀).fg.F ∈ tr.HonestBlocksAt H := hFeq ▸ hHB hΦ.rooted.1
  -- `Σ.F` and `P` are compatible (both on the origin chain)
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hPU hFU
      (onOriginChainWithin_iff.2 (Or.inr ⟨P, s, hPo, Relation.ReflTransGen.refl⟩))
      (hinv.caches_at_cut hrun hb0 hy fun k hk => (hcut k (by omega)).trans hb).1 with hPF | hFP
  · -- `Σ.F` has passed `P`
    obtain ⟨E, hE, hEr, -⟩ := hinv.record y (k₀ + 1) d hd hcut hb hy
    refine ⟨E, ⟨y, k₀ + 1, d, hd, hcut, hy, hE⟩, hEr, Or.inr ?_⟩
    rw [hpost, hfg]
    exact hPF
  -- every slot-`s'` vote of a voter still honest at `d` is held and resolved, its head above `P`
  have hbatch : ∀ x j e, HVoteAt tr H x j e → x ∈ H d → e.msg.slot = s' →
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Anc (tr.HonestBlocksAt H) P Hd ∧
        e.msg ∈ (tr.projAC.state y k₀).pool s' ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s' + 2 * sp.Δ) := by
    intro x j e hv hxd hes
    obtain ⟨Hd, hHdU, hHdr, hPHd⟩ := hinv.vote_extends P s hPo x j e hv (hvb x j e hv hes)
      (by omega)
    obtain ⟨hHdt, hpool, hres⟩ := honest_vote_at_update_at hrun hnc hsync hy hu hb hHdU
      (hFeq ▸ hFP.trans hPHd) hv hxd hes hHdr.symm
    exact ⟨Hd, hHdt, hHdr, hPHd, hpool, hres⟩
  -- `P` is in the frame, above `Σ.F`
  have hPt : P ∈ ℓ.frame.tree := by
    obtain ⟨x, hxv⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨hxd, j, e, hv, hes⟩ := votersAt_iff.1 hxv
    obtain ⟨Hd, hHdt, -, hPHd, -⟩ := hbatch x j e hv hxd hes
    rw [hfr] at hHdt ⊢
    have hPHd' := honest_held_anc_at hrun hnc hy hPHd hHdt.1
    have hPfg : P ∈ (tr.state y k₀).fg.tree := by
      by_cases hne : P = Hd
      · exact hne ▸ hHdt.1
      · exact (Goldilocks.Anc.mem hPHd' hne).1
    exact ⟨hPfg, honest_held_anc_at hrun hnc hy hFP hPfg⟩
  have hFPΦ : ℓ.frame.Anc ℓ.frame.F P := hΦ.rooted.2 P hPt
  -- `P` has a strict majority at the update's test, counted at `d`
  have hmaj : (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s'}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s' P := by
    rw [← projAC_state_at hrun hy]
    set A := tr.projAC.state y k₀
    set Hv := VotersAt tr H s' d
    have hone : ∀ x j e, HVoteAt tr H x j e → x ∈ H d → e.msg.slot = s' →
        ∀ v ∈ A.pool s', v.val = x → v = e.msg := by
      intro x j e hv hxd hs v hvp hvx
      obtain ⟨j', -, e', hv', rfl⟩ := pool_vote_at hrun hnc hy hvp (hvx ▸ hxd)
      have hs' := state_pool_slot_at hrun hnc hy s' _ hvp
      rw [hvx] at hv'
      exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
        (one_vote_per_slot_at hrun hnc hv' hv (hs'.trans hs.symm)).2
    have hsupp : Hv ⊆ SA.supporters ℓ.frame ⟨{v | v ∈ A.pool s'}, {v | v ∈ A.pool s' ∧
        SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s' + 2 * sp.Δ)}⟩ s' P := by
      intro x hxv
      obtain ⟨hxd, j, e, hv, hs⟩ := votersAt_iff.1 hxv
      obtain ⟨Hd, hHdt, hHdr, hPHd, hvp, hres⟩ := hbatch x j e hv hxd hs
      obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
      have hval := (castAt_spec_at hrun hnc hx ⟨hcx, hex⟩).1
      refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, Hd, hHdt, hHdr,
        SA.anc_tree_of_anc_U hU hΦ hHB hPt hPHd hHdt⟩
      rintro ⟨v, hv₁, v', hv', hne, hvx, hv'x⟩
      exact hne ((hone x j e hv hxd hs v hv₁ hvx).trans (hone x j e hv hxd hs v' hv' hv'x).symm)
    have hvot : SA.voters {v | v ∈ A.pool s'} ⊆ Hv ∪ (H d)ᶜ := by
      rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H d
      · obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hv hw
        exact Or.inl (votersAt_iff.2 ⟨hw, j, e, he, state_pool_slot_at hrun hnc hy s' _ hv⟩)
      · exact Or.inr hw
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le Hv (H d)ᶜ
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    change _ < 2 * (SA.supporters ℓ.frame _ s' P).ncard
    omega
  -- the result is the deepest majority block above `Σ.F`, which extends `P`
  set A := (tr.state y k₀).ac
  set S := {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
    (SA.voters {v | v ∈ A.pool s'}).ncard < 2 * SA.confirmationScore sp A ℓ.frame s' B}
  have hS : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s'}, {v | v ∈ A.pool s' ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s' + 2 * sp.Δ)}⟩
  have hcs : ∀ B, SA.confirmationScore sp A ℓ.frame s' B = (SA.supporters ℓ.frame V s' B).ncard :=
    fun _ => rfl
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ C ∈ S, Compatible ℓ.frame.tree B C := fun B hB C hC =>
    SA.majority_chain sp _ ℓ.frame V s' B C hΦ hsub hB.1 hC.1 (hcs B ▸ hB.2.2) (hcs C ▸ hC.2.2)
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hS ⟨P, hPt, hFPΦ, hmaj⟩
  have hPD := SA.anc_deepest hΦ hS hch hD P ⟨hPt, hFPΦ, hmaj⟩
  have hC : SA.getConfirmation sp A ℓ.frame s' = some D := hD
  have hv := result_not_vetoed_at hrun hnc hb0 hinv hy hu hb hC
  -- the record moves to the result, or keeps a deeper one
  obtain ⟨-, hcall, ht', hj⟩ := hu
  rw [projAC_state_at hrun hy] at hj
  classical
  have hrec : (tr.state y (k₀ + 1)).ac.latestConfirmed =
      if SA.AncR ℓ.frame D A.latestConfirmed then A.latestConfirmed else D.root := by
    rw [hpost, show (tr.post k₀).ac = _ from (congrArg Prod.fst hstep).symm, hcall]
    exact Compose.acOnTick_update_record y ht' hj hC hv
  have hDt : D ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  split_ifs at hrec with hA
  · obtain ⟨R, hR, hRr, hDR⟩ := hA
    exact ⟨R, hHB hR, hRr.trans hrec.symm, Or.inl (Anc.mono hHB (hPD.trans hDR))⟩
  · exact ⟨D, hHB hDt, hrec.symm, Or.inl (hPD.mono hHB)⟩

/-- **A strictly later update adopts the proposal** (`s < s'`): `P` is the result of the update
of slot `s` of a node honest, awake and joined at `t_s + 6Δ = t_{s+1} + 2Δ` (the `2Δ` slot-point
count `SleepyBounds.late`), hence an origin of label `s`. -/
theorem later_update_adopts_gt_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ s' : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time k₀)) (hss : s < s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocksAt H) P E ∨
        Anc (tr.HonestBlocksAt H) P (tr.state y (k₀ + 1)).fg.F) := by
  have hΔ := sp.toParams.hΔ
  have ht : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + 6 * sp.Δ ≤ b := by
    have := (SA.ts_le_iff sp).2 (show (s : Int) ≤ s' by exact_mod_cast hss.le)
    linarith
  have hT : sp.ts (s + 1 : Nat) + 2 * sp.Δ = sp.ts s + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hf := hB.late (s + 1) (sp.ts (s + 1 : Nat) + 2 * sp.Δ) le_rfl (by rw [hT]; exact hsb)
    (by linarith)
  rw [hT] at hf
  obtain ⟨x, hx, hw, hj⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hf).ne'
  obtain ⟨kx, ℓx, hux⟩ := update_of_awake_joined_at hrun hx hw hj
  have hkx : tr.time kx = sp.ts s + 6 * sp.Δ := hux.2.2.1
  have hxk : x ∈ H (tr.time kx) := hkx ▸ hx
  obtain ⟨hC, -⟩ := adopt_result_at hrun hnc hb0 hsync hB hinv hp hP hPs hxk hux (by linarith)
  have hPt : P ∈ ℓx.frame.tree := (SA.deepest_mem hC).1.1
  have hPU : P ∈ tr.HonestBlocksAt H := (frameIn_at hrun hnc hxk hux.1).2 hPt
  have hxb : tr.time kx ≤ b := by linarith
  have hPo : OriginWithin tr H P s b := originWithin_iff.2
    ⟨x, kx, _, hxk, hxb, Or.inl ⟨ℓx, hux, by rw [projAC_state_at hrun hxk]; exact hC, rfl⟩⟩
  exact update_adopts_origin_at hrun hnc hb0 hinv hsync hB hPo hPU hy hss hu hb

/-- **An update of any slot `s' ≥ s` adopts the proposal** of slot `s`, through `b`. -/
theorem later_update_adopts_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ s' : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time k₀)) (hss : s ≤ s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocksAt H) P E ∨
        Anc (tr.HonestBlocksAt H) P (tr.state y (k₀ + 1)).fg.F) := by
  rcases hss.lt_or_eq with hlt | rfl
  · exact later_update_adopts_gt_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hlt hu hb
  · obtain ⟨E, hE, hEr, hPE⟩ := update_adopts_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb
    exact ⟨E, hE, hEr, Or.inl hPE⟩

end Consensus.Goldilocks.Compose.Growing

end
