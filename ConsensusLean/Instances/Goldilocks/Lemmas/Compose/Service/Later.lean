module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Adopt
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: a later update adopts the honest proposal

For R.2 (`IncludeSleepy`, a reader that slept through `t_s + 6Δ`): after an honest node's joined
update of any slot `s' ≥ s`, its record names a block extending the honest proposal `P` of slot
`s`, or its `Σ.F` extends `P` (then the record, if in the frame, extends `Σ.F`, and otherwise the
confirmed tip is `Σ.F`). For `s' = s` this is `update_adopts`. For `s' > s`, `P` is a regular
origin (the update of slot `s` at an honest joined node adopts it), every honest vote of slot `s'`
extends it (S2, `SleepyInvariantUpTo.vote_extends`), the honest batch of slot `s'` reaches the
joined updater resolved, so when `P` is in the frame it has a strict majority and the result
extends it, and is not vetoed; when `Σ.F` has passed `P`, the second disjunct holds. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} (y : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 = (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x
        .proposal).1 t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- **An honest validator awake and joined at `t_s + 6Δ` runs the update of slot `s`** there: its
tick at that public time starts with `ac_on_tick`, joined. -/
theorem update_of_awake_joined {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} (hx : x ∈ H) {s : Nat} (hw : tr.awake x (sp.ts s + 6 * sp.Δ))
    (hj : tr.JoinedAt x (sp.ts s + 6 * sp.Δ)) :
    ∃ k ℓ, SA.UpdateAt tr.projAC x k s ℓ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 : (0 : Time) ≤ sp.ts s := by
    simp only [SAParams.ts]
    exact mul_nonneg (by linarith) (Int.natCast_nonneg s)
  obtain ⟨j, c, hj'⟩ := hrun.tick_of_awake x hx _ (by linarith)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 6)
      (by simp only [SAParams.ts]; ring)) hw
  obtain ⟨-, hk, -⟩ := hj'
  have hlen :
      0 < (Node.exec proposer dg x (tr.state x j) (sp.ts s + 6 * sp.Δ) (.tick c)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg x (tr.state x j) (sp.ts s + 6 * sp.Δ) (.tick c)).2[0]'hlen =
      (Node.acCall x (tr.state x j) (sp.ts s + 6 * sp.Δ) .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  have hnr : ¬ tr.RestartAt x j := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have htj : tr.projAC.time j = sp.ts s + 6 * sp.Δ := ht0
  refine ⟨j, ℓ, ⟨hn0, by simp [RunTrace.projAC, hl, RunTrace.acLabel]⟩, hcall, htj, ?_⟩
  rw [projAC_state hrun.toLocalRun hx j, htj]
  exact ((joined_projection_from hrun hx _).2.1 j ⟨_, hn0, hl⟩ hnr ht0).1 hj

/-- **A later update adopts an origin within `b`** (`s' > s`).
Every honest slot-`s'` vote occurs before the bounded update and extends the origin (S2), and
`Σ.F` is compatible with it (S1). When `P ⪯ Σ.F`, the second disjunct holds. Otherwise each honest
slot-`s'` vote's head is above `Σ.F`, so it is held and resolved at the update
(`honest_vote_at_update`); then `P` is in the frame with a strict majority (the honest slot-`s'`
voters support it, the rest are faulty), the deepest majority block above `Σ.F` extends it, is not
vetoed (`result_not_vetoed_before`), and the record moves to it or keeps a deeper one. -/
theorem update_adopts_origin_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {b : Time}
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPo : OriginWithin tr H P s b)
    (hPU : P ∈ tr.HonestBlocks H) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ s' : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hss : s < s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b)
    (hfb : tr.FaultBound H (sp.ts s' + sp.Δ)) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y (k₀ + 1)).fg.F) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcount : Hᶜ.ncard <
      {x | x ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s'}.ncard := by
    refine lt_of_lt_of_le hfb (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨j, e, hv, hs, -⟩ :=
      vote_of_awake_joined hrun hnc hx (mayVote_stock hrun hnc hx _) hw hj
    exact ⟨hx, j, e, hv, hs⟩
  have hcut : ∀ k < k₀ + 1, tr.time k ≤ b := fun k hk =>
    (hrun.time_mono (by omega)).trans hb
  have hvb : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s' →
      tr.time j ≤ b := by
    rintro x hx j e ⟨ℓx, hc, he⟩ hs
    have ht := (cast_head_fcRoot hr hx ⟨hc, he⟩).2
    rw [hs] at ht
    have hu' : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
    change tr.time j ≤ _ at ht
    linarith
  -- the update's cut
  obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hu.1.2
  obtain rfl : c = .ac ℓ := by
    cases c with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨hfr, hstep, hfg, -⟩ := hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hu.1.1, hc⟩
  have hpost : tr.state y (k₀ + 1) = tr.post k₀ := by
    rw [Trace.state, ite_eq_left ⟨hu.1.1, by rw [hc]; exact Option.some_ne_none _⟩]
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy k₀
  have hHB : ℓ.frame.tree ⊆ tr.HonestBlocks H := fun X hX =>
    ⟨y, hy, k₀, by rw [hfr] at hX; exact hX.1⟩
  have hFeq : ℓ.frame.F = (tr.state y k₀).fg.F := by rw [hfr]; rfl
  have hFU : (tr.state y k₀).fg.F ∈ tr.HonestBlocks H := hFeq ▸ hHB hΦ.rooted.1
  -- `Σ.F` and `P` are compatible (both on the origin chain)
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hPU hFU
      (onOriginChainWithin_iff.2 (Or.inr ⟨P, s, hPo, Relation.ReflTransGen.refl⟩))
      (hinv.caches y hy k₀ (fun k hk => hcut k (by omega))).1 with hPF | hFP
  · -- `Σ.F` has passed `P`
    obtain ⟨E, hE, hEr, -⟩ := hinv.record y hy (k₀ + 1) hcut
    refine ⟨E, ⟨y, hy, k₀ + 1, hE⟩, hEr, Or.inr ?_⟩
    rw [hpost, hfg]
    exact hPF
  -- every honest slot-`s'` vote is held and resolved at the update, its head above `P`
  have hbatch : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s' →
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Anc (tr.HonestBlocks H) P Hd ∧
        e.msg ∈ (tr.projAC.state y k₀).pool s' ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s' + 2 * sp.Δ) := by
    intro x hx j e hv hes
    obtain ⟨Hd, hHdU, hHdr, hPHd⟩ := hinv.vote_extends P s hPo x hx j e hv
      (hvb x hx j e hv hes) (by omega)
    obtain ⟨hHdt, hpool, hres⟩ := honest_vote_at_update_before hrun' hsync hb
      hy hu hHdU (hFeq ▸ hFP.trans hPHd) hx hv hes hHdr.symm
    exact ⟨Hd, hHdt, hHdr, hPHd, hpool, hres⟩
  -- `P` is in the frame, above `Σ.F`
  have hPt : P ∈ ℓ.frame.tree := by
    obtain ⟨x, hx, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero
      (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨Hd, hHdt, -, hPHd, -⟩ := hbatch x hx j e hv hes
    rw [hfr] at hHdt ⊢
    have hPHd' := honest_held_anc hrun hnc hy hPHd hHdt.1
    have hPfg : P ∈ (tr.state y k₀).fg.tree := by
      by_cases hne : P = Hd
      · exact hne ▸ hHdt.1
      · exact (Goldilocks.Anc.mem hPHd' hne).1
    exact ⟨hPfg, honest_held_anc hrun hnc hy hFP hPfg⟩
  have hFPΦ : ℓ.frame.Anc ℓ.frame.F P := hΦ.rooted.2 P hPt
  -- `P` has a strict majority at the update's test
  have hmaj : (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s'}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s' P := by
    rw [← projAC_state hrun.toLocalRun hy]
    set A := tr.projAC.state y k₀
    set Hv := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s'}
    have hcount : Hᶜ.ncard < Hv.ncard := hcount
    have hone : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s' →
        ∀ v ∈ A.pool s', v.val = x → v = e.msg := by
      intro x hx j e hv hs v hvp hvx
      obtain ⟨j', -, e', hv', rfl⟩ := hrun'.honest.pool_vote y hy k₀ s' v hvp (hvx ▸ hx)
      have hs' := SA.state_pool_slot sp hr hy k₀ s' _ hvp
      rw [hvx] at hv'
      exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
        (SA.one_vote_per_slot sp _ ro H _ _ hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2
    have hsupp : Hv ⊆ SA.supporters ℓ.frame ⟨{v | v ∈ A.pool s'}, {v | v ∈ A.pool s' ∧
        SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s' + 2 * sp.Δ)}⟩ s' P := by
      rintro x ⟨hx, j, e, hv, hs⟩
      obtain ⟨Hd, hHdt, hHdr, hPHd, hvp, hres⟩ := hbatch x hx j e hv hs
      obtain ⟨ℓx, hcx, hex⟩ := hv
      have hval := (SA.castAt_spec hr hx ⟨hcx, hex⟩).1
      refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, Hd, hHdt, hHdr,
        SA.anc_tree_of_anc_U hU hΦ hHB hPt hPHd hHdt⟩
      rintro ⟨v, hv, v', hv', hne, hvx, hv'x⟩
      exact hne ((hone x hx j e ⟨ℓx, hcx, hex⟩ hs v hv hvx).trans
        (hone x hx j e ⟨ℓx, hcx, hex⟩ hs v' hv' hv'x).symm)
    have hvot : SA.voters {v | v ∈ A.pool s'} ⊆ Hv ∪ Hᶜ := by
      rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H
      · obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote y hy k₀ s' _ hv hw
        exact Or.inl ⟨hw, j, e, he, SA.state_pool_slot sp hr hy k₀ s' _ hv⟩
      · exact Or.inr hw
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le Hv Hᶜ
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
  have hv := result_not_vetoed_before hrun hnc hinv hy hu hb hC
  -- the record moves to the result, or keeps a deeper one
  obtain ⟨-, hcall, ht, hj⟩ := hu
  rw [projAC_state hrun.toLocalRun hy] at hj
  classical
  have hrec : (tr.state y (k₀ + 1)).ac.latestConfirmed =
      if SA.AncR ℓ.frame D A.latestConfirmed then A.latestConfirmed else D.root := by
    rw [hpost, show (tr.post k₀).ac = _ from (congrArg Prod.fst hstep).symm, hcall]
    exact acOnTick_update_record y ht hj hC hv
  have hDt : D ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  split_ifs at hrec with hA
  · obtain ⟨R, hR, hRr, hDR⟩ := hA
    exact ⟨R, hHB hR, hRr.trans hrec.symm, Or.inl (Anc.mono hHB (hPD.trans hDR))⟩
  · exact ⟨D, hHB hDt, hrec.symm, Or.inl (hPD.mono hHB)⟩

/-- An honest proposal becomes a regular origin at its slot's update; the bounded
origin-adoption theorem then handles every strictly later update. -/
theorem later_update_adopts_gt_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time}
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time),
      sp.ts s + d ≤ b → tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ s' : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hss : s < s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y (k₀ + 1)).fg.F) := by
  have hΔ := sp.toParams.hΔ
  have hsb : sp.ts s + 6 * sp.Δ ≤ b := by
    have := (SA.ts_le_iff sp).2 (show (s : Int) ≤ s' by exact_mod_cast hss.le)
    have ht : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
    linarith
  have hT : sp.ts (s + 1 : Nat) + 2 * sp.Δ =
      sp.ts s + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hf := hfb (s + 1) (2 * sp.Δ) (by simp) (by rw [hT]; exact hsb)
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at hf
  rw [hT] at hf
  obtain ⟨x, hx, hw, hj⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hf).ne'
  obtain ⟨kx, ℓx, hux⟩ := update_of_awake_joined hrun hx hw hj
  obtain ⟨hC, -⟩ := adopt_result_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hx hux
    (by have ht : tr.time kx = sp.ts s + 6 * sp.Δ := hux.2.2.1; linarith) hstock
  have hfx : ℓx.frame = Node.frame (tr.state x kx) := by
    obtain ⟨⟨hn, hl⟩, -⟩ := hux
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓx := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    exact (hrun.cutLaw x hx kx (.ac ℓx) ⟨hn, hc⟩).1
  have hPt : P ∈ ℓx.frame.tree := (SA.deepest_mem hC).1.1
  rw [hfx] at hPt
  have hxb : tr.time kx ≤ tr.time k₀ := by
    have hx' : tr.time kx = sp.ts s + 6 * sp.Δ := hux.2.2.1
    have hu' : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
    have hle : sp.ts s ≤ sp.ts s' := (SA.ts_le_iff sp).2 (by exact_mod_cast hss.le)
    linarith
  have hPo : OriginWithin tr H P s b := originWithin_iff.2
    ⟨x, hx, kx, _, hxb.trans hb, Or.inl ⟨ℓx, hux,
      by rw [projAC_state hrun.toLocalRun hx]; exact hC, rfl⟩⟩
  exact update_adopts_origin_before hrun hnc hinv
    hsync.ac hPo ⟨x, hx, kx, hPt.1⟩ hy hss hu hb
    (hfb s' sp.Δ (by simp) (by
      have ht : tr.time k₀ = sp.ts s' + 6 * sp.Δ := hu.2.2.1
      linarith))

/-- An update inside the horizon adopts an honest proposal of any earlier slot. -/
theorem later_update_adopts_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time),
      sp.ts s + d ≤ b → tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ s' : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hss : s ≤ s')
    (hu : SA.UpdateAt tr.projAC y k₀ s' ℓ) (hb : tr.time k₀ ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      (Anc (tr.HonestBlocks H) P E ∨ Anc (tr.HonestBlocks H) P (tr.state y (k₀ + 1)).fg.F) := by
  rcases hss.lt_or_eq with hlt | rfl
  · exact later_update_adopts_gt_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hy hlt hu hb
      hstock
  · obtain ⟨E, hE, hEr, hPE⟩ := update_adopts_before hrun hnc hb0 hsync hfb hinv
      hp hP hPs hpj hy hu hb hstock
    exact ⟨E, hE, hEr, Or.inl hPE⟩

end Consensus.Goldilocks.Compose

end
