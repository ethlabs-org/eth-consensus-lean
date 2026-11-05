module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the next vote batch (extending `V_s` to `V_{s+1}`)

Fix an honest slot-`(s+1)` vote, and assume `P_{s+1}`, `V_s` and that the honest slot-`(s+1)` votes
at earlier cuts extend the block in question (the first-bad-vote argument). The lock and later-batch
steps are stated for a block `B` with the hypotheses they use, so that the proposal-adoption
bootstrap applies them to the protected proposal; for an origin `C` of label `j ≤ s`:

* **Locks** (`vote_locks_compatible_upTo`): every live lock block after the unlocking is compatible
  with `C`: a lock of slot at most `s` sits below an origin of its slot, compared with `C` by
  `P_{s+1}`; one of slot `s + 1` is optimistic and was selected over earlier honest
  slot-`(s+1)` votes, which extend `C` (`SA.locks_compatible`).
* **First transfer** (`first_transfer_step_upTo`, `j = s`): `C` at or below `fc_root` (the vote's
  head extends `fc_root`), or, with `vote_frame` and the transport (`result_carry_before`,
  `optimistic_carry_before`, `result_writer_pool_before`), A1.8 for a result and A1.4 (a) for an
  optimistic selection.
* **Later batch** (`later_transfer_step_upTo`, `j < s`): the slot-`s` honest votes all extend `C`
  (`V_s`); the more than `f` of them cast by the validators awake and joined at `t_s + Δ` are held
  and resolved at the vote freeze, and only faulty seats oppose or equivocate, so `C`'s children
  towards the vote win the walk (`SA.isBest_of_majority`, `SA.anc_getHead`).
* `votes_below_succ`: strong induction on the cut index over the slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-! ### Over an SA trace -/

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The later-batch walk for a selected honest slot-`s` batch: its votes extend `B`, are
carried at the read point, and outnumber half of a set covering all merged voters.
Viability and compatibility of all live locks then make the successor vote extend `B`. -/
theorem vote_extends_of_counted_batch (hrun : SA.ACRun proposer tr H U)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n FGP}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H)
    (hSXv : ∀ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', SA.VoteAt tr x j e' → e'.msg.slot = s → SA.VoteExtends U e'.msg B)
    (hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ W)
    (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : SA.CarryAt tr U y i e s
      {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    SA.VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := SA.castAt_spec hr hy hc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := SA.voteDomain_anc hr hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  -- The selected honest batch supplies supporters of `B` at `y`.
  have hsupp : SX ⊆
      SA.supporters ℓ.frame (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
    intro w hwSX
    have hw := hSXH hwSX
    obtain ⟨j, e', hv, hvs⟩ := hSXv w hwSX
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (SA.castAt_spec hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} :=
      ⟨w, hwSX, j, e', hv, rfl, hvs⟩
    -- `y` holds `e'.msg` itself (an honest validator has one slot-`s` vote)
    have hheld : SA.HeldBefore e.readPoint e'.msg (sp.ts s + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u, u.slot = s → SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
            u ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
          intro u hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SA.SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega,
              ite_false]
            simpa [hus] using hu.1
          · simpa [SA.freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          SA.honest_merged_vote hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := (SA.one_vote_per_slot sp) FGP ro H U tr hr w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := SA.honest_head hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hwSX j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := SA.carried_supporter hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (SA.honest_not_equivocator hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  have hcore := SA.anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB =>
        SA.voteDomain_subset_tree hB) hdomA hviab.voteDomain
    hlocks fun X' Cx hCx hp hCxC =>
      SA.isBest_of_majority hΦ (SA.merged_support_subset hr hy hc (s + 1)) (fun B hB =>
          (SA.voteDomain_subset_tree hB.1))
        hsupp hW hcount hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = SA.getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- The full honest batch is a counted batch when it outnumbers the faulty seats. -/
theorem vote_extends_of_batch (hrun : SA.ACRun proposer tr H U)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n FGP}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    (hall : ∀ x ∈ H, ∀ j e', SA.VoteAt tr x j e' → e'.msg.slot = s → SA.VoteExtends U e'.msg B)
    (hcount : Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s}.ncard)
    (hcarry : SA.CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    SA.VoteExtends U e.msg B := by
  let SX : Set (Fin sp.n) := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s}
  have hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hrun hy hc hv hw
      exact Or.inl ⟨hw, j, e', hv', by
        rw [he']; exact SA.merged_vote_slot hrun.localRun hy hc v hv⟩
    · exact Or.inr hw
  have hcount' : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    change Hᶜ.ncard < SX.ncard at hcount
    omega
  have hset : {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} =
      {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} := by
    ext v
    constructor
    · rintro ⟨x, hx, j, e', hv, rfl, hs'⟩
      exact ⟨x, ⟨hx, j, e', hv, hs'⟩, j, e', hv, rfl, hs'⟩
    · rintro ⟨x, hx, j, e', hv, he, hs'⟩
      exact ⟨x, hx.1, j, e', hv, he, hs'⟩
  rw [hset] at hcarry
  exact vote_extends_of_counted_batch hrun hy hc hs hviab (fun _ hx => hx.1)
    (fun _ hx => hx.2) (fun x hx => hall x hx.1) hW hcount' hcarry hlocks

end SA

/-! ### Over a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- An origin is an honest block: a block of its writer's frame. -/
private theorem origin_mem (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hC : Origin tr H C s) :
    C ∈ tr.HonestBlocks H := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨x, hx, i, CV, ⟨ℓ, hupd, hconf, -⟩ | ⟨ℓ, A, hpt, -, hsel, -⟩⟩ := origin_iff.1 hC
  · exact (SA.frameIn_of_callAt hr hx hupd.1).2 (SA.deepest_mem hconf).1.1
  · unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.frameIn_of_callAt hr hx hpt.1).2 (SA.deepest_mem hsel).1.1

/-- An honest vote of a slot `m ≤ s` is cast by `t_s + Δ`. -/
private theorem vote_time_le (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x k e) {s : Nat} (hs : e.msg.slot ≤ s) :
    tr.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  have h : tr.time k ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hx ⟨hc, he⟩).2
  have h2 : sp.ts (e.msg.slot : Int) ≤ sp.ts (s : Int) := by
    unfold SAParams.ts
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by linarith [sp.toParams.hΔ])
  linarith

variable {b : Time} {s₀ : Nat}

/-- From slot `0`, no head was accepted before `t_0 = 0`: the catch-up hypothesis is vacuous. -/
private theorem hold_zero (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {T : Time} :
    ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts (0 : Nat) →
      Anc (tr.HonestBlocks H) Φ.F B → SA.AcceptedBefore tr.projAC y B T :=
  fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m))

/-- The honest voters outnumber the faults on the window from slot `s₀ ≤ s` to `b`. -/
private theorem faults_lt_honest_voters_win (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s)
    (hs : sp.ts s + sp.Δ ≤ b) :
    Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}.ncard := by
  refine lt_of_lt_of_le (faults_lt_awake_joined_win hwin hs₀ hs) (Set.ncard_le_ncard ?_)
  rintro x ⟨hx, hw, hj⟩
  obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined hrun hnc hx hw hj
  exact ⟨hx, k, e, hv, hs⟩

/-- `honest_batch_carry_upTo` on the window from slot `s₀ ≤ s` to `b`, with the heads accepted
before `t_{s₀}` caught up (`hold`). -/
private theorem honest_batch_carry_win (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  have hsync := syncAC_of_window hrun hwin (a := sp.ts s₀) (b' := sp.ts s + 2 * sp.Δ) le_rfl
    (by linarith)
  -- each vote of the batch, with its own validator as the writer
  have hone : ∀ v ∈ {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s},
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s {v} := by
    rintro v ⟨x, hx, k, e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk := (SA.castAt_spec hr hx ⟨hck, he'⟩).2.1
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hck, he'⟩
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall x hx k e' ⟨ℓk, hck, he'⟩ hvs
    obtain rfl : Hd = Hv :=
      hU.1 ((SA.frameIn_of_callAt hr hx hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.projAC.time k < sp.ts s + 2 * sp.Δ := by
      rw [hvs] at hkt
      linarith
    refine carryAt_of_writer_win hr hsync (ts_le_ts hs₀) le_rfl hx hy hc hs ?_
      (acceptedBefore_of_old hrun hold hx)
    rintro v rfl
    refine ⟨hvs, ⟨k, ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases frame_anc_accepted hr hx k ℓk hck Hd hHd Hd .refl with hg | ⟨k', hk', hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k', hacc, lt_of_le_of_lt (hr.time_mono hk') hkt'⟩
  exact ⟨hr.awake_of_call y hy i ℓ hc.1, (SA.castAt_spec hr hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- The honest batch reaches a next-slot vote using recipient service within the horizon. -/
theorem honest_batch_carry_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsync : SleepyServiceBefore tr H ΔF b)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hone : ∀ v ∈ {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s},
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s {v} := by
    rintro v ⟨x, hx, k, e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk := (SA.castAt_spec hr hx ⟨hck, he'⟩).2.1
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hck, he'⟩
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall x hx k e' ⟨ℓk, hck, he'⟩ hvs
    obtain rfl : Hd = Hv :=
      hU.1 ((SA.frameIn_of_callAt hr hx hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.projAC.time k < sp.ts s + 2 * sp.Δ := by
      rw [hvs] at hkt
      linarith
    refine carryAt_of_writer_before hr hsync.ac
      hx hy hc hs hib ?_
    rintro v rfl
    refine ⟨hvs, ⟨k, ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases frame_anc_accepted hr hx k ℓk hck Hd hHd Hd .refl with hg | ⟨k', hk', hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k', hacc, lt_of_le_of_lt (hr.time_mono hk') hkt'⟩
  exact ⟨hr.awake_of_call y hy i ℓ hc.1, (SA.castAt_spec hr hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- **The live locks at a slot-`(s+1)` vote are compatible with `B`**, with `f < n/2`: a block
compatible with every origin of a label in `[s₀, s]` whose event precedes the vote, with the live
lock blocks of the read-point locks of slots `< s₀` (`hlow`), and that the earlier honest
slot-`(s+1)` votes extend. -/
private theorem vote_locks_compatible_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, OriginBefore tr H C j i → s₀ ≤ j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hlow : ∀ L ∈ SA.liveLockBlocks sp {l ∈ e.readPoint.locks | l.slot < s₀} ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hsi : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hc).2.1
  -- compatibility with `B` passes to ancestors
  have down : ∀ {X Y}, Anc (tr.HonestBlocks H) X Y → Compatible (tr.HonestBlocks H) Y B →
      Compatible (tr.HonestBlocks H) X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hlL⟩
  by_cases hl₀s : l₀.slot < s₀
  · exact hlow L ⟨hL, _, ⟨l₀, ⟨hl₀, hl₀s⟩, B₀, hB₀, hB₀r, hlive, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (SA.anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · -- a lock of slot in `[s₀, s]` sits below a stored lock, below an origin of its slot
    obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      SA.readPoint_locks_below_stored hr hy hc (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    rw [projAC_state hrun.toLocalRun hy i] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hy i l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 ⟨y, hy, i, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    exact down ((Anc.mono hΦU hA).trans hL₁O) (hBc O l₁.slot hO (by omega) (by omega)).symm
  · -- a lock of slot `s + 1` or later is optimistic, over earlier honest slot-`(s+1)` votes
    obtain ⟨Φ', A, D, -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      SA.lock_origin_readPoint hrun' hy hc l₀ hl₀ (by rw [hs]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (SA.origin_compatible hU hΦ'U h34 hf fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (tr.time j) := (SA.castAt_spec hr hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      SA.slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

/-- **The live locks at a slot-`(s+1)` vote at a time `≤ b` are compatible with `B`**, a block
compatible with every origin within `b` of label at most `s` that the earlier honest
slot-`(s+1)` votes extend. -/
theorem vote_locks_compatible_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  refine vote_locks_compatible_of (s₀ := 0) hrun hnc (two_faults_lt_of_prefix hpre) hy hc hs
    (fun C j hC _ hj => hBc C j (hC.within hib') hj) ?_ hE
  intro L hL
  obtain ⟨-, l, ⟨l₀, ⟨-, h⟩, -⟩, -⟩ := hL
  exact absurd h (Nat.not_lt_zero _)


/-- **First transfer on a window** (§2.3): an honest slot-`(s+1)` vote at a time `≤ b` extends
an origin `C` within `b` of label `s ≥ s₀` that is in its viable voter tree or at or below
`fc_root` (`vote_frame`), with every live lock block compatible with `C`, when the heads accepted
before `t_{s₀}` are caught up (`hold`) and the earlier honest slot-`(s+1)` votes extend `C`. -/
private theorem first_transfer_win (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : OriginWithin tr H C s b)
    (hvf : C ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) C ℓ.frame.fcRoot)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L C)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  rcases hvf with hv | hCf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hCf.trans (Anc.mono hΦU hfHd)⟩
  have hF : Anc (tr.HonestBlocks H) ℓ.frame.F C := Anc.mono hΦU (hΦ.rooted.2 C hv.1.1)
  obtain ⟨x, hx, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · exact SA.result_transfer sp _ ro H _ tr.projAC proposer hrun' s x y i₀ i C CV ℓ e hx hR hy hc hs
      (result_carry_win hrun hnc hwin hx hs₀ hR hy hc hs hib hold hF) (Or.inl hv) hlocks
      (result_writer_pool_win hrun hnc hwin hx hs₀ hR hi₀ hy hc hs)
  · exact SA.optimistic_transfer_stored sp hrun' hx hO .refl (two_faults_lt_of_window hwin) hy
      hc hs (optimistic_carry_win hrun hnc hwin hx hs₀ hO hy hc hs hib hold hF) (Or.inl hv) hE

/-- **First transfer up to `b`** (§2.3): an honest slot-`(s+1)` vote at a time `≤ b` extends an
origin `C` within `b` of label `s` that the earlier honest slot-`(s+1)` votes extend. -/
theorem first_transfer_step_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : OriginWithin tr H C s b)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hCc : ∀ C' j, OriginWithin tr H C' j b → j ≤ s → Compatible (tr.HonestBlocks H) C C' :=
    fun C' j hC' hj => originsBelowUpTo_iff.1 hP C s C' j (by omega) (by omega) hC hC'
  obtain ⟨x', hx', k', e', hv', -, hs', hext'⟩ := honest_supporter_upTo hrun hnc hpre hC
  exact first_transfer_win hrun hnc hpre.window (Nat.zero_le s) hy hc hs hib (hold_zero hrun) hC
    (vote_frame_upTo hrun hnc hpre hP hy hc hs hib (origin_mem hrun hnc hC.origin) hCc
      ⟨x', hx', k', e', hv', hs', hext'⟩)
    (vote_locks_compatible_upTo hrun hnc hpre hy hc hs hib hCc hE) hE

/-- First transfer with service restricted to recipient deadlines within `b`. -/
theorem first_transfer_step_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : OriginWithin tr H C s b)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hCc : ∀ C' j, OriginWithin tr H C' j b → j ≤ s → Compatible (tr.HonestBlocks H) C C' :=
    fun C' j hC' hj => originsBelowUpTo_iff.1 hP C s C' j (by omega) (by omega) hC hC'
  obtain ⟨x', hx', k', e', hv', -, hs', hext'⟩ := honest_supporter_before hrun hnc hb hsync hfb hC
  have hvf := vote_frame_before hrun hnc hb hsync hfb hP hy hc hs hib
    (origin_mem hrun hnc hC.origin) hCc ⟨x', hx', k', e', hv', hs', hext'⟩
  have hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L C := by
    refine vote_locks_compatible_of (s₀ := 0) hrun hnc hf hy hc hs
      (fun C' j hC' _ hj => hCc C' j
        (hC'.within (fun k hk => (hrun.time_mono hk.le).trans hib)) hj) ?_ hE
    intro L hL
    obtain ⟨-, l, ⟨l₀, ⟨-, h⟩, -⟩, -⟩ := hL
    exact absurd h (Nat.not_lt_zero _)
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  rcases hvf with hv | hCf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hCf.trans (Anc.mono hΦU hfHd)⟩
  have hF : Anc (tr.HonestBlocks H) ℓ.frame.F C := Anc.mono hΦU (hΦ.rooted.2 C hv.1.1)
  obtain ⟨x, hx, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · exact SA.result_transfer sp _ ro H _ tr.projAC proposer hrun' s x y i₀ i C CV ℓ e hx hR hy hc hs
      (result_carry_before hrun hnc hsync hx hR hy hc hs hib hF) (Or.inl hv) hlocks
      (result_writer_pool_before hrun hnc hsync.ac
        hx hR hi₀ hy hc hs)
  · exact SA.optimistic_transfer_stored sp hrun' hx hO .refl hf hy hc hs
      (optimistic_carry_before hrun hnc hsync hx hO hy hc hs hib hF) (Or.inl hv) hE


/-- **Later batch on a window** (§2.4): an honest slot-`(s+1)` vote at a time `≤ b` (`s ≥ s₀`)
extends a block `B` that every honest slot-`s` vote extends, that is in its viable voter tree or
at or below `fc_root` (`vote_frame`), with every live lock block compatible with `B`, when the
heads accepted before `t_{s₀}` are caught up (`hold`). -/
private theorem later_transfer_win (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hvf : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  rcases hvf with hvB | hBf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  exact vote_extends_of_batch hrun' hy hc hs (Or.inl hvB) hall
    (faults_lt_honest_voters_win hrun hnc hwin hs₀ (by linarith))
    (honest_batch_carry_win hrun hnc hwin hs₀ hy hc hs hib hold hall
      (Anc.mono hΦU (hΦ.rooted.2 B hvB.1.1))) hlocks

/-- **Later batch up to `b`** (§2.4): an honest slot-`(s+1)` vote at a time `≤ b` extends a block
`B` that every honest slot-`s` vote extends, compatible with every origin within `b` of label at
most `s`, and extended by the earlier honest slot-`(s+1)` votes. -/
theorem later_transfer_step_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  obtain ⟨x, hx, k, e', hv, hvs⟩ := honest_vote_exists_upTo hrun hnc hpre s (by linarith)
  exact later_transfer_win hrun hnc hpre.window (Nat.zero_le s) hy hc hs hib (hold_zero hrun)
    (vote_frame_upTo hrun hnc hpre hP hy hc hs hib hB hBc
      ⟨x, hx, k, e', hv, hvs, hall x hx k e' hv hvs⟩)
    (vote_locks_compatible_upTo hrun hnc hpre hy hc hs hib hBc hE) hall

/-- Later-batch transfer with recipient-deadline-bounded service. -/
theorem later_transfer_step_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  have hcount : Hᶜ.ncard <
      {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}.ncard := by
    refine lt_of_lt_of_le (hfb s sp.Δ (by simp) (by linarith)) (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨k, e', hv, hs', -⟩ := vote_of_awake_joined hrun hnc hx hw hj
    exact ⟨hx, k, e', hv, hs'⟩
  obtain ⟨x, hx, k, e', hv, hvs⟩ :=
    (Set.ncard_pos (Set.toFinite _)).1 ((Nat.zero_le _).trans_lt hcount)
  have hvf := vote_frame_before hrun hnc hb hsync hfb hP hy hc hs hib hB hBc
    ⟨x, hx, k, e', hv, hvs, hall x hx k e' hv hvs⟩
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
    refine vote_locks_compatible_of (s₀ := 0) hrun hnc hf hy hc hs
      (fun C j hC _ hj => hBc C j
        (hC.within (fun k hk => (hrun.time_mono hk.le).trans hib)) hj) ?_ hE
    intro L hL
    obtain ⟨-, l, ⟨l₀, ⟨-, h⟩, -⟩, -⟩ := hL
    exact absurd h (Nat.not_lt_zero _)
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  rcases hvf with hvB | hBf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  exact vote_extends_of_batch hrun' hy hc hs (Or.inl hvB) hall hcount
    (honest_batch_carry_before hrun hnc hsync hy hc hs hib hall
      (Anc.mono hΦU (hΦ.rooted.2 B hvB.1.1))) hlocks


/-- **Extending the vote frontier up to `b`**: `P_{s+1}` and `V_s` up to `b` give `V_{s+1}` up
to `b`. -/
theorem votes_below_succ_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    (hV : VotesBelowUpTo tr H s b) : VotesBelowUpTo tr H (s + 1) b := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  -- the slot-`(s+1)` votes at times `≤ b`, by strong induction on the cut (the first bad vote)
  have key : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = s + 1 → ∀ C j, OriginWithin tr H C j b → j ≤ s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rintro y hy e ⟨ℓ, hc⟩ hib hs C j hC hj
      have hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C :=
        fun x hx k hk e' hv hs' =>
          ih k hk x hx e' hv ((hrun.time_mono hk.le).trans hib) hs' C j hC hj
      rcases hj.lt_or_eq with hj | rfl
      · have hti := (honest_vote_restarts hrun hnc hy hc hs).2
        exact later_transfer_step_upTo hrun hnc hpre hP hy hc hs hib (origin_mem hrun hnc hC.origin)
          (fun C' j' hC' hj' => originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
          (fun x hx k e' hv hs' => votesBelowUpTo_iff.1 hV C j hC x hx k e' hv
            (by linarith [vote_time_le hrun hnc hx hv hs'.le]) (by omega) hs'.le) hE
      · exact first_transfer_step_upTo hrun hnc hpre hP hy hc hs hib hC hE
  refine votesBelowUpTo_iff.2 fun C j hC y hy i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact votesBelowUpTo_iff.1 hV C j hC y hy i e hv hib hj (by omega)
  · exact key i y hy e hv hib (by omega) C j hC (by omega)

/-- The first-bad-vote induction uses only recipient deadlines within the horizon. -/
theorem votes_below_succ_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    (hV : VotesBelowUpTo tr H s b) : VotesBelowUpTo tr H (s + 1) b := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have key : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = s + 1 → ∀ C j, OriginWithin tr H C j b → j ≤ s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rintro y hy e ⟨ℓ, hc⟩ hib hs C j hC hj
      have hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C :=
        fun x hx k hk e' hv hs' =>
          ih k hk x hx e' hv ((hrun.time_mono hk.le).trans hib) hs' C j hC hj
      rcases hj.lt_or_eq with hj | rfl
      · have hti := (honest_vote_restarts hrun hnc hy hc hs).2
        exact later_transfer_step_before hrun hnc hb hsync hfb hP hy hc hs hib
          (origin_mem hrun hnc hC.origin)
          (fun C' j' hC' hj' => originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
          (fun x hx k e' hv hs' => votesBelowUpTo_iff.1 hV C j hC x hx k e' hv
            (by linarith [vote_time_le hrun hnc hx hv hs'.le]) (by omega) hs'.le) hE
      · exact first_transfer_step_before hrun hnc hb hsync hfb hP hy hc hs hib hC hE
  refine votesBelowUpTo_iff.2 fun C j hC y hy i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact votesBelowUpTo_iff.1 hV C j hC y hy i e hv hib hj (by omega)
  · exact key i y hy e hv hib (by omega) C j hC (by omega)

/-- **Extending the vote frontier**: `P_{s+1}` and `V_s` give `V_{s+1}`. -/
theorem votes_below_succ (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) : VotesBelow tr H (s + 1) := by
  refine votesBelow_iff.2 fun C j hC y hy i e hv hj hm => ?_
  obtain ⟨bC, hbC⟩ := hC.exists_within
  exact votesBelowUpTo_iff.1 (votes_below_succ_upTo hrun hnc
    (hsl.prefix (le_max_right (max (tr.time i) bC) 0)) (hP.upTo _) (hV.upTo _)) C j
    (hbC.mono ((le_max_right _ bC).trans (le_max_left _ 0))) y hy i e hv
    ((le_max_left _ bC).trans (le_max_left _ 0)) hj hm


end Consensus.Goldilocks.Compose

end
