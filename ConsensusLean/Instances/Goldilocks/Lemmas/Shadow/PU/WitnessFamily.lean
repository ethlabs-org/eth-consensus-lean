module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.UnanimousStep
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LaterHead
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin

public section

/-! # The early-witness family over the shadow run (interface)

A frozen witness `Q ⪰ X` carries next-slot votes and proposals to later heads. The `J` clause
lives in the witness (`EarlyWitness`): a witness `Q` held by an honest `z` at cut `c` in a
`Generic.FrameWindow … M isTop J` carries

  `M − 1 ≤ σ_z(Q).h ∧ (isTop → σ_z(Q).h = M − 1 → J ⪯ Q)` (the witness clause),

which `early_witness_viable'` supplies from `Q ∈ ellw.frame.viableHeads`. A shadow window with
`isTop` may change from top-clean to top-contest inside it (stock kept those apart), so the stock
lemmas are re-proved per cut, not instantiated: split on `σ(Q) ≥ M` (the stock contest and gap
argument) and `σ(Q) = M − 1` in a top window (`J ⪯ Q`).

Interface first: every statement below without a proof is unresolved until proved. The frame-relay
and stamp lemmas read only the frame's tree and `F`, which the shadow frame shares with the stock
one. The optimistic variants follow in this file. -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State} {hold : Time}

/-- An honest acceptance reaches a later honest caller, after GST by relay and before it by
catch-up (`relayed_accept_before_at`). -/
private theorem relayed_accept_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {k j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hxk : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {elly : ACLabel (goldilocksNode sp)} (hcy : tr.projAC.CallAt y j elly)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j) (hkt : tr.time k + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ a < j, tr.AcceptAt y a B ∧ tr.time a < max (tr.time k + sp.Δ) (gbar g + 2 * sp.Δ) := by
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl' : ∀ c ≤ j, tr.deadline y c (max (tr.time k) g) sp.Δ ≤ tr.time k + sp.Δ := by
      intro c hc
      rw [max_eq_left ((Healing.le_gbar g).trans hnew), ← Compose.projAC_deadline]
      have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
        (fun r hrc hrs => hnr r (hrc.trans hc) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
      rwa [max_eq_left hnew] at h
    obtain ⟨a, haj, ha, hat⟩ := hsvc.relay x k B hxk ha ((Healing.le_gbar g).trans hnew)
      y j hy ⟨_, Compose.projAC_callAt.mp hcy⟩ ((hdl' j le_rfl).trans hkt) hF
    refine ⟨a, lt_of_le_of_ne haj ?_, ha,
      lt_max_of_lt_left (hat.trans_le (hdl' a haj))⟩
    intro he
    subst a
    cases Option.some.inj (ha.2.symm.trans (Compose.projAC_callAt.mp hcy).2)
  · obtain ⟨a, hlt, hacc, hat⟩ := hrun.toLocalRun.fgCatchAt hcatch hxk ha
      (not_le.mp hnew) hy hg hF
    exact ⟨a, hlt, hacc, lt_max_of_lt_right hat⟩

/-- Historical frame membership relays without requiring the sender to remain honest
(`frame_relay_before_at` over the shadow run). -/
theorem frame_relay_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {ellx elly : ACLabel (goldilocksNode sp)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hd := hrun.time_nonneg j
  have hp := hrun.upTo hd
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j elly := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcy⟩
  have hac := Compose.goldilocks_ac_projection_from hp (hnc.upTo _)
  have hPh := AC.frameIn_of_callAt hac.localRun hy hc'
  have hFstate : elly.frame.F = (tr.state y j).fg.F := by
    rw [frame_of_projAC_at hrun hy hcy, Node.frame_eq, Store.toFrame_F]
  rcases Healing.Growing.frame_block_acceptance_at hrun hx hcx hB with hgB | ⟨k, hk, hxk, ha⟩
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hac.localRun.toU hy j elly hc'
    have hBU : B ∈ tr.HonestBlocksAt H := by
      have hq0 := hrun.time_nonneg q
      have hcx' : (tr.upTo (tr.time q)).projAC.CallAt x q ellx := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcx⟩
      exact RunTrace.honestBlocks_upTo_subset hrun.time_mono hq0
        ((AC.frameIn_of_callAt (Compose.goldilocks_ac_projection_from (hrun.upTo hq0)
          (hnc.upTo _)).localRun hx hcx').2 hB)
    have hcoh := Compose.Growing.honestBlocksAt_coherent hrun hnc
    have he : B = G := hcoh.1 hBU
      (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd hG)
      ((congrArg Block.root hgB).trans hGr.symm)
    rw [he] at hF
    rcases Relation.ReflTransGen.cases_tail hF with heq | ⟨C, _, hpar⟩
    · rw [he]
      exact heq.symm ▸ hPh.1.rooted.1
    · exact (Option.some_ne_none _ (hpar.2.2.symm.trans hGp)).elim
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have hle := hrun.time_mono hk.le
    linarith only [hle, hq]
  obtain ⟨a, haj, ha, -⟩ := relayed_accept_before_at hrun hsvc hcatch hxk ha hy hnr hcy hg hkt
    (hFstate ▸ hF)
  have ha' : (tr.upTo (tr.time j)).AcceptAt y a B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono haj.le, ha⟩
  obtain ⟨hacc, _, _⟩ := Healing.ac_block_after hp.toLocalRun hy ha'
  have hBF : Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) elly.frame.F B := by
    obtain ⟨ella, hca, hba⟩ := hacc
    have ht := (AC.frameIn_of_callAt hac.localRun hy hca).2
      ((AC.accept_new sp hac.localRun hy ⟨ella, hca, hba⟩).1 ella hca)
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd ht hF
  exact AC.mem_tree_of_acceptAtU sp hac.localRun.toU hy hacc (by omega) hc' hBF

/-- An early frame witness has a pre-freeze stamp at a later honest cast
(`frame_witness_readPoint_stamp_at` over the shadow run). -/
theorem frame_witness_readPoint_stamp_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {a i s : Nat} (hx : x ∈ H (tr.time a))
    (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode sp)}
    (hcx : tr.projAC.CallAt x a ellx)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hes : e.msg.slot = s + 1) (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (ha : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ellx.frame.tree)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ (tr.state y i).fg.tree ∧
      e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (s + 1)) := by
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hs : sp.slot (tr.time i) = s + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hes
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hs])
  have hts := AC.ts_succ s (sp := sp)
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hQt := frame_relay_before_at hrun hnc hsvc hcatch hx hy
    (fun r hr' hrs => hnr _ r (hrun.antitone (hrun.time_mono hr') hy) hrs) hcx hc.1 hQ
    (by linarith only [hm, hti, hts, sp.toParams.hΔ])
    (by linarith only [ha, hti, hts, sp.toParams.hΔ]) hFQ
  have hacc : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q
      (AC.freeze sp (s + 1)) := by
    rcases Healing.Growing.frame_block_acceptance_at hrun hx hcx hQ with hg | ⟨k, hka, hxk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    have hkt := (hrun.time_mono hka.le).trans_lt ha
    have hfr : ell.frame.F = (tr.state y i).fg.F := by
      rw [frame_of_projAC_at hrun hy hc.1, Node.frame_eq, Store.toFrame_F]
    have hp := hrun.upTo (hrun.time_nonneg i)
    have accepted : ∃ q < i, tr.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hnew : gbar g ≤ tr.time k
      · have hdl : tr.deadline y i (max (tr.time k) g) sp.Δ ≤ tr.time i := by
          rw [max_eq_left ((Healing.le_gbar g).trans hnew), ← Compose.projAC_deadline]
          have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := i)
            (fun r hri hrs => hnr y r (hrun.antitone (hrun.time_mono hri) hy)
              (Compose.projAC_restartAt.mp hrs)) (tr.time k)
          change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
          rw [max_eq_left hnew] at h
          exact h.trans (by linarith only [hkt, hti, hts, sp.toParams.hΔ])
        obtain ⟨q, hqi, hq, hqd⟩ := hsvc.relay x k Q hxk hk ((Healing.le_gbar g).trans hnew)
          y i hy ⟨_, Compose.projAC_callAt.mp hc.1⟩ hdl (hfr ▸ hFQ)
        have hqi' : q < i := by
          refine lt_of_le_of_ne hqi ?_
          rintro rfl
          cases Option.some.inj (hq.2.symm.trans (Compose.projAC_callAt.mp hc.1).2)
        have hdead := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := q)
          (fun r hrq hrs => hnr y r (hrun.antitone (hrun.time_mono (hrq.trans hqi)) hy)
            (Compose.projAC_restartAt.mp hrs)) (tr.time k)
        change _ ≤ max (tr.time k) (gbar g) + sp.Δ at hdead
        rw [max_eq_left hnew, Compose.projAC_deadline] at hdead
        rw [max_eq_left ((Healing.le_gbar g).trans hnew)] at hqd
        exact ⟨q, hqi', hq, by rw [hfz]; linarith only [hqd, hdead, hkt]⟩
      · obtain ⟨q, hq, hacc, hqt⟩ := hrun.toLocalRun.fgCatchAt hcatch hxk hk
          (not_le.mp hnew) hy (by linarith only [hm, hti, hts, sp.toParams.hΔ]) (hfr ▸ hFQ)
        exact ⟨q, hq, hacc, by rw [hfz]; linarith only [hqt, hm, sp.toParams.hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := accepted
    have hq' := (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hrun.time_mono hqi.le, hq⟩
    obtain ⟨hqa, htq, _⟩ := Healing.ac_block_after hp.toLocalRun hy hq'
    exact Or.inr ⟨q + 1, by rwa [RunTrace.upTo_projAC] at hqa,
      by change tr.time (q + 1) < _; rw [show tr.time (q + 1) = tr.time q from htq]; exact hqt⟩
  refine ⟨?_, ?_⟩
  · rw [frame_of_projAC_at hrun hy hc.1, Node.frame_eq, Store.toFrame_tree] at hQt
    exact hQt.1
  · have h := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
      (by simpa only [hes] using hacc)
      (fun k hki hrs => by
        have h := hnr y k (hrun.antitone (hrun.time_mono hki) hy)
          (Compose.projAC_restartAt.mp ((ACTrace.upTo_restartAt).mp hrs).2)
        change tr.time k < _
        rw [hes, hfz]
        linarith only [h, hm, sp.toParams.hΔ])
      (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hes, hfz];
          linarith only [hti, hts, sp.toParams.hΔ])
    simpa only [hes] using h

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **`Σ.F` below a crossing**: a finalized block `F` of `y`'s chain to `X` (observed while honest
at `u`) is below a block `W` held by `x` (observed while honest at `t`) whose state height exceeds
the finalized height of `X`. Certificate intersection is charged at `max u t`. -/
private theorem finalized_anc_obs
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X F W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y m).fg.tree)
    (hFt : F ∈ (tr.state y m).fg.tree) (hFr : F.root = ((tr.state y m).fg.σ X.root).F)
    (hW : W ∈ (tr.state x i).fg.tree)
    (hlt : ((tr.state y m).fg.σ X.root).hF < ((tr.state x i).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) F W :=
  honest_anc_of_store_anc_at ht hxtime hx <| Store.finalized_anc_of_safe
    (fg_reachable_at hrun hu hytime hy) (fg_reachable_at hrun ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent hrun hnc) (fun _ h => ⟨y, m, u, hu, hytime, hy, h⟩)
    (fun _ h => ⟨x, i, t, ht, hxtime, hx, h⟩) hf
    (held_atts_safe_at hrun hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hX hFt hFr hW hlt


/-- A source's replay floor passes to a descendant held at an independently honest cut. -/
private theorem floor_le_of_honest_ancestor_at
    {sp : ACParams}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i c : Nat}
    (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} {floor : Nat}
    (hX : X ∈ (tr.state z c).fg.tree) (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    floor ≤ ((tr.state x i).fg.σ W.root).h := by
  have hti := hrun.time_nonneg i
  have hbi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hXt := mem_of_honest_anc_at hrun hnc hti hbi hx hXW hW
  have ha := store_anc_of_honest_anc_at hrun hnc hti hbi hx hXW hW
  have hle := Healing.h_le_of_store_anc (fg_reachable_at hrun hti hbi hx) ha
  rw [← σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
    (fun q hq => hrun.time_mono hq.le) hz hti hbi hx hX hXt] at hle
  exact hh.trans hle


/-- **The finalized tip of an honest observation is below every held block strictly above its
justified height** (the quorum branch of `finalized_below_floor_held_at`, read off the justified
height instead of the stock head-height floor). -/
theorem finalized_below_of_hj_lt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i m : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (hf : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z m).fg.tree)
    (hgt : (tr.state y i).fg.hj < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have htm := hrun.time_nonneg m
  have hbm : ∀ q < m, tr.time q ≤ tr.time m := fun q hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at hrun ht hy hb
  have hrz := Compose.Growing.reachable_at hrun htm hz hbm
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hsub := Compose.Growing.tree_held_at ht hy hb
  have hcoh := hU.mono hsub
  obtain ⟨hF, hJm, hFJ, ⟨Bj, hBj, hBjJ, _⟩, hmax, -, X, hX, hXF⟩ :=
    Store.cache_invariants _ _ _ _ hr
  have hg := Healing.Store.genesis_mem hr
  have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := fun he => by
    rw [hcoh.1 hF hg he]
    exact ((Goldilocks.Store.accepted_tree _ _ _ _ hrz).2.2.2 W hW)
      |>.mono (Compose.Growing.tree_held_at htm hz hbm)
  rcases Healing.Store.fin_pair_entry hr hX with
    he | ⟨E, hE, hEr, _⟩
  · exact hgen (hXF.symm.trans he)
  obtain rfl : E = (tr.state y i).fg.F := hcoh.1 hE hF (hEr.trans hXF)
  obtain ⟨J, hJt, hJr, -, hcase⟩ :=
    Goldilocks.Store.J_entry_hj _ _ hr hBj
  obtain rfl : J = (tr.state y i).fg.J := hcoh.1 hJt hJm (hJr.trans hBjJ)
  rcases hcase with ⟨he, -⟩ | ⟨hJh, -⟩
  · have hgF := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 _ hF
    rw [he] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have hFh := Healing.h_le_of_store_anc hr hFJ
  have hstrict : ((tr.state y i).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h := by
    omega
  exact finalized_anc_obs hrun hnc ht hb hy htm hbm hz hf hX hF hXF.symm hW hstrict

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **A window's witness places every honest finalized tip in it below an independently held
descendant** (`FrameWindow.finalized_below_descendant_at` over the shadow run, with the witness
clause on `X` in place of `floor ≤ σ(X).h` and `kindJ → J ⪯ X`). -/
theorem _root_.Consensus.Goldilocks.Generic.FrameWindow.finalized_below_descendant_at
    {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x z : Fin sp.n} {j i c : Nat}
    (hy : y ∈ H (tr.time j)) (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time j) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ X.root).h ∧
      (isTop → ((tr.state z c).fg.σ X.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J X))
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F W := by
  have hjt := hrun.time_nonneg j
  have hbj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
  have hM := hframe.M_eq y j hy hjlo hjhi
  have htop := hframe.top_iff y j hy hjlo hjhi
  have hjm := Healing.Store.hj_lt_hmax_of_reachable
    (Compose.Growing.reachable_at hrun hjt hy hbj)
  by_cases hcase : isTop ∧ ((tr.state z c).fg.σ X.root).h = M - 1
  · obtain ⟨ht, he⟩ := hcase
    have hJX := hwit.2 ht he
    have hFJ :=
      (Store.cache_invariants _ _ _ _ (Compose.Growing.reachable_at hrun hjt hy hbj)).2.2.1
    rw [hframe.root_eq y j hy hjlo hjhi ht] at hFJ
    exact (hFJ.mono (Compose.Growing.tree_held_at hjt hy hbj)).trans (hJX.trans hXW)
  · have hWh := Growing.floor_le_of_honest_ancestor_at hrun hnc hx hz hX le_rfl hW hXW
    refine Growing.finalized_below_of_hj_lt_at hrun hnc hy hx hf hW ?_
    by_cases ht : isTop
    · have hX' : M ≤ ((tr.state z c).fg.σ X.root).h := by
        have := hwit.1
        by_contra hlt
        exact hcase ⟨ht, by omega⟩
      have := htop.2 ht
      omega
    · have := mt htop.1 ht
      have := hwit.1
      omega

/-- **The frame geometry of a held witness at a reader's cut**: for a reader honest at its call
holding a descendant `Q` of `X` with `F ⪯ Q` and `Q` P-U viable in its store, either `X` is below
its finalized tip, or `X` and `Q` are in its frame above `F` with `Q` a P-U viable head. The
window-free core of `witness_frame_at'` and `witness_frame_stock_at'`. -/
theorem witness_frame_of_held
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQy : Q ∈ (tr.state y i).fg.tree)
    (hFQ : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hv : (tr.state y i).fg.IsViable Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) :
    Anc (tr.HonestBlocksAt H) X ell.frame.F ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F X ∧ X ∈ ell.frame.tree ∧
        ell.frame.Anc ell.frame.fcRoot X ∧ Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧
        ell.frame.Anc X Q) := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hrun.time_mono hq.le
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  rw [Compose.Growing.frame_of_projAC_at hrun hy hc]
  rcases AC.anc_total hU hFQ hXQ with hFX | hXF
  swap
  · exact Or.inl (by rwa [Node.frame_eq, Store.toFrame_F])
  have hΦ := Compose.Growing.frameOK_at hrun ht hy hb
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H := by
    rw [Node.frame_eq, Store.toFrame_tree]
    exact fun _ h => ⟨y, i, tr.time i, ht, hb, hy, h.1⟩
  have hXy := Growing.mem_of_honest_anc_at hrun hnc ht hb hy hXQ hQy
  have hFXs := Growing.store_anc_of_honest_anc_at hrun hnc ht hb hy hFX hXy
  have hFQs := Growing.store_anc_of_honest_anc_at hrun hnc ht hb hy (hFX.trans hXQ) hQy
  have hXt : X ∈ (Node.frame (tr.state y i)).tree := by
    rw [Node.frame_eq, Store.toFrame_tree]; exact ⟨hXy, hFXs⟩
  have hQt : Q ∈ (Node.frame (tr.state y i)).tree := by
    rw [Node.frame_eq, Store.toFrame_tree]; exact ⟨hQy, hFQs⟩
  have hvQ : Q ∈ (Node.frame (tr.state y i)).viableHeads := by
    rw [Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hQy, hFQs, hv⟩
  have hXQf := AC.anc_tree_of_anc_U hU hΦ hsub hXt hXQ hQt
  have hFt : (Node.frame (tr.state y i)).fcRoot ∈ (Node.frame (tr.state y i)).tree :=
    hΦ.fcRoot_mem
  refine Or.inr ⟨by rwa [Node.frame_eq, Store.toFrame_F], hXt, ?_, hQt, hvQ, hXQf⟩
  apply AC.anc_tree_of_anc_U hU hΦ hsub hFt _ hXt
  rw [Node.frame_eq, Store.toFrame_fcRoot]
  exact hFX

/-- In a `Generic.FrameWindow`, a held block carrying the P-U witness clause at the reader is P-U
viable in the reader's store. -/
private theorem isViable_of_frameWindow
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hlo : lo ≤ tr.time i)
    (hhi : tr.time i ≤ hi) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQy : Q ∈ (tr.state y i).fg.tree)
    (hwit : M - 1 ≤ ((tr.state y i).fg.σ Q.root).h ∧
      (isTop → ((tr.state y i).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q)) :
    (tr.state y i).fg.IsViable Q := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hrun.time_mono hq.le
  have hr := Compose.Growing.reachable_at hrun ht hy hb
  rw [Store.isViable_iff, hframe.M_eq y i hy hlo hhi]
  have hjm := Healing.Store.hj_lt_hmax_of_reachable hr
  have hM := hframe.M_eq y i hy hlo hhi
  have htop := hframe.top_iff y i hy hlo hhi
  rcases Nat.lt_or_ge ((tr.state y i).fg.σ Q.root).h M with hlt | hge
  · have he : ((tr.state y i).fg.σ Q.root).h = M - 1 := by have := hwit.1; omega
    refine Or.inr ⟨by omega, ?_⟩
    by_cases ht' : isTop
    · right
      have hJQ := Growing.store_anc_of_honest_anc_at hrun hnc ht hb hy (hwit.2 ht' he) hQy
      rwa [hframe.root_eq y i hy hlo hhi ht']
    · left
      have := mt htop.1 ht'
      omega
  · exact Or.inl hge

/-- **The frame geometry of a viable witness at a reader's cut** (`witness_frame_at` over the
shadow frame): for a reader honest at its call in a `Generic.FrameWindow`, holding a descendant `Q`
of `X` that carries the witness clause, either `X` is below its finalized tip, or `X` and `Q` are in
its frame above `F` with `Q` a P-U viable head. The witness clause is exactly P-U viability at the
window's `M` and `J`; no `fc_root = J` case arises. -/
theorem witness_frame_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell) (hlo : lo ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQy : Q ∈ (tr.state y i).fg.tree)
    (hwit : M - 1 ≤ ((tr.state y i).fg.σ Q.root).h ∧
      (isTop → ((tr.state y i).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) :
    Anc (tr.HonestBlocksAt H) X ell.frame.F ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F X ∧ X ∈ ell.frame.tree ∧
        ell.frame.Anc ell.frame.fcRoot X ∧ Q ∈ ell.frame.tree ∧ Q ∈ ell.frame.viableHeads ∧
        ell.frame.Anc X Q) := by
  exact witness_frame_of_held hrun hnc hy hc hQy
    (hframe.finalized_below_descendant_at hrun hnc hy hy hy (by rwa [max_self]) hlo hhi hQy hwit
      hQy .refl)
    (isViable_of_frameWindow hrun hnc hframe hy hlo hhi hQy hwit) hXQ

/-- **A witness of a window**: every honest reader of the window holding `Q`, with the fault
margin at its cut, has `F ⪯ Q` and `Q` P-U viable in its store. Supplied by the P-U window and
witness (`windowWitness_of_frameWindow'`) and by the stock window and witness
(`windowWitness_of_stock`); the early-witness family reads only this. -/
structure WindowWitness (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (lo hi : Time) (Q : AC.Blk sp.n (List (FG.Att sp.n))) : Prop where
  held : ∀ y j, y ∈ H (tr.time j) → lo ≤ tr.time j → tr.time j ≤ hi →
    (H (tr.time j))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n → Q ∈ (tr.state y j).fg.tree →
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F Q ∧ (tr.state y j).fg.IsViable Q

/-- Restricting the interval keeps a window witness. -/
theorem WindowWitness.mono {lo hi lo' hi' : Time} {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : WindowWitness tr H lo hi Q) (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    WindowWitness tr H lo' hi' Q :=
  ⟨fun y j hy h₁ h₂ => h.held y j hy (hl.trans h₁) (h₂.trans hh)⟩

/-- The P-U witness clause of a held block is a witness of a `Generic.FrameWindow`. -/
theorem windowWitness_of_frameWindow
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))} (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q)) :
    WindowWitness tr H lo hi Q := by
  refine ⟨fun y j hy hlo hhi hm hQy => ?_⟩
  have hwy : M - 1 ≤ ((tr.state y j).fg.σ Q.root).h ∧
      (isTop → ((tr.state y j).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q) := by
    rwa [← Growing.σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
      (fun _ hq => hrun.time_mono hq.le) hz (hrun.time_nonneg j)
      (fun _ hq => hrun.time_mono hq.le) hy hQ hQy]
  exact ⟨hframe.finalized_below_descendant_at hrun hnc hy hy hy (by rwa [max_self]) hlo hhi
      hQy hwy hQy .refl,
    isViable_of_frameWindow hrun hnc hframe hy hlo hhi hQy hwy⟩

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State} {hold : Time}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- Fewer than a third faulty is below the replay quorum excess. -/
private theorem quorum_excess {t : Time} (h : 3 * (H t)ᶜ.ncard ≤ sp.n - 1) :
    (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
  have hn := sp.toParams.hn
  have he : sp.n = sp.toParams.n := rfl
  change (H t)ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.n
  omega

/-- A prefix vote by a node honest at `d` extends `B` in the prefix's honest blocks when it does
in the run's (`narrow_vote`). -/
private theorem narrow_vote
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d)
    {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.VoteAt (tr.projAC.upTo d) x k e)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    AC.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg B := by
  have hr := (acRun_prefix hrun hnc hd).localRun
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hd
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hrun.vstart hx hc
  have hHdU := (AC.frameIn_of_callAt hr hx hc.1).2 hHd
  obtain ⟨W, hW, hWr, hBW⟩ := hext
  obtain rfl : W = Hd := hU.1 hW (subU hHdU) (hWr.trans hHdr.symm)
  exact ⟨W, hHdU, hWr, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdU hBW⟩

/-- Prior votes extending a prefix propagate through a window witness: the window-free core of
`unanimous_next_votes_of_witness_at'` and `unanimous_next_votes_of_stock_witness_at'`. -/
theorem unanimous_next_votes_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : Healing.WindowWitness tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hΔ := sp.toParams.hΔ
  have ht := AC.ts_succ (sp := sp) m
  have hgm : gbar g ≤ sp.ts m := by linarith
  have htime {y i ell e} (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ell e)
      (hs : e.msg.slot = m + 1) : sp.ts (m + 1 : Nat) ≤ tr.time i ∧
      tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
    refine ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2
      (by rw [← (Compose.Growing.castAt_spec_at hrun hnc hy hc).2.1, hs]), ?_⟩
    simpa only [hs] using (Compose.Growing.cast_head_fcRoot_at hrun hnc hy hc).2
  have hnext := Healing.Growing.UnanimousStep.next_votes_extend_of_viable
    (m := m) (P := X) (b := b) hrun hnc
    (hviable := fun y i ell e hy hc hs hib _ => by
      obtain ⟨hlo, hhi⟩ := htime hy hc hs
      obtain ⟨hQy, hstamp⟩ := hheld y i e hy ⟨ell, hc⟩ hs
      have hmargin := sp.toParams.fg.faults_lt_quorum_margin (hf _ (hrun.time_nonneg i) hib)
      obtain ⟨hFQ, hvy⟩ := hW.held y i hy (by linarith) hhi hmargin hQy
      rcases Healing.witness_frame_of_held hrun hnc hy hc.1 hQy hFQ hvy hXQ with
        hXF | ⟨hFX, -, hrootX, hQt, hvQ, hXQf⟩
      · exact Or.inl hXF
      have hQdom : Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (m + 1) := ⟨hQt, Or.inl hstamp⟩
      have hr := Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg i)
      have hdom := AC.voterBlockTree_ancU hr.localRun.toU hr.vstart hy
        (AC.upTo_castAt.mpr ⟨le_rfl, hc⟩)
      rw [hs] at hdom
      exact Or.inr ⟨hFX, Or.inl ⟨hdom Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩⟩)
    (htransfer := fun y i ell e hy hc hs hib hFX hV ih => by
      have h0 := hrun.time_nonneg i
      have hlo := (htime hy hc hs).1
      have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch h0 hib
      refine Healing.Growing.UnanimousStep.next_vote_of_batch hrun hnc hsvc hcatch
        (fun x j e' hx hv _ hj => hG x j e' hx hv hj) hgm hK.facts.hP
        (hK.facts.committeeTAt hrun hnc) hK.facts.hsize hy hc hs hib ?_ ?_
        (hK.cs2 (m + 1) (by linarith) (by linarith) _ h0 hib) hFX hV ih
      · intro x hx
        obtain ⟨j, e', hv, hj, htj⟩ := AC.honest_votes_in_slot_before hS hm (by linarith)
          (fun z hz r _ hrs => by
            obtain ⟨hrd, hrs⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _)).mp hrs
            rw [AC.ts_sub_one]
            exact (hnr z r (hrun.antitone hrd hz) (Compose.projAC_restartAt.mp hrs)).trans
              (by linarith)) x hx.2 hx.1
        exact ⟨j, e', (AC.upTo_voteAt.mp hv).2, hj, htj⟩
      · refine Healing.Growing.KernelProof.faultBoundK_of_service_at hK hrun hawake hnr hgm
          (by linarith) h0 ?_ hib
        rw [← (Compose.Growing.castAt_spec_at hrun hnc hy hc).2.1, hs]
        simpa using hgm)
  intro y i e hy hv hs
  obtain ⟨ell, hc⟩ := hv
  exact hnext y i e hy ⟨ell, hc⟩ ((htime hy hc hs).2.trans hmb) hs

/-- Prior votes extending a prefix propagate through a frozen viable witness
(`unanimous_next_votes_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_votes_of_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  exact unanimous_next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    (Healing.windowWitness_of_frameWindow hrun hnc hframe hz hQ hwit) hXQ hheld hG hK

/-- The same prefix reaches an actual next-slot proposal head through a window witness: the
window-free core of `unanimous_next_proposal_of_witness_at'` and its stock form. -/
theorem unanimous_next_proposal_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : Healing.WindowWitness tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hgm : gbar g ≤ sp.ts m := by linarith
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := by linarith
  have hlo : sp.ts m ≤ tr.time i := by linarith
  have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by linarith
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  have hS := hK.healthy_base_before_at' hrun hnc hsvc hawake hf hcatch ht0 hib
  have hr := hS.run.localRun
  have hf3 := hf _ ht0 hib
  have hcp : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hk => hmono hk.le
  have hdp : (AC.acProposal sp ((tr.projAC.upTo (tr.time i)).state y i) ell.frame
      ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcp
  obtain ⟨hFQy, hvy⟩ := hW.held y i hy hlo hhi (quorum_excess hf3) hQy
  rcases Healing.witness_frame_of_held hrun hnc hy hc hQy hFQy hvy hXQ
    with hXF | ⟨hFX, hXt, hrootX, hQt, hvQ, hXQf⟩
  · have he := (AC.acProposal_head hdp).2
    rw [he]
    exact hXF.trans (((AC.anc_getHead_of_compat hPhi (Or.inr rfl)
      (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl)
      (fun B (hB : B ∈ ell.frame.viableTree ell.frame.tree) => hB.1)
      _ _ hPhi.F_anc_fcRoot).mono hPhiU).mono subU)
  have hG' : ∀ x ∈ H (tr.time i), ∀ j e', AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' →
      e'.msg.slot = m → AC.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
        e'.msg X := by
    intro x hx j e' hv' hs'
    obtain ⟨hjd, hv''⟩ := AC.upTo_voteAt.mp hv'
    exact narrow_vote hrun hnc ht0 hx hv' (hG x j e' (hrun.antitone hjd hx) hv'' hs')
  have hrelay : ∀ x ∈ H (tr.time i), ∀ k ev, AC.VoteAt (tr.projAC.upTo (tr.time i)) x k ev →
      ev.msg.slot = m → ∀ B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)),
        B.root = ev.msg.head →
        Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ell.frame.F B := by
    intro x hx k ev hv' hs' B hB hBr
    obtain ⟨W, hW, hWr, hXW⟩ := hG' x hx k ev hv' hs'
    obtain rfl : B = W := hr.coherent.1 hB hW (hBr.trans hWr.symm)
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hB (hFX.trans (hXW.mono subU))
  have hrestart : ∀ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ gbar g := by
    intro k hk
    obtain ⟨hkd, hk⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _)).mp hk
    exact hnr y k (hrun.antitone hkd hy) (Compose.projAC_restartAt.mp hk)
  have hdl : ∀ k ≤ i, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := AC.goldilocksAC sp _) (tr.projAC.upTo (tr.time i)) y k t ≤
        max t (sp.ts m) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts m)
      (fun r _ hrs => (hrestart r hrs).trans hgm) t
  have hrs : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      (tr.projAC.upTo (tr.time i)).time k < sp.ts m :=
    fun k _ hk => (hrestart k hk).trans_lt (by linarith)
  have hhalf := AC.honest_voters_half_before hS hm (show sp.ts m + sp.Δ ≤ tr.time i by linarith)
    (fun x hx r _ hrest => by
      obtain ⟨hrd, hrest⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _)).mp hrest
      rw [AC.ts_sub_one]
      exact (hnr x r (hrun.antitone hrd hx) (Compose.projAC_restartAt.mp hrest)).trans
        (by linarith))
  have hhalf' : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m}.ncard := by
    have hle := Set.ncard_le_ncard (s := {x | x ∈ H (tr.time i) ∧ ∃ j e',
      AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m ∧
        (tr.projAC.upTo (tr.time i)).time j ≤ sp.ts m + sp.Δ})
      (t := {x | x ∈ H (tr.time i) ∧ ∃ j e',
        AC.VoteAt (tr.projAC.upTo (tr.time i)) x j e' ∧ e'.msg.slot = m})
      (by rintro x ⟨hx, j, e', hv', hs', _⟩; exact ⟨hx, j, e', hv', hs'⟩)
    omega
  have hpre := hrun.upTo ht0
  refine (AC.batch_proposal hS.run (K := K) (hS.cs2 m hgm (by linarith)) hhalf' hG' hy hcp
    (fun v hv => hS.hP.1 y hy i m v hv) (AC.proposal_slot hti) hdp
    ⟨hXt, Or.inl ⟨hXt, hrootX, Q, hQt, hvQ, hXQf⟩⟩ ?_ ?_).mono subU
  · intro x hx k e hv hs
    obtain ⟨W, hW, hWr, -, hp, -, hb⟩ := AC.late_vote_held_of_frame_before hS hy hcp hm
      (show sp.ts m + 2 * sp.Δ ≤ tr.time i by linarith) le_rfl hdl hrs hx hv hs
      (hrelay x hx k e hv hs)
    exact AC.heldAtProposal_iff.mpr ⟨Or.inl hp, W, hW, hWr, hWr ▸ lt_trans hb
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩
  · apply AC.highLocksCompatible_iff.mpr
    intro l hl _ hlm L hL hLr
    have hl' : l ∈ ((tr.upTo (tr.time i)).state y i).ac.locks := by
      have h := Compose.projAC_state hpre.toLocalRun hy i
      rw [RunTrace.upTo_projAC] at h
      rwa [h] at hl
    have hls := Compose.proposal_locks_slot_of hpre (hnc.upTo _) hy
      (by rw [RunTrace.upTo_projAC]; exact hcp) hcall
      (by rw [RunTrace.upTo_projAC]; exact hdp) hti (by rw [RunTrace.upTo_projAC]; exact hS.hP)
      (hS.cs2 (m + 1) (by linarith) (by linarith)) l hl'
    have heq : l.slot = m := by omega
    obtain ⟨O, hLO, a, CV, hopt⟩ := AC.proposal_high_lockU hr.toU hS.run.vstart hy hti hl hlm hL hLr
    rw [heq] at hopt
    rcases AC.optimisticLock_compatibleU hS.run.toU K hS.hP hy hopt (hS.cs2 m hgm (by linarith))
        hG' with hOX | hXO
    · exact Or.inl (hLO.trans hOX)
    · exact AC.anc_total hr.coherent hLO hXO

/-- The same prefix reaches an actual next-slot proposal head
(`unanimous_next_proposal_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_proposal_of_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  exact unanimous_next_proposal_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    (Healing.windowWitness_of_frameWindow hrun hnc hframe hz hQ hwit) hXQ hG hy hc hcall hti hd
    hQy hK

/-- An early window witness propagates its prefix to later honest calls: the window-free core of
`later_heads_of_early_witness_at'` and `later_heads_of_stock_witness_at'`, from a window witness
and the finalized tips below the witness. -/
theorem later_heads_of_windowWitness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a)) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hW : Healing.WindowWitness tr H (sp.ts s) (sp.ts N + sp.Δ) Q)
    (hfin : ∀ y i, y ∈ H (tr.time i) → sp.ts s ≤ tr.time i → tr.time i ≤ sp.ts N + sp.Δ →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hsstep := AC.ts_succ s (sp := sp)
  have hFst {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
      {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell) :
      ell.frame.F = (tr.state y i).fg.F := by
    rw [frame_of_projAC_at hrun hy hc, Node.frame_eq, Store.toFrame_F]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at hQw
    exact hQw.1
  have hvt {y : Fin sp.n} {i : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
      (hy : y ∈ H (tr.time i)) (hv : AC.VoteAt tr.projAC y i e) :
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ := by
    obtain ⟨ell, hc⟩ := hv
    simpa only using (Compose.Growing.cast_head_fcRoot_at hrun hnc hy hc).2
  have hstep := Healing.Growing.UnanimousStep.later_heads_of_step (s := s + 1) (N := N)
    (b := sp.ts N + sp.Δ) (P := X) (fun y i e hy hv _ hs => hbase y i e hy hv hs)
    (fun m hsm hmN hprior => by
      have ht := hts (show m + 1 ≤ N by omega)
      have hms := hts (show s ≤ m by omega)
      have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by
        have := hts (show s + 1 ≤ m by omega)
        linarith only [hm, this, hsstep]
      have hprior' : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
          e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X :=
        fun y i e hy hv hs => hprior y i e hy hv
          (by have h := hvt hy hv; rw [hs] at h; linarith only [h, hts (show m ≤ N by omega)])
          hs
      have hwin := hW.mono (hts (show s ≤ m by omega))
        (show sp.ts (m + 1 : Nat) + sp.Δ ≤ sp.ts N + sp.Δ by linarith only [ht])
      have hfinal {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
          (hlo : sp.ts s ≤ tr.time i) (hhi : tr.time i ≤ sp.ts N + sp.Δ) :
          Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q := hfin y i hy hlo hhi
      have hvotes := unanimous_next_votes_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr
        hwarm (by linarith only [ht, hmb]) hwin hXQ ?_ hprior' hK
      · refine ⟨fun y i e hy hv _ hs => hvotes y i e hy hv hs, ?_⟩
        intro y i ell hy hc hcall hti _ d pay hd
        have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
        have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith only [ht, hΔ]
        have hmstep := AC.ts_succ m (sp := sp)
        have hQt := frame_relay_before_at hrun hnc hsvc hcatch hw hy
          (fun r hr' hrs => hnr _ r (hrun.antitone (hrun.time_mono hr') hy) hrs) hcw hc hQw
          (by rw [hti]; linarith only [hwarm, hmstep, hΔ])
          (by rw [hti]; linarith only [hat, hms, hsstep, hmstep, hΔ])
          ((hFst hy hc) ▸ hfinal hy hlo hhi)
        rw [frame_of_projAC_at hrun hy hc, Node.frame_eq, Store.toFrame_tree] at hQt
        exact unanimous_next_proposal_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr
          hwarm (by linarith only [ht, hmb]) hwin hXQ hprior' hy hc hcall hti hd hQt.1 hK
      · intro y i e hy hv hes
        obtain ⟨ell, hc⟩ := hv
        have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg i))
          (hnc.upTo _)).localRun
        rw [RunTrace.upTo_projAC] at hr
        have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
        have hs : sp.slot (tr.time i) = m + 1 :=
          (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hes
        have hlo : sp.ts s ≤ tr.time i :=
          (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by
            rw [hs]; exact_mod_cast (by omega : s ≤ m + 1))
        have hhi : tr.time i ≤ sp.ts N + sp.Δ := by
          have h := hvt hy ⟨ell, hc⟩
          rw [hes] at h
          linarith only [h, ht]
        exact frame_witness_readPoint_stamp_at hrun hnc hsvc hcatch hnr hw hy hcw hc hes hwarm
          (by linarith only [hat, hms, hsstep, hΔ]) hQw ((hFst hy hc.1) ▸ hfinal hy hlo hhi))
  intro r hr hrN
  obtain ⟨hv, hp⟩ := hstep r hr hrN
  refine ⟨fun y i e hy hve hs => hv y i e hy hve ?_ hs, fun h2 y i ell hy hc hcall hti d pay hd =>
    hp (by omega) y i ell hy hc hcall hti (by rw [hti]; linarith only [hts hrN, hΔ]) d pay hd⟩
  have h := hvt hy hve
  rw [hs] at h
  linarith only [h, hts hrN]

/-- **A next-vote base propagates through later labels** from an early viable witness
(`later_heads_of_early_witness_at` over the shadow run). The witness is a viable head of the
witness's call frame (`hvQ`), read inside the window (`halo`); `floor ≤ σ(Q).h` and
`kindJ → J ⪯ X` are replaced by it (`early_witness_viable'`). -/
theorem later_heads_of_early_witness_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have hΔ := sp.toParams.hΔ
  have hsstep := AC.ts_succ s (sp := sp)
  have hsN : sp.ts (s + 1 : Nat) ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by linarith only [hat, hsstep, hsN, hΔ]
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  have hwit := early_witness_viable hrun hframe hw halo hahi hcw hvQ
  exact later_heads_of_windowWitness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb hw hat hcw
    hQw (Healing.windowWitness_of_frameWindow hrun hnc hframe hw hQ hwit)
    (fun y i hy hlo hhi => hframe.finalized_below_descendant_at hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ hwit hQ .refl) hXQ hbase hK r hrlo hrN

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest
(`frameIn_at`). -/
private theorem frameIn_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H := by
  have h := AC.frameIn_of_callAt (acRun_prefix hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨h.1, h.2.trans (RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg i))⟩

/-- Joinedness of the cast bounds its relay deadlines (`witness_voterBlockTree_at` over the
shadow run): an early frame witness is in the next-slot voter's block tree. -/
theorem witness_voterBlockTree_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {w y : Fin sp.n} {a i : Nat} (hw : w ∈ H (tr.time a)) (hy : y ∈ H (tr.time i))
    {ellw ell : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQw : Q ∈ ellw.frame.tree)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = s + 1) (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ AC.voterBlockTree sp e.readPoint ell.frame (s + 1) := by
  have ht0 := hrun.time_nonneg i
  have hr := (acRun_prefix hrun hnc ht0).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have subU := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono ht0
  obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc.1
  have hQU := (frameIn_at hrun hnc hw hcw).2 hQw
  have hslot : sp.slot (tr.time i) = s + 1 := (AC.castAt_specU hr.toU hy hc').2.1.symm.trans hs
  have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
  have hts := AC.ts_succ s (sp := sp)
  have hΔ := sp.toParams.hΔ
  have hfz : AC.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by
    simp only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = s by omega]
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hjoined := (AC.castAt_specU hr.toU hy hc').2.2.1
    have hj : AC.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAtU hr.toU hy hc']
      exact hjoined
    intro k hk hrestart
    have h := (AC.joined_awakeU sp _ (H (tr.time i)) _ _ hr.toU y hy i ell hc'.1 hj).2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hrun.time_mono hk, hrestart⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at h
    simpa only [hslot, show ((s + 1 : Nat) : Int) - 1 = s by omega] using h
  have hdl : ∀ k ≤ i, ∀ t, t < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k t < sp.ts s + 3 * sp.Δ := by
    intro k hk t ht
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
      (fun r hr hrestart => hrs r (hr.trans hk) hrestart) t
    have hm' : max t (sp.ts s) < sp.ts s + 2 * sp.Δ := max_lt ht (by linarith only [hΔ])
    change tr.projAC.deadline y k t ≤ max t (sp.ts s) + sp.Δ at h
    linarith only [hm', h]
  have ha : AC.AcceptedBefore (tr.projAC.upTo (tr.time i)) y Q (AC.freeze sp (s + 1)) := by
    rcases Healing.Growing.frame_block_acceptance_at hrun hw hcw hQw with hg | ⟨k, hka, hwk, hk⟩
    · exact Or.inl (congrArg Block.root hg)
    obtain ⟨hk', htk, -⟩ := Healing.ac_block_after (hrun.upTo (hrun.time_nonneg a)).toLocalRun hw
      ((RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono hka.le, hk⟩)
    rw [RunTrace.upTo_projAC] at hk'
    have hacc := (ACTrace.upTo_acceptAt.mp hk').2
    have hwk' : w ∈ H (tr.time (k + 1)) := by
      change tr.time (k + 1) = tr.time k at htk
      rwa [htk]
    have hkt : tr.time (k + 1) < sp.ts s + 2 * sp.Δ := by
      change tr.time (k + 1) = tr.time k at htk
      rw [htk]
      exact (hrun.time_mono hka.le).trans_lt hat
    have hex : ∃ q ≤ i, tr.projAC.AcceptAt y q Q ∧ tr.time q < AC.freeze sp (s + 1) := by
      by_cases hkg : gbar g ≤ tr.time (k + 1)
      · obtain ⟨q, hqi, hq, hqt⟩ :=
          (Healing.Growing.KernelProof.service_syncACAt hrun hsvc (lo := g) (hi := tr.time (k + 1))
              le_rfl).2
            w (k + 1) Q hwk' hacc ((Healing.le_gbar g).trans hkg) le_rfl y i ell hy hc.1
            (by have := hdl i le_rfl _ hkt;
                change tr.projAC.deadline y i (tr.time (k + 1)) ≤ tr.time i;
                linarith only [this, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; exact hqt.trans (hdl q hqi _ hkt)⟩
      · obtain ⟨q, hqi, hq, hqt⟩ := hrun.toLocalRun.acCatchAt hcatch hwk' hacc
          (lt_of_not_ge hkg) hy hc.1 (by linarith only [hm, hti, hts, hΔ]) hFQ
        exact ⟨q, hqi, hq, by rw [hfz]; linarith only [hqt, hm, hΔ]⟩
    obtain ⟨q, hqi, hq, hqt⟩ := hex
    exact Or.inr ⟨q, ACTrace.upTo_acceptAt.mpr ⟨hrun.time_mono hqi, hq⟩, hqt⟩
  have hQt : Q ∈ ell.frame.tree := by
    rcases ha with hg | ⟨k, hk, hkt⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy i ell hc'.1
      obtain rfl : Q = G := hU.1 hQU (subU hGU) (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFQ with heq | ⟨P, -, hP⟩
      · exact heq ▸ hPhi.rooted.1
      · exact False.elim (Option.some_ne_none _ (hP.2.2.symm.trans hGp))
    · have hki : k ≤ i := by
        by_contra hn
        have ht := hrun.time_mono (show i ≤ k by omega)
        change tr.time k < _ at hkt
        rw [hfz] at hkt
        linarith only [ht, hkt, hti, hts, hΔ]
      obtain ⟨ella, hca, hba⟩ := hk
      have hk : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k Q := ⟨ella, hca, hba⟩
      have hQp := (AC.frameIn_of_callAt hr hy hca).2 ((AC.accept_new sp hr hy hk).1 _ hca)
      exact AC.mem_tree_of_acceptAtU sp hr.toU hy hk hki hc'.1
        (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht0 hQp hFQ)
  have hstamp := AC.readPoint_blockStamp_lt_of_acceptedBefore hr hrun.vstart hy hc' hQt
    (by simpa only [hs] using ha)
    (fun k hk hrk => by
      have h := hrs k hk (ACTrace.upTo_restartAt.mp hrk).2
      change tr.time k < _
      rw [hs, hfz]
      linarith only [h, hΔ])
    (by change AC.freeze sp e.msg.slot ≤ tr.time i; rw [hs, hfz];
        linarith only [hti, hts, hΔ])
  exact ⟨hQt, Or.inl (by simpa only [hs] using hstamp)⟩

/-- A window witness propagates its prefix to next-slot votes: the window-free core of
`next_votes_of_early_witness_at'` and `next_votes_of_stock_witness_at'`. -/
theorem next_votes_of_windowWitness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a)) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hW : Healing.WindowWitness tr H (sp.ts s) hi Q)
    (hfin : ∀ y i, y ∈ H (tr.time i) → sp.ts s ≤ tr.time i → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F Q)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have htime {y i ell e} (hy : y ∈ H (tr.time i)) (hc : AC.CastAt tr.projAC y i ell e)
      (hs : e.msg.slot = s + 1) : sp.ts s ≤ tr.time i ∧ tr.time i ≤ hi := by
    have ht0 := hrun.time_nonneg i
    have hti : sp.ts (s + 1 : Nat) ≤ tr.time i := (AC.ts_le_iff_le_slot sp ht0 _).2
      (by rw [← (Compose.Growing.castAt_spec_at hrun hnc hy hc).2.1, hs])
    have hts := AC.ts_succ s (sp := sp)
    refine ⟨by linarith only [hti, hts, sp.toParams.hΔ], ?_⟩
    have ht := (Compose.Growing.cast_head_fcRoot_at hrun hnc hy hc).2
    rw [hs] at ht
    exact ht.trans hnext
  have hkernel := Healing.Growing.UnanimousStep.next_votes_extend_of_viable
    (m := s) (P := X) (b := hi) hrun hnc
    (hviable := fun y i ell e hy hcast hs _ _ => by
      obtain ⟨hlo, hhi⟩ := htime hy hcast hs
      have hfr := frame_of_projAC_at hrun hy hcast.1
      have hmargin : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n :=
        sp.toParams.fg.faults_lt_quorum_margin (hf _ (hrun.time_nonneg i) (hhi.trans hmb))
      have hFQ := hfin y i hy hlo hhi
      have hFe : ell.frame.F = (tr.state y i).fg.F := by
        rw [hfr, Node.frame_eq, Store.toFrame_F]
      rcases AC.anc_total hU hFQ hXQ with hFX | hXF
      swap
      · exact Or.inl (hFe ▸ hXF)
      have hdom := witness_voterBlockTree_at hrun hnc hsvc hcatch hm hw hy hcw hat hQw
        hcast hs (hFe ▸ hFX.trans hXQ)
      have hQy : Q ∈ (tr.state y i).fg.tree := by
        have ht := hdom.1
        rw [hfr, Node.frame_eq, Store.toFrame_tree] at ht
        exact ht.1
      obtain ⟨hFQy, hvy⟩ := hW.held y i hy hlo hhi hmargin hQy
      rcases Healing.witness_frame_of_held hrun hnc hy hcast.1 hQy hFQy hvy hXQ with
        hXF | ⟨-, -, hroot, -, hvQ, hXQf⟩
      · exact Or.inl hXF
      have hr := (acRun_prefix hrun hnc (hrun.time_nonneg i)).localRun
      have hdomA := AC.voterBlockTree_ancU hr.toU hrun.vstart hy
        (AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩)
      rw [hs] at hdomA
      exact Or.inr ⟨hFe ▸ hFX, Or.inl ⟨hdomA Q hdom X hXQf, hroot, Q, hdom, hvQ, hXQf⟩⟩)
    (htransfer := fun y i ell e hy hcast hs hib hFX hV hearlier =>
      htransfer y i ell e hy hcast hs hib
        (by rw [← frame_of_projAC_at hrun hy hcast.1]; exact hFX) hV
        (fun z k ev hki hz hv hes => hearlier z k hki hz ev hv hes))
  intro y i e hy hv hs
  obtain ⟨ell, hc⟩ := hv
  exact hkernel y i e hy ⟨ell, hc⟩ (htime hy hc hs).2 hs

/-- Common early-witness induction with the lock-specific transfer supplied by the caller
(`next_votes_of_early_witness_at` over the shadow run, witness `hvQ` read inside the window). -/
theorem next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s) hi M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hahi : tr.time a ≤ hi := by
    linarith only [hat, AC.ts_succ s (sp := sp), hnext, sp.toParams.hΔ]
  have hwit := early_witness_viable hrun hframe hw halo hahi hcw hvQ
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    have h := hQw
    rw [frame_of_projAC_at hrun hw hcw, Node.frame_eq, Store.toFrame_tree] at h
    exact h.1
  exact next_votes_of_windowWitness_at hrun hnc hsvc _hawake hf hcatch hm hnext hmb hw hat hcw
    hQw (Healing.windowWitness_of_frameWindow hrun hnc hframe hw hQ hwit)
    (fun y i hy hlo hhi => hframe.finalized_below_descendant_at hrun hnc hy hw hw
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le (hhi.trans hmb)
          (hahi.trans hmb)))) hlo hhi hQ hwit hQ .refl) hXQ htransfer
end Consensus.Goldilocks.Shadow.PU.Growing

end
