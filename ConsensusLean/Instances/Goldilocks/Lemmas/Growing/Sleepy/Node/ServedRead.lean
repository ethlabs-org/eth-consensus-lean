module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Gate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Regimes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the head at a read and the record step

The dynamic forms of `read_head_support_before` (G1, G2 at a read) and `record_step_upTo` (G3)
of `Compose/Sleepy/Served`, from the dynamic invariant `Growing.SleepyInvariantUpTo`.

The chain-generic steps of `Compose/Sleepy/Served` (`Compose/Sleepy/ServedSteps`, shared with
it: `ReadInvWith`, `head_support_at`, `record_step_of` and the read and tick machinery under them)
are applied to the prefix `tr.upTo d` with the honest set `H d`. Every node they name is honest at
`d`: the reader (honest at its cut `i`, after the read time `t`) and the validators the read
classifies, at `d = t` (the record writer at `d = tr.time i` for the record step). The chain
predicate `Ch` is the dynamic `OnOriginChainWithin` and the origin predicate `O` the dynamic
`OriginWithin`; the steps read them only as hypotheses. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- An older origin has a read majority when the latest slot's honest votes are delivered. -/
private theorem origin_read_majority_at {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SleepyServiceBefore tr H ΔF b) {K : SA.CommitteeDict sp.n}
    (hKB : CommitteeFacts tr H K) (hBK : CommitteeBoundsFrom tr H K 0 b)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (hi : ∀ k < i, tr.time k ≤ t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} {j q : Nat}
    (hO : OriginWithin tr H R j b) (hjq : j < q)
    (hL : (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 = q)
    (hrd : ReadAtCut proposer dg (tr.upTo t) y i t)
    (hRt : R ∈ (Node.frame (tr.state y i)).tree) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard := by
  have hst : (tr.upTo t).state y i = tr.state y i := Trace.upTo_state tr y hi
  have hLp : (q : Int) = (SA.latestView sp ((tr.upTo t).state y i).ac
      (Node.frame ((tr.upTo t).state y i)) t).2 := by rw [hst]; exact hL.symm
  have hqt : sp.ts q + sp.Δ ≤ t := by
    have h := (latest_slot_tick_at_read (hrun.upTo ht0) hy hrd hLp).1
    linarith [sp.toParams.hΔ]
  have hall : ∀ x k e, HVoteAt tr H x k e → e.msg.slot = q →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg R := by
    intro x k e hv hs
    obtain ⟨hx, ℓ, hc⟩ := hVoteAt_iff.1 hv
    have hkt := (cast_time_at hrun hnc hx hc).2
    rw [hs] at hkt
    exact hinv.vote_extends R j hO x k e hv (hkt.trans (hqt.trans htb)) (hs ▸ hjq)
  exact read_majority_of_extending_at hrun hnc hKB.hP ht0 hy hi hL
    (extendingMajority_of_all_at hrun hnc hKB.hGate hall hqt
      (hBK.slotK q t (Nat.zero_le _) hqt htb (latestView_lt_six ht0 hL.symm).le))
    hRt (by
      intro x k e hv hx hs hext
      obtain ⟨hxk, ℓ, hc⟩ := hVoteAt_iff.1 hv
      have hkt := (cast_time_at hrun hnc hxk hc).2
      rw [hs] at hkt
      have hvp : SA.VoteAt (tr.upTo t).projAC x k e := by
        rw [RunTrace.upTo_projAC]
        exact sa_voteAt_upTo.mpr ⟨hkt.trans hqt, ℓ, hc⟩
      have hac := (SleepyServiceBefore.upTo hrun hsync ht0).ac
      have hsyncp : ReadSyncOrService (tr.upTo t) (H t) t := Or.inr
        { message := fun x hx k v hv h0 z hz j ℓ hc hdl hj =>
            hac.message x hx k v hv h0 z hz j ℓ hc (hdl.trans (le_min htb le_rfl)) hj
          relay := fun x hx k B hB h0 z hz j ℓ hc hdl hj ha =>
            hac.relay x hx k B hB h0 z hz j ℓ hc
              (hdl.trans (le_min htb le_rfl)) hj ha }
      have hpool := latest_vote_delivered (hrun.upTo ht0) (hnc.upTo t)
        (Or.inl hsyncp) hy hrd hLp hx hvp hs
      obtain ⟨Hd, hHd, hHdr, hRHd⟩ := voteExtends_upTo hrun hnc ht0 hx hvp hext
      have hΦ := frameOK_at hrun ht0 hy hi
      have hΦU : (Node.frame (tr.state y i)).tree ⊆ (tr.upTo t).HonestBlocks (H t) := by
        intro X hX
        exact ⟨y, hy, i, by rw [hst]; exact hX.1⟩
      have hF : Anc ((tr.upTo t).HonestBlocks (H t))
          ((tr.upTo t).state y i).fg.F Hd := by
        rw [hst]
        exact ((hΦ.rooted.2 R hRt).mono hΦU).trans hRHd
      obtain ⟨hHdt, hstamp⟩ := honest_head_in_frame_at_read (hrun.upTo ht0) (hnc.upTo t)
        (Or.inl hsyncp) hy hrd hLp hx hvp hs hHd hHdr hF
      rw [hst] at hpool hHdt
      rw [projAC_state (hrun.upTo ht0).toLocalRun hy i, hst] at hstamp
      exact ⟨hpool, Hd, hHdt, hHdr, hstamp⟩)

/-- The origins before a cut of the prefix through `d` are origins of the run, within every
horizon after the cut's earlier cuts. -/
private theorem originWithin_of_upTo' {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {d b : Time}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s m : Nat}
    (hm : ∀ k < m, tr.time k ≤ b) (h : Compose.OriginBefore (tr.upTo d) (H d) C s m) :
    OriginWithin tr H C s b := by
  obtain ⟨x, hx, k, hk, CV, hO⟩ := Compose.originBefore_iff.1 h
  rw [RunTrace.upTo_projAC] at hO
  rcases hO with hO | hO
  · obtain ⟨hkd, hO⟩ := (sa_resultAt_upTo hrun.time_mono).mp hO
    exact OriginWithin.of_result (hrun.antitone hkd hx) (hm k hk) hO
  · obtain ⟨hkd, hO⟩ := (sa_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact OriginWithin.of_optimistic (hrun.antitone hkd hx) (hm k hk) hO

/-- **The static read invariant of the prefix** through the read time `t ≥ 0`, for a reader
honest at `t` and the state before a cut `m` whose earlier cuts are at or before `t`, from the
dynamic invariant up to `b ≥ t` and the service up to `b`. -/
private theorem readInvWith_upTo {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    (hsync : SleepyServiceBefore tr H ΔF b) {y : Fin sp.n} {m : Nat} {t : Time}
    (hy : y ∈ H t) (ht0 : 0 ≤ t) (htb : t ≤ b)
    (hm : ∀ k < m, tr.time k ≤ t) :
    Compose.ReadInvWith (tr.upTo t) (H t) (fun B => OnOriginChainWithin tr H B b)
      (fun C s => OriginWithin tr H C s b) y m t
      (Compose.ReadSyncOrService (tr.upTo t) (H t) t) := by
  have hsub := upTo_subset hrun ht0
  have hst : ∀ m' ≤ m, (tr.upTo t).state y m' = tr.state y m' := fun m' hm' =>
    Trace.upTo_state tr y fun k hk => hm k (by omega)
  have hmt : ∀ m' ≤ m, ∀ k < m', tr.time k ≤ t := fun m' hm' k hk => hm k (by omega)
  have hmb : ∀ m' ≤ m, ∀ k < m', tr.time k ≤ b := fun m' hm' k hk => (hm k (by omega)).trans htb
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y m t ht0 hm htb hy
  have hac := (SleepyServiceBefore.upTo hrun hsync ht0).ac
  refine
    { compat := fun X Y hX hY hXc hYc => compatible_upTo hrun hnc ht0 hX hY
        (OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible (hsub hX) (hsub hY)
          hXc hYc)
      anc := fun A B hA hAB h => OnOriginChainWithin.of_anc hrun hnc (hsub hA) (hAB.mono hsub) h
      record := ⟨C, by rw [hst m le_rfl]; exact hC, by rw [hst m le_rfl]; exact hCr,
        onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
      locks := by
        rw [hst m le_rfl]
        exact hinv.locks y m t ht0 hm htb hy
      caches := by
        rw [hst m le_rfl]
        exact hinv.caches y m t ht0 hm htb hy
      origin := fun C s h => originWithin_of_upTo' hrun (hmb m le_rfl) h
      viable := fun m' hm' C s hO hC => by
        rw [hst m' hm'] at hC ⊢
        exact hinv.viable y m' t ht0 (hmt m' hm') htb hy C s hO hC
      vote_extends := fun C s hO x hx k hk e hv hs => by
        have hv' := hv
        rw [RunTrace.upTo_projAC] at hv'
        obtain ⟨hkd, hv'⟩ := sa_voteAt_upTo.mp hv'
        exact voteExtends_upTo hrun hnc ht0 hx hv
          (hinv.vote_extends C s hO x k e (hVoteAt_iff.2 ⟨hrun.antitone hkd hx, hv'⟩)
            (hmb m le_rfl k hk) hs)
      sync := Or.inr
        { message := fun x hx k v hv h0 z hz j ℓ hc hdl hj =>
            hac.message x hx k v hv h0 z hz j ℓ hc (hdl.trans (le_min htb le_rfl)) hj
          relay := fun x hx k B hB h0 z hz j ℓ hc hdl hj ha =>
            hac.relay x hx k B hB h0 z hz j ℓ hc
              (hdl.trans (le_min htb le_rfl)) hj ha } }

/-- **G1, G2 at a read under growing faults** (the dynamic `read_head_support_before`): the state
of a node before cut `i`, read at a time `t ∈ [0, b]` at which it is honest, at or after every
cut before `i` and at or before cut `i`, the node awake and joined at `t`: the anchor at `t` is
compatible with the record's block `R`, and `R` is at or below it, or viable with a strict majority
of the latest view's voters at `t` as supporters. For an older origin of `R` the majority is the
committee slot count of `hBK` at the latest view's slot, charged at the read time `t`, over that
slot's honest votes, which extend the origin and are delivered before the read
(`origin_read_majority_at`). -/
theorem read_head_support_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    (hsync : SleepyServiceBefore tr H ΔF b) {y : Fin sp.n} {i : Nat} {t : Time}
    (hy : y ∈ H t) (ht0 : 0 ≤ t) (htb : t ≤ b)
    {K : SA.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b)
    (hle : ∀ k < i, tr.time k ≤ t) (hti : t ≤ tr.time i)
    (hwj : tr.awake y t ∧ tr.JoinedAt y t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : RecordAt tr y i R) :
    Compatible (Node.frame (tr.state y i)).tree
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
              t).1.votes).ncard <
            2 * (SA.supporters (Node.frame (tr.state y i))
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
              R).ncard)) := by
  have hst : (tr.upTo t).state y i = tr.state y i := Trace.upTo_state tr y hle
  have h := Compose.read_head_support_of (hrun.upTo ht0) (hnc.upTo _) hy
    (fun m hm _ => readInvWith_upTo hinv hrun hnc hsync hy ht0 htb hm) hle hti
    (fun _ => ⟨⟨hwj.1, le_rfl⟩, joinedAt_upTo hwj.2⟩) (R := R)
    (by rw [RecordAt, hst]; exact hR)
    (by
      intro m hm _ hrd hRm j hO hjl
      have hstm : (tr.upTo t).state y m = tr.state y m := Trace.upTo_state tr y hm
      rw [RecordAt, hstm] at hRm
      rw [hstm] at hjl ⊢
      obtain ⟨q, hq⟩ : ∃ q : Nat, (q : Int) =
          (SA.latestView sp (tr.state y m).ac (Node.frame (tr.state y m)) t).2 :=
        ⟨_, Int.toNat_of_nonneg (by omega)⟩
      exact origin_read_majority_at hrun hnc hinv hsync hKB hBK ht0 htb hy hm hO
        (by omega) hq.symm hrd hRm.1)
  rwa [hst] at h

/-- **G3 under growing faults, the record step**: at a cut of a node honest then, with every cut up
to it at a time `≤ b`, the record moves to a descendant (inside the blocks held while honest). -/
theorem record_step_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hi : ∀ k ≤ i, tr.time k ≤ b) :
    ∀ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocksAt H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocksAt H) E E' := by
  intro E hE hEr
  have hd : 0 ≤ tr.time i := hrun.time_nonneg i
  have hsub := upTo_subset (d := tr.time i) hrun hd
  have hyd : y ∈ H (tr.time i) := hy
  have hi' : ∀ k < i, tr.time k ≤ b := fun k hk => hi k hk.le
  have hst : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono hk.le
  have hst' : (tr.upTo (tr.time i)).state y (i + 1) = tr.state y (i + 1) :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have ⟨C, hC, hCr, hgo⟩ := hinv.record_at_cut hrun (hd.trans (hi i le_rfl)) hy hi'
  have hCU : C ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := ⟨y, hyd, i, hst ▸ hC⟩
  obtain rfl : E = C := (honestBlocksAt_coherent hrun hnc).1 hE (hsub hCU) (hEr.trans hCr.symm)
  obtain ⟨E', hE', hE'r, hEE'⟩ := Compose.record_step_of (hrun.upTo hd) (hnc.upTo _) hyd i
    (Ch := fun B => OnOriginChainWithin tr H B b)
    (fun X Y hX hY hXc hYc => compatible_upTo hrun hnc hd hX hY
      (OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible (hsub hX) (hsub hY)
        hXc hYc))
    ⟨E, by rw [hst]; exact hC, by rw [hst]; exact hCr,
      onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨E, s, hs, .refl⟩)⟩
    (by rw [hst]; exact (hinv.caches_at_cut hrun (hd.trans (hi i le_rfl)) hy hi').1)
    (fun C s CV hO => by
      rw [RunTrace.upTo_projAC] at hO
      refine onOriginChainWithin_iff.2 (Or.inr ⟨C, s, ?_, .refl⟩)
      rcases hO with hO | hO
      · exact OriginWithin.of_result hy (hi i le_rfl)
          ((sa_resultAt_upTo hrun.time_mono).mp hO).2
      · exact OriginWithin.of_optimistic hy (hi i le_rfl)
          ((sa_optimisticLockAt_upTo hrun.time_mono).mp hO).2)
    E hCU (by rw [hst]; exact hEr)
  exact ⟨E', hsub hE', by rw [← hst']; exact hE'r, hEE'.mono hsub⟩

end Consensus.Goldilocks.Compose.Growing

end
