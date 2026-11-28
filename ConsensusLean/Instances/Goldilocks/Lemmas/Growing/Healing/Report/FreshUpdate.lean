module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.LocalFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTick
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective

public section

/-! # Fresh updates: unlock, selection and viability -/

namespace Consensus.Goldilocks.Healing.Growing

/-! ## Older locks after an honest next-slot unlock

Only the receiver's execution through the receiving cut is retained. The supporting
committee belongs to the unlock frame, rather than a run-wide honest cohort.
-/

section

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- A vote branch of the prefix through `d` is a vote branch of the run at a time `≤ d`. -/
theorem voteBranchAt_upTo_iff (hm : Monotone tr.time) {d : Time} {y : Fin sp.n} {j : Nat}
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n} :
    AC.VoteBranchAt (tr.projAC.upTo d) y j ell R ↔
      tr.time j ≤ d ∧ AC.VoteBranchAt tr.projAC y j ell R := by
  have hs (ht : tr.time j ≤ d) := Trace.upTo_state tr.projAC y (d := d) (i := j)
    fun _ hk => (hm hk.le).trans ht
  rw [AC.voteBranchAt_iff, AC.voteBranchAt_iff]
  constructor
  · rintro ⟨hc, hrest⟩
    have ht := ((Trace.upTo_callAt _).mp hc).1
    rw [hs ht] at hrest
    exact ⟨ht, ((Trace.upTo_callAt _).mp hc).2, hrest⟩
  · rintro ⟨ht, hc, hrest⟩
    refine ⟨(Trace.upTo_callAt _).mpr ⟨ht, hc⟩, ?_⟩
    rw [hs ht]
    exact hrest

/-- A supporting half-committee at a receiver's next-slot vote branch clears old incompatible
labels for a receiver that is still honest at the later observation, from starts up to the vote
permission. The branch need not emit, so the receiver need not vote in that slot. -/
theorem older_locks_compatible_after_unlock_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {j k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hs : sp.slot (tr.time j) = u + 1) (hjk : j < k)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    {S : Set (Fin sp.n)}
    (hS : ∀ x ∈ S,
      x ∈ AC.equivocators (AC.mergedVoteView sp R ell.frame (u + 1)).votes ∨
        ∃ v ∈ (AC.mergedVoteView sp R ell.frame (u + 1)).support,
          v.val = x ∧ (v.slot : Int) = u ∧ AC.AncR ell.frame P v.head)
    (hhalf : sp.committeeSize ≤ 2 * S.ncard) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P := by
  have hd := hrun.time_nonneg k
  have hr := (Compose.Growing.acRun_upTo hrun hnc hd).localRun
  have hb' : AC.VoteBranchAt (tr.projAC.upTo (tr.time k)) y j ell R :=
    (voteBranchAt_upTo_iff hrun.time_mono).2 ⟨hrun.time_mono hjk.le, hb⟩
  have hstate := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hsub := Compose.Growing.upTo_subset hrun hd
  intro l hl hls L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by
    rwa [hstate]
  obtain ⟨_, _, _, _, B, hB, hBr, _⟩ :=
    AC.lock_provenanceU (hr := hr.toU) hrun.vstart hy k l hl'
  have hLB : L = B := (hrun.toLocalRun.coherent hnc).1
    hL (hsub hB) (hLr.trans hBr.symm)
  subst L
  exact (AC.older_locks_compatible_after_unlock_branch hr hy hb' hs hjk hPt hS hhalf
    l hl' hls B hB hBr).imp (Anc.mono hsub) (Anc.mono hsub)

end

/-! ## Fresh fast locks and their adjacent report reads

The update and report are consecutive actual calls. Local execution is retained only
through their common timestamp; no later honesty of the original proposer is required.
-/

section

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Explicit joinedness, rather than a stronger GST margin, supplies actual votes
by the slot deadline from the healthy base on that deadline's prefix. -/
theorem honest_votes_of_joined_before_at {K : AC.CommitteeDict sp.n}
    {g : Time} {u : Nat}
    (hS : AC.HealthyBaseUpTo K (tr.projAC.upTo (sp.ts u + sp.Δ))
      (H (sp.ts u + sp.Δ)) ((tr.upTo (sp.ts u + sp.Δ)).HonestBlocks (H (sp.ts u + sp.Δ)))
      proposer g (sp.ts u + sp.Δ))
    (hgu : gbar g ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ)) :
    ∀ x, x ∈ H (sp.ts u + sp.Δ) → x ∈ K.committee u →
      ∃ j e, AC.VoteAt tr.projAC x j e ∧ e.msg.slot = u ∧
        tr.time j ≤ sp.ts u + sp.Δ := by
  intro x hx hxK
  obtain ⟨j, e, hv, hs, ht⟩ := AC.honest_votes_of_joined_before hS hgu le_rfl
    (fun x hx r hrs hrt => by
      obtain ⟨ell, hc, hrestart⟩ := hrs
      exact hjoin x hx r
        ⟨ell, ((Trace.upTo_callAt _).mp hc).2, hrestart⟩ hrt) x hx hxK
  obtain ⟨ell, hc, he⟩ := hv
  exact ⟨j, e, ⟨ell, ((Trace.upTo_callAt _).mp hc).2, he⟩, hs, ht⟩

/-- Explicit joinedness gives every honest node, committee member or not, a vote branch of the
slot by its deadline, from the healthy base on that deadline's prefix. -/
theorem honest_vote_branches_of_joined_before_at {K : AC.CommitteeDict sp.n}
    {g : Time} {u : Nat}
    (hS : AC.HealthyBaseUpTo K (tr.projAC.upTo (sp.ts u + sp.Δ))
      (H (sp.ts u + sp.Δ)) ((tr.upTo (sp.ts u + sp.Δ)).HonestBlocks (H (sp.ts u + sp.Δ)))
      proposer g (sp.ts u + sp.Δ))
    (hgu : gbar g ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ)) :
    ∀ x, x ∈ H (sp.ts u + sp.Δ) →
      ∃ j ell R, AC.VoteBranchAt tr.projAC x j ell R ∧ sp.slot (tr.time j) = u ∧
        tr.time j ≤ sp.ts u + sp.Δ := by
  intro x hx
  obtain ⟨j, ell, R, hb, hs, ht⟩ := AC.honest_vote_branches_of_joined_before hS hgu le_rfl
    (fun x hx r hrs hrt => by
      obtain ⟨ell, hc, hrestart⟩ := hrs
      exact hjoin x hx r
        ⟨ell, ((Trace.upTo_callAt _).mp hc).2, hrestart⟩ hrt) x hx
  exact ⟨j, ell, R, ((voteBranchAt_upTo_iff hS.run.localRun.time_mono).1 hb).2, hs, ht⟩

/-- A vote by a validator still honest at the read has its strict early message
stamp in the receiver's pool, at the slot committees `K` of a run from `K`'s committee start.
Only the receiving prefix is used. -/
theorem honest_vote_early_pool_before_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    {x : Fin sp.n} (hx : x ∈ H (tr.time j)) {i : Nat}
    {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : AC.VoteAt tr.projAC x i e) (hes : e.msg.slot = u)
    (hit : tr.time i ≤ tr.time j) (hK : CommitteeHalfUpTo tr H K g b) :
    e.msg ∈ (tr.projAC.state y j).pool u ∧
      (tr.projAC.state y j).voteStamp e.msg < AC.ETime.of (sp.ts u + 2 * sp.Δ) := by
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch (hrun.time_nonneg j) hjb
  have hs := Trace.upTo_state tr.projAC y (i := j)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hv' : AC.VoteAt (tr.projAC.upTo (tr.time j)) x i e := by
    obtain ⟨ellx, hcx, he⟩ := hv
    exact ⟨ellx, (Trace.upTo_callAt _).mpr ⟨hit, hcx⟩, he⟩
  have hrst : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts u := by
    intro k _ ⟨ellk, hck, hk⟩
    have hkt := ((Trace.upTo_callAt _).mp hck).1
    have hbound := hnr y k (hrun.antitone hkt hy)
      (Compose.projAC_restartAt.mp ⟨ellk, ((Trace.upTo_callAt _).mp hck).2, hk⟩)
    linarith [sp.toParams.hΔ]
  have hp := AC.honest_vote_early_pool_before hS hy hc'
    (by linarith [sp.toParams.hΔ]) ht le_rfl
    (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrst r (hr.trans hkj) hrs).le) t)
    hrst hx hv' hes j (Or.inl rfl)
  simpa only [hs] using hp

/-- A historically honest acceptance supplies the receiver's strict block stamp,
without retaining sender honesty until the receiving call, from any vote-permitted start. -/
theorem blockStamp_early_of_historical_acceptance_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hgu : gbar g ≤ sp.ts u)
    {x y : Fin sp.n} {i j : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i P)
    (hti : tr.time i = sp.ts u)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hPt : P ∈ ell.frame.tree) :
    (tr.projAC.state y j).blockStamp P.root < AC.ETime.of (sp.ts u + 2 * sp.Δ) := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg j)).localRun
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hPhi := AC.frameIn_of_callAt hr hy hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono
    (hrun.time_nonneg j)
  obtain ⟨q, hqj, haq, hqt⟩ := accepted_relay_before_at hrun hsvc hnr hx ha
    (hti ▸ hgu) hy hc (by rw [hti]; linarith [sp.toParams.hΔ])
    ((hPhi.1.rooted.2 P hPt).mono (fun Q hQ => hsub (hPhi.2 hQ)))
  have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y q P := by
    obtain ⟨ellq, hcq, heq⟩ := haq
    exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqj, hcq⟩, heq⟩
  have hp := AC.blockStamp_lt_of_acceptedBeforeU sp hr.toU hrun.vstart hy hc' hPt
    (Or.inr ⟨q, haq', by change tr.time q < _; rw [hti] at hqt; linarith [sp.toParams.hΔ]⟩)
    (fun k _ hrs => by
      have hck := hrs.choose_spec.1
      have hrt := ((Trace.upTo_callAt _).mp hck).1
      have hb := hnr y k (hrun.antitone hrt hy)
        (Compose.projAC_restartAt.mp
          ⟨hrs.choose, ((Trace.upTo_callAt _).mp hck).2, hrs.choose_spec.2⟩)
      change tr.time k < _
      linarith [sp.toParams.hΔ]) (Or.inl ht)
  simpa only [Trace.upTo_state tr.projAC y (i := j)
    (fun q hq => hrun.time_mono hq.le)] using hp

/-- Early proposal resolution needs historical block relay only for the block
stamp. Vote delivery and uniqueness are charged at the receiving cut. The pool holds the votes
of the honest members of the slot committee `K u`, for a run from `K`'s committee start. -/
theorem unanimous_early_pool_of_blockStamp_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hbs : (tr.projAC.state y j).blockStamp P.root <
      AC.ETime.of (sp.ts u + 2 * sp.Δ))
    (hvotes : ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ i e,
      AC.VoteAt tr.projAC x i e ∧ e.msg.slot = u ∧ tr.time i ≤ tr.time j)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ v ∈ (tr.projAC.state y j).pool u,
      v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v <
        AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch (hrun.time_nonneg j) hjb
  have hr := hS.run.localRun
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hs := Trace.upTo_state tr.projAC y (i := j)
    (fun q hq => hrun.time_mono hq.le)
  have hPhi := AC.frameIn_of_callAt hr hy hc'
  intro x hx hxK
  obtain ⟨i, e, hv, hes, hit⟩ := hvotes x hx hxK
  have hv' : AC.VoteAt (tr.projAC.upTo (tr.time j)) x i e := by
    obtain ⟨ellx, hcx, he⟩ := hv
    exact ⟨ellx, (Trace.upTo_callAt _).mpr ⟨hit, hcx⟩, he⟩
  have heP := hun x i e (hrun.antitone hit hx) hv hes
  obtain ⟨hm, hvs⟩ := honest_vote_early_pool_before_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hy hc ht hjb hx hv hes hit hK
  have hval := (AC.castAt_specU hr.toU hx ⟨hv'.choose_spec.1, hv'.choose_spec.2⟩).1
  refine ⟨e.msg, hm, hval, heP,
    AC.resolutionTime_lt_of hPhi.1 hPt heP.symm (by omega) hvs (heP ▸ hbs), ?_⟩
  intro v' hm' hv'x
  have hm'' : v' ∈ ((tr.projAC.upTo (tr.time j)).state y j).pool u := by
    rwa [hs]
  obtain ⟨q, _, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j u v' hm'' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨_, rfl⟩ := AC.one_vote_per_slotU sp _ _ _ _ hr.toU x hx q i e' e he' hv'
    ((AC.state_pool_slotU sp hr.toU hS.run.vstart hy j u _ hm'').trans hes.symm)
  rfl

/-- The warm route assembles the early unanimous pool using only joinedness at
the vote deadline and historical honesty of the proposal's first acceptance, for the honest
members of the slot committee `K u` of a run from `K`'s committee start. -/
theorem unanimous_early_pool_of_acceptance_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} {a : Nat} (hz : z ∈ H (tr.time a))
    (ha : tr.projAC.AcceptAt z a P) (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ v ∈ (tr.projAC.state y j).pool u,
      v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v <
        AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hgu : gbar g ≤ sp.ts u := by linarith [sp.toParams.hΔ]
  have hshort : sp.ts u + sp.Δ ≤ tr.time j := by linarith [sp.toParams.hΔ]
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by
      linarith [AC.gbar_nonneg g, sp.toParams.hΔ]) (hshort.trans hjb)
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  exact unanimous_early_pool_of_blockStamp_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hPs hun hy hc ht hjb hPt
    (blockStamp_early_of_historical_acceptance_at hrun hnc hsvc hnr hgu hz ha hta hy hc ht hPt)
    (fun x hx hxK => by
      obtain ⟨i, e, hv, hes, hit⟩ := hvotes x (hrun.antitone hshort hx) hxK
      exact ⟨i, e, hv, hes, hit.trans hshort⟩) hK

/-- Wakefulness and the receiver's restart cutoff produce the actual joined update, whether or
not its tick signs, from any vote-permitted start. -/
theorem update_call_of_awake_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {u : Nat}
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell, AC.UpdateAt tr.projAC y k u ell := by
  let T := sp.ts (u + 1 : Nat) + 2 * sp.Δ
  have hT : T = sp.ts u + 6 * sp.Δ := by
    dsimp only [T, ACParams.ts]
    push_cast
    ring
  have hΔ := sp.toParams.hΔ
  have hT0 : 0 ≤ T := by
    rw [hT]
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    linarith
  have hr := hrun.upTo hT0
  have hslot : sp.slot T = u + 1 := by
    rw [hT]
    apply AC.slot_of_mem sp (u + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith
  have hjoin : ∀ i, (tr.upTo T).time i = sp.ts u + 6 * sp.Δ →
      AC.joined sp ((tr.upTo T).projAC.state y i) ((tr.upTo T).time i) := by
    intro i hi
    unfold AC.joined
    have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo T)).localRun
    rcases AC.restartTime_stateU hac.toU hrun.vstart hy i with h | ⟨r, _, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [hi, ← hT, hslot, show ((u + 1 : Nat) : Int) - 1 = u by omega]
      rw [RunTrace.upTo_projAC] at hrs
      have hrt := ((Trace.upTo_callAt _).mp hrs.choose_spec.1).1
      have hrestart : tr.RestartAt y r := Compose.projAC_restartAt.mp
        ⟨hrs.choose, ((Trace.upTo_callAt _).mp hrs.choose_spec.1).2, hrs.choose_spec.2⟩
      have hbound := hnr y r (hrun.antitone hrt hy) hrestart
      change tr.time r ≤ _
      linarith
  obtain ⟨k, ell, hu⟩ :=
    Healing.update_call_of_awake hr hy
      ⟨hT ▸ hawake y T hy (by rw [hT]; linarith) hTb, hT.symm.le⟩ hjoin
  have hkt : tr.time k ≤ T := by
    have h := hu.2.2.1
    change tr.time k = sp.ts u + 6 * sp.Δ at h
    exact (h.trans hT.symm).le
  rw [RunTrace.upTo_projAC] at hu
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => (hrun.time_mono hq.le).trans hkt)
  refine ⟨k, ell, ?_⟩
  refine ⟨((Trace.upTo_callAt _).mp hu.1).2, hu.2.1, hu.2.2.1, ?_⟩
  simpa only [hs, Trace.upTo_time] using hu.2.2.2

/-- Signing ticks supply the joined update and its adjacent to-FG call. -/
theorem update_toFG_calls_of_awake_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {u : Nat}
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hsign : sign y (sp.ts (u + 1 : Nat) + 2 * sp.Δ) = true) :
    ∃ k ell ell', AC.UpdateAt tr.projAC y k u ell ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (k + 1) = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      ell'.frame = ell.frame := by
  have hΔ := sp.toParams.hΔ
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
  have hpub : sp.toParams.IsPublic (sp.ts u + 6 * sp.Δ) :=
    ⟨4 * (u : Int) + 6, by simp only [ACParams.ts]; ring⟩
  have hgu : gbar g ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by rw [hT]; linarith
  obtain ⟨j, w, hg⟩ := signTickAt_of_calendar_at hrun hcal (hT ▸ hy)
    (by linarith) hpub (hT ▸ hawake y _ hy hgu hTb) (hT ▸ hsign)
  obtain ⟨ell, ell', hc, hcall, ht, hc', hto, ht', hfr⟩ :=
    Healing.toFG_second_cut_of_signing_tick hg (Healing.not_proposes_update_time y u)
      fun i c hci hti => hrun.cutLaw y i c hci (by rw [hti]; exact hT ▸ hy)
  have hjoin := joined_of_restart_le_at hrun hnc hy
    (by rw [hT]; linarith : sp.ts u + 4 * sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    (fun r _ hyr hrs => (hnr y r hyr hrs).trans (by linarith)) (ht.trans hT.symm)
  exact ⟨j, ell, ell', ⟨hc, hcall, ht, hjoin⟩, hc', hto, ht'.trans hT.symm, hfr⟩

/-- Once selection and no-veto are known, local execution inserts the fresh fast lock.
The conclusion keeps its two-slot lifetime independently of the service proof. From any start. -/
theorem fresh_fast_lock_of_selection_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu : AC.UpdateAt tr.projAC y k u ell) (hPt : P ∈ ell.frame.tree)
    (hconf : AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P)
    (hfast : AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P)
    (hva : ell.frame.viableAncestor P = P) :
    ∃ e, u + 2 ≤ e ∧
      (⟨P.root, u, true, e⟩ : AC.Lock) ∈ (tr.projAC.post k).locks := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg k)).localRun
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hpost := Obligations.post_of_update hr hy
    ((AC.upTo_updateAt hrun.time_mono).2 ⟨le_rfl, hu⟩)
  rw [Trace.upTo_post, hs, Trace.upTo_time] at hpost
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.projAC.time k) = u + 1 := by
    change sp.slot (tr.time k) = u + 1
    rw [hkt]
    apply AC.slot_of_mem sp (u + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  rw [hpost]
  have hwf := AC.locksWF_state hr hrun.vstart hy k
  rw [hs] at hwf
  exact AC.fastLock_mem_updateConfirmation_floor hPt hva hconf hnv hfast
    (by rw [hslot]; have := sp.two_le_k; omega)
    (fun l hl => hwf.cap hl) (by omega)

end

/-! ## Full-frame viability through an honest observation

Persistence is local to the receiver. The retained frame window ends at the actual
observation, rather than extending the receiver's honesty beyond that cut.
-/

section

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- A call-local viability witness fixes its viable ancestor. -/
theorem proposal_viable_after_votes_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y k ell) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hroot : ell.frame.Anc ell.frame.fcRoot P)
    (hv : P ∈ ell.frame.viableHeads) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg k)).localRun
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hv, .refl⟩
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  exact ⟨hvi, AC.viableAncestor_self (AC.frameIn_of_callAt hr hy hc').1 hPt (Or.inl hvi), hv⟩

/-- At an actual update the warm unanimous pool forces confirmation and fast
selection, at the slot committees `K` of a run from `K`'s committee start. No
lock-compatibility premise is used to select the raw result. -/
theorem unanimous_update_selection_at
    {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b)
    (hvi : P ∈ ell.frame.viableTree ell.frame.tree)
    (hva : ell.frame.viableAncestor P = P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have _ := hdes
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hlate : sp.ts u + 2 * sp.Δ ≤ tr.time k := by rw [hkt]; linarith
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith) hz
  have hp := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hacc := (Healing.accept_of_proposesAt hp (hnc.upTo _) hzk hP').1
  obtain ⟨ha', hta', _⟩ := Healing.ac_block_after hp.toLocalRun hzk hacc
  have ha : tr.projAC.AcceptAt z (kP + 1) P := by
    rw [RunTrace.upTo_projAC] at ha'
    obtain ⟨ella, hca, hea⟩ := ha'
    exact ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
  have hta : tr.time (kP + 1) = sp.ts u := hta'.trans htime
  have hza : z ∈ H (tr.time (kP + 1)) := hta' ▸ hzk
  have hpool := unanimous_early_pool_of_acceptance_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hPs hun hza ha hta hy hu.1 hlate hkb hvi.1 hK
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg k)).localRun
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hPg : P.root ≠ sp.genesisRoot := by
    have hra := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg (kP + 1))).localRun
    apply AC.accept_ne_genesisU sp hra.toU hza
    obtain ⟨ella, hca, hea⟩ := ha
    exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
  have hslots : ∀ v ∈ (tr.projAC.state y k).pool u, v.slot = u := by
    intro v hv
    apply AC.state_pool_slotU sp hr.toU hrun.vstart hy k u v
    rwa [hs]
  obtain ⟨hconf, hfast⟩ := AC.confirmation_of_unanimous_early_pool
    (AC.frameIn_of_callAt hr hy hc').1 hvi.1 hPg K (hK.facts.hsize u)
    (fun v hv => hK.facts.hP.1 (tr.time k) y hy k (fun q hq => hrun.time_mono hq.le) u v hv)
    (hK.cs2 u hgu (by linarith) _ (hrun.time_nonneg k) hkb) hslots hpool
  exact ⟨hvi, hconf, hfast, hva⟩

end

end Consensus.Goldilocks.Healing.Growing

end
