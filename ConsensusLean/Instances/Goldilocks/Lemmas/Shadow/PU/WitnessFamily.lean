module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The early-witness family over the shadow run (interface)

The stock family (`FollowFinality`, `WitnessUnanimity`/`FollowWitnessBoundary`, `FollowRelay`,
`FreshVotesRelay`, `FollowInduction`, `FollowLaterBoundary`) carries a frozen witness `Q ⪰ X` by
`floor ≤ σ(Q).h` and `kindJ → J ⪯ X`, over a stock `FrameWindow`. Over the shadow frame the `J`
clause moves to the witness (`EarlyWitness`): a witness `Q` held by an honest `z` at cut `c` in a
`Healing.FrameWindow' … M isTop J` carries

  `M − 1 ≤ σ_z(Q).h ∧ (isTop → σ_z(Q).h = M − 1 → J ⪯ Q)` (the witness clause),

which `early_witness_viable'` supplies from `Q ∈ ellw.frame.viableHeads`. A shadow window with
`isTop` may change from top-clean to top-contest inside it (stock kept those apart), so the stock
lemmas are re-proved per cut, not instantiated: split on `σ(Q) ≥ M` (the stock contest and gap
argument) and `σ(Q) = M − 1` in a top window (`J ⪯ Q`).

Interface first: every statement below without a proof is unresolved until proved. The frame-relay
and stamp lemmas read only the frame's tree and `F`, which the shadow frame shares with the stock
one. The optimistic variants follow in this file. -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State} {hold : Time}

/-- Stub (Lane C `Run`): `Healing.ac_block_after` over the shadow run. -/
theorem ac_block_after_stub {P : Params} {A : NodeAC P} {tr : RunTrace A}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H₀ : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {ini}
    (_h : Node.LocalRun' proposer dg H₀ sg tr ini) {y : Fin P.n} (_hy : y ∈ H₀) {k : Nat}
    {B : A.Blk} (_ha : tr.AcceptAt y k B) :
    tr.projAC.AcceptAt y (k + 1) B ∧ tr.time (k + 1) = tr.time k ∧
      ¬ tr.RestartAt y (k + 1) := by
  sorry

/-- A block in an honest frame has an earlier honest FG acceptance, or is genesis
(`frame_block_acceptance_at`). -/
theorem frame_block_acceptance_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {x : Fin sp.n} {q : Nat}
    (hx : x ∈ H (tr.time q)) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt x q ell) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ell.frame.tree) :
    B = sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload ∨
      ∃ k < q, x ∈ H (tr.time k) ∧ tr.AcceptAt x k B := by
  have hd := hrun.time_nonneg q
  have ht : B ∈ ((tr.upTo (tr.time q)).state x q).fg.tree := by
    rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
    rw [frame_of_projAC_at' hrun hx hc, Node.frame'_eq, Store.toFrame'_tree] at hB
    exact hB.1
  rcases Coherence.tree_accepted' (hrun.upTo hd).toLocalRun' hx ht with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, hk, hrun.antitone (hrun.time_mono hk.le) hx,
      ((RunTrace.upTo_acceptAt _).mp ha).2⟩

/-- An honest acceptance reaches a later honest caller, after GST by relay and before it by
catch-up (`relayed_accept_before_at`). -/
private theorem relayed_accept_before_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {k j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hxk : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {elly : ACLabel (goldilocksNode' sp ro)} (hcy : tr.projAC.CallAt y j elly)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j) (hkt : tr.time k + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ a < j, tr.AcceptAt y a B ∧ tr.time a < max (tr.time k + sp.Δ) (gbar g + 2 * sp.Δ) := by
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl' : ∀ c ≤ j, tr.deadline y c (max (tr.time k) g) sp.Δ ≤ tr.time k + sp.Δ := by
      intro c hc
      rw [max_eq_left ((AC.le_gbar g).trans hnew), ← Compose.projAC_deadline]
      have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
        (fun r hrc hrs => hnr r (hrc.trans hc) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at h
      rwa [max_eq_left hnew] at h
    obtain ⟨a, haj, ha, hat⟩ := hsvc.relay x k B hxk ha ((AC.le_gbar g).trans hnew)
      y j hy ⟨_, Compose.projAC_callAt.mp hcy⟩ ((hdl' j le_rfl).trans hkt) hF
    refine ⟨a, lt_of_le_of_ne haj ?_, ha,
      lt_max_of_lt_left (hat.trans_le (hdl' a haj))⟩
    intro he
    subst a
    cases Option.some.inj (ha.2.symm.trans (Compose.projAC_callAt.mp hcy).2)
  · obtain ⟨a, hlt, hacc, hat⟩ := hrun.toLocalRun'.fgCatchAt' hcatch hxk ha
      (not_le.mp hnew) hy hg hF
    exact ⟨a, hlt, hacc, lt_max_of_lt_right hat⟩

/-- Historical frame membership relays without requiring the sender to remain honest
(`frame_relay_before_at` over the shadow run). -/
theorem frame_relay_before_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {q j : Nat} (hx : x ∈ H (tr.time q)) (hy : y ∈ H (tr.time j))
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    {ellx elly : ACLabel (goldilocksNode' sp ro)}
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
  have hac := Compose.goldilocks_ac_projection_from' hp (hnc.upTo _)
  have hPh := AC.frameIn_of_callAt hac.localRun hy hc'
  have hFstate : elly.frame.F = (tr.state y j).fg.F := by
    rw [frame_of_projAC_at' hrun hy hcy, Node.frame'_eq, Store.toFrame'_F]
  rcases frame_block_acceptance_at' hrun hx hcx hB with hgB | ⟨k, hk, hxk, ha⟩
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hac.localRun.toU hy j elly hc'
    have hBU : B ∈ tr.HonestBlocksAt H := by
      have hq0 := hrun.time_nonneg q
      have hcx' : (tr.upTo (tr.time q)).projAC.CallAt x q ellx := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcx⟩
      exact RunTrace.honestBlocks_upTo_subset hrun.time_mono hq0
        ((AC.frameIn_of_callAt (Compose.goldilocks_ac_projection_from' (hrun.upTo hq0)
          (hnc.upTo _)).localRun hx hcx').2 hB)
    have hcoh := Coherence.honestBlocksAt_coherent' hrun hnc
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
  obtain ⟨a, haj, ha, -⟩ := relayed_accept_before_at' hrun hsvc hcatch hxk ha hy hnr hcy hg hkt
    (hFstate ▸ hF)
  have ha' : (tr.upTo (tr.time j)).AcceptAt y a B :=
    (RunTrace.upTo_acceptAt _).mpr ⟨hrun.time_mono haj.le, ha⟩
  obtain ⟨hacc, _, _⟩ := ac_block_after_stub hp.toLocalRun' hy ha'
  have hBF : Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) elly.frame.F B := by
    obtain ⟨ella, hca, hba⟩ := hacc
    have ht := (AC.frameIn_of_callAt hac.localRun hy hca).2
      ((AC.accept_new sp hac.localRun hy ⟨ella, hca, hba⟩).1 ella hca)
    exact RunTrace.anc_upTo_of_right' hrun hnc hd ht hF
  exact AC.mem_tree_of_acceptAtU sp hac.localRun.toU hy hacc (by omega) hc' hBF

/-- An early frame witness has a pre-freeze stamp at a later honest cast
(`frame_witness_readPoint_stamp_at` over the shadow run). -/
theorem frame_witness_readPoint_stamp_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} {a i s : Nat} (hx : x ∈ H (tr.time a))
    (hy : y ∈ H (tr.time i))
    {ellx ell : ACLabel (goldilocksNode' sp ro)}
    (hcx : tr.projAC.CallAt x a ellx)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hes : e.msg.slot = s + 1) (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (ha : tr.time a < sp.ts s + 2 * sp.Δ)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hQ : Q ∈ ellx.frame.tree)
    (hFQ : Anc (tr.HonestBlocksAt H) ell.frame.F Q) :
    Q ∈ (tr.state y i).fg.tree ∧
      e.readPoint.blockStamp Q.root < AC.ETime.of (AC.freeze sp (s + 1)) := by
  sorry

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- **A window's witness places every honest finalized tip in it below an independently held
descendant** (`FrameWindow.finalized_below_descendant_at` over the shadow run, with the witness
clause on `X` in place of `floor ≤ σ(X).h` and `kindJ → J ⪯ X`). -/
theorem FrameWindow'.finalized_below_descendant_at' {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x z : Fin sp.n} {j i c : Nat}
    (hy : y ∈ H (tr.time j)) (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time j) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ X.root).h ∧
      (isTop → ((tr.state z c).fg.σ X.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J X))
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F W := by
  sorry

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State} {hold : Time}

/-- Prior votes extending a prefix propagate through a frozen viable witness
(`unanimous_next_votes_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_votes_of_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
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
  sorry

/-- The same prefix reaches an actual next-slot proposal head
(`unanimous_next_proposal_of_witness_at` over the shadow run, witness clause on `Q`). -/
theorem unanimous_next_proposal_of_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m M : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) M isTop J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hwit : M - 1 ≤ ((tr.state z c).fg.σ Q.root).h ∧
      (isTop → ((tr.state z c).fg.σ Q.root).h = M - 1 → Anc (tr.HonestBlocksAt H) J Q))
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j e →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  sorry

/-- **A next-vote base propagates through later labels** from an early viable witness
(`later_heads_of_early_witness_at` over the shadow run). The witness is a viable head of the
witness's call frame (`hvQ`), read inside the window (`halo`); `floor ≤ σ(Q).h` and
`kindJ → J ⪯ X` are replaced by it (`early_witness_viable'`). -/
theorem later_heads_of_early_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) (sp.ts N + sp.Δ) M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
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
  sorry

/-- An early viable witness propagates an optimistic prefix to later honest calls
(`optimistic_later_heads_of_early_witness_at` over the shadow run, witness `hvQ` read inside the
window). -/
theorem optimistic_later_heads_of_early_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {isTop : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) (sp.ts N + sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  sorry

/-- Common early-witness induction with the lock-specific transfer supplied by the caller
(`next_votes_of_early_witness_at` over the shadow run, witness `hvQ` read inside the window). -/
theorem next_votes_of_early_witness_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {isTop : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) hi M isTop J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame' (tr.state y i)).F X →
      AC.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → AC.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  sorry

/-- An optimistic write propagates a viable prefix to next-slot votes
(`optimistic_next_votes_of_early_witness_at` over the shadow run). -/
theorem optimistic_next_votes_of_early_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {isTop : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  sorry

/-- The first next-slot proposal follows the same prefix
(`optimistic_next_proposal_of_early_witness_at` over the shadow run). -/
theorem optimistic_next_proposal_of_early_witness_at' {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s M : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts (s + 1 : Nat) ≤ b)
    {isTop : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s) (sp.ts (s + 1 : Nat)) M isTop J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (halo : sp.ts s ≤ tr.time a) (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode' sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hvQ : Q ∈ ellw.frame.viableHeads)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  sorry

/-- An optimistic supporter's anchor propagates to later honest calls
(`optimistic_supporter_later_heads_at` over the shadow run). -/
theorem optimistic_supporter_later_heads_at' {s₀ s N M : Nat}
    {isTop : Prop} {J L D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = AC.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (AC.Vote sp.n)} (hop : AC.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  sorry

end Consensus.Goldilocks.Shadow.PU.Growing

end
