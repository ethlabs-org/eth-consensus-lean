module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.World
public import ConsensusLean.Instances.Goldilocks.AsChainShape
@[expose] public section

/-! # Late publication of a signed FG attestation

A bounded continuation of the two-validator fixture (`ΔAC = 1`). Validator zero signs its
first row at time 5. The release schedule may suppress its poll at that time without suppressing
signing. The other validator's schedule is unchanged. -/

namespace Consensus.Goldilocks.Witness.LateRelease

open AC AsChainShape Simulation TwoRun
open Blocks Shape

/-- Only validator zero is denied release, from time 5 up to but excluding `stop`. -/
def releaseUntil (stop : Time) (y : Fin sp.n) (t : Time) : Bool :=
  decide (y ≠ w0 ∨ t < 5 ∨ stop ≤ t)

/-- The signing poll of the first row, after the AC tick of time 5. That AC tick is silent and
does not change the node, by `tick_report_ac` on the fixture's state at time 5. -/
noncomputable def signer : State sp ro where
  self := w0
  node := (world 5).1 w0
  now := 5
  outbox := []
  relayBuf := []
  fgDue := true
  ticked := true

private theorem signer_reports : (Node.acToFG signer.node 5).2.2 = some (blk 1) := by
  obtain ⟨hfg, _, _, hac⟩ := world_good 5 w0
  rw [show tip 5 = 1 from rfl] at hfg hac
  rw [show rep 5 = 0 from rfl] at hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  exact (ac_report hf (by decide) hac).2

private theorem signer_attests : ∃ Λ, (Node.acToFG signer.node 5).1.fg.attest
    (Node.acToFG signer.node 5).1.record w0 (blk 1) = some (row w0 1, Λ) := by
  obtain ⟨hfg, _, hrec, _⟩ := world_good 5 w0
  rw [show tip 5 = 1 from rfl] at hfg
  rw [show nrw 5 = 0 from rfl] at hrec
  obtain ⟨Λ, ha, _⟩ := attest_new hfg le_rfl w0 hrec
  exact ⟨Λ, ha⟩

/-- Poll the signing duty at time 5 under a bounded release denial. -/
noncomputable def signingPoll (stop : Time) := pollBatch signer 5 (releaseUntil stop)

private theorem signer_pool_empty : signer.node.fg.atts = [] := by
  change ((world 5).1 w0).fg.atts = []
  rw [(world_good 5 w0).atts]
  rfl

private theorem signingPoll_spec {stop : Time} (h : 5 < stop) :
    ∃ Λ, signingPoll stop =
      ({ signer with
          node := { (Node.acToFG signer.node 5).1 with record := Λ }
          fgDue := false
          held := [row w0 1] }, []) := by
  obtain ⟨Λ, ha⟩ := signer_attests
  have hdeny : releaseUntil stop signer.self signer.now = false := by
    change releaseUntil stop w0 5 = false
    simp [releaseUntil, not_le.mpr h]
  have hup : fgUpdate signer (releaseUntil stop) =
      { signer with
          node := { (Node.acToFG signer.node 5).1 with record := Λ }
          fgDue := false
          held := [row w0 1] } := by
    rw [fgUpdate_eq signer (releaseUntil stop)]
    have hdeny' : releaseUntil stop w0 5 = false := hdeny
    simp only [show signer.now = 5 from rfl, show signer.self = w0 from rfl,
      signer_reports, ha, hdeny', Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨Λ, ?_⟩
  unfold signingPoll pollBatch
  rw [show (releaseUntil stop signer.self signer.now && signer.ticked) = false by rw [hdeny]; rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold poll
  rw [ite_eq_left (show signer.fgDue = true from rfl), hup]
  rfl

private theorem releaseUntil_gap (stop : Time) (hstop : 5 ≤ stop) (y : Fin sp.n) (t : Time) :
    ∃ u, t ≤ u ∧ u ≤ t + (stop - 5) ∧ releaseUntil stop y u = true := by
  change ∃ u : Int, t ≤ u ∧ u ≤ t + (stop - 5) ∧ releaseUntil stop y u = true
  change (5 : Int) ≤ stop at hstop
  by_cases ht : t < 5 ∨ stop ≤ t
  · exact ⟨t, le_rfl, by omega, by simp [releaseUntil, ht]⟩
  · have h5 : (5 : Int) ≤ t := le_of_not_gt (fun h => ht (Or.inl h))
    have hts : t ≤ stop := le_of_not_ge (fun h => ht (Or.inr h))
    exact ⟨stop, hts, by omega, by simp [releaseUntil]⟩

/-- (b) With R = 1 the first row is held outside the signer's pool and batch at time 5.
At time 6 an early poll still cannot release it; after the tick step, a poll admits it to
the pool, publishes it alone, and empties the queue. -/
theorem release_gap_one :
    (∀ y t, ∃ u, t ≤ u ∧ u ≤ t + 1 ∧ releaseUntil 6 y u = true) ∧
    (signingPoll 6).1.held = [row w0 1] ∧ (signingPoll 6).2 = [] ∧
    (signingPoll 6).1.node.fg.atts = [] ∧
    let early := { (signingPoll 6).1 with now := 6, ticked := false }
    pollBatch early 6 (releaseUntil 6) = (early, []) ∧
    let sent := pollBatch { early with ticked := true } 6 (releaseUntil 6)
    sent.1.held = [] ∧ sent.1.node.fg.atts = [row w0 1] ∧
      sent.2 = [(Body.att (encodeAtt (row w0 1)), [])] := by
  refine ⟨releaseUntil_gap 6 (by decide), ?_⟩
  obtain ⟨Λ, hs⟩ := signingPoll_spec (stop := 6) (by decide)
  rw [hs]
  refine ⟨rfl, rfl, signer_pool_empty, rfl, rfl, ?_, rfl⟩
  change (signer.node.fg.onAttestation (row w0 1)).atts = [row w0 1]
  simp [Store.onAttestation, signer_pool_empty]

/-- The local proposal state at slot 2. The denied poll supplies the held queue, and the
stock fixture's only pooled row is absent because it has not been admitted. -/
noncomputable def proposalState : State sp ro :=
  { signer with
    node := { (world 8).1 w0 with fg := { ((world 8).1 w0).fg with atts := [] } }
    now := 8
    fgDue := false
    held := (signingPoll 9).1.held }

/-- (b) With R = 4 the denied poll before slot 2 keeps the old row. The actual proposal
operation then omits that row, which the same proposal with no held rows would carry; the
first allowed poll after the proposal releases it. This is a bounded local continuation of
the stock fixture: changing slot 2's payload changes its digest, so the stock run's later
votes and block deliveries cannot be reused. -/
theorem denied_proposal_omits_held :
    (∀ y t, ∃ u, t ≤ u ∧ u ≤ t + 4 ∧ releaseUntil 9 y u = true) ∧
    let pre := (pollBatch proposalState 8 (releaseUntil 9)).1
    let sent := propose pre 2
    let flushed := pollBatch { sent.1 with now := 9 } 9 (releaseUntil 9)
    let p := ([vote w0 1, vote w1 1], [vote w0 1, vote w1 1])
    let parent := parentRef sp.genesisRoot (some (blk 1).root)
    (pollBatch proposalState 8 (releaseUntil 9)).2 = [] ∧
    (propose { pre with held := [], node := (world 8).1 w0 } 2).2 =
      some (parent, encodeInfo [row w0 1] p, payloadObjs [row w0 1] p) ∧
    sent.2 = some (parent, encodeInfo [] p, payloadObjs [] p) ∧
    flushed.1.held = [] ∧ flushed.2 = [(Body.att (encodeAtt (row w0 1)), [])] := by
  refine ⟨releaseUntil_gap 9 (by decide), ?_⟩
  classical
  obtain ⟨hfg, hatts, _, hac⟩ := world_good 8 w0
  rw [show tip 8 = 1 from rfl] at hfg hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  have hp : ((world 8).1 w0).ac.pool 1 = [vote w0 1, vote w1 1] := by
    rw [hac.pool]; rfl
  have hv (y : Fin sp.n) : ((world 8).1 w0).ac.voteStamp (vote y 1) < ⊤ := by
    have hm : vote y 1 ∈ poolT w0 8 1 := by
      rw [← hac.pool, hp]; rcases eq_w0_or_w1 y with rfl | rfl <;> simp
    rw [hac.vstamp 1 _ hm]; exact etime_of_lt_top _
  have hb : ((world 8).1 w0).ac.blockStamp (blk 1).root < ⊤ := by
    rw [hac.bstamp 1 le_rfl le_rfl]; exact etime_of_lt_top _
  obtain ⟨L, d, hprop, hd, _, _⟩ :=
    acProposal_tick hf hac.restart hp hv hb hac.locks hac.tipLock
  change AC.acProposal sp ((world 8).1 w0).ac (Node.frame ((world 8).1 w0)) 8 = _ at hprop
  have ha : ((world 8).1 w0).fg.proposalAttestations (blk 1) = [row w0 1] := by
    rw [proposalAttestations_blk hfg (by rw [hatts]; rfl), blk_fgPayload]
    rfl
  obtain ⟨Λ, hs⟩ := signingPoll_spec (stop := 9) (by decide)
  have hhold : proposalState.held = [row w0 1] := by
    change (signingPoll 9).1.held = _
    rw [hs]
  have hempty : proposalState.node.fg.proposalAttestations (blk 1) = [] := by
    simp [proposalState, Store.proposalAttestations]
  have hpre : pollBatch proposalState 8 (releaseUntil 9) = (proposalState, []) := by
    rfl
  dsimp only
  rw [hpre]
  have hjust (st : State sp ro) (hac' : st.node.ac = ((world 8).1 w0).ac)
      (hf' : Node.frame st.node = Node.frame ((world 8).1 w0)) (ht : st.now = 8) :
      let p := ([vote w0 1, vote w1 1], [vote w0 1, vote w1 1])
      let atts := st.node.fg.proposalAttestations (blk 1)
      propose st 2 =
        ({ st with node := { st.node with ac := { ((world 8).1 w0).ac with locks := L } } },
          some (parentRef sp.genesisRoot (some (blk 1).root),
            encodeInfo atts p, payloadObjs atts p)) := by
    dsimp only
    rw [propose_eq]
    unfold Node.acProposal
    change (let r := AC.acProposal sp st.node.ac (Node.frame st.node) st.now; _) = _
    simp only [hac', hf', ht, hprop, hd]
  have hheld := hjust proposalState rfl rfl rfl
  refine ⟨rfl, ?_, ?_⟩
  · rw [hjust _ rfl rfl rfl]; dsimp only; rw [ha]
  · rw [hheld]
    rw [hempty]
    refine ⟨rfl, ?_⟩
    unfold pollBatch proposalState
    rw [hs]
    exact ⟨rfl, rfl⟩

/-- (b) R = 0: the stock signing poll appends nothing to `held` and the batch is exactly the
ordinary poll body, with no extra release of the signed row. -/
theorem stock_signing_batch :
    (pollBatch signer 5).1.held = [] ∧
    (pollBatch signer 5).2 = [(Body.att (encodeAtt (row w0 1)), [])] := by
  obtain ⟨Λ, ha⟩ := signer_attests
  have hfg : fgUpdate signer =
      { signer with
        node := (Node.onAttestation { (Node.acToFG signer.node 5).1 with record := Λ } (row w0 1)).1
        fgDue := false
        outbox := [Body.att (encodeAtt (row w0 1))] } := by
    rw [fgUpdate_eq]
    simp only [show signer.now = 5 from rfl, show signer.self = w0 from rfl, signer_reports, ha,
      ↓reduceIte]
    rfl
  change (poll signer 5).1.held = [] ∧ (poll signer 5).2.toList ++ [] ++ [] ++ [] = _
  unfold poll
  rw [ite_eq_left (show signer.fgDue = true from rfl)]
  rw [hfg]
  exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.Witness.LateRelease

end
