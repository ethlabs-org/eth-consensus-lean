module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVotes

public section

/-! # Goldilocks Healing: proposal holding from a writer, and vote transfer

* `heldAtProposal_of_writer`: a vote of an honest writer in `[t_σ, t_σ + 2Δ)` whose head extends
  the proposer's `Φ.F` reaches the honest proposer of slot `σ + 1`;
* `result_prefix_vote_extends_of_stored`: an honest vote of slot `s + 1` carrying a slot-`s` result
  extends a block below the result, from the stored locks and the earlier same-label votes;
* `next_vote_extends_before`: an honest vote of slot `m + 1` extends `B` when the honest votes of
  slots `m` and `m + 1` at earlier cuts do. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {g t₀ : Time} {proposer : Nat → Fin sp.n}

/-- **(P) from a writer, after the GST or by catch-up**: a slot-`σ` vote sent or admitted by an
honest writer in `[t_σ, t_σ + 2Δ)`, whose head extends the proposer's `Φ.F` and is genesis, or
was accepted by the writer from `a₀` on before `t_σ + 2Δ`, or by the proposer before `t_σ + 3Δ`,
reaches the honest proposer of slot `σ + 1`
(Sync relays the vote and the head before `t_σ + 3Δ`; rooted retention keeps the head). -/
theorem heldAtProposal_of_writer {ini} (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {a₀ b : Time} (hsync : SyncAC (goldilocksAC sp FGP ro) H U a₀ b tr) {σ : Nat}
    (ha₀ : a₀ ≤ sp.ts σ) (hb : sp.ts σ + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (ht : tr.time i = sp.ts (σ + 1 : Nat))
    (hrs : ∀ k ≤ i, tr.RestartAt x k → tr.time k < sp.ts σ) {v : Vote sp.n} (hvs : v.slot = σ)
    (hsend : ∃ k, tr.SendOrAdmit w k v ∧ sp.ts σ ≤ tr.time k ∧ tr.time k < sp.ts σ + 2 * sp.Δ)
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
      (Hv.root = sp.genesisRoot ∨
        (∃ k, tr.AcceptAt w k Hv ∧ a₀ ≤ tr.time k ∧ tr.time k < sp.ts σ + 2 * sp.Δ) ∨
        ∃ k ≤ i, tr.AcceptAt x k Hv ∧ tr.time k < sp.ts σ + 3 * sp.Δ)) :
    HeldAtProposal (tr.state x i) ℓ.frame σ v := by
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts σ + 2 * sp.Δ → tr.deadline x k τ < sp.ts σ + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hk) hr').le) τ
    have h₂ := max_lt hτ (show sp.ts σ < sp.ts σ + 2 * sp.Δ by linarith only [hΔ])
    change tr.deadline x k τ ≤ max τ (sp.ts σ) + sp.Δ at h₁
    linarith only [h₂, h₁]
  refine heldAtProposal_iff.2 ⟨?_, ?_⟩
  · obtain ⟨k, hsk, hk1, hk2⟩ := hsend
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hsync.1 w hw k v hsk (ha₀.trans hk1) (by
        linarith only [hb, hk2])
      x hx i ℓ hc (by linarith only [hdl i le_rfl _ hk2, ht, hk1, hk2, hts])
    have hk'lt : tr.time k' < sp.ts σ + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hk2)
    have hk'i' : k' < i := lt_of_le_of_ne hk'i (by rintro rfl; linarith only [hΔ, hts, hk'lt, ht])
    have hnr : ∀ r, k' + 1 ≤ r → r < i → ¬ tr.RestartAt x r := fun r h₁ h₂ hrr => by
      have := hrs r h₂.le hrr
      have := hr.time_mono (show k' ≤ r by omega)
      linarith
    have hsk' : sp.slot (tr.time k') = σ :=
      slot_of_mem sp σ (hk1.trans hkk') (by rw [hts]; linarith only [hk1, hk2, hk'lt])
    have hmono := pool_mono hr hx (show k' + 1 ≤ i by omega) hnr σ
    have h := held_of_processAtU hr.toU hx hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk'])
    rw [hvs] at h
    exact backed_mono (P := {w | w ∈ (tr.state x (k' + 1)).pool σ})
      (Q := {w | w ∈ (tr.state x i).pool σ}) (fun _ hw => hmono hw) h
  · obtain ⟨Hv, hHv, hHvr, hFHv, hacc⟩ := hhead
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr.toU hx i ℓ hc
    obtain ⟨hHt, hAB⟩ : Hv ∈ ℓ.frame.tree ∧ AcceptedBefore tr x Hv (sp.ts σ + 3 * sp.Δ) := by
      rcases hacc with hg | ⟨kw, hkw, hkwa, hkwt⟩ | ⟨ky, hky, hacc, hkyt⟩
      · refine ⟨?_, Or.inl hg⟩
        obtain rfl : Hv = G := hU.1 hHv hGU (hg.trans hGr.symm)
        obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFHv
        · exact h ▸ hΦ.rooted.1
        · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
      · obtain ⟨ky, hky, hacc, hkyt⟩ := hsync.2 w hw kw Hv hkw hkwa (by
          linarith only [hb, hkwt]) x hx i ℓ hc
          (by linarith only [hdl i le_rfl _ hkwt, ht, hΔ, hts]) hFHv
        exact ⟨mem_tree_of_acceptAtU sp hr.toU hx hacc hky hc hFHv,
          Or.inr ⟨ky, hacc, hkyt.trans (hdl ky hky _ hkwt)⟩⟩
      · exact ⟨mem_tree_of_acceptAtU sp hr.toU hx hacc hky hc hFHv, Or.inr ⟨ky, hacc, hkyt⟩⟩
    refine ⟨Hv, hHt, hHvr, ?_⟩
    exact (blockStamp_lt_of_acceptedBeforeU sp hr.toU hini hx hc hHt hAB
      (fun k hk hrk => (hrs k hk hrk).trans (by linarith only [hΔ]))
      (Or.inl (by
          rw [ht, hts]; linarith only [hΔ]))).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))

/-- Current-cut result-prefix transfer, for the slot committees `K` (P, and CS2 at the label
`s + 1`). Service and viability are current inputs; stored older locks and earlier same-label
votes account for the live read-point locks. -/
theorem result_prefix_vote_extends_of_stored {ini} (hrun : ACRun proposer tr H U ini)
    (K : CommitteeDict sp.n) (hP : CommitteeP K tr H) {x y : Fin sp.n} (hx : x ∈ H)
    (hy : y ∈ H) {r s i : Nat} {B C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hf : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (hres : ResultAt tr x r s C CV) (hBC : Anc U B C)
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hstored : ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ U, Y.root = l.block → Compatible U Y B)
    (hE : EarlierVotesExtend tr H U i (s + 1) B)
    (hmerged : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state x r).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state x r).pool s}) :
    VoteExtends U e.msg B :=
  result_transfer_ancU sp hrun.toU hx hres hBC hy hc hs hcarry hviab
    (live_locks_of_stored_before hrun K hP hf hy hc hs hstored hE) hmerged

/-- Later transfer needs extension only at earlier cuts, for the predecessor and
current labels, for the slot committees `K` (P, T, their size, CS at the label `m` and CS2 at
`m + 1`). Slot monotonicity places every predecessor vote before this cast. The `Sync`
argument is no longer needed (A1.3 dropped it); it stays for the callers' interface. -/
theorem next_vote_extends_before {ini} (hrun : ACRun proposer tr H U ini)
    (K : CommitteeDict sp.n) (hP : CommitteeP K tr H) (hT : CommitteeT K tr H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    {m i : Nat} {y : Fin sp.n} {B : Blk sp.n FGP}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} {e : Em sp FGP}
    (hy : y ∈ H) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = m + 1)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', VoteAt tr z q e' →
      (e'.msg.slot = m ∨ e'.msg.slot = m + 1) → VoteExtends U e'.msg B)
    (hhalf : sp.committeeSize ≤
      2 * {z | z ∈ H ∧ ∃ q e', VoteAt tr z q e' ∧ e'.msg.slot = m}.ncard)
    (hcarry : CarryAt tr U y i e m
      {v | ∃ z ∈ H, ∃ q e', VoteAt tr z q e' ∧ e'.msg = v ∧ v.slot = m})
    (hfault : FaultBoundK K m tr H (tr.time i))
    (hf1 : 2 * (K.committee (m + 1) ∩ Hᶜ).ncard < sp.committeeSize)
    (_hsync : SyncAC (goldilocksAC sp FGP ro) H U (sp.ts m) (tr.time i) tr)
    (hviab : ViableAtVote ℓ e (m + 1) B) :
    VoteExtends U e.msg B := by
  refine next_transfer_of_carry sp hrun K hP hT hsize hy hc hs ?_ hhalf hcarry hfault hf1 hviab
    (fun z hz q hq e' hv he => hprior z hz q hq e' hv (Or.inr he))
  intro z hz q e' hv he
  have hqi : q < i := by
    by_contra hn
    obtain ⟨ell, hcast⟩ := hv
    have hq := (castAt_specU hrun.localRun.toU hz hcast).2.1
    have hi := (castAt_specU hrun.localRun.toU hy hc).2.1
    have hmono := slot_mono sp (hrun.localRun.time_nonneg i)
      (hrun.localRun.time_mono (Nat.le_of_not_gt hn))
    omega
  exact hprior z hz q hqi e' hv (Or.inl he)

end Consensus.Goldilocks.AC

end
