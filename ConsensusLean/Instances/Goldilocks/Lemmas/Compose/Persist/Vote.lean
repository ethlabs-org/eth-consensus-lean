module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore

public section

/-! # Goldilocks Persist, part 2: the vote step of C1.1

At an honest vote of a slot `σ ∈ (s, m]` (a cut of the run's AC projection), with the caches of
the voter compatible with `B`: (i) `B` is in the viable voter block tree or at or below `fc_root`
(`FrameGeometry.viable_of_frozen_witnesses`: the voter's `fc_root` is its `Σ.J` or `Σ.F`, then
(K2)), and (ii) the vote extends `B` (below `fc_root` by requirement 1, otherwise by A1.2 for
`σ = s + 1` and A1.3 after). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

/-! ### Honest votes on an AC trace of the SA -/

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- Every emission of a call has a duty head whose root is the vote's head, and is cast no later
than `Δ` after the start of the call's slot. -/
private def EmitsHeads (t : Time) (r : SA.SAState sp.n × List (SA.Em sp FGP)) : Prop :=
  ∀ e ∈ r.2, (∃ d, e.head = some d ∧ d.head.root = e.msg.head) ∧ t ≤ sp.ts (sp.slot t) + sp.Δ

private theorem tryVote_emitsHeads (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : EmitsHeads t (SA.tryVote sp x A Φ t) := by
  unfold SA.tryVote
  dsimp only
  split_ifs with h1
  · simp [EmitsHeads]
  · simp [EmitsHeads]
  all_goals try simp only [EmitsHeads, List.not_mem_nil, false_imp_iff, implies_true]
  all_goals
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨_, rfl, rfl⟩, not_lt.1 (not_or.1 (not_or.1 h1).2).2⟩

private theorem step_emitsHeads (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SA.SAState sp.n)
    {Φ : SA.Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    EmitsHeads t ((goldilocksSA sp FGP ro).step self A Φ t c) := by
  cases c with
  | tick =>
    change EmitsHeads t (SA.acOnTick sp self A Φ t)
    unfold SA.acOnTick
    dsimp only
    split_ifs
    all_goals first
      | exact fun e he => tryVote_emitsHeads self A Φ t e he
      | simp [EmitsHeads]
  | message m => exact tryVote_emitsHeads self _ Φ t
  | block B => exact tryVote_emitsHeads self _ Φ t
  | proposal => simp [EmitsHeads, ACInterface.step]
  | toFG => simp [EmitsHeads, ACInterface.step]
  | restart =>
    intro e he
    change e ∈ (SA.acRestart sp ro self A Φ t).2 at he
    rw [(SA.restart_state sp FGP ro self A Φ t hΦ ht).1] at he
    simp at he

variable {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}

/-- The state before an honest call is reachable, with a frame and time from which the call is
lawful. -/
theorem pre_reachable {ini} (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hcall : tr.CallAt y i ℓ) :
    ∃ Φp tp, (goldilocksSA sp FGP ro).ReachableAtFrom (ini y) y U (tr.state y i) Φp tp ∧
      tp ≤ tr.time i ∧
      (goldilocksSA sp FGP ro).CallOK U Φp (tr.time i) ℓ.call ℓ.frame := by
  rcases hr.frameLaw y hy i ℓ hcall with ⟨hn, Φ₀, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
  · refine ⟨Φ₀, 0, ?_, hr.time_nonneg i, hok⟩
    rw [tr.state_of_noCall hn, hr.init y hy]
    exact .init Φ₀ hi hf
  · refine ⟨ℓ'.frame, tr.time j, ?_, hr.time_mono hj.le, hok⟩
    rw [tr.state_of_lastCall hc' hj hnb]
    exact localRun_reachable hr y hy j ℓ' hc'

/-- **An honest vote's head extends `fc_root`** (requirement 1, A0.6), and the vote is cast no
later than `Δ` after the start of its slot. -/
theorem cast_head_fcRoot {ini} (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, SA.VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ := by
  have hU := hr.coherent
  obtain ⟨hcall, he⟩ := hc
  have hx := hr.exec i ℓ hcall.2 (hcall.1 ▸ hy)
  rw [hcall.1] at hx
  obtain ⟨Φp, tp, hreach, htp, hok⟩ := pre_reachable hr hy hcall
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).2 := by
    rw [hx]; exact he
  obtain ⟨⟨d, hd, hdr⟩, hle⟩ :=
    step_emitsHeads ro y (tr.state y i) hok.1.1 (hr.time_nonneg i) ℓ.call e he'
  have hok' := (((SA.interface_requirements_from sp FGP ro (hini y)).1 y U hU _ _ _
    (ACInterface.reachableAtFrom_iff.1 hreach)).2
    (tr.time i) ℓ.call.toStart ℓ.frame htp
    (ACInterface.callOK_ofStart.2 (by rw [ACInterface.Call.ofStart_toStart]; exact hok)) e
    (by rw [ACInterface.step_ofStart, ACInterface.Call.ofStart_toStart]; exact he') d hd).1
  have hs := (SA.castAt_spec hr hy ⟨hcall, he⟩).2.1
  refine ⟨⟨d.head, ?_, hdr, hok'⟩, hs ▸ hle⟩
  by_cases hne : ℓ.frame.fcRoot = d.head
  · exact hne ▸ hok.1.1.fcRoot_mem
  · exact (Anc.mem hok' hne).2

end SA

/-! ### Honest votes in a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}

/-- The frame of an honest AC cut of a run is `fg_to_ac(Σ)` of the node's state. -/
theorem frame_of_projAC {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame = Node.frame (tr.state y k) :=
  (hrun.cutLaw y hy k _ (projAC_callAt.mp hc)).1

/-- `Sync` on a window gives it on every subwindow. -/
theorem syncAC_mono {P : Params} {FGP : Type} {A : ACInterface P FGP} {H : Set (Fin P.n)}
    {U : Set A.Blk} {a b a' b' : Time} {tr : ACTrace A} (h : SyncAC A H U a b tr) (ha : a ≤ a')
    (hb : b' ≤ b) : SyncAC A H U a' b' tr :=
  ⟨fun x hx i m hs h₁ h₂ => h.1 x hx i m hs (ha.trans h₁) (h₂.trans hb),
    fun x hx i B hB h₁ h₂ => h.2 x hx i B hB (ha.trans h₁) (h₂.trans hb)⟩

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

end Consensus.Goldilocks.Compose

end
