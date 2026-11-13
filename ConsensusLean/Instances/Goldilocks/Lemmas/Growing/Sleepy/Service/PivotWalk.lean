module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.PivotOld
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the pivot of a proposal

The σ-copy of the second half of `Compose/Service/Pivot`: the proposal walk passes every old
origin (`proposal_walk_passes_old_at`), and the pivot `D` of a proposal (`pivot_at`). The
proposer is honest at `t_s + Δ` (the hold), so at its proposal and at every slot-`s` vote, which is
cast by `t_s + Δ`; a voter is honest at its vote.

The steps of `Compose/Service/Pivot` whose nodes are honest at one time
(`Compose/Service/PivotSteps`, shared with it) are applied to the prefix through that time: the
proposal's anchor and suffix at `d = t_s` (`proposal_anchor_old_of`, `proposal_suffix_viable_of`,
with `proposal_rows_old_of`, `proposal_fcRoot_old_of`, `proposal_lock_below`), and a voter's
anchor at the vote's time (`vote_anchor_cases_of_old`, with `honest_eq_proposal_of_root`), where
the proposer is honest by the hold. Their old origins are origins of the prefix, so old origins of
the run (`oldOrigin_of_upTo`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- An old origin of the prefix through `d` is an old origin of the run. -/
theorem oldOrigin_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {d : Time} {s : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (h : Compose.OldOrigin (tr.upTo d) (H d) s O) :
    OldOrigin tr H s O := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := Compose.oldOrigin_iff.1 h
  · rw [RunTrace.upTo_projAC] at hR
    obtain ⟨hkd, hR⟩ := (sa_resultAt_upTo hrun.time_mono).mp hR
    exact oldOrigin_iff.2 ⟨x, k, m, CV, hrun.antitone hkd hx, Or.inl ⟨hR, hm⟩⟩
  · rw [RunTrace.upTo_projAC] at hO
    obtain ⟨hkd, hO⟩ := (sa_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact oldOrigin_iff.2 ⟨x, k, m, CV, hrun.antitone hkd hx, Or.inr ⟨hO, hm⟩⟩

/-- The proposal call and its duty head, read in the prefix through the call's time. -/
private theorem proposal_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {p : Fin sp.n}
    {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay)) :
    (tr.upTo (tr.time i)).projAC.CallAt p i ℓp ∧
      (SA.acProposal sp ((tr.upTo (tr.time i)).projAC.state p i) ℓp.frame (tr.time i)).2 =
        some (d, pay) := by
  rw [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl]
  exact ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hc, hd⟩

/-- **The proposal's anchor is below an old origin, or genesis** (lifted at `t_s`). -/
theorem proposal_anchor_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hstock : sp.committeeSize = sp.n) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocksAt H) d.start O := by
  have h0 := hrun.time_nonneg i
  obtain ⟨hc', hd'⟩ := proposal_upTo hrun hc hd
  rcases proposal_anchor_old_of (hrun.upTo h0) (hnc.upTo _) hf hp hc' hcall hd' hti hstock with
    h | ⟨O, hO, hsO⟩
  · exact Or.inl h
  · exact Or.inr ⟨O, oldOrigin_of_upTo hrun hO, hsO.mono (upTo_subset hrun h0)⟩

/-- **The proposal walk from `D` to `Q` is through viable heads**, for `D` of the proposal's frame
above every old origin (lifted at `t_s`). -/
theorem proposal_suffix_viable_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ ℓp.frame.tree)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O D)
    (hstock : sp.committeeSize = sp.n) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  have h0 := hrun.time_nonneg i
  obtain ⟨hc', hd'⟩ := proposal_upTo hrun hc hd
  exact proposal_suffix_viable_of (hrun.upTo h0) (hnc.upTo _) hf hp hc' hcall hd' hti hDt
    (fun O hO => RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0
      (frame_upTo_at hrun hnc hp hc hDt) (hDold O (oldOrigin_of_upTo hrun hO))) hstock

/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`** (lifted at the vote's time `d`,
with the proposer honest then): for a block `D` above every old origin and below `Q = P.parent`, at
a slot-`s` vote of a node honest then whose earlier slot-`s` votes by nodes honest at them are
`P`. -/
theorem vote_anchor_cases_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    (hf : 2 * (H (tr.time j))ᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H (tr.time j)) {k : Nat}
    {P Q D : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hkj : tr.time k ≤ tr.time j) (hs0 : 0 < s) (hPQ : P.parent = some Q.root)
    (hQU : Q ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)))
    (hDQ : Anc (tr.HonestBlocksAt H) D Q)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O D)
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hE : ∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root)
    (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocksAt H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocksAt H) := by
  have h0 := hrun.time_nonneg j
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun h0
  have hDQ' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hQU hDQ
  have hDU : D ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    by_cases h : D = Q
    · exact h ▸ hQU
    · exact (hDQ'.mem h).1
  have h := vote_anchor_cases_of_old (hrun.upTo h0) (hnc.upTo _) hf hp
    (k := k) (P := P) ⟨(RunTrace.upTo_ownBlockAt tr).mpr ⟨hkj, hP.1⟩, hP.2.1, hP.2.2⟩ hs0 hPQ hQU
    hDQ' hDU (fun O hO => RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hDU
      (hDold O (oldOrigin_of_upTo hrun hO))) hy
    (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩) hes
    (fun x hx j' hj' e' hv hs => by
      rw [RunTrace.upTo_projAC] at hv
      obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
      exact hE x j' e' hj' (hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩) hs) hstock
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl (h.mono hsub)
  · exact Or.inr ⟨h1.mono hsub, h2.mono hsub, hsub h3⟩

/-- A live lock block of the proposal's anchor sits below the proposer's own lock write of the
slot of a stored lock live at the proposal, written up to it (`lock_write_at`; unlocking and
`live_locks` only move locks back, keeping slot and expiry). -/
theorem proposal_live_lock_below_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {i : Nat} (hp : p ∈ H (tr.time i))
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocksAt H)
    {t : Time} {σ : Int} {V : SA.View sp.n} {A₁ : SA.SAState sp.n}
    (hA₁ : A₁.locks = SA.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ SA.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, l.LiveAt sp t ∧
      ∃ D, LockWithin tr H D l.slot (tr.time i) ∧ Anc (tr.HonestBlocksAt H) L D := by
  have hU := honestBlocksAt_coherent hrun hnc
  rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hlL⟩
  obtain rfl : L = Φ.viableAncestor B :=
    hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, -, -, he, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
    ((SA.locks_move_back sp) _ Φ _ t hΦ).2.2 σ V l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [projAC_state_at hrun hp] at hl₁
  obtain ⟨L₁, hL₁, hL₁r, D, hD, hL₁D⟩ :=
    lock_write_at hrun hnc (hrun.time_nonneg i) (fun _ hk => hrun.time_mono hk.le) hp l₁ hl₁
  obtain rfl : L₁ = B₁ :=
    hU.1 (mem_honestBlocksAt hrun hp hL₁) (hΦU hB₁) (hL₁r.trans hB₁r.symm)
  refine ⟨l₁, hl₁, ?_, D, hD,
    (Anc.mono hΦU ((SA.anc_viableAncestor Φ _).trans hB'B₁)).trans hL₁D⟩
  change sp.slot t ≤ l₁.expiry
  rw [← he]
  exact hlive

/-- A live lock block of the proposal's anchor sits below the proposer's own lock write of the
slot of a stored lock, written up to the proposal (`lock_write_at`; unlocking and `live_locks`
only move locks back). -/
theorem proposal_lock_below_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {i : Nat} (hp : p ∈ H (tr.time i))
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocksAt H)
    {t : Time} {σ : Int} {V : SA.View sp.n} {A₁ : SA.SAState sp.n}
    (hA₁ : A₁.locks = SA.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ SA.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, ∃ D,
      LockWithin tr H D l.slot (tr.time i) ∧ Anc (tr.HonestBlocksAt H) L D := fun L hL =>
  let ⟨l, hl, _, h⟩ := proposal_live_lock_below_at hrun hnc hp hΦ hΦU hA₁ L hL
  ⟨l, hl, h⟩

/-- **The proposal walk passes a supported held block**, under the service from `a ≤ t_{s−1}`
with its catch-up before `a + κ ≤ max (t_{s−1} + 3Δ) 0` and the counts from `σ₀ ≤ s − 1`: a block
`O` held by the proposer or below its `Σ.F`, at or below `fc_root` or in the full viable tree when
held, supported at slot `s − 1` (`proposal_best_toward_from`) and compatible with every lock write
of the slot of a stored lock live at the proposal, is below the proposal's head: the live locks of
the walk sit below such writes (`proposal_live_lock_below_at`), and the children towards `O` win
(`SA.anc_getHead`). -/
theorem proposal_walk_passes_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) (hs0 : 0 < s) (hσ₀ : σ₀ + 1 ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - 1)) (hκ : a + κ ≤ max (sp.ts ((s : Int) - 1) + 3 * sp.Δ) 0)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hOt : O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocksAt H) O ℓp.frame.F)
    (hviab : O ∈ ℓp.frame.tree →
      ℓp.frame.Anc O ℓp.frame.fcRoot ∨ O ∈ ℓp.frame.viableTree ℓp.frame.tree)
    (hO : (∀ x j e, HVoteAt tr H x j e → e.msg.slot + 1 = s → tr.time j ≤ b →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg O) ∨
      ∃ x k CV, x ∈ H (tr.time k) ∧ SA.OptimisticLockAt tr.projAC x k (s - 1) O CV)
    (hlock : ∀ l ∈ (tr.state p i).ac.locks, l.LiveAt sp (tr.time i) → ∀ D,
      LockWithin tr H D l.slot (tr.time i) → Compatible (tr.HonestBlocksAt H) D O)
    (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) O d.head := by
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦ hd
  obtain ⟨A₁, hA₁, -, hhd⟩ := acProposal_walk hd
  rcases hOt with hOt | hOF
  swap
  · exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hbest := proposal_best_toward_from hrun hnc hsync hB hp hc hcall hd hti hb hs0 hσ₀ ha hκ
    hOt hO hstock
  rw [← hsl_i] at hbest
  rw [hhd]
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A₁ (tr.time i) _ _ (fun _ h => h)
    (fun B hB X hXB => SA.mem_of_anc hXB hB) (hviab hOt).symm ?_ hbest)
  intro L hL
  obtain ⟨l, hl, hlive, D, hD, hLD⟩ := proposal_live_lock_below_at hrun hnc hp hΦ hΦU hA₁ L hL
  rcases hlock l hl hlive D hD with h | h
  · exact Or.inl (hLD.trans h)
  · exact SA.anc_total hU hLD h

/-- **The proposal walk passes every old origin**: the origin is held by the proposer (or below
its `Σ.F`, below the walk's start), so viable or at or below `fc_root` (`held_origin_viable_at`,
`2 f_d < n` at `d = t_s`); the proposer's live locks sit below origins, compatible with it (S1);
and the children towards it win (`proposal_best_toward_old_at`, `SA.anc_getHead`). -/
theorem proposal_walk_passes_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {s i : Nat}
    (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) (hstock : sp.committeeSize = sp.n) :
    ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O d.head := by
  intro O hO
  have hU := honestBlocksAt_coherent hrun hnc
  have hf := hB.two _ (hrun.time_nonneg i) hb
  have hib : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hb
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨m, hm, hOm⟩ := hO.within hrun (hti ▸ hb)
  have hfr := frame_of_projAC_at hrun hp hc
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  refine proposal_walk_passes_from hrun hnc (hsync.toFrom hrun) hB hp hc hcall hd hti hb
    (by omega) (by omega) (by
      rw [show ((s' + 1 : Nat) : Int) - 1 = (s' : Int) by push_cast; ring]
      exact ts_natCast_nonneg _) (by rw [zero_add]; exact le_max_right _ _)
    (proposal_holds_old_at hrun hnc hsync hB hinv hp hc hcall hd hti hb hstock O hO)
    (fun hOt => ?_) (hO.support_at hrun hinv (hti ▸ hb)) (fun l _ _ D hD => ?_) hstock
  · have hviab := held_origin_viable_at hrun hnc hp hf
      (fun C l D n hC hD => hinv.origins_compatible C l D n (hC.mono hb) (hD.mono hb))
      (fun C m' hC => hinv.origins_compatible O m C m' hOm (hC.within hib)) (hfr ▸ hOt)
    rwa [← hfr] at hviab
  · obtain ⟨O', hO', hDO'⟩ := hD.below_origin hrun hnc
    rcases hinv.origins_compatible O' l.slot O m (hO'.mono hb) hOm with h | h
    · exact Or.inl (hDO'.trans h)
    · exact SA.anc_total hU hDO' h


/-- **The pivot from a family of blocks** below the proposal's head. For a family `Old` of blocks
that the proposal walk passes (`hpass`), whose members and the walk's start are extended by every
slot-`s` vote by a node honest at it (`hext`), such that the walk from any block of the proposer's
tree above the start and every member of `Old` is through viable heads (`hsuf`), and a voter's
anchor is below such a block or on `P`'s chain above it (`hanc`): the deepest of the start and the
members of `Old` on the walk is a pivot. The proposer of slot `s` is honest at `t_s + Δ` (the
hold). For a voter honest at its vote, the earlier slot-`s` votes by nodes honest at them are
assumed to be `P` (the caller's strong induction on the cut). -/
theorem pivot_of (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} {p : Fin sp.n} {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hp : p ∈ H (sp.ts s + sp.Δ)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {Old : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hpass : ∀ O, Old O → Anc (tr.HonestBlocksAt H) O d.head)
    (hext : ∀ X, (X = d.start ∨ Old X) → ∀ y j e, HVoteAt tr H y j e → tr.time j ≤ b →
      e.msg.slot = s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hsuf : ∀ D ∈ ℓp.frame.tree, ℓp.frame.Anc d.start D →
      (∀ O, Old O → Anc (tr.HonestBlocksAt H) O D) →
      ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    (hanc : ∀ D ∈ ℓp.frame.tree, ℓp.frame.Anc D d.head →
      (∀ O, Old O → Anc (tr.HonestBlocksAt H) O D) →
      ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b →
        e.msg.slot = s →
        (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) →
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
          (Anc (tr.HonestBlocksAt H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
            Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
            P ∈ tr.HonestBlocksAt H)) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b →
        e.msg.slot = s →
        (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  -- `D`: the deepest of the start and the members of the family on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ Old X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, Old O → Anc (tr.HonestBlocksAt H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  refine ⟨D, hsD, hDQ, hsuf D hDt hsD hDold, fun y j ℓy e hy hcy hjb hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hcy.1
  have hhead := (castAt_spec_at hrun hnc hy hcy).2.2.2
  rw [hes] at hhead
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) :=
    SA.anc_ghost (fun B hB => (SA.voteDomain_subset_tree hB.1)) _ hat
  have hht := mem_of_anc_left hah hat
  -- the vote's head extends `D`
  have hDh : Anc (tr.HonestBlocksAt H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      hext D hDk y j e (hVoteAt_iff.2 ⟨hy, ℓy, hcy.1, hcy.2⟩) hjb hes
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  rcases hanc D hDt hDQ hDold y j ℓy e hy hcy hjb hes hE with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

/-- **The pivot** under growing faults. The proposer of slot `s` is honest at `t_s + Δ` (the
hold), so at its proposal and at every slot-`s` vote. For a voter honest at its vote, the earlier
slot-`s` votes by nodes honest at them are assumed to be `P` (the caller's strong induction on the
cut). -/
theorem pivot_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) (hib : tr.time i ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b →
        e.msg.slot = s →
        (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have h0 := hrun.time_nonneg i
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := hB.two _ h0 hib
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  have hkt : tr.time k = sp.ts s := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hs0 : 0 < s := by
    have hk0 := hrun.time_nonneg k
    have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [hkt]; linarith) hp
    obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, -⟩ := hP
    rcases blockCall_cases (hrun.upTo hk0).toLocalRun hpk
        ((Trace.upTo_callAt_of_le _ le_rfl).mpr hcB) with
      hg | ⟨j, x, rfl, -, hPr, d', pay', -, hB, -⟩
    · have h := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
      simp only [Nat.add_zero] at h
      exact absurd h hpos
    rw [← hPs, hB]
    exact hPr.1
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := proposal_walk_passes_old_at hrun hnc hsync hB hinv hpi hc hcall hd hti hib hstock
  -- the start and the old origins are extended by the honest slot-`s` votes (genesis, or S2)
  have hextO : ∀ O, OldOrigin tr H s O → ∀ y j e, HVoteAt tr H y j e → tr.time j ≤ b →
      e.msg.slot = s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg O := fun O hO y j e hv hjb hes =>
    let ⟨m, hm, hOm⟩ := hO.within hrun (hti ▸ hib)
    hinv.vote_extends O m hOm y j e hv hjb (by omega)
  refine pivot_of hrun hnc hp hc hd hti hPQ (Old := OldOrigin tr H s) hpass
    (fun X hX y j e hv hjb hes => ?_) (fun D hDt _ hDold =>
      proposal_suffix_viable_at hrun hnc hpi hf hc hcall hd hti hDt hDold hstock)
    (fun D hDt hDQ hDold y j ℓy e hy hcy hjb hes hE => ?_)
  · rcases hX with rfl | hO
    · obtain ⟨hy, ℓy, hcy, hey⟩ := hVoteAt_iff.1 hv
      obtain ⟨⟨Hd, hHdt, hHdr, -⟩, -⟩ := cast_head_fcRoot_at hrun hnc hy ⟨hcy, hey⟩
      have hHdU := (frameIn_at hrun hnc hy hcy).2 hHdt
      rcases proposal_anchor_old_at hrun hnc hpi hf hc hcall hd hti hstock with hg | ⟨O, hO, hsO⟩
      · exact ⟨Hd, hHdU, hHdr, honestAt_genesis_root_anc hrun hU (hΦpU hstart) hg hHdU⟩
      · obtain ⟨Hd', hHd', hHd'r, hOH⟩ := hextO O hO y j e hv hjb hes
        exact ⟨Hd', hHd', hHd'r, hsO.trans hOH⟩
    · exact hextO X hO y j e hv hjb hes
  · have hj1 : sp.ts s ≤ tr.time j := by
      have h := (castAt_spec_at hrun hnc hy hcy).2.1
      rw [hes] at h
      exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← h])
    have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
    exact vote_anchor_cases_at hrun hnc hy (hB.two _ (hrun.time_nonneg j) hjb)
      (hrun.antitone hjt hp) hP (hkt.trans_le hj1) hs0 hPQ
      (mem_upTo_of_frame hrun (hrun.antitone hjt hp) (hti ▸ hj1) hc (mem_of_anc_left hDQ hDt))
      (Anc.mono hΦpU hDQ) hDold hcy hes hE hstock

end Consensus.Goldilocks.Compose.Growing

end
