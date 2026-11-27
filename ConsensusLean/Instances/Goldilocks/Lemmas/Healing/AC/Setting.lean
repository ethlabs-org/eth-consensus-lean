module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.RelSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.RelSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked

public section

/-! # Goldilocks Healing: the healthy setting (healthy driven AC traces)

The healthy premises over an AC trace of the AC (`HealthyBase`: `ACRun`, `Driven`, `Healthy(g)` and
`Catch(2Δ)`, with no assumption on the frames), and what they give at once (every honest
validator is awake from `g` on, so there is no later restart):

* no honest node restarts after `ḡ` (`restart_le`): a restart is a wake, and an honest node is
  awake from `ḡ` on;
* hence an honest node is joined at every time `t` with `ḡ ≤ t_{slot(t)−1}`, in its state
  before every call at such a time (`joined_state`; the state's
  `restart_time` is the time of the node's latest restart, `restartTime_stateU`);
* `Sync[a, b]` for every `a ≥ ḡ` (`syncAC`) and `f < h_t` there (`faultBound`), `f < n/2`.

The settings at a write mode and an unlock oracle (`HealthyACCore`, `HealthyBaseU`) are defined in
`Milestones/Statements/Healing/ACU`; this module proves their facts. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **The healthy premises** over an AC trace of the AC: the trace
contract with the honest-object facts, a driven trace, `Healthy(g)` and `Catch(2Δ)` (no
assumption on the frames). -/
structure HealthyBase (tr : GTrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) (g : Time) : Prop where
  run : ACRun proposer tr H U
  driven : Driven proposer tr H
  healthy : HealthyAC tr H U g
  catchUp : CatchAC tr H U g (2 * sp.Δ)
  /-- The committee is population-sized (`committeeSize = n`). -/
  stock : sp.committeeSize = sp.n

/-- Finite health with deadline-bounded service, for the slot committees `K`. Driven duties
remain conditional on actual awake witnesses, so they assert no activity beyond the horizon. The
run starts at `K`'s committee start (a node may vote exactly in its committees' slots), its pools
and merged views hold committee votes (P, T), and fewer than half of each slot committee from `ḡ`
through `b` is faulty. The stock committee is `CommitteeDict.full`. -/
structure HealthyBaseUpTo (K : CommitteeDict sp.n) (tr : GTrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (proposer : Nat → Fin sp.n) (g b : Time) : Prop where
  run : ACRun proposer tr H U (committeeStart sp.genesisRoot K)
  driven : Driven proposer tr H
  sync : SyncACWindowBefore H U (gbar g) b tr
  catchUp : CatchACWindowBefore tr H U (gbar g) (2 * sp.Δ) b
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1
  hsize : ∀ s, (K.committee s).ncard = sp.committeeSize
  hP : CommitteeP K tr H
  hT : CommitteeT K tr H
  cs2 : ∀ s : Nat, gbar g ≤ sp.ts s → sp.ts s ≤ b →
    2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize

/-- `Healthy(g)` gives its service and awake part. -/
theorem HealthyAC.core (h : HealthyAC tr H U g) : HealthyACCore tr H U g :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- `f < n/2`, from the fault clause `3f ≤ n − 1` of `Healthy(g)`. -/
theorem HealthyAC.two_faulty_lt (h : HealthyAC tr H U g) : 2 * Hᶜ.ncard < sp.n := by
  have := h.2.2.2
  have := sp.toParams.hn
  change 1 ≤ sp.n at this
  omega

theorem HealthyBase.toU (h : HealthyBase tr H U proposer g) :
    HealthyBaseU (WriteMode.parent sp) (parentOracle sp tr) tr H U proposer g :=
  ⟨h.run.toU, h.driven.toU, h.healthy.core, h.healthy.two_faulty_lt, h.catchUp, h.stock⟩

theorem le_gbar (g : Time) : g ≤ gbar g := le_max_left g 0

theorem gbar_nonneg (g : Time) : 0 ≤ gbar g := le_max_right g 0

theorem ts_sub_one (sp : ACParams) (a : Int) : sp.ts (a - 1) = sp.ts a - 4 * sp.Δ := by
  simp only [ACParams.ts]; ring

/-! ### Restart time of a state -/

section RestartTime

private theorem rt_blockReceipt (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime :=
  rfl

/-- A call other than a restart keeps `restart_time`. -/
private theorem rt_step
    {L : Set Lock} (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP ro).Call) (hc : c ≠ .restart) :
    (stepWithM sp ro wm self L A Φ t c).1.restartTime = A.restartTime := by
  cases c with
  | tick =>
    change (acOnTickWithM sp wm self L A Φ t).1.restartTime = _
    unfold acOnTickWithM; dsimp only
    split_ifs <;> simp only [updateConfirmationM_field ACState.restartTime (fun _ _ => rfl),
      AC.updateConfirmation_restartTime, AC.tryVote_restartTimeWith]
  | proposal =>
    change (acProposalWith sp L A Φ t).1.restartTime = _
    unfold acProposalWith; split_ifs <;> rfl
  | toFG =>
    change (acToFG sp A Φ t).1.restartTime = _
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    change (tryVoteWithM sp wm self L _ Φ t).1.restartTime = _
    rw [AC.tryVote_restartTimeWith, rt_optimistic,
      AC.admitVote_restartTime]
  | block B =>
    change (tryVoteWithM sp wm self L _ Φ t).1.restartTime = _
    rw [AC.tryVote_restartTimeWith, rt_optimistic, rt_blockReceipt]
  | restart => exact absurd rfl hc

/-- **The restart time of a state**: the state of an honest node before cut `i` has `restart_time =
−∞`, or the time of a restart of the node at an earlier cut. With the unlock given. -/
theorem restartTime_stateU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    (tr.state y i).restartTime = ⊥ ∨
      ∃ k < i, tr.RestartAt y k ∧ (tr.state y i).restartTime = (tr.time k : WithBot Time) := by
  induction i with
  | zero =>
    left
    change (tr.init y).restartTime = ⊥
    obtain ⟨m, hm⟩ := voteStart_iff.1 (hini y)
    rw [hr.init y hy, hm]; rfl
  | succ i ih =>
    by_cases hn : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y i ℓ := ⟨hn.1, hℓ⟩
      have hst : tr.state y (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hn
      have he := hr.exec i ℓ hℓ (hn.1 ▸ hy)
      rw [hn.1] at he
      have hpost : tr.post i =
          (stepWithM sp ro wm y (u i) (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
        rw [he]
      rw [hst, hpost]
      by_cases hrs : ℓ.call = .restart
      · right
        have hΦ := (frameIn_of_callAtU hr hy hc).1
        refine ⟨i, Nat.lt_succ_self i, ⟨ℓ, hc, hrs⟩, ?_⟩
        rw [hrs]
        exact ((restart_state sp) FGP ro y (tr.state y i) ℓ.frame (tr.time i) hΦ
          (hr.time_nonneg i)).2.2.2.2.2.1
      · rw [rt_step (L := u i) y _ _ _ _ hrs]
        exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans (Nat.lt_succ_self i), h⟩
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst]
      exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans (Nat.lt_succ_self i), h⟩

/-- **Joined from the restart bound**: the state of an honest node before cut `i` is joined at the
time of `i` when each of its restarts before `i` is at or before `t_{slot(t)−1}`, `t` that time. -/
theorem joined_state_of_restarts
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hrs : ∀ k < i, tr.RestartAt y k → tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)) :
    joined sp (tr.state y i) (tr.time i) := by
  unfold joined
  rcases restartTime_stateU hr hini hy i with h | ⟨k, hki, hrk, h⟩
  · rw [h]; exact bot_le
  · rw [h]; exact WithBot.coe_le_coe.mpr (hrs k hki hrk)

end RestartTime

/-! ### Voted slot of a state -/

section VotedSlot

private theorem vs_admitVote (A : ACState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot := by
  unfold admitVote; split_ifs <;> rfl

private theorem vs_optimistic (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem vs_blockReceipt (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot :=
  rfl

/-- `try_vote` keeps `voted_slot` and emits nothing, or emits a vote of slot `slot(t)` and
leaves `voted_slot = slot(t)`. -/
private theorem vs_tryVoteWith
    {L : Set Lock} (x : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (hp : A.mayVote (sp.slot t) = true) :
    ((tryVoteWithM sp wm x L A Φ t).1.votedSlot = A.votedSlot ∧
        (tryVoteWithM sp wm x L A Φ t).2 = []) ∨
      ((tryVoteWithM sp wm x L A Φ t).1.votedSlot = sp.slot t ∧
        ∃ e ∈ (tryVoteWithM sp wm x L A Φ t).2, e.msg.slot = sp.slot t) := by
  unfold tryVoteWithM
  simp only [hp, ↓reduceIte]
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  all_goals exact Or.inr ⟨by rw [vs_optimistic, vs_admitVote], _,
      List.mem_singleton_self _, rfl⟩

private theorem vs_tryVote (x : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (hp : A.mayVote (sp.slot t) = true) :
    ((tryVote sp x A Φ t).1.votedSlot = A.votedSlot ∧ (tryVote sp x A Φ t).2 = []) ∨
      ((tryVote sp x A Φ t).1.votedSlot = sp.slot t ∧
        ∃ e ∈ (tryVote sp x A Φ t).2, e.msg.slot = sp.slot t) := by
  rw [tryVote_eq_tryVoteWith, ← tryVoteWithM_parent]
  exact vs_tryVoteWith x A Φ t hp

/-- `tryVote_votes` with the unlock given: the vote branch of `tryVoteWithM_branch` emits when
the node may vote in the slot. -/
theorem tryVote_votesWith
    {L : Set Lock} (x : Fin sp.n) {A : ACState sp.n} (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t) (ht : t = sp.ts (sp.slot t) + sp.Δ)
    (hp : A.mayVote (sp.slot t) = true) :
    ∃ e ∈ (tryVoteWithM sp wm x L A Φ t).2, e.msg.slot = sp.slot t := by
  obtain ⟨e, he, -, -, hsl⟩ := (tryVoteWithM_branch (wm := wm) (L := L) x Φ hj hv ht.le
    fun h => absurd ht (ne_of_lt h.1)).1 hp
  exact ⟨e, by rw [he]; exact List.mem_singleton_self _, hsl⟩

/-- `try_vote` at `t_s + Δ` of a joined node that has not voted in slot `s = slot(t)` casts a
vote of slot `s`. -/
theorem tryVote_votes (x : Fin sp.n) {A : ACState sp.n} (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t) (ht : t = sp.ts (sp.slot t) + sp.Δ)
    (hp : A.mayVote (sp.slot t) = true) :
    ∃ e ∈ (tryVote sp x A Φ t).2, e.msg.slot = sp.slot t :=
  tryVote_votesWith (wm := WriteMode.parent sp) (x := x) (A := A) (Φ := Φ) (t := t) (hj := hj)
      (hv := hv) (ht := ht) (hp := hp)

end VotedSlot

namespace HealthyBaseU

variable {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g)
include hS

/-- An honest node is awake from `ḡ` on. -/
theorem awake {y : Fin sp.n} (hy : y ∈ H) {t : Time} (ht : gbar g ≤ t) : tr.awake y t :=
  hS.healthy.awake y hy t ht

/-- `f < n/2`. -/
theorem two_faulty_lt : 2 * Hᶜ.ncard < sp.n :=
  hS.faults

/-- **No restart after `ḡ`**: a restart is a wake, and an honest node is awake from `ḡ` on. -/
theorem restart_le {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) :
    tr.time k ≤ gbar g := by
  by_contra hlt
  rw [not_le] at hlt
  have hr := hS.run.localRun
  obtain ⟨ℓ, hc, hcall⟩ := hk
  obtain ⟨u, hu0, -, hna, hbefore⟩ := hr.sleep_of_restart y hy k ℓ hc hcall
  have hug : u < gbar g := by
    by_contra h
    exact hna (hS.awake hy (not_lt.mp h))
  obtain ⟨k', ⟨ℓ', hc', -⟩, huk', hk'g⟩ :=
    hr.restart_at_wake y hy u (gbar g) hu0 hug hna (hS.awake hy le_rfl)
  have hk'k : k' < k := by
    by_contra h
    have := hr.time_mono (not_lt.mp h)
    linarith
  have := hbefore k' hk'k ℓ' hc'
  linarith

/-- The state of an honest node before a cut at a time `t` with `ḡ ≤ t_{slot(t)−1}` is
joined at `t`. -/
theorem joined_state {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (ht : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)) :
    joined sp (tr.state y i) (tr.time i) :=
  joined_state_of_restarts hS.run.localRun hS.run.vstart hy i fun _ _ hrk =>
    (hS.restart_le hy hrk).trans ht

/-- `Sync[a, b]` for every `a ≥ ḡ`. -/
theorem syncAC {a : Time} (ha : gbar g ≤ a) (b : Time) :
    SyncAC (goldilocksAC sp FGP ro) H U a b tr := by
  have hg : ∀ τ, a ≤ τ → g ≤ τ := fun τ h => (le_gbar g).trans (ha.trans h)
  refine ⟨fun x hx i m hm hai _ y hy j ℓ hc hdl => ?_,
    fun x hx i B hB hai _ y hy j ℓ hc hdl hF =>
      hS.healthy.relay x hx i B hB (hg _ hai) y hy j ℓ hc hdl hF⟩
  have hmax : max (tr.time i) g = tr.time i := max_eq_left (hg _ hai)
  have := hS.healthy.message x hx i m hm y hy j ℓ hc (by rwa [hmax])
  simpa only [hmax] using this

end HealthyBaseU

namespace HealthyBase

variable (hS : HealthyBase tr H U proposer g)
include hS

/-- `f < n/2` (from `3f ≤ n − 1`). -/
theorem two_faulty_lt : 2 * Hᶜ.ncard < sp.n :=
  hS.toU.two_faulty_lt

/-- **No restart after `ḡ`**: a restart is a wake, and an honest node is awake from `ḡ` on. -/
theorem restart_le {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) :
    tr.time k ≤ gbar g :=
  hS.toU.restart_le hy hk

/-- The state of an honest node before a cut at a time `t` with `ḡ ≤ t_{slot(t)−1}` is
joined at `t`. -/
theorem joined_state {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (ht : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)) :
    joined sp (tr.state y i) (tr.time i) :=
  hS.toU.joined_state hy i ht

/-- `Sync[a, b]` for every `a ≥ ḡ`. -/
theorem syncAC {a : Time} (ha : gbar g ≤ a) (b : Time) :
    SyncAC (goldilocksAC sp FGP ro) H U a b tr :=
  hS.toU.syncAC ha b

end HealthyBase

/-! ### Vocabulary of the steps -/

end Consensus.Goldilocks.AC

end
