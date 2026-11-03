module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible

public section

/-! # Goldilocks Healing: the setting of H.1 (healthy driven AC traces with trivial frames)

H.1's premises over an AC trace of the SA (`StandaloneRun`: `ACRun`, `Driven`, `TrivialFrames`,
`Healthy(g)` and `Catch(2Δ)`; all but the trivial frames are `HealthyBase`, shared with H.2),
and what they give at once (healing-simple `t1-proof.md` §1:
"every honest validator is awake from `g` onward ... There is no later restart"):

* no honest node restarts after `ḡ` (`restart_le`): a restart is a wake, and an honest node is
  awake from `ḡ` on;
* hence an honest node is joined at every time `t` with `ḡ ≤ t_{slot(t)−1}`, both on the trace
  (`joinedAt`) and in its state before every call at such a time (`joined_state`; the state's
  `restart_time` is the time of the node's latest restart, `restartTime_state`);
* `Sync[a, b]` for every `a ≥ ḡ` (`syncAC`) and `f < h_t` there (`faultBound`), `f < n/2`.

It also holds the vocabulary of H.1's steps (`GoodOrigin`, `VotesExtendAfter`,
`ProposalsExtendAfter`, `LocksSettled`), shared by `Transfer.lean` and `Steps.lean`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **The healthy premises shared by H.1 and H.2** over an AC trace of the SA: the trace
contract with the honest-object facts, a driven trace, `Healthy(g)` and `Catch(2Δ)` (no
assumption on the frames). -/
structure HealthyBase (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) (g : Time) : Prop where
  run : ACRun proposer tr H U
  driven : Driven proposer tr H
  healthy : HealthyAC tr H U g
  catchUp : CatchAC tr H U g (2 * sp.Δ)

/-- Finite health with deadline-bounded service. Driven duties remain conditional
on actual awake witnesses, so they assert no activity beyond the horizon. -/
structure HealthyBaseUpTo (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) (g b : Time) : Prop where
  run : ACRun proposer tr H U
  driven : Driven proposer tr H
  sync : SyncACWindowBefore H U (gbar g) b tr
  catchUp : CatchACWindowBefore tr H U (gbar g) (2 * sp.Δ) b
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1

/-- **H.1's premises** over an AC trace of the SA: the healthy premises (`HealthyBase`) and
trivial frames. -/
structure StandaloneRun (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) (g : Time) : Prop extends HealthyBase tr H U proposer g where
  trivial : TrivialFrames tr H

theorem le_gbar (g : Time) : g ≤ gbar g := le_max_left g 0

theorem gbar_nonneg (g : Time) : 0 ≤ gbar g := le_max_right g 0

theorem Θ_nonneg (sp : SAParams) : 0 ≤ Θ sp := by
  have := sp.toParams.hΔ
  unfold Θ
  positivity

theorem ts_sub_one (sp : SAParams) (a : Int) : sp.ts (a - 1) = sp.ts a - 4 * sp.Δ := by
  simp only [SAParams.ts]; ring

/-! ### Restart time of a state -/

section RestartTime

private theorem rt_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').restartTime = A'.restartTime from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, SA.admitVote_restartTime]

/-- A call other than a restart keeps `restart_time`. -/
private theorem rt_step (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksSA sp FGP ro).Call) (hc : c ≠ .restart) :
    ((goldilocksSA sp FGP ro).step self A Φ t c).1.restartTime = A.restartTime := by
  cases c with
  | tick =>
    change (acOnTick sp self A Φ t).1.restartTime = _
    unfold acOnTick; dsimp only
    split_ifs <;> simp only [SA.updateConfirmation_restartTime, SA.tryVote_restartTime]
  | proposal =>
    change (acProposal sp A Φ t).1.restartTime = _
    unfold acProposal; split_ifs <;> rfl
  | toFG =>
    change (acToFG sp A Φ t).1.restartTime = _
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    change (tryVote sp self _ Φ t).1.restartTime = _
    rw [SA.tryVote_restartTime, rt_optimistic, SA.admitVote_restartTime]
  | block B =>
    change (tryVote sp self _ Φ t).1.restartTime = _
    rw [SA.tryVote_restartTime, rt_optimistic, rt_blockReceipt]
  | restart => exact absurd rfl hc

/-- **The restart time of a state**: the state of an honest node before cut `i` has
`restart_time = −∞`, or the time of a restart of the node at an earlier cut. -/
theorem restartTime_state (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    (tr.state y i).restartTime = ⊥ ∨
      ∃ k < i, tr.RestartAt y k ∧ (tr.state y i).restartTime = (tr.time k : WithBot Time) := by
  induction i with
  | zero =>
    left
    change (tr.init y).restartTime = ⊥
    rw [hr.init y hy]; rfl
  | succ i ih =>
    by_cases hn : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y i ℓ := ⟨hn.1, hℓ⟩
      have hst : tr.state y (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hn
      have he := hr.exec i ℓ hℓ (hn.1 ▸ hy)
      rw [hn.1] at he
      have hpost : tr.post i =
          ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
        rw [he]
      rw [hst, hpost]
      by_cases hrs : ℓ.call = .restart
      · right
        have hΦ := (frameIn_of_callAt hr hy hc).1
        refine ⟨i, Nat.lt_succ_self i, ⟨ℓ, hc, hrs⟩, ?_⟩
        rw [hrs]
        exact ((restart_state sp) FGP ro y (tr.state y i) ℓ.frame (tr.time i) hΦ
          (hr.time_nonneg i)).2.2.2.2.2.2.1
      · rw [rt_step y _ _ _ _ hrs]
        exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans (Nat.lt_succ_self i), h⟩
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst]
      exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans (Nat.lt_succ_self i), h⟩

end RestartTime

/-! ### Voted slot of a state -/

section VotedSlot

private theorem vs_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot := by
  unfold admitVote; split_ifs <;> rfl

private theorem vs_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem vs_update (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).votedSlot = A.votedSlot := by
  unfold updateConfirmation updateLatestConfirmed; dsimp only
  split
  · rfl
  · split_ifs <;> rfl

private theorem vs_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').votedSlot = A'.votedSlot from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, vs_admitVote]

/-- `try_vote` keeps `voted_slot` and emits nothing, or emits a vote of slot `slot(t)` and
leaves `voted_slot = slot(t)`. -/
private theorem vs_tryVote (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((tryVote sp x A Φ t).1.votedSlot = A.votedSlot ∧ (tryVote sp x A Φ t).2 = []) ∨
      ((tryVote sp x A Φ t).1.votedSlot = sp.slot t ∧
        ∃ e ∈ (tryVote sp x A Φ t).2, e.msg.slot = sp.slot t) := by
  unfold tryVote; dsimp only
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  all_goals exact Or.inr ⟨by rw [vs_optimistic, vs_admitVote], _, List.mem_singleton_self _, rfl⟩

/-- A call other than a restart keeps `voted_slot`, or emits a vote of slot `slot(t)` and
leaves `voted_slot = slot(t)`; a restart sets `voted_slot = −1`. -/
private theorem vs_step (self : Fin sp.n) (A : SAState sp.n) {Φ : Frm sp.n FGP} {t : Time}
    (hΦ : FrameOK Φ) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    let r := (goldilocksSA sp FGP ro).step self A Φ t c
    r.1.votedSlot = A.votedSlot ∨ r.1.votedSlot = -1 ∨
      (r.1.votedSlot = sp.slot t ∧ ∃ e ∈ r.2, e.msg.slot = sp.slot t) := by
  cases c with
  | tick =>
    change (acOnTick sp self A Φ t).1.votedSlot = _ ∨ (acOnTick sp self A Φ t).1.votedSlot = _ ∨
      ((acOnTick sp self A Φ t).1.votedSlot = _ ∧ ∃ e ∈ (acOnTick sp self A Φ t).2, _)
    unfold acOnTick; dsimp only
    split_ifs
    all_goals first
      | exact Or.inl rfl
      | exact Or.inl (vs_update _ _ _ _)
      | (rcases vs_tryVote self A Φ t with h | h
         · exact Or.inl ((vs_update _ _ _ _).trans h.1)
         · exact Or.inr (Or.inr ⟨(vs_update _ _ _ _).trans h.1, h.2⟩))
      | (rcases vs_tryVote self A Φ t with h | h
         · exact Or.inl h.1
         · exact Or.inr (Or.inr h))
  | proposal =>
    left
    change (acProposal sp A Φ t).1.votedSlot = _
    unfold acProposal; split_ifs <;> rfl
  | toFG =>
    left
    change (acToFG sp A Φ t).1.votedSlot = _
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    change (tryVote sp self _ Φ t).1.votedSlot = _ ∨ (tryVote sp self _ Φ t).1.votedSlot = _ ∨
      ((tryVote sp self _ Φ t).1.votedSlot = _ ∧ ∃ e ∈ (tryVote sp self _ Φ t).2, _)
    rcases vs_tryVote self (optimisticConfirmation sp (admitVote sp A t m) Φ t) Φ t with h | h
    · exact Or.inl (h.1.trans (by rw [vs_optimistic, vs_admitVote]))
    · exact Or.inr (Or.inr h)
  | block B =>
    change (tryVote sp self _ Φ t).1.votedSlot = _ ∨ (tryVote sp self _ Φ t).1.votedSlot = _ ∨
      ((tryVote sp self _ Φ t).1.votedSlot = _ ∧ ∃ e ∈ (tryVote sp self _ Φ t).2, _)
    rcases vs_tryVote self (optimisticConfirmation sp (blockReceipt sp A t B) Φ t) Φ t with h | h
    · exact Or.inl (h.1.trans (by rw [vs_optimistic, vs_blockReceipt]))
    · exact Or.inr (Or.inr h)
  | restart =>
    right; left
    exact ((restart_state sp) FGP ro self A Φ t hΦ ht).2.2.2.2.2.1

/-- **The voted slot of a state**: when the state of an honest node before cut `i` has
`voted_slot = σ ≥ 0`, the node cast a vote of slot `σ` at an earlier cut. -/
theorem vote_of_votedSlot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ σ : Nat, (tr.state y i).votedSlot = σ → ∃ j < i, ∃ e, VoteAt tr y j e ∧ e.msg.slot = σ := by
  induction i with
  | zero =>
    intro σ h
    change (tr.init y).votedSlot = σ at h
    rw [hr.init y hy] at h
    change (-1 : Int) = σ at h
    omega
  | succ i ih =>
    intro σ h
    by_cases hn : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y i ℓ := ⟨hn.1, hℓ⟩
      have hst : tr.state y (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hn
      have he := hr.exec i ℓ hℓ (hn.1 ▸ hy)
      rw [hn.1] at he
      rw [hst] at h
      have hv := vs_step (ro := ro) y (tr.state y i) (frameIn_of_callAt hr hy hc).1
        (hr.time_nonneg i) ℓ.call
      rw [he] at hv
      dsimp only at hv
      rcases hv with hv | hv | ⟨hv, e, hem, hes⟩
      · obtain ⟨j, hj, h'⟩ := ih σ (hv ▸ h)
        exact ⟨j, hj.trans (Nat.lt_succ_self i), h'⟩
      · omega
      · exact ⟨i, Nat.lt_succ_self i, e, ⟨ℓ, hc, hem⟩, by omega⟩
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst] at h
      obtain ⟨j, hj, h'⟩ := ih σ h
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h'⟩

/-- `try_vote` at `t_s + Δ` of a joined node that has not voted in slot `s = slot(t)` casts a
vote of slot `s`. -/
theorem tryVote_votes (x : Fin sp.n) {A : SAState sp.n} (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t) (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    ∃ e ∈ (tryVote sp x A Φ t).2, e.msg.slot = sp.slot t := by
  rcases vs_tryVote x A Φ t with h | h
  · exfalso
    unfold tryVote at h; dsimp only at h
    split_ifs at h with h1 h2
    · rcases h1 with h1 | h1 | h1
      · exact h1 hj
      · exact hv h1
      · linarith
    · linarith [h2.1]
    all_goals simp at h
  · exact h.2

end VotedSlot

namespace HealthyBase

variable (hS : HealthyBase tr H U proposer g)
include hS

/-- An honest node is awake from `ḡ` on. -/
theorem awake {y : Fin sp.n} (hy : y ∈ H) {t : Time} (ht : gbar g ≤ t) : tr.awake y t :=
  hS.healthy.2.2.1 y hy t ht

/-- `f < n/2` (from `3f ≤ n − 1`). -/
theorem two_faulty_lt : 2 * Hᶜ.ncard < sp.n := by
  have := hS.healthy.2.2.2
  have := sp.toParams.hn
  change 1 ≤ sp.n at this
  omega

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

/-- An honest node is joined at every `t` with `ḡ ≤ t_{slot(t)−1}`. -/
theorem joinedAt {y : Fin sp.n} (hy : y ∈ H) {t : Time}
    (ht : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) : JoinedAt tr y t :=
  fun _ hk _ => (hS.restart_le hy hk).trans ht

/-- The state of an honest node before a cut at a time `t` with `ḡ ≤ t_{slot(t)−1}` is
joined at `t`. -/
theorem joined_state {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (ht : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)) :
    joined sp (tr.state y i) (tr.time i) := by
  unfold joined
  rcases restartTime_state hS.run.localRun hy i with h | ⟨k, -, hrk, h⟩
  · rw [h]; exact bot_le
  · rw [h]; exact WithBot.coe_le_coe.mpr ((hS.restart_le hy hrk).trans ht)

/-- `Sync[a, b]` for every `a ≥ ḡ`. -/
theorem syncAC {a : Time} (ha : gbar g ≤ a) (b : Time) :
    SyncAC (goldilocksSA sp FGP ro) H U a b tr := by
  have hg : ∀ τ, a ≤ τ → g ≤ τ := fun τ h => (le_gbar g).trans (ha.trans h)
  refine ⟨fun x hx i m hm hai _ y hy j ℓ hc hdl => ?_,
    fun x hx i B hB hai _ y hy j ℓ hc hdl hF =>
      hS.healthy.2.1 x hx i B hB (hg _ hai) y hy j ℓ hc hdl hF⟩
  have hmax : max (tr.time i) g = tr.time i := max_eq_left (hg _ hai)
  have := hS.healthy.1 x hx i m hm y hy j ℓ hc (by rwa [hmax])
  simpa only [hmax] using this

/-- `f < h_t` at every `t` with `ḡ ≤ t_{slot(t)−1}`: every honest node is awake and joined
there. -/
theorem faultBound {t : Time} (ht0 : 0 ≤ t) (ht : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) :
    FaultBound tr H t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : {y | y ∈ H ∧ tr.awake y t ∧ JoinedAt tr y t} = H :=
    Set.ext fun y => ⟨fun h => h.1, fun hy => ⟨hy, hS.awake hy (ht.trans hts), hS.joinedAt hy ht⟩⟩
  unfold FaultBound honestAwakeJoined
  rw [hsub]
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := hS.two_faulty_lt
  omega

end HealthyBase

/-! ### Vocabulary of the steps (T1 §§1–6) -/

/-- **A good origin** (T1 §1) of label `j` on `B`: an honest fast lock write of slot `j ≥ r`, or
an honest slow lock write of slot `j` whose window `[j − k + 1, j]` is `≥ r`. -/
def GoodOrigin (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (g : Time) (B : Blk sp.n FGP)
    (j : Nat) : Prop :=
  (∃ x ∈ H, ∃ i CV, FastLockAt tr x i j B CV ∧ gbar g + 4 * sp.Δ ≤ sp.ts j) ∨
  (∃ x ∈ H, ∃ i, SlowLockAt tr x i j B ∧ gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))

/-- Every honest vote of a slot after `j` extends `B`. -/
def VotesExtendAfter (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (j : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x ∈ H, ∀ i e, VoteAt tr x i e → j < e.msg.slot → VoteExtends U e.msg B

/-- The head of every honest `ac_proposal` at the start of a slot after `j` extends `B`. -/
def ProposalsExtendAfter (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (j : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) (m : Nat) d pay, tr.CallAt x i ℓ →
    ℓ.call = .proposal → tr.time i = sp.ts m → j < m →
    (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) → Anc U B d.head

/-- **Settled locks from `T`** (T1 §§3–5): at every cut of an honest node at a time `≥ T`,
every stored lock live there (`slot(t) ≤ j + k`) is on a block that every honest vote and
proposal head of a slot after its label `j` extends. -/
def LocksSettled (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (T : Time) : Prop :=
  ∀ y ∈ H, ∀ i, T ≤ tr.time i → ∀ l ∈ (tr.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k →
    ∀ L ∈ U, L.root = l.block →
      VotesExtendAfter tr H U l.slot L ∧ ProposalsExtendAfter tr H U l.slot L

theorem goodOrigin_iff {B : Blk sp.n FGP} {j : Nat} : GoodOrigin tr H g B j ↔
    ((∃ x ∈ H, ∃ i CV, FastLockAt tr x i j B CV ∧ gbar g + 4 * sp.Δ ≤ sp.ts j) ∨
      (∃ x ∈ H, ∃ i, SlowLockAt tr x i j B ∧
        gbar g + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))) := Iff.rfl

theorem votesExtendAfter_iff {j : Nat} {B : Blk sp.n FGP} : VotesExtendAfter tr H U j B ↔
    ∀ x ∈ H, ∀ i e, VoteAt tr x i e → j < e.msg.slot → VoteExtends U e.msg B := Iff.rfl

theorem proposalsExtendAfter_iff {j : Nat} {B : Blk sp.n FGP} :
    ProposalsExtendAfter tr H U j B ↔
      ∀ x ∈ H, ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)) (m : Nat) d pay, tr.CallAt x i ℓ →
        ℓ.call = .proposal → tr.time i = sp.ts m → j < m →
        (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay) →
        Anc U B d.head := Iff.rfl

theorem locksSettled_iff {T : Time} : LocksSettled tr H U T ↔
    ∀ y ∈ H, ∀ i, T ≤ tr.time i → ∀ l ∈ (tr.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block →
        VotesExtendAfter tr H U l.slot L ∧ ProposalsExtendAfter tr H U l.slot L := Iff.rfl

theorem LocksSettled.mono {T T' : Time} (h : LocksSettled tr H U T) (hT : T ≤ T') :
    LocksSettled tr H U T' :=
  fun y hy i hi => h y hy i (hT.trans hi)

end Consensus.Goldilocks.SA

end
