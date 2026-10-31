module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same

public section

/-! # Goldilocks under `Sleepy`: comparing origins (extending `P_s` to `P_{s+1}`)

workbench#11 §2.1, §2.2 and §4 "Extend the origin frontier".

* **An honest supporter** (`honest_supporter`, §2.1): an origin of label `s` has an honest slot-`s`
  vote whose head extends it. For a result: the honest validators awake and joined at `t_s + Δ`
  (more than `f`, by `Sleepy`) vote in slot `s` and reach the joined writer before `t_s + 2Δ`, so
  they are among its participants; if every counted supporter were faulty, the participants would
  hold those seats and more than `f` disjoint honest ones, against the strict majority. For an
  optimistic selection: `3n/4 > f` voters.
* **Same-label origins compare** (`same_label_compatible`, §2.2): two results by the disjointness
  of conflicting supporter sets and the relay of counted votes to both writers (RR); a result and
  an optimistic selection by the relay of the `≥ 3n/4` optimistic seats (RO); two selections share
  `n/2 > f` seats (OO).
* `origins_below_succ`: an origin of label `s` and one of label `j < s` are both below the head of
  the honest supporter's vote, which extends the older one by `V_s`. -/

/-! ## Over SA traces: `voted_slot`, and the relay of one slot's votes to a writer -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

private theorem admitVote_keeps (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot ∧
      (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem updateLatestConfirmed_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).votedSlot = A.votedSlot ∧
      (updateLatestConfirmed sp A Φ C).restartTime = A.restartTime := by
  unfold updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot ∧
      (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_keeps _ _ _

private theorem updateConfirmation_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs
    · exact ⟨rfl, rfl⟩
    · exact updateLatestConfirmed_keeps _ _ _

private theorem blockReceipt_keeps (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot ∧
      (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').votedSlot = A'.votedSlot ∧
      (l.foldl (fun A v => admitVote sp A t v) A').restartTime = A'.restartTime from
    h { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }
  induction l with
  | nil => exact fun _ => ⟨rfl, rfl⟩
  | cons v l ih =>
    intro A'
    simp only [List.foldl_cons]
    exact ⟨(ih _).1.trans (admitVote_keeps _ _ _).1, (ih _).2.trans (admitVote_keeps _ _ _).2⟩

private theorem acProposal_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime := by
  unfold acProposal
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem acToFG_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG
  dsimp only
  split_ifs
  · split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A call from `A` to `A'` with the emissions `es` keeps `restart_time`, and keeps `voted_slot`
or emits a vote of the slot that `A'` records. -/
private def VotedStep (A A' : SAState sp.n) (es : List (Em sp FGP)) : Prop :=
  A'.restartTime = A.restartTime ∧
    (A'.votedSlot = A.votedSlot ∨ ∃ e ∈ es, (e.msg.slot : Int) = A'.votedSlot)

private theorem VotedStep.pre {A B A' : SAState sp.n} {es : List (Em sp FGP)}
    (h : VotedStep B A' es) (hv : B.votedSlot = A.votedSlot)
    (hr : B.restartTime = A.restartTime) : VotedStep A A' es :=
  ⟨h.1.trans hr, h.2.imp_left (·.trans hv)⟩

private theorem tryVote_votedStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : VotedStep A (tryVote sp self A Φ t).1 (tryVote sp self A Φ t).2 := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩
  all_goals
    refine ⟨(optimistic_keeps _ _ _).2.trans (admitVote_keeps _ _ _).2,
      Or.inr ⟨_, List.mem_singleton_self _, ?_⟩⟩
    rw [(optimistic_keeps _ _ _).1, (admitVote_keeps _ _ _).1]

private theorem acOnTick_votedStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : VotedStep A (acOnTick sp self A Φ t).1 (acOnTick sp self A Φ t).2 := by
  unfold acOnTick
  dsimp only
  have hr : VotedStep A
      (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])).1
      (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])).2 := by
    split_ifs
    · exact tryVote_votedStep _ _ _ _
    · exact ⟨rfl, Or.inl rfl⟩
  generalize (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])) = r at hr ⊢
  split_ifs <;> first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact hr
    | exact ⟨(updateConfirmation_keeps _ _ _ _).2.trans hr.1,
        by rw [(updateConfirmation_keeps _ _ _ _).1]; exact hr.2⟩

/-- One call: a restart, which resets `voted_slot` to `−1`, or a `VotedStep`. -/
private theorem step_votedStep (self : Fin sp.n) (A : SAState sp.n) {Φ : Frm sp.n FGP}
    (t : Time) (hΦ : FrameOK Φ) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    ((goldilocksSA sp FGP ro).step self A Φ t c).1.votedSlot = -1 ∨
      VotedStep A ((goldilocksSA sp FGP ro).step self A Φ t c).1
        ((goldilocksSA sp FGP ro).step self A Φ t c).2 := by
  cases c with
  | tick => exact Or.inr (acOnTick_votedStep _ _ _ _)
  | proposal => exact Or.inr ⟨(acProposal_keeps _ _ _).2, Or.inl (acProposal_keeps _ _ _).1⟩
  | toFG => exact Or.inr ⟨(acToFG_keeps _ _ _).2, Or.inl (acToFG_keeps _ _ _).1⟩
  | message m =>
    exact Or.inr ((tryVote_votedStep _ _ _ _).pre
      ((optimistic_keeps _ _ _).1.trans (admitVote_keeps _ _ _).1)
      ((optimistic_keeps _ _ _).2.trans (admitVote_keeps _ _ _).2))
  | block B =>
    exact Or.inr ((tryVote_votedStep _ _ _ _).pre
      ((optimistic_keeps _ _ _).1.trans (blockReceipt_keeps _ _ _).1)
      ((optimistic_keeps _ _ _).2.trans (blockReceipt_keeps _ _ _).2))
  | restart => exact Or.inl ((restart_state sp) FGP ro self A Φ t hΦ ht).2.2.2.2.2.1

/-- Before cut `i`, an honest node's `voted_slot` is `−1` or the slot of a vote it cast at an
earlier cut. -/
private theorem votedSlot_cast (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : (tr.state y i).votedSlot = -1 ∨
      ∃ k < i, ∃ e, VoteAt tr y k e ∧ (e.msg.slot : Int) = (tr.state y i).votedSlot := by
  induction i with
  | zero =>
    left
    change (tr.init y).votedSlot = -1
    rw [hr.init y hy]
    rfl
  | succ i ih =>
    have ih' : (tr.state y i).votedSlot = -1 ∨
        ∃ k < i + 1, ∃ e, VoteAt tr y k e ∧ (e.msg.slot : Int) = (tr.state y i).votedSlot := by
      rcases ih with h | ⟨k, hk, e, hv, hes⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, hk.trans (Nat.lt_succ_self i), e, hv, hes⟩
    by_cases hn : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hn
      rw [tr.state_succ_of_call hc]
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      rcases step_votedStep (ro := ro) y (tr.state y i) (tr.time i) (frameIn_of_callAt hr hy hc).1
        (hr.time_nonneg i) ℓ.call with h | ⟨-, h | ⟨e, hem, hes⟩⟩ <;>
        rw [he] at * <;> dsimp only at *
      · exact Or.inl h
      · rw [h]; exact ih'
      · exact Or.inr ⟨i, Nat.lt_succ_self i, e, ⟨ℓ, hc, hem⟩, hes⟩
    · rw [tr.state_succ_of_not fun ℓ hc => hn ⟨ℓ, hc⟩]
      exact ih'

/-- At the tick at `t_s + Δ` of a joined node, `try_vote` runs: the node votes in slot `s`, or
`voted_slot = s` already. -/
private theorem acOnTick_votes (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    A.votedSlot = sp.slot t ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg.slot = sp.slot t := by
  unfold acOnTick
  simp only [hj, not_true_eq_false, ↓reduceIte, ← ht]
  unfold tryVote
  dsimp only
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact Or.inl h
    · linarith
  · linarith [h₂.1]
  all_goals exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩

private theorem ts_succ_add (s : Nat) (a : Time) :
    sp.ts (s + 1 : Nat) + a = sp.ts s + 4 * sp.Δ + a := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot of a time in `[t_s, t_s + 4Δ)` is `s`. -/
private theorem slot_of_lt {s : Nat} {t : Time} (h₁ : sp.ts s ≤ t) (h₂ : t < sp.ts s + 4 * sp.Δ) :
    sp.slot t = s :=
  slot_of_mem sp s h₁ (by rw [← add_zero (sp.ts (s + 1 : Nat)), ts_succ_add]; linarith)

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
private theorem update_restarts (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {Y : Fin sp.n}
    (hY : Y ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr Y c s ℓ) :
    ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
  rw [hc.1, hcall] at he
  have hpost : joined sp (tr.post c) (tr.time c) := by
    have : tr.post c = (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1 :=
      (congrArg Prod.fst he).symm
    unfold joined at hj ⊢
    rw [this, (acOnTick_votedStep Y _ _ _).1]
    exact hj
  have hsl : sp.slot (tr.time c) = s + 1 :=
    slot_of_lt (s := s + 1) (by rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), ts_succ_add]; linarith)
      (by rw [ht, ts_succ_add]; linarith)
  intro k hk hrk
  have := ((joined_awake sp) FGP ro H U tr hr Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

/-- `u` has a slot-`s` vote whose head extends `D` inside `U`, which `X` sent or admitted at a
time in `[t_s, t_s + 2Δ)`. -/
private def Relayed (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat)
    (D : Blk sp.n FGP) (u : Fin sp.n) : Prop :=
  ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ

/-- A vote that an honest node holds before cut `c`, of slot `s`, admitted before a time of slot
`s`, was admitted by the node at a time in `[t_s, T)`. -/
private theorem admitted_in_window (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {X : Fin sp.n} (hX : X ∈ H) {c s : Nat} {v : Vote sp.n} (hvs : v.slot = s)
    (hv : v ∈ (tr.state X c).pool s) {T : Time} (hT : T ≤ sp.ts s + 2 * sp.Δ)
    (hlt : ∀ k < c, (tr.state X c).voteStamp v = ETime.of (tr.time k) → tr.time k < T) :
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < T := by
  have hΔ := sp.toParams.hΔ
  rcases pool_origin hr hX c v (hvs ▸ hv) with ⟨k, hk, hsend, hst, hsl⟩ |
    ⟨k, hk, ℓ, hck, -, hst, B, hB, hvB⟩
  · refine ⟨k, hsend, ?_, hlt k hk hst⟩
    exact ((ts_le_iff_le_slot sp (hr.time_nonneg k)) _).2 (by rw [← hvs]; exact_mod_cast hsl)
  · exfalso
    have h1 := (frame_validPayload sp hr hX hck B hB).1 v hvB
    have h2 := frame_slot_le sp hr hX hck B hB
    have h3 := hlt k hk hst
    have h4 : sp.slot (tr.time k) ≤ s := by
      by_contra h
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg k)) (s + 1 : Nat)).2 (by push_cast; omega)
      rw [← add_zero (sp.ts (s + 1 : Nat)), ts_succ_add] at this
      linarith
    omega

/-- **A result's side.** At an honest update of slot `s` with result `D`: the node's restarts were
at or before `t_s`; its counted validators `S` are more than half of its voters; each has a vote
in its pool, extending `D`, and does not equivocate there, and that vote was admitted in
`[t_s, t_s + 2Δ)`. -/
private theorem result_side (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Relayed tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hr := hrun.localRun
  have hmaj := result_majority hR
  obtain ⟨ℓ, hu, -, rfl⟩ := hR
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hY hu.1
  refine ⟨ℓ, _, hu.1, hu.2.2.1, update_restarts hr hY hu, hmaj, ?_, ?_⟩
  · rintro u ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvs := state_pool_slot sp hr hY c s v hvp
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, admitted_in_window hr hY hvs hvp le_rfl
      fun k _ hst => ?_⟩
    have hst' : (tr.state Y c).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) := by
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · split_ifs at hres
        · exact absurd hres (by simp [ETime.of])
        · exact lt_of_le_of_lt (le_max_left _ _) hres
    rw [hst] at hst'
    exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst')
  · rintro u ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- **An optimistic selection's seats.** At an honest optimistic confirmation of slot `s` on `D`,
three quarters of the committee are optimistic voters of `D`, each with a vote extending `D` that
the node admitted (or cast) in `[t_s, t_s + 2Δ)`. -/
private theorem optimistic_seats (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Relayed tr U X s D := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hfl
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hX hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hcond
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34 hcond
  refine ⟨ℓ, A, hpt, hΦU, h34, ?_⟩
  rintro u ⟨v, hv, rfl, R, hR, hRr, hDR⟩
  have hvs := optimisticPoint_pool_slot hr hX hpt hv
  have htk : tr.time k < sp.ts s + 2 * sp.Δ := not_le.1 (not_or.1 (not_or.1 hcond).2).2
  refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
  exact admitted_in_window hr hX hvs (optimisticPoint_pool_post hr hX hpt s hv) le_rfl
    fun k' hk' _ => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk')) htk

/-- A `Relayed` vote reaches an honest node's update of slot `s` (its restarts at or before `t_s`)
under `Sync`: the node holds it, or two other votes of its validator. -/
private theorem relayed_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : Relayed tr U X s D u) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_forward hr hsync hX hsend h1 (by rw [ts_succ_add]; linarith) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by rw [ht]; linarith)
    fun t ht₁ ht₂ => by rw [slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]; omega
  rwa [hvs] at this

/-- Relay delivery to an update uses no recipient deadline beyond that update. -/
private theorem relayed_held_before (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {s : Nat} {b : Time} (hsync : SyncACBefore H U b tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : Relayed tr U X s D u) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_before_forward hr hsync hX hsend (by linarith) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by rw [ht]; linarith)
    fun t ht₁ ht₂ => by rw [slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]; omega
  rwa [hvs] at this

/-- **Against an update.** At an honest update of slot `s` whose validators `S` support `DY`
without equivocating, the validators `T` with relayed votes for a block `D` that conflicts with
`DY` are voters there, and none is in `S`. -/
private theorem relayed_against_of_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    {X Y : Fin sp.n} {c : Nat} {D DY : Blk sp.n FGP}
    (held : ∀ {u}, Relayed tr U X s D u →
      ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
        (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}))
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have hU := hr.coherent
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ :=
      held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

private theorem relayed_against (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D DY : Blk sp.n FGP}
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard :=
  relayed_against_of_held hr (relayed_held hr hsync hX hY hc ht hrs) hS hT hnc

end Consensus.Goldilocks.SA

/-! ## Over a Goldilocks run -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem ts_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  simp only [SAParams.ts]
  exact mul_nonneg (by linarith) (Int.natCast_nonneg s)

/-- Slot starts are monotone in the slot. -/
theorem ts_le_ts {s s' : Nat} (h : s ≤ s') : sp.ts s ≤ sp.ts s' :=
  (SA.ts_le_iff sp).2 (by exact_mod_cast h)

/-- Under `Sleepy`, `f < n/2`. -/
theorem two_faults_lt_of_sleepy (hsl : tr.SleepyRun H ΔF) : 2 * Hᶜ.ncard < sp.n := by
  have h := (hsl.2 0).1
  have hle : tr.honestAwakeJoined H (sp.toParams.slotTime 0) ≤ H.ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold RunTrace.FaultBound at h
  omega

/-- Under `Sleepy`, more than `f` honest validators are awake and joined at `t_s + Δ`. -/
theorem faults_lt_awake_joined (hsl : tr.SleepyRun H ΔF) (s : Nat) :
    Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard := by
  have h := (hsl.2 s).2.1
  have hT : sp.toParams.slotTime s + sp.toParams.Δ = sp.ts s + sp.Δ := by
    rw [sp.slotTime_eq]; simp only [SAParams.ts]
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
  rwa [hT] at h

/-- Under `Sleepy`, `Sync` from any `a ≥ 0` holds of the AC projection. -/
theorem syncAC_of_sleepy (hrun : GoldilocksRun proposer dg H tr) (hsl : tr.SleepyRun H ΔF)
    {a b : Time} (ha : 0 ≤ a) :
    SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) a b tr.projAC :=
  sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer ΔF a b
    hrun.toLocalRun (show tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b) (fun τ => a ≤ τ ∧ τ ≤ b) id from
      ⟨hsl.1.deltaF, fun x hx i m hm hw => hsl.1.message x hx i m hm (ha.trans hw.1),
        fun x hx i B hB hw => hsl.1.block x hx i B hB (ha.trans hw.1),
        fun x hx i B hB hw => hsl.1.relay x hx i B hB (ha.trans hw.1),
        fun x hx i a' h hw => hsl.1.attestation x hx i a' h (ha.trans hw.1)⟩)

variable {b : Time} {s₀ : Nat}

/-- On the window from slot `s₀` to `b`, `f < n/2` (`f < h_{t_{s₀}}`). -/
theorem two_faults_lt_of_window (hwin : SleepyWindow tr H ΔF s₀ b) : 2 * Hᶜ.ncard < sp.n := by
  obtain ⟨hb, -, hfb⟩ := sleepyWindow_iff.1 hwin
  have h := hfb s₀ le_rfl 0 (by simp) (by simpa using hb)
  have hle : tr.honestAwakeJoined H (sp.ts s₀ + 0) ≤ H.ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold RunTrace.FaultBound at h
  omega

/-- On the window from slot `s₀` to `b`, more than `f` honest validators are awake and joined at
`t_s + Δ ≤ b` for `s ≥ s₀`. -/
theorem faults_lt_awake_joined_win (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s)
    (hs : sp.ts s + sp.Δ ≤ b) :
    Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard := by
  have h := (sleepyWindow_iff.1 hwin).2.2 s hs₀ sp.Δ (by simp) hs
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
  exact h

/-- On the window from slot `s₀` to `b`, `Sync[a, b']` holds of the AC projection for
`t_{s₀} ≤ a` and `b' ≤ b − Δ`. -/
theorem syncAC_of_window (hrun : GoldilocksRun proposer dg H tr) (hwin : SleepyWindow tr H ΔF s₀ b)
    {a b' : Time} (ha : sp.ts s₀ ≤ a) (hb : b' ≤ b - sp.Δ) :
    SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) a b' tr.projAC :=
  have hs := (sleepyWindow_iff.1 hwin).2.1
  sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer ΔF a b'
    hrun.toLocalRun (show tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b') (fun τ => a ≤ τ ∧ τ ≤ b') id
      from ⟨hs.deltaF,
        fun x hx i m hm hw => hs.message x hx i m hm ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i B hB hw => hs.block x hx i B hB ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i B hB hw => hs.relay x hx i B hB ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i a' h hw => hs.attestation x hx i a' h ⟨ha.trans hw.1, hw.2.trans hb⟩⟩)

/-- Under `SleepyFrom`, `f < n/2` (`f < h_{t_{s₀}}`). -/
theorem two_faults_lt_of_from (hfrom : SleepyFrom tr H ΔF s₀) : 2 * Hᶜ.ncard < sp.n :=
  two_faults_lt_of_window (hfrom.window (b := sp.ts s₀) le_rfl)

/-- Under the prefix premises up to `b ≥ 0`, `f < n/2` (`f < h_0`). -/
theorem two_faults_lt_of_prefix (hpre : SleepyPrefix tr H ΔF b) : 2 * Hᶜ.ncard < sp.n :=
  two_faults_lt_of_window hpre.window

/-- Under the prefix premises up to `b`, more than `f` honest validators are awake and joined at
`t_s + Δ ≤ b`. -/
theorem faults_lt_awake_joined_upTo (hpre : SleepyPrefix tr H ΔF b) (s : Nat)
    (hs : sp.ts s + sp.Δ ≤ b) :
    Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard :=
  faults_lt_awake_joined_win hpre.window (Nat.zero_le s) hs

/-- Under the prefix premises up to `b`, `Sync[a, b']` holds of the AC projection for
`0 ≤ a` and `b' ≤ b − Δ`. -/
theorem syncAC_of_prefix (hrun : GoldilocksRun proposer dg H tr) (hpre : SleepyPrefix tr H ΔF b)
    {a b' : Time} (ha : 0 ≤ a) (hb : b' ≤ b - sp.Δ) :
    SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) a b' tr.projAC :=
  syncAC_of_window hrun hpre.window (by rwa [ts_natCast_zero]) hb

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 =
      (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal).1 t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- **An honest validator awake and joined at `t_s + Δ` votes in slot `s`**, at or before
`t_s + Δ`: its tick there runs `try_vote` unless it voted in slot `s` already. -/
theorem vote_of_awake_joined (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hw : tr.awake y (sp.ts s + sp.Δ))
    (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, SA.VoteAt tr.projAC y k e ∧ e.msg.slot = s ∧ tr.projAC.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 := ts_nonneg (sp := sp) s
  have hslot : sp.slot (sp.ts s + sp.Δ) = s :=
    SA.slot_of_mem sp s (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  obtain ⟨j, x, hj'⟩ := hrun.tick_of_awake y hy _ (by linarith)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 1)
      (by simp only [SAParams.ts]; ring)) hw
  obtain ⟨-, hk, -⟩ := hj'
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ) (.tick x)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ) (.tick x)).2[0]'hlen =
      (Node.acCall y (tr.state y j) (sp.ts s + sp.Δ) .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  have hc : tr.projAC.CallAt y j ℓ := ⟨hn0, by simp [RunTrace.projAC, hl, RunTrace.acLabel]⟩
  have htj : tr.projAC.time j = sp.ts s + sp.Δ := ht0
  have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hemit : (SA.acOnTick sp y (tr.projAC.state y j) ℓ.frame (tr.projAC.time j)).2 = ℓ.emits :=
    congrArg Prod.snd he
  have hnr : ¬ tr.RestartAt y j := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have hjo : SA.joined sp (tr.projAC.state y j) (tr.projAC.time j) := by
    rw [projAC_state hrun.toLocalRun hy j, htj]
    exact ((joined_projection sp ro dg H tr proposer hrun y hy _).2.1 j ⟨_, hn0, hl⟩ hnr ht0).1 hj
  rcases SA.acOnTick_votes y _ ℓ.frame hjo (by rw [htj, hslot]) with hv | ⟨e, he', hes⟩
  · rcases SA.votedSlot_cast hr hy j with h | ⟨k, hk, e, hve, hes⟩
    · omega
    · refine ⟨k, e, hve, ?_, (hr.time_mono hk.le).trans htj.le⟩
      rw [htj, hslot] at hv
      omega
  · refine ⟨j, e, ⟨ℓ, hc, hemit ▸ he'⟩, ?_, htj.le⟩
    rwa [htj, hslot] at hes

/-- **The honest validators awake and joined at `t_s + Δ` are participants** of an honest update
of slot `s`: their slot-`s` votes reach the writer, whose restarts are at or before `t_s`. -/
private theorem awake_participant (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat}
    (hsync : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s) (sp.ts s + sp.Δ)
      tr.projAC) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hw hj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have := SA.sync_forward hr hsync hy
    ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    hsk hk hX hu.1 (fun k' hk' hr' => (SA.update_restarts hr hX hu k' hk' hr').trans hsk)
    (by rw [hu.2.2.1]; linarith) fun t h₁ h₂ => by
      have : sp.slot t = s := SA.slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith)
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- Awake joined validators participate in a result observed before the finite deadline
cutoff. Only their vote deadlines are used; later receiver wakes are irrelevant. -/
theorem awake_participant_window_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat} {a b : Time}
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hw hj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    linarith
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    linarith
  have := SA.sync_window_before_forward hr hsync hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (ha.trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (SA.update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := SA.slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith)
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- The zero-source finite participant theorem retains its original interface. -/
theorem awake_participant_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat} {b : Time}
    (hsync : SyncACBefore H (tr.HonestBlocks H) b tr.projAC)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} :=
  awake_participant_window_before hrun hnc ⟨hsync.message, hsync.relay⟩
    (ts_nonneg s) hX hu hib hy hw hj

/-- If every honest validator is awake and joined, windowed forwarding gives more than
twice the faulty population in the actual update pool. No head resolution is needed. -/
theorem honest_participants_window_before
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a b : Time} {s : Nat}
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b)
    (hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ))
    (hf : 3 * Hᶜ.ncard < sp.n) :
    2 * Hᶜ.ncard < (SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard := by
  have hsub : H ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
    awake_participant_window_before hrun hnc hsync ha hX hu hib hy
      (hready y hy).1 (hready y hy).2
  have hcount := Set.ncard_le_ncard hsub
  have htotal : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- **A result and an optimistic selection of one slot are compatible** (RO): the `≥ 3n/4`
optimistic seats reach the writer, where none supports the result. -/
private theorem result_optimistic_compatible (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat}
    (hsync : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s)
      (sp.ts (s + 1 : Nat) + sp.Δ) tr.projAC) {X x : Fin sp.n} (hX : X ∈ H) (hx : x ∈ H)
    {i i' : Nat} {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i s C CV) (hO : SA.OptimisticLockAt tr.projAC x i' s C' CV') :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  by_contra hnc'
  obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := SA.result_side hrun' hX hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := SA.optimistic_seats hrun' hx hO
  have := SA.relayed_against hrun'.localRun hsync hx hX hc ht hrs hS hT fun h => hnc' (Or.symm h)
  have := hle (SA.voters {v | v ∈ (tr.projAC.state X i).pool s})
  omega

/-- `honest_vote_exists_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem honest_vote_exists_win (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s) (hs : sp.ts s + sp.Δ ≤ b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s := by
  obtain ⟨y, hy, hw, hj⟩ := Set.nonempty_of_ncard_ne_zero
    (Nat.zero_lt_of_lt (faults_lt_awake_joined_win hwin hs₀ hs)).ne'
  obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined hrun hnc hy hw hj
  exact ⟨y, hy, k, e, hv, hs⟩

/-- **Every slot up to `b` has an honest vote**: an honest validator awake and joined at
`t_s + Δ ≤ b` (there are more than `f ≥ 0` of them) votes in slot `s`. -/
theorem honest_vote_exists_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (s : Nat) (hs : sp.ts s + sp.Δ ≤ b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s :=
  honest_vote_exists_win hrun hnc hpre.window (Nat.zero_le s) hs

/-- **Every slot from `s₀` has an honest vote** under `SleepyFrom`. -/
theorem honest_vote_exists_from (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) {s : Nat} (hs₀ : s₀ ≤ s) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s :=
  honest_vote_exists_win hrun hnc (hfrom.window (b := sp.ts s + sp.Δ)
    ((ts_le_ts hs₀).trans (le_add_of_nonneg_right sp.toParams.hΔ.le))) hs₀ le_rfl

/-- **Every slot has an honest vote**: an honest validator awake and joined at `t_s + Δ` (there
are more than `f ≥ 0` of them) votes in slot `s`. -/
theorem honest_vote_exists (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (s : Nat) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s :=
  honest_vote_exists_upTo hrun hnc (hsl.prefix (le_max_right (sp.ts s + sp.Δ) 0)) s
    (le_max_left _ _)

/-- `honest_supporter_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem honest_supporter_win (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs₀ : s₀ ≤ s) (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, hX, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · -- a result: a counted validator is honest, by the strict majority over the participants
    have hmaj := SA.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ := faults_lt_awake_joined_win hwin hs₀ (by linarith)
    have hsync := syncAC_of_window hrun hwin (a := sp.ts s) (b' := sp.ts s + sp.Δ) (ts_le_ts hs₀)
      (by linarith)
    have hJV : {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
      awake_participant hrun hnc hsync hX hu hy.1 hy.2.1 hy.2.2
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint
          {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hrun'.honest.pool_vote X hX i₀ s _ hvp hwH
    obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hX hu.1
    exact ⟨_, hwH, j, e, hve, (hrun.time_mono hj.le).trans hi₀,
      SA.state_pool_slot sp hr hX i₀ s _ hvp, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · -- an optimistic selection: `3n/4 > f` voters
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    have hf := two_faults_lt_of_window hwin
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H := not_not.1 huH
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    exact ⟨_, huH, j, e, hve, (hrun.time_mono hj).trans hi₀, hvs, R, hΦU hR, hRr,
      Anc.mono hΦU hCR⟩

/-- An origin within the finite horizon has an honest supporter using only deadline-bounded
service and the fault bounds at slot points inside the horizon. -/
theorem honest_supporter_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb : 0 ≤ b) (hsync : tr.SyncBefore H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, hX, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · have hmaj := SA.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ := hfb s sp.Δ (by simp) (by linarith)
    change Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard at hJ
    have hJV : {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
      awake_participant_before hrun hnc (syncBefore_projection hrun.toLocalRun hsync)
        hX hu hi₀ hy.1 hy.2.1 hy.2.2
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint
          {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hrun'.honest.pool_vote X hX i₀ s _ hvp hwH
    obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hX hu.1
    exact ⟨_, hwH, j, e, hve, (hrun.time_mono hj.le).trans hi₀,
      SA.state_pool_slot sp hr hX i₀ s _ hvp, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    have hf : 2 * Hᶜ.ncard < sp.n := by
      have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
      change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
      have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
        Set.ncard_le_ncard fun x hx => hx.1
      have hn : H.ncard + Hᶜ.ncard = sp.n := by
        rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H := not_not.1 huH
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    exact ⟨_, huH, j, e, hve, (hrun.time_mono hj).trans hi₀, hvs, R, hΦU hR, hRr,
      Anc.mono hΦU hCR⟩

/-- **§2.1 up to `b`, an origin within `b` has an honest supporter**: an honest slot-`s` vote at a
time `≤ b` whose head extends it. -/
theorem honest_supporter_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  honest_supporter_win hrun hnc hpre.window (Nat.zero_le s) hC

/-- **§2.1 from `s₀`, an origin of label `s ≥ s₀` has an honest supporter**: an honest slot-`s`
vote whose head extends it, under `SleepyFrom`. -/
theorem honest_supporter_from (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginFrom tr H C s s₀) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  have ⟨b, hb⟩ := hC.origin.exists_within
  have ⟨x, hx, j, e, hv, _, hs, hext⟩ := honest_supporter_win hrun hnc
    (hfrom.window (le_max_right b (sp.ts s₀))) hC.le (hb.mono (le_max_left b _))
  ⟨x, hx, j, e, hv, hs, hext⟩

/-- **§2.1, an origin has an honest supporter**: an honest slot-`s` vote whose head extends it. -/
theorem honest_supporter (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : Origin tr H C s) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  have ⟨b, hb⟩ := hC.exists_within
  have ⟨x, hx, j, e, hv, _, hs, hext⟩ := honest_supporter_upTo hrun hnc
    (hsl.prefix (le_max_right b 0)) (hb.mono (le_max_left b 0))
  ⟨x, hx, j, e, hv, hs, hext⟩

/-- `same_label_compatible_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem same_label_compatible_win (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b)
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hs₀ : s₀ ≤ s)
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- `Sync` up to `t_{s+1} + Δ` from a result within `b`, at `t_s + 6Δ`
  have hsync : ∀ {Y i CV D}, tr.time i ≤ b → SA.ResultAt tr.projAC Y i s D CV →
      SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
        tr.projAC := fun hi ⟨_, hu, _⟩ => by
    have ht : tr.time _ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    exact syncAC_of_window hrun hwin (ts_le_ts hs₀) (by rw [hts]; linarith)
  obtain ⟨X, hX, i, CV, hi, hR | hO⟩ := originWithin_iff.1 hC <;>
    obtain ⟨X', hX', i', CV', hi', hR' | hO'⟩ := originWithin_iff.1 hC'
  · -- RR: each side's counted validators reach the other writer, where none supports it
    by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := SA.result_side hrun' hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := SA.result_side hrun' hX' hR'
    have h1 := SA.relayed_against hrun'.localRun (hsync hi hR) hX' hX hc ht hrs hS hSF'
      fun h => hnc' (Or.symm h)
    have h2 := SA.relayed_against hrun'.localRun (hsync hi hR) hX hX' hc' ht' hrs' hS' hSF hnc'
    omega
  · exact result_optimistic_compatible hrun hnc (hsync hi hR) hX hX' hR hO'
  · exact Or.symm (result_optimistic_compatible hrun hnc (hsync hi' hR') hX' hX hR' hO)
  · -- OO: an honest validator in common, with one slot-`s` vote
    have hr := hrun'.localRun
    have hU := hr.coherent
    have hf := two_faults_lt_of_window hwin
    have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
      (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
    by_contra hnc'
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := SA.optimistic_seats hrun' hX' hO'
    have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ℓ.frame s C)
      (SA.optimisticVoters sp A' ℓ'.frame s C')
    have := hle (SA.optimisticVoters sp A ℓ.frame s C ∪ SA.optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C ∩ SA.optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      SA.optimisticPoint_pool_vote hrun' hX' hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc' (SA.anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- Origins of one label compare using recipient deadlines only up to `b`. -/
theorem same_label_compatible_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : tr.SyncBefore H ΔF b)
    (hf : 2 * Hᶜ.ncard < sp.n)
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hs := syncBefore_projection hrun.toLocalRun hsync
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  have hro : ∀ {X x i i' D D' CV CV'}, X ∈ H → x ∈ H → tr.time i ≤ b →
      SA.ResultAt tr.projAC X i s D CV → SA.OptimisticLockAt tr.projAC x i' s D' CV' →
      Compatible (tr.HonestBlocks H) D D' := by
    intro X x i i' D D' CV CV' hX hx hi hR hO
    by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := SA.result_side hrun' hX hR
    obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := SA.optimistic_seats hrun' hx hO
    have := SA.relayed_against_of_held hrun'.localRun
      (SA.relayed_held_before hrun'.localRun hs hx hX hc ht hi hrs) hS hT
      fun h => hnc' (Or.symm h)
    have := hle (SA.voters {v | v ∈ (tr.projAC.state X i).pool s})
    omega
  obtain ⟨X, hX, i, CV, hi, hR | hO⟩ := originWithin_iff.1 hC <;>
    obtain ⟨X', hX', i', CV', hi', hR' | hO'⟩ := originWithin_iff.1 hC'
  · by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := SA.result_side hrun' hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := SA.result_side hrun' hX' hR'
    have h1 := SA.relayed_against_of_held hrun'.localRun
      (SA.relayed_held_before hrun'.localRun hs hX' hX hc ht hi hrs) hS hSF'
      fun h => hnc' (Or.symm h)
    have h2 := SA.relayed_against_of_held hrun'.localRun
      (SA.relayed_held_before hrun'.localRun hs hX hX' hc' ht' hi' hrs') hS' hSF hnc'
    omega
  · exact hro hX hX' hi hR hO'
  · exact Or.symm (hro hX' hX hi' hR' hO)
  · have hr := hrun'.localRun
    have hU := hr.coherent
    by_contra hnc'
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := SA.optimistic_seats hrun' hX' hO'
    have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ℓ.frame s C)
      (SA.optimisticVoters sp A' ℓ'.frame s C')
    have := hle (SA.optimisticVoters sp A ℓ.frame s C ∪ SA.optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C ∩ SA.optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      SA.optimisticPoint_pool_vote hrun' hX' hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc' (SA.anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- **§2.2 up to `b`, origins within `b` of one label are compatible** (RR, RO, OO). -/
theorem same_label_compatible_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' :=
  same_label_compatible_win hrun hnc hpre.window (Nat.zero_le s) hC hC'

/-- **§2.2 from `s₀`, origins of one label `s ≥ s₀` are compatible** under `SleepyFrom`. -/
theorem same_label_compatible_from (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginFrom tr H C s s₀) (hC' : OriginFrom tr H C' s s₀) :
    Compatible (tr.HonestBlocks H) C C' :=
  have ⟨b, hb⟩ := hC.origin.exists_within
  have ⟨b', hb'⟩ := hC'.origin.exists_within
  same_label_compatible_win hrun hnc (hfrom.window (le_max_right (max b b') (sp.ts s₀))) hC.le
    (hb.mono ((le_max_left b b').trans (le_max_left _ _)))
    (hb'.mono ((le_max_right b b').trans (le_max_left _ _)))

/-- **§2.2, origins of one label are compatible** (RR, RO, OO). -/
theorem same_label_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : Origin tr H C s) (hC' : Origin tr H C' s) : Compatible (tr.HonestBlocks H) C C' :=
  have ⟨b, hb⟩ := hC.exists_within
  have ⟨b', hb'⟩ := hC'.exists_within
  same_label_compatible_upTo hrun hnc (hsl.prefix (le_max_right (max b b') 0))
    (hb.mono ((le_max_left b b').trans (le_max_left _ 0)))
    (hb'.mono ((le_max_right b b').trans (le_max_left _ 0)))

/-- Two blocks below the head of one vote are compatible. -/
private theorem compatible_of_voteExtends (hU : Coherent (tr.HonestBlocks H)) {v : Vote sp.n}
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.VoteExtends (tr.HonestBlocks H) v C)
    (h' : SA.VoteExtends (tr.HonestBlocks H) v C') : Compatible (tr.HonestBlocks H) C C' := by
  obtain ⟨Hd, hHd, hHdr, hC⟩ := h
  obtain ⟨Hd', hHd', hHd'r, hC'⟩ := h'
  obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
  exact Anc.total hU hC hC'

/-- **Extending the origin frontier up to `b`**: `P_s` and `V_s` up to `b` give `P_{s+1}` up to
`b`. -/
theorem origins_below_succ_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H s b)
    (hV : VotesBelowUpTo tr H s b) : OriginsBelowUpTo tr H (s + 1) b := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  rw [originsBelowUpTo_iff] at hP ⊢
  -- an origin of label `s` and one of label `j < s` are below the honest supporter's head
  have hnew : ∀ C C' j, j < s → OriginWithin tr H C s b → OriginWithin tr H C' j b →
      Compatible (tr.HonestBlocks H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hib, hs, hext⟩ := honest_supporter_upTo hrun hnc hpre hC
    exact compatible_of_voteExtends hU hext
      (votesBelowUpTo_iff.1 hV C' j hC' x hx i e hv hib (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatible_upTo hrun hnc hpre hC hC'

/-- The finite-deadline origin step preserves the horizon on every vote witness. -/
theorem origins_below_succ_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : tr.SyncBefore H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H s b) (hV : VotesBelowUpTo tr H s b) :
    OriginsBelowUpTo tr H (s + 1) b := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  rw [originsBelowUpTo_iff] at hP ⊢
  have hnew : ∀ C C' j, j < s → OriginWithin tr H C s b → OriginWithin tr H C' j b →
      Compatible (tr.HonestBlocks H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hib, hs, hext⟩ := honest_supporter_before hrun hnc hb hsync hfb hC
    exact compatible_of_voteExtends hU hext
      (votesBelowUpTo_iff.1 hV C' j hC' x hx i e hv hib (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatible_before hrun hnc hsync hf hC hC'

/-- **Extending the origin frontier**: `P_s` and `V_s` give `P_{s+1}`. -/
theorem origins_below_succ (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H s) (hV : VotesBelow tr H s) :
    OriginsBelow tr H (s + 1) := by
  refine originsBelow_iff.2 fun C j C' j' hj hj' hC hC' => ?_
  obtain ⟨b, hb⟩ := hC.exists_within
  obtain ⟨b', hb'⟩ := hC'.exists_within
  exact originsBelowUpTo_iff.1 (origins_below_succ_upTo hrun hnc
    (hsl.prefix (le_max_right (max b b') 0)) (hP.upTo _) (hV.upTo _)) C j C' j' hj hj'
    (hb.mono ((le_max_left b b').trans (le_max_left _ 0)))
    (hb'.mono ((le_max_right b b').trans (le_max_left _ 0)))

/-- **Extending the origin frontier from `s₀`**: `P_s` and `V_s` from `s₀` give `P_{s+1}` from
`s₀`, under `SleepyFrom`. -/
theorem origins_below_succ_from (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) {s : Nat} (hP : OriginsBelowFrom tr H s₀ s)
    (hV : VotesBelowFrom tr H s₀ s) : OriginsBelowFrom tr H s₀ (s + 1) := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  rw [originsBelowFrom_iff] at hP ⊢
  -- an origin of label `s` and one of label `j < s` are below the honest supporter's head
  have hnew : ∀ C C' j, j < s → OriginFrom tr H C s s₀ → OriginFrom tr H C' j s₀ →
      Compatible (tr.HonestBlocks H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hs, hext⟩ := honest_supporter_from hrun hnc hfrom hC
    exact compatible_of_voteExtends hU hext
      (votesBelowFrom_iff.1 hV C' j hC' x hx i e hv (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatible_from hrun hnc hfrom hC hC'

end Consensus.Goldilocks.Compose

end
