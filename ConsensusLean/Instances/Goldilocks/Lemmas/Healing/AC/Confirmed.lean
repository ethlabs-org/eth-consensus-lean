module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ConfirmedBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SettledFrom
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the confirmed tip after an honest proposal (H.1 (ii))

The helpers of `proposal_confirmed` (up to the first update in `ConfirmedBase`), over a
`StandaloneRun` (H.1's premises) and an honest proposal `P` of slot `p`:

* `late_vote_held`: at an honest call from `t_s + 2Δ` on (`s ≥ r`), every honest slot-`s`
  vote is held, with its head in the call's frame, both resolved before `t_s + 2Δ`, before and
  after the call;
* `proposal_mem_tree`: `P` is in every honest frame from `t_p + Δ` on;
* `lock_compatible`, `liveLock_compatible`: every lock live at an honest call from
  `t_p + 6Δ` on, before or after it, compares with `P` (labels `< p` by `LocksSettled` and the
  exact slot-`p` votes, labels `≥ p` by their origin's honest supporter,
  `origin_compatible_proposal`);
* `first_update_post`, `first_update_record`: the slot-`p` update at `t_p + 6Δ` has result
  `P`, not vetoed, with `P` passing the fast test, so its own fast selection
  (`fastSelect_eq_result`);
* `record_step`, `record_extends`: from that update on the record extends `P` (a candidate
  compares with `P`, and an ancestor candidate is refused);
* `head_extends`: the head extends `P` (the latest view is of a slot `≥ p + 1` whose honest
  batch is held and resolved);
* `anc_acConfirmed_of_frame` (frame-only, shared with H.2): then the confirmed tip extends
  `P`. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## The record after the first update -/

/-- The record names a block of the frame that extends `P`. -/
private def RecP (Φ : Frm sp.n FGP) (P : Blk sp.n FGP) (A : SAState sp.n) : Prop :=
  ∃ R ∈ Φ.tree, R.root = A.latestConfirmed ∧ Φ.Anc P R

private theorem RecP.of_eq {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A A' : SAState sp.n}
    (h : A'.latestConfirmed = A.latestConfirmed) (hR : RecP Φ P A) : RecP Φ P A' := by
  obtain ⟨R, hR, hRr, hPR⟩ := hR
  exact ⟨R, hR, hRr.trans h.symm, hPR⟩

private theorem RecP.mono {Φ Φ' : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    (hsub : Φ.tree ⊆ Φ'.tree) (hR : RecP Φ P A) : RecP Φ' P A := by
  obtain ⟨R, hR, hRr, hPR⟩ := hR
  exact ⟨R, hsub hR, hRr, hPR.mono hsub⟩

/-- A record write of a candidate comparing with `P` keeps the record extending `P`: an ancestor
candidate is refused, a descendant replaces it. -/
private theorem RecP.ulc {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    (hR : RecP Φ P A) {C : Blk sp.n FGP} (hC : C ∈ Φ.tree) (hcomp : Compatible Φ.tree C P) :
    RecP Φ P (updateLatestConfirmed sp A Φ C) := by
  unfold updateLatestConfirmed
  split_ifs with h
  · exact hR
  · refine ⟨C, hC, rfl, ?_⟩
    rcases hcomp with hCP | hPC
    · exfalso
      obtain ⟨R, hR, hRr, hPR⟩ := hR
      exact h ⟨R, hR, hRr, hCP.trans hPR⟩
    · exact hPC

private theorem lc_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold admitVote; split_ifs <;> rfl

private theorem lc_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).latestConfirmed = A.latestConfirmed := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').latestConfirmed = A'.latestConfirmed from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, lc_admitVote]

private theorem pool_sub_tryVote
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ∀ σ, ∀ v ∈ A.pool σ, v ∈ (tryVoteWithM sp wm x L A Φ t).1.pool σ := by
  intro σ v hv
  unfold tryVoteWithM
  dsimp only
  split_ifs
  · exact hv
  · exact hv
  all_goals try exact hv
  all_goals
    rw [optimisticConfirmationM_keep _ SA.optimistic_pool]
    unfold admitVote
    split_ifs
    · exact hv
    · exact hv
    · simp only [Function.update_apply]
      split_ifs with hσ
      · subst hσ; exact List.mem_append_left _ hv
      · exact hv

private theorem RecP.ofOptimistic {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    {t : Time} (hR : RecP Φ P A)
    (hsel : ∀ B, optimisticSelect sp A Φ t = some B → Compatible Φ.tree B P) :
    RecP Φ P (optimisticConfirmationM sp wm A Φ t) := by
  refine optimisticConfirmationM_of (P := RecP Φ P) ?_ hR
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact hR
  · have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    let N : Set (Nat × Bool × Nat) := {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))}
    exact RecP.ulc (A := { A with locks := addLocks sp A.locks Φ t (sp.slot t) N })
      hR (deepest_mem hB).1.1 (hsel B h)

private theorem RecP.ofTryVote
    {L : Set Lock} {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {x : Fin sp.n}
    {A : SAState sp.n} {t : Time} (hR : RecP Φ P A)
    (hsel : ∀ A' B, A'.pool = (tryVoteWithM sp wm x L A Φ t).1.pool →
      optimisticSelect sp A' Φ t = some B → Compatible Φ.tree B P) :
    RecP Φ P (tryVoteWithM sp wm x L A Φ t).1 := by
  unfold tryVoteWithM at hsel ⊢
  dsimp only at hsel ⊢
  split_ifs at hsel ⊢
  · exact hR
  · exact hR
  all_goals try exact RecP.of_eq rfl hR
  all_goals
    exact RecP.ofOptimistic (RecP.of_eq (lc_admitVote _ _ _) hR) fun B hB =>
      hsel _ B (optimisticConfirmationM_keep _ SA.optimistic_pool _ _ _ _).symm hB

private theorem RecP.ofUpdate {Φ : Frm sp.n FGP} {P : Blk sp.n FGP} {A : SAState sp.n}
    {t : Time} {s : Nat} (hR : RecP Φ P A)
    (hres : ∀ C, getConfirmation sp A Φ s = some C → Compatible Φ.tree C P) :
    RecP Φ P (updateConfirmationM sp wm A Φ t s) := by
  refine RecP.of_eq (updateConfirmationM_field SAState.latestConfirmed (fun _ _ => rfl) wm A Φ t s)
    ?_
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact hR
  · dsimp only
    split_ifs
    · exact hR
    all_goals
      exact RecP.ulc (A := { A with saved := Function.update A.saved s (some C.root) }) hR
        (deepest_mem hC).1.1 (hres C hC)

/-- `optimisticSelect_compatible` with the unlock given. -/
theorem optimisticSelect_compatibleU
    {uL : Nat → Set Lock} (hS : HealthyBaseU wm uL tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    {A : SAState sp.n} (hA : ∀ σ, ∀ v ∈ A.pool σ, v ∈ (tr.state y (c + 1)).pool σ)
    {B : Blk sp.n FGP} (hsel : optimisticSelect sp A ℓ.frame (tr.time c) = some B) :
    Compatible ℓ.frame.tree B P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  have hsl : p + 1 ≤ sp.slot (tr.time c) := by
    have := (ts_le_iff_le_slot sp (hr.time_nonneg c) (p + 1 : Nat)).1
      (by simp only [SAParams.ts] at htc ⊢; push_cast; linarith)
    exact_mod_cast this
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have hBt := (deepest_mem hsel).1.1
  have h34 := (deepest_mem hsel).1.2.1
  rw [hS.run.stock] at h34
  have hf := hS.two_faulty_lt
  have hlt : Hᶜ.ncard <
      (optimisticVoters sp A ℓ.frame (sp.slot (tr.time c)) B).ncard := by omega
  obtain ⟨u, ⟨x, hx, rfl, R, hR, hRr, hBR⟩, hu⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hx' := hA _ x hx
  obtain ⟨j', -, e', hve, rfl⟩ := hS.run.honest.pool_vote y hy (c + 1) _ _ hx' (not_not.1 hu)
  have hes := state_pool_slotU sp hr hy (c + 1) _ _ hx'
  have hcomp := compatible_of_vote hU hvotes (not_not.1 hu) hve (by omega)
    ⟨R, hΦU hR, hRr, hBR.mono hΦU⟩
  rcases hcomp with h | h
  · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hBt h hPt)
  · exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hPt h hBt)

/-- **An optimistic selection compares with `P`**: at an honest call at `t ≥ t_p + 6Δ`,
from a state whose pools the call keeps, the block an optimistic check selects has three
quarters of the committee as voters, one of them honest, whose vote (of a slot `> p`) extends
`P`. -/
theorem optimisticSelect_compatible (hS : HealthyBase tr H U proposer g)
    {p : Nat} {P : Blk sp.n FGP}
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    {A : SAState sp.n} (hA : ∀ σ, ∀ v ∈ A.pool σ, v ∈ (tr.state y (c + 1)).pool σ)
    {B : Blk sp.n FGP} (hsel : optimisticSelect sp A ℓ.frame (tr.time c) = some B) :
    Compatible ℓ.frame.tree B P :=
  optimisticSelect_compatibleU (hS := hS.toU) (p := p) (P := P) (hvotes := hvotes) (y := y)
      (hy := hy) (c := c) (ℓ := ℓ) (hc := hc) (htc := htc) (hPt := hPt) (A := A) (hA := hA)
          (B := B) (hsel := hsel)

/-- `record_step` with the unlock given. -/
theorem record_stepU
    {u : Nat → Set Lock} (hS : HealthyBaseU wm u tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    (hR : ∃ R ∈ ℓ.frame.tree, R.root = (tr.state y c).latestConfirmed ∧ ℓ.frame.Anc P R) :
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  change RecP ℓ.frame P (tr.state y c) at hR
  change RecP ℓ.frame P (tr.post c)
  have hst : tr.state y (c + 1) = tr.post c := by simp [Trace.state, hc.1, hc.2]
  have hopt : ∀ A' : SAState sp.n, (∀ σ, ∀ v ∈ A'.pool σ, v ∈ (tr.post c).pool σ) →
      ∀ B, optimisticSelect sp A' ℓ.frame (tr.time c) = some B →
        Compatible ℓ.frame.tree B P := fun A' hA' B hB =>
    optimisticSelect_compatibleU hS hvotes hy hc htc hPt (fun σ v hv => hst ▸ hA' σ v hv) hB
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have hpost : tr.post c =
      (stepWithM sp ro wm y (u c) (tr.state y c) ℓ.frame (tr.time c) ℓ.call).1 := by
    rw [he]
  generalize hA : tr.state y c = A at hR hpost
  generalize ht : tr.time c = t at hopt hpost htc
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hpost
    change tr.post c = (acOnTickWithM sp wm y (u c) A ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    unfold acOnTickWithM at hopt ⊢
    dsimp only at hopt ⊢
    by_cases hj : joined sp A t
    swap
    · simp only [eq_true hj, ↓reduceIte] at hopt ⊢
      exact hR
    simp only [eq_false (not_not.2 hj), ↓reduceIte] at hopt ⊢
    by_cases hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
    · have hv : ¬ t = sp.ts (sp.slot t) + sp.Δ := fun h => by linarith only [hu.1, hΔ, h]
      simp only [eq_true hu, eq_false hv, ↓reduceIte] at hopt ⊢
      -- the update of slot `slot(t) − 1 ≥ p`
      refine RecP.ofUpdate (A := A) hR fun C hC => ?_
      have hs0 := hu.2
      have hsl : p + 1 ≤ sp.slot t := by
        have := (ts_le_iff_le_slot sp (ht ▸ hr.time_nonneg c) (p + 1 : Nat)).1
          (by simp only [SAParams.ts] at htc ⊢; push_cast; linarith only [hΔ, htc])
        exact_mod_cast this
      have hts : sp.ts ((sp.slot t - 1 : Nat) : Int) + 4 * sp.Δ = sp.ts (sp.slot t) := by
        simp only [SAParams.ts]; push_cast [Nat.cast_sub (by omega : 1 ≤ sp.slot t)]; ring
      have hps : sp.ts p ≤ sp.ts ((sp.slot t - 1 : Nat) : Int) := (ts_le_iff sp).2 (by omega)
      rw [← hA] at hC
      obtain ⟨z, hz, j', e, hv, hes, hext⟩ := result_extendedU hS (hp.trans hps) hy hc
        (by rw [ht]; linarith only [hu.1, hΔ, hts]) hC
      have hcomp := compatible_of_vote hU hvotes hz hv (by omega) hext
      have hCt := (deepest_mem hC).1.1
      rcases hcomp with h | h
      · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hCt h hPt)
      · exact Or.inr (anc_tree_of_anc_U hU hΦ hΦU hPt h hCt)
    simp only [eq_false hu, ↓reduceIte] at hopt ⊢
    by_cases hv : t = sp.ts (sp.slot t) + sp.Δ
    · simp only [eq_true hv, ↓reduceIte] at hopt ⊢
      exact RecP.ofTryVote (L := u c) hR fun A' B hA' hB =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B hB
    · simp only [eq_false hv, ↓reduceIte] at hopt ⊢
      exact hR
  | proposal =>
    rw [hcall] at hpost
    change tr.post c = (acProposalWith sp (u c) A ℓ.frame t).1 at hpost
    rw [hpost]
    refine RecP.of_eq ?_ hR
    unfold acProposalWith; split_ifs <;> rfl
  | toFG =>
    rw [hcall] at hpost
    change tr.post c = (acToFG sp A ℓ.frame t).1 at hpost
    rw [hpost]
    refine RecP.of_eq ?_ hR
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    rw [hcall] at hpost
    change tr.post c = (tryVoteWithM sp wm y (u c)
      (optimisticConfirmationM sp wm (admitVote sp A t m) ℓ.frame t) ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    refine RecP.ofTryVote (L := u c) (RecP.ofOptimistic (RecP.of_eq (lc_admitVote _ _ _) hR)
      fun B hB => hopt _ (fun σ v hv => ?_) B hB) fun A' B hA' hB =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B hB
    exact pool_sub_tryVote (L := u c) _ _ _ _ σ v
      (by rw [optimisticConfirmationM_keep _ SA.optimistic_pool]; exact hv)
  | block B =>
    rw [hcall] at hpost
    change tr.post c = (tryVoteWithM sp wm y (u c)
      (optimisticConfirmationM sp wm (blockReceipt sp A t B) ℓ.frame t) ℓ.frame t).1 at hpost
    rw [hpost] at hopt ⊢
    refine RecP.ofTryVote (L := u c) (RecP.ofOptimistic (RecP.of_eq (lc_blockReceipt _ _ _) hR)
      fun B' hB' => hopt _ (fun σ v hv => ?_) B' hB') fun A' B' hA' hB' =>
        hopt A' (fun σ v hv => by rw [← hA']; exact hv) B' hB'
    exact pool_sub_tryVote (L := u c) _ _ _ _ σ v
      (by rw [optimisticConfirmationM_keep _ SA.optimistic_pool]; exact hv)
  | restart =>
    rw [hcall] at hpost
    change tr.post c = (acRestart sp ro y A ℓ.frame t).1 at hpost
    rw [hpost]
    exact RecP.of_eq ((restart_state sp) FGP ro y A ℓ.frame t hΦ
      (ht ▸ hr.time_nonneg c)).2.2.1 hR

/-- **The record step**: an honest call at `t ≥ t_p + 6Δ` keeps the record extending `P`:
every candidate it writes (an optimistic selection, or the result of an update of a slot `≥ p`)
compares with `P`, and a restart keeps the record. -/
theorem record_step (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (htc : sp.ts p + 6 * sp.Δ ≤ tr.time c) (hPt : P ∈ ℓ.frame.tree)
    (hR : ∃ R ∈ ℓ.frame.tree, R.root = (tr.state y c).latestConfirmed ∧ ℓ.frame.Anc P R) :
    ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R :=
  record_stepU (hS := hS.toU) (p := p) (P := P) (hp := hp) (hvotes := hvotes) (y := y) (hy := hy)
      (c := c) (ℓ := ℓ) (hc := hc) (htc := htc) (hPt := hPt) (hR := hR)

/-- `trivial_tree_mono` with the unlock given. -/
theorem trivial_tree_monoU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {c c' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc' : tr.CallAt y c' ℓ')
    (hc : tr.CallAt y c ℓ) (hcc : c' ≤ c) : ℓ'.frame.tree ⊆ ℓ.frame.tree := by
  intro X hX
  rw [(hS.trivial y hy c' ℓ' hc').2.2.2] at hX
  rw [(hS.trivial y hy c ℓ hc).2.2.2]
  rcases Set.mem_insert_iff.1 hX with rfl | ⟨k, hk, hacc⟩
  · rw [← trivial_F_eqU hS hy hy hc hc']
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨k, hk.trans hcc, hacc⟩

/-- Under trivial frames the tree of an honest node only grows. -/
theorem trivial_tree_mono (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {c c' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc' : tr.CallAt y c' ℓ')
    (hc : tr.CallAt y c ℓ) (hcc : c' ≤ c) : ℓ'.frame.tree ⊆ ℓ.frame.tree :=
  trivial_tree_monoU (hS := hS.toU) (y := y) (hy := hy) (c := c) (c' := c') (ℓ := ℓ) (ℓ' := ℓ')
      (hc' := hc') (hc := hc) (hcc := hcc)

/-- `record_extends_coreU` with the locks settled above the floor `p` only (at a mode of width
`k`). -/
theorem record_extends_core_fromU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) (hw : wm.width = sp.k)
    {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposalU u tr (proposer p) p P)
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledFromU u tr H U p (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓk : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt y k ℓk) (hcallk : ℓk.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) :
    ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg0 := gbar_nonneg g
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAtU hr hpH hc).2 ((accept_newU sp hr hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro ℓ hc hkc
    have htc : sp.ts p + 6 * sp.Δ ≤ tr.time c := htk ▸ hr.time_mono hkc
    rcases Nat.eq_or_lt_of_le hkc with rfl | hkc
    · obtain rfl : ℓ = ℓk := Option.some.inj (hc.2.symm.trans hck.2)
      exact first_update_recordU hS.toHealthyBaseU (by
          linarith only [hp4, hΔ, hΘ]) hexact hy hc hcallk htk
        (proposal_mem_treeU hS hpH hP (by linarith only [hp4, hΔ, hΘ]) hy hc (by
            linarith only [htk, hΔ])).1
        (liveLock_compatible_core_fromU hS hw hp4 hset hexact hvotes hPU hy hc htc (Or.inl rfl))
    have hPt := (proposal_mem_treeU hS hpH hP (by linarith only [hp4, hΔ, hΘ]) hy hc (by
        linarith only [hΔ, htc])).1
    rcases tr.noCall_or_lastCall y c with hn | ⟨c', hc'c, ℓ', hc', hnb⟩
    · exact absurd hck (hn k (Nat.zero_le _) hkc ℓk)
    have hkc' : k ≤ c' := by
      by_contra h
      exact hnb k (by omega) hkc ℓk hck
    have hR := ih c' hc'c ℓ' hc' hkc'
    rw [← tr.state_of_lastCall hc' hc'c hnb] at hR
    exact record_stepU hS.toHealthyBaseU (by linarith only [hp4, hΔ, hΘ]) hvotes hy hc htc hPt
      (RecP.mono (trivial_tree_monoU hS hy hc' hc hc'c.le) hR)

/-- `record_extends_core` with the unlock given, at a mode of width `k`. -/
theorem record_extends_coreU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) (hw : wm.width = sp.k)
    {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposalU u tr (proposer p) p P)
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettledU u tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓk : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt y k ℓk) (hcallk : ℓk.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) :
    ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R :=
  record_extends_core_fromU hS hw hpH hP hp4 (hset.toFrom p) hexact hvotes hy hck hcallk htk

/-- **The record after the first update**: from an honest node's tick at `t_p + 6Δ` on,
at every later call of the node, the record after the call names a block of the call's frame
that extends `P`. -/
theorem record_extends_core (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓk : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt y k ℓk) (hcallk : ℓk.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) :
    ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R :=
  record_extends_coreU (hS := hS.toU) (hw := rfl) (p := p) (P := P) (hpH := hpH) (hP := hP.toU)
      (hp4 := hp4)
      (hset := hset.toU) (hexact := hexact) (hvotes := hvotes) (y := y) (hy := hy) (k := k)
          (ℓk := ℓk) (hck := hck) (hcallk := hcallk) (htk := htk)

/-- `record_extends_core` from `t_p ≥ ḡ + 2Θ + 8Δ`. -/
theorem record_extends (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hexact : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓk : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt y k ℓk) (hcallk : ℓk.call = .tick) (htk : tr.time k = sp.ts p + 6 * sp.Δ) :
    ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      ∃ R ∈ ℓ.frame.tree, R.root = (tr.post c).latestConfirmed ∧ ℓ.frame.Anc P R :=
  record_extends_core hS hpH hP (by linarith only [hp, sp.toParams.hΔ, Θ_nonneg sp])
    hset hexact hvotes hy hck hcallk htk

/-! ## The head and the confirmed tip -/

/-- `head_extends_of_frame` with the unlock given. -/
theorem head_extends_of_frameU
    {uL : Nat → Set Lock} (hS : HealthyBaseU wm uL tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    (hPv : P ∈ ℓ.frame.viableTree ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  have hPt := hPv.1
  have hst : tr.state y (j + 1) = tr.post j := by simp [Trace.state, hc.1, hc.2]
  have ht0 := hr.time_nonneg j
  -- the latest view's slot `m ≥ p + 1`, due
  obtain ⟨m, hm, hpm, htm⟩ : ∃ m : Nat, (latestView sp (tr.post j) ℓ.frame (tr.time j)).2 = m ∧
      p + 1 ≤ m ∧ sp.ts m + 2 * sp.Δ ≤ tr.time j := by
    have h1 : sp.ts (sp.slot (tr.time j)) ≤ tr.time j := (ts_le_iff_le_slot sp ht0 _).2 le_rfl
    have h2 : tr.time j < sp.ts (sp.slot (tr.time j)) + 4 * sp.Δ := by
      have := (ts_le_iff_le_slot sp ht0 ((sp.slot (tr.time j) : Int) + 1)).not.2 (by omega)
      simp only [SAParams.ts] at this ⊢
      linarith only [this]
    have hs1 : p + 1 ≤ sp.slot (tr.time j) := by
      have := (ts_le_iff_le_slot sp ht0 (p + 1 : Nat)).1
        (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith only [htj, h1, h2])
      exact_mod_cast this
    unfold latestView
    dsimp only
    split_ifs with h
    · exact ⟨_, rfl, hs1, h⟩
    · have hs2 : p + 2 ≤ sp.slot (tr.time j) := by
        by_contra hlt
        have heq : sp.slot (tr.time j) = p + 1 := by omega
        rw [heq] at h
        exact h (by simp only [SAParams.ts] at htj ⊢; push_cast; linarith only [htj])
      have h1s : 1 ≤ sp.slot (tr.time j) := by omega
      refine ⟨sp.slot (tr.time j) - 1, by rw [Nat.cast_sub h1s]; push_cast; ring, by omega, ?_⟩
      have : sp.ts ((sp.slot (tr.time j) - 1 : Nat) : Int) + 4 * sp.Δ =
          sp.ts (sp.slot (tr.time j)) := by
        simp only [SAParams.ts]; rw [Nat.cast_sub h1s]; push_cast
        ring
      linarith only [h1, h2, this]
  have hm4 : gbar g + 4 * sp.Δ ≤ sp.ts m := hp.trans ((ts_le_iff sp).2 (by omega))
  have hV : (latestView sp (tr.post j) ℓ.frame (tr.time j)).1 =
      voteView (tr.post j) ℓ.frame m ⊤ := by
    rw [← hm]; rfl
  unfold acHead
  rw [hV, hm]
  have hsupp : (voteView (tr.post j) ℓ.frame m ⊤).support ⊆
      (voteView (tr.post j) ℓ.frame m ⊤).votes := fun v hv => List.mem_of_mem_filter hv
  have hvotes_sub : (voteView (tr.post j) ℓ.frame m ⊤).votes ⊆
      {v | v ∈ (tr.post j).pool m} := by
    intro v hv
    have := List.mem_of_mem_filter hv
    simpa [SAState.poolAt] using this
  have h1 : H ⊆ supporters ℓ.frame (voteView (tr.post j) ℓ.frame m ⊤) m P := by
    intro u hu
    obtain ⟨i, e, hv, hes⟩ := honest_votes_in_slotU hS hm4 u hu
    obtain ⟨Hd', hHd', hHd'r, hPHd'⟩ := hvotes u hu i e hv (by omega)
    obtain ⟨Hd, hHdt, hHdr, hHds, hh⟩ := late_vote_held_of_frameU hS hy hc hm4 htm hu hv hes
      fun Hd hHd hHdr => by
        rw [hU.1 hHd hHd' (hHdr.trans hHd'r.symm)]
        exact ((hΦ.rooted.2 P hPt).mono hΦU).trans hPHd'
    obtain ⟨hmem, hvst, hbst⟩ := hh (j + 1) (Or.inr rfl)
    rw [hst] at hmem hvst hbst
    obtain ⟨hval, -⟩ := castAt_specU hr hu ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    have hres : resolutionTime (tr.post j) ℓ.frame e.msg < ⊤ :=
      resolutionTime_lt_of hΦ hHdt hHdr (hes ▸ hHds) (hvst.trans (SA.etime_of_lt_top _))
        (hbst.trans (SA.etime_of_lt_top _))
    have hmemv : e.msg ∈ (voteViewList (tr.post j) ℓ.frame m ⊤).1 := by
      simp only [voteViewList, SAState.poolAt, List.mem_filter, decide_eq_true_eq]
      exact ⟨by simpa using hmem, hvst.trans (SA.etime_of_lt_top _)⟩
    refine ⟨fun heq => honest_not_equivocator_poolU hS hy (j + 1) m hu ?_, e.msg, ?_, hval,
      by rw [hes], ?_⟩
    · rw [hst]; exact equivocators_mono hvotes_sub heq
    · change e.msg ∈ (voteViewList (tr.post j) ℓ.frame m ⊤).2
      simp only [voteViewList, List.mem_filter, decide_eq_true_eq] at hmemv ⊢
      exact ⟨hmemv, hres⟩
    · obtain rfl : Hd = Hd' := hU.1 (hΦU hHdt) hHd' (hHdr.trans hHd'r.symm)
      exact ⟨Hd, hHdt, hHdr, anc_tree_of_anc_U hU hΦ hΦU hPt hPHd' hHdt⟩
  have h3 : (Set.univ : Set (Fin sp.n)).ncard < 2 * H.ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := hS.two_faulty_lt
    omega
  exact anc_getHead hU hΦ hΦU (tr.post j) (tr.time j) _ (m : Int) (dom := ℓ.frame.tree)
    subset_rfl (fun B hB X hX => mem_of_anc hX hB) (Or.inl hPv) hlocks
    fun X Cx hCx hpx hCxP => isBest_of_majority hΦ hsupp (fun B hB => hB.1) h1
      (Set.subset_univ _) h3 hCx hpx hCxP

/-- **The head extends `P`** (also for H.2 (ii)): at an honest call at `t ≥ t_p + 6Δ` whose frame
has `P` in its viable tree, the head after the call extends `P`: the latest view is of a slot
`m ≥ p + 1` whose honest votes are all held and resolved and extend `P` (`n − f > n/2` supporters
along `P`), and every live lock compares with `P`. -/
theorem head_extends_of_frame (hS : HealthyBase tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j)
    (hPv : P ∈ ℓ.frame.viableTree ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) :=
  head_extends_of_frameU (hS := hS.toU) (p := p) (P := P) (hp := hp) (hvotes := hvotes) (y := y)
      (hy := hy) (j := j) (ℓ := ℓ) (hc := hc) (htj := htj) (hPv := hPv) (hlocks := hlocks)

/-- `head_extends` with the unlock given. -/
theorem head_extendsU
    {u : Nat → Set Lock} (hS : StandaloneRunU wm u tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hS.run.localRun hy hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial y hy j ℓ hc
  exact head_extends_of_frameU hS.toHealthyBaseU hp hvotes hy hc htj
    ⟨hPt, by rw [hfc]; exact hΦ.rooted.2 P hPt, P, hPt, by rw [hvh]; exact hPt,
      Relation.ReflTransGen.refl⟩ hlocks

/-- `head_extends_of_frame` under trivial frames, where every tree block is viable. -/
theorem head_extends (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hp : gbar g + 4 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (htj : sp.ts p + 6 * sp.Δ ≤ tr.time j) (hPt : P ∈ ℓ.frame.tree)
    (hlocks : ∀ L ∈ liveLockBlocks sp (tr.post j).locks ℓ.frame (tr.time j),
      Compatible U L P) :
    ℓ.frame.Anc P (acHead sp (tr.post j) ℓ.frame (tr.time j)) :=
  head_extendsU (hS := hS.toU) (p := p) (P := P) (hp := hp) (hvotes := hvotes) (y := y) (hy := hy)
      (j := j) (ℓ := ℓ) (hc := hc) (htj := htj) (hPt := hPt) (hlocks := hlocks)

/-- **The confirmed tip from the frame** (also for H.2 (ii)): in a well-formed frame inside a
coherent `U`, a block `P` below both the effective record (`latest_confirmed` if in the tree, else
`Φ.F`) and the head is below the confirmed tip, the deepest common ancestor of the two (when `P` is
not in the tree it is below `Φ.F`, which every block of the tree extends). -/
theorem anc_acConfirmed_of_frame (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} {t : Time} {P : Blk sp.n FGP}
    (hPC : Anc U P ((lookup Φ A.latestConfirmed).getD Φ.F))
    (hPH : Anc U P (acHead sp A Φ t)) : Anc U P (acConfirmed sp A Φ t) := by
  have hCt : (lookup Φ A.latestConfirmed).getD Φ.F ∈ Φ.tree := by
    cases h : lookup Φ A.latestConfirmed with
    | none => exact hΦ.rooted.1
    | some R => exact (lookup_eq_some h).1
  have hHt : acHead sp A Φ t ∈ Φ.tree :=
    getHead_mem hΦ (T := Φ.viableTree Φ.tree) (fun _ hX => hX.1) _ _ _ _
  unfold acConfirmed
  dsimp only
  have hFS : Φ.F ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)} :=
    ⟨hΦ.rooted.1, hΦ.rooted.2 _ hCt, hΦ.rooted.2 _ hHt⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X h => h.1) ⟨Φ.F, hFS⟩
  have hch : ∀ B ∈ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (acHead sp A Φ t)}, ∀ C ∈ {X | X ∈ Φ.tree ∧
      Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧ Φ.Anc X (acHead sp A Φ t)},
      Compatible Φ.tree B C := fun B hB C hC => anc_total hΦ.coherent hB.2.1 hC.2.1
  rw [hD, Option.getD_some]
  by_cases hPt : P ∈ Φ.tree
  · exact (anc_deepest hΦ (fun X h => h.1) hch hD P
      ⟨hPt, anc_tree_of_anc_U hU hΦ hΦU hPt hPC hCt,
        anc_tree_of_anc_U hU hΦ hΦU hPt hPH hHt⟩).mono hΦU
  · rcases anc_total hU hPC ((hΦ.rooted.2 _ hCt).mono hΦU) with h | h
    · exact h.trans ((anc_deepest hΦ (fun X h => h.1) hch hD Φ.F hFS).mono hΦU)
    · exact absurd (frame_mem_of_between sp hU hΦ hΦU hCt hPC h) hPt

/-- The confirmed tip when the record names a block of the frame extending `P` and the head
extends `P`. -/
theorem anc_acConfirmed_of_record (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} {t : Time} {P R : Blk sp.n FGP} (hR : R ∈ Φ.tree)
    (hRr : R.root = A.latestConfirmed) (hPR : Φ.Anc P R) (hPH : Φ.Anc P (acHead sp A Φ t)) :
    Anc U P (acConfirmed sp A Φ t) := by
  have hlk : lookup Φ A.latestConfirmed = some R := by
    cases h : lookup Φ A.latestConfirmed with
    | none => exact absurd ⟨R, hR, hRr⟩ (lookup_eq_none h)
    | some R' =>
      obtain ⟨h1, h2⟩ := lookup_eq_some h
      rw [hΦ.coherent.1 h1 hR (h2.trans hRr.symm)]
  refine anc_acConfirmed_of_frame hU hΦ hΦU ?_ (hPH.mono hΦU)
  rw [hlk, Option.getD_some]
  exact hPR.mono hΦU

/-- Finite stamped honest batch from actual unanimous casts. The actual-vote existence
input is separate from agreement; no ready-proposal support clause is needed. -/
theorem unanimous_pool_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts s) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts s)
    {P : Blk sp.n FGP} (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x ∈ H, ∃ i e, VoteAt tr x i e ∧ e.msg.slot = s ∧ e.msg.head = P.root) :
    ∀ x ∈ H, ∃ v ∈ (tr.state y j).pool s, v.val = x ∧ v.head = P.root ∧
      resolutionTime (tr.state y j) ell.frame v < ETime.of (sp.ts s + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.state y j).pool s, v'.val = x → v' = v := by
  have hr := hS.run.localRun
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  intro x hx
  obtain ⟨i, e, hv, hes, heP⟩ := hvotes x hx
  obtain ⟨B, hB, hBr, hBs, hmem, hvs, hbs⟩ :=
    late_vote_held_of_frame_before hS hy hc hs ht hjb hdeadline hrestart hx hv hes
      (fun B hBU hBr => by
        rw [hr.coherent.1 hBU (hPhiU hPt) (hBr.trans heP)]
        exact (hPhi.rooted.2 P hPt).mono hPhiU)
  obtain ⟨hval, -⟩ := castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, hmem, hval, heP,
    resolutionTime_lt_of hPhi hB hBr (hes ▸ hBs) hvs hbs, ?_⟩
  intro v' hv' hv'x
  obtain ⟨q, -, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j s v' hv' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr x hx q i e' e he' hv
    ((state_pool_slot sp hr hy j s _ hv').trans hes.symm)
  rfl

end Consensus.Goldilocks.SA

end
