module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the transfer to the proposal duty over any frames

The argument at the votes applies at a proposal; here over an AC run (`ACRun`) with the frame facts
as premises, so that H.1 (trivial frames, `StandaloneRun`) and H.2 (general frames, `InclusionRun`)
instantiate the same arguments. An honest `ac_proposal` of slot `σ + 1` (at cut `i` of `x`, label
`ℓ`, frame `Φ = ℓ.frame`) walks the full viable tree with the slot-`σ` votes it holds
(`vote_view(𝒜, Φ, σ, ⊤)`), from the anchor of its locks after unlocking against that view
(`acProposal_head`). Its head extends `B` when (`proposal_walk`)

* **(V)** `B ∈ Φ.tree` and `B` is in the full viable tree or at or below `fc_root`,
* every live lock after the unlocking is compatible with `B` (`unlocked_compatible`, from (L)),
* the children toward `B` are the best (a strict majority of the voters, or a cover).

The premises each setting supplies:

* **(P)** `HeldAtProposal`: a vote is in the proposer's slot-`σ` pool or its validator equivocates
  there, and its head is a block of `Φ.tree` with a finite stamp; for the honest slot-`σ` votes
  (batch), the counted votes of an update (A1.2, A1.8) or the optimistic pool's votes (A1.4 (a));
* **(L)** `HighLocksCompatible` (stored live locks of slot `≥ σ`), and for a result whose supporters
  may be under half, `LowLocksCompatible` (those of slot `< σ`);
* **(W)** the writer's pool covers the proposer's: every slot-`σ` vote the proposer holds is held
  by the update's writer, or its validator equivocates there (`writer_pool_proposal` gives it
  from `Sync[t_σ, t_σ + 4Δ]`).

Conclusions: `batch_proposal` (A1.3), `update_first_proposal` (A1.2), `optimistic_first_proposal`
(A1.4 (a)), `result_first_proposal` (A1.8 for an ancestor of a result). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-! ## The proposal duty -/

/-- `acProposal_head` with the unlock given. -/
theorem acProposal_headWith
    {L : Set Lock} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposalWith sp L A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ d.head = getHead sp { A with locks := L } Φ t
      (Φ.viableTree Φ.tree) (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) := by
  unfold acProposalWith at h
  split_ifs at h with hj
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hj, by rw [← h.1]⟩

/-- An `ac_proposal` that returns a duty head is joined, and its head is the walk of the full
viable tree with the held votes of the previous slot, from the anchor of the unlocked locks. -/
theorem acProposal_head {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposal sp A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ d.head = getHead sp
      { A with locks := (unlock sp A.locks Φ t ((sp.slot t : Int) - 1)
          (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))) } Φ t
      (Φ.viableTree Φ.tree) (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) :=
  acProposal_headWith (by rwa [acProposal_eq_acProposalWith] at h)

/-- `acProposal` at a time of slot `σ + 1` is `acProposalWith` of its unlock at `σ`. -/
theorem acProposal_eq_acProposalWith_slot {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {σ : Nat} (hslot : sp.slot t = σ + 1) :
    acProposal sp A Φ t = acProposalWith sp
      (unlock sp A.locks Φ t σ (View.ofLists (voteViewList A Φ σ ⊤))) A Φ t := by
  rw [acProposal_eq_acProposalWith, hslot, show ((σ + 1 : Nat) : Int) - 1 = σ by push_cast; ring]

/-- The unlock relation at an honest proposal of slot `σ + 1`. -/
theorem ACLocalRunU.lawful_proposal {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal) (hslot : sp.slot (tr.time i) = σ + 1) :
    UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) (u i) := by
  have h := hr.lawfulAt hx hc (frameIn_of_callAtU hr hx hc).1
  rw [hcall] at h
  simp only [callInputM, callViewM] at h
  rwa [hslot, show ((σ + 1 : Nat) : Int) - 1 = σ by push_cast; ring] at h

/-- `unlocked_compatible` for any locks related to the stored ones by the unlock relation. -/
theorem unlocked_compatibleRel (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {L L' : Set Lock} {t : Time}
    {σ : Int} {V : View sp.n}
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S, w ∈ equivocators V.votes ∨
        ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = σ ∧ AncR Φ B x.head) ∧
        sp.n ≤ 2 * S.ncard) ∨
      ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → (l.slot : Int) < σ → ∀ X ∈ U, X.root = l.block →
        Compatible U X B)
    (hhigh : ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → σ ≤ (l.slot : Int) → ∀ X ∈ U,
      X.root = l.block → Compatible U X B) (hwf : LocksWF sp L)
    (hL : UnlockRel sp L Φ t σ V L') :
    ∀ C ∈ liveLockBlocks sp L' Φ t, Compatible U C B := by
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  rintro C ⟨hC, l, ⟨l₁, hl₁, B₁, hB₁, hB₁r, -, rfl⟩, hlC⟩
  have hCe : C = Φ.viableAncestor B₁ :=
    hU.1 (hΦU hC) (hΦU (viableAncestor_anc hΦ hB₁).1) hlC.symm
  subst hCe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₁)) ?_
  -- the stored lock the related lock comes from
  obtain ⟨l₃, hl₃, B₃, hB₃, hB₃r, hlive, hs, -, -, hmv, hkeep⟩ := hL l₁ hl₁
  replace hlive : sp.slot t ≤ l₃.slot + sp.k := hlive.trans (hwf.cap hl₃)
  have hva := (viableAncestor_anc hΦ hB₃).1
  have h₂₃ : Anc U (Φ.viableAncestor B₃) B₃ := Anc.mono hΦU (anc_viableAncestor _ B₃)
  by_cases hlt : (l₃.slot : Int) < σ
  · obtain ⟨Y, hY, hYr, hYT⟩ := hmv hlt
    obtain rfl : B₁ = Y := hΦ.coherent.1 hB₁ hY (hB₁r.trans hYr.symm)
    rcases hlow with ⟨S, hS, hn⟩ | hlow
    · exact (unlockRel_compatible hΦ hB hS hn hL l₁ hl₁ (hs ▸ hlt) B₁ hB₁ hB₁r).imp
        (Anc.mono hΦU) (Anc.mono hΦU)
    · exact down ((Anc.mono hΦU (hYT.trans (unlockTarget_anc sp hΦ V σ hva).2)).trans h₂₃)
        (hlow l₃ hl₃ hlive hlt B₃ (hΦU hB₃) hB₃r)
  · obtain rfl : B₁ = Φ.viableAncestor B₃ :=
      hΦ.coherent.1 hB₁ hva (hB₁r.trans (hkeep (not_lt.1 hlt)))
    exact down h₂₃ (hhigh l₃ hl₃ hlive (not_lt.1 hlt) B₃ (hΦU hB₃) hB₃r)

/-- **The unlocked locks are compatible** with `B ∈ Φ.tree` (A0.4 at the unlock): the unlocking
against a view `V` of slot `σ` is compatible with `B ∈ Φ.tree` when every stored live lock of slot
`≥ σ` is, and either half of the committee support `B` or equivocate in `V` (the unlocking moves
the older locks to compatible ancestors), or every stored live lock of slot `< σ` is compatible
with `B` too. -/
theorem unlocked_compatible (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {L : Set Lock} {t : Time} {σ : Int}
    {V : View sp.n}
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S, w ∈ equivocators V.votes ∨
        ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = σ ∧ AncR Φ B x.head) ∧
        sp.n ≤ 2 * S.ncard) ∨
      ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → (l.slot : Int) < σ → ∀ X ∈ U, X.root = l.block →
        Compatible U X B)
    (hhigh : ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → σ ≤ (l.slot : Int) → ∀ X ∈ U,
      X.root = l.block → Compatible U X B) (hwf : LocksWF sp L) :
    ∀ C ∈ liveLockBlocks sp (unlock sp L Φ t σ V) Φ t, Compatible U C B :=
  unlocked_compatibleRel hU hΦ hΦU hB hlow hhigh hwf (unlockRel_unlock hΦ L t σ V)

/-! ## The premises -/

/-- **(P)** The vote `v` reaches the proposer (state `A`, frame `Φ`, slot `σ`): it is in the
slot-`σ` pool or its validator equivocates there, and its head is a block of `Φ.tree` with a
finite stamp. -/
def HeldAtProposal (A : SAState sp.n) (Φ : Frm sp.n FGP) (σ : Nat) (v : Vote sp.n) : Prop :=
  (v ∈ A.pool σ ∨ v.val ∈ equivocators {w | w ∈ A.pool σ}) ∧
    ∃ R ∈ Φ.tree, R.root = v.head ∧ A.blockStamp R.root < ⊤

theorem heldAtProposal_iff {A : SAState sp.n} {Φ : Frm sp.n FGP} {σ : Nat} {v : Vote sp.n} :
    HeldAtProposal A Φ σ v ↔ (v ∈ A.pool σ ∨ v.val ∈ equivocators {w | w ∈ A.pool σ}) ∧
      ∃ R ∈ Φ.tree, R.root = v.head ∧ A.blockStamp R.root < ⊤ := Iff.rfl

/-- **(L-high)** Every stored lock of `A` of slot `≥ σ`, live at `t`, on a block of `U`, is
compatible with `B`. -/
def HighLocksCompatible (U : Set (Blk sp.n FGP)) (A : SAState sp.n) (t : Time) (σ : Nat)
    (B : Blk sp.n FGP) : Prop :=
  ∀ l ∈ A.locks, sp.slot t ≤ l.slot + sp.k → σ ≤ l.slot → ∀ X ∈ U, X.root = l.block →
    Compatible U X B

theorem highLocksCompatible_iff {A : SAState sp.n} {t : Time} {σ : Nat} {B : Blk sp.n FGP} :
    HighLocksCompatible U A t σ B ↔ ∀ l ∈ A.locks, sp.slot t ≤ l.slot + sp.k → σ ≤ l.slot →
      ∀ X ∈ U, X.root = l.block → Compatible U X B := Iff.rfl

/-- **(L-low)** Every stored lock of `A` of slot `< σ`, live at `t`, on a block of `U`, is
compatible with `B`. -/
def LowLocksCompatible (U : Set (Blk sp.n FGP)) (A : SAState sp.n) (t : Time) (σ : Nat)
    (B : Blk sp.n FGP) : Prop :=
  ∀ l ∈ A.locks, sp.slot t ≤ l.slot + sp.k → l.slot < σ → ∀ X ∈ U, X.root = l.block →
    Compatible U X B

theorem lowLocksCompatible_iff {A : SAState sp.n} {t : Time} {σ : Nat} {B : Blk sp.n FGP} :
    LowLocksCompatible U A t σ B ↔ ∀ l ∈ A.locks, sp.slot t ≤ l.slot + sp.k → l.slot < σ →
      ∀ X ∈ U, X.root = l.block → Compatible U X B := Iff.rfl

/-! ## The proposal's view -/

/-- `pool_stamp_lt_top` with the unlock given. -/
theorem pool_stamp_lt_topU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {v : Vote sp.n} (hv : v ∈ (tr.state y i).pool v.slot) :
    (tr.state y i).voteStamp v < ⊤ := by
  rcases pool_originU hr hy i v hv with ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
    rw [hst] <;> exact etime_of_lt_top _

/-- A vote of an honest node's pool has a finite stamp. -/
theorem pool_stamp_lt_top (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {v : Vote sp.n} (hv : v ∈ (tr.state y i).pool v.slot) :
    (tr.state y i).voteStamp v < ⊤ :=
  pool_stamp_lt_topU (hr := hr.toU) (y := y) (hy := hy) (i := i) (v := v) (hv := hv)

/-- `mem_proposalView_votes` with the unlock given. -/
theorem mem_proposalView_votesU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) (v : Vote sp.n) :
    v ∈ (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes ↔
      v ∈ (tr.state x i).pool σ := by
  change v ∈ ((tr.state x i).poolAt σ).filter _ ↔ _
  simp only [SAState.poolAt, show ¬ ((σ : Int) < 0) by omega, ite_false, Int.toNat_natCast,
    List.mem_filter, decide_eq_true_eq, and_iff_left_iff_imp]
  intro hv
  exact pool_stamp_lt_topU hr hx (state_pool_slotU sp hr hx i σ v hv ▸ hv)

/-- The proposal's view holds exactly the pool's slot-`σ` votes (their stamps are finite). -/
theorem mem_proposalView_votes (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) (v : Vote sp.n) :
    v ∈ (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes ↔
      v ∈ (tr.state x i).pool σ :=
  mem_proposalView_votesU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (Φ := Φ) (v := v)

/-- The support of a view of lists is among its votes. -/
theorem ofLists_support_subset (A : SAState sp.n) (Φ : Frm sp.n FGP) (σ : Int) (c : ETime) :
    (View.ofLists (voteViewList A Φ σ c)).support ⊆ (View.ofLists (voteViewList A Φ σ c)).votes :=
  fun _ hv => (List.mem_filter.1 hv).1

/-- `proposalView_equivocator` with the unlock given. -/
theorem proposalView_equivocatorU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n}
    (h : w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes) :
    w ∈ equivocators {v | v ∈ (tr.state x i).pool σ} :=
  equivocators_mono (fun v hv => (mem_proposalView_votesU hr hx i σ Φ v).1 hv) h

/-- An equivocator of the proposal's view equivocates in the pool. -/
theorem proposalView_equivocator (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n}
    (h : w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes) :
    w ∈ equivocators {v | v ∈ (tr.state x i).pool σ} :=
  proposalView_equivocatorU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (Φ := Φ) (w := w)
      (h := h)

/-- `honest_pool_not_equivocator` with the unlock given. -/
theorem honest_pool_not_equivocatorU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators {v | v ∈ (tr.state x i).pool σ} := by
  rintro ⟨a, ha, b, hb, hab, rfl, hbw⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hrun.honest.pool_vote x hx i σ _ ha hw
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hrun.honest.pool_vote x hx i σ _ hb (hbw ▸ hw)
  have has := state_pool_slotU sp hrun.localRun hx i σ _ ha
  have hbs := state_pool_slotU sp hrun.localRun hx i σ _ hb
  rw [hbw] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hrun.localRun _ hw ja jb ea eb hva hvb
    (has.trans hbs.symm)
  exact hab rfl

/-- An honest validator does not equivocate in an honest node's pool. -/
theorem honest_pool_not_equivocator (hrun : ACRun proposer tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators {v | v ∈ (tr.state x i).pool σ} :=
  honest_pool_not_equivocatorU (hrun := hrun.toU) (x := x) (hx := hx) (i := i) (σ := σ) (w := w)
      (hw := hw)

/-- `honest_not_equivocator_proposal` with the unlock given. -/
theorem honest_not_equivocator_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes := fun h =>
  honest_pool_not_equivocatorU hrun hx i σ hw (proposalView_equivocatorU hrun.localRun hx i σ Φ h)

/-- An honest validator does not equivocate in the view of an honest proposal. -/
theorem honest_not_equivocator_proposal (hrun : ACRun proposer tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes :=
  honest_not_equivocator_proposalU (hrun := hrun.toU) (x := x) (hx := hx) (i := i) (σ := σ)
      (Φ := Φ) (w := w) (hw := hw)

/-- `proposal_supporter` with the unlock given. -/
theorem proposal_supporterU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {v : Vote sp.n} (hvs : v.slot = σ) (hv : v ∈ (tr.state x i).pool σ) {C R : Blk sp.n FGP}
    (hR : R ∈ ℓ.frame.tree) (hRr : R.root = v.head) (hRs : R.slot ≤ σ)
    (hCR : ℓ.frame.Anc C R) (hbs : (tr.state x i).blockStamp R.root < ⊤)
    (hneq : v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes) :
    v.val ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ C := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
  have hvst := pool_stamp_lt_topU hr hx (hvs ▸ hv)
  have hres : resolutionTime (tr.state x i) ℓ.frame v < ⊤ := by
    unfold resolutionTime
    rw [← hRr, SA.lookup_of_mem hΦ hR]
    simp only [show ¬ v.slot < R.slot by omega, ite_false]
    exact max_lt hvst hbs
  have hpool : v ∈ (tr.state x i).poolAt (σ : Int) := by simpa [SAState.poolAt] using hv
  refine ⟨hneq, v, ?_, rfl, by simp [hvs], R, hR, hRr, hCR⟩
  exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hpool, by simpa using hvst⟩, by simpa using hres⟩

/-- **A held vote supports at the proposal.** A slot-`σ` vote that the proposer holds, with a
head (of slot at most `σ`) in its tree with a finite stamp, is counted as support for every
ancestor `C` of its head in the proposal's view, unless its validator equivocates there. -/
theorem proposal_supporter (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {v : Vote sp.n} (hvs : v.slot = σ) (hv : v ∈ (tr.state x i).pool σ) {C R : Blk sp.n FGP}
    (hR : R ∈ ℓ.frame.tree) (hRr : R.root = v.head) (hRs : R.slot ≤ σ)
    (hCR : ℓ.frame.Anc C R) (hbs : (tr.state x i).blockStamp R.root < ⊤)
    (hneq : v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes) :
    v.val ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ C :=
  proposal_supporterU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (ℓ := ℓ) (hc := hc)
      (v := v) (hvs := hvs) (hv := hv) (C := C) (R := R) (hR := hR) (hRr := hRr) (hRs := hRs)
          (hCR := hCR) (hbs := hbs) (hneq := hneq)

/-! ## The walk of a proposal -/

/-- `proposal_walk` with the unlock given. -/
theorem proposal_walkU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    {B : Blk sp.n FGP}
    (hV : B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot)
    (hlocks : ∀ C ∈ liveLockBlocks sp L ℓ.frame (tr.time i),
      Compatible U C B)
    (hbest : ∀ X Cx : Blk sp.n FGP, Cx ∈ ℓ.frame.viableTree ℓ.frame.tree →
      Cx.parent = some X.root → ℓ.frame.Anc Cx B →
      IsBest sp (goldfishScore sp ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
        σ)
        {B' | B' ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ B'.parent = some X.root ∧
          goldfishEligible sp ℓ.frame (tr.time i)
            (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B'} Cx) :
    Anc U B d.head := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  obtain ⟨-, hd⟩ := acProposal_headWith hprop
  rw [hslot, show ((σ + 1 : Nat) : Int) - 1 = σ by push_cast; ring] at hd
  rw [hd]
  exact Anc.mono hΦU (anc_getHead hr.coherent hΦ hΦU _ _ _ _ subset_rfl
    (fun _ hB' X hX => mem_of_anc hX hB') hV hlocks hbest)

/-- **The proposal's walk** (`anc_getHead` at the proposal): the head of an honest
`ac_proposal` of slot `σ + 1` extends a block `B` of its tree that is viable or at or below
`fc_root` (V), when every live lock after the unlocking is compatible with `B` and every child
toward `B` is the best. -/
theorem proposal_walk (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    {B : Blk sp.n FGP}
    (hV : B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot)
    (hlocks : ∀ C ∈ liveLockBlocks sp (unlock sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))) ℓ.frame (tr.time i),
      Compatible U C B)
    (hbest : ∀ X Cx : Blk sp.n FGP, Cx ∈ ℓ.frame.viableTree ℓ.frame.tree →
      Cx.parent = some X.root → ℓ.frame.Anc Cx B →
      IsBest sp (goldfishScore sp ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
        σ)
        {B' | B' ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ B'.parent = some X.root ∧
          goldfishEligible sp ℓ.frame (tr.time i)
            (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B'} Cx) :
    Anc U B d.head :=
  proposal_walkU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (ℓ := ℓ) (hc := hc)
      (hslot := hslot) (d := d) (pay := pay)
          (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (B := B) (hV := hV)
          (hlocks := hlocks) (hbest := hbest)

/-! ## The locks at a proposal -/

/-- `optimisticLock_compatible` with the unlock given. -/
theorem optimisticLock_compatibleU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {z : Fin sp.n} (hz : z ∈ H) {k s : Nat} {O : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr z k s O CV) {B : Blk sp.n FGP}
    (hB : ∀ w ∈ H, ∀ j e, VoteAt tr w j e → e.msg.slot = s → VoteExtends U e.msg B) :
    Compatible U O B := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hopt
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hz hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34
  refine origin_compatible hr.coherent hΦU h34 hf fun v hv hvH => ?_
  obtain ⟨hvs, j, -, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hz hpt hv hvH
  exact hB _ hvH j e hve hvs

/-- An honest optimistic lock is compatible with `B` when every honest vote of its slot extends
`B` (`f < n/2`). -/
theorem optimisticLock_compatible (hrun : ACRun proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {z : Fin sp.n} (hz : z ∈ H) {k s : Nat} {O : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr z k s O CV) {B : Blk sp.n FGP}
    (hB : ∀ w ∈ H, ∀ j e, VoteAt tr w j e → e.msg.slot = s → VoteExtends U e.msg B) :
    Compatible U O B :=
  optimisticLock_compatibleU (hrun := hrun.toU) (hf := hf) (z := z) (hz := hz) (k := k) (s := s)
      (O := O) (CV := CV) (hopt := hopt) (B := B) (hB := hB)

/-- `proposal_high_lock` with the unlock given. -/
theorem proposal_high_lockU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlσ : σ ≤ l.slot) {X : Blk sp.n FGP} (hX : X ∈ U)
    (hXr : X.root = l.block) : ∃ O, Anc U X O ∧ ∃ k CV, OptimisticLockAt tr x k l.slot O CV := by
  obtain ⟨L, hL, hLr, O, hLO, k, hk, CV, hO⟩ := lock_below_originU hr hx i l hl
  obtain rfl : X = L := hr.coherent.1 hX hL (hXr.trans hLr.symm)
  refine ⟨O, hLO, k, CV, hO.resolve_left ?_⟩
  rintro ⟨ℓ', ⟨-, -, htk, -⟩, -⟩
  have hΔ := sp.toParams.hΔ
  have h1 := hr.time_mono hk.le
  have h2 : sp.ts σ ≤ sp.ts l.slot := (ts_le_iff sp).2 (by exact_mod_cast hlσ)
  have h3 : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rw [htk, ht, h3] at h1
  linarith

/-- At a proposal of slot `σ + 1` (at `t_{σ+1}`), a stored lock of slot `≥ σ` sits below an
optimistic lock of its slot: no update of such a slot has happened yet. -/
theorem proposal_high_lock (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlσ : σ ≤ l.slot) {X : Blk sp.n FGP} (hX : X ∈ U)
    (hXr : X.root = l.block) : ∃ O, Anc U X O ∧ ∃ k CV, OptimisticLockAt tr x k l.slot O CV :=
  proposal_high_lockU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (ht := ht) (l := l)
      (hl := hl) (hlσ := hlσ) (X := X) (hX := hX) (hXr := hXr)

/-- The time and the slot of an honest proposal of slot `σ + 1`. -/
theorem proposal_slot {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) :
    sp.slot (tr.time i) = σ + 1 := by
  have hΔ := sp.toParams.hΔ
  rw [ht]
  exact slot_of_mem sp (σ + 1) le_rfl (by simp only [SAParams.ts]; push_cast; linarith)

/-- `proposal_locks` with the unlock given. -/
private theorem proposal_locksU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {B : Blk sp.n FGP} {L : Set Lock} (hB : B ∈ ℓ.frame.tree)
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S,
        w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∨
          w ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B) ∧
        sp.n ≤ 2 * S.ncard) ∨ LowLocksCompatible U (tr.state x i) (tr.time i) σ B)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    ∀ C ∈ liveLockBlocks sp L ℓ.frame (tr.time i),
      Compatible U C B := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  refine unlocked_compatibleRel hr.coherent hΦ hΦU hB ?_
    (fun l hl hlive hlσ X hX hXr => hhigh l hl hlive (by exact_mod_cast hlσ) X hX hXr)
    (locksWF_stateU hr hx i) hL
  rcases hlow with ⟨S, hS, hn⟩ | hlow
  · refine Or.inl ⟨S, fun w hw => ?_, hn⟩
    rcases hS w hw with h | ⟨-, v, hv, hvw, hvs, hva⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · exact Or.inr fun l hl hlive hlσ X hX hXr => hlow l hl hlive (by exact_mod_cast hlσ) X hX hXr

/-- The unlocked locks of an honest proposal of slot `σ + 1` are compatible with `B ∈ Φ.tree`,
from (L-high) and either half of the committee supporting `B` (or equivocating) in its view, or
(L-low). -/
private theorem proposal_locks (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S,
        w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∨
          w ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B) ∧
        sp.n ≤ 2 * S.ncard) ∨ LowLocksCompatible U (tr.state x i) (tr.time i) σ B)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    ∀ C ∈ liveLockBlocks sp (unlock sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))) ℓ.frame (tr.time i),
      Compatible U C B :=
  proposal_locksU (hr := hr.toU) (x := x) (hx := hx) (i := i) (σ := σ) (ℓ := ℓ) (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hr hx hc).1 _ _ _ _)
      (B := B) (hB := hB) (hlow := hlow) (hhigh := hhigh)

/-! ## The honest batch at a proposal (A1.3) -/

/-- `batch_proposal` with the unlock given. -/
theorem batch_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n) {σ : Nat}
    {B : Blk sp.n FGP}
    (hhalf : sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = σ}.ncard)
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ →
      HeldAtProposal (tr.state x i) ℓ.frame σ e.msg)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  set V := View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)
  set SX : Set (Fin sp.n) := {w | w ∈ H ∧ ∃ j e', VoteAt tr w j e' ∧ e'.msg.slot = σ}
  -- the honest voters of slot `σ` support `B` at the proposal
  have hsupp : SX ⊆ supporters ℓ.frame V σ B := by
    rintro w ⟨hw, j, e, hv, hes⟩
    obtain ⟨ℓw, hcw, hew⟩ := id hv
    have hval : e.msg.val = w := (castAt_specU hr hw ⟨hcw, hew⟩).1
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := hP w hw j e hv hes
    have hheld : e.msg ∈ (tr.state x i).pool σ := hheld.resolve_right fun h =>
      honest_pool_not_equivocatorU hrun hx i σ hw (hval ▸ h)
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hB w hw j e hv hes
    obtain ⟨Hd', hHd', hHd'r, hHds⟩ := honest_headU hrun hw hv
    obtain rfl : Hd = R := hU.1 hHd (hΦU hR) (hHdr.trans hRr.symm)
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hHd'r.trans hHdr.symm)
    rw [← hval]
    exact proposal_supporterU hr hx hc hes hheld hR hRr (hes ▸ hHds)
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 hBHd hR) hbs
      (honest_not_equivocator_proposalU hrun hx i σ ℓ.frame (hval ▸ hw))
  -- the voters are honest slot-`σ` voters or faulty
  have hvoters : voters V.votes ⊆ SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · have hv' := (mem_proposalView_votesU hr hx i σ ℓ.frame v).1 hv
      obtain ⟨j, -, e, hve, he⟩ := hrun.honest.pool_vote x hx i σ v hv' hw
      exact Or.inl ⟨hw, j, e, hve, by rw [he]; exact state_pool_slotU sp hr hx i σ v hv'⟩
    · exact Or.inr hw
  have h3 : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    omega
  exact proposal_walkU hr hx hc hslot hprop hV.2
    (proposal_locksU hr hx hc hV.1 hL (Or.inl ⟨SX, fun w hw => Or.inr (hsupp hw), hhalf⟩) hhigh)
    fun X Cx hCx hp hCxB => isBest_of_majority hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hsupp hvoters h3 hCx hp hCxB

/-- **The honest batch at a proposal** (A1.3 at the proposal duty: thereafter the honest
batch releases older conflicting locks): when the honest voters of slot `σ` are half of the
committee and every honest slot-`σ` vote extends `B` and reaches the proposer (P), the head of an
honest proposal of slot `σ + 1` extends `B`, under (V) and (L-high). -/
theorem batch_proposal (hrun : ACRun proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n) {σ : Nat}
    {B : Blk sp.n FGP}
    (hhalf : sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = σ}.ncard)
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ →
      HeldAtProposal (tr.state x i) ℓ.frame σ e.msg)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head :=
  batch_proposalU (hrun := hrun.toU) (hf := hf) (σ := σ) (B := B) (hhalf := hhalf) (hB := hB)
      (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _) (hslot := hslot)
          (d := d) (pay := pay)
          (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (hV := hV)
              (hP := hP) (hhigh := hhigh)

/-! ## The writer's update at the proposal -/

/-- `pool_sent` with the unlock given. -/
theorem pool_sentU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {z : Fin sp.n} (hz : z ∈ H)
    {c σ : Nat} (hrs : ∀ k < c, tr.RestartAt z k → tr.time k < sp.ts σ) {v : Vote sp.n}
    (hv : v ∈ (tr.state z c).pool σ) :
    ∃ k < c, tr.SendOrAdmit z k v ∧ sp.ts σ ≤ tr.time k ∧
      (tr.state z c).voteStamp v = ETime.of (tr.time k) := by
  have hvs := state_pool_slotU sp hr hz c σ v hv
  rcases pool_originU hr hz c v (hvs ▸ hv) with
    ⟨k, hk, hsend, hst, hsl⟩ | ⟨k, hk, ℓk, hck, hrk, -, B, hB, hvB⟩
  · exact ⟨k, hk, hsend,
      (ts_le_iff_le_slot sp (hr.time_nonneg k) σ).2 (by rw [← hvs]; exact_mod_cast hsl), hst⟩
  · exfalso
    have hBv := (frame_validPayloadU sp hr hz hck B hB).1 v hvB
    have hBs := frame_slot_leU sp hr hz hck B hB
    have htk := hrs k hk ⟨ℓk, hck, hrk⟩
    have : ¬ (σ : Int) ≤ sp.slot (tr.time k) := fun h => by
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
      linarith
    omega

/-- A slot-`σ` vote of an honest node's pool, whose restarts before cut `c` are before `t_σ`, was
sent or admitted by the node at an earlier cut, at or after `t_σ`, at its stamp (no restart
replays it). -/
theorem pool_sent (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {z : Fin sp.n} (hz : z ∈ H)
    {c σ : Nat} (hrs : ∀ k < c, tr.RestartAt z k → tr.time k < sp.ts σ) {v : Vote sp.n}
    (hv : v ∈ (tr.state z c).pool σ) :
    ∃ k < c, tr.SendOrAdmit z k v ∧ sp.ts σ ≤ tr.time k ∧
      (tr.state z c).voteStamp v = ETime.of (tr.time k) :=
  pool_sentU (hr := hr.toU) (z := z) (hz := hz) (c := c) (σ := σ) (hrs := hrs) (v := v) (hv := hv)

/-- `writer_pool_proposal` with the unlock given. -/
theorem writer_pool_proposalU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ σ ℓX) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    (ht : tr.time i = sp.ts (σ + 1 : Nat))
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts σ) (sp.ts σ + 4 * sp.Δ) tr)
    (hrsX : ∀ k ≤ i₀, tr.RestartAt X k → tr.time k ≤ sp.ts σ)
    (hrsx : ∀ k < i, tr.RestartAt x k → tr.time k < sp.ts σ) :
    ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ} := by
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (σ + 2 : Nat) = sp.ts σ + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro v hv
  have hvs := state_pool_slotU sp hr hx i σ v hv
  obtain ⟨k, hk, hsend, h1, -⟩ := pool_sentU hr hx hrsx hv
  have hki : tr.time k ≤ sp.ts σ + 4 * sp.Δ := by rw [← hts, ← ht]; exact hr.time_mono hk.le
  have := sync_forwardU hr hsync hx hsend h1 hki hX hupd.1
    (fun k' hk' hrk => (hrsX k' hk' hrk).trans h1)
    (by rw [hupd.2.2.1]; linarith) fun t ht₁ ht₂ => by
      have ht0 : 0 ≤ t := (hr.time_nonneg k).trans ht₁
      have ha := (ts_le_iff_le_slot sp ht0 σ).1 (h1.trans ht₁)
      have hb : ¬ ((σ + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
        have := (ts_le_iff_le_slot sp ht0 _).2 h
        rw [hts₂] at this; linarith
      rw [hvs]; omega
  rwa [hvs] at this

/-- **The writer's pool covers the proposer's** (W): under `Sync[t_σ, t_σ + 4Δ]`, with the
writer's restarts up to its update at or before `t_σ` and the proposer's before its proposal
before `t_σ`, a slot-`σ` vote that an honest proposer of slot `σ + 1` holds is held by an honest
node at its update of slot `σ`, or that node holds two votes of its validator. -/
theorem writer_pool_proposal (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ σ ℓX) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    (ht : tr.time i = sp.ts (σ + 1 : Nat))
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts σ) (sp.ts σ + 4 * sp.Δ) tr)
    (hrsX : ∀ k ≤ i₀, tr.RestartAt X k → tr.time k ≤ sp.ts σ)
    (hrsx : ∀ k < i, tr.RestartAt x k → tr.time k < sp.ts σ) :
    ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ} :=
  writer_pool_proposalU (hr := hr.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (ℓX := ℓX)
      (hupd := hupd) (x := x) (hx := hx) (i := i) (ht := ht) (hsync := hsync) (hrsX := hrsX)
          (hrsx := hrsx)

/-- `counted_held` with the unlock given. -/
private theorem counted_heldU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hcX : tr.CallAt X i₀ ℓX)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) {E : Blk sp.n FGP} {v : Vote sp.n}
    (hv : v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E)
    (hP : HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    v.slot = σ ∧ v ∈ (tr.state x i).pool σ ∧
      v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∧
      ∃ R ∈ ℓ.frame.tree, R.root = v.head ∧ R.slot ≤ σ ∧ Anc U E R ∧
        (tr.state x i).blockStamp R.root < ⊤ := by
  have hU := hr.coherent
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAtU hr hX hcX
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hc
  obtain ⟨hvp, hneqX, hres, R', hR', hR'r, hER'⟩ := hv
  have hvs := state_pool_slotU sp hr hX i₀ σ v hvp
  have hR's : ¬ v.slot < R'.slot := by
    intro hlt
    unfold resolutionTime at hres
    rw [← hR'r, SA.lookup_of_mem hΦX hR'] at hres
    dsimp only at hres
    split_ifs at hres
    exact absurd hres (not_lt.2 le_top)
  obtain ⟨hheld, R, hR, hRr, hbs⟩ := hP
  obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
  have hnoeq : v.val ∉ equivocators {w | w ∈ (tr.state x i).pool σ} := by
    rintro ⟨a, ha, b, hb, hab, haw, hbw⟩
    apply hneqX
    rcases hW a ha with ha' | ⟨a', ha', b', hb', hab', ha'w, hb'w⟩
    · rcases hW b hb with hb' | ⟨a', ha', b', hb', hab', ha'w, hb'w⟩
      · exact ⟨a, ha', b, hb', hab, haw, hbw⟩
      · exact ⟨a', ha', b', hb', hab', ha'w.trans hbw, hb'w.trans hbw⟩
    · exact ⟨a', ha', b', hb', hab', ha'w.trans haw, hb'w.trans haw⟩
  exact ⟨hvs, hheld.resolve_right hnoeq, fun h => hnoeq (proposalView_equivocatorU hr hx i σ _ h),
    R, hR, hRr, by omega, Anc.mono hΦXU hER', hbs⟩

/-- A counted vote of an honest update of slot `σ` that reaches the proposer (P), under (W), is
held there without its validator equivocating in the proposal's view, and its head is a block
of `Φ.tree` extending `E`, of slot at most `σ`, with a finite stamp. -/
private theorem counted_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hcX : tr.CallAt X i₀ ℓX)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) {E : Blk sp.n FGP} {v : Vote sp.n}
    (hv : v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E)
    (hP : HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    v.slot = σ ∧ v ∈ (tr.state x i).pool σ ∧
      v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∧
      ∃ R ∈ ℓ.frame.tree, R.root = v.head ∧ R.slot ≤ σ ∧ Anc U E R ∧
        (tr.state x i).blockStamp R.root < ⊤ :=
  counted_heldU (hr := hr.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (ℓX := ℓX) (hcX := hcX)
      (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc) (E := E) (v := v) (hv := hv) (hP := hP)
          (hW := hW)

/-- `counted_supporters_proposal` with the unlock given. -/
theorem counted_supporters_proposalU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hcX : tr.CallAt X i₀ ℓX) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) {B E : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) (hBE : Anc U B E)
    (hP : ∀ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E,
      HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E, v.val = w} ⊆
      supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨hvs, hheld, hneq, R, hR, hRr, hRs, hER, hbs⟩ :=
    counted_heldU hr hX hcX hx hc hv (hP v hv) hW
  exact proposal_supporterU hr hx hc hvs hheld hR hRr hRs
    (anc_tree_of_anc_U hr.coherent hΦ hΦU hB (hBE.trans hER) hR) hbs hneq

/-- The validators that an honest update of slot `σ` counts for `E` are supporters of every
`B ⪯ E` of the tree in the view of an honest proposal of slot `σ + 1`, under (P) for the counted
votes and (W). -/
theorem counted_supporters_proposal (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hcX : tr.CallAt X i₀ ℓX) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) {B E : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) (hBE : Anc U B E)
    (hP : ∀ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E,
      HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E, v.val = w} ⊆
      supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B :=
  counted_supporters_proposalU (hr := hr.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (ℓX := ℓX)
      (hcX := hcX) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc) (B := B) (E := E) (hB := hB)
          (hBE := hBE) (hP := hP) (hW := hW)

/-- `result_best_at_proposal` with the unlock given. -/
theorem result_best_at_proposalU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr X i₀ σ C CV) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) (hBC : Anc U B C)
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    ∀ X' Cx : Blk sp.n FGP, Cx ∈ ℓ.frame.viableTree ℓ.frame.tree →
      Cx.parent = some X'.root → ℓ.frame.Anc Cx B →
      IsBest sp (goldfishScore sp ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
        σ)
        {B' | B' ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ B'.parent = some X'.root ∧
          goldfishEligible sp ℓ.frame (tr.time i)
            (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B'} Cx := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
  have hmaj := result_majority hres
  obtain ⟨ℓX, hupd, -, rfl⟩ := hres
  have hvoters : voters (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ⊆
      voters {v | v ∈ (tr.state X i₀).pool σ} := by
    rintro w ⟨v, hv, rfl⟩
    rcases hW v ((mem_proposalView_votesU hr hx i σ ℓ.frame v).1 hv) with
      h | ⟨a, ha, -, -, -, haw, -⟩
    · exact ⟨v, h, rfl⟩
    · exact ⟨a, ha, haw⟩
  exact fun X' Cx hCx hp hCxB => isBest_of_majority hΦ (ofLists_support_subset _ _ _ _)
    (fun _ h => h.1) (counted_supporters_proposalU hr hX hupd.1 hx hc hB hBC hP hW) hvoters
    hmaj hCx hp hCxB

/-- **A result's majority at the proposal** (A1.8 (b) at the proposal duty): for an honest
result `C` of slot `σ` and a block `B ⪯ C` of the tree of an honest proposal of slot `σ + 1`,
under (P) for the counted votes and (W), every child toward `B` is the best of its siblings. -/
theorem result_best_at_proposal (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr X i₀ σ C CV) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) (hBC : Anc U B C)
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ}) :
    ∀ X' Cx : Blk sp.n FGP, Cx ∈ ℓ.frame.viableTree ℓ.frame.tree →
      Cx.parent = some X'.root → ℓ.frame.Anc Cx B →
      IsBest sp (goldfishScore sp ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
        σ)
        {B' | B' ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ B'.parent = some X'.root ∧
          goldfishEligible sp ℓ.frame (tr.time i)
            (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B'} Cx :=
  result_best_at_proposalU (hr := hr.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (C := C)
      (CV := CV) (hres := hres) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc) (B := B)
          (hB := hB) (hBC := hBC) (hP := hP) (hW := hW)

/-! ## The first proposal after an origin -/

/-- `result_first_proposal` with the unlock given. -/
theorem result_first_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat}
    {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hres : ResultAt tr X i₀ σ C CV)
    (hDC : Anc U D C) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ})
    (hlow : LowLocksCompatible U (tr.state x i) (tr.time i) σ D)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head :=
  proposal_walkU hrun.localRun hx hc hslot hprop hV.2
    (proposal_locksU hrun.localRun hx hc hV.1 hL (Or.inr hlow) hhigh)
    (result_best_at_proposalU hrun.localRun hX hres hx hc hV.1 hDC hP hW)

/-- **A result transfers to the next proposal** (A1.8 for an ancestor `D ⪯ C` of an honest result
`C` of slot `σ`, at the proposal duty): under (V) for `D`, (P) for the counted votes, (W),
(L-high) and (L-low), the head of an honest proposal of slot `σ + 1` extends `D`. -/
theorem result_first_proposal (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat}
    {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hres : ResultAt tr X i₀ σ C CV)
    (hDC : Anc U D C) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ})
    (hlow : LowLocksCompatible U (tr.state x i) (tr.time i) σ D)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head :=
  result_first_proposalU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (C := C)
      (D := D) (CV := CV) (hres := hres) (hDC := hDC) (x := x) (hx := hx) (i := i) (ℓ := ℓ)
          (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _) (hslot := hslot)
          (d := d) (pay := pay)
              (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (hV := hV)
                  (hP := hP)
              (hW := hW) (hlow := hlow) (hhigh := hhigh)

/-- `update_first_proposal` with the unlock given. -/
theorem update_first_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfu : FastUpdateAt tr X i₀ σ D CV)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ})
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head := by
  have hr := hrun.localRun
  obtain ⟨ℓX, C, hupd, hconf, hfs, rfl⟩ := hfu
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAtU hr hX hupd.1
  obtain ⟨⟨-, -, hDC⟩, -, hfast⟩ := (deepest_mem hfs).1
  have hDC' : Anc U D C := Anc.mono hΦXU hDC
  -- the votes counted for `C` are counted for `D`
  have hCD : fastCounted sp (tr.state X i₀) ℓX.frame σ C ⊆
      fastCounted sp (tr.state X i₀) ℓX.frame σ D := by
    rintro v ⟨hv, hneq, hres, R, hR, hRr, hCR⟩
    exact ⟨hv, hneq, hres, R, hR, hRr, hDC.trans hCR⟩
  set SX := {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ D, v.val = w}
  have hhalf : sp.n ≤ 2 * SX.ncard := by
    refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨hw, v, ⟨hv, hres⟩, hval, -, hanc⟩
    exact ⟨v, ⟨hv, hval ▸ hw, hres, hanc⟩, hval⟩
  have hsupp := counted_supporters_proposalU hr hX hupd.1 hx hc hV.1
    (Relation.ReflTransGen.refl (a := D)) hP hW
  exact proposal_walkU hr hx hc hslot hprop hV.2
    (proposal_locksU hr hx hc hV.1 hL (Or.inl ⟨SX, fun w hw => Or.inr (hsupp hw), hhalf⟩) hhigh)
    (result_best_at_proposalU hr hX ⟨ℓX, hupd, hconf, rfl⟩ hx hc hV.1 hDC'
      (fun v hv => hP v (hCD hv)) hW)

/-- **A fast update transfers to the next proposal** (A1.2 at the proposal duty): for an honest
fast lock of slot `σ` on `D` written by the fast test of an update, under (V) for `D`, (P) for
the votes counted for `D`, (W) and (L-high), the head of an honest proposal of slot `σ + 1`
extends `D`: the counted validators of `D` are half of the committee and support `D` (they
release the older locks), and the result's majority leads the walk to `D`. -/
theorem update_first_proposal (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfu : FastUpdateAt tr X i₀ σ D CV)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hW : ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ})
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head :=
  update_first_proposalU (hrun := hrun.toU) (X := X) (hX := hX) (i₀ := i₀) (σ := σ) (D := D)
      (CV := CV) (hfu := hfu) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _) (hslot := hslot)
          (d := d) (pay := pay)
              (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (hV := hV)
                  (hP := hP) (hW := hW) (hhigh := hhigh)

/-- `optimistic_first_proposal_stored` with the unlock given. -/
theorem optimistic_first_proposal_storedU
    {uL : Nat → Set Lock} (hrun : ACRunU wm uL proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) {B : Blk sp.n FGP} (hBD : Anc U B D)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  obtain ⟨ℓX, A, hpt, hslX, hsel, rfl⟩ := id hopt
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAtU hr hX hpt.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  obtain ⟨-, h34, -⟩ := (deepest_mem hsel').1
  rw [hslX] at h34
  set V := View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤) with hV'
  set SX := optimisticVoters sp A ℓX.frame σ D
  -- every optimistic voter supports `D` at the proposal, or equivocates there
  have hcover : SX ⊆ supporters ℓ.frame V σ B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R', hR', hR'r, hDR'⟩
    have hvs := optimisticPoint_pool_slotU hr hX hpt hv
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := hP v ⟨hv, R', hR', hR'r, hDR'⟩
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
    have hheld : v ∈ (tr.state x i).pool σ := hheld.resolve_right fun h =>
      heq (equivocators_mono (fun u hu => (mem_proposalView_votesU hr hx i σ ℓ.frame u).2 hu) h)
    have hRs : R.slot ≤ σ := by
      have := frame_slot_leU sp hr hX hpt.1 R hR'
      omega
    exact proposal_supporterU hr hx hc hvs hheld hR hRr hRs
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 (hBD.trans (Anc.mono hΦXU hDR')) hR) hbs heq
  -- counting: the equivocators are faulty, the other voters are outside `SX`
  have hE : (equivocators V.votes).ncard ≤ Hᶜ.ncard := Set.ncard_le_ncard fun w hw =>
    fun hwH => honest_not_equivocator_proposalU hrun hx i σ ℓ.frame hwH hw
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ ((voters V.votes \ SX) ∪ SX))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_union_eq Set.disjoint_sdiff_left] at this
    exact this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  exact proposal_walkU hr hx hc hslot hprop hV.2
    (proposal_locksU hr hx hc hV.1 hL (Or.inl ⟨SX, fun w hw => (hcover hw).symm, by omega⟩) hhigh)
    fun X' Cx hCx hp hCxD => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover h3 hCx hp hCxD

/-- Optimistic proposal transfer for an ancestor B of the selected block D. -/
theorem optimistic_first_proposal_stored (hrun : ACRun proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) {B : Blk sp.n FGP} (hBD : Anc U B D)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head :=
  optimistic_first_proposal_storedU (hrun := hrun.toU) (hf := hf) (X := X) (hX := hX) (i₀ := i₀)
      (σ := σ) (D := D) (CV := CV) (hopt := hopt) (B := B) (hBD := hBD) (x := x) (hx := hx)
          (i := i) (ℓ := ℓ) (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _) (hslot := hslot)
          (d := d) (pay := pay) (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop)
              (hV := hV) (hP := hP) (hhigh := hhigh)

/-- Two actual optimistic selections of the same slot are compatible, by honest
quorum overlap and one vote per slot. No delivery or head-viability premise is used. -/
theorem optimisticLock_pair_compatible (hrun : ACRun proposer tr H U)
    (hf : 2 * Hᶜ.ncard < sp.n)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {i j s : Nat}
    {D E : Blk sp.n FGP} {CV CW : Set (Vote sp.n)}
    (hd : OptimisticLockAt tr x i s D CV) (he : OptimisticLockAt tr y j s E CW) :
    Compatible U D E := by
  have hr := hrun.localRun
  obtain ⟨-, hnD, ellD, A, hpD, -, hvD, hhD⟩ := optimisticLockAt_spec hrun hx hd
  obtain ⟨-, hnE, ellE, A', hpE, -, hvE, hhE⟩ := optimisticLockAt_spec hrun hy he
  have hi := Set.ncard_inter_add_ncard_union (voters CV) (voters CW)
  have hu := Set.ncard_le_ncard (Set.subset_univ (voters CV ∪ voters CW))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hu
  obtain ⟨w, ⟨⟨v, hv, hvw⟩, v', hv', hv'w⟩, hw⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := voters CV ∩ voters CW) (by omega)
  have hw : w ∈ H := not_not.mp hw
  obtain ⟨a, -, ev, hev, hevv⟩ := hhD v hv (hvw ▸ hw)
  obtain ⟨b, -, ev', hev', hevv'⟩ := hhE v' hv' (hv'w ▸ hw)
  have heqv : v = v' := by
    have hvval : v.val = v'.val := hvw.trans hv'w.symm
    have heq := (one_vote_per_slot sp) FGP ro H U tr hr v.val (hvw ▸ hw)
      a b ev ev' (by simpa only [← hevv] using hev)
      (by simpa only [← hevv', hvval] using hev')
      (by rw [hevv, hevv', (hvD v hv).2.1, (hvE v' hv').2.1])
    exact hevv.symm.trans ((congrArg (fun e : Em sp FGP => e.msg) heq.2).trans hevv')
  obtain ⟨R, hR, hRr, hDR⟩ := (hvD v hv).2.2
  obtain ⟨R', hR', hR'r, hER'⟩ := (hvE v' hv').2.2
  have hDU := (frameIn_of_callAt hr hx hpD.1).2
  have hEU := (frameIn_of_callAt hr hy hpE.1).2
  obtain rfl : R' = R := hr.coherent.1 (hEU hR') (hDU hR)
    (hR'r.trans ((congrArg Vote.head heqv).symm.trans hRr.symm))
  exact anc_total hr.coherent (hDR.mono hDU) (hER'.mono hEU)

/-- `optimistic_first_proposal` with the unlock given. -/
theorem optimistic_first_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    {L : Set Lock}
    (hprop : (acProposalWith sp L (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head :=
  optimistic_first_proposal_storedU hrun hf hX hopt .refl hx hc hslot hprop hL hV hP hhigh

/-- **An optimistic confirmation transfers to the next proposal** (A1.4 (a) at the proposal
duty): its counted votes supply the whole-pool walk's cover. -/
theorem optimistic_first_proposal (hrun : ACRun proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : D ∈ ℓ.frame.tree ∧
      (D ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc D ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ D) :
    Anc U D d.head :=
  optimistic_first_proposalU (hrun := hrun.toU) (hf := hf) (X := X) (hX := hX) (i₀ := i₀) (σ := σ)
      (D := D) (CV := CV) (hopt := hopt) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _)
          (hslot := hslot) (d := d) (pay := pay)
              (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (hV := hV)
                  (hP := hP)
              (hhigh := hhigh)

end Consensus.Goldilocks.SA

end
