module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the transfer to the proposal duty over any frames

The argument at the votes applies at a proposal; here over an AC run (`ACRun`) with the frame facts
as premises, so that the settings with trivial frames and with general frames instantiate the
same arguments. An honest `ac_proposal` of slot `σ + 1` (at cut `i` of `x`, label
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
  by the update's writer, or its validator equivocates there.

Conclusion: `batch_proposal` (A1.3). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → SAState sp.n}

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

/-- `unlocked_compatible` for any locks related to the stored ones by the unlock relation. -/
theorem unlocked_compatibleRel (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {L L' : Set Lock} {t : Time}
    {σ : Int} {V : View sp.n}
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S, w ∈ equivocators V.votes ∨
        ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = σ ∧ AncR Φ B x.head) ∧
        sp.committeeSize ≤ 2 * S.ncard) ∨
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
        sp.committeeSize ≤ 2 * S.ncard) ∨
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

/-! ## The proposal's view -/

/-- A vote of an honest node's pool has a finite stamp, for any unlock. -/
theorem pool_stamp_lt_topU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {v : Vote sp.n} (hv : v ∈ (tr.state y i).pool v.slot) :
    (tr.state y i).voteStamp v < ⊤ := by
  rcases pool_originU hr hini hy i v hv with ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
    rw [hst] <;> exact etime_of_lt_top _

/-- `mem_proposalView_votes` with the unlock given. -/
theorem mem_proposalView_votesU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) (v : Vote sp.n) :
    v ∈ (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes ↔
      v ∈ (tr.state x i).pool σ := by
  change v ∈ ((tr.state x i).poolAt σ).filter _ ↔ _
  simp only [SAState.poolAt, show ¬ ((σ : Int) < 0) by omega, ite_false, Int.toNat_natCast,
    List.mem_filter, decide_eq_true_eq, and_iff_left_iff_imp]
  intro hv
  exact pool_stamp_lt_topU hr hini hx (state_pool_slotU sp hr hini hx i σ v hv ▸ hv)

/-- The proposal's view holds exactly the pool's slot-`σ` votes (their stamps are finite). -/
theorem mem_proposalView_votes (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) (v : Vote sp.n) :
    v ∈ (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes ↔
      v ∈ (tr.state x i).pool σ :=
  mem_proposalView_votesU (hr := hr.toU) (hini := hini)
    (x := x) (hx := hx) (i := i) (σ := σ) (Φ := Φ) (v := v)

/-- The support of a view of lists is among its votes. -/
theorem ofLists_support_subset (A : SAState sp.n) (Φ : Frm sp.n FGP) (σ : Int) (c : ETime) :
    (View.ofLists (voteViewList A Φ σ c)).support ⊆ (View.ofLists (voteViewList A Φ σ c)).votes :=
  fun _ hv => (List.mem_filter.1 hv).1

/-- An equivocator of the proposal's view equivocates in the pool, for any unlock. -/
theorem proposalView_equivocatorU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n}
    (h : w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes) :
    w ∈ equivocators {v | v ∈ (tr.state x i).pool σ} :=
  equivocators_mono (fun v hv => (mem_proposalView_votesU hr hini hx i σ Φ v).1 hv) h

/-- An honest validator does not equivocate in an honest node's pool (any unlock). -/
theorem honest_pool_not_equivocatorU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators {v | v ∈ (tr.state x i).pool σ} := by
  rintro ⟨a, ha, b, hb, hab, rfl, hbw⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hrun.honest.pool_vote x hx i σ _ ha hw
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hrun.honest.pool_vote x hx i σ _ hb (hbw ▸ hw)
  have has := state_pool_slotU sp hrun.localRun hrun.vstart hx i σ _ ha
  have hbs := state_pool_slotU sp hrun.localRun hrun.vstart hx i σ _ hb
  rw [hbw] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hrun.localRun _ hw ja jb ea eb hva hvb
    (has.trans hbs.symm)
  exact hab rfl

/-- `honest_not_equivocator_proposal` with the unlock given. -/
theorem honest_not_equivocator_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes := fun h =>
  honest_pool_not_equivocatorU hrun hx i σ hw (proposalView_equivocatorU hrun.localRun hrun.vstart
    hx i σ Φ h)

/-- An honest validator does not equivocate in the view of an honest proposal. -/
theorem honest_not_equivocator_proposal (hrun : ACRun proposer tr H U ini) {x : Fin sp.n}
    (hx : x ∈ H)
    (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes :=
  honest_not_equivocator_proposalU (hrun := hrun.toU) (x := x) (hx := hx) (i := i) (σ := σ)
      (Φ := Φ) (w := w) (hw := hw)

/-- `proposal_supporter` with the unlock given. -/
theorem proposal_supporterU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {v : Vote sp.n} (hvs : v.slot = σ) (hv : v ∈ (tr.state x i).pool σ) {C R : Blk sp.n FGP}
    (hR : R ∈ ℓ.frame.tree) (hRr : R.root = v.head) (hRs : R.slot ≤ σ)
    (hCR : ℓ.frame.Anc C R) (hbs : (tr.state x i).blockStamp R.root < ⊤)
    (hneq : v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes) :
    v.val ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ C := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
  have hvst := pool_stamp_lt_topU hr hini hx (hvs ▸ hv)
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
theorem proposal_supporter (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {v : Vote sp.n} (hvs : v.slot = σ) (hv : v ∈ (tr.state x i).pool σ) {C R : Blk sp.n FGP}
    (hR : R ∈ ℓ.frame.tree) (hRr : R.root = v.head) (hRs : R.slot ≤ σ)
    (hCR : ℓ.frame.Anc C R) (hbs : (tr.state x i).blockStamp R.root < ⊤)
    (hneq : v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes) :
    v.val ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ C :=
  proposal_supporterU (hr := hr.toU) (hini := hini)
    (x := x) (hx := hx) (i := i) (σ := σ) (ℓ := ℓ) (hc := hc)
      (v := v) (hvs := hvs) (hv := hv) (C := C) (R := R) (hR := hR) (hRr := hRr) (hRs := hRs)
          (hCR := hCR) (hbs := hbs) (hneq := hneq)

/-! ## The walk of a proposal -/

/-- `proposal_walk` with the unlock given. -/
theorem proposal_walkU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
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
theorem proposal_walk (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {x : Fin sp.n}
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
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) (K : CommitteeDict sp.n)
    (hPK : CommitteeP K tr H) {z : Fin sp.n} (hz : z ∈ H) {k s : Nat} {O : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hopt : OptimisticLockAt tr z k s O CV)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) {B : Blk sp.n FGP}
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
  refine origin_compatible hr.coherent hΦU K h34
    (fun _ ⟨v, hv, hvx, _⟩ => hvx ▸ hPK.2 z hz k ℓ A hpt s v hv) hf fun v hv hvH => ?_
  obtain ⟨hvs, j, -, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hz hpt hv hvH
  exact hB _ hvH j e hve hvs

/-- An honest optimistic lock is compatible with `B` when every honest vote of its slot extends
`B`, for slot committees `K` whose members hold the counted pools (P) and fewer than half of
whose slot-`s` members are faulty. -/
theorem optimisticLock_compatible (hrun : ACRun proposer tr H U ini) (K : CommitteeDict sp.n)
    (hPK : CommitteeP K tr H) {z : Fin sp.n} (hz : z ∈ H) {k s : Nat} {O : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hopt : OptimisticLockAt tr z k s O CV)
    (hf : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) {B : Blk sp.n FGP}
    (hB : ∀ w ∈ H, ∀ j e, VoteAt tr w j e → e.msg.slot = s → VoteExtends U e.msg B) :
    Compatible U O B :=
  optimisticLock_compatibleU (hrun := hrun.toU) K hPK hz hopt hf hB

/-- `proposal_high_lock` with the unlock given. -/
theorem proposal_high_lockU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlσ : σ ≤ l.slot) {X : Blk sp.n FGP} (hX : X ∈ U)
    (hXr : X.root = l.block) : ∃ O, Anc U X O ∧ ∃ k CV, OptimisticLockAt tr x k l.slot O CV := by
  obtain ⟨L, hL, hLr, O, hLO, k, hk, CV, hO⟩ := lock_below_originU hr
    hini hx i l hl
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
theorem proposal_high_lock (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlσ : σ ≤ l.slot) {X : Blk sp.n FGP} (hX : X ∈ U)
    (hXr : X.root = l.block) : ∃ O, Anc U X O ∧ ∃ k CV, OptimisticLockAt tr x k l.slot O CV :=
  proposal_high_lockU (hr := hr.toU) (hini := hini)
    (x := x) (hx := hx) (i := i) (σ := σ) (ht := ht) (l := l)
      (hl := hl) (hlσ := hlσ) (X := X) (hX := hX) (hXr := hXr)

/-- The time and the slot of an honest proposal of slot `σ + 1`. -/
theorem proposal_slot {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) :
    sp.slot (tr.time i) = σ + 1 := by
  have hΔ := sp.toParams.hΔ
  rw [ht]
  exact slot_of_mem sp (σ + 1) le_rfl (by simp only [SAParams.ts]; push_cast; linarith)

/-- The unlocked locks of an honest proposal of slot `σ + 1` are compatible with `B ∈ Φ.tree`,
from (L-high) and either half of the committee supporting `B` (or equivocating) in its view, or
(L-low), for any unlock.
Kept for a downstream consumer. -/
theorem proposal_locksU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    {B : Blk sp.n FGP} {L : Set Lock} (hB : B ∈ ℓ.frame.tree)
    (hL : UnlockRel sp (tr.state x i).locks ℓ.frame (tr.time i) σ
      (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) L)
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S,
        w ∈ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∨
          w ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B) ∧
        sp.committeeSize ≤ 2 * S.ncard) ∨ LowLocksCompatible U (tr.state x i) (tr.time i) σ B)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    ∀ C ∈ liveLockBlocks sp L ℓ.frame (tr.time i),
      Compatible U C B := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  refine unlocked_compatibleRel hr.coherent hΦ hΦU hB ?_
    (fun l hl hlive hlσ X hX hXr => hhigh l hl hlive (by exact_mod_cast hlσ) X hX hXr)
    (locksWF_stateU hr hini hx i) hL
  rcases hlow with ⟨S, hS, hn⟩ | hlow
  · refine Or.inl ⟨S, fun w hw => ?_, hn⟩
    rcases hS w hw with h | ⟨-, v, hv, hvw, hvs, hva⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · exact Or.inr fun l hl hlive hlσ X hX hXr => hlow l hl hlive (by exact_mod_cast hlσ) X hX hXr

/-! ## The honest batch at a proposal (A1.3) -/

/-- `batch_proposal` with the unlock given. -/
theorem batch_proposalU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) {K : CommitteeDict sp.n}
    {σ : Nat} (hf : 2 * (K.committee σ ∩ Hᶜ).ncard < sp.committeeSize)
    {B : Blk sp.n FGP}
    (hhalf : sp.committeeSize ≤
      2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = σ}.ncard)
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hK : ∀ v ∈ (tr.state x i).pool σ, v.val ∈ K.committee σ)
    (hslot : sp.slot (tr.time i) = σ + 1)
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
    exact proposal_supporterU hr hrun.vstart hx hc hes hheld hR hRr (hes ▸ hHds)
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 hBHd hR) hbs
      (honest_not_equivocator_proposalU hrun hx i σ ℓ.frame (hval ▸ hw))
  -- the voters are honest slot-`σ` voters or faulty members of the slot-`σ` committee
  have hvoters : voters V.votes ⊆ SX ∪ (K.committee σ ∩ Hᶜ) := by
    rintro w ⟨v, hv, rfl⟩
    have hv' := (mem_proposalView_votesU hr hrun.vstart hx i σ ℓ.frame v).1 hv
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e, hve, he⟩ := hrun.honest.pool_vote x hx i σ v hv' hw
      have hvs := state_pool_slotU sp hr hrun.vstart hx i σ v hv'
      exact Or.inl ⟨hw, j, e, hve, by rw [he]; exact hvs⟩
    · exact Or.inr ⟨hK v hv', hw⟩
  have h3 : (SX ∪ (K.committee σ ∩ Hᶜ)).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX (K.committee σ ∩ Hᶜ)
    omega
  exact proposal_walkU hr hx hc hslot hprop hV.2
    (proposal_locksU hr hrun.vstart hx hc hV.1 hL (Or.inl ⟨SX, fun w hw => Or.inr (hsupp hw),
      hhalf⟩) hhigh)
    fun X Cx hCx hp hCxB => isBest_of_majority hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hsupp hvoters h3 hCx hp hCxB

/-- **The honest batch at a proposal** (A1.3 at the proposal duty: thereafter the honest
batch releases older conflicting locks): when the honest voters of slot `σ` are half of the
committee and every honest slot-`σ` vote extends `B` and reaches the proposer (P), the head of an
honest proposal of slot `σ + 1` extends `B`, under (V) and (L-high). The proposer's slot-`σ` pool
holds only votes of the slot-`σ` committee, fewer than half of which is faulty. -/
theorem batch_proposal (hrun : ACRun proposer tr H U ini) {K : CommitteeDict sp.n} {σ : Nat}
    (hf : 2 * (K.committee σ ∩ Hᶜ).ncard < sp.committeeSize)
    {B : Blk sp.n FGP}
    (hhalf : sp.committeeSize ≤
      2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = σ}.ncard)
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x i ℓ) (hK : ∀ v ∈ (tr.state x i).pool σ, v.val ∈ K.committee σ)
    (hslot : sp.slot (tr.time i) = σ + 1)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ →
      HeldAtProposal (tr.state x i) ℓ.frame σ e.msg)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B) :
    Anc U B d.head :=
  batch_proposalU (hrun := hrun.toU) (hf := hf) (σ := σ) (B := B) (hhalf := hhalf) (hB := hB)
      (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc) (hK := hK)
      (hL := unlockRel_unlock (frameIn_of_callAt hrun.localRun hx hc).1 _ _ _ _) (hslot := hslot)
          (d := d) (pay := pay)
          (hprop := by rwa [acProposal_eq_acProposalWith_slot hslot] at hprop) (hV := hV)
              (hP := hP) (hhigh := hhigh)

/-! ## The writer's update at the proposal -/

/-! ## The first proposal after an origin -/

end Consensus.Goldilocks.SA

end
