module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # Goldilocks Healing: a good origin transfers to the proposal duty (T1 §3–§4)

"The same argument applies at a proposal" (healing-simple `t1-proof.md` §3). Over a
`StandaloneRun`, an honest `ac_proposal` of slot `σ + 1` at `t_{σ+1}` walks the full viable tree
with the slot-`σ` votes it holds (`vote_view(𝒜, Φ, σ, ⊤)`), from the anchor of its locks after
unlocking against that view. Its head extends a block `B` when

* `B` is in its tree (accepted by relay before `t_σ + 3Δ`),
* every live lock after the unlocking is compatible with `B`, and
* the children toward `B` are the best (a strict majority of the voters, or a cover).

The three first-duty arguments mirror A1.2 (a fast update), A1.4 (a) (an optimistic
confirmation) and A1.8 (a slow origin's result) at the proposal; later duties are the honest
batch (A1.3). `proposals_extend_of_origin` assembles them for H.1's `origin_transfer_proposals`,
given that the votes after the origin extend `B`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}

/-! ## The proposal duty -/

/-- An `ac_proposal` that returns a duty head is joined, and its head is the walk of the full
viable tree with the held votes of the previous slot, from the anchor of the unlocked locks. -/
theorem acProposal_head {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposal sp A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ d.head = getHead sp
      { A with locks := (unlock sp A.locks Φ t ((sp.slot t : Int) - 1)
          (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))) } Φ t
      (Φ.viableTree Φ.tree) (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) := by
  unfold acProposal at h
  split_ifs at h with hj
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hj, by rw [← h.1]⟩

/-- **Unlocking keeps compatibility.** Every live lock block after `unlock` against `V` at slot
`σ` is compatible with `B ∈ Φ.tree` when every stored live lock of slot `≥ σ` is, and either
half of the committee support `B` or equivocate in `V` (the unlocking moves the older locks to
compatible ancestors), or every stored live lock of slot `< σ` is compatible with `B` too. -/
theorem unlocked_compatible (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {L : Set Lock} {t : Time} {σ : Int}
    {V : View sp.n}
    (hlow : (∃ S : Set (Fin sp.n), (∀ w ∈ S, w ∈ equivocators V.votes ∨
        ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = σ ∧ AncR Φ B x.head) ∧
        sp.n ≤ 2 * S.ncard) ∨
      ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → (l.slot : Int) < σ → ∀ X ∈ U, X.root = l.block →
        Compatible U X B)
    (hhigh : ∀ l ∈ L, sp.slot t ≤ l.slot + sp.k → σ ≤ (l.slot : Int) → ∀ X ∈ U,
      X.root = l.block → Compatible U X B) :
    ∀ C ∈ liveLockBlocks sp (unlock sp L Φ t σ V) Φ t, Compatible U C B := by
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  rintro C ⟨hC, l, ⟨l₁, hl₁, B₁, hB₁, hB₁r, -, rfl⟩, hlC⟩
  have hCe : C = Φ.viableAncestor B₁ :=
    hU.1 (hΦU hC) (hΦU (viableAncestor_anc hΦ hB₁).1) hlC.symm
  subst hCe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₁)) ?_
  -- the stored lock below the unlocked one
  obtain ⟨l₂, ⟨l₃, hl₃, B₃, hB₃, hB₃r, hlive, rfl⟩, B₂, hB₂, hB₂r, hl₁e⟩ := id hl₁
  have hB₂e : B₂ = Φ.viableAncestor B₃ :=
    hΦ.coherent.1 hB₂ (viableAncestor_anc hΦ hB₃).1 hB₂r
  subst hB₂e
  have h₂₃ : Anc U (Φ.viableAncestor B₃) B₃ := Anc.mono hΦU (anc_viableAncestor _ B₃)
  split_ifs at hl₁e with hlt
  · subst hl₁e
    obtain ⟨hT, hTB⟩ := unlockTarget_anc sp hΦ V σ hB₂
    obtain rfl : B₁ = unlockTarget sp Φ V σ (Φ.viableAncestor B₃) := hΦ.coherent.1 hB₁ hT hB₁r
    rcases hlow with ⟨S, hS, hn⟩ | hlow
    · rcases unlock_compatible hΦ hB hS hn L t _ hl₁ hlt _ hB₁ rfl with h | h
      · exact Or.inl (Anc.mono hΦU h)
      · exact Or.inr (Anc.mono hΦU h)
    · exact down ((Anc.mono hΦU hTB).trans h₂₃) (hlow l₃ hl₃ hlive hlt B₃ (hΦU hB₃) hB₃r)
  · subst hl₁e
    obtain rfl : B₁ = Φ.viableAncestor B₃ :=
      hΦ.coherent.1 hB₁ (viableAncestor_anc hΦ hB₃).1 hB₁r
    exact down h₂₃ (hhigh l₃ hl₃ hlive (not_lt.1 hlt) B₃ (hΦU hB₃) hB₃r)

/-! ## At an honest proposal of slot `σ + 1`

`x` makes the proposal at cut `i`, at `t_{σ+1}`, with `ḡ + 4Δ ≤ t_σ`. -/

/-- A vote that an honest node sent or admitted in `[t_σ, t_σ + 3Δ)` reaches the proposer:
it holds it, or two other votes of its validator. -/
theorem proposal_forward (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {z : Fin sp.n}
    (hz : z ∈ H) {k : Nat} {v : Vote sp.n} (hsend : tr.SendOrAdmit z k v) (hvs : v.slot = σ)
    (h₁ : sp.ts σ ≤ tr.time k) (h₂ : tr.time k < sp.ts σ + 3 * sp.Δ) :
    v ∈ (tr.state x i).pool σ ∨ v.val ∈ equivocators {w | w ∈ (tr.state x i).pool σ} := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have := sync_forward hr (hS.syncAC (le_trans (by linarith) hσ) (sp.ts σ + 3 * sp.Δ)) hz hsend
    h₁ h₂.le hx hc (fun k' _ hrk => (hS.restart_le hx hrk).trans (by linarith))
    (by rw [ht, hts]; linarith) fun t ht₁ ht₂ => by
      rw [slot_of_mem sp σ (h₁.trans ht₁) (by rw [hts]; linarith), hvs]; omega
  rwa [hvs] at this

/-- A block (extending `Φ.F`) that an honest node accepted before `t_σ + 3Δ` is accepted by the
proposer before its proposal, so it is in its tree. -/
theorem proposal_accept (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {z : Fin sp.n}
    (hz : z ∈ H) {k : Nat} {X : Blk sp.n FGP} (hacc : tr.AcceptAt z k X)
    (hk : tr.time k < sp.ts σ + 3 * sp.Δ) (hF : Anc U ℓ.frame.F X) :
    ∃ k' < i, tr.AcceptAt x k' X := by
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨k', hk'i, hacc', hlt⟩ := relay_accept hS hz hacc hk (by linarith) hx hc
    (by rw [ht, hts]; linarith) hF
  exact ⟨k', lt_of_le_of_ne hk'i (by rintro rfl; rw [ht, hts] at hlt; linarith), hacc'⟩

/-- The walk ends in the frame tree. -/
private theorem head_mem_tree {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {T : Set (Blk sp.n FGP)}
    (hT : T ⊆ Φ.tree) (A : SAState sp.n) (t : Time) (V : View sp.n) (σ : Int) :
    getHead sp A Φ t T V σ ∈ Φ.tree := by
  have ha : getAnchor sp A Φ t ∈ Φ.tree := by
    unfold getAnchor
    cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
    | none => exact hΦ.fcRoot_mem
    | some D =>
      rcases (deepest_mem hd).1 with h | h
      · exact h.1
      · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem
  obtain h | h := eq_or_ne (getAnchor sp A Φ t) (getHead sp A Φ t T V σ)
  · exact h ▸ ha
  · exact (Anc.mem (C := getHead sp A Φ t T V σ) (anc_ghost hT _ ha) h).2

/-- Under trivial frames, `Φ.F` is the same block at every honest call. -/
private theorem frame_F_eq (hS : StandaloneRun tr H U g) {y z : Fin sp.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hc' : tr.CallAt z j ℓ') : ℓ.frame.F = ℓ'.frame.F := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨hΦ', hΦ'U⟩ := frameIn_of_callAt hr hz hc'
  exact hr.coherent.1 (hΦU hΦ.rooted.1) (hΦ'U hΦ'.rooted.1)
    ((hS.trivial y hy i ℓ hc).1.trans (hS.trivial z hz j ℓ' hc').1.symm)

/-- Under trivial frames, a block of `U` is in an honest node's tree when it is genesis or
accepted by the node by then. -/
theorem trivial_mem_tree (hS : StandaloneRun tr H U g) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) {X : Blk sp.n FGP} (hX : X ∈ U)
    (h : X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k X) : X ∈ ℓ.frame.tree := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨hF, -, -, htree⟩ := hS.trivial y hy i ℓ hc
  rcases h with h | h
  · obtain rfl : X = ℓ.frame.F := hr.coherent.1 hX (hΦU hΦ.rooted.1) (h.trans hF.symm)
    exact hΦ.rooted.1
  · rw [htree]; exact Set.mem_insert_of_mem _ h

/-- An honest vote's head, and every ancestor `X` of it, extends `Φ.F` (at every honest call)
and is genesis or a block the voter accepted by its vote. -/
theorem vote_head_accepted (hS : StandaloneRun tr H U g) {z : Fin sp.n} (hz : z ∈ H) {j : Nat}
    {e : Em sp FGP} (hv : VoteAt tr z j e) {X Hd : Blk sp.n FGP} (hHd : Hd ∈ U)
    (hHdr : Hd.root = e.msg.head) (hX : Anc U X Hd) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc' : tr.CallAt y i ℓ') :
    Anc U ℓ'.frame.F X ∧ (X.root = sp.genesisRoot ∨ ∃ k ≤ j, tr.AcceptAt z k X) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hXU : X ∈ U := by
    by_cases h : X = Hd
    · exact h ▸ hHd
    · exact (Anc.mem hX h).1
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hz hc
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hr hz ⟨hc, he⟩
  have hm := head_mem_tree hΦ (fun _ hX => hX.1.1) e.readPoint (tr.time j)
    (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)
    (T := ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot))
  obtain rfl := hU.1 hHd (hΦU hm) (hHdr.trans hhead)
  have hacc : X.root = sp.genesisRoot ∨ ∃ k ≤ j, tr.AcceptAt z k X := by
    rcases trivial_anc_mem hS hz hc hm hX with h | h
    · exact Or.inl (h ▸ (hS.trivial z hz j ℓ hc).1)
    · exact Or.inr h
  refine ⟨?_, hacc⟩
  rw [frame_F_eq hS hy hz hc' hc]
  exact (hΦ.rooted.2 X (trivial_mem_tree hS hz hc hXU hacc)).mono hΦU

private theorem lookup_mem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) : lookup Φ B.root = some B := by
  cases h : lookup Φ B.root with
  | none => exact absurd ⟨B, hB, rfl⟩ (lookup_eq_none h)
  | some B' =>
    obtain ⟨hB', hr⟩ := lookup_eq_some h
    exact congrArg some (hΦ.coherent.1 hB' hB hr)

private theorem etime_finite (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

/-- A vote of an honest node's pool has a finite stamp. -/
theorem pool_stamp_lt_top (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {v : Vote sp.n} (hv : v ∈ (tr.state y i).pool v.slot) :
    (tr.state y i).voteStamp v < ⊤ := by
  rcases pool_origin hr hy i v hv with ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
    rw [hst] <;> exact etime_finite _

/-- **A held vote supports at the proposal.** A slot-`σ` vote that the proposer holds, with a
head (of slot at most `σ`) in its tree that is genesis or accepted before the proposal, is
counted as support for every ancestor `C` of its head in the proposal's view, unless its
validator equivocates there. -/
theorem proposal_supporter (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hcall : ℓ.call = .proposal) {v : Vote sp.n} (hvs : v.slot = σ)
    (hv : v ∈ (tr.state x i).pool σ) {C Hv : Blk sp.n FGP}
    (hHv : Hv ∈ ℓ.frame.tree) (hHvr : Hv.root = v.head) (hHvs : Hv.slot ≤ σ)
    (hCHv : ℓ.frame.Anc C Hv) (hacc : Hv.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Hv)
    (hneq : v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes) :
    v.val ∈ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ C := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hx hc
  have hvst := pool_stamp_lt_top hr hx (hvs ▸ hv)
  have hbs : (tr.state x i).blockStamp Hv.root < ETime.of (tr.time i + 1) :=
    blockStamp_lt_of_acceptedBefore sp hr hx hc hHv
      (hacc.imp id fun ⟨k, hk, hacc⟩ =>
        ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk.le) (lt_add_one _)⟩)
      (fun k hk _ => lt_of_le_of_lt (hr.time_mono hk) (lt_add_one _))
      (Or.inr (by rw [hcall]; exact fun h => by cases h))
  have hres : resolutionTime (tr.state x i) ℓ.frame v < ⊤ := by
    unfold resolutionTime
    rw [← hHvr, lookup_mem hΦ hHv]
    simp only [show ¬ v.slot < Hv.slot by omega, ite_false]
    exact max_lt hvst (lt_trans hbs (etime_finite _))
  have hpool : v ∈ (tr.state x i).poolAt (σ : Int) := by simpa [SAState.poolAt] using hv
  refine ⟨hneq, v, ?_, rfl, by simp [hvs], Hv, hHv, hHvr, hCHv⟩
  exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hpool, by simpa using hvst⟩, by simpa using hres⟩

/-! ## The proposal's view -/

/-- The proposal's view holds exactly the pool's slot-`σ` votes (their stamps are finite). -/
theorem mem_proposalView_votes (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i σ : Nat) (Φ : Frm sp.n FGP) (v : Vote sp.n) :
    v ∈ (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes ↔
      v ∈ (tr.state x i).pool σ := by
  change v ∈ ((tr.state x i).poolAt σ).filter _ ↔ _
  simp only [SAState.poolAt, show ¬ ((σ : Int) < 0) by omega, ite_false, Int.toNat_natCast,
    List.mem_filter, decide_eq_true_eq, and_iff_left_iff_imp]
  intro hv
  exact pool_stamp_lt_top hr hx (state_pool_slot sp hr hx i σ v hv ▸ hv)

/-- The support of a view of lists is among its votes. -/
theorem ofLists_support_subset (A : SAState sp.n) (Φ : Frm sp.n FGP) (σ : Int) (c : ETime) :
    (View.ofLists (voteViewList A Φ σ c)).support ⊆ (View.ofLists (voteViewList A Φ σ c)).votes :=
  fun _ hv => (List.mem_filter.1 hv).1

/-- An honest validator does not equivocate in an honest node's pool. -/
theorem honest_pool_not_equivocator (hrun : ACRun tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators {v | v ∈ (tr.state x i).pool σ} := by
  rintro ⟨a, ha, b, hb, hab, rfl, hbw⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hrun.honest.pool_vote x hx i σ _ ha hw
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hrun.honest.pool_vote x hx i σ _ hb (hbw ▸ hw)
  have has := state_pool_slot sp hrun.localRun hx i σ _ ha
  have hbs := state_pool_slot sp hrun.localRun hx i σ _ hb
  rw [hbw] at hvb
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hrun.localRun _ hw ja jb ea eb hva hvb
    (has.trans hbs.symm)
  exact hab rfl

/-! ## The walk of a proposal -/

/-- **The proposal's walk** (`anc_getHead` at the proposal, under trivial frames): the head of an
honest `ac_proposal` of slot `σ + 1` extends a block `B` of its tree when every live lock after
the unlocking is compatible with `B` and every child toward `B` is the best. -/
theorem proposal_walk (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
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
    Anc U B d.head := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial x hx i ℓ hc
  obtain ⟨-, hd⟩ := acProposal_head hprop
  rw [hslot, show ((σ + 1 : Nat) : Int) - 1 = σ by push_cast; ring] at hd
  rw [hd]
  refine Anc.mono hΦU (anc_getHead hr.coherent hΦ hΦU _ _ _ _ subset_rfl
    (fun _ hB' X hX => mem_of_anc hX hB') (Or.inl ?_) hlocks hbest)
  refine ⟨hB, by rw [hfc]; exact hΦ.rooted.2 B hB, B, hB, by rw [hvh]; exact hB,
    Relation.ReflTransGen.refl⟩

/-! ## The locks of slot `σ` or later at a proposal of slot `σ + 1` -/

/-- An honest optimistic lock is compatible with `B` when every honest vote of its slot extends
`B` (`f < n/2`). -/
theorem optimisticLock_compatible (hS : StandaloneRun tr H U g) {z : Fin sp.n} (hz : z ∈ H)
    {k s : Nat} {O : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hopt : OptimisticLockAt tr z k s O CV)
    {B : Blk sp.n FGP}
    (hB : ∀ w ∈ H, ∀ j e, VoteAt tr w j e → e.msg.slot = s → VoteExtends U e.msg B) :
    Compatible U O B := by
  have hrun := hS.run
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hopt
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hz hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34
  refine origin_compatible hr.coherent hΦU h34 hS.two_faulty_lt fun v hv hvH => ?_
  obtain ⟨hvs, j, -, e, hve, rfl⟩ := optimisticPoint_pool_vote hrun hz hpt hv hvH
  exact hB _ hvH j e hve hvs

/-- At a proposal of slot `σ + 1` (at `t_{σ+1}`), a stored lock of slot `≥ σ` sits below an
optimistic lock of its slot: no update of such a slot has happened yet. -/
theorem proposal_high_lock (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlσ : σ ≤ l.slot) {X : Blk sp.n FGP} (hX : X ∈ U)
    (hXr : X.root = l.block) : ∃ O, Anc U X O ∧ ∃ k CV, OptimisticLockAt tr x k l.slot O CV := by
  have hr := hS.run.localRun
  obtain ⟨L, hL, hLr, O, hLO, k, hk, CV, hO⟩ := lock_below_origin hr hx i l hl
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

/-! ## The honest batch at a proposal (A1.3) -/

private theorem compat_down (hU : Coherent U) {B X Y : Blk sp.n FGP} (hXY : Anc U X Y)
    (h : Compatible U Y B) : Compatible U X B := by
  rcases h with h | h
  · exact Or.inl (hXY.trans h)
  · exact anc_total hU hXY h

private theorem equivocators_mono {S T : Set (Vote sp.n)} (h : S ⊆ T) :
    equivocators S ⊆ equivocators T := by
  rintro w ⟨a, ha, b, hb, hab, haw, hbw⟩
  exact ⟨a, h ha, b, h hb, hab, haw, hbw⟩

/-- An honest validator does not equivocate in the view of an honest proposal. -/
theorem honest_not_equivocator_proposal (hrun : ACRun tr H U) {x : Fin sp.n} (hx : x ∈ H)
    (i σ : Nat) (Φ : Frm sp.n FGP) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (View.ofLists (voteViewList (tr.state x i) Φ σ ⊤)).votes := fun h =>
  honest_pool_not_equivocator hrun hx i σ hw <| equivocators_mono
    (fun v hv => (mem_proposalView_votes hrun.localRun hx i σ Φ v).1 hv) h

/-- The time and the slot of an honest proposal of slot `σ + 1`. -/
private theorem proposal_slot {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) :
    sp.slot (tr.time i) = σ + 1 := by
  have hΔ := sp.toParams.hΔ
  rw [ht]
  exact slot_of_mem sp (σ + 1) le_rfl (by simp only [SAParams.ts]; push_cast; linarith)

/-- An honest slot-`σ` vote (`σ ≥ r`) reaches an honest proposal of slot `σ + 1`, and its head
and every ancestor of it in `U` are in the proposer's tree, accepted before the proposal. -/
theorem honest_vote_at_proposal (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {w : Fin sp.n}
    (hw : w ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr w j e) (hes : e.msg.slot = σ) :
    e.msg ∈ (tr.state x i).pool σ ∧ ∀ X Hd : Blk sp.n FGP, Hd ∈ U → Hd.root = e.msg.head →
      Anc U X Hd → X ∈ ℓ.frame.tree ∧ (X.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k X) := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓw, hcw, hew⟩ := id hv
  obtain ⟨hval, hsl, -, -⟩ := castAt_spec hr hw ⟨hcw, hew⟩
  have htj : tr.time j ≤ sp.ts σ + sp.Δ := by
    have := vote_time_le hr hw hv; rwa [← hsl, hes] at this
  have htj' : sp.ts σ ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [← hsl, hes])
  refine ⟨?_, fun X Hd hHd hHdr hXHd => ?_⟩
  · rcases proposal_forward hS hx hc ht hσ hw ⟨ℓw, hcw, Or.inl ⟨e, hew, rfl⟩⟩ hes htj'
      (by linarith) with h | h
    · exact h
    · rw [hval] at h
      exact absurd h (honest_pool_not_equivocator hrun hx i σ hw)
  obtain ⟨hF, hacc⟩ := vote_head_accepted hS hw hv hHd hHdr hXHd hx hc
  have hXU : X ∈ U := by
    by_cases h : X = Hd
    · exact h ▸ hHd
    · exact (Anc.mem hXHd h).1
  have hacc' : X.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k X :=
    hacc.imp id fun ⟨k, hkj, hk⟩ => proposal_accept hS hx hc ht hσ hw hk
      (lt_of_le_of_lt (hr.time_mono hkj) (by linarith)) hF
  exact ⟨trivial_mem_tree hS hx hc hXU (hacc'.imp id fun ⟨k, hk, h⟩ => ⟨k, hk.le, h⟩), hacc'⟩

/-- **The honest batch at a proposal** (A1.3 at the proposal duty, T1 §3 "Thereafter the honest
batch ... releases older conflicting locks"): when every honest vote of a slot `σ ≥ r` and of
every later slot extends `B`, the head of every honest proposal of slot `σ + 1` extends `B`. -/
theorem batch_proposal (hS : StandaloneRun tr H U g) {σ : Nat}
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {B : Blk sp.n FGP}
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    (hlater : VotesExtendAfter tr H U σ B) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U B d.head := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  set SX : Set (Fin sp.n) := {w | w ∈ H ∧ ∃ j e', VoteAt tr w j e' ∧ e'.msg.slot = σ}
  have hhalf : sp.n ≤ 2 * SX.ncard := honest_voters_half hS.toHealthyBase hσ
  have hf := hS.two_faulty_lt
  -- `B` is in the proposer's tree
  have hBt : B ∈ ℓ.frame.tree := by
    obtain ⟨w, hw, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero (s := SX) (by omega)
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hB w hw j e hv hes
    exact ((honest_vote_at_proposal hS hx hc ht hσ hw hv hes).2 B Hd hHd hHdr hBHd).1
  -- the honest voters of slot `σ` support `B` at the proposal
  have hsupp : SX ⊆ supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
      σ B := by
    rintro w ⟨hw, j, e, hv, hes⟩
    obtain ⟨ℓw, hcw, hew⟩ := id hv
    have hval : e.msg.val = w := (castAt_spec hr hw ⟨hcw, hew⟩).1
    obtain ⟨hheld, hanc⟩ := honest_vote_at_proposal hS hx hc ht hσ hw hv hes
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hB w hw j e hv hes
    obtain ⟨Hd', hHd', hHd'r, hHds⟩ := honest_head hrun hw hv
    obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
    obtain ⟨hHdt, hacc⟩ := hanc Hd Hd hHd hHdr Relation.ReflTransGen.refl
    rw [← hval]
    exact proposal_supporter hS hx hc hcall hes hheld hHdt hHdr (hes ▸ hHds)
      (anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHdt) hacc
      (honest_not_equivocator_proposal hrun hx i σ ℓ.frame (hval ▸ hw))
  -- the voters are honest slot-`σ` voters or faulty
  have hvoters : voters (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ⊆
      SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · have hv' := (mem_proposalView_votes hr hx i σ ℓ.frame v).1 hv
      obtain ⟨j, -, e, hve, he⟩ := hrun.honest.pool_vote x hx i σ v hv' hw
      exact Or.inl ⟨hw, j, e, hve, by rw [he]; exact state_pool_slot sp hr hx i σ v hv'⟩
    · exact Or.inr hw
  have h3 : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    omega
  refine proposal_walk hS hx hc (proposal_slot ht) hprop hBt
    (unlocked_compatible hU hΦ hΦU hBt (Or.inl ⟨SX, fun w hw => ?_, hhalf⟩) ?_)
    fun X Cx hCx hp hCxB => isBest_of_majority hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hsupp hvoters h3 hCx hp hCxB
  · obtain ⟨-, v, hv, hvw, hvs, hva⟩ := hsupp hw
    exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · intro l hl _ hlσ X hX hXr
    obtain ⟨O, hXO, k, CV, hopt⟩ := proposal_high_lock hS hx ht hl (by exact_mod_cast hlσ) hX hXr
    refine compat_down hU hXO (optimisticLock_compatible hS hx hopt fun w hw j e hv hs => ?_)
    rcases (show l.slot = σ ∨ σ < l.slot by omega) with h | h
    · exact hB w hw j e hv (hs.trans h)
    · exact votesExtendAfter_iff.1 hlater w hw j e hv (by omega)

/-! ## Votes and blocks of an earlier honest node at the proposal -/

/-- A slot-`σ` vote (`σ ≥ r`) of an honest node's pool was sent or admitted by the node at an
earlier cut, at or after `t_σ`, at its stamp (no restart replays it: restarts are before `ḡ`). -/
theorem pool_sent (hS : StandaloneRun tr H U g) {z : Fin sp.n} (hz : z ∈ H) {c σ : Nat}
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {v : Vote sp.n} (hv : v ∈ (tr.state z c).pool σ) :
    ∃ k < c, tr.SendOrAdmit z k v ∧ sp.ts σ ≤ tr.time k ∧
      (tr.state z c).voteStamp v = ETime.of (tr.time k) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hvs := state_pool_slot sp hr hz c σ v hv
  rcases pool_origin hr hz c v (hvs ▸ hv) with
    ⟨k, hk, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, hrk, -, B, hB, hvB⟩
  · exact ⟨k, hk, hsend,
      (ts_le_iff_le_slot sp (hr.time_nonneg k) σ).2 (by rw [← hvs]; exact_mod_cast hsl), hst⟩
  · exfalso
    have hBv := (frame_validPayload sp hr hz hck B hB).1 v hvB
    have hBs := frame_slot_le sp hr hz hck B hB
    have htk := hS.restart_le hz ⟨ℓk, hck, hrk⟩
    have : ¬ (σ : Int) ≤ sp.slot (tr.time k) := fun h => by
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
      linarith
    omega

/-- A block that an honest node had in its tree at a call before `t_σ + 3Δ` (or genesis), and
every ancestor of it, is in the tree of an honest proposal of slot `σ + 1`, genesis or accepted
before it. -/
theorem early_block_at_proposal (hS : StandaloneRun tr H U g) {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {R : Blk sp.n FGP}
    (hR : R ∈ U) (hRe : R.root = sp.genesisRoot ∨ ∃ z ∈ H, ∃ k₁ ℓ₁, tr.CallAt z k₁ ℓ₁ ∧
      tr.time k₁ < sp.ts σ + 3 * sp.Δ ∧ R ∈ ℓ₁.frame.tree) {Y : Blk sp.n FGP}
    (hYR : Anc U Y R) :
    Y ∈ ℓ.frame.tree ∧ (Y.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Y) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hYU : Y ∈ U := by
    by_cases h : Y = R
    · exact h ▸ hR
    · exact (Anc.mem hYR h).1
  have hgen : Y.root = sp.genesisRoot →
      Y ∈ ℓ.frame.tree ∧ (Y.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Y) := fun hg =>
    ⟨trivial_mem_tree hS hx hc hYU (Or.inl hg), Or.inl hg⟩
  rcases hRe with hg | ⟨z, hz, k₁, ℓ₁, hc₁, ht₁, hR₁⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hx i ℓ hc
    obtain rfl : R = G := hU.1 hR hGU (hg.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hYR with h | ⟨c, -, hp⟩
    · exact hgen (h ▸ hg)
    · have := hp.2.2
      rw [hGp] at this
      exact absurd this (by simp)
  · obtain ⟨hΦ₁, hΦ₁U⟩ := frameIn_of_callAt hr hz hc₁
    rcases trivial_anc_mem hS hz hc₁ hR₁ hYR with hYF | ⟨k', hk', hacc⟩
    · exact hgen (hYF ▸ (hS.trivial z hz k₁ ℓ₁ hc₁).1)
    · have hY₁ : Y ∈ ℓ₁.frame.tree := by
        rw [(hS.trivial z hz k₁ ℓ₁ hc₁).2.2.2]; exact Set.mem_insert_of_mem _ ⟨k', hk', hacc⟩
      have hF : Anc U ℓ.frame.F Y := by
        rw [frame_F_eq hS hx hz hc hc₁]; exact (hΦ₁.rooted.2 Y hY₁).mono hΦ₁U
      obtain ⟨k, hk, hacc'⟩ := proposal_accept hS hx hc ht hσ hz hacc
        (lt_of_le_of_lt (hr.time_mono hk') ht₁) hF
      exact ⟨trivial_mem_tree hS hx hc hYU (Or.inr ⟨k, hk.le, hacc'⟩), Or.inr ⟨k, hk, hacc'⟩⟩

/-- **The writer's pool, for the proposer's pool.** A slot-`σ` vote that an honest proposer of
slot `σ + 1` holds is held by an honest node at its update of slot `σ` (at `t_σ + 6Δ`), or that
node holds two votes of its validator. -/
theorem writer_pool_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ σ ℓX)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) :
    ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ} := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (σ + 2 : Nat) = sp.ts σ + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro v hv
  have hvs := state_pool_slot sp hr hx i σ v hv
  obtain ⟨k, hk, hsend, h1, -⟩ := pool_sent hS hx hσ hv
  have hki : tr.time k ≤ sp.ts σ + 4 * sp.Δ := by rw [← hts, ← ht]; exact hr.time_mono hk.le
  have := sync_forward hr (hS.syncAC (le_trans (by linarith) hσ) (sp.ts σ + 4 * sp.Δ)) hx hsend
    h1 hki hX hupd.1 (fun k' _ hrk => (hS.restart_le hX hrk).trans (by linarith))
    (by rw [hupd.2.2.1]; linarith) fun t ht₁ ht₂ => by
      have ht0 : 0 ≤ t := (hr.time_nonneg k).trans ht₁
      have ha := (ts_le_iff_le_slot sp ht0 σ).1 (h1.trans ht₁)
      have hb : ¬ ((σ + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
        have := (ts_le_iff_le_slot sp ht0 _).2 h
        rw [hts₂] at this; linarith
      rw [hvs]; omega
  rwa [hvs] at this

/-- **A counted vote at the proposal** (A1.8 (c) at the proposal duty): a vote that an honest
update of slot `σ` counts for a block `E` (`fastCounted`, resolved before `t_σ + 2Δ`) is held by
an honest proposer of slot `σ + 1`, whose view does not show its validator equivocating; its
head extends `E` and is, with its ancestors, in the proposer's tree. -/
theorem counted_at_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ σ ℓX)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {E : Blk sp.n FGP} {v : Vote sp.n}
    (hv : v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E) :
    v.slot = σ ∧ v ∈ (tr.state x i).pool σ ∧
      v.val ∉ equivocators (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ∧
      ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ σ ∧ Anc U E R ∧ ∀ Y, Anc U Y R →
        Y ∈ ℓ.frame.tree ∧ (Y.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Y) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAt hr hX hupd.1
  obtain ⟨hvp, hneqX, hres, R, hR, hRr, hER⟩ := hv
  have hvs := state_pool_slot sp hr hX i₀ σ v hvp
  unfold resolutionTime at hres
  rw [← hRr, lookup_mem hΦX hR] at hres
  dsimp only at hres
  split_ifs at hres with hlt
  · exact absurd hres (not_lt.2 le_top)
  have hvst := lt_of_le_of_lt (le_max_left _ _) hres
  have hbs := lt_of_le_of_lt (le_max_right _ _) hres
  obtain ⟨k, -, hsend, h1, hst⟩ := pool_sent hS hX hσ hvp
  rw [hst] at hvst
  have hk2 : tr.time k < sp.ts σ + 2 * sp.Δ := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hvst)
  -- the proposer's votes reach the writer's update
  have hwp := writer_pool_proposal hS hX hupd hσ hx ht
  have hnoeq : v.val ∉ equivocators {w | w ∈ (tr.state x i).pool σ} := by
    rintro ⟨a, ha, b, hb, hab, haw, hbw⟩
    apply hneqX
    rcases hwp a ha with ha' | ⟨a', ha', b', hb', hab', ha'w, hb'w⟩
    · rcases hwp b hb with hb' | ⟨a', ha', b', hb', hab', ha'w, hb'w⟩
      · exact ⟨a, ha', b, hb', hab, haw, hbw⟩
      · exact ⟨a', ha', b', hb', hab', ha'w.trans hbw, hb'w.trans hbw⟩
    · exact ⟨a', ha', b', hb', hab', ha'w.trans haw, hb'w.trans haw⟩
  have hheld : v ∈ (tr.state x i).pool σ := by
    rcases proposal_forward hS hx hc ht hσ hX hsend hvs h1 (by linarith) with h | h
    · exact h
    · exact absurd h hnoeq
  refine ⟨hvs, hheld, fun h => hnoeq (equivocators_mono
    (fun w hw => (mem_proposalView_votes hr hx i σ ℓ.frame w).1 hw) h), R, hΦXU hR, hRr,
    by omega, Anc.mono hΦXU hER, fun Y hYR => early_block_at_proposal hS hx hc ht hσ (hΦXU hR)
      ?_ hYR⟩
  -- the head was accepted by the writer before `t_σ + 2Δ`
  rcases accepted_of_blockStamp_lt hS hX hbs with hg | ⟨k₁, -, R', hR'r, hacc, ht₁⟩
  · exact Or.inl hg
  · obtain ⟨ℓ₁, hc₁, hcall₁⟩ := id hacc
    have hR'₁ := (accept_new sp hr hX hacc).1 ℓ₁ hc₁
    obtain rfl : R' = R :=
      hU.1 ((frameIn_of_callAt hr hX hc₁).2 hR'₁) (hΦXU hR) hR'r
    exact Or.inr ⟨X, hX, k₁, ℓ₁, hc₁, by linarith, hR'₁⟩

/-- The validators that an honest update of slot `σ` counts for `E` are supporters of every
`B ⪯ E` of the tree in the view of an honest proposal of slot `σ + 1`. -/
theorem counted_supporters_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ σ ℓX)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {B E : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
    (hBE : Anc U B E) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E, v.val = w} ⊆
      supporters ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨hvs, hheld, hneq, R, hR, hRr, hRs, hER, hacc⟩ :=
    counted_at_proposal hS hX hupd hσ hx hc ht hv
  obtain ⟨hRt, hRacc⟩ := hacc R Relation.ReflTransGen.refl
  exact proposal_supporter hS hx hc hcall hvs hheld hRt hRr hRs
    (anc_tree_of_anc_U hr.coherent hΦ hΦU hB (hBE.trans hER) hRt) hRacc hneq

/-- **A result's majority at the proposal** (A1.8 (b) at the proposal duty): for an honest
result `C` of slot `σ` and a block `B ⪯ C` of the tree of an honest proposal of slot `σ + 1`,
every child toward `B` is the best of its siblings (a strict majority of the proposal's voters,
who are participants at the update). -/
theorem result_best_at_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hres : ResultAt tr X i₀ σ C CV)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
    (hBC : Anc U B C) :
    ∀ X' Cx : Blk sp.n FGP, Cx ∈ ℓ.frame.viableTree ℓ.frame.tree →
      Cx.parent = some X'.root → ℓ.frame.Anc Cx B →
      IsBest sp (goldfishScore sp ℓ.frame (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤))
        σ)
        {B' | B' ∈ ℓ.frame.viableTree ℓ.frame.tree ∧ B'.parent = some X'.root ∧
          goldfishEligible sp ℓ.frame (tr.time i)
            (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)) σ B'} Cx := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hx hc
  have hmaj := result_majority hres
  obtain ⟨ℓX, hupd, -, rfl⟩ := hres
  have hwp := writer_pool_proposal hS hX hupd hσ hx ht
  have hvoters : voters (View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤)).votes ⊆
      voters {v | v ∈ (tr.state X i₀).pool σ} := by
    rintro w ⟨v, hv, rfl⟩
    rcases hwp v ((mem_proposalView_votes hr hx i σ ℓ.frame v).1 hv) with
      h | ⟨a, ha, -, -, -, haw, -⟩
    · exact ⟨v, h, rfl⟩
    · exact ⟨a, ha, haw⟩
  exact fun X' Cx hCx hp hCxB => isBest_of_majority hΦ (ofLists_support_subset _ _ _ _)
    (fun _ h => h.1) (counted_supporters_proposal hS hX hupd hσ hx hc hcall ht hB hBC) hvoters
    hmaj hCx hp hCxB

/-- An ancestor of an honest result of slot `σ` is in the tree of an honest proposal of slot
`σ + 1` (below the head of a counted vote). -/
theorem result_block_at_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hres : ResultAt tr X i₀ σ C CV)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {B : Blk sp.n FGP} (hBC : Anc U B C) :
    B ∈ ℓ.frame.tree := by
  have hmaj := result_majority hres
  obtain ⟨ℓX, hupd, -, rfl⟩ := hres
  obtain ⟨w, v, hv, -⟩ := Set.nonempty_of_ncard_ne_zero
    (s := {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ C, v.val = w}) (by omega)
  obtain ⟨-, -, -, R, -, -, -, hCR, hacc⟩ := counted_at_proposal hS hX hupd hσ hx hc ht hv
  exact (hacc B (hBC.trans hCR)).1

/-! ## The first proposal after a good origin -/

/-- **A fast update transfers to the next proposal** (A1.2 at the proposal duty): for an honest
fast lock of slot `σ ≥ r` on `D` written by the fast test of an update, when every honest vote
of a later slot extends `D`, the head of every honest proposal of slot `σ + 1` extends `D`. -/
theorem update_first_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfu : FastUpdateAt tr X i₀ σ D CV)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hcall : ℓ.call = .proposal) (ht : tr.time i = sp.ts (σ + 1 : Nat))
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨ℓX, C, hupd, hconf, hnc, hfs, hCV⟩ := id hfu
  have hres : ResultAt tr X i₀ σ C (fastCounted sp (tr.state X i₀) ℓX.frame σ C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAt hr hX hupd.1
  obtain ⟨⟨-, -, hDC⟩, hfast⟩ := (deepest_mem hfs).1
  have hDC' : Anc U D C := Anc.mono hΦXU hDC
  have hDt := result_block_at_proposal hS hX hres hσ hx hc ht hDC'
  -- the counted validators of `D` are half of the committee, and supporters of `D`
  set SX := {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ D, v.val = w}
  have hhalf : sp.n ≤ 2 * SX.ncard := by
    refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
    rintro w ⟨hw, v, ⟨hv, hres⟩, hval, -, hanc⟩
    exact ⟨v, ⟨hv, hval ▸ hw, hres, hanc⟩, hval⟩
  have hsupp := counted_supporters_proposal hS hX hupd hσ hx hc hcall ht hDt
    (Relation.ReflTransGen.refl (a := D))
  refine proposal_walk hS hx hc (proposal_slot ht) hprop hDt
    (unlocked_compatible hU hΦ hΦU hDt (Or.inl ⟨SX, fun w hw => ?_, hhalf⟩) ?_)
    (result_best_at_proposal hS hX hres hσ hx hc hcall ht hDt hDC')
  · obtain ⟨-, v, hv, hvw, hvs, hva⟩ := hsupp hw
    exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · intro l hl _ hlσ Y hY hYr
    obtain ⟨O, hYO, k, CV', hopt⟩ := proposal_high_lock hS hx ht hl (by exact_mod_cast hlσ) hY hYr
    refine compat_down hU hYO ?_
    rcases (show l.slot = σ ∨ σ < l.slot by omega) with h | h
    · rw [h] at hopt
      exact fastLock_fastLock_compatible hS.toHealthyBase hx (Or.inr hopt) hX (Or.inl hfu)
        (by linarith)
    · exact optimisticLock_compatible hS hx hopt fun w hw j e hv hs =>
        votesExtendAfter_iff.1 hlater w hw j e hv (by omega)

/-- **An optimistic confirmation transfers to the next proposal** (A1.4 (a) at the proposal
duty): for an honest optimistic lock of slot `σ ≥ r` on `D`, when every honest vote of a later
slot extends `D`, the head of every honest proposal of slot `σ + 1` extends `D`. Its `3n/4`
optimistic voters reach the proposer, each as a supporter of `D` or an equivocator there. -/
theorem optimistic_first_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ)
    (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨ℓX, A, hpt, hslX, hsel, -⟩ := id hopt
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_callAt hr hX hpt.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  obtain ⟨hDX, h34, -⟩ := (deepest_mem hsel').1
  rw [hslX] at h34
  -- the optimistic check is in `[t_σ, t_σ + 2Δ)`
  have hti₀ : tr.time i₀ < sp.ts σ + 2 * sp.Δ := by
    rw [← hslX]; exact not_le.1 (not_or.1 (not_or.1 hcond).2).2
  have hearly : ∀ R ∈ ℓX.frame.tree, ∀ Y, Anc U Y R →
      Y ∈ ℓ.frame.tree ∧ (Y.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Y) :=
    fun R hR Y hYR => early_block_at_proposal hS hx hc ht hσ (hΦXU hR)
      (Or.inr ⟨X, hX, i₀, ℓX, hpt.1, by linarith, hR⟩) hYR
  have hDt := (hearly D hDX D Relation.ReflTransGen.refl).1
  set V := View.ofLists (voteViewList (tr.state x i) ℓ.frame σ ⊤) with hV
  set SX := optimisticVoters sp A ℓX.frame σ D
  -- every optimistic voter supports `D` at the proposal, or equivocates there
  have hcover : SX ⊆ supporters ℓ.frame V σ D ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R, hR, hRr, hDR⟩
    have hvs := optimisticPoint_pool_slot hr hX hpt hv
    obtain ⟨k, hk, hsend, h1, -⟩ :=
      pool_sent hS hX hσ (optimisticPoint_pool_post hr hX hpt σ hv)
    have hkt : tr.time k < sp.ts σ + 3 * sp.Δ :=
      lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) (by linarith)
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    rcases proposal_forward hS hx hc ht hσ hX hsend hvs h1 hkt with hheld | h
    · obtain ⟨hRt, hRacc⟩ := hearly R hR R Relation.ReflTransGen.refl
      have hRs : R.slot ≤ σ := by
        have := frame_slot_le sp hr hX hpt.1 R hR
        omega
      exact proposal_supporter hS hx hc hcall hvs hheld hRt hRr hRs
        (anc_tree_of_anc_U hU hΦ hΦU hDt (Anc.mono hΦXU hDR) hRt) hRacc heq
    · exfalso
      exact heq (equivocators_mono
        (fun u hu => (mem_proposalView_votes hr hx i σ ℓ.frame u).2 hu) h)
  -- counting: the equivocators are faulty, the other voters are outside `SX`
  have hf := hS.two_faulty_lt
  have hE : (equivocators V.votes).ncard ≤ Hᶜ.ncard := Set.ncard_le_ncard fun w hw =>
    fun hwH => honest_not_equivocator_proposal hrun hx i σ ℓ.frame hwH hw
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ ((voters V.votes \ SX) ∪ SX))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_union_eq Set.disjoint_sdiff_left] at this
    exact this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  refine proposal_walk hS hx hc (proposal_slot ht) hprop hDt
    (unlocked_compatible hU hΦ hΦU hDt (Or.inl ⟨SX, fun w hw => ?_, by omega⟩) ?_)
    fun X' Cx hCx hp hCxD => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover h3 hCx hp hCxD
  · rcases hcover hw with ⟨-, v, hv, hvw, hvs, hva⟩ | h
    · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
    · exact Or.inl h
  · intro l hl _ hlσ Y hY hYr
    obtain ⟨O, hYO, k, CV', hopt'⟩ :=
      proposal_high_lock hS hx ht hl (by exact_mod_cast hlσ) hY hYr
    refine compat_down hU hYO ?_
    rcases (show l.slot = σ ∨ σ < l.slot by omega) with h | h
    · rw [h] at hopt'
      exact fastLock_fastLock_compatible hS.toHealthyBase hx (Or.inr hopt') hX (Or.inr hopt)
        (by linarith)
    · exact optimisticLock_compatible hS hx hopt' fun w hw j e hv hs =>
        votesExtendAfter_iff.1 hlater w hw j e hv (by omega)

/-- **A slow origin transfers to the next proposal** (A1.8 for the ancestor `D` at the proposal
duty, T1 §4): for an honest slow lock of slot `σ` on `D` whose window `[σ − k + 1, σ]` is `≥ r`,
when every honest vote of a later slot extends `D`, the head of every honest proposal of slot
`σ + 1` extends `D`: every stored live lock there is compatible with `D` (by T1 §2 against the
writer's saved results), and the result's majority leads the walk to `D`. -/
theorem slow_first_proposal (hS : StandaloneRun tr H U g) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr X i₀ σ D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((σ : Int) - sp.k + 1))
    (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨ℓX, C, hupd, hconf, -, hdeep, -⟩ := id hsl
  have hres : ResultAt tr X i₀ σ C (fastCounted sp (tr.state X i₀) ℓX.frame σ C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  have hΦXU := (frameIn_of_callAt hr hX hupd.1).2
  obtain ⟨⟨-, -, hDC⟩, -⟩ := (deepest_mem hdeep).1
  have hDC' : Anc U D C := Anc.mono hΦXU hDC
  have hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ := hs.trans ((ts_le_iff sp).2 (by omega))
  have hDt := result_block_at_proposal hS hX hres hσ hx hc ht hDC'
  have hwin := slow_window_results hr hX hsl (U := U)
  have hslot := proposal_slot ht
  -- every stored live lock is compatible with `D`
  have hall : ∀ l ∈ (tr.state x i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → ∀ Y ∈ U,
      Y.root = l.block → Compatible U Y D := by
    intro l hl hlive Y hY hYr
    rcases le_or_gt l.slot σ with hle | hlt
    · obtain ⟨L, hL, hLr, O, hLO, k, -, CV, hO⟩ := lock_below_origin hr hx i l hl
      obtain rfl : Y = L := hU.1 hY hL (hYr.trans hLr.symm)
      obtain ⟨kx, R, CVx, hR, hDR⟩ := hwin l.slot (by omega) hle
      have hjr : gbar g + 4 * sp.Δ ≤ sp.ts l.slot := hs.trans ((ts_le_iff sp).2 (by omega))
      have hcomp : Compatible U O R := by
        rcases hO with hO | hO
        · exact result_result_compatible hS.toHealthyBase hx hO hX hR hjr
        · exact (result_optimistic_compatible hS.toHealthyBase hX hR hx hO hjr).symm
      rcases hcomp with h | h
      · exact anc_total hU (hLO.trans h) hDR
      · exact anc_total hU hLO (hDR.trans h)
    · obtain ⟨O, hYO, k, CV', hopt⟩ := proposal_high_lock hS hx ht hl hlt.le hY hYr
      exact compat_down hU hYO (optimisticLock_compatible hS hx hopt fun w hw j e hv hs =>
        votesExtendAfter_iff.1 hlater w hw j e hv (by omega))
  refine proposal_walk hS hx hc hslot hprop hDt
    (unlocked_compatible hU hΦ hΦU hDt (Or.inr fun l hl hlive _ => hall l hl hlive)
      fun l hl hlive _ => hall l hl hlive)
    (result_best_at_proposal hS hX hres hσ hx hc hcall ht hDt hDC')

/-! ## Assembly -/

/-- **A good origin transfers to the proposals** (T1 §3–§4 at the proposal duty): if every
honest vote of a slot after the label `j` of a good origin on `B` extends `B`, the head of every
honest proposal of a slot after `j` extends `B`: the first one by the origin's argument, the
later ones by the honest batch. -/
theorem proposals_extend_of_origin (hS : StandaloneRun tr H U g) {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) (hvotes : VotesExtendAfter tr H U j B) :
    ProposalsExtendAfter tr H U j B := by
  have hk := sp.two_le_k
  rw [proposalsExtendAfter_iff]
  intro x hx i ℓ m d pay hc hcall ht hjm hprop
  obtain ⟨σ, rfl⟩ : ∃ σ, m = σ + 1 := ⟨m - 1, by omega⟩
  have hjr : gbar g + 4 * sp.Δ ≤ sp.ts j := by
    rcases goodOrigin_iff.1 hB with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact h
    · exact h.trans ((ts_le_iff sp).2 (by omega))
  have hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ := hjr.trans ((ts_le_iff sp).2 (by omega))
  rcases (show j = σ ∨ j < σ by omega) with rfl | hlt
  · rcases goodOrigin_iff.1 hB with ⟨X, hX, i₀, CV, hfu | hopt, -⟩ | ⟨X, hX, i₀, hsl, hs⟩
    · exact update_first_proposal hS hX hfu hσ hvotes hx hc hcall ht hprop
    · exact optimistic_first_proposal hS hX hopt hσ hvotes hx hc hcall ht hprop
    · exact slow_first_proposal hS hX hsl hs hvotes hx hc hcall ht hprop
  · exact batch_proposal hS hσ (fun z hz j' e hv hs =>
      votesExtendAfter_iff.1 hvotes z hz j' e hv (by omega))
      (votesExtendAfter_iff.2 fun z hz j' e hv hs =>
        votesExtendAfter_iff.1 hvotes z hz j' e hv (by omega)) hx hc hcall ht hprop

end Consensus.Goldilocks.SA

end
