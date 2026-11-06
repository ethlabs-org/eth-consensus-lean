module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: a good origin transfers to the proposal duty

The same argument applies at a proposal, over a `StandaloneRun`: the arguments are those of
`ProposalCore` (A1.2, A1.3, A1.4 (a), A1.8 at the proposal duty, over any frames), and this file
supplies their premises under trivial frames:

* (V) a block an honest node accepted before `t_σ + 3Δ` is accepted by the proposer by relay
  (`proposal_accept`), so it is in its tree, which is all viable (`TrivialFrames`);
* (P) the honest slot-`σ` votes (`honest_vote_at_proposal`) and the counted votes of an update
  (`counted_at_proposal`) are held by the proposer, with heads in its tree accepted before it;
* (W) from `Sync` after `ḡ` (`writer_pool_proposal`);
* (L) the stored locks of slot `≥ σ` are optimistic (`proposal_high_lock`), compatible by the
  votes after the origin and same-slot compatibility for slot `σ`; for a slow origin, the older
  live locks by same-slot compatibility against the writer's saved results.

`proposals_extend_of_origin` assembles them for H.1's `origin_transfer_proposals`, given that the
votes after the origin extend `B`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## At an honest proposal of slot `σ + 1`

`x` makes the proposal at cut `i`, at `t_{σ+1}`, with `ḡ + 4Δ ≤ t_σ`. -/

/-- A vote that an honest node sent or admitted in `[t_σ, t_σ + 3Δ)` reaches the proposer:
it holds it, or two other votes of its validator. -/
theorem proposal_forward (hS : StandaloneRun tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat}
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
theorem proposal_accept (hS : StandaloneRun tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H) {i σ : Nat}
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

/-- Under trivial frames, a block of `U` is in an honest node's tree when it is genesis or
accepted by the node by then. -/
theorem trivial_mem_tree (hS : StandaloneRun tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
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
theorem vote_head_accepted (hS : StandaloneRun tr H U proposer g)
    {z : Fin sp.n} (hz : z ∈ H) {j : Nat}
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
  have hm := getHead_mem hΦ (fun _ hX => (voteDomain_subset_tree hX.1)) e.readPoint (tr.time j)
    (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)
    (T := ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
  obtain rfl := hU.1 hHd (hΦU hm) (hHdr.trans hhead)
  have hacc : X.root = sp.genesisRoot ∨ ∃ k ≤ j, tr.AcceptAt z k X := by
    rcases trivial_anc_mem hS hz hc hm hX with h | h
    · exact Or.inl (h ▸ (hS.trivial z hz j ℓ hc).1)
    · exact Or.inr h
  refine ⟨?_, hacc⟩
  rw [trivial_F_eq hS hy hz hc' hc]
  exact (hΦ.rooted.2 X (trivial_mem_tree hS hz hc hXU hacc)).mono hΦU

/-! ## The premises of `ProposalCore` under trivial frames -/

private theorem compat_down (hU : Coherent U) {B X Y : Blk sp.n FGP} (hXY : Anc U X Y)
    (h : Compatible U Y B) : Compatible U X B := by
  rcases h with h | h
  · exact Or.inl (hXY.trans h)
  · exact anc_total hU hXY h

/-- The restarts of an honest node are at or before `ḡ`, so before `t_σ` for `σ ≥ r`. -/
private theorem restart_before (hS : StandaloneRun tr H U proposer g) {z : Fin sp.n} (hz : z ∈ H)
    {σ : Nat} (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {k : Nat} (hrk : tr.RestartAt z k) :
    tr.time k < sp.ts σ :=
  lt_of_le_of_lt (hS.restart_le hz hrk) (by have := sp.toParams.hΔ; linarith)

/-- (W) under `StandaloneRun`: `Sync` from `ḡ` and restarts at or before `ḡ`. -/
private theorem trivial_writer_pool (hS : StandaloneRun tr H U proposer g)
    {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ σ ℓX)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) :
    ∀ v ∈ (tr.state x i).pool σ, v ∈ (tr.state X i₀).pool σ ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool σ} :=
  writer_pool_proposal hS.run.localRun hX hupd hx ht
    (hS.syncAC (by have := sp.toParams.hΔ; linarith) _)
    (fun _ _ hrk => (restart_before hS hX hσ hrk).le) fun _ _ hrk => restart_before hS hx hσ hrk

/-- A block of an honest proposer's tree that is genesis or accepted before the proposal has a
finite stamp there. -/
private theorem trivial_stamp (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hcall : ℓ.call = .proposal) {R : Blk sp.n FGP} (hR : R ∈ ℓ.frame.tree)
    (hacc : R.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k R) :
    (tr.state x i).blockStamp R.root < ⊤ := by
  have hr := hS.run.localRun
  exact lt_trans (blockStamp_lt_of_acceptedBefore sp hr hx hc hR
    (hacc.imp id fun ⟨k, hk, hacc⟩ =>
      ⟨k, hacc, lt_of_le_of_lt (hr.time_mono hk.le) (lt_add_one _)⟩)
    (fun k hk _ => lt_of_le_of_lt (hr.time_mono hk) (lt_add_one _))
    (Or.inr (by rw [hcall]; exact fun h => by cases h))) (etime_finite _)

/-- (V) under trivial frames: every block of the tree is viable. -/
private theorem trivial_viable_at (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) :
    B ∈ ℓ.frame.tree ∧ (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot) := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hS.run.localRun hx hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial x hx i ℓ hc
  exact ⟨hB, Or.inl ⟨hB, by rw [hfc]; exact hΦ.rooted.2 B hB, B, hB, by rw [hvh]; exact hB,
    Relation.ReflTransGen.refl⟩⟩

/-- An honest slot-`σ` vote (`σ ≥ r`) reaches an honest proposal of slot `σ + 1`, and its head
and every ancestor of it in `U` are in the proposer's tree, accepted before the proposal. -/
theorem honest_vote_at_proposal (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
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

/-- A block that an honest node had in its tree at a call before `t_σ + 3Δ` (or genesis), and
every ancestor of it, is in the tree of an honest proposal of slot `σ + 1`, genesis or accepted
before it. -/
theorem early_block_at_proposal (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
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
        rw [trivial_F_eq hS hx hz hc hc₁]; exact (hΦ₁.rooted.2 Y hY₁).mono hΦ₁U
      obtain ⟨k, hk, hacc'⟩ := proposal_accept hS hx hc ht hσ hz hacc
        (lt_of_le_of_lt (hr.time_mono hk') ht₁) hF
      exact ⟨trivial_mem_tree hS hx hc hYU (Or.inr ⟨k, hk.le, hacc'⟩), Or.inr ⟨k, hk, hacc'⟩⟩

/-- **A counted vote at the proposal** (A1.8 (c) at the proposal duty): a vote that an honest
update of slot `σ` counts for a block `E` (`fastCounted`, resolved before `t_σ + 2Δ`) is held by
an honest proposer of slot `σ + 1`, whose view does not show its validator equivocating; its
head extends `E` and is, with its ancestors, in the proposer's tree. -/
theorem counted_at_proposal (hS : StandaloneRun tr H U proposer g) {X : Fin sp.n} (hX : X ∈ H)
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
  rw [← hRr, SA.lookup_of_mem hΦX hR] at hres
  dsimp only at hres
  split_ifs at hres with hlt
  · exact absurd hres (not_lt.2 le_top)
  have hvst := lt_of_le_of_lt (le_max_left _ _) hres
  have hbs := lt_of_le_of_lt (le_max_right _ _) hres
  obtain ⟨k, -, hsend, h1, hst⟩ := pool_sent hr hX (fun _ _ hrk => restart_before hS hX hσ hrk) hvp
  rw [hst] at hvst
  have hk2 : tr.time k < sp.ts σ + 2 * sp.Δ := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hvst)
  -- the proposer's votes reach the writer's update
  have hwp := trivial_writer_pool hS hX hupd hσ hx ht
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
  refine ⟨hvs, hheld, fun h => hnoeq (proposalView_equivocator hr hx i σ ℓ.frame h), R,
    hΦXU hR, hRr,
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

/-- An ancestor of an honest result of slot `σ` is in the tree of an honest proposal of slot
`σ + 1` (below the head of a counted vote). -/
theorem result_block_at_proposal (hS : StandaloneRun tr H U proposer g) {X : Fin sp.n} (hX : X ∈ H)
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

/-- (P) for the counted votes of an honest update of slot `σ ≥ r` under trivial frames. -/
private theorem trivial_counted_held (hS : StandaloneRun tr H U proposer g)
    {X : Fin sp.n} (hX : X ∈ H)
    {i₀ σ : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ σ ℓX)
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {E : Blk sp.n FGP} :
    ∀ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame σ E,
      HeldAtProposal (tr.state x i) ℓ.frame σ v := by
  intro v hv
  obtain ⟨-, hheld, -, R, -, hRr, -, -, hacc⟩ := counted_at_proposal hS hX hupd hσ hx hc ht hv
  obtain ⟨hRt, hRacc⟩ := hacc R Relation.ReflTransGen.refl
  exact heldAtProposal_iff.2 ⟨Or.inl hheld, R, hRt, hRr, trivial_stamp hS hx hc hcall hRt hRacc⟩

/-- (L-high) under `StandaloneRun`: a stored lock of slot `> σ` is optimistic over votes that
extend `B`, and one of slot `σ` is compatible with `B` by `hsame`. -/
private theorem trivial_high_locks (hS : StandaloneRun tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H)
    {i σ : Nat} (ht : tr.time i = sp.ts (σ + 1 : Nat)) {B : Blk sp.n FGP}
    (hlater : VotesExtendAfter tr H U σ B)
    (hsame : ∀ k CV O, OptimisticLockAt tr x k σ O CV → Compatible U O B) :
    HighLocksCompatible U (tr.state x i) (tr.time i) σ B := by
  have hrun := hS.run
  refine highLocksCompatible_iff.2 fun l hl _ hlσ Y hY hYr => ?_
  obtain ⟨O, hYO, k, CV, hopt⟩ := proposal_high_lock hrun.localRun hx ht hl hlσ hY hYr
  refine compat_down hrun.localRun.coherent hYO ?_
  rcases (show l.slot = σ ∨ σ < l.slot by omega) with h | h
  · rw [h] at hopt
    exact hsame k CV O hopt
  · exact optimisticLock_compatible hrun hS.two_faulty_lt hx hopt fun w hw j e hv hs =>
      votesExtendAfter_iff.1 hlater w hw j e hv (by omega)

/-! ## The first and later proposals after a good origin under trivial frames -/

/-- The honest batch (A1.3) at a proposal of slot `σ + 1`, `σ ≥ r`. -/
private theorem trivial_batch_proposal (hS : StandaloneRun tr H U proposer g) {σ : Nat}
    (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {B : Blk sp.n FGP}
    (hB : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ → VoteExtends U e.msg B)
    (hlater : VotesExtendAfter tr H U σ B) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U B d.head := by
  have hrun := hS.run
  have hhalf := honest_voters_half hS.toHealthyBase hσ
  have hP : ∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = σ →
      e.msg ∈ (tr.state x i).pool σ ∧ ∃ R ∈ ℓ.frame.tree, R.root = e.msg.head ∧
        (R.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k R) := by
    intro z hz j e hv hes
    obtain ⟨hheld, hanc⟩ := honest_vote_at_proposal hS hx hc ht hσ hz hv hes
    obtain ⟨Hd, hHd, hHdr, -⟩ := hB z hz j e hv hes
    obtain ⟨hHdt, hacc⟩ := hanc Hd Hd hHd hHdr Relation.ReflTransGen.refl
    exact ⟨hheld, Hd, hHdt, hHdr, hacc⟩
  -- `B` is in the proposer's tree
  have hBt : B ∈ ℓ.frame.tree := by
    obtain ⟨w, hw, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero
      (s := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = σ})
      (by have := hS.two_faulty_lt; omega)
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hB w hw j e hv hes
    exact ((honest_vote_at_proposal hS hx hc ht hσ hw hv hes).2 B Hd hHd hHdr hBHd).1
  exact batch_proposal hrun hS.two_faulty_lt hhalf hB hx hc (proposal_slot ht) hprop
    (trivial_viable_at hS hx hc hBt)
    (fun z hz j e hv hes =>
      let ⟨hheld, R, hR, hRr, hacc⟩ := hP z hz j e hv hes
      heldAtProposal_iff.2 ⟨Or.inl hheld, R, hR, hRr, trivial_stamp hS hx hc hcall hR hacc⟩)
    (trivial_high_locks hS hx ht hlater fun _ _ _ hopt =>
      optimisticLock_compatible hrun hS.two_faulty_lt hx hopt hB)

/-- A fast update of slot `σ ≥ r` (A1.2) at the next proposal. -/
private theorem trivial_update_first_proposal (hS : StandaloneRun tr H U proposer g) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfu : FastUpdateAt tr X i₀ σ D CV) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ)
    (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓX, C, hupd, hconf, hfs, rfl⟩ := id hfu
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hr hX hupd.1
  have hDC : Anc U D C := Anc.mono hΦXU (deepest_mem hfs).1.1.2.2
  have hDt := result_block_at_proposal hS hX ⟨ℓX, hupd, hconf, rfl⟩ hσ hx hc ht hDC
  exact update_first_proposal hS.run hX hfu hx hc (proposal_slot ht) hprop
    (trivial_viable_at hS hx hc hDt) (trivial_counted_held hS hX hupd hσ hx hc hcall ht)
    (trivial_writer_pool hS hX hupd hσ hx ht)
    (trivial_high_locks hS hx ht hlater fun _ _ _ hopt =>
      fastLock_fastLock_compatible hS.toHealthyBase hx (Or.inr hopt) hX (Or.inl hfu)
        (by linarith))

/-- An optimistic confirmation of slot `σ ≥ r` (A1.4 (a)) at the next proposal. -/
private theorem trivial_optimistic_first_proposal (hS : StandaloneRun tr H U proposer g)
    {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt tr X i₀ σ D CV) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ)
    (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓX, A, hpt, hslX, hsel, rfl⟩ := id hopt
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hr hX hpt.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  have hDX := (deepest_mem hsel').1.1
  -- the optimistic check is in `[t_σ, t_σ + 2Δ)`
  have hti₀ : tr.time i₀ < sp.ts σ + 2 * sp.Δ := by
    rw [← hslX]; exact not_le.1 (not_or.1 (not_or.1 hcond).2).2
  have hearly : ∀ R ∈ ℓX.frame.tree, ∀ Y, Anc U Y R →
      Y ∈ ℓ.frame.tree ∧ (Y.root = sp.genesisRoot ∨ ∃ k < i, tr.AcceptAt x k Y) :=
    fun R hR Y hYR => early_block_at_proposal hS hx hc ht hσ (hΦXU hR)
      (Or.inr ⟨X, hX, i₀, ℓX, hpt.1, by linarith, hR⟩) hYR
  have hDt := (hearly D hDX D Relation.ReflTransGen.refl).1
  refine optimistic_first_proposal hS.run hS.two_faulty_lt hX hopt hx hc (proposal_slot ht)
    hprop (trivial_viable_at hS hx hc hDt) ?_
    (trivial_high_locks hS hx ht hlater fun _ _ _ hopt' =>
      fastLock_fastLock_compatible hS.toHealthyBase hx (Or.inr hopt') hX (Or.inr hopt)
        (by linarith))
  rintro v ⟨hv, R, hR, hRr, -⟩
  have hvs := optimisticPoint_pool_slot hr hX hpt hv
  obtain ⟨k, hk, hsend, h1, -⟩ := pool_sent hr hX (fun _ _ hrk => restart_before hS hX hσ hrk)
    (optimisticPoint_pool_post hr hX hpt σ hv)
  have hkt : tr.time k < sp.ts σ + 3 * sp.Δ :=
    lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) (by linarith)
  obtain ⟨hRt, hRacc⟩ := hearly R hR R Relation.ReflTransGen.refl
  exact heldAtProposal_iff.2 ⟨proposal_forward hS hx hc ht hσ hX hsend hvs h1 hkt, R, hRt, hRr,
    trivial_stamp hS hx hc hcall hRt hRacc⟩

/-- A slow origin of slot `σ` whose window is `≥ r` (A1.8 for its block `D ⪯ C`) at the next
proposal: every stored live lock there is compatible with `D` (same-slot compatibility against
the writer's saved results, and the optimistic locks of later slots over votes extending `D`). -/
private theorem trivial_slow_first_proposal (hS : StandaloneRun tr H U proposer g) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ σ : Nat} {D : Blk sp.n FGP} (hsl : SlowLockAt tr X i₀ σ D)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts ((σ : Int) - sp.k + 1))
    (hlater : VotesExtendAfter tr H U σ D) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) (hcall : ℓ.call = .proposal)
    (ht : tr.time i = sp.ts (σ + 1 : Nat)) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay)) :
    Anc U D d.head := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hk := sp.two_le_k
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := id hsl
  have hres : ResultAt tr X i₀ σ C (fastCounted sp (tr.state X i₀) ℓX.frame σ C) :=
    ⟨ℓX, hupd, hconf, rfl⟩
  have hΦXU := (frameIn_of_callAt hr hX hupd.1).2
  obtain ⟨⟨-, -, hDC⟩, -⟩ := (deepest_mem hdeep).1
  have hDC' : Anc U D C := Anc.mono hΦXU hDC
  have hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ := hs.trans ((ts_le_iff sp).2 (by omega))
  have hDt := result_block_at_proposal hS hX hres hσ hx hc ht hDC'
  -- every stored live lock is compatible with `D`
  have hall : ∀ l ∈ (tr.state x i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → ∀ Y ∈ U,
      Y.root = l.block → Compatible U Y D := by
    intro l hl hlive Y hY hYr
    rcases le_or_gt l.slot σ with hle | hlt
    · exact slow_stored_locks hS.toHealthyBase hX hsl hs hx (by rw [proposal_slot ht]) l hl hlive
        hle Y hY hYr
    · obtain ⟨O, hYO, k, CV', hopt⟩ := proposal_high_lock hr hx ht hl hlt.le hY hYr
      exact compat_down hU hYO (optimisticLock_compatible hrun hS.two_faulty_lt hx hopt
        fun w hw j e hv hs => votesExtendAfter_iff.1 hlater w hw j e hv (by omega))
  exact result_first_proposal hrun hX hres hDC' hx hc (proposal_slot ht) hprop
    (trivial_viable_at hS hx hc hDt) (trivial_counted_held hS hX hupd hσ hx hc hcall ht)
    (trivial_writer_pool hS hX hupd hσ hx ht)
    (lowLocksCompatible_iff.2 fun l hl hlive _ => hall l hl hlive)
    (highLocksCompatible_iff.2 fun l hl hlive _ => hall l hl hlive)

/-! ## Assembly -/

/-- **A good origin transfers to the proposals** (the transfer at the proposal duty): if every
honest vote of a slot after the label `j` of a good origin on `B` extends `B`, the head of every
honest proposal of a slot after `j` extends `B`: the first one by the origin's argument, the
later ones by the honest batch. -/
theorem proposals_extend_of_origin (hS : StandaloneRun tr H U proposer g)
    {B : Blk sp.n FGP} {j : Nat}
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
    · exact trivial_update_first_proposal hS hX hfu hσ hvotes hx hc hcall ht hprop
    · exact trivial_optimistic_first_proposal hS hX hopt hσ hvotes hx hc hcall ht hprop
    · exact trivial_slow_first_proposal hS hX hsl hs hvotes hx hc hcall ht hprop
  · exact trivial_batch_proposal hS hσ (fun z hz j' e hv hs =>
      votesExtendAfter_iff.1 hvotes z hz j' e hv (by omega))
      (votesExtendAfter_iff.2 fun z hz j' e hv hs =>
        votesExtendAfter_iff.1 hvotes z hz j' e hv (by omega)) hx hc hcall ht hprop

end Consensus.Goldilocks.SA

end
