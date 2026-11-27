module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.VoteDomain

public section

/-! # P-U shadow kernel: the retained-vote induction and R1

The stock healing kernel's R1 chain over the shadow run:

* `KernelProof.high_origin_votes_of_domain_before_at'` (HighInduction): the strong induction on
  the cut, the vote domain an explicit input; stock proof.
* `ResetPremisesUpTo'.high_origin_votes_before_at'` (ResetFacts, R2): the deep quarantine arm
  plugs in the P-U vote domain (`held_target_vote_domain_before_of_quarantine_at'`); the cover
  arm is S2 of the high-source cover; stock proof.
* `ResetPremisesUpTo'.origins_compatible_at'` (ResetFacts, R1) and
  `ProposalImpl.finalized_compatible_high_origin_at'` (Pivot/OldSources); stock proofs.

The two frame-agnostic layers below the induction are named **interface stubs** in section
`Stub`: `high_vote_extends_of_domain_at'` (HighVote, with HighCarry) and
`origins_compatible_before_at'` (OriginCompare, with OriginLabel/HighOriginSources/LockWriter). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The cast law at a node honest at the cast (`Compose.Growing.castAt_spec_at`). -/
theorem castAt_spec_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode' sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ AC.joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (AC.getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (AC.voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  have hd := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo hd) (hnc.upTo _)).localRun
  have hc' : AC.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e := by
    rw [RunTrace.upTo_projAC]
    exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  exact AC.castAt_specU hr.toU hy hc'

/-- An origin above the frame's finalized tip is held by every later-label honest voter
(`KernelProof.high_origin_held_at_vote_at`). -/
theorem KernelProof.high_origin_held_at_vote_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r l k : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    O ∈ (tr.state y k).fg.tree := by
  obtain ⟨W, hW, hOW⟩ := Stub.high_origin_frozen_head_at' hp ho hrb hy hc hl hFO
  have hWy := (Shadow.PU.Growing.frame_tree_subset_at' hp.run hp.noColl hy hc.1).2 hW.1
  exact Compose.FrameGeometry.anc_mem (Coherence.held_anc_at' hp.run hp.noColl
    (hp.run.time_nonneg k) hy (fun _ hq => hp.run.time_mono hq.le) hOW hWy) hWy

/-- A high origin above a later honest cast's finalized tip is in its voter block tree
(`ResetPremisesUpTo.high_origin_held_at_vote_at`, `Outcome/VoteReceipt`): the voter block
tree is closed under ancestors and holds the origin's frozen head. -/
theorem ResetPremisesUpTo'.high_origin_held_at_vote_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hj : j < e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  obtain ⟨W, hW, hBW⟩ := Stub.high_origin_frozen_head_at' hp ho hib hy hc hj hF
  have hd := hp.run.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono hq.le
  have hr := (Compose.goldilocks_ac_projection_from' (hp.run.upTo hd)
    (hp.noColl.upTo _)).localRun
  have hc' : AC.CastAt (tr.upTo (tr.time k)).projAC y k ell e := by
    rw [RunTrace.upTo_projAC]
    exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hfr := Shadow.PU.Growing.frame_of_projAC_at' hp.run hy hc.1
  have hFe : ell.frame.F = (tr.state y k).fg.F := by rw [hfr, Node.frame'_eq, toFrame'_F]
  have hWs : W ∈ (tr.state y k).fg.tree ∧ (tr.state y k).fg.Anc (tr.state y k).fg.F W := by
    have h := hfr ▸ hW.1
    rwa [Node.frame'_eq, toFrame'_tree] at h
  have hBWs := Coherence.held_anc_at' hp.run hp.noColl hd hy hle hBW hWs.1
  have hBs := Compose.FrameGeometry.anc_mem hBWs hWs.1
  have hFBs := Coherence.held_anc_at' hp.run hp.noColl hd hy hle (hFe ▸ hF) hBs
  have hΦBW : ell.frame.Anc B W := by
    rw [hfr, Node.frame'_eq]
    simp only [Frame.Anc, toFrame'_tree]
    exact Anc.restrict hFBs hBWs
  exact AC.voterBlockTree_ancU hr.toU (hp.run.upTo hd).vstart hy hc' W hW B hΦBW

namespace Stub

/-- **Interface stub** (`KernelProof.high_vote_extends_of_domain_at`, `Kernel/HighVote`). -/
theorem high_vote_extends_of_domain_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b) (hj : j < e.msg.slot)
    (hvi : Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      j < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

/-- **Interface stub** (`KernelProof.origins_compatible_before_at`, `Kernel/OriginCompare`). -/
theorem origins_compatible_before_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold) {k : Nat}
    (hvote : ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ z c e, c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
        AC.VoteAt tr.projAC z c e → j < e.msg.slot →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) (hrk : r < k) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

end Stub

/-- **The retained-vote induction**, given the finite held-target domain
(`KernelProof.high_origin_votes_of_domain_before_at`). -/
theorem KernelProof.high_origin_votes_of_domain_before_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    (hdomain : ∀ {x y v : Fin sp.n} {r i q m : Nat}
      {B S : AC.Blk sp.n (List (FG.Att sp.n))},
      x ∈ H (tr.time r) → y ∈ H (tr.time i) →
      B ∈ (tr.state x r).fg.tree → tr.time r ≤ b →
      ∀ {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))},
      AC.CastAt tr.projAC y i ell e → tr.time i ≤ b →
      (Anc (tr.HonestBlocksAt H) ell.frame.F B →
        B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) →
      HighOrigin tr H g v q m S → tr.time q ≤ b → m < e.msg.slot →
      Compatible (tr.HonestBlocksAt H) B S →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) B O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) S O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O') →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkb x i j B ho hib y ell e hy hc hj
    have prior : ∀ x₀ i₀ j₀ B₀, HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
        ∀ z c e', c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
          AC.VoteAt tr.projAC z c e' → j₀ < e'.msg.slot →
            AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B₀ := by
      rintro x₀ i₀ j₀ B₀ ho₀ hi₀ z c e' hck hz hcb ⟨ell', hc'⟩ hj'
      exact ih c hck hcb x₀ i₀ j₀ B₀ ho₀ hi₀ z ell' e' hz hc' hj'
    have hslot := (castAt_spec_at' hp.run hp.noColl hy hc).2.1
    have hts : sp.ts e.msg.slot ≤ tr.time k :=
      (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mpr (by rw [hslot])
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      ((AC.ts_le_iff sp).mpr (by omega)).trans hts
    have compare : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) B O := by
      intro z d n O hd hO
      exact Stub.origins_compatible_before_at' hp prior ho hib
        (Or.inr fun c hct => not_le.mp fun hkc =>
          (not_lt_of_ge (hact.trans (hp.run.time_mono hkc))) hct)
        hO ((hp.run.time_mono hd.le).trans hkb) hd
    have pair : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < k → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O' := by
      intro z d n O hd hO z' d' n' O' hd' hO'
      exact Stub.origins_compatible_before_at' hp prior hO
        ((hp.run.time_mono hd.le).trans hkb) (Or.inl hd) hO'
        ((hp.run.time_mono hd'.le).trans hkb) hd'
    have hvi := hdomain (hp.run.antitone (le_max_right _ _) ho.1) hy
      (Outcome.high_origin_mem_at' hp.run hp.noColl ho) hib hc hkb
      (hp.high_origin_held_at_vote_at' ho hib hy hc hkb hj) ho hib hj
      (Or.inl .refl) compare compare pair
    exact Stub.high_vote_extends_of_domain_at' hp ho hy hc hkb hj hvi
      (fun z q e' hq hv hs => prior x i j B ho hib z q e' hq
        (Compose.Growing.hVoteAt_iff.1 hv).1 ((hp.run.time_mono hq.le).trans hkb)
        (Compose.Growing.hVoteAt_iff.1 hv).2 hs)

/-- **R2 over the shadow run** (`ResetPremisesUpTo.high_origin_votes_before_at`): every
later-label honest cast extends each high origin within the finite horizon. -/
theorem ResetPremisesUpTo'.high_origin_votes_before_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hcase : (∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · exact Or.inl fun D' hD' => by cases hD'; exact hb
      · exact Or.inr hc
  rcases hcase with hpre | hc
  · exact KernelProof.high_origin_votes_of_domain_before_at' hp
      (fun hx hy hBx hrb _ _ hcast hib hheld hS hqb hm hBS hcompare hseedCompare hpair =>
        KernelProof.held_target_vote_domain_before_of_quarantine_at' hp hx hy hBx hrb hcast hib
          hheld hS hqb hm hBS hcompare hseedCompare hpair hpre)
  · intro k hkb x i j B ho hib y ell e hy hc' hj
    exact hc.s2 B j (Compose.Growing.HealedOrigin.of_high hib ho) y k e
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hc'⟩) hkb hj

/-- **R1 over the shadow run** (`ResetPremisesUpTo.origins_compatible_at`): high origins within
the horizon are comparable. -/
theorem ResetPremisesUpTo'.origins_compatible_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O := by
  apply Stub.origins_compatible_before_at' hp (k := max i r + 1) ?_
    ho hib (Or.inl (by omega)) hO hrb (by omega)
  intro x₀ i₀ j₀ B₀ ho₀ hi₀ y c e _ hy hcb hv hj
  obtain ⟨ell, hc⟩ := hv
  exact hp.high_origin_votes_before_at' c hcb x₀ i₀ j₀ B₀ ho₀ hi₀ y ell e hy hc hj

/-- A held block with the genesis root is below every held block (`genesis_root_anc_at`). -/
private theorem genesis_root_anc_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {G B : AC.Blk sp.n (List (FG.Att sp.n))} (hG : G ∈ tr.HonestBlocksAt H)
    (hg : G.root = sp.toParams.genesisRoot) (hB : B ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) G B := by
  obtain ⟨y, k, t, ht, hle, hy, hBt⟩ := hB
  have hfs := finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Compose.Growing.reachable_at' hrun ht hy hle).reachableWith
  have hh := (accepted_tree_with hfs hr).2.2.2 B hBt
  have hsub := Compose.Growing.tree_held_at' ht hy hle
  have he : G = sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload :=
    (Coherence.honestBlocksAt_coherent' hrun hnc).1 hG (hsub (genesis_mem_with hfs hr)) hg
  rw [he]
  exact hh.mono hsub

/-- **The finalized cache compares with a high origin** at independently honest cuts
(`ProposalImpl.finalized_compatible_high_origin_at`). -/
theorem ProposalImpl.finalized_compatible_high_origin_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {x : Fin sp.n} {i j : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (hib : tr.time i ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state z c).fg.F O := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hfs := finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Compose.Growing.reachable_at' hp.run ht hz hle).reachableWith
  have hU := Coherence.honestBlocksAt_coherent' hp.run hp.noColl
  have hsub := Compose.Growing.tree_held_at' ht hz hle
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := cache_invariants_with hfs hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := J_entry_with hfs hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact Or.inl ((hFJ.mono hsub).trans (genesis_root_anc_at' hp.run hp.noColl
        (hsub hJm) (congrArg (·.root) hg)
        ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hp.run.time_mono hq.le,
          hp.run.antitone (le_max_right _ _) ho.1,
          Outcome.high_origin_mem_at' hp.run hp.noColl ho⟩))
    · obtain ⟨_, _, _, _, v, d, _, hdc, _, _, hor⟩ :=
        hp.left_entry_origin_or_covered_at' ht hle hz hcb hJm hJT (by omega) hEC
          (by have := hj_lt_h_with hfs hr hC; omega)
      rcases hor with ⟨r, hrd, m, B, hB, hJB⟩ | ⟨-, hcov⟩
      · have hFB := (hFJ.mono hsub).trans hJB
        rcases hp.origins_compatible_at' hB
            ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
        · exact Or.inl (hFB.trans h)
        · exact Anc.total hU hFB h
      · exact (hcov.of_anc (hFJ.mono hsub)).compatible_highOrigin' hp.run hp.noColl hib ho
  · exact Or.inl (hp.low_finalized_below_origin_at' ht hle hz hcb (by omega) ho hib)

end Consensus.Goldilocks.Healing.Growing

end
