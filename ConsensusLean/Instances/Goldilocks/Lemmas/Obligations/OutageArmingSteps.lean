module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks outage: the arming steps (cover label, saved attestations, slow-lock formation)

For an outage `[b₀, b₁)` armed at `T` under the lag `(4k+6)Δ` (node units), every origin `C`
within `T` has a label `σ` with `σ + k < j₀`, `j₀ := coverLabel b₀` (`armed_label_lt`); the saved
attestations of an update are above `C` (`saved_rows_above`); an own optimistic selection is
compatible with a later result of the same label (`own_optimistic_compatible_result`); and the pure
SA formation of a slow lock (`updateConfirmation_slow_lock_effective`). -/

namespace Consensus.Goldilocks.SA

/-- An ancestor of a block that conflicts with no live lock conflicts with no live lock. -/
theorem not_conflictsWithLock_of_anc {FGP : Type} {sp : SAParams} {L : Set Lock}
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {C D : Blk sp.n FGP} (hCD : Φ.Anc C D)
    (hnv : ¬ conflictsWithLock sp L Φ t D) : ¬ conflictsWithLock sp L Φ t C := by
  rintro ⟨W, hW, hCW⟩
  refine hnv ⟨W, hW, fun hDW => hCW ?_⟩
  rcases hDW with h | h
  · exact Or.inl (hCD.trans h)
  · exact anc_total hΦ.coherent hCD h

/-- **Slow formation** (independent writes): attestations above `C`, a result `D ⪰ C`, and no
live lock conflicting with `C` store the slow lock of slot `s` and expiry `s + k` on the viable
ancestor of the deepest unvetoed slow-test block `X`, `C ⪯ X ⪯ D`. A veto of `D` stops only the
record. -/
theorem updateConfirmation_slow_lock_of {FGP : Type} {sp : SAParams} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Nat} {C D : Blk sp.n FGP}
    (hD : getConfirmation sp A Φ s = some D) (hnvC : ¬ conflictsWithLock sp A.locks Φ t C)
    (hCt : C ∈ Φ.tree) (hCg : C.root ≠ sp.genesisRoot) (hCD : Φ.Anc C D)
    (hrows : ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc C S)
    (hlive : sp.slot t ≤ s + sp.k) :
    ∃ X, X ∈ Φ.tree ∧ Φ.Anc C X ∧ Φ.Anc X D ∧
      (⟨(Φ.viableAncestor X).root, s, false, s + sp.k⟩ : Lock) ∈
        (updateConfirmation sp A Φ t s).locks := by
  classical
  set S : Set (Blk sp.n FGP) := {B | B ∈ {B | B ∈ confirmationPath sp Φ D ∧
      ¬ conflictsWithLock sp A.locks Φ t B} ∧
    ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ Φ.tree,
      (Function.update A.saved s ((some D).map Block.root)) j = some S.root ∧ Φ.Anc B S}
  have hSt : S ⊆ Φ.tree := fun B hB => hB.1.1.1
  have hCS : C ∈ S := by
    refine ⟨⟨⟨hCt, hCg, hCD⟩, hnvC⟩, fun j hj₁ hj₂ => ?_⟩
    obtain ⟨S', hS', hsv, hCS'⟩ := hrows j hj₁ hj₂
    exact ⟨S', hS', by rw [Function.update_of_ne (by omega)]; exact hsv, hCS'⟩
  have hch : ∀ B ∈ S, ∀ B' ∈ S, Compatible Φ.tree B B' := fun B hB B' hB' =>
    anc_total hΦ.coherent hB.1.1.2.2 hB'.1.1.2.2
  obtain ⟨X, hX⟩ := exists_deepest hΦ hSt ⟨C, hCS⟩
  have hXS := (deepest_mem hX).1
  refine ⟨X, hSt hXS, anc_deepest hΦ hSt hch hX C hCS, hXS.1.1.2.2, ?_⟩
  have hlocks : ∀ A₂ : SAState sp.n, A₂.locks = A.locks →
      (⟨(Φ.viableAncestor X).root, s, false, s + sp.k⟩ : Lock) ∈ addLocks sp A₂.locks Φ t s
        {p | (∃ B, deepest Φ {B | B ∈ {B | B ∈ confirmationPath sp Φ D ∧
            ¬ conflictsWithLock sp A.locks Φ t B} ∧ FastTest sp A Φ s B} = some B ∧
            p = (B.root, true, fastExpiry sp A₂.locks Φ t s)) ∨
          (∃ B, deepest Φ S = some B ∧ p = (B.root, false, s + sp.k))} := by
    intro A₂ hA₂
    exact ⟨⟨X.root, s, false, s + sp.k⟩, Or.inr ⟨_, Or.inr ⟨X, hX, rfl⟩, rfl⟩, X, hSt hXS, rfl,
      hlive, rfl⟩
  simp only [updateConfirmation, hD]
  split_ifs
  · exact hlocks _ rfl
  · exact hlocks _ (updateLatestConfirmed_keeps_locks _ _ _)

/-- **Effective slow formation**: with `C` a candidate of `viable_ancestor` and unvetoed, the stored
slow block extends `C` (`anc_viableAncestor_of_candidate`). -/
theorem updateConfirmation_slow_lock_effective_of {FGP : Type} {sp : SAParams}
    {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Nat}
    {C D : Blk sp.n FGP} (hD : getConfirmation sp A Φ s = some D)
    (hnvC : ¬ conflictsWithLock sp A.locks Φ t C)
    (hCt : C ∈ Φ.tree) (hCg : C.root ≠ sp.genesisRoot) (hCD : Φ.Anc C D)
    (hrows : ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc C S)
    (hlive : sp.slot t ≤ s + sp.k) (hcand : Φ.AncestorCandidate C) :
    ∃ L, L ∈ Φ.tree ∧ Φ.Anc C L ∧
      (⟨L.root, s, false, s + sp.k⟩ : Lock) ∈ (updateConfirmation sp A Φ t s).locks := by
  obtain ⟨X, hX, hCX, -, hl⟩ :=
    updateConfirmation_slow_lock_of hΦ hD hnvC hCt hCg hCD hrows hlive
  exact ⟨Φ.viableAncestor X, (viableAncestor_anc hΦ hX).1,
    anc_viableAncestor_of_candidate hΦ hcand.symm hX hCX, hl⟩

/-- **Effective slow formation**: with `C` a candidate of `viable_ancestor`, the stored block
extends `C` (`anc_viableAncestor_of_candidate`). -/
theorem updateConfirmation_slow_lock_effective {FGP : Type} {sp : SAParams} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Nat} {C D : Blk sp.n FGP}
    (hD : getConfirmation sp A Φ s = some D) (hnv : ¬ conflictsWithLock sp A.locks Φ t D)
    (hCt : C ∈ Φ.tree) (hCg : C.root ≠ sp.genesisRoot) (hCD : Φ.Anc C D)
    (hrows : ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc C S)
    (hlive : sp.slot t ≤ s + sp.k) (hcand : Φ.AncestorCandidate C) :
    ∃ L f, L ∈ Φ.tree ∧ Φ.Anc C L ∧
      (⟨L.root, s, f, s + sp.k⟩ : Lock) ∈ (updateConfirmation sp A Φ t s).locks := by
  obtain ⟨L, hL, hCL, hl⟩ := updateConfirmation_slow_lock_effective_of hΦ hD
    (not_conflictsWithLock_of_anc hΦ hCD hnv) hCt hCg hCD hrows hlive hcand
  exact ⟨L, false, hL, hCL, hl⟩

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-! ### The arithmetic -/

/-- The cover label of an outage start `b₀`: the label whose update `t_j + 6Δ` is the first
after `b₀` (archive `coverLabel` for `b₀ ≥ 6Δ`). -/
def coverLabel (sp : SAParams) (b₀ : Time) : Nat := sp.slot (b₀ - 2 * sp.Δ)

theorem coverLabel_eq (sp : SAParams) (b₀ : Time) :
    coverLabel sp b₀ = sp.slot (b₀ - 2 * sp.Δ) := by rfl

/-- The cover gates: the update of `j₀ − 1` is by `b₀`, that of `j₀` after it. -/
theorem coverLabel_gates {b₀ : Time} (hb : 2 * sp.Δ ≤ b₀) :
    sp.ts (coverLabel sp b₀) + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (coverLabel sp b₀) + 6 * sp.Δ := by
  have hu : 0 ≤ b₀ - 2 * sp.Δ := by linarith
  have h1 := (SA.ts_le_iff_le_slot sp hu (coverLabel sp b₀)).2 le_rfl
  have h2 : ¬ sp.ts ((coverLabel sp b₀ : Int) + 1) ≤ b₀ - 2 * sp.Δ := fun h => by
    have := (SA.ts_le_iff_le_slot sp hu _).1 h
    rw [coverLabel_eq] at this
    omega
  simp only [SAParams.ts] at h1 h2 ⊢
  constructor <;> linarith

/-- (A3)/(A4) The outage lag puts every armed origin label more than `k` labels before the cover
label, and the cover label after `k`. -/
theorem armed_label_lt {T b₀ : Time} {σ : Nat} (hT : 0 ≤ T)
    (hlag : T + (4 * sp.k + 6) * sp.Δ ≤ b₀) (hσ : sp.ts σ ≤ T) :
    σ + sp.k < coverLabel sp b₀ ∧ sp.k < coverLabel sp b₀ := by
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := by positivity
  obtain ⟨-, hlt⟩ := coverLabel_gates (sp := sp) (b₀ := b₀) (by linarith [mul_nonneg hk hΔ.le])
  have h1 : sp.ts ((σ : Int) + sp.k) < sp.ts (coverLabel sp b₀) := by
    simp only [SAParams.ts] at hσ hlt ⊢
    linarith
  have h2 : sp.ts (sp.k : Int) < sp.ts (coverLabel sp b₀) := by
    have h0 : (0 : Time) ≤ sp.ts σ := by simp only [SAParams.ts]; positivity
    simp only [SAParams.ts] at hσ hlt h0 ⊢
    linarith
  have h1' := (SA.ts_lt_iff sp).1 h1
  have h2' := (SA.ts_lt_iff sp).1 h2
  constructor <;> omega

/-! ### S-vote -/

/-! ### The receiver epoch -/

/-! ### The saved attestations -/

/-- The frame of an update is the node's frame at the update's cut. -/
theorem update_frame {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y c s ℓ) :
    ℓ.frame = Node.frame (tr.state y c) := by
  obtain ⟨⟨hn, hl⟩, -⟩ := hu
  obtain ⟨cl, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
  obtain rfl : cl = .ac ℓ := by
    cases cl with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  exact (hrun.cutLaw y hy c (.ac ℓ) ⟨hn, hc⟩).1

/-- **The saved attestations** at an update of slot `s ≥ k`: from attestation updates before
it, no restart after the oldest attestation start, and a result above `C` at every attestation
update, every attestation of the slow test names a block of the frame above `C`. -/
theorem saved_rows_above {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y c s ℓ) (hks : sp.k ≤ s)
    (hFC : Anc (tr.HonestBlocks H) (tr.state y c).fg.F C)
    (hCt : C ∈ (tr.state y c).fg.tree)
    (hnr : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts ((s : Int) - sp.k + 1))
    (hex : ∀ q : Nat, (s : Int) - sp.k < q → q < s →
      ∃ k < c, ∃ ℓ', SA.UpdateAt tr.projAC y k q ℓ')
    (hrow : ∀ q : Nat, (s : Int) - sp.k < q → q < s → ∀ k < c, ∀ ℓ',
      SA.UpdateAt tr.projAC y k q ℓ' → ∃ R, SA.getConfirmation sp (tr.state y k).ac
        ℓ'.frame q = some R ∧ Anc (tr.HonestBlocks H) C R) :
    ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ ℓ.frame.tree,
      (tr.state y c).ac.saved j = some S.root ∧ ℓ.frame.Anc C S := by
  have hrun' := goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hfr := update_frame hrun hy hu
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy c
  have hHB : ℓ.frame.tree ⊆ tr.HonestBlocks H := fun X hX =>
    ⟨y, hy, c, by rw [hfr] at hX; exact hX.1⟩
  have hCΦ : C ∈ ℓ.frame.tree := by
    rw [hfr]; exact ⟨hCt, honest_held_anc hrun hnc hy hFC hCt⟩
  intro j hj₁ hj₂
  obtain ⟨q, rfl⟩ : ∃ q : Nat, j = q := ⟨j.toNat, by omega⟩
  have hq₂ : q < s := by exact_mod_cast hj₂
  obtain ⟨k₀, hk₀, ℓ₀, hu₀⟩ := hex q hj₁ hq₂
  have hk₀t : tr.time k₀ = sp.ts q + 6 * sp.Δ := hu₀.2.2.1
  have hlow : sp.ts ((s : Int) - sp.k + 1) ≤ sp.ts q := (SA.ts_le_iff sp).2 (by omega)
  -- no restart of `y` in `(k₀, c]`
  have hnr' : ∀ i, k₀ < i → i ≤ c → ¬ tr.projAC.RestartAt y i := by
    rintro i hi hic ⟨ℓr, hcr, hrr⟩
    have h1 := hnr i hic ⟨ℓr, projAC_callAt.1 hcr, hrr⟩
    have h2 := hrun.time_mono hi.le
    linarith
  -- `saved[q]` stays set from the update `k₀` to `c`
  have hsome : ∀ i, k₀ + 1 ≤ i → i ≤ c → ((tr.projAC.state y i).saved q).isSome := by
    intro i hi hic
    induction i, hi using Nat.le_induction with
    | base =>
      rw [SA.saved_after_update hr hy hu₀, Function.update_self]
      obtain ⟨R, hR, -⟩ := hrow q hj₁ hq₂ k₀ hk₀ ℓ₀ hu₀
      rw [projAC_state hrun.toLocalRun hy, hR]
      rfl
    | succ i hi ih =>
      rcases SA.saved_step_of_not_restart hr hy i q (hnr' i (by omega) (by omega)) with
        h | ⟨ℓ', hu', h⟩
      · rw [h]; exact ih (by omega)
      · obtain ⟨R, hR, -⟩ := hrow q hj₁ hq₂ i (by omega) ℓ' hu'
        rw [h, projAC_state hrun.toLocalRun hy, hR]
        rfl
  obtain ⟨r, hrs⟩ := Option.isSome_iff_exists.1 (hsome c hk₀ le_rfl)
  obtain ⟨k', hk', C', CV, ⟨ℓ', hu', hC', -⟩, hC'r⟩ := SA.saved_result hr hrun.vstart hy c q hrs
  obtain ⟨R, hR, hCR⟩ := hrow q hj₁ hq₂ k' hk' ℓ' hu'
  rw [projAC_state hrun.toLocalRun hy, hR] at hC'
  obtain rfl : R = C' := Option.some.inj hC'
  have hfr' := update_frame hrun hy hu'
  have hRt : R ∈ (tr.state y k').fg.tree := by
    have h := (SA.deepest_mem hR).1.1
    rw [hfr'] at h
    exact h.1
  have hRc := tree_mono hrun.toLocalRun hy hk'.le hRt
  have hRΦ : R ∈ ℓ.frame.tree := by
    rw [hfr]; exact ⟨hRc, honest_held_anc hrun hnc hy (hFC.trans hCR) hRc⟩
  refine ⟨R, hRΦ, ?_, SA.anc_tree_of_anc_U hU hΦ hHB hCΦ hCR hRΦ⟩
  rw [← projAC_state hrun.toLocalRun hy, hrs, hC'r]

/-! ### The veto analysis at the cover gate -/

/-- **An own optimistic selection is compatible with a later result of the same label**: its three
quarters of optimistic voters are in the updater's slot-`s` pool at the result (no restart in
between), and none of them supports a conflicting block, so a conflicting result would have at most
a quarter of the committee as supporters, not a majority. -/
theorem own_optimistic_compatible_result {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hP : SA.CommitteeP K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {y : Fin sp.n} (hy : y ∈ H)
    {k c s : Nat}
    {B' D : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (SA.Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC y k s B' CV) (hR : SA.ResultAt tr.projAC y c s D CV')
    (hkc : k < c) (hnr : ∀ r, k < r → r ≤ c → ¬ tr.RestartAt y r) :
    Compatible (tr.HonestBlocks H) B' D := by
  have hrun' := goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  obtain ⟨-, hcnt, ell, A, hp, -, hCV, -⟩ := SA.optimisticLockAt_spec hrun' hy hO K
    (hP.1 y hy (k + 1))
  obtain ⟨ℓ, hu, hD, -⟩ := hR
  have hΦU := (SA.frameIn_of_callAt hr hy hp.1).2
  have hΦU' := (SA.frameIn_of_callAt hr hy hu.1).2
  -- the optimistic pool is in the pool at the result
  have hsub : ∀ v ∈ A.pool s, v ∈ (tr.projAC.state y c).pool s := fun v hv =>
    SA.pool_mono hr hy (show k + 1 ≤ c by omega)
      (fun r hr₁ hr₂ ⟨ℓr, hcr, hrr⟩ => hnr r (by omega) hr₂.le ⟨ℓr, projAC_callAt.1 hcr, hrr⟩) s
      (SA.optimisticPoint_pool_post hr hy hp s hv)
  set V : SA.View sp.n := ⟨{v | v ∈ (tr.projAC.state y c).pool s},
    {v | v ∈ (tr.projAC.state y c).pool s ∧ SA.resolutionTime (tr.projAC.state y c) ℓ.frame v <
      SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hmaj : (SA.voters {v | v ∈ (tr.projAC.state y c).pool s}).ncard <
      2 * (SA.supporters ℓ.frame V s D).ncard := (SA.deepest_mem hD).1.2.2
  by_contra hconf
  -- no optimistic voter supports `D`
  have hdisj : Disjoint (SA.voters CV) (SA.supporters ℓ.frame V s D) := by
    refine Set.disjoint_left.2 ?_
    rintro i ⟨v, hv, rfl⟩ ⟨heq, x, ⟨hx, -⟩, hxi, -, R, hR, hRr, hDR⟩
    obtain ⟨hvA, hvs, R', hR', hR'r, hBR'⟩ := hCV v hv
    have hxv : x = v := by
      by_contra hne
      exact heq ⟨x, hx, v, hsub v hvA, hne, hxi, rfl⟩
    subst hxv
    obtain rfl : R' = R := hU.1 (hΦU hR') (hΦU' hR) (hR'r.trans hRr.symm)
    exact hconf (SA.anc_total hU (hBR'.mono hΦU) (hDR.mono hΦU'))
  have hvv : SA.voters CV ⊆ SA.voters {v | v ∈ (tr.projAC.state y c).pool s} := by
    rintro i ⟨v, hv, rfl⟩
    exact ⟨v, hsub v (hCV v hv).1, rfl⟩
  have h1 := Set.ncard_le_ncard hvv (Set.toFinite _)
  have h2 : (SA.voters CV ∪ SA.supporters ℓ.frame V s D).ncard ≤ sp.committeeSize := by
    rw [← hsize s]
    refine Set.ncard_le_ncard (Set.union_subset (hvv.trans ?_) ?_) (Set.toFinite _)
    · rintro i ⟨v, hv, rfl⟩
      exact (hP.1 y hy c s v hv)
    · rintro i ⟨-, v, ⟨hv, -⟩, rfl, -⟩
      exact hP.1 y hy c s v hv
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at h2
  omega

end Consensus.Goldilocks.Compose

end
