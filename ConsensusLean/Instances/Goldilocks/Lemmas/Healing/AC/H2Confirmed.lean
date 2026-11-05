module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.2 (ii), persistent inclusion after a unanimous honest proposal

The unanimous batch of slot `p` propagates to every later honest vote (`(P, p)` is protected by P3,
so `h2_votes_continue`); every surviving lock image compares with `P` (`h2_locks_compare`); the
record read by `ac_confirmed` extends `P` (`h2_record_extends`), and so does the head
(`h2_head_extends`); `ac_confirmed` is their deepest common ancestor (`anc_acConfirmed`, from the
frame lemma `anc_acConfirmed_of_frame` of `AC/Confirmed`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- The reads of H.2 (ii): calls of honest nodes from `t_p + 6Δ` on (at `t_p + 6Δ` itself,
from the node's tick there on). -/
def LateRead (tr : SATrace sp FGP ro) (p : Nat) (y : Fin sp.n) (j : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) : Prop :=
  tr.CallAt y j ℓ ∧ sp.ts p + 6 * sp.Δ ≤ tr.time j ∧
    (tr.time j = sp.ts p + 6 * sp.Δ →
      ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j)

/-- **All surviving lock images compare with `P`**: from `t_p` on, every stored lock of an honest
node live at a time `T ≥ t_p` is on a block compatible with `P`: a label `< p` sits below a clean
raw origin (`h2_drain`), which an honest slot-`p` vote extends with `P` (`raw_origin_votes`); a
label `≥ p` sits below a fast origin's block or a slow origin's result, which an honest vote of its
slot extends (the fast test or optimistic seats; the result's majority over all honest voters), and
that vote extends `P` (`h2_votes_continue`). -/
theorem h2_locks_compare (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P) :
    ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P := by
  have hrun := hI.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg := hI.le
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y P → Compatible U X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  -- two blocks extended by one honest vote compare
  have hcomp : ∀ {X Y : Blk sp.n FGP} {z : Fin sp.n}, z ∈ H → ∀ {j e}, VoteAt tr z j e →
      VoteExtends U e.msg X → VoteExtends U e.msg Y → Compatible U X Y := by
    intro X Y z hz j e hv ⟨Hd, hHd, hHdr, hXHd⟩ ⟨Hd', hHd', hHd'r, hYHd⟩
    obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
    exact anc_total hU hXHd hYHd
  intro y hy i T hT l hl hlive L hL hLr
  rcases Nat.lt_or_ge l.slot p with hlp | hpl
  · -- an older label: below a clean raw origin (drain), which an honest slot-`p` vote extends
    have hT0 : 0 ≤ T := by linarith [gbar_nonneg g]
    have hσ : t₀ + 2 * Θ sp ≤ sp.ts (sp.slot T) := by
      have h1 : ¬ sp.ts ((sp.slot T : Nat) + 1 : Int) ≤ T := by
        rw [ts_le_iff_le_slot sp hT0]; omega
      have h2 : sp.ts ((sp.slot T : Nat) + 1 : Int) = sp.ts (sp.slot T) + 4 * sp.Δ := by
        simp only [SAParams.ts]; ring
      linarith [not_le.1 h1]
    obtain ⟨B, ⟨L', hL', hL'r, hL'B⟩, hclean⟩ := h2_drain hI hy hl hlive hσ
    obtain rfl : L' = L := hU.1 hL' hL (hL'r.trans hLr.symm)
    obtain ⟨j, e, hve, hes⟩ := honest_votes_in_slot hI.toHealthyBase
      (show gbar g + 4 * sp.Δ ≤ sp.ts p by linarith) y hy
    exact down hL'B (hcomp hy hve (votesExtendAfter_iff.1 (raw_origin_votes hI hclean) y hy j e hve
      (by omega)) (hvotes y hy j e hve hes.ge))
  · have hlg : gbar g + 4 * sp.Δ ≤ sp.ts l.slot :=
      (show gbar g + 4 * sp.Δ ≤ sp.ts p by linarith).trans ((ts_le_iff sp).2 (by omega))
    cases hf : l.fast
    · -- a slow lock: below the result of its update, which has an honest supporter
      obtain ⟨j, -, D, hsl, L', hL', hL'r, hL'D⟩ := slow_lock_provenance hr hy i l hl hf
      obtain rfl : L' = L := hU.1 hL' hL (hL'r.trans hLr.symm)
      obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := hsl
      have hΦXU := (frameIn_of_callAt hr hy hupd.1).2
      have hDC : Anc U D C := Anc.mono hΦXU (deepest_mem hdeep).1.1.2.2
      obtain ⟨z, hz, j', e, hve, hes, hext⟩ :=
        result_honest_supporter hI hy (⟨ℓX, hupd, hconf, rfl⟩ : ResultAt tr y j l.slot C _) hlg
      exact down (hL'D.trans hDC) (hcomp hz hve hext (hvotes z hz j' e hve (hes ▸ hpl)))
    · -- a fast lock: an honest vote of its slot extends its block
      obtain ⟨j, -, B, CV, hfl, L', hL', hL'r, hL'B⟩ := fast_lock_provenance hr hy i l hl hf
      obtain rfl : L' = L := hU.1 hL' hL (hL'r.trans hLr.symm)
      obtain ⟨z, hz, j', e, hve, hes, hext⟩ := fastLock_honest_vote hrun hI.two_faulty_lt hy hfl
      exact down hL'B (hcomp hz hve hext (hvotes z hz j' e hve (hes ▸ hpl)))

/-! ## Helpers: the record read by `ac_confirmed`, the head from `fc_root` -/

/-- With `P ⪯ Φ.F`, the record read in `Φ` (the record's block, else `Φ.F`) extends `P`. -/
private theorem rec_of_F {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {P : Blk sp.n FGP} (h : Anc U P Φ.F) (r : Nat) : Anc U P ((lookup Φ r).getD Φ.F) := by
  cases hl : lookup Φ r with
  | none => exact h
  | some R => exact h.trans ((hΦ.rooted.2 R (lookup_eq_some hl).1).mono hΦU)

/-- A record naming a block of `Φ` that extends `P` is read as that block. -/
private theorem rec_of_mem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {P R : Blk sp.n FGP}
    (hR : R ∈ Φ.tree) {r : Nat} (hRr : R.root = r) (hPR : Anc U P R) :
    Anc U P ((lookup Φ r).getD Φ.F) := by
  cases hl : lookup Φ r with
  | none => exact absurd ⟨R, hR, hRr⟩ (lookup_eq_none hl)
  | some R' =>
    obtain ⟨hR', hR'r⟩ := lookup_eq_some hl
    change Anc U P R'
    rwa [hΦ.coherent.1 hR' hR (hR'r.trans hRr.symm)]

/-- When `P ⋠ Φ.F` and `P` is in the tree, a record read extending `P` names a tree block
extending `P`. -/
private theorem rec_to_tree (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {P : Blk sp.n FGP} (hPF : ¬ Anc U P Φ.F) (hPt : P ∈ Φ.tree) {r : Nat}
    (h : Anc U P ((lookup Φ r).getD Φ.F)) : ∃ R ∈ Φ.tree, R.root = r ∧ Φ.Anc P R := by
  cases hl : lookup Φ r with
  | none => rw [hl] at h; exact absurd h hPF
  | some R =>
    rw [hl] at h
    obtain ⟨hR, hRr⟩ := lookup_eq_some hl
    exact ⟨R, hR, hRr, anc_tree_of_anc_U hU hΦ hΦU hPt h hR⟩

/-- **Frame changes**: across a frame step `Φ ⊑_B Φ'` with `P ⪯ Φ'.fc_root` or `P` viable in
`Φ'`, the record read extending `P` persists (a pruned record `R ⪰ P` forces `P ⪯ Φ'.F`, since
`Φ'.F ⪯ P ⪯ R` would retain `R`). -/
private theorem rec_frameStep (hU : Coherent U) {Φ Φ' : Frm sp.n FGP} {B : Blk sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (hΦ' : FrameOK Φ') (hΦ'U : Φ'.tree ⊆ U)
    (hst : FrameStep Φ B Φ') {P : Blk sp.n FGP}
    (hinv : Anc U P Φ'.fcRoot ∨ P ∈ Φ'.viableTree Φ'.tree) {r : Nat}
    (h : Anc U P ((lookup Φ r).getD Φ.F)) : Anc U P ((lookup Φ' r).getD Φ'.F) := by
  have hBt : B ∈ Φ'.tree := hst.tree_eq ▸ ⟨Set.mem_insert _ _, hst.F'_anc_B⟩
  have hFF : Anc U Φ.F Φ'.F := hst.F_anc_F'.mono (Set.insert_subset_iff.2 ⟨hΦ'U hBt, hΦU⟩)
  by_cases hPF : Anc U P Φ'.F
  · exact rec_of_F hΦ' hΦ'U hPF r
  have hFP : Anc U Φ'.F P := by
    rcases hinv with h' | h'
    · exact (anc_total hU h' ((hΦ'.rooted.2 _ hΦ'.fcRoot_mem).mono hΦ'U)).resolve_left hPF
    · exact (hΦ'.rooted.2 P h'.1).mono hΦ'U
  cases hl : lookup Φ r with
  | none => rw [hl] at h; exact absurd (h.trans hFF) hPF
  | some R =>
    rw [hl] at h
    obtain ⟨hR, hRr⟩ := lookup_eq_some hl
    have hF'R : Anc U Φ'.F R := hFP.trans h
    have hF'm : Φ'.F ∈ insert B Φ.tree := by
      have := hΦ'.rooted.1
      rw [hst.tree_eq] at this
      exact this.1
    refine rec_of_mem hΦ' (hst.tree_eq ▸ ⟨Set.mem_insert_of_mem _ hR, ?_⟩) hRr h
    rcases Set.mem_insert_iff.1 hF'm with heq | hF't
    · rw [heq] at hF'R hFF
      exact absurd (mem_tree_of_between hU hΦ hΦU hFF hF'R hR) hst.new
    · exact (anc_tree_of_anc_U hU hΦ hΦU hF't hF'R hR).mono (Set.subset_insert _ _)

/-- `fc_root` is below every head: the anchor is `fc_root` or the deepest live lock block, a
candidate at least as deep as `fc_root`, hence above it. -/
private theorem fcRoot_anc_getHead {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SAState sp.n)
    (t : Time) {T : Set (Blk sp.n FGP)} (hT : T ⊆ Φ.tree) (V : View sp.n) (σ : Int) :
    Φ.Anc Φ.fcRoot (getHead sp A Φ t T V σ) := by
  have ha : Φ.Anc Φ.fcRoot (getAnchor sp A Φ t) ∧ getAnchor sp A Φ t ∈ Φ.tree := by
    unfold getAnchor
    rcases hD : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with _ | D
    · exact ⟨Relation.ReflTransGen.refl, hΦ.fcRoot_mem⟩
    obtain ⟨hDS, hmax⟩ := deepest_mem hD
    change Φ.Anc Φ.fcRoot D ∧ D ∈ Φ.tree
    by_cases he : D = Φ.fcRoot
    · subst he; exact ⟨Relation.ReflTransGen.refl, hΦ.fcRoot_mem⟩
    rcases hDS with hDl | hDf
    · refine ⟨?_, hDl.1⟩
      rcases liveLockBlock_candidate hΦ hDl with h | h
      · exact h.2.1
      · have h1 := depth_lt_of_anc hΦ h he hΦ.fcRoot_mem
        rcases hmax Φ.fcRoot (Or.inr rfl) (Ne.symm he) with h2 | ⟨h2, -⟩ <;> omega
    · exact absurd (Set.mem_singleton_iff.1 hDf) he
  unfold getHead
  exact ha.1.trans (anc_ghost hT _ ha.2)

/-- The live lock blocks of an honest node's stored locks at a time `≥ t_p` compare with `P`, by
`h2_locks_compare` (each is the viable ancestor of a live lock's block). -/
private theorem liveLock_compat (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {p : Nat}
    {P : Blk sp.n FGP}
    (hlocks : ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P)
    {y : Fin sp.n} (hy : y ∈ H) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (i : Nat) {T : Time} (hT : sp.ts p ≤ T) :
    ∀ L ∈ liveLockBlocks sp (tr.state y i).locks Φ T, Compatible U L P := by
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  have hva : Φ.Anc (Φ.viableAncestor B) B := anc_viableAncestor Φ B
  obtain rfl : L = Φ.viableAncestor B := hΦ.coherent.1 hLt (mem_of_anc hva hB) hLr.symm
  rcases hlocks y hy i T hT l hl (hlive.trans ((locksWF_state hr hy i).cap hl)) B (hΦU hB) hBr
    with h | h
  · exact Or.inl ((hva.mono hΦU).trans h)
  · exact anc_total hr.coherent (hva.mono hΦU) h

/-- **The record**: at every late read, the record that `ac_confirmed` reads (the latest confirmed
block in the frame, else `Φ.F`) extends `P`: the first test at `t_p + 6Δ` leaves a record extending
`P` or `P ⪯ Φ.F` (its result is `P`, unvetoed by `h2_locks_compare`); every later call keeps it (its
candidates compare with `P`, an ancestor candidate is refused), and so does every frame step (`Inv`
for `P`). -/
theorem h2_record_extends (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ →
      Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F) := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg := hI.le
  have hp4 : gbar g + 4 * sp.Δ ≤ sp.ts p := by linarith
  have hts : sp.ts (p + 1 : Nat) = sp.ts p + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hprot : Protected proposer tr H t₀ P p := Or.inr (Or.inr ⟨hpH, hP, hp, hunan⟩)
  rintro y hy j ℓ ⟨hc, ht, htick⟩
  -- in a frame from `t_{p+1}` on, `P ⪯ Φ.F` or `P` is in the tree
  have hcase : ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ →
      sp.ts p + 4 * sp.Δ ≤ tr.time c → ¬ Anc U P ℓ.frame.F → P ∈ ℓ.frame.tree := by
    intro c ℓ hc ht hPF
    obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
    rcases (hI.inv P p hprot y hy c ℓ hc (by rw [hts]; exact ht)).1 with h | h
    · exact mem_tree_of_between hU hΦ hΦU ((anc_total hU h
        ((hΦ.rooted.2 _ hΦ.fcRoot_mem).mono hΦU)).resolve_left hPF) h hΦ.fcRoot_mem
    · exact h.1
  -- the node's tick at `t_p + 6Δ`, at or before the read
  obtain ⟨k, hkj, ℓk, hck, hcallk, htk⟩ : ∃ k ≤ j, ∃ ℓk : ACLabel (goldilocksSA sp FGP ro),
      tr.CallAt y k ℓk ∧ ℓk.call = .tick ∧ tr.time k = sp.ts p + 6 * sp.Δ := by
    rcases eq_or_lt_of_le ht with heq | hlt
    · obtain ⟨k, hkj, ℓk, hck, hcall, htk⟩ := htick heq.symm
      exact ⟨k, hkj, ℓk, hck, hcall, htk.trans heq.symm⟩
    · obtain ⟨k, ℓk, hck, hcall, htk⟩ := hI.driven.tick y hy (sp.ts p + 6 * sp.Δ)
        (by linarith [gbar_nonneg g]) ⟨4 * (p : Int) + 6, by simp only [SAParams.ts]; ring⟩
        (hI.awake hy (by linarith))
      refine ⟨k, ?_, ℓk, hck, hcall, htk⟩
      by_contra h
      have := hr.time_mono (le_of_lt (not_le.1 h))
      linarith
  suffices key : ∀ c (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y c ℓ → k ≤ c →
      Anc U P ((lookup ℓ.frame (tr.post c).latestConfirmed).getD ℓ.frame.F) from
    key j ℓ hc hkj
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro ℓ hc hkc
    obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
    have htc : sp.ts p + 6 * sp.Δ ≤ tr.time c := htk ▸ hr.time_mono hkc
    by_cases hPF : Anc U P ℓ.frame.F
    · exact rec_of_F hΦ hΦU hPF _
    have hPt := hcase c ℓ hc (by linarith) hPF
    rcases Nat.eq_or_lt_of_le hkc with rfl | hkc
    · -- the first test: its result is `P`, unvetoed
      obtain rfl : ℓ = ℓk := Option.some.inj (hc.2.symm.trans hck.2)
      obtain ⟨R, hR, hRr, hPR⟩ := first_update_record hI.toHealthyBase hp4 hunan hy hc hcallk htk
        hPt (liveLock_compat hr hlocks hy hΦ hΦU k (by linarith))
      exact rec_of_mem hΦ hR hRr (hPR.mono hΦU)
    -- a later call: the previous call's record, moved to this call's frame, then the step
    rcases tr.noCall_or_lastCall y c with hn | ⟨c', hc'c, ℓ', hc', hnb⟩
    · exact absurd hck (hn k (Nat.zero_le _) hkc ℓk)
    have hkc' : k ≤ c' := by
      by_contra h
      exact hnb k (by omega) hkc ℓk hck
    have hR := ih c' hc'c ℓ' hc' hkc'
    rw [← tr.state_of_lastCall hc' hc'c hnb] at hR
    have hRc : Anc U P ((lookup ℓ.frame (tr.state y c).latestConfirmed).getD ℓ.frame.F) := by
      rcases hr.frameLaw y hy c ℓ hc with ⟨hn, -⟩ | ⟨c'', ℓ'', hc''c, hc'', hnb'', hok⟩
      · exact absurd hc' (hn c' (Nat.zero_le _) hc'c ℓ')
      obtain rfl : c' = c'' := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact hnb c'' (by omega) hc''c ℓ'' hc''
        · exact hnb'' c' (by omega) hc'c ℓ' hc'
      obtain rfl : ℓ' = ℓ'' := Option.some.inj (hc'.2.symm.trans hc''.2)
      obtain ⟨hΦ', hΦ'U⟩ := frameIn_of_callAt hr hy hc'
      obtain ⟨-, hok⟩ := hok
      have hstep : ℓ.frame = ℓ'.frame ∨ ∃ B, FrameStep ℓ'.frame B ℓ.frame := by
        generalize ℓ.call = cl at hok
        cases cl
        case block B => exact Or.inr ⟨B, hok.1⟩
        case message m => exact Or.inl hok.1
        all_goals exact Or.inl hok
      rcases hstep with heq | ⟨B, hst⟩
      · rw [heq]; exact hR
      · exact rec_frameStep hU hΦ' hΦ'U hΦ hΦU hst
          (hI.inv P p hprot y hy c ℓ hc (by rw [hts]; linarith)).1 hR
    obtain ⟨R, hR', hRr, hPR⟩ := record_step hI.toHealthyBase hp4 hvotes hy hc htc hPt
      (rec_to_tree hU hΦ hΦU hPF hPt hRc)
    exact rec_of_mem hΦ hR' hRr (hPR.mono hΦU)

/-- **Full heads**: at every late read, the head extends `P`: `P ⪯ fc_root`, below every head; or
`P` is viable (`Inv`), every live lock compares with `P` (`h2_locks_compare`) and the latest view's
honest votes, all extending `P`, give every child toward `P` a strict majority. -/
theorem h2_head_extends (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ → Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hr := hI.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg := hI.le
  have hts : sp.ts (p + 1 : Nat) = sp.ts p + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rintro y hy j ℓ ⟨hc, htj, -⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  rcases (hI.inv P p (Or.inr (Or.inr ⟨hpH, hP, hp, hunan⟩)) y hy j ℓ hc
    (by rw [hts]; linarith)).1 with h | h
  · exact h.trans ((fcRoot_anc_getHead hΦ _ _ (fun _ hX => hX.1) _ _).mono hΦU)
  refine (head_extends_of_frame hI.toHealthyBase (by linarith [gbar_nonneg g]) hvotes hy hc htj h
    ?_).mono hΦU
  rw [← show tr.state y (j + 1) = tr.post j by simp [Trace.state, hc.1, hc.2]]
  exact liveLock_compat hr hlocks hy hΦ hΦU (j + 1) (by linarith)

/-- **The confirmed tip extends a block both of its inputs extend** (`ac_confirmed` is the
deepest common ancestor of the record and the head in the frame's tree). -/
theorem anc_acConfirmed (hI : InclusionRun tr H U proposer g t₀)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {P : Blk sp.n FGP}
    (hC : Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F))
    (hH : Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j))) :
    Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hI.run.localRun hy hc
  exact anc_acConfirmed_of_frame hI.run.localRun.coherent hΦ hΦU hC hH

/-- **H.2 (ii)**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ`, if every
honest vote of slot `p` is `P`, then at every call of an honest node from `t_p + 6Δ` on (at
`t_p + 6Δ` itself, from its tick there on), `P ⪯ ac_confirmed` after the call. -/
theorem h2_proposal_confirmed (hI : InclusionRun tr H U proposer g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  -- `P` is a frame block, protected by P3; `h2_votes_continue` propagates the unanimous batch
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAt hI.run.localRun hpH hc).2
      ((accept_new sp hI.run.localRun hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  have hself : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → VoteExtends U e.msg P :=
    fun x hx j e hv hs => ⟨P, hPU, (hunan x hx j e hv hs).symm, Relation.ReflTransGen.refl⟩
  have hcont := h2_votes_continue hI (Or.inr (Or.inr ⟨hpH, hP, hp, hunan⟩)) le_rfl
    (by linarith) hself
  have hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P := by
    intro x hx j e hv hle
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact hself x hx j e hv h.symm
    · exact votesExtendAfter_iff.1 hcont x hx j e hv h
  have hlocks := h2_locks_compare hI hp hvotes
  intro y hy j ℓ hc ht htick
  have hr : LateRead tr p y j ℓ := ⟨hc, ht, htick⟩
  exact anc_acConfirmed hI hy hc (h2_record_extends hI hpH hP hp hunan hvotes hlocks y hy j ℓ hr)
    (h2_head_extends hI hpH hP hp hunan hvotes hlocks y hy j ℓ hr)

end Consensus.Goldilocks.SA

end
