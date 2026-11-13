module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks outage: the arming steps (S-vote and slow-lock formation)

For an outage `[b₀, b₁)` armed at
`T` under the lag `(4k+6)Δ` (node units), every origin `C` within `T` has a label `σ` with
`σ + k < j₀`, `j₀ := coverLabel b₀`; every honest vote of a slot in `(σ, j₀]` extends `C`
(S-vote); an honest updater whose slot's votes are delivered by `t_s + 2Δ ≤ b` has a result
extending `C`, held in its frame when `Σ.F ⪯ C`, with an honest supporter (Lemma P); the saved
attestations of an update extend `C`; and the pure SA formation of a slow lock. The veto analysis
at the cover gate `j₀` takes the lock-safety input (N) as a hypothesis. -/

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

/-- (A2) An origin within `T` started by `T`. -/
theorem OriginWithin.ts_le (hrun : GoldilocksRun proposer dg H tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} {T : Time}
    (h : OriginWithin tr H C σ T) : sp.ts σ ≤ T := by
  obtain ⟨x, -, i, CV, hi, ⟨ℓ, hu, -⟩ | ⟨ℓ, A, -, hs, -⟩⟩ := originWithin_iff.1 h
  · have ht : tr.time i = sp.ts σ + 6 * sp.Δ := hu.2.2.1
    have := sp.toParams.hΔ
    linarith
  · exact ((SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) σ).2 (by
      have hs' : sp.slot (tr.time i) = σ := hs
      rw [hs'])).trans hi

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

/-- Finite service only weakens when the horizon is lowered. -/
theorem SleepyServiceBefore.mono {ΔF b b' : Time} (h : SleepyServiceBefore tr H ΔF b)
    (hb : b' ≤ b) : SleepyServiceBefore tr H ΔF b' :=
  ⟨h.deltaF, ⟨fun x hx i m hm h0 y hy j ℓ hc hd ht =>
      h.ac.message x hx i m hm h0 y hy j ℓ hc (hd.trans hb) ht,
    fun x hx i B hB h0 y hy j ℓ hc hd ht ha =>
      h.ac.relay x hx i B hB h0 y hy j ℓ hc (hd.trans hb) ht ha⟩,
    fun x hx i B hB h0 y hy j hc hd ht ha => h.relay x hx i B hB h0 y hy j hc (hd.trans hb) ht ha⟩

/-! ### S-vote -/

/-! ### The receiver epoch -/

/-- (R1) Awake on `[a, z]`: every restart up to `z` is at or before every public `τ ∈ [a, z]`. -/
theorem restart_le_of_awakeOn (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {a z τ : Time} (haw : ∀ u, a ≤ u → u ≤ z → tr.awake y u)
    (haτ : a ≤ τ) (hτz : τ ≤ z) (hτ0 : 0 ≤ τ) (hpub : sp.toParams.IsPublic τ)
    {k : Nat} (hk : tr.RestartAt y k) (hkz : tr.time k ≤ z) : tr.time k ≤ τ := by
  have h := hrun.toLocalRun
  by_contra hgt
  push Not at hgt
  obtain ⟨u, -, huk, hs, hb⟩ := h.sleep_of_restart y hy k hk
  have hua : u < a := by
    by_contra hle
    exact hs (haw u (not_lt.1 hle) (by linarith))
  obtain ⟨j, x, hj⟩ := h.tick_of_awake y hy τ hτ0 hpub (haw τ haτ hτz)
  obtain ⟨hjc, hjt⟩ := group_call hj
  have hjk : j < k := by
    by_contra hkj
    have := h.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk hjc
  linarith

/-! ### Lemma P -/

/-- **Lemma P**: an update whose slot's votes are delivered by `t_s + 2Δ ≤ b` (the update
itself may be after `b`) has a result extending a bounded origin of an earlier label, held in its
frame when `Σ.F ⪯ C`, with an honest supporter in its pool. -/
theorem update_result_extends_origin (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hσs : σ < s) (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b) (hfb : tr.FaultBound H (sp.ts s + sp.Δ))
    (hFC : Anc (tr.HonestBlocks H) (tr.state y c).fg.F C) :
    C ∈ ℓ.frame.tree ∧ ∃ D, SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D ∧
      ℓ.frame.Anc C D ∧ ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
        e.msg ∈ (tr.state y c).ac.pool s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcount : Hᶜ.ncard <
      {x | x ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s}.ncard := by
    refine lt_of_lt_of_le hfb (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨j, e, hv, hs, -⟩ :=
      vote_of_awake_joined hrun hnc hx (mayVote_stock hrun hnc hx _) hw hj
    exact ⟨hx, j, e, hv, hs⟩
  have hvb : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      tr.time j ≤ b := by
    rintro x hx j e ⟨ℓx, hc, he⟩ hs
    have ht := (cast_head_fcRoot hr hx ⟨hc, he⟩).2
    rw [hs] at ht
    change tr.time j ≤ _ at ht
    linarith
  -- the update's cut
  obtain ⟨cl, hc, hcl⟩ := Option.bind_eq_some_iff.1 hu.1.2
  obtain rfl : cl = .ac ℓ := by
    cases cl with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨hfr, -, -, -⟩ := hrun.cutLaw y hy c (.ac ℓ) ⟨hu.1.1, hc⟩
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy c
  have hHB : ℓ.frame.tree ⊆ tr.HonestBlocks H := fun X hX =>
    ⟨y, hy, c, by rw [hfr] at hX; exact hX.1⟩
  have hFeq : ℓ.frame.F = (tr.state y c).fg.F := by rw [hfr]; rfl
  -- every honest slot-`s` vote is held and resolved at the update, its head above `C`
  have hbatch : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Anc (tr.HonestBlocks H) C Hd ∧
        e.msg ∈ (tr.projAC.state y c).pool s ∧
        SA.resolutionTime (tr.projAC.state y c) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    intro x hx j e hv hes
    obtain ⟨Hd, hHdU, hHdr, hCHd⟩ := hinv.vote_extends C σ hC x hx j e hv
      (hvb x hx j e hv hes) (by omega)
    obtain ⟨hHdt, hpool, hres⟩ := honest_vote_at_update_early hrun' hsync hsb
      hy hu hHdU (hFeq ▸ hFC.trans hCHd) hx hv hes hHdr.symm
    exact ⟨Hd, hHdt, hHdr, hCHd, hpool, hres⟩
  -- `C` is in the frame, above `Σ.F`
  have hCt : C ∈ ℓ.frame.tree := by
    obtain ⟨x, hx, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero
      (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨Hd, hHdt, -, hCHd, -⟩ := hbatch x hx j e hv hes
    rw [hfr] at hHdt ⊢
    have hCHd' := honest_held_anc hrun hnc hy hCHd hHdt.1
    have hCfg : C ∈ (tr.state y c).fg.tree := by
      by_cases hne : C = Hd
      · exact hne ▸ hHdt.1
      · exact (Goldilocks.Anc.mem hCHd' hne).1
    exact ⟨hCfg, honest_held_anc hrun hnc hy hFC hCfg⟩
  have hFCΦ : ℓ.frame.Anc ℓ.frame.F C := hΦ.rooted.2 C hCt
  rw [← projAC_state hrun.toLocalRun hy]
  set A := tr.projAC.state y c
  set Hv := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}
  have hone : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := hrun'.honest.pool_vote y hy c s v hvp (hvx ▸ hx)
    have hs' := SA.state_pool_slot sp hr hy c s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (SA.one_vote_per_slot sp _ ro H _ _ hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hcs : ∀ B, SA.confirmationScore sp A ℓ.frame s B = (SA.supporters ℓ.frame V s B).ncard :=
    fun _ => rfl
  have hsupp : Hv ⊆ SA.supporters ℓ.frame V s C := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨Hd, hHdt, hHdr, hCHd, hvp, hres⟩ := hbatch x hx j e hv hs
    obtain ⟨ℓx, hcx, hex⟩ := hv
    have hval := (SA.castAt_spec hr hx ⟨hcx, hex⟩).1
    refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, Hd, hHdt, hHdr,
      SA.anc_tree_of_anc_U hU hΦ hHB hCt hCHd hHdt⟩
    rintro ⟨v, hv, v', hv', hne, hvx, hv'x⟩
    exact hne ((hone x hx j e ⟨ℓx, hcx, hex⟩ hs v hv hvx).trans
      (hone x hx j e ⟨ℓx, hcx, hex⟩ hs v' hv' hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆ Hv ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote y hy c s _ hv hw
      exact Or.inl ⟨hw, j, e, he, SA.state_pool_slot sp hr hy c s _ hv⟩
    · exact Or.inr hw
  have hHvv : Hv ⊆ SA.voters {v | v ∈ A.pool s} := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨-, -, -, -, hvp, -⟩ := hbatch x hx j e hv hs
    exact ⟨e.msg, hvp, (SA.castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩).1⟩
  have hmaj : (SA.voters {v | v ∈ A.pool s}).ncard <
      2 * SA.confirmationScore sp A ℓ.frame s C := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le Hv Hᶜ
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    rw [hcs]
    omega
  -- the result is the deepest majority block above `Σ.F`, which extends `C`
  set S := {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
    (SA.voters {v | v ∈ A.pool s}).ncard < 2 * SA.confirmationScore sp A ℓ.frame s B}
  have hS : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ B' ∈ S, Compatible ℓ.frame.tree B B' := fun B hB B' hB' =>
    SA.majority_chain sp _ ℓ.frame V s B B' hΦ hsub hB.1 hB'.1 (hcs B ▸ hB.2.2)
      (hcs B' ▸ hB'.2.2)
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hS ⟨C, hCt, hFCΦ, hmaj⟩
  have hCD := SA.anc_deepest hΦ hS hch hD C ⟨hCt, hFCΦ, hmaj⟩
  have hDmaj := (SA.deepest_mem hD).1.2.2
  rw [hcs] at hDmaj
  refine ⟨hCt, D, hD, hCD, ?_⟩
  -- an honest supporter of `D`
  by_contra hno
  have hSpF : SA.supporters ℓ.frame V s D ⊆ Hᶜ := by
    rintro i ⟨-, v, ⟨hvp, -⟩, hvi, hvs, R, hR, hRr, hDR⟩
    intro hi
    obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote y hy c s v hvp (hvi ▸ hi)
    exact hno ⟨_, hi, j, e, hvi ▸ he, by exact_mod_cast hvs, hvp,
      R, hHB hR, hRr, hDR.mono hHB⟩
  have hSpv : SA.supporters ℓ.frame V s D ⊆ SA.voters {v | v ∈ A.pool s} := by
    rintro i ⟨-, v, ⟨hvp, -⟩, hvi, -⟩
    exact ⟨v, hvp, hvi⟩
  have hdisj : Disjoint Hv (SA.supporters ℓ.frame V s D) :=
    Set.disjoint_left.2 fun x hx hx' => hSpF hx' hx.1
  have h1 := Set.ncard_le_ncard (Set.union_subset hHvv hSpv) (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at h1
  have h2 := Set.ncard_le_ncard hSpF (Set.toFinite _)
  omega

/-- **P≤**: an update within `b` has root cover, or Lemma P's conclusion. -/
theorem update_result_or_root (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCU : C ∈ tr.HonestBlocks H) {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hσs : σ < s) (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hcb : tr.time c ≤ b) (hfb : tr.FaultBound H (sp.ts s + sp.Δ)) :
    Anc (tr.HonestBlocks H) C (tr.state y c).fg.F ∨
      (Anc (tr.HonestBlocks H) (tr.state y c).fg.F C ∧ C ∈ ℓ.frame.tree ∧
        ∃ D, SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D ∧ ℓ.frame.Anc C D) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hFU : (tr.state y c).fg.F ∈ tr.HonestBlocks H :=
    ⟨y, hy, c, (frameOK_state hrun.toLocalRun hy c).rooted.1.1⟩
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hCU hFU
      (onOriginChainWithin_iff.2 (Or.inr ⟨C, σ, hC, Relation.ReflTransGen.refl⟩))
      (hinv.caches y hy c (fun k hk => (hrun.time_mono hk.le).trans hcb)).1 with hCF | hFC
  · exact Or.inl hCF
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  obtain ⟨hCt, D, hD, hCD, -⟩ := update_result_extends_origin hrun hnc hinv hsync hC hy hσs hu
    (by linarith) hfb hFC
  exact Or.inr ⟨hFC, hCt, D, hD, hCD⟩

/-! ### The saved attestations -/

/-- The frame of an update is the node's frame at the update's cut. -/
theorem update_frame (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
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
theorem saved_rows_above (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
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
  obtain ⟨k', hk', C', CV, ⟨ℓ', hu', hC', -⟩, hC'r⟩ := SA.saved_result hr hy c q hrs
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
theorem own_optimistic_compatible_result (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k c s : Nat}
    {B' D : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (SA.Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC y k s B' CV) (hR : SA.ResultAt tr.projAC y c s D CV')
    (hkc : k < c) (hnr : ∀ r, k < r → r ≤ c → ¬ tr.RestartAt y r) :
    Compatible (tr.HonestBlocks H) B' D := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  obtain ⟨-, hcnt, ell, A, hp, -, hCV, -⟩ := SA.optimisticLockAt_spec hrun' hy hO
  rw [hrun'.stock] at hcnt
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
  have h2 : (SA.voters CV ∪ SA.supporters ℓ.frame V s D).ncard ≤ sp.n := by
    refine (Set.ncard_le_ncard (Set.subset_univ _)).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at h2
  omega

/-- **The veto analysis at the cover gate.** At the first update of slot `s` (after `b`),
whose slot's votes are delivered by `t_s + 2Δ ≤ b`, with a result `D ⪰ C` that an honest pool vote
supports: every live block that vetoes `D` is that of a stored lock of slot `s + 1` and extends
`C`. A vetoing lock of a label below `s` sits below an origin within `b`
(case (a)); one of label `s` below an own optimistic selection (case (b), no restart since
`t_s`); one of label `s + 1` below an own optimistic selection of slot `s + 1`, which an
optimistic voter outside `Opp` and so in `Hold` makes compatible with `C` through (N) (case (c)),
and conflicts with `D`. At the call site `Hold` is the holders and `Opp` the faulty validators
and the late wakers. -/
theorem cover_gate_veto_above (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y c s ℓ)
    (hfirst : ∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC y k s ℓ')
    (hD : SA.getConfirmation sp (tr.state y c).ac ℓ.frame s = some D) (hCD : ℓ.frame.Anc C D)
    (hsupp : ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
      e.msg ∈ (tr.state y c).ac.pool s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg D)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b)
    (hnr : ∀ r ≤ c, tr.RestartAt y r → tr.time r < sp.ts s)
    (Hold Opp : Set (Fin sp.n)) (hF : Hᶜ ⊆ Opp) (hopp : 2 * Opp.ncard < sp.n)
    (hcast : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s + 1 → j < c →
      x ∈ Hold ∨ x ∈ Opp)
    (hN : ∀ x ∈ Hold, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s + 1 → j < c →
      SA.VoteExtends (tr.HonestBlocks H) e.msg C) :
    ∀ V ∈ SA.liveLockBlocks sp (tr.state y c).ac.locks ℓ.frame (tr.time c),
      ¬ Compatible ℓ.frame.tree D V →
        (∃ l ∈ (tr.state y c).ac.locks, l.slot = s + 1 ∧
          ∃ B₀ ∈ ℓ.frame.tree, B₀.root = l.block ∧ V = ℓ.frame.viableAncestor B₀) ∧
        ℓ.frame.Anc C V := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hfr := update_frame hrun hy hu
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy c
  have hHB : ℓ.frame.tree ⊆ tr.HonestBlocks H := (SA.frameIn_of_callAt hr hy hu.1).2
  have hDt : D ∈ ℓ.frame.tree := (SA.deepest_mem hD).1.1
  have hCt : C ∈ ℓ.frame.tree := SA.mem_of_anc hCD hDt
  have hCD' := hCD.mono hHB
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  intro V hV hconf
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hV
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB₀
  have hVB' := hVB.mono hHB
  have hnoU : ¬ Compatible (tr.HonestBlocks H) D (ℓ.frame.viableAncestor B₀) := by
    rintro (h | h)
    · exact hconf (Or.inl (SA.anc_tree_of_anc_U hU hΦ hHB hDt h hVt))
    · exact hconf (Or.inr (SA.anc_tree_of_anc_U hU hΦ hHB hVt h hDt))
  -- a block above `B₀` compatible with `D` refutes the conflict
  have hO : ∀ O, Anc (tr.HonestBlocks H) B₀ O → Compatible (tr.HonestBlocks H) O D → False := by
    intro O hBO h
    apply hnoU
    rcases h with h | h
    · exact Or.inr (hVB'.trans (hBO.trans h))
    · exact SA.anc_total hU h (hVB'.trans hBO)
  obtain ⟨L, hL, hLr, O, hLO, k', hk', CV, hO'⟩ := SA.lock_below_origin hr hy c l
    (by rw [projAC_state hrun.toLocalRun hy]; exact hl)
  obtain rfl : B₀ = L := (hU.1 hL (hHB hB₀) (hLr.trans hB₀r.symm)).symm
  have hk'c := hrun.time_mono hk'.le
  -- an origin within `b` of a label below `s` is compatible with `D` (its honest supporter)
  have hearly : ∀ σ', σ' < s → OriginWithin tr H O σ' b →
      Compatible (tr.HonestBlocks H) O D := by
    intro σ' hσ' hOw
    obtain ⟨x, hx, j, e, hv, hes, -, Hd', hHd', hHd'r, hDHd'⟩ := hsupp
    obtain ⟨ℓx, hcx, hex⟩ := hv
    have hvt := (cast_head_fcRoot hr hx ⟨hcx, hex⟩).2
    rw [hes] at hvt
    obtain ⟨Hd, hHd, hHdr, hOHd⟩ := hinv.vote_extends O σ' hOw x hx j e ⟨ℓx, hcx, hex⟩
      (by change tr.time j ≤ _ at hvt; linarith) (by omega)
    obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
    exact SA.anc_total hU hOHd hDHd'
  rcases lt_trichotomy l.slot s with hls | hls | hls
  · -- (a) a label below `s`: an origin within `b`
    exfalso
    have hts := (SA.ts_le_iff sp).2 (show (l.slot : Int) + 1 ≤ s by omega)
    refine hO O hLO (hearly l.slot hls (originWithin_iff.2 ⟨y, hy, k', CV, ?_, hO'⟩))
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · have ht : tr.time k' = sp.ts l.slot + 6 * sp.Δ := hu'.2.2.1
      simp only [SAParams.ts] at hts ht hsb ⊢
      linarith
    · have ht := (SA.optimisticLockAt_spec hrun' hy hopt).1
      change tr.time k' < _ at ht
      simp only [SAParams.ts] at hts ht hsb ⊢
      linarith
  · -- (b) label `s`: the own optimistic selection, compatible with the result
    exfalso
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · exact hfirst k' hk' ℓ' (hls ▸ hu')
    · rw [hls] at hopt
      refine hO O hLO (own_optimistic_compatible_result hrun hnc hy hopt
        ⟨ℓ, hu, by rw [projAC_state hrun.toLocalRun hy]; exact hD, rfl⟩ hk' ?_)
      intro r hr₁ hr₂ hrr
      have h1 := hnr r hr₂ hrr
      have h2 := hrun.time_mono hr₁.le
      obtain ⟨ℓo, Ao, -, hso, -⟩ := hopt
      have h3 := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k') s).2 (by
        have : sp.slot (tr.time k') = s := hso
        rw [this])
      linarith
  · -- (c) a later label: an own optimistic selection of slot `s + 1`
    have hsc : sp.slot (tr.time c) = s + 1 := by
      have h6 : tr.time c = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := by
        rw [htc]; simp only [SAParams.ts]; push_cast; ring
      exact SA.slot_of_mem sp (s + 1) (by rw [h6]; linarith)
        (by rw [h6]; simp only [SAParams.ts]; push_cast; linarith)
    rcases hO' with ⟨ℓ', hu', -⟩ | hopt
    · exfalso
      have ht : tr.time k' = sp.ts l.slot + 6 * sp.Δ := hu'.2.2.1
      have := (SA.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts s by linarith)
      omega
    have hls' : l.slot = s + 1 := by
      obtain ⟨ℓo, Ao, -, hso, -⟩ := hopt
      have h1 := SA.slot_mono sp (hrun.time_nonneg k') hk'c
      have hso' : sp.slot (tr.time k') = l.slot := hso
      rw [hso', hsc] at h1
      omega
    obtain ⟨-, hcnt, ell, A, hp, -, hCV, hCVv⟩ := SA.optimisticLockAt_spec hrun' hy hopt
    rw [hrun'.stock] at hcnt
    have hellU := (SA.frameIn_of_callAt hr hy hp.1).2
    -- an honest optimistic voter in `Hold`
    obtain ⟨v, hvCV, hvH, hvHold⟩ : ∃ v ∈ CV, v.val ∈ H ∧ v.val ∈ Hold := by
      by_contra hno
      push Not at hno
      have hsub : SA.voters CV ⊆ Opp := by
        rintro i ⟨v, hv, rfl⟩
        by_cases hvH : v.val ∈ H
        · obtain ⟨a, ha, e', he', hev⟩ := hCVv v hv hvH
          rcases hcast _ hvH a e' (hev ▸ he')
            (by rw [hev, (hCV v hv).2.1, hls']) (by omega) with h | h
          · exact absurd h (hno v hv hvH)
          · exact h
        · exact hF hvH
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    obtain ⟨a, ha, e', he', hev⟩ := hCVv v hvCV hvH
    obtain ⟨Hd, hHd, hHdr, hCHd⟩ := hN v.val hvHold a e' (hev ▸ he')
      (by rw [hev, (hCV v hvCV).2.1, hls']) (by omega)
    obtain ⟨-, -, R, hR, hRr, hOR⟩ := hCV v hvCV
    obtain rfl : R = Hd := hU.1 (hellU hR) hHd (hRr.trans (by rw [hHdr, hev]))
    rcases SA.anc_total hU (hOR.mono hellU) hCHd with hOC | hCO
    · exact (hO O hLO (Or.inl (hOC.trans hCD'))).elim
    rcases SA.anc_total hU hCO (hVB'.trans hLO) with hCV' | hVC
    · exact ⟨⟨l, hl, hls', B₀, hB₀, hB₀r, rfl⟩, SA.anc_tree_of_anc_U hU hΦ hHB hCt hCV' hVt⟩
    · exact (hnoU (Or.inr (hVC.trans hCD'))).elim

/-! ### The armed updates of a no-sleep holder -/

/-- A node awake on `[a, z]` with `a ≤ t_r` runs the update of every slot `q ≥ r` whose update
is by `z` (joined there: its restarts up to `z` are at or before `t_r`). -/
theorem update_of_awakeOn (hrun : GoldilocksRun proposer dg H tr) {w : Fin sp.n} (hw : w ∈ H)
    {a z : Time} (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u) {r q : Nat} (ha : a ≤ sp.ts r)
    (hrq : r ≤ q) (hqz : sp.ts q + 6 * sp.Δ ≤ z) : ∃ k ℓ, SA.UpdateAt tr.projAC w k q ℓ := by
  have hΔ := sp.toParams.hΔ
  have hrq' := (SA.ts_le_iff sp).2 (show (r : Int) ≤ q by exact_mod_cast hrq)
  have h0 : (0 : Time) ≤ sp.ts r := by simp only [SAParams.ts]; positivity
  refine update_of_awake_joined hrun hw (haw _ (by linarith) hqz) fun k hk hkt => ?_
  have hkr := restart_le_of_awakeOn hrun hw haw ha (by linarith) h0
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (r : Int)) (by simp only [SAParams.ts]; ring))
    hk (hkt.trans hqz)
  have hsl : sp.slot (sp.ts q + 6 * sp.Δ) = q + 1 := by
    have h6 : sp.ts q + 6 * sp.Δ = sp.ts ((q + 1 : Nat) : Int) + 2 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rw [h6]
    exact SA.slot_of_mem sp (q + 1) (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  change 0 < sp.slot _ ∧ _ ≤ sp.toParams.slotTime (sp.slot _ - 1)
  rw [hsl, Nat.add_sub_cancel, sp.slotTime_eq]
  refine ⟨Nat.succ_pos q, ?_⟩
  change _ ≤ sp.ts q
  linarith

/-- **The first armed update** of slot `s` of a no-sleep holder `w`: it exists, its
restarts are at or before `t_{s−k+1}`, and when `Σ.F ⪯ C` the origin `C` (of a label `σ ≤ s − k`)
is in its frame below its result, which an honest pool vote supports, and every saved attestation of
the slow test names a block of the frame above `C`. -/
theorem armed_first_update (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → tr.FaultBound H (sp.ts q + sp.Δ))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    {w : Fin sp.n} (hw : w ∈ H) {a z : Time} (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ') ∧
      (∀ r ≤ c, tr.RestartAt w r → tr.time r ≤ sp.ts ((s : Int) - sp.k + 1)) ∧
      (Anc (tr.HonestBlocks H) (tr.state w c).fg.F C →
        C ∈ ℓ.frame.tree ∧ ∃ D, SA.getConfirmation sp (tr.state w c).ac ℓ.frame s = some D ∧
          ℓ.frame.Anc C D ∧
          (∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s ∧
            e.msg ∈ (tr.state w c).ac.pool s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg D) ∧
          ∀ j : Int, (s : Int) - sp.k < j → j < s → ∃ S ∈ ℓ.frame.tree,
            (tr.state w c).ac.saved j = some S.root ∧ ℓ.frame.Anc C S) := by
  classical
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hrI : ((s - sp.k + 1 : Nat) : Int) = (s : Int) - sp.k + 1 := by omega
  have ha' : a ≤ sp.ts (s - sp.k + 1 : Nat) := by rw [hrI]; exact ha
  have hex₀ : ∃ c, ∃ ℓ, SA.UpdateAt tr.projAC w c s ℓ :=
    update_of_awakeOn hrun hw haw ha' (by omega) hsz
  obtain ⟨ℓ, hu⟩ := Nat.find_spec hex₀
  have hfirst : ∀ k < Nat.find hex₀, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ' :=
    fun k hk ℓ' h => Nat.find_min hex₀ hk ⟨ℓ', h⟩
  have htc : tr.time (Nat.find hex₀) = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hτs := (SA.ts_le_iff sp).2 (show (s : Int) - sp.k + 1 ≤ s by
    have := sp.two_le_k; omega)
  have h0 : (0 : Time) ≤ sp.ts (s - sp.k + 1 : Nat) := by simp only [SAParams.ts]; positivity
  have hnr : ∀ r ≤ Nat.find hex₀, tr.RestartAt w r →
      tr.time r ≤ sp.ts ((s : Int) - sp.k + 1) := by
    intro r hr' hrr
    rw [← hrI]
    exact restart_le_of_awakeOn hrun hw haw ha' (by rw [hrI]; linarith) h0
      (show sp.toParams.IsPublic _ from Dvd.intro (4 * ((s - sp.k + 1 : Nat) : Int))
        (by simp only [SAParams.ts]; ring)) hrr ((hrun.time_mono hr').trans (htc ▸ hsz))
  refine ⟨Nat.find hex₀, ℓ, hu, hfirst, hnr, fun hFC => ?_⟩
  obtain ⟨hCt, D, hD, hCD, hsupp⟩ := update_result_extends_origin hrun hnc hinv hsync hC hw
    (by omega) hu hsb (hfb s (by linarith)) hFC
  refine ⟨hCt, D, hD, hCD, hsupp, ?_⟩
  have hCtfg : C ∈ (tr.state w (Nat.find hex₀)).fg.tree := by
    rw [update_frame hrun hw hu] at hCt; exact hCt.1
  refine saved_rows_above hrun hnc hw hu hks hFC hCtfg hnr ?_ ?_
  · intro q hq₁ hq₂
    have hqs := (SA.ts_lt_iff sp).2 (show (q : Int) < s by exact_mod_cast hq₂)
    obtain ⟨k, ℓ', hu'⟩ := update_of_awakeOn hrun hw haw ha' (r := s - sp.k + 1) (q := q)
      (by omega) (by linarith)
    refine ⟨k, ?_, ℓ', hu'⟩
    by_contra hck
    push Not at hck
    have h1 := hrun.time_mono hck
    have h2 : tr.time k = sp.ts q + 6 * sp.Δ := hu'.2.2.1
    linarith
  · intro q hq₁ hq₂ k hk ℓ' hu'
    have hqs := (SA.ts_lt_iff sp).2 (show (q : Int) < s by exact_mod_cast hq₂)
    have hFk : Anc (tr.HonestBlocks H) (tr.state w k).fg.F C :=
      (Healing.run_F_mono hrun.toLocalRun hw hk.le).trans hFC
    obtain ⟨-, R, hR, hCR, -⟩ := update_result_extends_origin hrun hnc hinv hsync hC hw
      (by omega) hu' (by linarith) (hfb q (by linarith)) hFk
    exact ⟨R, hR, hCR.mono (SA.frameIn_of_callAt hr hw hu'.1).2⟩

/-- The slot of an update's time is the next slot. -/
private theorem slot_update_time {s : Nat} : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 := by
  have hΔ := sp.toParams.hΔ
  have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rw [h6]
  exact SA.slot_of_mem sp (s + 1) (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)

/-- The post-state locks of an update are those of `update_confirmation`. -/
private theorem locks_after_update (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {w : Fin sp.n} (hw : w ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC w c s ℓ) :
    (tr.state w (c + 1)).ac.locks =
      (SA.updateConfirmation sp (tr.state w c).ac ℓ.frame (tr.time c) s).locks := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  rw [← projAC_state hrun.toLocalRun hw (c + 1), SA.state_after_update hr hw hu,
    projAC_state hrun.toLocalRun hw]
  rfl

/-- **O1 at an update within `b`**: the first update of slot `s` of a no-sleep holder,
at a time `≤ b`, has root cover, or stores a lock of slot `s` on a block of its frame above `C`. -/
theorem armed_lock_formed (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → tr.FaultBound H (sp.ts q + sp.Δ))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCU : C ∈ tr.HonestBlocks H) (hCg : C.root ≠ sp.genesisRoot)
    {w : Fin sp.n} (hw : w ∈ H) {a z : Time} (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 6 * sp.Δ ≤ b) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧
      (Anc (tr.HonestBlocks H) C (tr.state w c).fg.F ∨
        ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc C L ∧
          (⟨L.root, s, f, s + sp.k⟩ : SA.Lock) ∈ (tr.state w (c + 1)).ac.locks) := by
  have hΔ := sp.toParams.hΔ
  have hk2 := sp.two_le_k
  obtain ⟨c, ℓ, hu, -, -, hP⟩ := armed_first_update hrun hnc hinv hsync hfb hC hw haw hks hσs
    ha hsz (by linarith)
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  refine ⟨c, ℓ, hu, ?_⟩
  rcases update_result_or_root hrun hnc hinv hsync hC hCU hw (by omega) hu (htc ▸ hsb)
      (hfb s (by linarith)) with hroot | ⟨hFC, -, -⟩
  · exact Or.inl hroot
  obtain ⟨hCt, D, hD, hCD, -, hrows⟩ := hP hFC
  have hfr := update_frame hrun hw hu
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hw c
  have hcand : ℓ.frame.AncestorCandidate C := by
    rw [hfr] at hCt ⊢
    exact hinv.viable w hw c (fun k hk => (hrun.time_mono hk.le).trans (htc ▸ hsb)) C σ hC hCt
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by
    rw [htc, slot_update_time]; have := sp.two_le_k; omega
  obtain ⟨L, f, hL, hCL, hl⟩ := SA.updateConfirmation_slow_lock_effective hΦ hD
    (result_not_vetoed_before hrun hnc hinv hw hu (htc ▸ hsb) hD) hCt hCg hCD hrows hlive hcand
  exact Or.inr ⟨L, f, hL, hCL, (locks_after_update hrun hnc hw hu).symm ▸ hl⟩

/-- **O1 at the cover gate**: the first update of slot `s` of a no-sleep holder, whose
slot's votes are delivered by `t_s + 2Δ ≤ b` but which may itself be after `b`. Given (F) `Σ.F`
compatible with `C`, (VA) `C` a candidate when `Σ.F ⪯ C`, and (N) for the `Hold` votes of slot
`s + 1` before it, it has root cover or stores a lock of slot `s` and expiry `s + k` above `C`.
Under independent writes the slow lock is written even when the result is vetoed, because `C`
itself conflicts with no live lock (`cover_gate_veto_above`). -/
theorem armed_lock_cover (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    (hfb : ∀ q : Nat, sp.ts q + sp.Δ ≤ b → tr.FaultBound H (sp.ts q + sp.Δ))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {σ : Nat} (hC : OriginWithin tr H C σ b)
    (hCg : C.root ≠ sp.genesisRoot)
    {w : Fin sp.n} (hw : w ∈ H) {a z : Time} (haw : ∀ u, a ≤ u → u ≤ z → tr.awake w u)
    {s : Nat} (hks : sp.k ≤ s) (hσs : σ + sp.k ≤ s)
    (ha : a ≤ sp.ts ((s : Int) - sp.k + 1)) (hsz : sp.ts s + 6 * sp.Δ ≤ z)
    (hsb : sp.ts s + 2 * sp.Δ ≤ b)
    (Hold Opp : Set (Fin sp.n)) (hF : Hᶜ ⊆ Opp) (hopp : 2 * Opp.ncard < sp.n)
    (hcast : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s + 1 →
      tr.time j ≤ sp.ts s + 6 * sp.Δ → x ∈ Hold ∨ x ∈ Opp) :
    ∃ c ℓ, SA.UpdateAt tr.projAC w c s ℓ ∧ (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC w k s ℓ') ∧
      (Compatible (tr.HonestBlocks H) (tr.state w c).fg.F C →
        (Anc (tr.HonestBlocks H) (tr.state w c).fg.F C → ℓ.frame.AncestorCandidate C) →
        (∀ x ∈ Hold, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s + 1 → j < c →
          SA.VoteExtends (tr.HonestBlocks H) e.msg C) →
        Anc (tr.HonestBlocks H) C (tr.state w c).fg.F ∨
        ∃ L f, ℓ.frame.Anc C L ∧
          (⟨L.root, s, f, s + sp.k⟩ : SA.Lock) ∈ (tr.state w (c + 1)).ac.locks) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨c, ℓ, hu, hfirst, hnr, hP⟩ := armed_first_update hrun hnc hinv hsync hfb hC hw haw hks
    hσs ha hsz hsb
  have htc : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  refine ⟨c, ℓ, hu, hfirst, fun hFcomp hVA hN => ?_⟩
  rcases hFcomp with hFC | hCF
  swap
  · exact Or.inl hCF
  obtain ⟨hCt, D, hD, hCD, hsupp, hrows⟩ := hP hFC
  have hfr := update_frame hrun hw hu
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hw c
  have hτs := (SA.ts_lt_iff sp).2 (show (s : Int) - sp.k + 1 < s by
    have := sp.two_le_k; omega)
  have hveto := cover_gate_veto_above hrun hnc hinv hw hu hfirst hD hCD hsupp hsb
    (fun r hr hrr => (hnr r hr hrr).trans_lt hτs) Hold Opp hF hopp
    (fun x hx j e hv hs hj => hcast x hx j e hv hs (htc ▸ hrun.time_mono hj.le)) hN
  -- `C` conflicts with no live lock: a block compatible with `D` is compatible with `C ⪯ D`, and
  -- every block that vetoes `D` extends `C`
  have hnvC : ¬ SA.conflictsWithLock sp (tr.state w c).ac.locks ℓ.frame (tr.time c) C := by
    rintro ⟨W, hW, hCW⟩
    by_cases hDW : Compatible ℓ.frame.tree D W
    · rcases hDW with h | h
      · exact hCW (Or.inl (hCD.trans h))
      · exact hCW (SA.anc_total hΦ.coherent hCD h)
    · exact hCW (Or.inl (hveto W hW hDW).2)
  have hlive : sp.slot (tr.time c) ≤ s + sp.k := by
    rw [htc, slot_update_time]; have := sp.two_le_k; omega
  -- independent writes: the slow lock is written on the unvetoed part of the path, vetoed or not
  obtain ⟨L, -, hCL, hl⟩ := SA.updateConfirmation_slow_lock_effective_of hΦ hD hnvC hCt hCg
    hCD hrows hlive (hVA hFC)
  exact Or.inr ⟨L, false, hCL, (locks_after_update hrun hnc hw hu).symm ▸ hl⟩

end Consensus.Goldilocks.Compose

end
