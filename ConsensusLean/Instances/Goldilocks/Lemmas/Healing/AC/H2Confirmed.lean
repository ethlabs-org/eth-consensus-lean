module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed

public section

/-! # Goldilocks Healing: H.2 (ii), persistent inclusion after a unanimous honest proposal

workbench `h2-open-items.md` §7: the unanimous batch of slot `p` propagates to every later honest
vote (§7.1: `(P, p)` is protected by P3, so `h2_votes_continue`); every surviving lock image
compares with `P` (§7.2, `h2_locks_compare`); the record read by `ac_confirmed` extends `P`
(§§7.3–7.4, `h2_record_extends`, open), and so does the head (§7.5, `h2_head_extends`, open);
`ac_confirmed` is their deepest common ancestor (`anc_acConfirmed`, from the frame lemma
`anc_acConfirmed_of_frame` of `AC/Confirmed`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- The reads of H.2 (ii): calls of honest nodes from `t_p + 6Δ` on (at `t_p + 6Δ` itself,
from the node's tick there on). -/
def LateRead (tr : SATrace sp FGP ro) (p : Nat) (y : Fin sp.n) (j : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) : Prop :=
  tr.CallAt y j ℓ ∧ sp.ts p + 6 * sp.Δ ≤ tr.time j ∧
    (tr.time j = sp.ts p + 6 * sp.Δ →
      ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j)

/-- **§7.2, all surviving lock images compare with `P`**: from `t_p` on, every stored lock of an
honest node live at a time `T ≥ t_p` is on a block compatible with `P`: a label `< p` sits below
a clean raw origin (drain, §5), which an honest slot-`p` vote extends with `P` (§6.1); a label
`≥ p` sits below a fast origin's block or a slow origin's result, which an honest vote of its
slot extends (the fast test or optimistic seats; the result's majority over all honest voters),
and that vote extends `P` (§7.1). -/
theorem h2_locks_compare (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
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
      obtain ⟨ℓX, C, hupd, hconf, -, hdeep, -⟩ := hsl
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

/-- **§§7.3–7.4, the record**: at every late read, the record that `ac_confirmed` reads (the
latest confirmed block in the frame, else `Φ.F`) extends `P` (the first test at `t_p + 6Δ`
leaves a record extending `P` or `P ⪯ Φ.F`; every later receipt, tick and record write keeps
it). -/
theorem h2_record_extends (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ →
      Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F) := by
  sorry

/-- **§7.5, full heads**: at every late read, the head extends `P` (`P ⪯ fc_root`, or the
anchor compares with `P` by §7.2 and the latest view's honest votes, all extending `P`, give
every child toward `P` a strict majority). -/
theorem h2_head_extends (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i (T : Time), sp.ts p ≤ T → ∀ l ∈ (tr.state y i).locks,
      sp.slot T ≤ l.slot + sp.k → ∀ L ∈ U, L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ → Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  sorry

/-- **The confirmed tip extends a block both of its inputs extend** (`ac_confirmed` is the
deepest common ancestor of the record and the head in the frame's tree). -/
theorem anc_acConfirmed (hI : InclusionRun tr H U g t₀) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {P : Blk sp.n FGP}
    (hC : Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F))
    (hH : Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j))) :
    Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hI.run.localRun hy hc
  exact anc_acConfirmed_of_frame hI.run.localRun.coherent hΦ hΦU hC hH

/-- **H.2 (ii), §7**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ`, if every
honest vote of slot `p` is `P`, then at every call of an honest node from `t_p + 6Δ` on (at
`t_p + 6Δ` itself, from its tick there on), `P ⪯ ac_confirmed` after the call. -/
theorem h2_proposal_confirmed (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  -- `P` is a frame block, protected by P3; §7.1 propagates the unanimous batch
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
  exact anc_acConfirmed hI hy hc (h2_record_extends hI hpH hP hp hvotes hlocks y hy j ℓ hr)
    (h2_head_extends hI hpH hP hp hvotes hlocks y hy j ℓ hr)

end Consensus.Goldilocks.SA

end
