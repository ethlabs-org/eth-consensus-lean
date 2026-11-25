module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Select
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Delivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Votes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.ServedRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic inclusion: the record of a reader extends the proposal

For the proposal `P` of slot `p > 0` of a proposer honest at `t_p + Δ`, backed by every honest
slot-`p` vote and with a quarter-bounded committee (`Q`: members awake and joined at `t_p + Δ` and
honest at `t_p + 2Δ`, at least three quarters of the committee size), a node `y` awake and joined
throughout `[t_p, t_p + 2Δ]` runs, before `t_p + 2Δ`, an optimistic check that selects `P`: the
latest of the cuts at which `P` and the votes of `Q` reach it (`proposal_point_at`,
`vote_point_at`), at its last point (`point_top`). The record after that cut names a descendant
of `P` (`call_record_extends`), and it only extends afterwards (`record_step_at`):
`optimistic_record_extends_at`.

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- A block an optimistic check selects passes the three-quarter test of the check's slot. -/
private theorem optimisticSelect_pass {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {t : Time} {B : AC.Blk sp.n FGP} (h : AC.optimisticSelect sp A Φ t = some B) :
    3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A Φ (sp.slot t) B).ncard := by
  unfold AC.optimisticSelect at h
  dsimp only at h
  split_ifs at h
  exact (AC.deepest_mem h).1.2.1

/-- An optimistic point of the prefix through its call is one of the run. -/
private theorem optimisticPoint_upTo_iff {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {A : AC.ACState sp.n} :
    AC.OptimisticPoint (tr.projAC.upTo (tr.time i)) y i ℓ A ↔
      AC.OptimisticPoint tr.projAC y i ℓ A := by
  rw [AC.upTo_optimisticPoint hrun.time_mono]
  exact ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩

/-- **The last point of a call**, at the run: `point_top` on the prefix through the call. -/
private theorem point_top_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hnr : ℓ.call ≠ .restart) {A₀ : AC.ACState sp.n}
    (h₀ : AC.OptimisticPoint tr.projAC y i ℓ A₀) :
    ∃ A, AC.OptimisticPoint tr.projAC y i ℓ A ∧
      (∀ A', AC.OptimisticPoint tr.projAC y i ℓ A' → ∀ σ, A'.pool σ ⊆ A.pool σ) ∧
      (∀ σ, (tr.state y i).ac.pool σ ⊆ A.pool σ) ∧
      A.restartTime = (tr.projAC.state y i).restartTime := by
  have ha := (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun
  have hup := fun A => optimisticPoint_upTo_iff hrun (y := y) (i := i) (ℓ := ℓ) (A := A)
  have hst := projAC_upTo_state hrun (y := y) (le_refl (tr.time i))
  obtain ⟨A, hA, hall, hS, hr⟩ := point_top ha hy hnr ((hup A₀).2 h₀)
  refine ⟨A, (hup A).1 hA, fun A' hA' => hall A' ((hup A').2 hA'), fun σ v hv => hS σ ?_, ?_⟩
  · rw [hst, projAC_state_at hrun hy]; exact hv
  · rw [hr, hst]

/-- **The record after a check that selects `P`**, at the run: `call_record_extends` on the
prefix through the call, lifted to the blocks held while honest. -/
private theorem record_after_check_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hbelow : ∀ A B, AC.OptimisticPoint tr.projAC y i ℓ A →
      AC.optimisticSelect sp A ℓ.frame (tr.time i) = some B → ℓ.frame.Anc B P)
    {A₀ : AC.ACState sp.n} (hpt : AC.OptimisticPoint tr.projAC y i ℓ A₀)
    (hsel : AC.optimisticSelect sp A₀ ℓ.frame (tr.time i) = some P) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocksAt H) P E := by
  have hd := hrun.time_nonneg i
  have ha := (acRun_upTo hrun hnc hd).localRun
  have hup := fun A => optimisticPoint_upTo_iff hrun (y := y) (i := i) (ℓ := ℓ) (A := A)
  have hc' : (tr.projAC.upTo (tr.time i)).CallAt y i ℓ :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  obtain ⟨E, hE, hEr, hPE⟩ := call_record_extends ha hy hc'
    (fun A B hA hB => hbelow A B ((hup A).1 hA) hB) ((hup A₀).2 hpt) hsel
  have hpost : (tr.projAC.upTo (tr.time i)).post i = (tr.state y (i + 1)).ac := by
    rw [← AC.state_succ_of_call hc']
    have h := projAC_state (hrun.upTo hd).toLocalRun hy (i + 1)
    rw [RunTrace.upTo_projAC] at h
    rw [h, Trace.upTo_state tr y fun k hk => hrun.time_mono (Nat.lt_succ_iff.mp hk)]
  obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hy hc
  exact ⟨E, hΦU hE, hEr.trans (by rw [hpost]), hPE.mono hΦU⟩

/-- **An honest proposal is of a slot `> 0`**: the own proposal of a tick at the start of its
slot, which is not slot `0` (a block call at position `0` of its group is a delivery). -/
theorem proposesAt_slot_pos {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {p₀ : Fin sp.n} {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hp : p₀ ∈ H (tr.time k))
    (hP : tr.ProposesAt p₀ k P) : 0 < P.slot := by
  have hd := hrun.time_nonneg k
  obtain ⟨⟨acc, hc⟩, hpos⟩ := hP.1
  have hc' : (tr.upTo (tr.time k)).CallAt p₀ k (.fg (.block P acc)) :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  rcases blockCall_cases (hrun.upTo hd).toLocalRun hp hc' with hg |
    ⟨j₀, x, f, rfl, -, hPr, d, q, -, hB, -⟩
  · exact (hpos (hg.2.1 0 (List.length_pos_of_ne_nil hg.1)).2.2.2.1).elim
  · have hs : P.slot = sp.toParams.slotOf ((tr.upTo (tr.time (j₀ + 2))).time (j₀ + 2)) := by
      rw [hB]; rfl
    rw [hs]
    exact hPr.1

/-- The slot of a proposal released at `t_p` is `p`. -/
theorem proposesAt_slot_eq {p₀ : Fin sp.n} {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p₀ k P) {p : Nat} (hk : tr.time k = sp.ts p) : P.slot = p := by
  have h := hP.2.2
  rw [hk, sp.slotTime_eq] at h
  simp only [ACParams.ts] at h
  have := AC.four_delta_pos sp
  exact_mod_cast (mul_left_cancel₀ this.ne' h).symm

/-- **A3: the record of a node awake and joined through the optimistic window extends the
proposal.** For the proposal `P` of slot `p > 0` of a proposer honest at `t_p + Δ`, backed by
every slot-`p` vote of a node honest at `t_p + Δ`, with at least three quarters of the committee
size among the members of slot `p`'s committee awake and joined at `t_p + Δ` and honest through
`t_p + 2Δ` (which gives their votes' timely delivery and uniqueness), and with the optimistic
confirmation on: the record of a node honest at `t ≥ t_p + 2Δ` and awake and joined throughout
`[t_p, t_p + 2Δ]`, after all events at `t`, names a descendant of `P`. The finite inputs hold
through a proof horizon `b ≥ max t (t_p + 6Δ)`; `t_p + 6Δ` is only the horizon the proposal's
origin facts are read through (`proposal_point_at`, `proposal_not_conflicts_point_at`), not a
premise on honesty or delivery. -/
theorem optimistic_record_extends_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b) (hopt : sp.optimistic = true)
    (hcs : 0 < sp.committeeSize) {p₀ : Fin sp.n} {kP : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {p : Nat} (hp₀ : p₀ ∈ H (sp.ts p + sp.Δ))
    (hP : tr.ProposesAt p₀ kP P) (hPs : P.slot = p) (hpos : 0 < p)
    (hsb : sp.ts p + 6 * sp.Δ ≤ b) (hU : Healing.Unanimous tr (H (sp.ts p + sp.Δ)) p P)
    (hQ : 3 * sp.committeeSize ≤
      4 * {x | x ∈ K.committee p ∧ x ∈ H (sp.ts p + 2 * sp.Δ) ∧
        tr.awake x (sp.ts p + sp.Δ) ∧ tr.JoinedAt x (sp.ts p + sp.Δ)}.ncard)
    {y : Fin sp.n} {t : Time} {j : Nat} (ht : sp.ts p + 2 * sp.Δ ≤ t) (htb : t ≤ b)
    (hyt : y ∈ H t)
    (hw : ∀ d, sp.ts p ≤ d → d ≤ sp.ts p + 2 * sp.Δ → tr.awake y d ∧ tr.JoinedAt y d)
    (hj : Regimes.CutAfter tr j t) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y j).ac.latestConfirmed ∧
      Anc (tr.HonestBlocksAt H) P E := by
  classical
  have hΔ := sp.toParams.hΔ
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set Q := {x | x ∈ K.committee (q + 1) ∧ x ∈ H (sp.ts (q + 1 : Nat) + 2 * sp.Δ) ∧
    tr.awake x (sp.ts (q + 1 : Nat) + sp.Δ) ∧ tr.JoinedAt x (sp.ts (q + 1 : Nat) + sp.Δ)}
    with hQdef
  have hpb : sp.ts (q + 1 : Nat) + 2 * sp.Δ ≤ b := by linarith
  have hyd : y ∈ H (sp.ts (q + 1 : Nat) + 2 * sp.Δ) := hrun.antitone ht hyt
  -- each member of `Q` has a vote for `P` that reaches `y` in time
  have hitem : ∀ x ∈ Q, ∃ k, ∃ v : Vote sp.n, v.val = x ∧ v.head = P.root ∧
      (∃ ℓ A, AC.OptimisticPoint tr.projAC y k ℓ A ∧ sp.ts (q + 1 : Nat) ≤ tr.time k ∧
        tr.time k < sp.ts (q + 1 : Nat) + 2 * sp.Δ ∧ v ∈ A.pool (q + 1)) ∧
      ∀ m, k < m → tr.time m < sp.ts (q + 1 : Nat) + 2 * sp.Δ →
        v ∈ (tr.state y m).ac.pool (q + 1) := by
    rintro x ⟨hxK, hxd, hxw, hxj⟩
    have hx1 : x ∈ H (sp.ts (q + 1 : Nat) + sp.Δ) := hrun.antitone (by linarith) hxd
    obtain ⟨jx, e, he, hes, heh, -⟩ := committee_votes_proposal_at hrun hnc hsync hB hinv hp₀ hP
      hPs hsb hKB hBK hx1 hxK hxw hxj
    obtain ⟨k, ℓ, A, hpt, h1, h2, hv, hper⟩ := vote_point_at hrun hnc hsync hpb hyd hw hxd he hes
    obtain ⟨hxj', ℓv, hcv⟩ := hVoteAt_iff.1 he
    exact ⟨k, e.msg, (castAt_spec_at hrun hnc hxj' hcv).1, heh,
      ⟨ℓ, A, hpt, h1, h2, hv⟩, hper⟩
  obtain ⟨kq, ℓq, Aq, hptq, hq1, hq2, hPq, hPper⟩ := proposal_point_at hrun hnc hb0 hsync hB hinv
    hp₀ hP hPs hsb hKB hBK hyd hw
  -- the check cut: the latest of these cuts
  let g : Fin sp.n → Nat := fun x => if h : x ∈ Q then Classical.choose (hitem x h) else 0
  set js := max kq (Finset.univ.sup g) with hjs
  have hgle : ∀ x, g x ≤ js := fun x => le_max_of_le_right (Finset.le_sup (Finset.mem_univ x))
  have hkq : kq ≤ js := le_max_left _ _
  have hjpt : ∃ ℓ A, AC.OptimisticPoint tr.projAC y js ℓ A ∧ sp.ts (q + 1 : Nat) ≤ tr.time js ∧
      tr.time js < sp.ts (q + 1 : Nat) + 2 * sp.Δ := by
    rcases le_total (Finset.univ.sup g) kq with h | h
    · rw [hjs, max_eq_left h]
      exact ⟨ℓq, Aq, hptq, hq1, hq2⟩
    · rw [hjs, max_eq_right h]
      obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨y, Finset.mem_univ _⟩ g
      by_cases hxQ : x ∈ Q
      · have hgx : g x = Classical.choose (hitem x hxQ) := by
          simp only [g, hxQ, ↓reduceDIte]
        obtain ⟨v, -, -, ⟨ℓ, A, hpt, h1, h2, -⟩, -⟩ := Classical.choose_spec (hitem x hxQ)
        rw [hx, hgx]
        exact ⟨ℓ, A, hpt, h1, h2⟩
      · have hgx : g x = 0 := by simp only [g, hxQ, ↓reduceDIte]
        rw [show Finset.univ.sup g = kq by omega]
        exact ⟨ℓq, Aq, hptq, hq1, hq2⟩
  obtain ⟨ℓ, A₀, hpt₀, hjs1, hjs2⟩ := hjpt
  have hc := hpt₀.1
  have hyj : y ∈ H (tr.time js) := hrun.antitone hjs2.le hyd
  have hsl : sp.slot (tr.time js) = q + 1 := slot_eq_of_window hjs1 (by linarith)
  have hsl' : sp.toParams.slotOf (tr.time js) = q + 1 := hsl
  have hts : sp.ts (q : Nat) + 4 * sp.Δ = sp.ts (q + 1 : Nat) := by
    simp only [ACParams.ts]; push_cast; ring
  -- `y` restarted, if at all, before slot `p`, so the check cut is no restart and `y` is joined
  have hres : ∀ r, tr.RestartAt y r → tr.time r ≤ tr.time js →
      tr.time r ≤ sp.ts (q : Nat) := by
    intro r hr hrt
    have h := ((hw (tr.time js) hjs1 (by linarith)).2 r hr hrt).2
    rw [hsl', Nat.add_sub_cancel, sp.slotTime_eq] at h
    simpa only [ACParams.ts] using h
  have hnr : ℓ.call ≠ .restart := fun h => by
    have := hres js (Compose.projAC_restartAt.mp ⟨ℓ, hc, h⟩) le_rfl
    linarith
  have hjoinS := Healing.Growing.joined_of_restart_le_at hrun hnc hyj (u := q)
    (by rw [hts]; exact hjs1)
    (fun r hrt _ hr => hres r hr hrt) rfl
  obtain ⟨A, hA, hall, hS, hAr⟩ := point_top_at hrun hnc hyj hnr hpt₀
  have hjA : AC.joined sp A (tr.time js) := by
    unfold AC.joined at hjoinS ⊢
    rw [hAr]
    exact hjoinS
  have huniq : ∀ ℓ', tr.projAC.CallAt y js ℓ' → ℓ' = ℓ :=
    fun ℓ' h => Option.some.inj (h.2.symm.trans hc.2)
  have hPt : P ∈ ℓ.frame.tree := by
    rcases hkq.lt_or_eq with h | h
    · exact hPper js ℓ h hjs2 hc
    · rw [← huniq ℓq (h ▸ hptq.1)]
      exact hPq
  -- `Q` are optimistic voters of `P` at the last point of the check cut
  have hQsub : Q ⊆ AC.optimisticVoters sp A ℓ.frame (q + 1) P := by
    intro x hxQ
    have hgx : g x = Classical.choose (hitem x hxQ) := by
      simp only [g, hxQ, ↓reduceDIte]
    have hle : Classical.choose (hitem x hxQ) ≤ js := hgx ▸ hgle x
    obtain ⟨v, hvx, hvh, ⟨ℓx, Ax, hptx, -, -, hvA⟩, hper⟩ := Classical.choose_spec (hitem x hxQ)
    refine ⟨v, ?_, hvx, P, hPt, hvh.symm, Relation.ReflTransGen.refl⟩
    rcases hle.lt_or_eq with h | h
    · exact hS _ (hper js h hjs2)
    · rw [h] at hptx
      obtain rfl := huniq ℓx hptx.1
      exact hall Ax hptx _ hvA
  have hPass : 3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A ℓ.frame (q + 1) P).ncard :=
    hQ.trans (Nat.mul_le_mul_left 4 (Set.ncard_le_ncard hQsub (Set.toFinite _)))
  have hQK : Q ⊆ K.committee (q + 1) := fun x hx => hx.1
  have hQH : Q ⊆ H (sp.ts (q + 1 : Nat) + 2 * sp.Δ) := fun x hx => hx.2.1
  have hbelow : ∀ A' B, AC.OptimisticPoint tr.projAC y js ℓ A' →
      AC.optimisticSelect sp A' ℓ.frame (tr.time js) = some B → ℓ.frame.Anc B P := by
    intro A' B hA' hB
    have h3 := optimisticSelect_pass hB
    rw [hsl] at h3
    exact optimistic_pass_anc hrun hnc hKB hcs hU hQK hQH hQ hyj hjs2.le hA' hPt h3
  obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hyj hc
  have hlock := proposal_not_conflicts_point_at hrun hnc hb0 hsync hB hinv hp₀ hP hPs hsb hKB hBK
    hyj hA (by linarith) hPt (by rw [hsl]; omega)
    (fun D CV ⟨ℓ', A', hA', _, hsel', _⟩ => by
      obtain rfl := huniq ℓ' hA'.1
      exact Or.inl ((hbelow A' D hA' hsel').mono hΦU)) (tr.time js)
  have hsel := optimisticSelect_eq_proposal hrun hnc hopt hKB hcs (Nat.succ_pos q) hU hQK hQH hQ
    hyj hjs1 hjs2 hA hjA hPt hPass hlock
  obtain ⟨E, hE, hEr, hPE⟩ := record_after_check_at hrun hnc hyj hc hbelow hA hsel
  -- the record only extends from the check cut to `j`
  have hjj : js + 1 ≤ j := by
    by_contra hh
    have := hrun.time_mono (show j ≤ js by omega)
    linarith [hj.2]
  have key : ∀ i, js + 1 ≤ i → i ≤ j → ∃ E ∈ tr.HonestBlocksAt H,
      E.root = (tr.state y i).ac.latestConfirmed ∧ Anc (tr.HonestBlocksAt H) P E := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact fun _ => ⟨E, hE, hEr, hPE⟩
    | succ i _ ih =>
      intro hij
      obtain ⟨E₁, hE₁, hE₁r, hPE₁⟩ := ih (by omega)
      have hiy : y ∈ H (tr.time i) := hrun.antitone (hj.1 i (by omega)) hyt
      obtain ⟨E', hE', hE'r, hEE'⟩ := record_step_at hinv hrun hnc hiy
        (fun k hk => (hj.1 k (by omega)).trans htb) E₁ hE₁ hE₁r
      exact ⟨E', hE', hE'r, hPE₁.trans hEE'⟩
  exact key j hjj le_rfl

end Consensus.Goldilocks.Compose.Growing

end
