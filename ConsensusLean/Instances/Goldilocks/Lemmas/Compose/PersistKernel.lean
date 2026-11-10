module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.PersistKernel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Conditional FG persistence

The node and FG laws turn compatibility of actual AC sources into the full cut invariant.
Only the opaque AC predicate and source compatibility are supplied by the caller.
-/

namespace Consensus.Goldilocks.FG.Persist

open Compose

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)}
  {proposer : Nat → Fin P.n} {sg : A.Msg → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {Ts T0 T1 : Time} {B : A.Blk}

/-- A pre-state is the initial state of an interval or the post-state of an earlier call. -/
theorem state_of_le {y : Fin P.n} {j k : Nat} (h : j ≤ k) :
    tr.state y k = tr.state y j ∨ ∃ j', j ≤ j' ∧ j' < k ∧ tr.IsCall y j' ∧
      tr.state y k = tr.post j' := by
  induction k, h using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ k hjk ih =>
    by_cases hc : tr.IsCall y k
    · obtain ⟨c, hc'⟩ := hc
      exact Or.inr ⟨k, hjk, k.lt_succ_self, ⟨c, hc'⟩, Trace.state_succ_of_call _ hc'⟩
    · rw [Trace.state_succ_of_not _ fun c hc' => hc ⟨c, hc'⟩]
      exact ih.imp_right fun ⟨j', h₁, h₂, h₃, h₄⟩ => ⟨j', h₁, h₂.trans k.lt_succ_self, h₃, h₄⟩

/-- Recover pre-call caches from the first-cut condition and strictly earlier cut invariants. -/
theorem state_caches (hr : Node.LocalRun proposer dg H sg tr)
    (hK0 : ∀ y ∈ H, ∀ j, Ts ≤ tr.time j → (∀ k < j, tr.time k < Ts) →
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.J B)
    (k : Nat) (hcut : ∀ j < k, CutInv tr H Ts T1 B j) {y : Fin P.n} (hy : y ∈ H)
    (hk : Ts ≤ tr.time k) (hle : ∀ j < k, tr.time j < T1 + P.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  classical
  have hex : ∃ j, Ts ≤ tr.time j := ⟨k, hk⟩
  rcases state_of_le (tr := tr) (y := y) (Nat.find_min' hex hk) with h | ⟨j, hj, hjk, hc, h⟩
  · rw [h]
    exact hK0 y hy _ (Nat.find_spec hex) fun j hj => not_le.mp (Nat.find_min hex hj)
  · rw [h]
    exact (hcut j hjk y hy hc ((Nat.find_spec hex).trans (hr.time_mono hj)) (hle j hjk)).1

private theorem no_call_state {ac : ACTrace A} {y : Fin P.n} {j i : Nat} (hji : j ≤ i)
    (hn : ac.NoCallBetween y j i) : ac.state y i = ac.state y j := by
  induction i, hji using Nat.le_induction with
  | base => rfl
  | succ i hji ih =>
    rw [Trace.state_succ_of_not _ (fun ℓ hc => hn i hji (Nat.lt_succ_self _) ℓ hc)]
    exact ih fun k hk hki => hn k hk (Nat.lt_succ_of_lt hki)

private theorem pre_reachable {ac : ACTrace A} {U : Set A.Blk}
    (hr : ACLocalRun A H U ac) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel A} (hc : ac.CallAt y i ℓ) :
    ∃ Φ t, A.ReachableAt y U (ac.state y i) Φ t ∧ t ≤ ac.time i ∧
      A.CallOK U Φ (ac.time i) ℓ.call ℓ.frame := by
  have reach : ∀ i, ∀ ℓ, ac.CallAt y i ℓ →
      A.ReachableAt y U (ac.post i) ℓ.frame (ac.time i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro ℓ hc
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have he' : ac.post i = (A.step y (ac.state y i) ℓ.frame (ac.time i) ℓ.call).1 :=
        (congrArg Prod.fst he).symm
      rw [he']
      rcases hr.frameLaw y hy i ℓ hc with ⟨hn, Φ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
      · rw [no_call_state (Nat.zero_le i) hn, Trace.state, hr.init y hy]
        exact .step ℓ.call (.init Φ hi hf) (hr.time_nonneg i) hok
      · rw [no_call_state (Nat.succ_le_of_lt hj) hn, Trace.state_succ_of_call _ hc']
        exact .step ℓ.call (ih j hj ℓ' hc') (hr.time_mono hj.le) hok
  rcases hr.frameLaw y hy i ℓ hc with ⟨hn, Φ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
  · refine ⟨Φ, 0, ?_, hr.time_nonneg i, hok⟩
    rw [no_call_state (Nat.zero_le i) hn, Trace.state, hr.init y hy]
    exact .init Φ hi hf
  · refine ⟨ℓ'.frame, ac.time j, ?_, hr.time_mono hj.le, hok⟩
    rw [no_call_state (Nat.succ_le_of_lt hj) hn, Trace.state_succ_of_call _ hc']
    exact reach j ℓ' hc'

private theorem createAtt_T {Λ : FG.Record} {v : Fin P.n} {σe : FG.ChainState P.n}
    {a : FG.Att P.n} {Λ' : FG.Record} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  cases hp : Λ.heightPair σe.h σe.Th with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨h', T, τ⟩ := p
    rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp <;>
      exact hp.2.1.symm

private theorem attest_not_excluded (hq : A.Requirements)
    (hr : Node.LocalRun proposer dg H sg tr) (hnc : Compose.NoCollRun dg tr)
    {V : Nat → Prop} (hs : SourceStep tr H Ts T0 T1 B V) {v : Fin P.n} (hv : v ∈ H)
    {j : Nat} {a : FG.Att P.n} (hc : tr.SignAt v j a)
    (hlo : T0 < tr.time j) (hhi : tr.time j ≤ T1)
    (ih : ∀ i < j, V i ∧ CutInv tr H Ts T1 B i) :
    ∀ E ∈ Store.excludedEntries H (tr.HonestBlocks H) tr.projFG Ts B, a.T ≠ E.root := by
  obtain ⟨C, hc⟩ := hc
  obtain ⟨i, rfl, ℓ, hcall, hto, ht, hC, hfg⟩ := Compose.attest_source hr hv hc
  have hCB := hs i (fun k hk => ih k (by omega)) v hv ℓ C hcall hto hC (ht ▸ hlo) (ht ▸ hhi)
  have hac := Compose.ac_projection P A dg H sg tr proposer hq hr hnc
  have hpc := Compose.projAC_callAt.mpr hcall
  obtain ⟨Φ, t, hreach, htime, hok⟩ := pre_reachable hac hv hpc
  have hΦ : ℓ.frame = Φ := by
    have h := hok.2
    rw [hto] at h
    exact h
  have hsrc := hq.source v _ hac.coherent _ _ _ hreach (tr.time i) htime C
    (by rw [Compose.projAC_state hr hv, ← hΦ]; exact hC)
  have hCf : C ∈ ℓ.frame.tree := hΦ ▸ hsrc.1
  rw [(hr.cutLaw v hv i _ hcall).1] at hCf
  have hCt : C ∈ (tr.state v (i + 1)).fg.tree := by
    rw [hfg]
    exact hCf.1
  have hsub : (tr.state v (i + 1)).fg.tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨v, hv, i + 1, hX⟩
  have hT : a.T = ((tr.state v (i + 1)).fg.σ
      ((tr.state v (i + 1)).fg.σ C.root).Th).Th := createAtt_T (hr.cutLaw v hv _ _ hc).1
  obtain ⟨⟨E, hE, hEr, hEC, -, hETh⟩, -, -⟩ :=
    Store.entry_state_of_source P A.Payload _ _ (Compose.fg_reachable hr hv (i + 1)) C hCt
  have hTE : a.T = E.root := by rw [hT, ← hEr, hETh, hEr]
  intro E' hE' heq
  obtain ⟨hconf, z, hz, k, -, -, hanc, hne⟩ := Store.mem_excludedEntries.mp hE'
  have hE'U := (Anc.mem hanc hne.symm).2
  have hU := Compose.honest_blocks_coherent hr hnc
  have hEE : E' = E := hU.1 hE'U (hsub hE) (heq.symm.trans hTE)
  subst hEE
  apply hconf
  have hEC' := Anc.mono hsub hEC
  rcases hCB with h | h
  · exact Or.inl (hEC'.trans h)
  · exact Anc.total hU hEC' h

private theorem public_le {T : Time} (hT : P.IsPublic T) (hT1 : P.IsPublic T1)
    (h : T < T1 + P.Δ) : T ≤ T1 := by
  obtain ⟨q, rfl⟩ := hT
  obtain ⟨r, rfl⟩ := hT1
  have hΔ := P.hΔ
  have hqr : q < r + 1 := lt_of_mul_lt_mul_left (by nlinarith) hΔ.le
  exact mul_le_mul_of_nonneg_left (show q ≤ r by omega) hΔ.le

private theorem sign_before_delivery (hr : Node.LocalRun proposer dg H sg tr)
    {v y : Fin P.n} (hv : v ∈ H) (hy : y ∈ H) {j' k j₀ : Nat} {C : A.Blk} {a : FG.Att P.n}
    (hs : tr.CallAt v j' (.fg (.attest C (some a)))) {e : Node.Event A}
    (hg : tr.GroupAt proposer dg y j₀ (tr.time k) e) (he : e.phase = 2) (hk : j₀ ≤ k)
    (ht : tr.time j' = tr.time k) : j' < k := by
  obtain ⟨j₁, e₁, i₁, hg₁, rfl, hk₁⟩ := Compose.call_in_group hr hv hs
  have hm := List.mem_of_getElem? hk₁
  obtain ⟨xt, he₁⟩ := Compose.signed_only_in_ticks proposer dg v
    (tr.state v j₁) (tr.time (j₁ + i₁)) e₁ C a hm
  subst he₁
  rw [ht] at hg₁
  have hlen := (List.getElem?_eq_some_iff.1 hk₁).1
  by_contra hjk
  rcases lt_trichotomy j₀ j₁ with hlt | rfl | hgt
  · have h' := hr.phase_order y hy v hv j₀ j₁ _ e (.tick xt) hg hg₁ hlt
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have hn : y = v := ((hg.2.1 0 (List.length_pos_iff.2 hg.1)).1).symm.trans
      (hg₁.2.1 0 (List.length_pos_iff.2 hg₁.1)).1
    subst hn
    have h' := Compose.group_phase hg hg₁
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have := Compose.group_start hg₁ hg hgt.le (by rw [← ht] at hg₁ ⊢; omega)
    omega

private theorem exists_cut_time {e : Node.Event A} (a : Time) :
    ∃ T : Time, P.IsPublic T ∧ T ≤ a ∧ a ≤ T + P.Δ ∧ (T = a → e.phase = 2) ∧
      (a = T + P.Δ → e.phase ≤ 1) := by
  have hΔ := P.hΔ
  have hph : e.phase ≤ 2 := by cases e <;> simp [Node.Event.phase]
  by_cases hpub : P.IsPublic a
  · by_cases he : e.phase ≤ 1
    · refine ⟨a - P.Δ, ?_, by linarith, by linarith, fun h => by linarith, fun _ => he⟩
      obtain ⟨q, rfl⟩ := hpub
      exact ⟨q - 1, by ring⟩
    · exact ⟨a, hpub, le_rfl, by linarith, fun _ => by omega, fun h => by linarith⟩
  · refine ⟨P.Δ * (a / P.Δ), dvd_mul_right _ _, Int.mul_ediv_self_le hΔ.ne',
      (Int.lt_mul_ediv_self_add hΔ).le, fun h => absurd ⟨_, h.symm⟩ hpub, fun h => ?_⟩
    exact absurd ⟨a / P.Δ + 1, h.trans (by ring)⟩ hpub

/-- The FG cut step and strong induction discharge the conditional contract. -/
theorem contract : @Contract P A := by
  intro tr H proposer sg dg hq hr hg hnc Ts T0 T1 B V hT0 hT1 hK0 hK1 hvote hsource
  have hfg := Compose.fg_projection P A dg H sg tr proposer hq hg hr hnc
  have hstore : ∀ z ∈ H, ∀ j, tr.projFG.store z j = (tr.state z j).fg := fun z hz j => by
    change (tr.projFG.state z j).1 = _
    rw [Compose.projFG_state hr hz]
  have hK0' : ∀ z ∈ H, ∀ j, Ts ≤ tr.projFG.time j → (∀ k < j, tr.projFG.time k < Ts) →
      Compatible (tr.HonestBlocks H) (tr.projFG.store z j).F B ∧
        Compatible (tr.HonestBlocks H) (tr.projFG.store z j).J B := fun z hz j h₁ h₂ => by
    rw [hstore z hz]
    exact hK0 z hz j h₁ h₂
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    refine ⟨hvote k ih, ?_⟩
    rintro y hy ⟨c, hc⟩ hk₀ hk₁
    obtain ⟨j₀, e, hgroup, hj₀k, hkj₀⟩ := hr.grouped y hy k c hc
    obtain ⟨T, hTpub, hTa, haT, hTeq, haeq⟩ := exists_cut_time (e := e) (tr.time k)
    have hTle : T ≤ T1 := public_le hTpub hT1 (lt_of_le_of_lt hTa hk₁)
    have hrows : ∀ v ∈ H, ∀ j a, tr.projFG.SignAt v j a → T0 < tr.projFG.time j →
        tr.projFG.time j ≤ T →
        ∀ E ∈ Store.excludedEntries H (tr.HonestBlocks H) tr.projFG Ts B, a.T ≠ E.root := by
      rintro v hv j a ⟨src, hsc⟩ h₁ h₂ E hE
      have hsc' := Compose.projFG_callAt.mp hsc
      have hjk : j < k := by
        by_contra hjk
        have hkj := hr.time_mono (not_lt.mp hjk)
        have hTa' : T = tr.time k := le_antisymm hTa (hkj.trans h₂)
        exact hjk (sign_before_delivery hr hv hy hsc' hgroup (hTeq hTa') hj₀k
          (le_antisymm (h₂.trans hTa) hkj))
      exact attest_not_excluded hq hr hnc hsource hv ⟨src, hsc'⟩ h₁ (h₂.trans hTle)
        (fun i hi => ih i (hi.trans hjk)) E hE
    obtain ⟨hab, hcc⟩ := Store.cut_scope hfg hT0 hTpub hK0'
      (fun E hE => hK1 E (Store.mem_excludedEntries.mp hE)) hrows hy
    have hown : ∀ j ≤ k, ∀ X, tr.AcceptAt y j X → tr.time j = T + P.Δ →
        X.proposer = y ∧ P.slotTime X.slot = T + P.Δ := by
      intro j hj X hX htj
      have hak : tr.time k = T + P.Δ := le_antisymm haT (htj ▸ hr.time_mono hj)
      have he1 := haeq hak
      obtain ⟨j₂, e₂, hg₂, hj₂, hj₂'⟩ := hr.grouped y hy j _ hX
      rw [htj, ← hak] at hg₂
      rw [← hak]
      rcases lt_trichotomy j₂ j₀ with hlt | rfl | hgt
      · exact Compose.accept_in_tick hr hy hg₂
          ((hr.phase_order y hy y hy j₂ j₀ _ e₂ e hg₂ hgroup hlt).trans he1) hj₂
          (by rw [htj, ← hak] at hj₂'; exact hj₂') hX
      · exact Compose.accept_in_tick hr hy hg₂ ((Compose.group_phase hg₂ hgroup).le.trans he1)
          hj₂ (by rw [htj, ← hak] at hj₂'; exact hj₂') hX
      · have := Compose.group_start hgroup hg₂ hgt.le (by omega)
        omega
    have hS : tr.projFG.store y (k + 1) = (tr.post k).fg := by
      rw [hstore y hy, Trace.state_succ_of_call _ hc]
    refine ⟨?_, fun X hX => ?_⟩
    · have := hcc k hk₀ haT fun j hj X hX h₁ => by
        rcases (hr.time_mono hj).trans haT |>.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hown j hj X (Compose.projFG_callAt.mp hX) h⟩
      rwa [hS] at this
    · have := hab k X (Compose.projFG_callAt.mpr hX) hk₀ (by
        rcases haT.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hown k le_rfl X hX h⟩)
      simpa only [hS] using this

end Consensus.Goldilocks.FG.Persist
