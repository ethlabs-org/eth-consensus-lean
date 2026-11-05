module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Persist, part 2: the cut step of C1.1

G1.10 at the scope of C1.1 at an honest call at cut `k` (claims C1.1, "Proof shape"): apply the
FG statement over the FG projection of the run (`cut_scope`, FGStore) with `T₀ = t_{s+1} + Δ` and
`T` the greatest public time before the call's time `a` for a step of a tick (or a restart) at a
public `a`, else the greatest public time at most `a`. Then every honest attestation signed in
`(T₀, T]` is at an earlier cut (a tick's attestations precede the deliveries of its time), where the
attestation step (`attest_not_excluded`) applies. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)



/-! ### The cut step -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {proposer : Nat → Fin sp.n}

/-- A public time below `t_m + 2Δ` is at most `t_m + Δ`. -/
private theorem public_le {T : Time} (hT : sp.toParams.IsPublic T) {m : Nat}
    (h : T < sp.ts m + 2 * sp.Δ) : T ≤ sp.ts m + sp.Δ := by
  obtain ⟨q, rfl⟩ := hT
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have e : sp.ts m + 2 * sp.Δ = sp.Δ * (4 * m + 2) := by simp only [SA.SAParams.ts]; ring
  have e' : sp.ts m + sp.Δ = sp.Δ * (4 * m + 1) := by simp only [SA.SAParams.ts]; ring
  rw [e] at h
  rw [e']
  have h₁ : q < 4 * (m : Int) + 2 := lt_of_mul_lt_mul_left h hΔ.le
  have h₂ : q ≤ 4 * (m : Int) + 1 := by omega
  exact mul_le_mul_of_nonneg_left h₂ hΔ.le

/-- An honest signing at the time of a cut of a delivery is at an earlier cut: the ticks of a
time precede its deliveries (F.5 (run)). -/
private theorem sign_before_delivery (hrun : GoldilocksRun proposer dg H tr)
    {v y : Fin sp.n} (hv : v ∈ H)
    (hy : y ∈ H) {j' k j₀ : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hs : tr.CallAt v j' (.fg (.attest C (some a)))) {e : Node.Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j₀ (tr.time k) e) (he : e.phase = 2) (hk : j₀ ≤ k)
    (ht : tr.time j' = tr.time k) : j' < k := by
  obtain ⟨j₁, e₁, i₁, hg₁, rfl, hk₁⟩ := call_in_group hrun.toLocalRun hv hs
  have hm : Cut.fg (.attest C (some a)) ∈
      (Node.exec proposer dg v (tr.state v j₁) (tr.time (j₁ + i₁))
      e₁).2 := List.mem_of_getElem? hk₁
  obtain ⟨xt, he₁⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg v
    (tr.state v j₁) (tr.time (j₁ + i₁)) e₁ C a hm
  subst he₁
  rw [ht] at hg₁
  have hlen := (List.getElem?_eq_some_iff.1 hk₁).1
  by_contra hjk
  rcases lt_trichotomy j₀ j₁ with hlt | rfl | hgt
  · have h' : e.phase ≤ Node.Event.phase (.tick xt : Node.Event (goldilocksNode sp ro)) :=
      hrun.phase_order y hy v hv j₀ j₁ _ e (.tick xt) hg hg₁ hlt
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have hn : y = v := ((hg.2.1 0 (List.length_pos_iff.2 hg.1)).1).symm.trans
      (hg₁.2.1 0 (List.length_pos_iff.2 hg₁.1)).1
    subst hn
    have h' : e.phase = Node.Event.phase (.tick xt : Node.Event (goldilocksNode sp ro)) :=
      group_phase hg hg₁
    rw [he] at h'
    simp [Node.Event.phase] at h'
  · have := group_start hg₁ hg (le_of_lt hgt) (by rw [← ht] at hg₁ ⊢; omega)
    omega

variable {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
  {CV : Set (Vote sp.n)}

/-- The time `T` of G1.10 for a cut at time `a` of an event `e`: public, at most `a`, with
`a ≤ T + Δ`; `T = a` only for a delivery, `a = T + Δ` only for a restart or a tick. -/
private theorem exists_cut_time {e : Node.Event (goldilocksNode sp ro)} (a : Time) :
    ∃ T : Time, sp.toParams.IsPublic T ∧ T ≤ a ∧ a ≤ T + sp.Δ ∧ (T = a → e.phase = 2) ∧
      (a = T + sp.Δ → e.phase ≤ 1) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hph : e.phase ≤ 2 := by cases e <;> simp [Node.Event.phase]
  by_cases hpub : sp.toParams.IsPublic a
  · by_cases he : e.phase ≤ 1
    · refine ⟨a - sp.Δ, ?_, by linarith, by linarith, fun h => by linarith, fun _ => he⟩
      exact dvd_sub hpub (dvd_refl _)
    · exact ⟨a, hpub, le_rfl, by linarith, fun _ => by omega, fun h => by linarith⟩
  · refine ⟨sp.Δ * (a / sp.Δ), dvd_mul_right _ _, Int.mul_ediv_self_le hΔ.ne',
      (Int.lt_mul_ediv_self_add hΔ).le, fun h => absurd ⟨_, h.symm⟩ hpub, fun h => ?_⟩
    exact absurd ⟨a / sp.Δ + 1, h.trans (by ring)⟩ hpub

/-- **The cut step**: G1.10 at the scope of C1.1 at the honest call of cut `k`, from the
invariant at every earlier cut. -/
theorem cut_inv_step (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) : CutInv tr H s m B k := by
  rw [cutInv_iff]
  rintro y hy ⟨c, hc⟩ hk₀ hk₁
  have hlocal := hrun.toLocalRun
  have hfg := fg_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer
    (Compose.requirements sp ro) hrun.genesis_root_ok hlocal hp.noColl
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hstore : ∀ z ∈ H, ∀ j, tr.projFG.store z j = (tr.state z j).fg := fun z hz j => by
    change (tr.projFG.state z j).1 = _
    rw [projFG_state hlocal hz]
  have hT₀ : sp.toParams.IsPublic (sp.ts (s + 1 : Nat) + sp.Δ) :=
    ⟨4 * (s + 1 : Nat) + 1, by simp only [SA.SAParams.ts]; ring⟩
  have hex : ∀ E, E ∈ Store.excludedEntries H (tr.HonestBlocks H) tr.projFG (sp.ts s) B →
      E ∈ excludedEntries tr H s B := by
    intro E hE
    obtain ⟨hnc, z, hz, j, h₁, h₂, h₃, h₄⟩ := Store.mem_excludedEntries.mp hE
    rw [hstore z hz] at h₃ h₄
    exact ⟨hnc, z, hz, j, ⟨h₁, h₂⟩, h₃, h₄⟩
  have hK0 : ∀ z ∈ H, ∀ j, sp.ts s ≤ tr.projFG.time j → (∀ k < j, tr.projFG.time k < sp.ts s) →
      Compatible (tr.HonestBlocks H) (tr.projFG.store z j).F B ∧
        Compatible (tr.HonestBlocks H) (tr.projFG.store z j).J B := fun z hz j h₁ h₂ => by
    rw [hstore z hz]
    exact hp.clean.caches z hz j ⟨h₁, h₂⟩
  obtain ⟨j₀, e, hg, hj₀k, hkj₀⟩ := hlocal.grouped y hy k c hc
  obtain ⟨T, hTpub, hTa, haT, hTeq, haeq⟩ := exists_cut_time (e := e) (tr.time k)
  have hTle : T ≤ sp.ts m + sp.Δ := public_le hTpub (lt_of_le_of_lt hTa hk₁)
  have hrows : ∀ v ∈ H, ∀ j a, tr.projFG.SignAt v j a → sp.ts (s + 1 : Nat) + sp.Δ <
      tr.projFG.time j → tr.projFG.time j ≤ T →
      ∀ E ∈ Store.excludedEntries H (tr.HonestBlocks H) tr.projFG (sp.ts s) B, a.T ≠ E.root := by
    rintro v hv j a ⟨src, hsc⟩ h₁ h₂ E hE
    have hsc' := projFG_callAt.mp hsc
    have hjk : j < k := by
      by_contra hjk
      have hkj := hrun.time_mono (not_lt.mp hjk)
      have hTa' : T = tr.time k := le_antisymm hTa (hkj.trans h₂)
      exact hjk (sign_before_delivery hrun hv hy hsc' hg (hTeq hTa') hj₀k
        (le_antisymm (h₂.trans hTa) hkj))
    exact attest_not_excluded hrun hp hv ⟨src, hsc'⟩ h₁ (h₂.trans hTle)
      (fun i hi => ih i (hi.trans hjk)) E (hex E hE)
  obtain ⟨hab, hcc⟩ :=
    Store.cut_scope hfg hT₀ hTpub hK0 (fun E hE => hp.clean.fgAttCut E (hex E hE))
    hrows hy
  -- an acceptance at `T + Δ` up to cut `k` is the own proposal
  have hown : ∀ j ≤ k, ∀ X, tr.AcceptAt y j X → tr.time j = T + sp.Δ →
      X.proposer = y ∧ sp.toParams.slotTime X.slot = T + sp.Δ := by
    intro j hj X hX htj
    have hak : tr.time k = T + sp.Δ := le_antisymm haT (htj ▸ hrun.time_mono hj)
    have he1 := haeq hak
    obtain ⟨j₂, e₂, hg₂, hj₂, hj₂'⟩ := hlocal.grouped y hy j _ hX
    rw [htj, ← hak] at hg₂
    rw [← hak]
    rcases lt_trichotomy j₂ j₀ with hlt | rfl | hgt
    · exact accept_in_tick hlocal hy hg₂ ((hrun.phase_order y hy y hy j₂ j₀ _ e₂ e hg₂ hg
        hlt).trans he1) hj₂ (by rw [htj, ← hak] at hj₂'; exact hj₂') hX
    · exact accept_in_tick hlocal hy hg₂ ((group_phase hg₂ hg).le.trans he1) hj₂
        (by rw [htj, ← hak] at hj₂'; exact hj₂') hX
    · have := group_start hg hg₂ hgt.le (by omega)
      omega
  have hS : tr.projFG.store y (k + 1) = (tr.post k).fg := by
    rw [hstore y hy, Trace.state_succ_of_call _ hc]
  refine ⟨?_, fun X hX => ?_⟩
  · have := hcc k hk₀ haT fun j hj X hX h₁ => by
      rcases (hrun.time_mono hj).trans haT |>.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hown j hj X (projFG_callAt.mp hX) h⟩
    rwa [hS] at this
  · have := hab k X (projFG_callAt.mpr hX) hk₀ (by
      rcases haT.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hown k le_rfl X hX h⟩)
    simpa only [hS] using this

end Consensus.Goldilocks.Compose

end
