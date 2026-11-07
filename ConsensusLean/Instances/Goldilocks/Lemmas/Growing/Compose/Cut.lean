module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Algebra.Ring.Divisibility.Basic
meta import Mathlib.Tactic.Ring

public section

/-! # Persistence cut step with faults charged at consumption

The quorum-free entry argument uses the growing FG run and the namer budget at
`t_m + 2Δ`. Only the receiving node's store transitions are retained statically.
-/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

private theorem public_le {sp : SAParams} {T : Time} (hT : sp.toParams.IsPublic T) {m : Nat}
    (h : T < sp.ts m + 2 * sp.Δ) : T ≤ sp.ts m + sp.Δ := by
  obtain ⟨q, rfl⟩ := hT
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have e : sp.ts m + 2 * sp.Δ = sp.Δ * (4 * m + 2) := by simp only [SA.SAParams.ts]; ring
  have e' : sp.ts m + sp.Δ = sp.Δ * (4 * m + 1) := by simp only [SA.SAParams.ts]; ring
  rw [e] at h
  rw [e']
  have h₁ : q < 4 * (m : Int) + 2 := lt_of_mul_lt_mul_left h hΔ.le
  exact mul_le_mul_of_nonneg_left (show q ≤ 4 * (m : Int) + 1 by omega) hΔ.le

private theorem exists_cut_time {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {e : Node.Event (goldilocksNode sp ro)} (a : Time) :
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

/-! The following store-local facts do not assume anything about the origins of messages.
They are applied only to a prefix ending at the receiving node's honest call. -/

private theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.h = σ.h ∧ σ'.Th = σ.Th) ∨ (σ'.h = σ.h + 1 ∧ σ'.Th = B.root)) ∧
      ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

private theorem compatible_of_anc {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}
    (hS : Coherent S) {A B C : Block n FGP ACP} (hAC : Anc S A C)
    (hC : Compatible S C B) : Compatible S A B := by
  rcases hC with hCB | hBC
  · exact Or.inl (hAC.trans hCB)
  · exact Anc.total hS hAC hBC

private theorem onBlock_FJ {P : Params} {ACP : Type} {st st' : Store P ACP}
    {X : NodeBlock P ACP} (h : st.onBlock X = some st') :
    (st'.J = st.J ∨ st'.blocks (st'.σ X.root).J = some st'.J) ∧
      (st'.F = st.F ∨ st'.Anc st'.F st'.J) := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Store.onBlock_eq_some h
  set st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks X.root (some X),
              σ := Function.update st.σ X.root σ' }
  obtain ⟨atts, he⟩ := Store.addAtts_eq (Store.updateFinality st₁ σ') X.fgPayload
  obtain ⟨hb, hσ, -, -, hJ, hF⟩ := Store.updateFinality_spec st₁ σ'
  have ht : ({ Store.updateFinality st₁ σ' with atts := atts } : Store P ACP).tree = st₁.tree := by
    simp only [Store.tree, hb]
  have h₁ : st₁.σ X.root = σ' := Function.update_self ..
  rw [he, Store.Anc, ht]
  simp only [hb, hσ, h₁]
  exact ⟨hJ.imp (·.1) (·.1), hF.imp id (·.2.2.2)⟩

section StoreFacts

open Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H₀ : Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {ft : FGTrace P ACP}

private theorem tree_mono (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {k m : Nat} (hkm : k ≤ m) : (ft.store y k).tree ⊆ (ft.store y m).tree :=
  fun Z (hZ : (ft.store y k).blocks Z.root = some Z) => (held_mono hr hy hkm hZ).1

private theorem accept_mem (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {i : Nat} {X : NodeBlock P ACP} (hX : ft.AcceptAt y i X) :
    X ∈ (ft.store y (i + 1)).tree := by
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := onBlock_fields (accept_onBlock hr hy hX)
  change (ft.store y (i + 1)).blocks X.root = some X
  rw [hb, Function.update_self]

private theorem F_mono (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {k m : Nat} (hkm : k ≤ m) : (ft.store y m).Anc (ft.store y k).F (ft.store y m).F := by
  induction m, hkm using Nat.le_induction with
  | base => exact .refl
  | succ m _ ih =>
    rcases store_step hr hy m with he | ⟨X, -, hX⟩ | ⟨a, -, he⟩
    · rw [he]; exact ih
    · exact (ih.mono (tree_mono hr hy m.le_succ)).trans
        ((Store.finalized_monotone P ACP acp₀ _ (store_reachable hr hy m)).1 X _ hX)
    · obtain ⟨atts, he'⟩ := (ft.store y m).onAttestation_eq a
      rw [he, he']; exact ih

private theorem h_mono (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {i : Nat} {A W : NodeBlock P ACP} (h : (ft.store y i).Anc A W) :
    ((ft.store y i).σ A.root).h ≤ ((ft.store y i).σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    rcases (step_fields (step_σ hr hy hYW.2.1 hYW.2.2)).1 with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

private theorem J_entry (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {i : Nat} {W : NodeBlock P ACP} (hW : W ∈ (ft.store y i).tree) :
    ∃ E ∈ (ft.store y i).tree, E.root = ((ft.store y i).σ W.root).J ∧
      (ft.store y i).Anc E W ∧ (E = P.genesisBlock acp₀ ∨
        (((ft.store y i).σ E.root).h = ((ft.store y i).σ W.root).hj ∧
          ((ft.store y i).σ E.root).Th = E.root)) := by
  have hreach := store_reachable hr hy i
  have hg := (accepted_tree P ACP acp₀ _ hreach).2.2.1
  have hA := (accepted_tree P ACP acp₀ _ hreach).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
    exact ⟨_, hg, rfl, .refl, Or.inl rfl⟩
  | tail _ hYW ih =>
    rcases (step_fields (step_σ hr hy hYW.2.1 hYW.2.2)).2 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, hEY, h2⟩ := ih
      refine ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, ?_⟩
      rw [hj]; exact h2
    · obtain ⟨E, hE, h1, hEY, h2, h3⟩ :=
        (entry_state_of_source P ACP acp₀ _ hreach _ hYW.1).1
      exact ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW,
        Or.inr ⟨h2.trans hj.symm, h3.trans h1.symm⟩⟩

private theorem entry_between (hr : FGLocalRun acp₀ H₀ U ft) {y : Fin P.n} (hy : y ∈ H₀)
    {i : Nat} {A X : NodeBlock P ACP} (hAX : (ft.store y i).Anc A X) {k : Nat}
    (h1 : ((ft.store y i).σ A.root).h < k) (h2 : k ≤ ((ft.store y i).σ X.root).h) :
    ∃ W, (ft.store y i).Anc A W ∧ A ≠ W ∧ (ft.store y i).Anc W X ∧
      ((ft.store y i).σ W.root).h = k ∧ ((ft.store y i).σ W.root).Th = W.root := by
  induction hAX with
  | refl => omega
  | @tail Y X hAY hYX ih =>
    rcases (step_fields (step_σ hr hy hYX.2.1 hYX.2.2)).1 with ⟨hh, -⟩ | ⟨hh, hTh⟩
    · obtain ⟨W, h3, h4, h5, h6⟩ := ih (by omega)
      exact ⟨W, h3, h4, h5.tail hYX, h6⟩
    · by_cases hle : k ≤ ((ft.store y i).σ Y.root).h
      · obtain ⟨W, h3, h4, h5, h6⟩ := ih hle
        exact ⟨W, h3, h4, h5.tail hYX, h6⟩
      · have := h_mono hr hy hAY
        refine ⟨X, hAY.tail hYX, fun he => ?_, .refl, by omega, hTh⟩
        subst he; omega

/-- Store-local scope algebra with an externally supplied quorum-free entry row. -/
private theorem scope_block (hr : FGLocalRun acp₀ H₀ U ft) {B : NodeBlock P ACP}
    {Ts : Time} {y : Fin P.n} (hy : y ∈ H₀) {j₀ : Nat} (hj₀ : Ts ≤ ft.time j₀)
    (hmin : ∀ k < j₀, ft.time k < Ts) (hK : Compatible U (ft.store y j₀).F B) {i : Nat}
    {X : NodeBlock P ACP} (hji : j₀ ≤ i) (hX : ft.AcceptAt y i X)
    (core : ∀ E ∈ Store.excludedEntries H₀ U ft Ts B, ∀ h,
      ∀ A ∈ (ft.store y (i + 1)).tree, (ft.store y (i + 1)).Anc A X →
      ((ft.store y (i + 1)).σ A.root).h = h → ((ft.store y (i + 1)).σ A.root).Th = E.root →
      ((ft.store y (i + 1)).σ X.root).h = h ∧ ((ft.store y (i + 1)).σ X.root).Th = E.root ∧
        ((ft.store y (i + 1)).σ X.root).prog.card < P.fg.q) :
    (∀ A' ∈ (ft.store y (i + 1)).tree, (ft.store y (i + 1)).Anc A' X → ∀ Jb,
      (ft.store y (i + 1)).blocks ((ft.store y (i + 1)).σ A'.root).J = some Jb →
        Compatible U Jb B) ∧
    (¬ Compatible U X B → ∀ Pc, Anc U Pc X → Anc U Pc B →
      (∀ Q, Anc U Q X → Anc U Q B → Anc U Q Pc) →
      ((ft.store y (i + 1)).σ X.root).h ≤ ((ft.store y (i + 1)).σ Pc.root).h + 1) := by
  have hsub := hr.tree_subset y hy (i + 1)
  have hcoh : Coherent (ft.store y (i + 1)).tree := hr.coherent.mono hsub
  have excluded {E} (hEX : (ft.store y (i + 1)).Anc E X) (hc : ¬ Compatible U E B) :
      E ∈ Store.excludedEntries H₀ U ft Ts B ∧
      (ft.store y (i + 1)).Anc (ft.store y j₀).F E ∧ E ≠ (ft.store y j₀).F := by
    have hacc := accept_onBlock hr hy hX
    obtain ⟨-, -, -, -, -, hFX, -, -⟩ := onBlock_eq_some hacc
    rw [← (tree_grows P ACP acp₀ _ (store_reachable hr hy i)).1 X _ hacc] at hFX
    have hF₀X : (ft.store y (i + 1)).Anc (ft.store y j₀).F X :=
      ((F_mono hr hy hji).mono (tree_mono hr hy i.le_succ)).trans hFX
    have hne : E ≠ (ft.store y j₀).F := fun he => hc (he ▸ hK)
    rcases Anc.total hcoh hF₀X hEX with h | h
    · exact ⟨Store.mem_excludedEntries.mpr ⟨hc, y, hy, j₀, hj₀, hmin, h.mono hsub, hne⟩, h, hne⟩
    · exact absurd (compatible_of_anc hr.coherent (h.mono hsub) hK) hc
  refine ⟨fun A' hA' hA'X Jb hJb => ?_, fun hXB Pc hPX hPB hdeep => ?_⟩
  · by_contra hc
    obtain ⟨E, hE, hEr, hEA', hcase⟩ := J_entry hr hy hA'
    have hJE : Jb = E := by
      rw [← hEr] at hJb
      exact Option.some.inj (hJb.symm.trans hE)
    rw [hJE] at hc
    obtain ⟨hex, hF₀E, hne⟩ := excluded (hEA'.trans hA'X) hc
    rcases hcase with rfl | ⟨hh, hTh⟩
    · have hF₀ : (ft.store y j₀).F ∈ (ft.store y (i + 1)).tree := tree_mono hr hy (by omega)
        (cache_invariants P ACP acp₀ _ (store_reachable hr hy j₀)).1
      exact hne (Anc.antisymm hcoh hF₀E
        ((accepted_tree P ACP acp₀ _ (store_reachable hr hy (i + 1))).2.2.2 _ hF₀)).symm
    · have := (core E hex _ E hE (hEA'.trans hA'X) hh hTh).1
      have := h_mono hr hy hA'X
      have := (one_le_h hr hy hA').2
      omega
  · have hPXs := anc_of_U hr hy hPX (accept_mem hr hy hX)
    by_contra hlt
    obtain ⟨W, hPW, hne, hWX, hWh, hWTh⟩ := entry_between hr hy hPXs
      (k := ((ft.store y (i + 1)).σ Pc.root).h + 1) (by omega) (by omega)
    have hc : ¬ Compatible U W B := by
      rintro (hWB | hBW)
      · exact hne (Anc.antisymm hr.coherent (hPW.mono hsub) (hdeep W (hWX.mono hsub) hWB))
      · exact hXB (Or.inr (hBW.trans (hWX.mono hsub)))
    have := (core W (excluded hWX hc).1 _ W (Anc.mem hPW hne).2 hWX hWh hWTh).1
    omega

end StoreFacts

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Time → Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {proposer : Nat → Fin sp.n} {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
  {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}

/-- The persistence cut invariant follows from the invariant at all earlier cuts. -/
theorem cut_inv_step (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    CutInv tr H s m B k := by
  classical
  rw [cutInv_iff]
  rintro y hy ⟨c, hc⟩ hk₀ hk₁
  have hlocal := hrun.toLocalRun.upTo (hrun.time_nonneg k)
  have hfg := fg_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer
    (Compose.requirements sp ro) hrun.genesis_root_ok hrun.toLocalRun hp.noColl
  let ft : FGTrace sp.toParams (Payload sp.n) := tr.projFG.upTo (tr.time k)
  have hr := hfg.upTo (hrun.time_nonneg k)
  have hs (z : Fin sp.n) (i : Nat) (hi : i ≤ k + 1) :
      ft.store z i = tr.projFG.store z i := by
    exact congrArg Prod.fst (Trace.upTo_state tr.projFG z (i := i)
      (fun l hl => hrun.time_mono (show l ≤ k by omega)))
  have hpstate (z : Fin sp.n) (hz : z ∈ H (tr.time k)) (i : Nat) (hi : i ≤ k + 1) :
      tr.projFG.store z i = (tr.state z i).fg := by
    have h := Compose.projFG_state hlocal hz i
    rw [RunTrace.upTo_projFG,
      Trace.upTo_state tr.projFG z (fun l hl => hrun.time_mono (show l ≤ k by omega)),
      Trace.upTo_state tr z (fun l hl => hrun.time_mono (show l ≤ k by omega))] at h
    exact congrArg Prod.fst h
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hT₀ : sp.toParams.IsPublic (sp.ts (s + 1 : Nat) + sp.Δ) :=
    ⟨4 * (s + 1 : Nat) + 1, by simp only [SA.SAParams.ts]; ring⟩
  have hc' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  obtain ⟨j₀, e, hg, hj₀k, hkj₀⟩ := hlocal.grouped y hy k c hc'
  have hg' := (RunTrace.upTo_groupAt hrun.time_mono).mp hg |>.2
  obtain ⟨T, hTpub, hTa, haT, hTeq, haeq⟩ := exists_cut_time (e := e) (tr.time k)
  have hTle : T ≤ sp.ts m + sp.Δ := public_le hTpub (lt_of_le_of_lt hTa hk₁)
  have hrows : ∀ v j a, v ∈ H (tr.time j) → tr.projFG.SignAt v j a →
      sp.ts (s + 1 : Nat) + sp.Δ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ excludedEntries tr H s B, a.T ≠ E.root := by
    rintro v j a hv ⟨src, hsc⟩ h₁ h₂ E hE
    have hsc' := Compose.projFG_callAt.mp hsc
    have hjk : j < k := by
      by_contra hjk
      have hkj := hrun.time_mono (not_lt.mp hjk)
      have hTa' : T = tr.time k := le_antisymm hTa (hkj.trans h₂)
      exact hjk (sign_before_delivery hrun hv hy hsc' hg' (hTeq hTa') hj₀k
        (le_antisymm (h₂.trans hTa) hkj))
    exact attest_not_excluded hrun hp hv ⟨src, hsc'⟩ h₁ (h₂.trans hTle)
      (fun i hi => ih i (hi.trans hjk)) E hE
  have hown : ∀ j ≤ k, ∀ X, tr.AcceptAt y j X → tr.time j = T + sp.Δ →
      X.proposer = y ∧ sp.toParams.slotTime X.slot = T + sp.Δ := by
    intro j hj X hX htj
    have hak : tr.time k = T + sp.Δ := le_antisymm haT (htj ▸ hrun.time_mono hj)
    have he1 := haeq hak
    have hX' := (Trace.upTo_callAt tr).mpr ⟨hrun.time_mono hj, hX⟩
    obtain ⟨j₂, e₂, hg₂, hj₂, hj₂'⟩ := hlocal.grouped y hy j _ hX'
    change (tr.upTo (tr.time k)).GroupAt proposer dg y j₂ (tr.time j) e₂ at hg₂
    simp only [Trace.upTo_time] at hj₂'
    rw [htj, ← hak] at hg₂
    rw [← hak]
    rcases lt_trichotomy j₂ j₀ with hlt | rfl | hgt
    · exact Compose.accept_in_tick hlocal hy hg₂
        ((hlocal.phase_order y hy y hy j₂ j₀ _ e₂ e hg₂ hg hlt).trans he1) hj₂
        (by rw [htj, ← hak] at hj₂'; exact hj₂') hX'
    · exact Compose.accept_in_tick hlocal hy hg₂ ((group_phase hg₂ hg).le.trans he1) hj₂
        (by rw [htj, ← hak] at hj₂'; exact hj₂') hX'
    · have := group_start hg hg₂ hgt.le (by omega)
      omega
  have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, hk₀⟩
  let b := Nat.find hex
  have hbk : b ≤ k := Nat.find_min' hex hk₀
  have hb : sp.ts s ≤ tr.time b := Nat.find_spec hex
  have hmin : ∀ j < b, tr.time j < sp.ts s := fun j hj => not_le.mp (Nat.find_min hex hj)
  have hK := hp.clean.caches y b (hrun.antitone hk₀ hy) ⟨hb, hmin⟩
  have hchain : ∀ i, b ≤ i → i ≤ k → ∀ X, tr.AcceptAt y i X →
      (∀ A' ∈ (ft.store y (i + 1)).tree,
        (ft.store y (i + 1)).Anc A' X → ∀ Jb,
        (ft.store y (i + 1)).blocks
          ((ft.store y (i + 1)).σ A'.root).J = some Jb →
        Compatible (tr.HonestBlocksAt H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocksAt H) X B → ∀ Pc,
        Anc (tr.HonestBlocksAt H) Pc X → Anc (tr.HonestBlocksAt H) Pc B →
        (∀ Q, Anc (tr.HonestBlocksAt H) Q X → Anc (tr.HonestBlocksAt H) Q B →
          Anc (tr.HonestBlocksAt H) Q Pc) →
        ((ft.store y (i + 1)).σ X.root).h ≤
          ((ft.store y (i + 1)).σ Pc.root).h + 1) := by
    intro i hbi hik X hX
    have hXi := (Trace.upTo_callAt tr.projFG).mpr
      ⟨hrun.time_mono hik, Compose.projFG_callAt.mpr hX⟩
    have hKb : Compatible (tr.HonestBlocksAt H) (ft.store y b).F B := by
      rw [hs y b (by omega), hpstate y hy b (by omega)]
      exact hK.1
    apply scope_block hr hy hb hmin hKb hbi hXi
    intro E hE h A hA hAX hh hTh
    obtain ⟨hnc, z, hz, j, hjs, hjmin, ha, hne⟩ := Store.mem_excludedEntries.mp hE
    have hjk : j ≤ k := by by_contra h; exact (not_lt_of_ge hk₀) (hjmin k (by omega))
    rw [hs z j (by omega), hpstate z hz j (by omega)] at ha hne
    have hE' : E ∈ excludedEntries tr H s B :=
      ⟨hnc, z, j, hrun.antitone hk₀ hz, ⟨hjs, hjmin⟩, ha, hne⟩
    have ht : tr.time i < T + sp.Δ ∨
        (tr.time i = T + sp.Δ ∧ X.proposer = y ∧
          sp.toParams.slotTime X.slot = T + sp.Δ) := by
      rcases ((hrun.time_mono hik).trans haT).lt_or_eq with hi | hi
      · exact Or.inl hi
      · exact Or.inr ⟨hi, hown i hik X hX hi⟩
    have core := Store.Growing.quorum_free_entries sp.toParams (Payload sp.n) _ H
      (tr.HonestBlocksAt H) tr.projFG (excludedEntries tr H s B)
      (sp.ts (s + 1 : Nat) + sp.Δ) T (sp.ts m + 2 * sp.Δ) y hfg hT₀ hTpub
      (by linarith) hp.clean.fgAttCut hrows i X
      (hrun.antitone (hrun.time_mono hik) hy) (Compose.projFG_callAt.mpr hX) ht E hE' h A
    rw [hs y (i + 1) (by omega)] at hA hAX hh hTh ⊢
    exact core hA hAX hh hTh
  have hcache : ∀ j, b ≤ j → j ≤ k + 1 →
      Compatible (tr.HonestBlocksAt H) (ft.store y j).F B ∧
      Compatible (tr.HonestBlocksAt H) (ft.store y j).J B := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [hs y b (by omega), hpstate y hy b (by omega)]
      exact hK
    | succ j hbj ih =>
      intro hjk
      have ih := ih (by omega)
      rcases Store.store_step hr hy j with he | ⟨X, hX, hXo⟩ | ⟨a, -, he⟩
      · rw [he]; exact ih
      · obtain ⟨hJ, hF⟩ := onBlock_FJ hXo
        have hJc : Compatible (tr.HonestBlocksAt H)
            (ft.store y (j + 1)).J B := by
          rcases hJ with hJ | hJ
          · rw [hJ]; exact ih.2
          · exact (hchain j hbj (by omega) X
              (Compose.projFG_callAt.mp ((Trace.upTo_callAt _).mp hX).2)).1 X
              (accept_mem hr hy hX) .refl _ hJ
        refine ⟨?_, hJc⟩
        rcases hF with hF | hF
        · rw [hF]; exact ih.1
        · exact compatible_of_anc hr.coherent (hF.mono (hr.tree_subset y hy _)) hJc
      · obtain ⟨atts, he'⟩ := (ft.store y j).onAttestation_eq a
        rw [he, he']; exact ih
  have hS : ft.store y (k + 1) = (tr.post k).fg := by
    rw [hs y (k + 1) le_rfl, hpstate y hy (k + 1) le_rfl, Trace.state_succ_of_call _ hc]
  refine ⟨?_, fun X hX => ?_⟩
  · simpa only [hS] using hcache (k + 1) (by omega) le_rfl
  · simpa only [hS] using hchain k hbk le_rfl X hX

end Consensus.Goldilocks.Compose.Growing

end
