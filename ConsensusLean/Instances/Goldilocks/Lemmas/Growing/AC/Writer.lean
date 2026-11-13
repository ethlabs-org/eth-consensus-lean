module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Writer-pool transport between separately honest nodes -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

private theorem cast_time_le {K : Set (Fin sp.n)}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) K U tr) {y : Fin sp.n}
    (hy : y ∈ K) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) : tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ := by
  have hv : ∀ (A : SAState sp.n) (t : Time), (tryVote sp y A ℓ.frame t).2 ≠ [] →
      t ≤ sp.ts (sp.slot t) + sp.Δ := by
    intro A t h
    by_contra ht
    have hguard : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨
        sp.ts (sp.slot t) + sp.Δ < t := Or.inr (Or.inr (lt_of_not_ge ht))
    simp only [tryVote, hguard, ite_true] at h
    exact h rfl
  have hΦ := (frameIn_of_call hr hy hc.1).1
  obtain ⟨hc, he⟩ := hc
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have hne : ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 ≠ [] := by rw [hx]; exact List.ne_nil_of_mem he
  generalize tr.state y i = A at hne
  generalize ℓ.call = c at hne
  cases c with
  | tick =>
    change (acOnTick sp y A ℓ.frame (tr.time i)).2 ≠ [] at hne
    unfold acOnTick at hne
    dsimp only at hne
    split at hne
    · exact absurd rfl hne
    · change (if tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ then
        tryVote sp y A ℓ.frame (tr.time i) else (A, [])).2 ≠ [] at hne
      split at hne
      · exact hv _ _ hne
      · exact absurd rfl hne
  | proposal => exact absurd rfl hne
  | toFG => exact absurd rfl hne
  | message m => exact hv _ _ hne
  | block B => exact hv _ _ hne
  | restart =>
    change (acRestart sp ro y A ℓ.frame (tr.time i)).2 ≠ [] at hne
    exact absurd ((restart_state sp) FGP ro y A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1 hne

private theorem update_restarts {K : Set (Fin sp.n)} {c : Nat}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) K U tr)
    {Y : Fin sp.n} (hY : Y ∈ K) {s : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr Y c s ℓ) :
    ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ := sp.toParams.hΔ
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
  rw [hc.1, hcall] at he
  have hpost : joined sp (tr.post c) (tr.time c) := by
    unfold joined at hj ⊢
    rw [show tr.post c = (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1 from
      (congrArg Prod.fst he).symm, onTick_restartTime]
    exact hj
  have hsl : sp.slot (tr.time c) = s + 1 :=
    CompatibleSides.slot_of_lt (s := s + 1)
      (by rw [ht]; simp only [SAParams.ts]; push_cast; linarith)
      (by rw [ht]; simp only [SAParams.ts]; push_cast; linarith)
  intro k hk hrk
  have h := (SA.joined_awake sp FGP ro _ U tr hr Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at h

theorem writer_pool (hrun : ACRun proposer tr H U) {X : Fin sp.n} {i₀ s : Nat}
    (hX : X ∈ H (tr.time i₀)) {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr)
    {k : Nat} (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hr := hrun.localRun
  have hm := hr.time_mono
  have hry := hrun.upTo (hr.time_nonneg i)
  have hrX := hrun.upTo (hr.time_nonneg i₀)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hup' := (upTo_updateAt hm).mpr ⟨le_rfl, hupd⟩
  have hΔ := sp.toParams.hΔ
  have hts : ∀ m : Nat, sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := fun m => by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨_, hys, hyj, _⟩ := castAt_spec hry.localRun hy hc'
  have hsi : sp.slot (tr.time i) = s + 1 := hys.symm.trans hs
  have hrsy : ∀ j ≤ i, tr.RestartAt y j → tr.time j ≤ sp.ts s := by
    have hj' : joined sp ((tr.upTo (tr.time i)).post i) (tr.time i) := by
      unfold joined
      rw [restartTime_of_castAt hry.localRun hy hc']
      exact hyj
    intro j hj hjr
    have h := (SA.joined_awake sp FGP ro _ U _ hry.localRun y hy i ℓ hc'.1 hj').2 j hj
      ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hj, hjr⟩)
    rwa [Trace.upTo_time, hsi, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at h
  have hrsX : ∀ j ≤ i₀, tr.RestartAt X j → tr.time j ≤ sp.ts s := by
    intro j hj hjr
    exact update_restarts hrX.localRun hX hup' j hj
      ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hj, hjr⟩)
  intro v hv
  have hstate : (tr.upTo (tr.time i)).state y (k + 1) = tr.state y (k + 1) :=
    Trace.upTo_state tr y fun j hj => hm ((Nat.le_of_lt_succ hj).trans hk)
  have hv' := hstate.symm ▸ hv
  have hvs := state_pool_slot sp hry.localRun hy (k + 1) s v hv'
  rcases pool_origin hry.localRun hy (k + 1) v (hvs ▸ hv') with
    ⟨j, hj, hsend, _, hsl⟩ | ⟨j, hj, ℓj, hcj, hrj, _, B, hB, hvB⟩
  · obtain ⟨hjt, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
    have hsk : sp.ts s ≤ tr.time j :=
      (ts_le_iff_le_slot sp (hr.time_nonneg j) s).mpr (by rw [← hvs]; exact_mod_cast hsl)
    have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
      have h := cast_time_le hry.localRun hy hc'
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
      rw [hsi, hts] at h
      linarith
    have hrs : ∀ j' ≤ i₀, tr.RestartAt X j' → tr.time j' ≤ tr.time j :=
      fun j' hj' hrj' => (hrsX j' hj' hrj').trans hsk
    have hdl : tr.time j + sp.Δ ≤ tr.time i₀ := by rw [hupd.2.2.1]; linarith
    have hslot : ∀ t, tr.time j ≤ t → t < tr.time j + sp.Δ →
        (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t := by
      intro t h₁ h₂
      have ht : 0 ≤ t := (hr.time_nonneg j).trans h₁
      have ha := (ts_le_iff_le_slot sp ht s).mp (hsk.trans h₁)
      have hb : ¬ ((s + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
        have h' := (ts_le_iff_le_slot sp ht _).mpr h
        rw [hts₂] at h'
        linarith
      omega
    have h := sync_forward hr hsync (hr.antitone hjt hy) hsend hsk hjt hX hupd.1 hrs hdl hslot
    rwa [hvs] at h
  · obtain ⟨hjt, hcj⟩ := (Trace.upTo_callAt tr).mp hcj
    have hcj' := (Trace.upTo_callAt tr).mpr ⟨hjt, hcj⟩
    have hBv := (frame_validPayload sp hry.localRun hy hcj' B hB).1 v hvB
    have hBs := frame_slot_le sp hry.localRun hy hcj' B hB
    have htk := hrsy j ((Nat.le_of_lt_succ hj).trans hk) ⟨ℓj, hcj, hrj⟩
    have hnot : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time j) := fun h => by
      have h' := (ts_le_iff_le_slot sp (hr.time_nonneg j) _).mpr h
      rw [hts] at h'
      linarith
    change B.slot ≤ sp.slot (tr.time j) at hBs
    omega

private theorem mem_admitVote_pool {A : SAState sp.n} {t : Time} {v x : Vote sp.n} {σ : Nat}
    (h : x ∈ A.pool σ) : x ∈ (admitVote sp A t v).pool σ := by
  unfold admitVote
  split_ifs
  · exact h
  · exact h
  · simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.mem_append_left _ h
    · exact h

private theorem tryVote_pool (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (σ : Nat) : A.pool σ ⊆ (tryVote sp x A Φ t).1.pool σ := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  all_goals try exact List.Subset.refl _
  all_goals
    intro w hw
    rw [optimistic_pool]
    exact mem_admitVote_pool hw

private theorem foldl_admit_pool {t : Time} {σ : Nat} :
    ∀ (l : List (Vote sp.n)) (A : SAState sp.n),
      A.pool σ ⊆ (l.foldl (fun A v => admitVote sp A t v) A).pool σ
  | [], _ => List.Subset.refl _
  | _ :: l, _ => fun _ hw => foldl_admit_pool l _ (mem_admitVote_pool hw)

private theorem blockReceipt_held (A : SAState sp.n) {t : Time} {B : Blk sp.n FGP}
    {v : Vote sp.n} (hv : v ∈ blockVotes B) (h₁ : (sp.slot t : Int) - 1 ≤ v.slot)
    (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (blockReceipt sp A t B).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (blockReceipt sp A t B).pool v.slot} := by
  unfold blockReceipt
  generalize ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  generalize blockVotes B = l at hv
  induction l generalizing A' with
  | nil => simp at hv
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · have hs := foldl_admit_pool (t := t) (σ := v.slot) l (admitVote sp A' t v)
      rcases admitVote_held A' _ _ h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · exact Or.inl (hs h)
      · exact Or.inr ⟨a, hs ha, b, hs hb, hab, hav, hbv⟩
    · exact ih _ hv

theorem writer_merged (hrun : ACRun proposer tr H U) {X : Fin sp.n} {i₀ s : Nat}
    (hX : X ∈ H (tr.time i₀)) {ℓX : ACLabel (goldilocksSA sp FGP ro)}
    (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  have hr := hrun.localRun
  have hm := hr.time_mono
  have hry := hrun.upTo (hr.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  rintro v (hv | ⟨B, hB, hBs, hvB⟩) hvs
  · have hv := (List.mem_filter.mp hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    have hp := (readPoint_pool hry.localRun hy hc' (by simpa using hv)).1
    have hstate : (tr.upTo (tr.time i)).state y (i + 1) = tr.state y (i + 1) :=
      Trace.upTo_state tr y fun j hj => hm (Nat.le_of_lt_succ hj)
    rw [hstate] at hp
    exact writer_pool hrun hX hupd hy hc hs hsync le_rfl v hp
  · obtain ⟨_, hys, _, _⟩ := castAt_spec hry.localRun hy hc'
    rcases frame_genesis_or_accepted sp hry.localRun hy hc'.1 B hB with h0 |
      ⟨k, hki, ℓk, hck, hcall⟩
    · omega
    obtain ⟨hkt, hck⟩ := (Trace.upTo_callAt tr).mp hck
    have hyk := hr.antitone hkt hy
    have hBk : B.slot ≤ sp.slot (tr.time k) := by
      rcases hr.frameLaw y k ℓk hyk hck with ⟨_, Φ₀, _, _, hok⟩ | ⟨j, ℓ', _, _, _, hok⟩ <;>
      · rw [hcall] at hok
        obtain ⟨_, _, _, h⟩ := hok
        exact h
    have hki' := slot_mono sp (hr.time_nonneg k) (hm hki)
    have he := hr.exec k ℓk hck.2 (hck.1 ▸ hyk)
    rw [hck.1, hcall] at he
    have hpost : tr.post k = (tryVote sp y (optimisticConfirmation sp
        (blockReceipt sp (tr.state y k) (tr.time k) B) ℓk.frame (tr.time k)) ℓk.frame
        (tr.time k)).1 := (congrArg Prod.fst he).symm
    have hsub : ∀ w ∈ (blockReceipt sp (tr.state y k) (tr.time k) B).pool s,
        w ∈ (tr.state y (k + 1)).pool s := fun w hw => by
      rw [state_succ_of_call hck, hpost]
      exact tryVote_pool _ _ _ _ _ (by rw [optimistic_pool]; exact hw)
    have hw := writer_pool hrun hX hupd hy hc hs hsync hki
    change e.msg.slot = sp.slot (tr.time i) at hys
    rcases blockReceipt_held (tr.state y k) hvB (t := tr.time k) (by omega) (by omega) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rw [hvs] at h
      exact hw v (hsub v h)
    · rw [hvs] at ha hb
      rcases hw a (hsub a ha) with ha' | ha'
      · rcases hw b (hsub b hb) with hb' | hb'
        · exact Or.inr ⟨a, ha', b, hb', hab, hav, hbv⟩
        · exact Or.inr (hbv ▸ hb')
      · exact Or.inr (hav ▸ ha')

end Consensus.Goldilocks.SA.Growing

end
