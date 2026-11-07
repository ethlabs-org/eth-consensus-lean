module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Votes relayed while their writer is honest

The release carries its own honesty witness. A subsequent compromise does not cancel service.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The forwarding side, with sender honesty read at release, not at the recipient's cut. -/
def Relayed (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat) (D : Blk sp.n FGP) : Set (Fin sp.n) :=
  {u | ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
    (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, X ∈ H (tr.time k) ∧ tr.SendOrAdmit X k v ∧
      sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ}

theorem relayed_iff {X : Fin sp.n} {s : Nat} {D : Blk sp.n FGP} {u : Fin sp.n} :
    u ∈ Relayed tr H U X s D ↔
      ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
        (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
        ∃ k, X ∈ H (tr.time k) ∧ tr.SendOrAdmit X k v ∧
          sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ := Iff.rfl

/-- Three quarters of the committee have votes released by the optimistic writer while honest. -/
theorem optimistic_seats (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} {k s : Nat} (hX : X ∈ H (tr.time k))
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Relayed tr H U X s D := by
  have hm := hrun.localRun.time_mono
  obtain ⟨ℓ, A, hp, hU, hn, hf⟩ := SA.optimistic_side
    (hrun.upTo (hrun.localRun.time_nonneg k)) hX
    ((upTo_optimisticLockAt hm).mpr ⟨le_rfl, hfl⟩)
  refine ⟨ℓ, A, (upTo_optimisticPoint hm).mp hp |>.2, hU, hn, ?_⟩
  intro u hu
  obtain ⟨v, hv, hs, hR, j, hj, h1, h2⟩ := (SA.fwd_iff).mp (hf hu)
  obtain ⟨hjk, hj⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hj
  exact ⟨v, hv, hs, hR, j, hrun.localRun.antitone hjk hX, hj, h1, h2⟩

private theorem lastWake_eq_coe {y : Fin sp.n} {w : Time} :
    ∀ {c : Nat}, tr.lastWake y c = (w : WithBot Time) →
      ∃ k ≤ c, tr.RestartAt y k ∧ tr.time k = w
  | 0, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold ACTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_eq_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

private theorem deadline_eq {y : Fin sp.n} {c : Nat} {τ : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ τ) : tr.deadline y c τ = τ + sp.Δ := by
  unfold ACTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · rfl
  · obtain ⟨k, hk, hrk, rfl⟩ := lastWake_eq_coe hw
    simp [Option.elim, max_eq_left (h k hk hrk)]

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
      (by rw [ht]; simp only [SAParams.ts]; push_cast; nlinarith)
      (by rw [ht]; simp only [SAParams.ts]; push_cast; nlinarith)
  intro k hk hrk
  have h := (SA.joined_awake sp FGP ro _ U tr hr Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at h

/-- A result's counted seats have genuine releases by its writer, even after compromise. -/
theorem result_side (hrun : ACRun proposer tr H U)
    {Y : Fin sp.n} {c s : Nat} (hY : Y ∈ H (tr.time c))
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Relayed tr H U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hm := hrun.localRun.time_mono
  have hr := hrun.upTo (hrun.localRun.time_nonneg c)
  have hs : (tr.upTo (tr.time c)).state Y c = tr.state Y c :=
    Trace.upTo_state tr Y fun _ hk => hm hk.le
  have hmaj := result_majority hR
  obtain ⟨ℓ, hu, _, rfl⟩ := hR
  have hu' := (upTo_updateAt hm).mpr ⟨le_rfl, hu⟩
  obtain ⟨_, hΦU⟩ := frameIn_of_call hr.localRun hY hu'.1
  have hrs := update_restarts hr.localRun hY hu'
  refine ⟨ℓ, _, hu.1, hu.2.2.1, ?_, hmaj, ?_, ?_⟩
  · intro k hk hkr
    exact hrs k hk ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hk, hkr⟩)
  · rintro u ⟨v, ⟨hvp, _, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvp' : v ∈ ((tr.upTo (tr.time c)).state Y c).pool s := hs.symm ▸ hvp
    have hvs := state_pool_slot sp hr.localRun hY c s v hvp'
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
    obtain ⟨k, hsend, h1, h2⟩ := admitted_of_held hr.localRun hY hvs hvp' le_rfl
      (fun k _ hst => by
        rw [hs] at hst
        have hst' : (tr.state Y c).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) := by
          unfold resolutionTime at hres
          split at hres
          · exact absurd hres (by simp [ETime.of])
          · split_ifs at hres
            · exact absurd hres (by simp [ETime.of])
            · exact lt_of_le_of_lt (le_max_left _ _) hres
        rw [hst] at hst'
        exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst'))
    obtain ⟨hkc, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
    exact ⟨k, hrun.localRun.antitone hkc hY, hsend, h1, h2⟩
  · rintro u ⟨v, ⟨hvp, hne, _, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- Forwarding uses the source's honesty at release and the recipient's at its reading cut. -/
theorem sync_window_before_forward
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b : Time} (hsvc : ServiceWindowBefore H U a b tr)
    {y X : Fin sp.n} {k : Nat} {v : Vote sp.n} (hy : y ∈ H (tr.time k))
    (hsend : tr.SendOrAdmit y k v) (ha : a ≤ tr.time k) (hb : tr.time k + sp.Δ ≤ b)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hX : X ∈ H (tr.time i))
    (hc : tr.CallAt X i ℓ)
    (hrs : ∀ k' ≤ i, tr.RestartAt X k' → tr.time k' ≤ tr.time k)
    (hdl : tr.time k + sp.Δ ≤ tr.time i)
    (hslot : ∀ t, tr.time k ≤ t → t < tr.time k + sp.Δ →
      (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t) :
    v ∈ (tr.state X i).pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i).pool v.slot} := by
  have hm := hr.time_mono
  have hd : tr.deadline X i (tr.time k) = tr.time k + sp.Δ := deadline_eq hrs
  have hp := hsvc.message y k v hy hsend ha X i ℓ hX hc
    (by rw [hd]; exact hb) (by rw [hd]; exact hdl)
  have hp' := (upTo_messageServedBefore hm (d := tr.time i) le_rfl).mpr hp
  have hs : (tr.upTo (tr.time i)).state X i = tr.state X i :=
    Trace.upTo_state tr X fun _ hk => hm hk.le
  have h := held_of_deadline_service (hr.upTo (hr.time_nonneg i)) hX
    (fun j hj hjr => hrs j hj ((ACTrace.upTo_restartAt
      (A := goldilocksSA sp FGP ro)).mp hjr).2) hdl hslot hp'
  simpa only [hs] using h

theorem relayed_held_before
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {s : Nat} {b : Time} (hsvc : ServiceBefore H U b tr)
    {X Y : Fin sp.n} {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hY : Y ∈ H (tr.time c)) (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : sp.ts s + 3 * sp.Δ ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : Blk sp.n FGP} {u : Fin sp.n} (hu : u ∈ Relayed tr H U X s D) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hX, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have h := sync_window_before_forward hr hsvc hX hsend (hr.time_nonneg k)
    (by linarith) hY hc (fun j hj hjr => (hrs j hj hjr).trans h1)
    (by rw [ht]; linarith) fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]
      omega
  rwa [hvs] at h

/-- Relayed votes for an incompatible block occupy seats disjoint from the result's supporters.
Only release deadlines through `t_s + 3Δ` are consumed. -/
theorem relayed_against
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {s : Nat} {b : Time} (hsvc : ServiceBefore H U b tr)
    {X Y : Fin sp.n} {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hY : Y ∈ H (tr.time c)) (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : sp.ts s + 3 * sp.Δ ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : Blk sp.n FGP} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr H U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have held := fun {u} (hu : u ∈ Relayed tr H U X s D) =>
    relayed_held_before hr hsvc hY hc ht hb hrs hu
  have hU := hr.coherent
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, _, hv | ⟨a, ha, _, _, _, hav, _⟩⟩ := held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨_, v, hv, rfl, _⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

end Consensus.Goldilocks.SA.Growing

end
