module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # SA events in a retained prefix

Events are unchanged at cuts through the retention horizon. State-reading events additionally
use the trace's time order. These translations keep the ambient block universe unchanged.
-/

namespace Consensus.Goldilocks

namespace ACTrace

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} {tr : ACTrace A} {d : Time}

theorem upTo_restartAt {y : Fin P.n} {i : Nat} :
    RestartAt (A := A) (tr.upTo d) y i ↔ tr.time i ≤ d ∧ tr.RestartAt y i := by
  simp only [RestartAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, ⟨hi, hc⟩, hr⟩
    exact ⟨hi, ℓ, hc, hr⟩
  · rintro ⟨hi, ℓ, hc, hr⟩
    exact ⟨ℓ, ⟨hi, hc⟩, hr⟩

theorem upTo_acceptAt {y : Fin P.n} {i : Nat} {B : A.Blk} :
    AcceptAt (A := A) (tr.upTo d) y i B ↔ tr.time i ≤ d ∧ tr.AcceptAt y i B := by
  simp only [AcceptAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, ⟨hi, hc⟩, hr⟩
    exact ⟨hi, ℓ, hc, hr⟩
  · rintro ⟨hi, ℓ, hc, hr⟩
    exact ⟨ℓ, ⟨hi, hc⟩, hr⟩

theorem upTo_lastWake (hm : Monotone tr.time) (y : Fin P.n) :
    ∀ {i : Nat}, tr.time i ≤ d → lastWake (A := A) (tr.upTo d) y i = tr.lastWake y i
  | 0, hi => by
    rw [lastWake, lastWake, upTo_restartAt (A := A) (tr := tr) (i := 0)]
    rw [and_iff_right hi]
    rfl
  | i + 1, hi => by
    have ih := upTo_lastWake hm y ((hm (Nat.le_succ i)).trans hi)
    rw [lastWake, lastWake, upTo_restartAt (A := A) (tr := tr) (i := i + 1)]
    rw [and_iff_right hi, ih]
    rfl

theorem upTo_deadline (hm : Monotone tr.time) {y : Fin P.n} {i : Nat}
    (hi : tr.time i ≤ d) (τ : Time) :
    deadline (A := A) (tr.upTo d) y i τ = tr.deadline y i τ := by
  simp only [deadline, upTo_lastWake hm y hi]

end ACTrace

namespace SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {d : Time}

theorem upTo_voteAt {y : Fin sp.n} {i : Nat} {e : Em sp FGP} :
    VoteAt (tr.upTo d) y i e ↔ tr.time i ≤ d ∧ VoteAt tr y i e := by
  simp only [VoteAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, ⟨hi, hc⟩, he⟩
    exact ⟨hi, ℓ, hc, he⟩
  · rintro ⟨hi, ℓ, hc, he⟩
    exact ⟨ℓ, ⟨hi, hc⟩, he⟩

theorem upTo_castAt {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} :
    CastAt (tr.upTo d) y i ℓ e ↔ tr.time i ≤ d ∧ CastAt tr y i ℓ e := by
  simp only [CastAt, Trace.upTo_callAt, and_assoc]

private theorem state_eq (hm : Monotone tr.time) {y : Fin sp.n} {i : Nat}
    (hi : tr.time i ≤ d) : (tr.upTo d).state y i = tr.state y i :=
  Trace.upTo_state tr y fun _ hk => (hm hk.le).trans hi

theorem upTo_updateAt (hm : Monotone tr.time) {y : Fin sp.n} {i s : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} :
    UpdateAt (tr.upTo d) y i s ℓ ↔ tr.time i ≤ d ∧ UpdateAt tr y i s ℓ := by
  simp only [UpdateAt, Trace.upTo_callAt, Trace.upTo_time]
  constructor
  · rintro ⟨⟨hi, hc⟩, ht, hs, hj⟩
    rw [state_eq hm hi] at hj
    exact ⟨hi, hc, ht, hs, hj⟩
  · rintro ⟨hi, hc, ht, hs, hj⟩
    rw [← state_eq hm hi] at hj
    exact ⟨⟨hi, hc⟩, ht, hs, hj⟩

theorem upTo_resultAt (hm : Monotone tr.time) {y : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    ResultAt (tr.upTo d) y i s B CV ↔ tr.time i ≤ d ∧ ResultAt tr y i s B CV := by
  simp only [ResultAt, upTo_updateAt hm]
  constructor
  · rintro ⟨ℓ, ⟨hi, hu⟩, hB, hCV⟩
    rw [state_eq hm hi] at hB hCV
    exact ⟨hi, ℓ, hu, hB, hCV⟩
  · rintro ⟨hi, ℓ, hu, hB, hCV⟩
    rw [← state_eq hm hi] at hB hCV
    exact ⟨ℓ, ⟨hi, hu⟩, hB, hCV⟩

theorem upTo_fastUpdateAt (hm : Monotone tr.time) {y : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    FastUpdateAt (tr.upTo d) y i s B CV ↔ tr.time i ≤ d ∧ FastUpdateAt tr y i s B CV := by
  simp only [FastUpdateAt, upTo_updateAt hm, Trace.upTo_time]
  constructor
  · rintro ⟨ℓ, C, ⟨hi, hu⟩, hC, hB, hCV⟩
    rw [state_eq hm hi] at hC hB hCV
    exact ⟨hi, ℓ, C, hu, hC, hB, hCV⟩
  · rintro ⟨hi, ℓ, C, hu, hC, hB, hCV⟩
    rw [← state_eq hm hi] at hC hB hCV
    exact ⟨ℓ, C, ⟨hi, hu⟩, hC, hB, hCV⟩

theorem upTo_optimisticPoint (hm : Monotone tr.time) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {A : SAState sp.n} :
    OptimisticPoint (tr.upTo d) y i ℓ A ↔ tr.time i ≤ d ∧ OptimisticPoint tr y i ℓ A := by
  simp only [OptimisticPoint, Trace.upTo_callAt, Trace.upTo_time]
  by_cases hi : tr.time i ≤ d
  · simp only [hi, true_and, state_eq hm hi]
  · simp only [hi, false_and]

theorem upTo_optimisticLockAt (hm : Monotone tr.time) {y : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    OptimisticLockAt (tr.upTo d) y i s B CV ↔
      tr.time i ≤ d ∧ OptimisticLockAt tr y i s B CV := by
  simp only [OptimisticLockAt, upTo_optimisticPoint hm, Trace.upTo_time]
  constructor
  · rintro ⟨ℓ, A, ⟨hi, hp⟩, hs, hb, hv⟩
    exact ⟨hi, ℓ, A, hp, hs, hb, hv⟩
  · rintro ⟨hi, ℓ, A, hp, hs, hb, hv⟩
    exact ⟨ℓ, A, ⟨hi, hp⟩, hs, hb, hv⟩

theorem upTo_fastLockAt (hm : Monotone tr.time) {y : Fin sp.n} {i s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    FastLockAt (tr.upTo d) y i s B CV ↔ tr.time i ≤ d ∧ FastLockAt tr y i s B CV := by
  simp only [FastLockAt, upTo_fastUpdateAt hm, upTo_optimisticLockAt hm, and_or_left]

theorem upTo_toFGAt (hm : Monotone tr.time) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {B : Blk sp.n FGP} :
    ToFGAt (tr.upTo d) y i ℓ B ↔ tr.time i ≤ d ∧ ToFGAt tr y i ℓ B := by
  simp only [ToFGAt, Trace.upTo_callAt, Trace.upTo_time]
  by_cases hi : tr.time i ≤ d
  · simp only [hi, true_and, state_eq hm hi]
  · simp only [hi, false_and]

theorem upTo_joinedAt {y : Fin sp.n} {t : Time} (ht : t ≤ d) :
    JoinedAt (tr.upTo d) y t ↔ JoinedAt tr y t := by
  simp only [JoinedAt, ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro) (tr := tr),
    Trace.upTo_time]
  constructor
  · intro h k hk hkt
    exact h k ⟨hkt.trans ht, hk⟩ hkt
  · intro h k hk hkt
    exact h k hk.2 hkt

end SA

end Consensus.Goldilocks

end
