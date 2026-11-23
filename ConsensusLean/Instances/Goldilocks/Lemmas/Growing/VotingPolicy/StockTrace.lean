module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.VotingPolicy.Adapter
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # Voting-policy spike: a calendar AC run is a Goldilocks AC run

A trace of the calendar AC (`calendarAC`) becomes a trace of the Goldilocks AC
(`stockTrace`) by unlabelling the `ac_to_fg` calls outside the signing appointments, which are
stutters (`calendarAC_step_toFG_of_not_sign`), and keeping every other call. The states are the
same (`stockTrace_state`). `acLocalRun_stockTrace`: the AC contract under growing faults carries
over, given that every dropped call follows another call of its node at the same time (in a node
run, the tick's own `ac_on_tick` call, which comes first in its tick group). -/

namespace Consensus.Goldilocks.VotingPolicy

open AC

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP} {sign : Time → Bool}

/-- A calendar `ac_to_fg` call outside the appointments, at time `t`: a stutter. -/
def isStutter (sign : Time → Bool) (t : Time) : (calendarAC ro sign).Call → Bool
  | .toFG => !sign t
  | _ => false

theorem isStutter_eq_true_iff (t : Time) (c : (calendarAC ro sign).Call) :
    isStutter sign t c = true ↔ c = .toFG ∧ sign t = false := by
  cases c <;> simp [isStutter]

@[simp] theorem isStutter_tick (t : Time) : isStutter (ro := ro) sign t .tick = false := by rfl

/-- The Goldilocks label of a calendar call at time `t`; none for a stutter. -/
noncomputable def stockLabel (sign : Time → Bool) (t : Time) (ℓ : ACLabel (calendarAC ro sign)) :
    Option (ACLabel (goldilocksAC sp FGP ro)) :=
  if isStutter sign t ℓ.call then none else some ⟨stockCall ℓ.call, ℓ.frame, ℓ.emits⟩

/-- The calendar trace as a Goldilocks AC trace: the stutters unlabelled. -/
noncomputable def stockTrace (T : ACTrace (calendarAC ro sign)) :
    ACTrace (goldilocksAC sp FGP ro) where
  init := T.init
  node := T.node
  time := T.time
  event := T.event
  pos := T.pos
  label i := (T.label i).bind (stockLabel sign (T.time i))
  post := T.post
  awake := T.awake
  observationHorizon := T.observationHorizon

variable (T : ACTrace (calendarAC ro sign))

theorem stockTrace_time : (stockTrace T).time = T.time := by rfl

theorem stockTrace_awake : (stockTrace T).awake = T.awake := by rfl

theorem stockTrace_init : (stockTrace T).init = T.init := by rfl

/-- A call of the stock trace is a calendar call that is not a stutter. -/
theorem stockTrace_callAt_iff {y : Fin sp.n} {i : Nat} {ℓ' : ACLabel (goldilocksAC sp FGP ro)} :
    (stockTrace T).CallAt y i ℓ' ↔ ∃ ℓ, T.CallAt y i ℓ ∧ isStutter sign (T.time i) ℓ.call = false ∧
      ℓ' = ⟨stockCall ℓ.call, ℓ.frame, ℓ.emits⟩ := by
  constructor
  · rintro ⟨hn, hl⟩
    change (T.label i).bind (stockLabel sign (T.time i)) = some ℓ' at hl
    obtain ⟨ℓ, hℓ, hs⟩ := Option.bind_eq_some_iff.mp hl
    unfold stockLabel at hs
    split_ifs at hs with h
    cases hs
    exact ⟨ℓ, ⟨hn, hℓ⟩, by simpa using h, rfl⟩
  · rintro ⟨ℓ, ⟨hn, hℓ⟩, hs, rfl⟩
    refine ⟨hn, ?_⟩
    change (T.label i).bind (stockLabel sign (T.time i)) = _
    rw [hℓ]
    simp [stockLabel, hs]

variable {T} {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {ini : Fin sp.n → ACState sp.n}

/-- A stutter of a node honest at its time leaves the node's state. -/
private theorem post_of_stutter (hr : Growing.ACLocalRun (calendarAC ro sign) H U T ini)
    {y : Fin sp.n} {j : Nat} {ℓ : ACLabel (calendarAC ro sign)} (hc : T.CallAt y j ℓ)
    (hy : y ∈ H (T.time j)) (hs : isStutter sign (T.time j) ℓ.call = true) :
    T.post j = T.state y j := by
  have hex := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hex
  cases hcall : ℓ.call with
  | toFG =>
    rw [hcall] at hex hs
    have hsg : sign (T.time j) = false := by simpa [isStutter] using hs
    rw [calendarAC_step_toFG_of_not_sign ro hsg] at hex
    exact (congrArg Prod.fst hex).symm
  | _ => rw [hcall] at hs; simp [isStutter] at hs

/-- **The states are the calendar's**, for a node honest at every one of its earlier cuts. -/
theorem stockTrace_state (hr : Growing.ACLocalRun (calendarAC ro sign) H U T ini)
    {y : Fin sp.n} : ∀ i, (∀ j < i, T.node j = y → y ∈ H (T.time j)) →
      (stockTrace T).state y i = T.state y i
  | 0, _ => rfl
  | i + 1, hy => by
    have ih := stockTrace_state hr i fun j hj => hy j (by omega)
    by_cases hn : T.node i = y
    · cases hl : T.label i with
      | none =>
        have h1 : ∀ ℓ, ¬ T.CallAt y i ℓ := fun ℓ h => by rw [h.2] at hl; cases hl
        have h2 : ∀ ℓ, ¬ (stockTrace T).CallAt y i ℓ := fun ℓ h => by
          obtain ⟨ℓ₀, h₀, -⟩ := (stockTrace_callAt_iff T).1 h; exact h1 ℓ₀ h₀
        rw [Trace.state_succ_of_not _ h1, Trace.state_succ_of_not _ h2, ih]
      | some ℓ =>
        have hc : T.CallAt y i ℓ := ⟨hn, hl⟩
        rw [Trace.state_succ_of_call _ hc]
        cases hs : isStutter sign (T.time i) ℓ.call with
        | true =>
          have h2 : ∀ ℓ', ¬ (stockTrace T).CallAt y i ℓ' := fun ℓ' h => by
            obtain ⟨ℓ₀, h₀, h₀s, -⟩ := (stockTrace_callAt_iff T).1 h
            rw [h₀.2] at hl; cases hl; rw [hs] at h₀s; cases h₀s
          rw [Trace.state_succ_of_not _ h2, ih, post_of_stutter hr hc (hy i (by omega) hn) hs]
        | false =>
          rw [Trace.state_succ_of_call _ ((stockTrace_callAt_iff T).2 ⟨ℓ, hc, hs, rfl⟩)]
          rfl
    · have h1 : ∀ ℓ, ¬ T.CallAt y i ℓ := fun ℓ h => hn h.1
      have h2 : ∀ ℓ, ¬ (stockTrace T).CallAt y i ℓ := fun ℓ h => hn h.1
      rw [Trace.state_succ_of_not _ h1, Trace.state_succ_of_not _ h2, ih]

/-- A node honest at a cut was honest at each earlier one. -/
private theorem honest_before (hr : Growing.ACLocalRun (calendarAC ro sign) H U T ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (T.time i)) :
    ∀ j < i, T.node j = y → y ∈ H (T.time j) :=
  fun _ hj _ => hr.antitone (hr.time_mono hj.le) hy

/-- The frame law of the stock trace at a calendar call (a stutter included), by strong
induction: a dropped stutter keeps the frame (`callOK_drop_toFG`). -/
private theorem frameLaw_stock (hr : Growing.ACLocalRun (calendarAC ro sign) H U T ini)
    {y : Fin sp.n} : ∀ i (ℓ : ACLabel (calendarAC ro sign)), y ∈ H (T.time i) → T.CallAt y i ℓ →
      ((stockTrace T).NoCallBetween y 0 i ∧ ∃ Φ₀, (goldilocksAC sp FGP ro).InitialFrame Φ₀ ∧
        (goldilocksAC sp FGP ro).FrameIn U Φ₀ ∧
        (goldilocksAC sp FGP ro).CallOK U Φ₀ (T.time i) (stockCall ℓ.call) ℓ.frame) ∨
      (∃ j ℓ', j < i ∧ (stockTrace T).CallAt y j ℓ' ∧ (stockTrace T).NoCallBetween y (j + 1) i ∧
        (goldilocksAC sp FGP ro).CallOK U ℓ'.frame (T.time i) (stockCall ℓ.call) ℓ.frame) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro ℓ hy hc
  have hsub : ∀ a b, T.NoCallBetween y a b → (stockTrace T).NoCallBetween y a b :=
    fun a b h k hak hkb ℓ' hk => by
      obtain ⟨ℓ₀, h₀, -⟩ := (stockTrace_callAt_iff T).1 hk
      exact h k hak hkb ℓ₀ h₀
  rcases hr.frameLaw y i ℓ hy hc with ⟨hno, Φ₀, hi, hin, hok⟩ | ⟨j, ℓj, hji, hj, hno, hok⟩
  · exact Or.inl ⟨hsub _ _ hno, Φ₀, hi, hin, (calendarAC_callOK_iff ro sign _).1 hok⟩
  · have hok' := (calendarAC_callOK_iff ro sign _).1 hok
    cases hs : isStutter sign (T.time j) ℓj.call with
    | false =>
      exact Or.inr ⟨j, _, hji, (stockTrace_callAt_iff T).2 ⟨ℓj, hj, hs, rfl⟩, hsub _ _ hno, hok'⟩
    | true =>
      have htoFG : stockCall ℓj.call = .toFG := by
        cases h : ℓj.call <;> rw [h] at hs <;> simp [isStutter] at hs ⊢
      have hyj := hr.antitone (hr.time_mono hji.le) hy
      -- the stutter is not a stock call
      have hnot : ∀ ℓ', ¬ (stockTrace T).CallAt y j ℓ' := fun ℓ' h => by
        obtain ⟨ℓ₀, h₀, h₀s, -⟩ := (stockTrace_callAt_iff T).1 h
        have he : ℓ₀ = ℓj := Option.some.inj (h₀.2.symm.trans hj.2)
        rw [he, hs] at h₀s; cases h₀s
      have hjoin : ∀ a, (stockTrace T).NoCallBetween y a j →
          (stockTrace T).NoCallBetween y a i := fun a h k hak hki ℓ' hk => by
        rcases Nat.lt_trichotomy k j with hkj | rfl | hkj
        · exact h k hak hkj ℓ' hk
        · exact hnot ℓ' hk
        · exact hsub _ _ hno k hkj hki ℓ' hk
      rcases ih j hji ℓj hyj hj with ⟨hno₀, Φ₀, hi, hin, hok₀⟩ | ⟨k, ℓk, hkj, hk, hnok, hokk⟩
      · rw [htoFG] at hok₀
        have hΦ := callOK_toFG_frame ro hok₀
        rw [hΦ] at hok'
        exact Or.inl ⟨hjoin 0 hno₀, Φ₀, hi, hin, hok'⟩
      · rw [htoFG] at hokk
        exact Or.inr ⟨k, ℓk, by omega, hk, hjoin _ hnok, callOK_drop_toFG ro hokk hok'⟩

/-- **The node adapter, AC part: a calendar AC run is a Goldilocks AC run.** The calendar AC
contract under growing faults gives the Goldilocks AC contract on `stockTrace`, with the same
states, given `hprev`: each stutter of a node honest at its time follows a kept call of that node
at the same time. -/
theorem acLocalRun_stockTrace (hr : Growing.ACLocalRun (calendarAC ro sign) H U T ini)
    (hprev : ∀ y k ℓ, y ∈ H (T.time k) → T.CallAt y k ℓ →
      isStutter sign (T.time k) ℓ.call = true →
      ∃ j < k, ∃ ℓ', T.CallAt y j ℓ' ∧ isStutter sign (T.time j) ℓ'.call = false ∧
        T.time j = T.time k) :
    Growing.ACLocalRun (goldilocksAC sp FGP ro) H U (stockTrace T) ini where
  antitone := hr.antitone
  coherent := hr.coherent
  init := hr.init
  exec := fun i ℓ' hl hH => by
    have hc : (stockTrace T).CallAt (T.node i) i ℓ' := ⟨rfl, hl⟩
    obtain ⟨ℓ, hcT, hs, rfl⟩ := (stockTrace_callAt_iff T).1 hc
    change (goldilocksAC sp FGP ro).step (T.node i) ((stockTrace T).state (T.node i) i) ℓ.frame
      (T.time i) (stockCall ℓ.call) = (T.post i, ℓ.emits)
    rw [stockTrace_state hr (y := T.node i) i (honest_before hr hH)]
    have hex := hr.exec i ℓ hcT.2 hH
    rw [← hex]
    cases hcall : ℓ.call with
    | toFG =>
      rw [hcall] at hs
      have hsg : sign (T.time i) = true := by simpa [isStutter] using hs
      rw [stockCall_toFG]
      exact (calendarAC_step_toFG_of_sign ro hsg _ _ _).symm
    | _ => exact (calendarAC_step ro sign _ _ _ _ _ (by simp)).symm
  frameLaw := fun y i ℓ' hy hc => by
    obtain ⟨ℓ, hcT, -, rfl⟩ := (stockTrace_callAt_iff T).1 hc
    exact frameLaw_stock hr i ℓ hy hcT
  time_nonneg := hr.time_nonneg
  time_mono := hr.time_mono
  awake_of_call := fun y i ℓ' hy hc => by
    obtain ⟨ℓ, hc, -, -⟩ := (stockTrace_callAt_iff T).1 hc
    exact hr.awake_of_call y i ℓ hy hc
  restart_of_sleep := fun y i ℓ' u hy hc hu hui hs hb => by
    obtain ⟨ℓ, hcT, -, rfl⟩ := (stockTrace_callAt_iff T).1 hc
    refine (stockCall_eq_restart_iff _).2 (hr.restart_of_sleep y i ℓ u hy hcT hu hui hs ?_)
    intro j hj ℓj hcj
    have hyj := hr.antitone (hr.time_mono hj.le) hy
    cases hsj : isStutter sign (T.time j) ℓj.call with
    | false => exact hb j hj _ ((stockTrace_callAt_iff T).2 ⟨ℓj, hcj, hsj, rfl⟩)
    | true =>
      obtain ⟨k, hkj, ℓk, hck, hsk, htk⟩ := hprev y j ℓj hyj hcj hsj
      rw [← htk]
      exact hb k (by omega) _ ((stockTrace_callAt_iff T).2 ⟨ℓk, hck, hsk, rfl⟩)
  restart_at_wake := fun y u v hy hu huv hs hw => by
    obtain ⟨k, ⟨ℓ, hc, hr'⟩, h1, h2⟩ := hr.restart_at_wake y u v hy hu huv hs hw
    refine ⟨k, ⟨_, (stockTrace_callAt_iff T).2 ⟨ℓ, hc, by rw [hr']; rfl, rfl⟩, ?_⟩, h1, h2⟩
    exact (stockCall_eq_restart_iff _).2 hr'
  sleep_of_restart := fun y i ℓ' hy hc hr' => by
    obtain ⟨ℓ, hcT, -, rfl⟩ := (stockTrace_callAt_iff T).1 hc
    obtain ⟨u, hu, hui, hs, hb⟩ :=
      hr.sleep_of_restart y i ℓ hy hcT ((stockCall_eq_restart_iff _).1 hr')
    refine ⟨u, hu, hui, hs, fun j hj ℓj hcj => ?_⟩
    obtain ⟨ℓ₀, h₀, -, -⟩ := (stockTrace_callAt_iff T).1 hcj
    exact hb j hj ℓ₀ h₀

end Consensus.Goldilocks.VotingPolicy
