module
public import ConsensusProblem.Derived
public import ConsensusProblem.Network
public import Mathlib.Tactic

@[expose] public section

/-! # The network: delivery lemmas (L0 facts)

Lemmas about the network conditions of `ConsensusProblem/Network.lean`: holding,
reindexing deadlines, eager logs, and transfer of delivery to a prefix. -/

namespace Consensus

namespace CommLog

variable {V M : Type} {p : EnvPoint V} {L : CommLog V M}

/-- A receipt at the deadline itself is holding. -/
theorem held_of_recv {w : V} {m : M} {d : Time} (h : L.recv w m d) : L.Held p w m d :=
  ⟨d, le_rfl, Or.inr h, fun _ h₁ h₂ => absurd (lt_of_lt_of_le h₁ h₂) (lt_irrefl _)⟩

/-- Reindexing: delivery for `dl` gives delivery for every deadline function
`dl'` that is `dl` at a later start (`dl' a = dl (f a)`, `a ≤ f a`) with a
smaller cut. At a send time `t` with `f t > t` this uses `rewake`. -/
theorem Delivers.reindex {dl dl' f : Time → Time} {cut cut' : Time} (h : L.Delivers p dl cut)
    (hf : ∀ a, a ≤ f a) (hd : ∀ a, dl' a = dl (f a)) (hc : cut' ≤ cut) :
    L.Delivers p dl' cut' := by
  constructor
  · intro v hv m t hs w hw hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    rcases (hf t).lt_or_eq with hlt | heq
    · exact h.rewake v hv m t hs w hw (f t) hlt (le_trans hdc hc) hdh haw
    · rw [← heq] at hdc hdh haw ⊢
      exact h.msgs v hv m t hs w hw (le_trans hdc hc) hdh haw
  · intro v hv m t hs w hw a hta hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    exact h.rewake v hv m t hs w hw (f a) (lt_of_lt_of_le hta (hf a)) (le_trans hdc hc)
      hdh haw
  · intro u hu x τ hτ hua hx w hw a hτa hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    exact h.txs u hu x τ hτ hua hx w hw (f a) (le_trans hτa (hf a)) (le_trans hdc hc) hdh haw

/-- With no honest send before `0`, `PSync 0` is synchrony up to the horizon
(and so up to every cut). Without `SendsFromZero` this fails: a send at
`t < 0` has `PSync 0` deadline `Δ`, later than `t + Δ`. -/
theorem PSync.syncUntil_zero (hns : L.SendsFromZero p) (h : L.PSync p 0) (b : Time) :
    L.SyncUntil p b := by
  constructor
  · intro v hv m t hs w hw _ hdh haw
    have ht0 := hns v hv m t hs
    have := h.msgs v hv m t hs w hw
    simp only [max_eq_left ht0] at this
    exact this hdh hdh haw
  · intro v hv m t hs w hw a hta _ hdh haw
    have ht0 := hns v hv m t hs
    have := h.rewake v hv m t hs w hw a hta
    simp only [max_eq_left (le_trans ht0 hta.le)] at this
    exact this hdh hdh haw
  · intro u hu x τ hτ hua hx w hw a hτa _ hdh haw
    have := h.txs u hu x τ hτ hua hx w hw a hτa
    simp only [max_eq_left (le_trans hτ hτa)] at this
    exact this hdh hdh haw

/-- An eager log meets every deadline function at or above `max a g`, at
every cut. -/
theorem EagerFrom.delivers {g : Time} (h : L.EagerFrom p g) {dl : Time → Time}
    (hdl : ∀ a, max a g ≤ dl a) (cut : Time) : L.Delivers p dl cut := by
  constructor
  · intro v hv m t hs w hw _ hdh haw
    exact held_of_recv (h.recv v hv m t hs w hw (dl t) (hdl t) hdh haw)
  · intro v hv m t hs w hw a hta _ hdh haw
    refine held_of_recv (h.recv v hv m t hs w hw (dl a) ?_ hdh haw)
    exact le_trans (max_le_max hta.le le_rfl) (hdl a)
  · intro u hu x τ hτ hua hx w hw a hτa _ _ haw
    have hle : τ ≤ dl a := le_trans hτa (le_trans (le_max_left a g) (hdl a))
    exact ⟨dl a, le_trans hτ hle, le_rfl, h.txs u hu x τ hτ hua hx w hw (dl a) hle haw⟩

/-- An eager log from `g` is partially synchronous with every GST `g' ≥ g`. -/
theorem EagerFrom.psync {g g' : Time} (h : L.EagerFrom p g) (hg : g ≤ g') : L.PSync p g' := by
  apply h.delivers
  intro a
  have := p.env.Δ_pos
  exact max_le (le_trans (le_max_left a g') (by linarith))
    (le_trans hg (le_trans (le_max_right a g') (by linarith)))

/-- An eager log from `g ≤ 0` with no honest send before `0` is synchronous up
to every cut. -/
theorem EagerFrom.syncUntil {g : Time} (hns : L.SendsFromZero p) (h : L.EagerFrom p g)
    (hg : g ≤ 0) (b : Time) : L.SyncUntil p b :=
  (h.psync hg).syncUntil_zero hns b

/-- Delivery transfers to a log `L'` that agrees with `L` up to `b`, on the
point with horizon `b ≤ horizon`, for deadlines at or after the start
(`a ≤ dl a`): everything the clauses read lies at times `≤ b`. -/
theorem Delivers.prefix {L' : CommLog V M} {dl : Time → Time} {cut b : Time}
    (h : L.Delivers p dl cut) (hag : L'.AgreesUpTo L b) (hb : b ≤ p.horizon)
    (hdl : ∀ a, a ≤ dl a) : L'.Delivers { p with horizon := b } dl cut := by
  have hheld : ∀ w m d, d ≤ b → L.Held p w m d → L'.Held { p with horizon := b } w m d := by
    rintro w m d hd ⟨t', ht', hs, hn⟩
    have hb' : t' ≤ b := le_trans ht' hd
    refine ⟨t', ht', ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl (((hag.1 w m t' hb').1).mpr hs)
    · exact Or.inr (((hag.1 w m t' hb').2).mpr hs)
  constructor
  · intro v hv m t hs w hw hdc hdh haw
    have ht : t ≤ b := le_trans (hdl t) hdh
    exact hheld w m _ hdh (h.msgs v hv m t (((hag.1 v m t ht).1).mp hs) w hw hdc
      (le_trans hdh hb) haw)
  · intro v hv m t hs w hw a hta hdc hdh haw
    have ht : t ≤ b := le_trans (le_trans hta.le (hdl a)) hdh
    exact hheld w m _ hdh (h.rewake v hv m t (((hag.1 v m t ht).1).mp hs) w hw a hta hdc
      (le_trans hdh hb) haw)
  · intro u hu x τ hτ hua hx w hw a hτa hdc hdh haw
    obtain ⟨τ', h0, hτ', hin⟩ := h.txs u hu x τ hτ hua hx w hw a hτa hdc (le_trans hdh hb) haw
    exact ⟨τ', h0, hτ', by rw [hag.2 w τ' (le_trans hτ' hdh)]; exact hin⟩

end CommLog

end Consensus

end
