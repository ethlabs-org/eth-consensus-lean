module
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Spec.Problem.Network
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The network: delivery lemmas (L0 facts)

Lemmas about the network conditions of `ConsensusLean/Spec/Problem/Network.lean`: holding,
reindexing deadlines, eager logs, and transfer of delivery to a prefix. -/

namespace Consensus

namespace CommLog

variable {V M : Type} {p : EnvPoint V} {L : CommLog V M}

/-- A receipt at the deadline itself is holding. -/
theorem held_of_recv {w : V} {m : M} {d : Time} (h : L.recv w m d) : L.Held p w m d :=
  ⟨d, le_rfl, Or.inr h, fun _ h₁ h₂ => absurd (lt_of_lt_of_le h₁ h₂) (lt_irrefl _)⟩

/-- Awake throughout an interval is awake throughout every subinterval. -/
theorem _root_.Consensus.EnvPoint.AwakeOnClosed.mono {w : V} {a b a' b' : Time}
    (h : p.AwakeOnClosed w a b) (ha : a ≤ a') (hb : b' ≤ b) : p.AwakeOnClosed w a' b' :=
  fun u h₁ h₂ => h u (le_trans ha h₁) (le_trans h₂ hb)

/-- Reindexing: delivery for `dl` and `dlF` gives delivery for every pair of
deadline functions `dl'`, `dlF'` that are `dl`, `dlF` at a later start
(`dl' a = dl (f a)`, `dlF' a = dlF (f a)`, `a ≤ f a`) with a smaller cut. -/
theorem Delivers.reindex {dl dl' dlF dlF' f : Time → Time} {cut cut' : Time}
    (h : L.Delivers p dl dlF cut) (hf : ∀ a, a ≤ f a) (hd : ∀ a, dl' a = dl (f a))
    (hdF : ∀ a, dlF' a = dlF (f a)) (hc : cut' ≤ cut) : L.Delivers p dl' dlF' cut' := by
  constructor
  · intro v m t hs hv hr w a hta hdc hdh hw haw
    rw [hd] at hdc hdh hw haw ⊢
    exact h.msgs v m t hs hv hr w (f a) (le_trans hta (hf a)) (le_trans hdc hc) hdh hw
      (haw.mono (hf a) le_rfl)
  · intro v m t hs hv hr w a hta hdc hdh hw haw
    rw [hdF] at hdc hdh hw haw ⊢
    exact h.fgAtts v m t hs hv hr w (f a) (le_trans hta (hf a)) (le_trans hdc hc) hdh hw
      (haw.mono (hf a) le_rfl)
  · intro u x τ hτ hu hua hx w a hτa hdc hdh hw haw
    rw [hd] at hdc hdh hw haw ⊢
    exact h.txs u x τ hτ hu hua hx w (f a) (le_trans hτa (hf a)) (le_trans hdc hc) hdh hw
      (haw.mono (hf a) le_rfl)

/-- With no honest send before `0`, `PSync 0` is synchrony up to the horizon
(and so up to every cut). Without `SendsFromZero` this fails: a send at
`t < 0` has `PSync 0` deadline `Δ`, later than `t + Δ`. -/
theorem PSync.syncUntil_zero (hns : L.SendsFromZero p) (h : L.PSync p 0) (b : Time) :
    L.SyncUntil p b := by
  constructor
  · intro v m t hs hv hr w a hta _ hdh hw haw
    have ht0 := sendsFromZero_iff.mp hns v m t hs hv
    have := h.msgs v m t hs hv hr w a hta
    simp only [max_eq_left (le_trans ht0 hta)] at this
    exact this hdh hdh hw haw
  · intro v m t hs hv hr w a hta _ hdh hw haw
    have ht0 := sendsFromZero_iff.mp hns v m t hs hv
    have := h.fgAtts v m t hs hv hr w a hta
    simp only [max_eq_left (le_trans ht0 hta)] at this
    exact this hdh hdh hw haw
  · intro u x τ hτ hu hua hx w a hτa _ hdh hw haw
    have := h.txs u x τ hτ hu hua hx w a hτa
    simp only [max_eq_left (le_trans hτ hτa)] at this
    exact this hdh hdh hw haw

/-- An eager log meets every pair of deadline functions strictly above
`max a g`, at every cut. -/
theorem EagerFrom.delivers {g : Time} (h : L.EagerFrom p g) {dl dlF : Time → Time}
    (hdl : ∀ a, max a g < dl a) (hdlF : ∀ a, max a g < dlF a) (cut : Time) :
    L.Delivers p dl dlF cut := by
  have hheld : ∀ {d : Time → Time}, (∀ a, max a g < d a) → ∀ v m t,
      L.sent v m t → p.HonestAt v t → ∀ w a, t ≤ a → d a ≤ p.horizon → p.HonestAt w (d a) →
        p.AwakeOnClosed w a (d a) → L.Held p w m (d a) := by
    intro d hd v m t hs hv w a hta hdh hw haw
    have hle : max t g < d a := lt_of_le_of_lt (max_le_max hta le_rfl) (hd a)
    exact held_of_recv (h.recv v m t hs hv w (d a) hle hdh hw
      (haw (d a) (le_trans (le_max_left a g) (hd a).le) le_rfl))
  constructor
  · intro v m t hs hv _ w a hta _ hdh hw haw
    exact hheld hdl v m t hs hv w a hta hdh hw haw
  · intro v m t hs hv _ w a hta _ hdh hw haw
    exact hheld hdlF v m t hs hv w a hta hdh hw haw
  · intro u x τ hτ hu hua hx w a hτa _ _ hw haw
    have hle : τ ≤ dl a := le_trans hτa (le_trans (le_max_left a g) (hdl a).le)
    exact ⟨dl a, le_trans hτ hle, le_rfl, h.txs u x τ hτ hu hua hx w (dl a) hle hw
      (haw (dl a) (le_trans (le_max_left a g) (hdl a).le) le_rfl)⟩

/-- An eager log from `g` is partially synchronous with every GST `g' ≥ g`, at delays `Δ > 1`
and `ΔF > 1`: `PSync` holds strictly before `max a g' + Δ`, that is by `max a g' + Δ − 1`, and
the eager log serves strictly after `max a g` (at `Δ = 1` it would need same-time service). -/
theorem EagerFrom.psync {g g' : Time} (h : L.EagerFrom p g) (hg : g ≤ g') (hΔ : 1 < p.env.ΔAC)
    (hΔF : 1 < p.env.ΔFG) : L.PSync p g' := by
  have key : ∀ d : Time, 1 < d → ∀ a, max a g < max a g' + d - 1 := fun d hd a =>
    max_lt (lt_of_le_of_lt (le_max_left a g') (by linarith))
      (lt_of_le_of_lt hg (lt_of_le_of_lt (le_max_right a g') (by linarith)))
  exact h.delivers (key _ hΔ) (key _ hΔF) _

/-- An eager log from `g ≤ 0` with no honest send before `0` is synchronous up
to every cut. -/
theorem EagerFrom.syncUntil {g : Time} (hns : L.SendsFromZero p) (h : L.EagerFrom p g)
    (hg : g ≤ 0) (hΔ : 1 < p.env.ΔAC) (hΔF : 1 < p.env.ΔFG) (b : Time) : L.SyncUntil p b :=
  (h.psync hg hΔ hΔF).syncUntil_zero hns b

/-- Delivery transfers to a log `L'` that agrees with `L` up to `b`, on the
point with horizon `b ≤ horizon`, for deadlines at or after the start
(`a ≤ dl a`, `a ≤ dlF a`): everything the clauses read lies at times `≤ b`, and
the two logs have the same message class. -/
theorem Delivers.prefix {L' : CommLog V M} {dl dlF : Time → Time} {cut b : Time}
    (h : L.Delivers p dl dlF cut) (hag : L'.AgreesUpTo L b) (hb : b ≤ p.horizon)
    (hdl : ∀ a, a ≤ dl a) (hdlF : ∀ a, a ≤ dlF a) :
    L'.Delivers { p with horizon := b } dl dlF cut := by
  have hheld : ∀ w m d, d ≤ b → L.Held p w m d → L'.Held { p with horizon := b } w m d := by
    rintro w m d hd ⟨t', ht', hs, hn⟩
    have hb' : t' ≤ b := le_trans ht' hd
    refine ⟨t', ht', ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl (((hag.1 w m t' hb').1).mpr hs)
    · exact Or.inr (((hag.1 w m t' hb').2).mpr hs)
  have hrow : ∀ m, L'.fgAtt m ↔ L.fgAtt m := fun m => by rw [hag.2.2]
  constructor
  · intro v m t hs hv hr w a hta hdc hdh hw haw
    have ht : t ≤ b := le_trans (le_trans hta (hdl a)) hdh
    exact hheld w m _ hdh (h.msgs v m t (((hag.1 v m t ht).1).mp hs) hv
      (fun h' => hr ((hrow m).mpr h')) w a hta hdc (le_trans hdh hb) hw haw)
  · intro v m t hs hv hr w a hta hdc hdh hw haw
    have ht : t ≤ b := le_trans (le_trans hta (hdlF a)) hdh
    exact hheld w m _ hdh (h.fgAtts v m t (((hag.1 v m t ht).1).mp hs) hv ((hrow m).mp hr)
      w a hta hdc (le_trans hdh hb) hw haw)
  · intro u x τ hτ hu hua hx w a hτa hdc hdh hw haw
    obtain ⟨τ', h0, hτ', hin⟩ := h.txs u x τ hτ hu hua hx w a hτa hdc (le_trans hdh hb) hw haw
    exact ⟨τ', h0, hτ', by rw [hag.2.1 w τ' (le_trans hτ' hdh)]; exact hin⟩

end CommLog

end Consensus

end
