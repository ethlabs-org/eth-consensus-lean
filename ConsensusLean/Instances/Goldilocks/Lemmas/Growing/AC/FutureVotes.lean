module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Future compromised emissions are not honest participation

This witness isolates the unrestricted existential in `NextTransfer`'s participation set.
It is not a counterexample to the full transfer statement: there is no honest voting call.
-/

namespace Consensus.Goldilocks.SA.Growing.FutureVotes

variable (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP)
  (Φ : Frm sp.n FGP)

def H (t : Time) : Set (Fin sp.n) := {x | t < 1 ∧ x = x}

def emission (x : Fin sp.n) : Em sp FGP :=
  ⟨⟨x, 0, sp.genesisRoot⟩, SAState.initial sp.genesisRoot, none⟩

def trace : SATrace sp FGP ro where
  init := fun _ => SAState.initial sp.genesisRoot
  node := fun i => ⟨(i - 1) % sp.n, Nat.mod_lt _ sp.toParams.hn⟩
  time := fun i => if i = 0 then 0 else 2
  event := id
  pos := fun _ => 0
  label := fun i => if i = 0 then none else
    some ⟨.tick, Φ, [emission sp FGP ⟨(i - 1) % sp.n,
      Nat.mod_lt _ sp.toParams.hn⟩]⟩
  post := fun _ => SAState.initial sp.genesisRoot
  awake := fun _ _ => True

theorem future_vote (x : Fin sp.n) :
    VoteAt (trace sp FGP ro Φ) x (x.val + 1) (emission sp FGP x) ∧
      x ∈ H sp (0 : Time) ∧ x ∉ H sp ((trace sp FGP ro Φ).time (x.val + 1)) := by
  have he : (⟨x.val % sp.n, Nat.mod_lt _ sp.toParams.hn⟩ : Fin sp.n) = x := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  constructor
  · refine ⟨⟨.tick, Φ, [emission sp FGP x]⟩, ?_, by simp⟩
    constructor <;> simp [trace, he]
  · simp [H, trace]

theorem no_prefix_vote (x : Fin sp.n) (j : Nat) (e : Em sp FGP) :
    ¬ VoteAt ((trace sp FGP ro Φ).upTo 0) x j e := by
  rintro hv
  obtain ⟨hj, ℓ, hc, _⟩ := upTo_voteAt.mp hv
  by_cases hz : j = 0
  · subst j
    simp [Trace.CallAt, trace] at hc
  · simp [trace, hz] at hj

private theorem no_honest_call {x : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hx : x ∈ H sp ((trace sp FGP ro Φ).time i))
    (hc : (trace sp FGP ro Φ).CallAt x i ℓ) : False := by
  by_cases hi : i = 0
  · subst i
    simp [Trace.CallAt, trace] at hc
  · simp [H, trace, hi] at hx

/-- The component contract permits the adversarial emissions in this trace. -/
theorem localRun {U : Set (Blk sp.n FGP)} (hU : Coherent U) :
    Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) (H sp) U
      (trace sp FGP ro Φ) where
  antitone := by
    intro a b hab x hx
    change b < 1 ∧ x = x at hx
    exact ⟨hab.trans_lt hx.1, rfl⟩
  coherent := hU
  init := by intros; rfl
  exec := by
    intro i ℓ hl hx
    exact (no_honest_call sp FGP ro Φ hx ⟨rfl, hl⟩).elim
  frameLaw := by intro y i ℓ hy hc; exact (no_honest_call sp FGP ro Φ hy hc).elim
  time_nonneg := by intro i; simp only [trace]; split <;> norm_num
  time_mono := by
    intro a b hab
    change (if a = 0 then (0 : Time) else 2) ≤ (if b = 0 then 0 else 2)
    split_ifs
    all_goals norm_num
    all_goals omega
  awake_of_call := by intros; trivial
  restart_of_sleep := by intro y i ℓ u hy hc; exact (no_honest_call sp FGP ro Φ hy hc).elim
  restart_at_wake := by intro y u v hy hu huv hs; exact (hs trivial).elim
  sleep_of_restart := by intro y i ℓ hy hc; exact (no_honest_call sp FGP ro Φ hy hc).elim

end Consensus.Goldilocks.SA.Growing.FutureVotes

end
