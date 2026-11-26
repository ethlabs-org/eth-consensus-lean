module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the facts of HS.0 (bounded settling)

HS.0 (`Settle(Δ)`, claims §"Healing: phase service") is no longer proved in Lean: it was proved
inside the retired HR.3 (owner decision), and its proof is removed with it. What remains are
store and run facts: ancestors of a held block are held (`mem_of_anc`), the state of a node does
not change over cuts without its call (`state_eq_of_noCall`), a cut at or after `t` gives a first
cut from `t` (`exists_firstCutFrom_le`), and a snapshot's catch-up witness is read from a later
cut (`accept_before_snapshot`).

G1.2 at the chain level is `FG.FGParams.finalization_meets_crossing`
(`Lemmas/FGChain/Accountable`). -/

namespace Consensus.Goldilocks.Healing

open Store
open AC (gbar)

/-! ## Stores: strict-height finality and the evidence of a phase -/

section Stores

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- Ancestors of a held block are held. -/
theorem mem_of_anc {st : Store P ACP} {A B : NodeBlock P ACP} (h : st.Anc A B)
    (hB : B ∈ st.tree) : A ∈ st.tree := by
  induction h with
  | refl => exact hB
  | tail _ hp ih => exact ih hp.1

end Stores

/-! ## Runs: relay to the state at a time, and joining -/

section Runs

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
  {proposer : Nat → Fin P.n}

/-- The latest wake is the time of a restart. -/
private theorem lastWake_eq {y : Fin P.n} :
    ∀ {k : Nat} {w : Time}, tr.lastWake y k = (w : WithBot Time) →
      ∃ k' ≤ k, tr.RestartAt y k' ∧ tr.time k' = w
  | 0, w, h => by
    simp only [RunTrace.lastWake] at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | k + 1, w, h => by
    simp only [RunTrace.lastWake] at h
    split_ifs at h with hr
    · exact ⟨k + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k', hk', h1, h2⟩ := lastWake_eq h
      exact ⟨k', by omega, h1, h2⟩

/-- The state of `y` does not change over cuts without a call of `y`. -/
theorem state_eq_of_noCall {y : Fin P.n} {j j₂ : Nat} (hle : j ≤ j₂)
    (h : ∀ k, j ≤ k → k < j₂ → ¬ tr.IsCall y k) : tr.state y j₂ = tr.state y j := by
  induction j₂, hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [tr.state_succ_of_not fun c hc => h n hn (by omega) ⟨c, hc⟩,
      ih fun k hk hk' => h k hk (by omega)]

/-- A cut at or after `t` gives a first cut from `t`, at or before it. -/
theorem exists_firstCutFrom_le {t : Time} {j : Nat} (hj : t ≤ tr.time j) :
    ∃ j₁, tr.FirstCutFrom j₁ t ∧ j₁ ≤ j := by
  classical
  have hex : ∃ k, t ≤ tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩,
    Nat.find_min' hex hj⟩

/-- Read a snapshot's catch-up witness from a later cut. -/
theorem accept_before_snapshot {t : Time} {y : Fin P.n} {j : Nat} {B : A.Blk}
    (hj : t ≤ tr.time j)
    (catchUp : ∀ q ≤ j, tr.FirstCutFrom q t → ∃ k < q, tr.AcceptAt y k B) :
    ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < t := by
  obtain ⟨q, hq, hqj⟩ := exists_firstCutFrom_le hj
  obtain ⟨k, hk, hak⟩ := catchUp q hqj hq
  exact ⟨k, hk.trans_le hqj, hak, hq.2 k hk⟩

end Runs

end Consensus.Goldilocks.Healing

end
