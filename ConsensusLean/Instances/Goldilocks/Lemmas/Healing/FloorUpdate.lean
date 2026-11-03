module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

public section

/-! # Goldilocks: a unanimous update writes a fresh lock floor

consensus-lean#135, item N3. Under `Unanimous tr H p P`, the slot-`p` update of an honest node at
`t_p + 6Δ` has result `P`, no veto, and `P` passes the fast test (`first_update_post`). When `P`
is its own viable ancestor, the update writes the fast lock `⟨P.root, p, true⟩`
(`fastLock_mem_updateConfirmation`, the step `hlock` of `candidate_after_fast_update`, stated
here without the viable-tree premise). So after the tick the node has the floor of slot `p` on
every `B₀ ⪯ P` of its frame. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **A fast update writes a fresh fast lock**: result `P`, no veto, fast selection `P`, `t`
within the new lock's guaranteed life (`slot(t) ≤ u + 2`), and `P` its own viable ancestor. The
lock's expiry is `fastExpiry ≥ u + 2`. -/
theorem fastLock_mem_updateConfirmation_floor {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {u : Nat} {P : Blk sp.n FGP} (hPt : P ∈ Φ.tree) (hva : Φ.viableAncestor P = P)
    (hconf : getConfirmation sp A Φ u = some P) (hnv : ¬ conflictsWithLock sp A.locks Φ t P)
    (hfast : fastSelect sp A Φ u P = some P) (hlive : sp.slot t ≤ u + 2) :
    ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : Lock) ∈ (updateConfirmation sp A Φ t u).locks := by
  -- no live lock vetoes `P`, so `P` is also the deepest fast block of the unvetoed path
  obtain ⟨⟨hPp, hPf⟩, hmax⟩ := deepest_mem hfast
  have hD : deepest Φ {B | B ∈ {B | B ∈ confirmationPath sp Φ P ∧
      ¬ conflictsWithLock sp A.locks Φ t B} ∧ FastTest sp A Φ u B} = some P := by
    have hex : ∃ B, IsDeepest Φ {B | B ∈ {B | B ∈ confirmationPath sp Φ P ∧
        ¬ conflictsWithLock sp A.locks Φ t B} ∧ FastTest sp A Φ u B} B :=
      ⟨P, ⟨⟨hPp, hnv⟩, hPf⟩, fun X hX hXP => hmax X ⟨hX.1.1, hX.2⟩ hXP⟩
    cases hd : deepest Φ {B | B ∈ {B | B ∈ confirmationPath sp Φ P ∧
        ¬ conflictsWithLock sp A.locks Φ t B} ∧ FastTest sp A Φ u B} with
    | none =>
      unfold deepest at hd
      simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
    | some D' =>
      obtain ⟨hD', hmax'⟩ := deepest_mem hd
      by_contra hne
      have hne' : D' ≠ P := fun h => hne (congrArg some h)
      rcases hmax D' ⟨hD'.1.1, hD'.2⟩ hne' with h₁ | ⟨h₁, h₂⟩ <;>
        rcases hmax' P ⟨⟨hPp, hnv⟩, hPf⟩ (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega
  unfold updateConfirmation
  simp only [hconf]
  exact ⟨_, le_fastExpiry sp _ Φ t u, ⟨P.root, u, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPt, rfl,
    hlive.trans (le_fastExpiry sp _ Φ t u), by rw [hva]⟩

/-- `fastLock_mem_updateConfirmation_floor` without the expiry bound. -/
theorem fastLock_mem_updateConfirmation {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {u : Nat} {P : Blk sp.n FGP} (hPt : P ∈ Φ.tree) (hva : Φ.viableAncestor P = P)
    (hconf : getConfirmation sp A Φ u = some P) (hnv : ¬ conflictsWithLock sp A.locks Φ t P)
    (hfast : fastSelect sp A Φ u P = some P) (hlive : sp.slot t ≤ u + 2) :
    ∃ e, (⟨P.root, u, true, e⟩ : Lock) ∈ (updateConfirmation sp A Φ t u).locks :=
  let ⟨e, _, h⟩ := fastLock_mem_updateConfirmation_floor hPt hva hconf hnv hfast hlive
  ⟨e, h⟩

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g : Time}

end Consensus.Goldilocks.Healing

end
