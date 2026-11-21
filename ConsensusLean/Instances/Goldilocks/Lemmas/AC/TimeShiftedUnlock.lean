module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Optimistic prefix passage for the candidate live-pool unlock

The candidate supplies `voteView A Φ s ⊤` to `unlock` and `getHead`. Stock `tryVote` supplies
`mergedVoteView` instead; these lemmas do not identify those views or describe a stock cast. -/

namespace Consensus.Goldilocks.SA.TSQ

variable {sp : SAParams} {FGP : Type} {Φ : Frm sp.n FGP}

/-- The candidate live-pool unlock handles older locks. Newer locks require provenance,
not an assumption that the reader and proposer unlocked the same way. -/
theorem live_unlock_locks (ok : FrameOK Φ) (A : SAState sp.n) (s : Nat) (t : Time)
    {C : Blk sp.n FGP} (hc : C ∈ Φ.tree) {S : Set (Fin sp.n)}
    (cover : S ⊆ scoreSeats Φ (voteView A Φ s (ETime.of (freeze sp (s + 1)))) s C)
    (half : sp.committeeSize ≤ 2 * S.ncard)
    (recent : ∀ l ∈ A.locks, s ≤ l.slot → l.LiveAt sp t → ∀ B ∈ Φ.tree,
      B.root = l.block → Compatible Φ.tree B C) :
    ∀ X ∈ liveLockBlocks sp (unlock sp A.locks Φ t s (voteView A Φ s ⊤)) Φ t,
      Compatible Φ.tree X C := by
  let V := voteView A Φ s ⊤
  have prior := unlock_compatible ok (V := V) (s := s) hc (S := S) (fun w hw => by
    have h := freeze_to_cast (cover hw)
    rw [scoreSeats_eq] at h
    exact h.elim (fun hs => Or.inr hs.2) Or.inl) half A.locks t
  have down {X Y : Blk sp.n FGP} (xy : Φ.Anc X Y) (yc : Compatible Φ.tree Y C) :
      Compatible Φ.tree X C := yc.elim (fun h => Or.inl (xy.trans h)) (Anc.total ok.coherent xy)
  intro X hx
  obtain ⟨l, hl, Y, hy, yr, _, rfl⟩ := mem_liveLockBlocks ok hx
  apply down (anc_viableAncestor _ Y)
  by_cases h : (l.slot : Int) < s
  · exact prior _ hl h _ hy yr
  obtain ⟨l₀, ⟨l₁, h₁, B, hb, br, live, rfl⟩, Z, hz, zr, rfl⟩ := hl
  split_ifs at h yr with old
  · exact (h old).elim
  change ¬ (l₁.slot : Int) < s at old
  have eq := ok.coherent.1 hy (viableAncestor_anc ok hb).1 yr
  exact eq ▸ down (anc_viableAncestor _ B) (recent l₁ h₁ (by omega) live B hb br)

/-- An optimistic certificate forces the candidate live-pool fallback before emission. The only
lock-origin obligation is for *input* locks too recent to move, not all output locks. -/
theorem optimistic_fallback_after_unlock (ok : FrameOK Φ) (A : SAState sp.n) (s : Nat)
    (t : Time) {C : Blk sp.n FGP} (hc : C ∈ Φ.tree) (signers committee faulty : Set (Fin sp.n))
    (size : committee.ncard = sp.committeeSize)
    (cover : signers ⊆ scoreSeats Φ (voteView A Φ s (ETime.of (freeze sp (s + 1)))) s C)
    (charge : equivocators (voteView A Φ s ⊤).votes ⊆ faulty)
    (eligible : voters (voteView A Φ s ⊤).votes ⊆ committee)
    (cert : 3 * committee.ncard ≤ 4 * signers.ncard) (fault : 2 * faulty.ncard < committee.ncard)
    (recent : ∀ l ∈ A.locks, s ≤ l.slot → l.LiveAt sp t → ∀ B ∈ Φ.tree,
      B.root = l.block → Compatible Φ.tree B C)
    (closed : ∀ B ∈ voterBlockTree sp A Φ (s + 1), ∀ X, Φ.Anc X B →
      X ∈ voterBlockTree sp A Φ (s + 1))
    (viable : C ∈ Φ.viableTree (voteDomain sp A Φ (s + 1)) ∨ Φ.Anc C Φ.fcRoot) :
    let V := voteView A Φ s ⊤
    let R := { A with locks := unlock sp A.locks Φ t s V }
    Φ.Anc C (getHead sp R Φ t (Φ.viableTree (voteDomain sp R Φ (s + 1))) V s) := by
  have dom := (forced_optimistic signers committee faulty cover charge eligible cert fault).2
  exact fallback_extends ok _ s t closed viable
    (live_unlock_locks ok A s t hc cover (by omega) recent) dom

end Consensus.Goldilocks.SA.TSQ

end
