module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Steps of a parent-first receipt traversal

The steps of a received forwarding chain's traversal that read neither the fault model nor the
run: the ancestry guard on one coherent chain, acceptance at the exact canonical receipt
position, and the genesis-parent leaf wrapper. Constant faults (`Simulation/PublicationDecode`)
and growing faults (`Growing/Simulation/Forward/Held`) use them alike. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- On one coherent ancestor chain, an unheld child above the receiver's finalized
tip can be attached to its held parent. No agreement between receivers is used. -/
theorem receipt_ancestry {n : Nat} {FGP ACP : Type}
    {U T : Set (Block n FGP ACP)} {F A P B : Block n FGP ACP}
    (hU : Coherent U) (hF : F ∈ T) (hAB : Anc U A B) (hFB : Anc U F B)
    (hparent : ParentIn U P A) (hP : P ∈ T)
    (hlocal : ∀ {X Y}, Anc U X Y → Y ∈ T → Anc T X Y) :
    A ∈ T ∨ Anc (insert A T) F A := by
  rcases Anc.total hU hAB hFB with hAF | hFA
  · have h := hlocal hAF hF
    by_cases he : A = F
    · exact Or.inl (he ▸ hF)
    · exact Or.inl (h.mem he).1
  · by_cases he : F = A
    · exact Or.inl (he ▸ hF)
    · rcases hFA.cases_tail with heq | ⟨Q, hFQ, hQA⟩
      · exact False.elim (he heq.symm)
      · have hQP : Q = P := hU.1 hQA.1 hparent.1
          (Option.some.inj (hQA.2.2.symm.trans hparent.2.2))
        subst Q
        exact Or.inr (((hlocal hFQ hP).mono (Set.subset_insert _ _)).tail
          ⟨Or.inr hP, Or.inl rfl, hparent.2.2⟩)

/-- A successful store transfer at the exact canonical receipt position yields
acceptance there; a future-slot empty handler is excluded explicitly. -/
theorem deliverSeq_block_accepts {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {hs : List (Header Info × Nat)} {y : Fin sp.n} {u : Time} {B : Blk sp}
    {os : List (Wire sp.n)} {r e : Nat}
    (hd : decodeBlock sp (binding := stock) hs (blockObj sp B) = some B)
    (hseq : DeliverSeq proposer tr dg hs y u (blockObj sp B :: os) r e)
    (ht : ¬ sp.toParams.slotOf u < B.slot)
    (hon : ∃ dst', (tr.state y r).fg.onBlock B = some dst') :
    tr.AcceptAt y r B ∧ r < e := by
  have hc : canonEvent sp ro (binding := stock) hs (blockObj sp B) = some (.block B) := by
    simp only [canonEvent, hd]
  obtain ⟨dst', hon⟩ := hon
  cases hseq with
  | drop h _ => rw [hc] at h; cases h
  | noCut event h hz _ =>
    have heq := Option.some.inj (h.symm.trans hc)
    subst event
    simp [exec, onBlock, ht, hon] at hz
  | event event h hg htail =>
    have heq := Option.some.inj (h.symm.trans hc)
    subst event
    have hlen : 0 < (exec proposer dg y (tr.state y r) u (.block B)).2.length := by
      simp [exec, onBlock, ht, hon]
    obtain ⟨hn, _, _, _, hl⟩ := hg.2.1 0 hlen
    have hcall : tr.AcceptAt y r B := by
      refine ⟨by simpa using hn, ?_⟩
      simpa [exec, onBlock, ht, hon] using hl
    have hbound := (deliverSeq_cover htail).1
    exact ⟨hcall, by omega⟩

/-- The leaf wrapper processes its genesis-parent child at the same starting cut. -/
theorem deliverSeq_forward_genesis {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {hs : List (Header Info × Nat)} {y x : Fin sp.n} {u t : Time} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u (forwardObj sp x t none B).parts j j') :
    DeliverSeq proposer tr dg hs y u (blockObj sp B).parts j j' := by
  rw [Model.Obj.parts_eq] at h
  have hz : canonEvent sp ro (binding := stock) hs (forwardObj sp x t none B) = none := by
    simp [canonEvent, forwardObj, decodeBlock, decodeVoteObj, decodeAttObj, stock]
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    simpa only [forwardObj, Model.Obj.carried, Option.toList_none, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail

end Consensus.Goldilocks.Simulation

end
