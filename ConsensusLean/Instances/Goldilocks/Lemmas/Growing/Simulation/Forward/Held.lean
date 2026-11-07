module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Prefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut

public section

/-! # Parent-first receipt traversal under growing faults

The growing-fault form of `forward_receipt_held`. A receiver honest at `d ≥ 0` through its
reading cut `j` (every cut before `j` at a time `≤ d`) holds every block of a received forwarding
chain below its finalized tip, when every wrapper of the chain was accepted by its signer at a cut
at which the signer was honest. Signer and receiver need not be honest at a common time: each is
read on its own prefix run, and the blocks held while honest are their common coherent universe
(`fgRun_upTo`). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}

/-- Every cut up to an acceptance cut is at a time no later than it. -/
private theorem time_le_acc (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (k : Nat) : ∀ m < k + 1, tr.time m ≤ tr.time k :=
  fun _ hm => hrun.time_mono (by omega)

/-- Acceptance by a node honest then records its block in its tree at the following cut. -/
private theorem accepted_mem_succ_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {k : Nat} {B : Blk sp} (hx : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) :
    B ∈ (tr.state x (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call ha,
    (Store.tree_grows sp.toParams _ _ _ (reachable_upTo hrun (hrun.time_nonneg k)
      (fun m hm => time_le_acc hrun k m (by omega)) hx)).1 B _ (hrun.cutLaw x k _ ha hx).2.1]
  exact Set.mem_insert _ _

/-- A block accepted by a node honest then is held while honest. -/
private theorem accepted_held_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {k : Nat} {B : Blk sp} (hx : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) :
    B ∈ tr.HonestBlocksAt H :=
  held_upTo (hrun.time_nonneg k) (time_le_acc hrun k) hx (accepted_mem_succ_at hrun hx ha)

/-- A root occupied at a receiver honest through its cut is the exact already-accepted source
block. -/
private theorem received_root_absent_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {k r : Nat} {d : Time} {B : Blk sp}
    (hd : 0 ≤ d) (hb : ∀ m < r, tr.time m ≤ d) (hy : y ∈ H d) (hx : x ∈ H (tr.time k))
    (ha : tr.AcceptAt x k B) (hnot : B ∉ (tr.state y r).fg.tree) :
    (tr.state y r).fg.blocks B.root = none := by
  cases hb' : (tr.state y r).fg.blocks B.root with
  | none => rfl
  | some C =>
    have hroot := (reachable_upTo hrun hd hb hy).blocks_root hb'
    have hC : C ∈ (tr.state y r).fg.tree := by
      change (tr.state y r).fg.blocks C.root = some C
      rwa [hroot]
    have heq := (Compose.Growing.honest_blocks_coherent hrun hnc).1 (held_upTo hd hb hy hC)
      (accepted_held_at hrun hx ha) hroot
    exact False.elim (hnot (heq ▸ hC))

/-- The exact parent of a block accepted by a node honest then was held at its acceptance cut. -/
private theorem accepted_parent_held_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {k : Nat} {B P : Blk sp}
    (hx : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k B) (hp : B.parent = some P.root)
    (hP : P ∈ tr.HonestBlocksAt H) : P ∈ (tr.state x k).fg.tree := by
  have hb : ∀ m < k, tr.time m ≤ tr.time k := fun m hm => hrun.time_mono hm.le
  obtain ⟨pr, _, hpr, _, hh, _⟩ := Store.onBlock_eq_some (hrun.cutLaw x k _ ha hx).2.1
  have heq : pr = P.root := Option.some.inj (hpr.symm.trans hp)
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hh
  have hroot := (reachable_upTo hrun (hrun.time_nonneg k) hb hx).blocks_root hQ
  have hQt : Q ∈ (tr.state x k).fg.tree := by
    change (tr.state x k).fg.blocks Q.root = some Q
    rwa [hroot]
  have hQP := (Compose.Growing.honest_blocks_coherent hrun hnc).1
    (held_upTo (hrun.time_nonneg k) hb hx hQt) hP (hroot.trans heq)
  exact hQP ▸ hQt

/-- Two FG runs over one coherent universe give a block held at two of their honest nodes the same
state. -/
private theorem σ_eq_of_held_two {P : Params} {ACP : Type} {acp₀ : ACP} {H₁ H₂ : Set (Fin P.n)}
    {U : Set (NodeBlock P ACP)} {tr₁ tr₂ : FGTrace P ACP}
    (hr₁ : FGLocalRun acp₀ H₁ U tr₁) (hr₂ : FGLocalRun acp₀ H₂ U tr₂)
    {y z : Fin P.n} (hy : y ∈ H₁) (hz : z ∈ H₂) {i j : Nat} {B : NodeBlock P ACP}
    (hBy : B ∈ (tr₁.store y i).tree) (hBz : B ∈ (tr₂.store z j).tree) :
    (tr₁.store y i).σ B.root = (tr₂.store z j).σ B.root := by
  have hgz := (Store.accepted_tree P ACP acp₀ _ (Store.store_reachable hr₂ hz j)).2.2.2
  have hg := (Store.accepted_tree P ACP acp₀ _ (Store.store_reachable hr₁ hy i)).2.2.2 B hBy
  clear hBy
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr₁ hy,
      Store.σ_genesis hr₂ hz]
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    have hW'z : W' ∈ (tr₂.store z j).tree := by
      rcases Relation.ReflTransGen.cases_tail (hgz W hBz) with he | ⟨Z, -, hZ, -, hZp⟩
      · rw [he] at hp
        cases hp
      · obtain rfl : Z = W' := hr₂.coherent.1 (hr₂.tree_subset z hz j hZ)
          (hr₁.tree_subset y hy i h1) (Option.some.inj (hZp.symm.trans hp))
        exact hZ
    have e := Store.step_σ hr₁ hy h2 hp
    rw [ih hW'z, Store.step_σ hr₂ hz hBz hp] at e
    exact (Option.some.inj e).symm

/-- The parent state needed by receiver transfer is the same at an honest receiver and at the
source's acceptance cut, though they are honest at different times. -/
private theorem receipt_parent_state_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {r s : Nat} {d e : Time} {P : Blk sp}
    (hd : 0 ≤ d) (hb : ∀ m < r, tr.time m ≤ d) (hy : y ∈ H d)
    (he : 0 ≤ e) (hb' : ∀ m < s, tr.time m ≤ e) (hx : x ∈ H e)
    (hPy : P ∈ (tr.state y r).fg.tree) (hPx : P ∈ (tr.state x s).fg.tree) :
    (tr.state y r).fg.σ P.root = (tr.state x s).fg.σ P.root := by
  rw [← projFG_store_upTo hrun hd hy hb] at hPy ⊢
  rw [← projFG_store_upTo hrun he hx hb'] at hPx ⊢
  exact σ_eq_of_held_two (fgRun_upTo hrun hnc hd) (fgRun_upTo hrun hnc he) hy hx hPy hPx

/-- On one coherent ancestor chain, an unheld child above the receiver's finalized tip can be
attached to its held parent. -/
private theorem receipt_ancestry {n : Nat} {FGP ACP : Type}
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

/-- The tree of a receiver honest through `j` grows between its cuts up to `j`. -/
private theorem tree_mono_upTo
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j m e : Nat} {d : Time} (hd : 0 ≤ d) (hbj : ∀ k < j, tr.time k ≤ d)
    (hy : y ∈ H d) (hme : m ≤ e) (hej : e ≤ j) :
    (tr.state y m).fg.tree ⊆ (tr.state y e).fg.tree := by
  rw [← Trace.upTo_state tr y (fun k hk => hbj k (by omega)),
    ← Trace.upTo_state tr y (fun k hk => hbj k (by omega))]
  exact Compose.tree_mono (hrun.upTo hd).toLocalRun hy hme

/-- At an earlier receipt cut of a receiver honest through `j`, a block whose parent is held and
which lies below the finalized tip at `j` is held or passes the receiver's ancestry guard. -/
private theorem receipt_held_or_ancestry_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {r j : Nat} {d : Time}
    (hd : 0 ≤ d) (hbj : ∀ k < j, tr.time k ≤ d) (hy : y ∈ H d) (hrj : r ≤ j)
    {A P B : Blk sp} (hAB : Anc (tr.HonestBlocksAt H) A B)
    (hFB : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B)
    (hparent : ParentIn (tr.HonestBlocksAt H) P A)
    (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨
      Anc (insert A (tr.state y r).fg.tree) (tr.state y r).fg.F A := by
  have hbr : ∀ k < r, tr.time k ≤ d := fun k hk => hbj k (by omega)
  have hF := (Store.cache_invariants sp.toParams (SA.Payload sp.n) _ _
    (reachable_upTo hrun hd hbr hy)).1
  have hmono := Healing.run_F_mono (hrun.upTo hd).toLocalRun hy hrj
  rw [Trace.upTo_state tr y hbr, Trace.upTo_state tr y hbj] at hmono
  refine receipt_ancestry (Compose.Growing.honest_blocks_coherent hrun hnc) hF hAB
    ((hmono.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)).trans hFB) hparent hP
    (fun h hY => ?_)
  rw [← projFG_store_upTo hrun hd hy hbr] at hY ⊢
  exact Store.anc_of_U (fgRun_upTo hrun hnc hd) hy h hY

/-- At an earlier receipt cut of a receiver honest through `j`, a block accepted by a source
honest at its acceptance, with its parent held, is held or passes the receiver's acceptance
guard. -/
private theorem receipt_held_or_transfer_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {k r j : Nat} {d : Time}
    (hd : 0 ≤ d) (hbj : ∀ m < j, tr.time m ≤ d) (hy : y ∈ H d) (hrj : r ≤ j)
    {A P B : Blk sp} (hx : x ∈ H (tr.time k)) (ha : tr.AcceptAt x k A)
    (hAB : Anc (tr.HonestBlocksAt H) A B)
    (hFB : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B)
    (hp : A.parent = some P.root) (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨ ∃ dst', (tr.state y r).fg.onBlock A = some dst' := by
  have hbr : ∀ m < r, tr.time m ≤ d := fun m hm => hbj m (by omega)
  have hPu : P ∈ tr.HonestBlocksAt H := held_upTo hd hbr hy hP
  have hAu : A ∈ tr.HonestBlocksAt H := accepted_held_at hrun hx ha
  rcases receipt_held_or_ancestry_at hrun hnc hd hbj hy hrj hAB hFB ⟨hPu, hAu, hp⟩ hP with
    hheld | hanc
  · exact Or.inl hheld
  · by_cases hheld : A ∈ (tr.state y r).fg.tree
    · exact Or.inl hheld
    · apply Or.inr
      have hsrc := (hrun.cutLaw x k _ ha hx).2.1
      have hstate := receipt_parent_state_at hrun hnc hd hbr hy (hrun.time_nonneg k)
        (fun m hm => hrun.time_mono hm.le) hx hP (accepted_parent_held_at hrun hnc hx ha hp hPu)
      exact Store.onBlock_transfer hsrc hp
        (received_root_absent_at hrun hnc hd hbr hy hx ha hheld)
        (Option.isSome_iff_exists.mpr ⟨P, hP⟩) hstate hanc

/-- A successful store transfer at the exact canonical receipt position yields acceptance there;
a future-slot empty handler is excluded explicitly. -/
private theorem deliverSeq_block_accepts
    {hs : List (Header Info × Nat)} {y : Fin sp.n} {u : Time} {B : Blk sp}
    {os : List (Wire sp.n)} {r e : Nat}
    (hd : decodeBlock sp hs (blockObj sp B) = some B)
    (hseq : DeliverSeq proposer tr dg hs y u (blockObj sp B :: os) r e)
    (ht : ¬ sp.toParams.slotOf u < B.slot)
    (hon : ∃ dst', (tr.state y r).fg.onBlock B = some dst') :
    tr.AcceptAt y r B ∧ r < e := by
  have hc : canonEvent sp ro hs (blockObj sp B) = some (.block B) := by
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
private theorem deliverSeq_forward_genesis
    {hs : List (Header Info × Nat)} {y x : Fin sp.n} {u t : Time} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u (forwardObj sp x t none B).parts j j') :
    DeliverSeq proposer tr dg hs y u (blockObj sp B).parts j j' := by
  rw [Model.Obj.parts_eq] at h
  have hz : canonEvent sp ro hs (forwardObj sp x t none B) = none := by
    simp [canonEvent, forwardObj, decodeBlock, decodeVoteObj, decodeAttObj]
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    simpa only [forwardObj, Model.Obj.carried, Option.toList_none, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail

/-- **Parent-first receipt traversal under growing faults.** A receiver honest at `d ≥ 0` through
its reading cut `j` admits a received forwarding chain whose wrappers were each accepted by their
signer at a cut where it was honest, when its finalized tip at `j` is below the chain's child. -/
theorem forward_receipt_held_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} {j : Nat} {d : Time}
    (hd : 0 ≤ d) (hbj : ∀ k < j, tr.time k ≤ d) (hy : y ∈ H d)
    {hs : List (Header Info × Nat)} {u : Time} {B : Blk sp}
    (hFB : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∀ (A : Blk sp) (o : Wire sp.n) (t : Time) (p : Option (Wire sp.n)) (r e : Nat),
      decodeForward sp hs o = some (x, t, p, A) →
      DeliverSeq proposer tr dg hs y u o.parts r e → e ≤ j → t ≤ u →
      Anc (tr.HonestBlocksAt H) A B →
      (∀ q tq pq C, Model.Obj.Contains o q →
        decodeForward sp hs q = some (x, tq, pq, C) →
          ∃ k, tr.AcceptAt x k C ∧ x ∈ H (tr.time k)) →
      A ∈ (tr.state y e).fg.tree := by
  intro A
  induction hslot : A.slot using Nat.strong_induction_on generalizing A with
  | h n ih =>
    intro o t p r e hd' hseq hej htu hAB hsource
    obtain ⟨k, ha, hxk⟩ := hsource o t p A (Model.Obj.Contains.refl _) hd'
    have hre := (deliverSeq_cover hseq).1
    have child (m : Nat) (P : Blk sp) (hPe : P ∈ (tr.state y m).fg.tree)
        (hp : A.parent = some P.root)
        (hchild : DeliverSeq proposer tr dg hs y u (blockObj sp A).parts m e) :
        A ∈ (tr.state y e).fg.tree := by
      have hme := (deliverSeq_cover hchild).1
      rcases receipt_held_or_transfer_at hrun hnc hd hbj hy (hme.trans hej) hxk ha hAB hFB hp
          hPe with hheld | hon
      · exact tree_mono_upTo hrun hd hbj hy hme hej hheld
      · have htime := (decodeForward_child hd').2.trans htu
        have hslot' : A.slot ≤ sp.toParams.slotOf u := by
          apply Nat.le_findGreatest _ htime
          have hcast := (le_slotTime sp.toParams A.slot).trans htime
          exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
        rw [Model.Obj.parts_eq] at hchild
        obtain ⟨hacc, hlt⟩ := deliverSeq_block_accepts (decodeForward_child hd').1 hchild
          (not_lt.mpr hslot') hon
        have hym : y ∈ H (tr.time m) := hrun.antitone (hbj m (by omega)) hy
        exact tree_mono_upTo hrun hd hbj hy (Nat.succ_le_of_lt hlt) hej
          (accepted_mem_succ_at hrun hym hacc)
    rcases decodeForward_parent_cases hd' with ⟨hp, hgen⟩ |
      ⟨parent, pt, pp, P, hp, hdec, hpar, _, hlt, hpt⟩
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t none A hd'
      rw [ho] at hseq
      apply child r (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      · exact (Store.accepted_tree sp.toParams _ _ _
          (reachable_upTo hrun hd (fun k hk => hbj k (by omega)) hy)).2.2.1
      · exact hgen
      · exact deliverSeq_forward_genesis hseq
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t (some parent) A hd'
      have hc : Model.Obj.Contains o parent := by
        rw [ho]
        exact Model.Obj.Contains.step (by simp [forwardObj, Model.Obj.carried])
          (Model.Obj.Contains.refl _)
      obtain ⟨kp, hpa, hxp⟩ := hsource parent pt pp P hc hdec
      have hPu : P ∈ tr.HonestBlocksAt H := accepted_held_at hrun hxp hpa
      have hAu : A ∈ tr.HonestBlocksAt H := accepted_held_at hrun hxk ha
      have hPB : Anc (tr.HonestBlocksAt H) P B :=
        (Relation.ReflTransGen.single ⟨hPu, hAu, hpar⟩).trans hAB
      rw [ho] at hseq
      obtain ⟨m, hparent, hchild⟩ := deliverSeq_forward_parent hseq
      have hme := (deliverSeq_cover hchild).1
      have hheld := ih P.slot (by omega) P rfl parent pt pp r m hdec hparent
        (hme.trans hej) (hpt.trans htu) hPB
        (fun q tq pq C hq hqdec => hsource q tq pq C (hc.trans hq) hqdec)
      exact child m P hheld hpar hchild

end Consensus.Goldilocks.Simulation

end
