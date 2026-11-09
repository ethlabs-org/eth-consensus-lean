module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Lemmas.Model.Protection

public section

/-! # Forwarding decoding and recursive receipt provenance -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

theorem contained_parts_infix {n : Nat} {Role Item Body : Type}
    {o q : Model.Obj n Role Item Body} (h : Model.Obj.Contains o q) :
    ∃ pre post, o.parts = pre ++ q.parts ++ post := by
  rcases h.cases with rfl | ⟨c, hc, hcq⟩
  · exact ⟨[], [], by simp⟩
  · obtain ⟨pre, post, hp⟩ := contained_parts_infix hcq
    obtain ⟨before, after, he, _⟩ := List.eq_append_cons_of_mem hc
    refine ⟨o :: (before.flatMap Model.Obj.parts ++ pre),
      post ++ after.flatMap Model.Obj.parts, ?_⟩
    rw [Model.Obj.parts_eq, he, List.flatMap_append, List.flatMap_cons, hp]
    simp only [List.cons_append, List.append_assoc]
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (Model.Obj.carried_size_lt _)

/-- Splitting recursive receipt processing preserves the actual intermediate cut,
rather than replacing a processing occurrence by an arbitrary historical call. -/
theorem deliverSeq_append_split {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {hs : List (Header Info × Nat)}
    {y : Fin sp.n} {t : Time} (xs ys : List (Wire sp.n)) {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y t (xs ++ ys) j j') :
    ∃ m, DeliverSeq proposer tr dg hs y t xs j m ∧
      DeliverSeq proposer tr dg hs y t ys m j' := by
  induction xs generalizing j with
  | nil => exact ⟨j, .nil j, h⟩
  | cons x xs ih =>
    cases h with
    | event e he hg htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .event e he hg hl, hr⟩
    | drop he htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .drop he hl, hr⟩
    | noCut e he hz htail =>
      obtain ⟨m, hl, hr⟩ := ih htail
      exact ⟨m, .noCut e he hz hl, hr⟩

/-- A forwarding envelope itself has no node handler. -/
private theorem canonEvent_forward_none (hs : List (Header Info × Nat))
    (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n)) (B : Blk sp) :
    canonEvent sp ro hs (forwardObj sp x t p B) = none := by
  simp [canonEvent, forwardObj, decodeBlock, decodeVoteObj, decodeAttObj]

/-- A forwarding chain processes the exact parent's entire subtree before the
child's canonical block and payload; the split retains the actual cut boundary. -/
theorem deliverSeq_forward_parent {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {hs : List (Header Info × Nat)}
    {y x : Fin sp.n} {u t : Time} {parent : Wire sp.n} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u
      (forwardObj sp x t (some parent) B).parts j j') :
    ∃ m, DeliverSeq proposer tr dg hs y u parent.parts j m ∧
      DeliverSeq proposer tr dg hs y u (blockObj sp B).parts m j' := by
  rw [Model.Obj.parts_eq] at h
  have hz := canonEvent_forward_none (ro := ro) hs x t (some parent) B
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    have ht : DeliverSeq proposer tr dg hs y u
        (parent.parts ++ (blockObj sp B).parts) j j' := by
      simpa only [forwardObj, Model.Obj.carried, Option.toList_some, List.cons_append,
        List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail
    exact deliverSeq_append_split _ _ ht

/-- The leaf wrapper processes its genesis-parent child at the same starting cut. -/
private theorem deliverSeq_forward_genesis {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {hs : List (Header Info × Nat)} {y x : Fin sp.n} {u t : Time} {B : Blk sp} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y u (forwardObj sp x t none B).parts j j') :
    DeliverSeq proposer tr dg hs y u (blockObj sp B).parts j j' := by
  rw [Model.Obj.parts_eq] at h
  have hz := canonEvent_forward_none (ro := ro) hs x t none B
  cases h with
  | event e he _ _ => rw [hz] at he; cases he
  | noCut e he _ _ => rw [hz] at he; cases he
  | drop _ htail =>
    simpa only [forwardObj, Model.Obj.carried, Option.toList_none, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] using htail

/-- On one coherent ancestor chain, an unheld child above the receiver's finalized
tip can be attached to its held parent. No agreement between receivers is used. -/
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

/-- The observation's receiver guard bounds every earlier receipt cut. Once the
parent is held, the child is already held or satisfies the receiver's ancestry guard. -/
theorem receipt_held_or_ancestry {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {r j : Nat} (hrj : r ≤ j)
    {A P B : Blk sp} (hAB : Anc (tr.HonestBlocks H) A B)
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B)
    (hparent : ParentIn (tr.HonestBlocks H) P A)
    (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨
      Anc (insert A (tr.state y r).fg.tree) (tr.state y r).fg.F A := by
  have hF := (Store.cache_invariants sp.toParams (SA.Payload sp.n) _ _
    (Compose.fg_reachable hrun.toLocalRun hy r)).1
  exact receipt_ancestry (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hF hAB
    ((Healing.run_F_mono hrun.toLocalRun hy hrj).trans hFB) hparent hP
    (fun h hY => Compose.honest_held_anc hrun hnc hy h hY)

/-- The parent state needed by receiver transfer is independent of which honest
holder supplies it, including holders on opposite sides of a restart. -/
private theorem receipt_parent_state {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s : Nat} {P : Blk sp}
    (hPy : P ∈ (tr.state y r).fg.tree) (hPx : P ∈ (tr.state x s).fg.tree) :
    (tr.state y r).fg.σ P.root = (tr.state x s).fg.σ P.root := by
  have hp (z : Fin sp.n) (hz : z ∈ H) (i : Nat) :
      tr.projFG.store z i = (tr.state z i).fg := by
    change (tr.projFG.state z i).1 = _
    rw [Compose.projFG_state hrun.toLocalRun hz i]
  rw [← hp y hy r] at hPy ⊢
  rw [← hp x hx s] at hPx ⊢
  exact Store.σ_eq_of_held (Compose.projFG_localRun hrun hnc) hy hx hPy hPx

/-- Acceptance records its block in the honest tree at the following cut. -/
private theorem accepted_mem_succ {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {B : Blk sp} (ha : tr.AcceptAt x k B) :
    B ∈ (tr.state x (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call ha,
    (Store.tree_grows sp.toParams _ _ _ (Compose.fg_reachable hrun.toLocalRun hx k)).1
      B _ (hrun.cutLaw x hx k _ ha).2.1]
  exact Set.mem_insert _ _

/-- A root occupied at an honest receiver is the exact already-accepted source
block, not merely a wire-equivalent block, under run-wide collision freedom. -/
private theorem received_root_absent {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {k r : Nat} {B : Blk sp}
    (ha : tr.AcceptAt x k B) (hnot : B ∉ (tr.state y r).fg.tree) :
    (tr.state y r).fg.blocks B.root = none := by
  cases hb : (tr.state y r).fg.blocks B.root with
  | none => rfl
  | some C =>
    have hroot := (Compose.fg_reachable hrun.toLocalRun hy r).blocks_root hb
    have hC : C ∈ (tr.state y r).fg.tree := by
      change (tr.state y r).fg.blocks C.root = some C
      rwa [hroot]
    have heq := Compose.tree_root_inj hrun.toLocalRun hnc hy hx hC
      (accepted_mem_succ hrun hx ha) hroot
    exact False.elim (hnot (heq ▸ hC))

/-- The exact parent of an accepted block was held at its source acceptance cut. -/
private theorem accepted_parent_held {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {B P : Blk sp}
    (ha : tr.AcceptAt x k B) (hp : B.parent = some P.root)
    (hP : P ∈ tr.HonestBlocks H) : P ∈ (tr.state x k).fg.tree := by
  obtain ⟨pr, _, hpr, _, hh, _⟩ := Store.onBlock_eq_some (hrun.cutLaw x hx k _ ha).2.1
  have heq : pr = P.root := Option.some.inj (hpr.symm.trans hp)
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hh
  have hroot := (Compose.fg_reachable hrun.toLocalRun hx k).blocks_root hQ
  have hQt : Q ∈ (tr.state x k).fg.tree := by
    change (tr.state x k).fg.blocks Q.root = some Q
    rwa [hroot]
  have hQP := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1
    ⟨x, hx, k, hQt⟩ hP (hroot.trans heq)
  exact hQP ▸ hQt

/-- At an earlier receipt cut, a source-accepted ancestor with its parent held is
already held or passes the receiver store's full acceptance guard. -/
theorem receipt_held_or_transfer {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {k r j : Nat} (hrj : r ≤ j)
    {A P B : Blk sp} (ha : tr.AcceptAt x k A)
    (hAB : Anc (tr.HonestBlocks H) A B)
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B)
    (hp : A.parent = some P.root) (hP : P ∈ (tr.state y r).fg.tree) :
    A ∈ (tr.state y r).fg.tree ∨ ∃ dst', (tr.state y r).fg.onBlock A = some dst' := by
  have hPu : P ∈ tr.HonestBlocks H := ⟨y, hy, r, hP⟩
  have hAu : A ∈ tr.HonestBlocks H := ⟨x, hx, k + 1, accepted_mem_succ hrun hx ha⟩
  rcases receipt_held_or_ancestry hrun hnc hy hrj hAB hFB ⟨hPu, hAu, hp⟩ hP with
    hheld | hanc
  · exact Or.inl hheld
  · by_cases hheld : A ∈ (tr.state y r).fg.tree
    · exact Or.inl hheld
    · apply Or.inr
      have hsrc := (hrun.cutLaw x hx k _ ha).2.1
      have hstate := receipt_parent_state hrun hnc hx hy hP
        (accepted_parent_held hrun hnc hx ha hp hPu)
      exact Store.onBlock_transfer hsrc hp (received_root_absent hrun hnc hx hy ha hheld)
        (Option.isSome_iff_exists.mpr ⟨P, hP⟩) hstate hanc

/-- A successful store transfer at the exact canonical receipt position yields
acceptance there; a future-slot empty handler is excluded explicitly. -/
private theorem deliverSeq_block_accepts {proposer : Nat → Fin sp.n}
    {tr : GoldilocksTrace sp ro} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
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

/-- Parsing a forwarding envelope authenticates its outer signer, independently of
whether its contained block was accepted by any receiver. -/
theorem decodeForward_signer {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : o.signer? = some x := by
  rw [forwardObj_of_decodeForward hs o x t p B h]
  rfl

/-- Parent-first receipt traversal admits a source-accepted wrapper chain whenever
the final observation's receiver tip is below its child. Source provenance is kept
for every nested wrapper, not inferred from a possibly refused receiver call. -/
theorem forward_receipt_held {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {hs : List (Header Info × Nat)} {u : Time} {j : Nat} {B : Blk sp}
    (hFB : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B) :
    ∀ (A : Blk sp) (o : Wire sp.n) (t : Time) (p : Option (Wire sp.n)) (r e : Nat),
      decodeForward sp hs o = some (x, t, p, A) →
      DeliverSeq proposer tr dg hs y u o.parts r e → e ≤ j → t ≤ u →
      Anc (tr.HonestBlocks H) A B →
      (∀ q tq pq C, Model.Obj.Contains o q →
        decodeForward sp hs q = some (x, tq, pq, C) → ∃ k, tr.AcceptAt x k C) →
      A ∈ (tr.state y e).fg.tree := by
  intro A
  induction hslot : A.slot using Nat.strong_induction_on generalizing A with
  | h n ih =>
    intro o t p r e hd hseq hej htu hAB hsource
    obtain ⟨k, ha⟩ := hsource o t p A (Model.Obj.Contains.refl _) hd
    have hre := (deliverSeq_cover hseq).1
    have child (m : Nat) (P : Blk sp) (hPe : P ∈ (tr.state y m).fg.tree)
        (hp : A.parent = some P.root)
        (hchild : DeliverSeq proposer tr dg hs y u (blockObj sp A).parts m e) :
        A ∈ (tr.state y e).fg.tree := by
      have hme := (deliverSeq_cover hchild).1
      rcases receipt_held_or_transfer hrun hnc hx hy (hme.trans hej) ha hAB hFB hp hPe with
        hheld | hon
      · exact Compose.tree_mono hrun.toLocalRun hy hme hheld
      · have htime := (decodeForward_child hd).2.trans htu
        have hslot' : A.slot ≤ sp.toParams.slotOf u := by
          apply Nat.le_findGreatest _ htime
          have hcast := (le_slotTime sp.toParams A.slot).trans htime
          exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
        rw [Model.Obj.parts_eq] at hchild
        obtain ⟨hacc, hlt⟩ := deliverSeq_block_accepts (decodeForward_child hd).1 hchild
          (not_lt.mpr hslot') hon
        exact Compose.tree_mono hrun.toLocalRun hy (Nat.succ_le_of_lt hlt)
          (accepted_mem_succ hrun hy hacc)
    rcases decodeForward_parent_cases hd with ⟨hp, hgen⟩ |
      ⟨parent, pt, pp, P, hp, hdec, hpar, _, hlt, hpt⟩
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t none A hd
      rw [ho] at hseq
      apply child r (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      · exact (Store.accepted_tree sp.toParams _ _ _
          (Compose.fg_reachable hrun.toLocalRun hy r)).2.2.1
      · exact hgen
      · exact deliverSeq_forward_genesis hseq
    · subst p
      have ho := forwardObj_of_decodeForward hs o x t (some parent) A hd
      have hc : Model.Obj.Contains o parent := by
        rw [ho]
        exact Model.Obj.Contains.step (by simp [forwardObj, Model.Obj.carried])
          (Model.Obj.Contains.refl _)
      obtain ⟨kp, hpa⟩ := hsource parent pt pp P hc hdec
      have hPu : P ∈ tr.HonestBlocks H := ⟨x, hx, kp + 1, accepted_mem_succ hrun hx hpa⟩
      have hAu : A ∈ tr.HonestBlocks H := ⟨x, hx, k + 1, accepted_mem_succ hrun hx ha⟩
      have hPB : Anc (tr.HonestBlocks H) P B :=
        (Relation.ReflTransGen.single ⟨hPu, hAu, hpar⟩).trans hAB
      rw [ho] at hseq
      obtain ⟨m, hparent, hchild⟩ := deliverSeq_forward_parent hseq
      have hme := (deliverSeq_cover hchild).1
      have hheld := ih P.slot (by omega) P rfl parent pt pp r m hdec hparent
        (hme.trans hej) (hpt.trans htu) hPB
        (fun q tq pq C hq hqdec => hsource q tq pq C (hc.trans hq) hqdec)
      exact child m P hheld hpar hchild

/-- Decoding the same canonical block under two digest tables agrees when they agree
on that block's header; this is the root-sensitive replacement for wire injectivity. -/
theorem decodeBlock_transport {hs hs' : List (Header Info × Nat)} {o : Wire sp.n}
    {B : Blk sp} (hd : decodeBlock sp hs o = some B)
    (hr : rootOf hs' (headerOf sp B) = rootOf hs (headerOf sp B)) :
    decodeBlock sp hs' o = some B := by
  obtain rfl := eq_blockObj_of_decodeBlock hd
  unfold decodeBlock at hd ⊢
  simp only [blockObj] at hd ⊢
  rw [hr]
  exact hd

/-- Forwarding decode is unchanged when both digest tables agree on every
canonical child carried by the envelope, including its recursive parent chain. -/
theorem decodeForward_transport {hs hs' : List (Header Info × Nat)} :
    ∀ (B : Blk sp) (o : Wire sp.n) (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n)),
      decodeForward sp hs o = some (x, t, p, B) →
      (∀ C : Blk sp, Model.Obj.Contains o (blockObj sp C) →
        rootOf hs' (headerOf sp C) = rootOf hs (headerOf sp C)) →
      decodeForward sp hs' o = some (x, t, p, B) := by
  intro B
  induction hslot : B.slot using Nat.strong_induction_on generalizing B with
  | h n ih =>
    intro o x t p hd hr
    have ho := forwardObj_of_decodeForward hs o x t p B hd
    have hc : Model.Obj.Contains o (blockObj sp B) := by
      rw [ho]
      exact Model.Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _))
        (Model.Obj.Contains.refl _)
    have hb := decodeBlock_transport (decodeForward_child hd).1 (hr B hc)
    have ht := decodeForward_time_nonneg hd
    have htime := (decodeForward_child hd).2
    rcases decodeForward_parent_cases hd with ⟨hp, hg⟩ |
      ⟨parent, pt, pp, A, hp, hpa, hpar, hng, hlt, hpt⟩
    · subst p
      rw [ho]
      exact decodeForward_genesis hs' x t B hb hg ht htime
    · subst p
      have hcp : Model.Obj.Contains o parent := by
        rw [ho]
        exact Model.Obj.Contains.step (by simp [forwardObj, Model.Obj.carried])
          (Model.Obj.Contains.refl _)
      have hpa' := ih A.slot (by omega) A rfl parent x pt pp hpa
        (fun C hC => hr C (hcp.trans hC))
      rw [ho]
      exact decodeForward_parent hs' x t pt B A parent pp hb hpa' hpar hng hlt hpt ht htime

/-- A durable-map update retains an old wrapper or records this exact acceptance.
This statement deliberately retains the accepted block, including its root; equality of
wire encodings alone does not recover that root. -/
theorem queueAccepted_wrapper_origin (st : State sp ro) (B : Blk sp)
    {root : Nat} {o : Wire sp.n}
    (h : (queueAccepted st B).wrappers root = some o) :
    st.wrappers root = some o ∨
      ∃ p, root = B.root ∧ o = forwardObj sp st.self st.now p B := by
  unfold queueAccepted at h
  split at h
  · exact Or.inl h
  · rename_i r hr
    generalize hp : (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent at h
    cases parent with
    | none => exact Or.inl h
    | some p =>
      change Function.update st.wrappers B.root
        (some (forwardObj sp st.self st.now p B)) root = some o at h
      simp only [Function.update_apply] at h
      split_ifs at h with hr
      · exact Or.inr ⟨p, hr, (Option.some.inj h).symm⟩
      · exact Or.inl h

/-- Queueing a successful cut preserves the acceptance clock and local identity. -/
private theorem queueAccepted_self_now (st : State sp ro) (B : Blk sp) :
    (queueAccepted st B).self = st.self ∧ (queueAccepted st B).now = st.now := by
  unfold queueAccepted
  split
  · exact ⟨rfl, rfl⟩
  · rename_i r hr
    generalize (if r = sp.genesisRoot then some none else
      (st.wrappers r).map some) = parent
    cases parent <;> exact ⟨rfl, rfl⟩

/-- Every new durable wrapper in a handler result names a successful acceptance cut of
that handler. The old-map alternative preserves history across unrelated handlers. -/
theorem apply_wrapper_origin (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    {root : Nat} {o : Wire sp.n} (h : (apply st result).wrappers root = some o) :
    st.wrappers root = some o ∨ ∃ B p,
      .fg (.block B true) ∈ result.2 ∧ root = B.root ∧
      o = forwardObj sp st.self st.now p B := by
  have aux : ∀ (cs : List (Cut (goldilocksNode sp ro))) (st : State sp ro),
      (cs.foldl (fun s c => match c with
        | .fg (.block B true) => queueAccepted s B
        | _ => s) st).wrappers root = some o →
      st.wrappers root = some o ∨ ∃ B p,
        .fg (.block B true) ∈ cs ∧ root = B.root ∧
        o = forwardObj sp st.self st.now p B := by
    intro cs
    induction cs with
    | nil => intro st h; exact Or.inl h
    | cons c cs ih =>
      intro st h
      cases c with
      | ac c =>
        rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
        · exact Or.inl h
        · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false =>
            rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
            · exact Or.inl h
            · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
          | true =>
            rcases ih (queueAccepted st B) h with h | ⟨C, p, hm, hr, ho⟩
            · rcases queueAccepted_wrapper_origin st B h with h | ⟨p, hr, ho⟩
              · exact Or.inl h
              · exact Or.inr ⟨B, p, List.mem_cons_self, hr, ho⟩
            · rw [(queueAccepted_self_now st B).1, (queueAccepted_self_now st B).2] at ho
              exact Or.inr ⟨C, p, List.mem_cons_of_mem _ hm, hr, ho⟩
        | _ =>
          rcases ih st h with h | ⟨B, p, hm, hr, ho⟩
          · exact Or.inl h
          · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, hr, ho⟩
  exact aux result.2 st h

/-- Fresh queue entries retain an indexed successful cut of the very handler that
created them, ready to be embedded into the event's cut prefix. -/
theorem apply_forward_origin_index (st : State sp ro)
    (result : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (q : Time × List (Wire sp.n)) (hq : q ∈ (apply st result).forwards) :
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ j : Nat,
      result.2[j]? = some (.fg (.block B true)) ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  rcases apply_forward_origin st result q hq with h | ⟨B, p, hm, he⟩
  · exact Or.inl h
  · obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hm
    exact Or.inr ⟨B, p, j, by simpa only [List.getElem?_eq_getElem hj] using congrArg some heq, he⟩

/-- A single delivered object can create a wrapper only through its actual canonical
handler. This keeps the handler state needed to locate the cut in recursive processing. -/
theorem processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    (q : Time × List (Wire sp.n)) (hq : q ∈ (processOne hs st o).forwards) :
    q ∈ st.forwards ∨ ∃ e B, ∃ p : Option (Wire sp.n),
      canonEvent sp ro hs o = some e ∧
      .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2 ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  have hrelay : ∀ (s : State sp ro) (c : Prop) [Decidable c],
      (relayIf s c o).forwards = s.forwards := by
    intro s c _
    unfold relayIf
    split <;> rfl
  rcases canonEvent_cases (ro := ro) hs o with he | ⟨B, he⟩ | ⟨v, he⟩ | ⟨a, he⟩
  · exact Or.inl (by simpa only [processOne, he] using hq)
  all_goals
    simp only [processOne, he, hrelay] at hq
    rcases apply_forward_origin _ _ q hq with h | ⟨C, p, hm, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, C, p, he, hm, hq⟩

/-- A successful canonical handler cut names the exact decoded input block. -/
private theorem accepted_canonEvent_block (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n)
    {e : Event (goldilocksNode sp ro)} {B : Blk sp}
    (he : canonEvent sp ro hs o = some e)
    (hb : .fg (.block B true) ∈ (exec proposer dg st.self st.node st.now e).2) :
    decodeBlock sp hs o = some B := by
  rcases canonEvent_cases (ro := ro) hs o with h | ⟨C, h⟩ | ⟨v, h⟩ | ⟨a, h⟩
  · rw [h] at he
    cases he
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp only [exec, onBlock] at hb
    split at hb
    · exact False.elim (List.not_mem_nil hb)
    · split at hb
      · simp at hb
      · simp only [List.mem_cons, List.not_mem_nil, Cut.fg.injEq,
          FGLabel.block.injEq, and_true, acCall, reduceCtorEq, or_false] at hb
        subst C
        exact decodeBlock_of_canonEvent h
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp [exec, onMessage, acCall] at hb
  · have heq := Option.some.inj (he.symm.trans h)
    subst e
    simp [exec, onAttestation] at hb

/-- A fresh queue entry from recursive receipt has a successful record in that exact
delivery traversal, including its node and clock. -/
theorem foldl_processOne_forward_origin (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (i : Nat) (q : Time × List (Wire sp.n)) :
    ∀ (os : List (Wire sp.n)) (st : State sp ro) (sub : Nat),
    q ∈ (os.foldl (processOne hs) st).forwards →
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), ∃ r,
      r ∈ deliverRecs proposer dg hs st.self st.now i os st.node sub ∧
      r.label = .fg (.block B true) ∧ r.node = st.self ∧ r.time = st.now ∧
      q = (st.now, p.toList ++ [blockObj sp B]) ∧
      decodeBlock sp hs (blockObj sp B) = some B ∧ blockObj sp B ∈ os := by
  intro os
  induction os with
  | nil => intro st sub h; exact Or.inl h
  | cons o os ih =>
    intro st sub h
    rcases ih (processOne hs st o) (sub + 1) h with h | ⟨B, p, r, hm, hl, hn, ht, hq, hd, ho⟩
    · rcases processOne_forward_origin proposer dg hs st o q h with h | ⟨e, B, p, he, hm, hq⟩
      · exact Or.inl h
      · obtain ⟨j, hj, hlabel⟩ := List.getElem_of_mem hm
        have hj' : j <
            (groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e).length := by
          rwa [length_groupRecs]
        obtain ⟨hn, ht, _, _, hl⟩ :=
          getElem_groupRecs proposer dg st.self st.node st.now (Nat.pair i sub) e j hj'
        have hd := accepted_canonEvent_block proposer dg hs st o he hm
        have hd' : decodeBlock sp hs (blockObj sp B) = some B := by
          rwa [eq_blockObj_of_decodeBlock hd] at hd
        refine Or.inr ⟨B, p, _, ?_, hl.trans hlabel, hn, ht, hq, hd', ?_⟩
        · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
          exact List.mem_append_left _ (List.getElem_mem hj')
        · rw [eq_blockObj_of_decodeBlock hd]
          exact List.mem_cons_self
    · simp only [processOne_self, processOne_now] at hm hn ht hq
      rw [processOne_node proposer dg] at hm
      refine Or.inr ⟨B, p, r, ?_, hl, hn, ht, hq, hd, List.mem_cons_of_mem _ ho⟩
      cases he : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he]
        simpa only [he] using hm
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
        exact List.mem_append_right _ (by simpa only [he] using hm)

end Consensus.Goldilocks.Simulation
