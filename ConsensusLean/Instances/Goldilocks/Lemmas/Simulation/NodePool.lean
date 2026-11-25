module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers

public section

/-! # The node's pool across a tick and its own admissions

Processing attestations appends the new ones without repetition; the node's tick keeps the pool
(the AC calls write only `𝒜`, the record only `Λ`, and an own proposal carries only pool
attestations). Moved from `NodeOpLawsLawful` so that the replay laws can use it. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable {e : Encoding F E p hN hn A}

section Pool

variable {P : Params} {N : NodeAC P}

/-- Processing attestations appends the new ones, without repetition. -/
theorem foldl_onAttestation_new (l : List (FG.Att P.n)) (n : NodeState N) :
    ∃ d : List (FG.Att P.n), (∀ a ∈ d, a ∈ l) ∧ (∀ a ∈ d, a ∉ n.fg.atts) ∧ d.Nodup ∧
      l.foldl (fun n a => (Node.onAttestation n a).1) n =
        { n with fg := { n.fg with atts := n.fg.atts ++ d } } := by
  induction l generalizing n with
  | nil => exact ⟨[], by simp, by simp, List.nodup_nil, by simp⟩
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases ha : a ∈ n.fg.atts
    · have h : (Node.onAttestation n a).1 = n := by
        simp [Node.onAttestation, Store.onAttestation, ha]
      rw [h]
      obtain ⟨d, hdl, hd, hnd, he⟩ := ih n
      exact ⟨d, fun x hx => List.mem_cons_of_mem _ (hdl x hx), hd, hnd, he⟩
    · obtain ⟨d, hdl, hd, hnd, he⟩ := ih (Node.onAttestation n a).1
      have h : (Node.onAttestation n a).1 =
          { n with fg := { n.fg with atts := n.fg.atts ++ [a] } } := by
        simp [Node.onAttestation, Store.onAttestation, ha]
      rw [h] at hd he
      refine ⟨a :: d, fun x hx => ?_, fun b hb => ?_,
        List.nodup_cons.2 ⟨fun h' => hd a h' (by simp), hnd⟩, by rw [h, he]; simp⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hdl x hx)
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact fun h' => hd b hb (by simp [h'])

/-- An attestation in the pool's growth across processing a list is in the list. -/
theorem mem_growth (l : List (FG.Att P.n)) (n : NodeState N) {a : FG.Att P.n}
    (ha : a ∈ (l.foldl (fun n a => (Node.onAttestation n a).1) n).fg.atts.drop
      n.fg.atts.length) : a ∈ l := by
  obtain ⟨d, hdl, -, -, he⟩ := foldl_onAttestation_new l n
  rw [he] at ha
  simp only [List.drop_left] at ha
  exact hdl a ha

/-- Processing at most one attestation grows the pool by it exactly when it is new. -/
theorem growth_toList (o : Option (FG.Att P.n)) (n : NodeState N) :
    (o.toList.foldl (fun n a => (Node.onAttestation n a).1) n).fg.atts.drop n.fg.atts.length =
      o.toList.filter (fun a => a ∉ n.fg.atts) := by
  cases o with
  | none => simp
  | some a =>
    by_cases ha : a ∈ n.fg.atts <;>
      simp [Node.onAttestation, Store.onAttestation, ha]

/-- Processing fresh distinct attestations appends them. -/
theorem foldl_onAttestation_fresh (d : List (FG.Att P.n)) (n : NodeState N)
    (hd : ∀ a ∈ d, a ∉ n.fg.atts) (hnd : d.Nodup) :
    d.foldl (fun n a => (Node.onAttestation n a).1) n =
      { n with fg := { n.fg with atts := n.fg.atts ++ d } } := by
  induction d generalizing n with
  | nil => simp
  | cons a d ih =>
    have ha := hd a List.mem_cons_self
    have h : (Node.onAttestation n a).1 =
        { n with fg := { n.fg with atts := n.fg.atts ++ [a] } } := by
      simp [Node.onAttestation, Store.onAttestation, ha]
    rw [List.foldl_cons, h, ih]
    · simp
    · intro b hb hb'
      simp only [List.mem_append, List.mem_singleton] at hb'
      rcases hb' with hb' | rfl
      · exact hd b (List.mem_cons_of_mem _ hb) hb'
      · exact (List.nodup_cons.1 hnd).1 hb
    · exact (List.nodup_cons.1 hnd).2

/-- **Processing a list of attestations is processing the pool's growth**: `on_attestation`
appends an attestation exactly when it is new. -/
theorem foldl_onAttestation_growth (l : List (FG.Att P.n)) (n : NodeState N) :
    l.foldl (fun n a => (Node.onAttestation n a).1) n =
      ((l.foldl (fun n a => (Node.onAttestation n a).1) n).fg.atts.drop
        n.fg.atts.length).foldl (fun n a => (Node.onAttestation n a).1) n := by
  obtain ⟨d, -, hd, hnd, he⟩ := foldl_onAttestation_new l n
  rw [he]
  simp only [List.drop_left]
  exact (foldl_onAttestation_fresh d n hd hnd).symm

/-- Adding attestations already in the pool keeps the pool. -/
private theorem addAtts_atts_of_subset (st : Store P N.Payload) (l : List (FG.Att P.n))
    (h : ∀ a ∈ l, a ∈ st.atts) : (st.addAtts l).atts = st.atts := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts]
    have ha : st.onAttestation a = st := by simp [Store.onAttestation, h a List.mem_cons_self]
    rw [ha]
    exact ih st fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- A tick step keeps the pool: the AC calls write only `𝒜`, the record only `Λ`, and the own
proposal's block carries only attestations of the pool. -/
private theorem tickStep_atts (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) N.Payload)
    (self : Fin P.n) (st : NodeState N) (t : Time) (x : Nat) (s : TickStep) :
    (tickStep pr dg self st t x s).1.fg.atts = st.fg.atts := by
  cases s with
  | acTick => rfl
  | proposal =>
    simp only [tickStep]
    split
    · split
      · rfl
      · simp only [proposeBlock, Node.onBlock]
        split
        · rfl
        · split
          · rfl
          · rename_i fg' hb
            obtain ⟨-, σ', -, -, -, -, -, rfl⟩ := Store.onBlock_eq_some hb
            change (Store.addAtts _ _).atts = _
            rw [addAtts_atts_of_subset _ _ fun a ha => ?_]
            · exact (Store.updateFinality_spec _ _).2.2.1
            · rw [(Store.updateFinality_spec _ _).2.2.1]
              simp only [mkBlock, Store.proposalAttestations] at ha
              exact (List.mem_filter.1 ha).1
    · rfl
  | fgUpdate =>
    simp only [tickStep]
    split
    · rfl
    · simp only [Node.attest]; split <;> rfl

/-- The node's tick keeps the pool. -/
theorem exec_tick_atts (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) N.Payload)
    (self : Fin P.n) (st : NodeState N) (t : Time) (x : Nat) (b : Bool) :
    (exec pr dg self st t (.tick x b)).1.fg.atts = st.fg.atts := by
  simp only [exec, onTick, runSteps]
  generalize tickSteps b = l
  suffices ∀ acc : NodeState N × List (Cut N), acc.1.fg.atts = st.fg.atts →
      (l.foldl (fun acc step => let r := tickStep pr dg self acc.1 t x step
        (r.1, acc.2 ++ r.2)) acc).1.fg.atts = st.fg.atts from this _ rfl
  induction l with
  | nil => exact fun _ h => h
  | cons s l ih => exact fun acc h => ih _ ((tickStep_atts pr dg self _ t x s).trans h)

end Pool

/-- The node's tick keeps the pool. -/
theorem postTick_atts [DecidableEq V] (rho : Model.Run (compiled F) E) (v : V) (i : Nat)
    (t : Time) :
    (postTick e rho e.adapter.sign v i t).fg.atts =
      (e.adapter.node (stateAt e rho v i)).fg.atts := by
  rw [postTick_eq]
  split
  · exact exec_tick_atts _ _ _ _ _ _ _
  · rfl

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
