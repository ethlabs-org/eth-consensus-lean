module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Held
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events

public section

/-! # Acceptance of a received forwarding chain under growing faults

The growing-fault forms of `received_forward_accepted_before`, without a constant-fault premise.
The recipient is honest at a time `t₀` no earlier than every cut before its reading cut `j` (it
may be compromised by the time of cut `j` itself); ancestry is read inside the blocks held while
honest. The signer is honest either at its stamp, with the envelope its genuine release there
(`received_forward_accepted_before_of_released_at`), or at the delivery
(`received_forward_accepted_before_at`, which reduces to the first by unforgeability).

Every wrapper nested in a genuine release is in the signer's view after it, hence was itself
released, and accepted, by the signer while honest (`released_forward_source_acceptance_at`).
The parent-first traversal is `forward_receipt_held_at`, with the receiver read on its prefix
through the later of `t₀` and the delivery. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Events in list order have nondecreasing times. -/
private theorem sendsAt_time_le (hv : rho.ExecutionValid) {j j' : Nat} {w w' : V} {s s' : Time}
    (hs : rho.SendsAt w j s) (hs' : rho.SendsAt w' j' s') (hjj : j ≤ j') : s ≤ s' := by
  rcases hjj.lt_or_eq with hlt | rfl
  · rcases hs with hs | ⟨_, hs⟩ <;> rcases hs' with hs' | ⟨_, hs'⟩ <;>
      rcases keyLe_of_lt S rho hv hs hs' hlt with h | ⟨h, _⟩ <;> first | exact h.le
  · rcases hs with hs | ⟨_, hs⟩ <;> rcases hs' with hs' | ⟨_, hs'⟩ <;>
      rw [hs] at hs' <;> cases hs' <;> exact le_rfl

/-- **Wrappers in a genuine release.** Every forwarding wrapper signed by `x` and contained in an
object that `x` released at its event `j₀` at `t`, while honest at `t`, was itself accepted by
`x` before the end of `j₀`, at its stamp `tq ≤ t`. -/
theorem released_forward_source_acceptance_at (hv : rho.ExecutionValid)
    {j₀ : Nat} {x : Fin (Fintype.card V)} {t : Time} {o q : Wire (Fintype.card V)}
    (hs : rho.SendsAt (rho.key x) j₀ t) (ho : o ∈ rho.releasesAt j₀)
    (hx : rho.key x ∉ rho.faultyAt t) (hq : Model.Obj.Contains o q)
    {tq : Time} {pq : Option (Wire (Fintype.card V))} {C : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash q) q =
      some (x, tq, pq, C)) :
    ∃ k < cutMap S rho hn (j₀ + 1), (simTraceAt S rho hn).AcceptAt x k C ∧
      (simTraceAt S rho hn).time k = tq ∧ tq ≤ t := by
  have hj₀ : j₀ < rho.events.length := by
    rcases hs with hs | ⟨_, hs⟩ <;> exact (List.getElem?_eq_some_iff.mp hs).1
  have hct : rho.cutTime (j₀ + 1) = t := by
    rcases hs with hs | ⟨_, hs⟩ <;> simp [Model.Run.cutTime, hs, Model.Event.time]
  have hview : o ∈ rho.ViewIdx (rho.key x) (j₀ + 1) :=
    rho.mem_viewIdx_iff.mpr ⟨j₀, o, Nat.lt_succ_self _, Or.inl ⟨t, hs, ho⟩, .refl _⟩
  have hxh : x ∈ honestKeysAt S rho (rho.cutTime (j₀ + 1)) := by
    rw [mem_honestKeysAt_iff, hct]
    exact fun h => hx (rho.faultyAt_mono (min_le_left _ _) h)
  have hsign : rho.signerOf q = some (rho.key x) := by
    change q.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j, hj, s, hsj, hqj⟩ := contained_view_released_at S rho hv hj₀ hview hq hxh hsign
  have hkx : rho.ownKey (rho.key x) = x := rho.key.symm_apply_apply _
  have hd' := hd
  rw [← hkx] at hd'
  have hst := released_forward_stamp S rho hn hv hsj hqj hd'
  have hacc : ∃ k < cutMap S rho hn (j + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key x)) k C ∧
      (simTrace S rho hn).time k = tq := by
    rcases hsj with hsj | ⟨receipt', hsj⟩
    · exact tick_released_forward_acceptance S rho hn hv hsj hqj hd'
    · exact delivery_released_forward_acceptance S rho hn hv hsj hqj hd'
  obtain ⟨k, hk, ha, ht⟩ := hacc
  rw [simTraceAt_eq]
  exact ⟨k, hk.trans_le (cutMap_mono S rho hn (by omega)), hkx ▸ ha, ht,
    hst ▸ sendsAt_time_le S rho hv hsj hs (by omega)⟩

/-- A receipt before a strict deadline, of a forwarding envelope that its signer released while
honest at its stamp `t`, gives an acceptance before that deadline when the recipient's finalized
tip at a later reading cut is below the forwarded block. The signer may be compromised before the
delivery. -/
theorem received_forward_accepted_before_of_released_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : v ∉ rho.faultyAt t₀)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt t)
    (hrel : rho.releases (rho.key x) o t)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.F B)
    (hu : u < deadline) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTraceAt S rho hn).time k ≤ u ∧ (simTraceAt S rho hn).time k < deadline := by
  obtain ⟨j₀, hs₀, ho₀⟩ := hrel
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hvu : v ∉ rho.faultyAt u := hv.honest_only _ (List.mem_of_getElem? he)
  obtain ⟨hu0, huh⟩ := hv.in_horizon _ (List.mem_of_getElem? he)
  have hkx : rho.ownKey (rho.key x) = x := rho.key.symm_apply_apply _
  have hstamp : ∀ {j s}, rho.SendsAt (rho.key x) j s → o ∈ rho.releasesAt j → t = s :=
    fun hsj hoj => released_forward_stamp S rho hn hv hsj hoj (by rw [hkx]; exact hd)
  -- The stamp is no later than the receipt: otherwise the signer is honest at the receipt.
  have htu : t ≤ u := by
    by_contra hlt
    have hxu : rho.key x ∉ rho.faultyAt u :=
      fun h => hx (rho.faultyAt_mono (le_of_lt (lt_of_not_ge hlt)) h)
    have hsign : rho.signerOf o = some (rho.key x) := by
      change o.signer?.map rho.key = some (rho.key x)
      rw [decodeForward_signer hd]
      rfl
    obtain ⟨j, s, hj, hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hsign hxu
    exact hlt (hstamp hs ho ▸ sendsAt_time_le S rho hv hs (Or.inr ⟨receipt, he⟩) hj.le)
  -- The receiver is read on its prefix through the later of `t₀` and the receipt.
  set D := max t₀ u
  have hD : 0 ≤ D := hu0.trans (le_max_right _ _)
  have hyD : rho.ownKey v ∈ honestKeysAt S rho D := by
    have hu' := honest_ownKey_at S rho hvu huh
    rcases le_total t₀ u with h | h
    · rwa [show D = u from max_eq_right h]
    · rw [show D = t₀ from max_eq_left h, mem_honestKeysAt_iff]
      simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using
        fun hf => hy (rho.faultyAt_mono (min_le_left _ _) hf)
  have hbj : ∀ k < j, (simTraceAt S rho hn).time k ≤ D :=
    fun k hk => (hj₀ k hk).trans (le_max_left _ _)
  have hbe : ∀ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).time k ≤ D :=
    fun k hk => hbj k (by omega)
  have hFB' : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn (i + 1))).fg.F B := by
    have hmono := Healing.run_F_mono (hrun.upTo hD).toLocalRun hyD hij
    rw [Trace.upTo_state _ _ hbe, Trace.upTo_state _ _ hbj] at hmono
    exact (hmono.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hD)).trans hFB
  -- Split the delivery at the received envelope.
  have hseq := simTraceAt_deliver S rho hn hv he
  obtain ⟨pre, post, hparts⟩ := contained_parts_infix hc
  change DeliverSeq (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)
    _ _ _ _ _ _ receipt.parts _ _ at hseq
  rw [hparts, List.append_assoc] at hseq
  obtain ⟨r, _, htail⟩ := deliverSeq_append_split _ _ hseq
  obtain ⟨e, hsub, hpost⟩ := deliverSeq_append_split _ _ htail
  have hej := (deliverSeq_cover hpost).1
  have hd' := (decodeForward_receipt_iff S rho hn hc).mpr hd
  have hsource : ∀ q tq pq C, Model.Obj.Contains o q →
      decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt) q =
        some (x, tq, pq, C) →
      ∃ k, (simTraceAt S rho hn).AcceptAt x k C ∧
        x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) := by
    intro q tq pq C hq hdec
    obtain ⟨k, _, ha, hk, htq⟩ := released_forward_source_acceptance_at S rho hn hv hs₀ ho₀ hx hq
      ((decodeForward_receipt_iff S rho hn (hc.trans hq)).mp hdec)
    refine ⟨k, ha, ?_⟩
    rw [mem_honestKeysAt_iff, hk]
    exact fun h => hx (rho.faultyAt_mono ((min_le_left _ _).trans htq) h)
  have hheld := forward_receipt_held_at hrun hnc hD hbe hyD hFB' B o t p r e hd' hsub hej htu
    .refl hsource
  rw [← Trace.upTo_state _ _ fun k hk => hbe k (by omega)] at hheld
  obtain ⟨k, hk, ha⟩ : ∃ k < cutMap S rho hn (i + 1),
      (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B := by
    rcases Compose.tree_cases (hrun.upTo hD).toLocalRun hyD hheld with hgen | ⟨k, hk, ha⟩
    · have hp := (decodeBlock_wire (decodeForward_child hd).1).2.1
      exact False.elim (hp (hgen ▸ rfl))
    · exact ⟨k, hk.trans_le hej, ((RunTrace.upTo_acceptAt _).mp ha).2⟩
  rw [simTraceAt_eq] at ha ⊢
  obtain ⟨r', q, ev, _, hq, hstart, _, _, _, ht, _⟩ :=
    simTrace_cut S rho hn (by rw [ha.2]; simp)
  have hqi : q ≤ i := by
    by_contra h
    have hm : cutMap S rho hn (i + 1) ≤ cutMap S rho hn q :=
      cutMap_mono S rho hn (by omega)
    exact (not_lt_of_ge (hm.trans hstart)) hk
  have htime : (simTrace S rho hn).time k ≤ u := by
    rw [ht]
    rcases hqi.lt_or_eq with hlt | rfl
    · rcases keyLe_of_lt S rho hv hq he hlt with h | h
      · exact h.le
      · exact h.1.le
    · rw [he] at hq
      cases hq
      exact le_rfl
  exact ⟨k, hk, ha, htime, htime.trans_lt hu⟩

/-- The same acceptance when the signer is honest at the delivery: unforgeability then makes the
envelope its genuine release at its stamp. -/
theorem received_forward_accepted_before_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {i j : Nat} {v : V} {receipt o : Wire (Fintype.card V)}
    {x : Fin (Fintype.card V)} {u t deadline : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u)) {t₀ : Time}
    (hj₀ : ∀ k < j, (simTraceAt S rho hn).time k ≤ t₀) (hy : v ∉ rho.faultyAt t₀)
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hij : cutMap S rho hn (i + 1) ≤ j)
    (hFB : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).state (rho.ownKey v) j).fg.F B)
    (hu : u < deadline) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTraceAt S rho hn).time k ≤ u ∧ (simTraceAt S rho hn).time k < deadline := by
  have hsign : rho.signerOf o = some (rho.key x) := by
    change o.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j', s, hj', hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hsign hx
  have hkx : rho.ownKey (rho.key x) = x := rho.key.symm_apply_apply _
  have hts : t = s := released_forward_stamp S rho hn hv hs ho (by rw [hkx]; exact hd)
  subst hts
  have hxt : rho.key x ∉ rho.faultyAt t := fun h =>
    hx (rho.faultyAt_mono (sendsAt_time_le S rho hv hs (Or.inr ⟨receipt, he⟩) hj'.le) h)
  exact received_forward_accepted_before_of_released_at S rho hn hv hnc he hj₀ hy hc hxt
    ⟨j', hs, ho⟩ hd hij hFB hu

end Consensus.Goldilocks.Simulation

end
