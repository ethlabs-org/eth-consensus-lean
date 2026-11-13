module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core

public section

/-! # Received forwarding envelopes under growing faults

The growing-fault forms of the static receipt bounds, without a constant-fault premise. Each
signer is read honest at the time the bound needs it: unforgeability is applied at the delivery.

* `received_forward_stamp_le_at`: a forwarding envelope signed by a key honest at its delivery
  has a stamp no later than the delivery;
* `received_voteForward_processAt_at`, `held_voteForward_source_or_process_at`: a first-release
  vote envelope whose signer is honest at its stamp is processed by each receiver no earlier
  than the stamp. A receipt before the stamp would be at a time the signer is still honest, so
  unforgeability excludes it. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Authentication at the delivery and event order bound the stamp of a forwarding envelope by
its receipt time, when its signer is honest at the delivery, even when the envelope is nested
inside the delivered object. -/
theorem received_forward_stamp_le_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V) S.vote} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V) S.vote)} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  have hsign : rho.signerOf o = some (rho.key x) := by
    change o.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j, s, hj, hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hsign hx
  have hd' : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey (rho.key x), t, p, B) := by
    simpa only [Model.Run.ownKey, Equiv.symm_apply_apply] using hd
  have ht := released_forward_stamp S rho hn hv hs ho hd'
  rw [ht]
  obtain ⟨hi, hei⟩ := List.getElem?_eq_some_iff.mp he
  rcases hs with hs | ⟨receipt', hs⟩
  all_goals
    obtain ⟨hj', hej⟩ := List.getElem?_eq_some_iff.mp hs
    have horder := List.pairwise_iff_getElem.mp hv.sorted j i hj' hi hj
    rw [hej, hei] at horder
    rcases horder with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq

/-- A received first-release vote envelope whose signer is honest at its stamp is processed in
the delivery's group, no earlier than the stamp. -/
theorem received_voteForward_processAt_at (hv : rho.ExecutionValid)
    {source i : Nat} {x : Fin (Fintype.card V)} {v : V} {τ u : Time}
    {receipt : Wire (Fintype.card V) S.vote} {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m])) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTraceAt S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTraceAt S rho hn).time k = u ∧ τ ≤ u := by
  rw [simTraceAt_eq]
  have htime : τ ≤ u := by
    by_contra hlt
    have hxu : rho.key x ∉ rho.faultyAt u :=
      fun h => hx (rho.faultyAt_mono (le_of_lt (lt_of_not_ge hlt)) h)
    obtain ⟨j, s, hji, hsend, hrel⟩ := hv.unforgeable i v receipt u he _ hc (rho.key x) rfl hxu
    have hsj : source ≤ j := by
      by_contra h
      exact hfirst j (Nat.lt_of_not_ge h) hrel
    have hsi : source < i := hsj.trans_lt hji
    apply hlt
    rcases hs with hs | ⟨o, hs⟩ <;>
      rcases keyLe_of_lt S rho hv hs he hsi with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
    · exact h.le
    · exact h.le
  obtain ⟨k, hlo, hhi, hp, ht⟩ := received_vote_processAt S rho hn he
    (hc.trans (Model.Obj.Contains.step (List.mem_singleton_self _) (.refl _)))
  exact ⟨k, hlo, hhi, hp, ht, htime⟩

/-- Holdings of a first-release vote envelope whose signer is honest at its stamp either belong
to its source or give an actual recipient processing cut between the stamp and the holding time.
The source alternative is not itself a fresh-processing claim. -/
theorem held_voteForward_source_or_process_at (hv : rho.ExecutionValid)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ d : Time}
    {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∉ rho.faultyAt τ) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (hh : rho.log.Held rho.point (rho.key y)
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m]) d) :
    y = x ∨ ∃ k, (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      τ ≤ (simTraceAt S rho hn).time k ∧ (simTraceAt S rho hn).time k ≤ d := by
  obtain ⟨u, hud, hsend | hrecv, _⟩ := hh
  · obtain ⟨i, hi, hrel⟩ := hsend
    have hxy : x = rho.ownKey (rho.key y) := by
      rcases hi with he | ⟨o, he⟩
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.tick_auth _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.deliver_auth _ _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
    exact Or.inl (hxy.trans (rho.key.symm_apply_apply y)).symm
  · obtain ⟨i, hi⟩ := hrecv
    obtain ⟨k, _, _, hp, ht, hτ⟩ := received_voteForward_processAt_at S rho hn hv hx hs
      hfirst hi (.refl _)
    have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
    rw [hkey] at hp
    exact Or.inr ⟨k, hp, ht ▸ hτ, ht ▸ hud⟩

end Consensus.Goldilocks.Simulation

end
