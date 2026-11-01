module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollection
public import AvailableChainPCSAProofs.Proofs.Shared.HeadSupport

public section

/-! Formation honest HEAD pools and the timely equivocation filter.
Shared authenticity and single emission give every honest seat one HEAD. -/
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The stored pool cannot contain two different HEADs from an honest seat. -/
theorem pcsa_formation_honest_head_clean_of_evidence (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (st : State p.n)
    (hEvidence : StoreEvidence (RootBlockInRun p c E rho) (HeadAuthentic E rho) st)
    (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (GridCO.votesAt st.base s) i = false := by
  have hw : ∀ o ∈ GridCO.votesAt st.base s,
      GridCO.headSeat? o = some i → ∃ r, o = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) := by
    intro o ho his
    have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp ho).2
    obtain ⟨auth, msg⟩ := o
    cases auth with
    | none => cases msg <;> cases hl
    | proposer r => cases msg <;> cases hl
    | seat r j =>
      cases msg with
      | proposal B raw sup => cases hl
      | head b =>
        change some r = some s at hl
        change some j = some i at his
        obtain rfl := Option.some.inj hl
        obtain rfl := Option.some.inj his
        exact ⟨b, rfl⟩
  apply Bool.eq_false_iff.mpr
  intro he
  have hc := Gen.AC.Root.cap_pair (n := p.n)
  obtain ⟨u, hu, v, hv, hne, hui, hvi⟩ := (hc _ i).mp he
  obtain ⟨r, rfl⟩ := hw u hu hui
  obtain ⟨r', rfl⟩ := hw v hv hvi
  rw [StoreEvidence_def] at hEvidence
  have ha := hEvidence.2.2 _ (List.mem_filter.mp hu).1
  have hb := hEvidence.2.2 _ (List.mem_filter.mp hv).1
  rw [HeadAuthentic_def] at ha hb
  obtain ⟨t, ht⟩ := ha s i r rfl hi
  obtain ⟨t', ht'⟩ := hb s i r' rfl hi
  have hr := (head_emission_unique p c m E rho hBase.valid.nodup _ s i r r' t t' ht ht').1
  exact hne (congrArg (fun x => (⟨.seat s i, .head x⟩ : GridCO.Wire p.n .root)) hr)

/-- Honest HEAD seats stay non-equivocating in every honest indexed pool. -/
theorem pcsa_formation_honest_head_clean (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (y : V) (hy : y ∈ rho.honest) (k : Nat) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (GridCO.votesAt (V2.D.Run.stateBefore E rho k y).st.base s) i = false := by
  exact pcsa_formation_honest_head_clean_of_evidence E rho hBase _
    (evidence_stateBefore E rho hBase.valid.toUnforgeableSignatures k y hy) s i hi

/-- Honest HEAD seats stay non-equivocating at each honest duty read. -/
theorem pcsa_formation_honest_head_clean_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (y : V) (hy : y ∈ rho.honest) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho y t = some nd) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (GridCO.votesAt nd.st.base s) i = false := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  apply pcsa_formation_honest_head_clean_of_evidence E rho hBase _ ?_ s i hi
  exact clock_evidence p _ _ _ t
    (evidence_stateBefore E rho hBase.valid.toUnforgeableSignatures k y hy)

/-- An early resolved HEAD from an honest seat passes the equivocation filter. -/
theorem pcsa_formation_timely_head_of_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (y : V) (hy : y ∈ rho.honest) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho y t = some nd) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.earlyVotes p.toParams.engine (actView nd.st) s)
    (hSeat : GridCO.headSeat? o = some i) : o ∈ timelyHeads p (actView nd.st) s := by
  have he := pcsa_formation_honest_head_clean_read E rho hBase y hy t nd hr s i hi
  delta timelyHeads
  apply List.mem_filter.mpr
  refine ⟨ho, ?_⟩
  rw [hSeat]
  change (!GridCO.equivocates (GridCO.votesAt nd.st.base s) i) = true
  rw [he]
  rfl

end AvailableChain.PCSA.Run
end
