module
public import AvailableChainSAPC.Proofs.Archive

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The shared engine emits a seat signature only at its duty, with the
single payload returned by `act`. This is independent of the protocol. -/
theorem emittedAt_seat_action {V : Type} [DecidableEq V] {n : Nat}
    (P : ProtocolSpec n) (E : Env V) (rho : Run V P) (index : Nat)
    (v : V) (t : Time) (r : P.Label) (i : Fin n) (payload : P.Payload)
    (ho : (⟨.seat r i, payload⟩ : P.Object) ∈ Run.emittedAt P E rho index v t) :
    t = P.actTime r ∧
      P.act (P.clock (Run.stateBefore P rho index v) t) r = some payload := by
  unfold Run.emittedAt at ho
  split at ho
  · simp only [List.mem_append] at ho
    rcases ho with (hact | hprop) | hgossip
    · obtain ⟨label, hl, ha⟩ := List.mem_filterMap.mp hact
      obtain ⟨msg, hm, he⟩ := Option.map_eq_some_iff.mp ha
      have heauth := congrArg Signed.auth he
      have hepayload := congrArg Signed.payload he
      have hlabel : label = r := (Auth.seat.inj heauth).1
      subst label
      change msg = payload at hepayload
      subst msg
      exact ⟨((P.duties_spec r t).mp hl).symm, hm⟩
    · obtain ⟨s, _, hp⟩ := List.mem_filterMap.mp hprop
      split at hp
      · obtain ⟨msg, _, he⟩ := Option.map_eq_some_iff.mp hp
        have heauth := congrArg Signed.auth he
        cases heauth
      · simp at hp
    · obtain ⟨msg, _, he⟩ := List.mem_map.mp hgossip
      have heauth := congrArg Signed.auth he
      cases heauth
  · simp at ho

/-- A valid schedule has one tick per node and time; there is one signed
payload per seat duty, including its ack field. -/
theorem emitted_seat_unique {V : Type} [DecidableEq V] {n : Nat}
    (P : ProtocolSpec n) (E : Env V) (rho : Run V P)
    (hs : ScheduleWellFormed E rho) (v : V) (r : P.Label) (i : Fin n)
    (a b : P.Payload) (ta tb : Time)
    (ha : Run.emits P E rho v ⟨.seat r i, a⟩ ta)
    (hb : Run.emits P E rho v ⟨.seat r i, b⟩ tb) : a = b := by
  obtain ⟨j, hj, hja⟩ := ha
  obtain ⟨k, hk, hkb⟩ := hb
  obtain ⟨hta, hacta⟩ := emittedAt_seat_action P E rho j v ta r i a hja
  obtain ⟨htb, hactb⟩ := emittedAt_seat_action P E rho k v tb r i b hkb
  subst ta; subst tb
  have hjlen := (List.getElem?_eq_some_iff.mp hj).1
  have hjk : j = k := (List.Nodup.getElem?_inj hjlen hs.nodup).mp (hj.trans hk.symm)
  subst k
  exact Option.some.inj (hacta.symm.trans hactb)

private theorem fold_archive_origin {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (w : World V (sapc p))
    (v : V) (h : HeadWire p.n)
    (hh : h ∈ ((events.foldl World.step w) v).receivedHeads) :
    h ∈ (w v).receivedHeads ∨ ∃ parent t, Event.deliver v parent t ∈ events ∧
      (parent = fromHead h ∨ carries parent (fromHead h)) := by
  induction events generalizing w with
  | nil => exact Or.inl hh
  | cons e events ih =>
      rcases ih _ hh with hfirst | ⟨parent, t, hm, hc⟩
      · cases e with
        | tick u t =>
            by_cases hv : v = u
            · subst v
              simp only [World.step, Function.update_self] at hfirst
              exact Or.inl ((clock_archive p (w u) t) ▸ hfirst)
            · exact Or.inl (by simpa [World.step, hv] using hfirst)
        | deliver u parent t =>
            by_cases hv : v = u
            · subst v
              have hm : h ∈ (process p (w u) parent).receivedHeads := by
                simp only [World.step, Function.update_self] at hfirst
                simpa [sapc] using hfirst
              rcases process_archive_origin p (w u) parent h hm with hold | hc
              · exact Or.inl hold
              · exact Or.inr ⟨parent, t, by simp, hc⟩
            · exact Or.inl (by simpa [World.step, hv] using hfirst)
      · exact Or.inr ⟨parent, t, List.mem_cons_of_mem _ hm, hc⟩

/-- Every complete archived signature has a direct or carried receipt.
No finite age window or path-resolution premise is needed. -/
theorem archive_origin_at_read {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (t : Time) (h : HeadWire p.n)
    (hh : h ∈ (Run.readAt (sapc p) rho t v).receivedHeads) :
    ∃ parent receipt, Run.processes (sapc p) rho v parent receipt ∧
      (parent = fromHead h ∨ carries parent (fromHead h)) := by
  rcases fold_archive_origin p _ World.init v h hh with hold | ⟨parent, time, hm, hc⟩
  · simp [World.init, sapc, initial] at hold
  · obtain ⟨he, _⟩ := List.mem_filter.mp hm
    obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp he
    exact ⟨parent, time, ⟨index, hi⟩, hc⟩

/-- Honest complete HEADs in the archive retain their engine signatures. -/
theorem archived_honest_head_emitted {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho)
    (v : V) (t : Time) (r : Slot) (i : Fin p.n) (data : HeadData)
    (hh : (⟨.seat r i, data⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho t v).receivedHeads)
    (honest : rho.seatOf r i ∈ rho.honest) :
    ∃ time, Run.emits (sapc p) E rho (rho.seatOf r i)
      (fromHead ⟨.seat r i, data⟩) time := by
  obtain ⟨parent, time, hm, hc⟩ := archive_origin_at_read p rho v t _ hh
  rcases hc with rfl | hc
  · obtain ⟨t', _, he⟩ := hs.unforgeable v _ time hm _ honest rfl
    exact ⟨t', he⟩
  · obtain ⟨t', _, he⟩ := hs.carried v _ time hm _ hc _ honest rfl
    exact ⟨t', he⟩

theorem archived_honest_heads_equal {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (v : V) (t : Time) (r : Slot) (i : Fin p.n) (a b : HeadData)
    (ha : (⟨.seat r i, a⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho t v).receivedHeads)
    (hb : (⟨.seat r i, b⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho t v).receivedHeads)
    (hh : rho.seatOf r i ∈ rho.honest) : a = b := by
  obtain ⟨ta, hea⟩ := archived_honest_head_emitted p E rho
    hx.toUnforgeableSignatures v t r i a ha hh
  obtain ⟨tb, heb⟩ := archived_honest_head_emitted p E rho
    hx.toUnforgeableSignatures v t r i b hb hh
  have he := emitted_seat_unique (sapc p) E rho hx.toScheduleWellFormed
    (rho.seatOf r i) r i (.head a) (.head b) ta tb hea heb
  exact Msg.head.inj he

/-- Authentication at an arbitrary engine input. The signature includes
both the target and the ack, and its time is the exact seat duty. -/
def ArchiveAuthenticated {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (st : State p.n) : Prop :=
  ∀ r i data, (⟨.seat r i, data⟩ : HeadWire p.n) ∈ st.receivedHeads →
    rho.seatOf r i ∈ rho.honest →
    Run.emits (sapc p) E rho (rho.seatOf r i)
      (fromHead ⟨.seat r i, data⟩) (voteTime p r)

/-- Every selected event list has authentic archived HEADs. This covers
index inputs, strict-time inputs, public reads, and the complete run. -/
theorem archive_authenticated_at_fold {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho)
    (events : List (Event V (sapc p).Object)) (hsub : events ⊆ rho.events) (v : V) :
    ArchiveAuthenticated p E rho ((events.foldl World.step World.init) v) := by
  intro r i data hm honest
  rcases fold_archive_origin p events World.init v _ hm with hinit | ⟨parent, t, he, hc⟩
  · simp [World.init, sapc, initial] at hinit
  · have hproc : Run.processes (sapc p) rho v parent t :=
      List.mem_iff_getElem?.mp (hsub he)
    have hem : ∃ t', Run.emits (sapc p) E rho (rho.seatOf r i)
        (fromHead ⟨.seat r i, data⟩) t' := by
      rcases hc with rfl | hc
      · obtain ⟨t', _, hem⟩ := hs.unforgeable v _ t hproc _ honest rfl
        exact ⟨t', hem⟩
      · obtain ⟨t', _, hem⟩ := hs.carried v _ t hproc _ hc _ honest rfl
        exact ⟨t', hem⟩
    obtain ⟨t', hem⟩ := hem
    obtain ⟨index, hi, ho⟩ := hem
    have ht := (emittedAt_seat_action (sapc p) E rho index _ t' r i (.head data) ho).1
    change t' = voteTime p r at ht
    rw [← ht]
    exact ⟨index, hi, ho⟩

theorem archive_authenticated_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho) (index : Nat) (v : V) :
    ArchiveAuthenticated p E rho (Run.stateBefore (sapc p) rho index v) :=
  archive_authenticated_at_fold p E rho hs _ (List.take_subset _ _) v

theorem archive_authenticated_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho) (t : Time) (v : V) :
    ArchiveAuthenticated p E rho (Run.stateBeforeTime (sapc p) rho t v) :=
  archive_authenticated_at_fold p E rho hs _ (fun _ h => (List.mem_filter.mp h).1) v

theorem archive_authenticated_at_read {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho) (t : Time) (v : V) :
    ArchiveAuthenticated p E rho (Run.readAt (sapc p) rho t v) :=
  archive_authenticated_at_fold p E rho hs _ (fun _ h => (List.mem_filter.mp h).1) v

/-- Compare complete honest payloads across distinct readers and inputs. -/
theorem authenticated_heads_equal {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (left right : State p.n) (hl : ArchiveAuthenticated p E rho left)
    (hr : ArchiveAuthenticated p E rho right) (r : Slot) (i : Fin p.n) (a b : HeadData)
    (ha : (⟨.seat r i, a⟩ : HeadWire p.n) ∈ left.receivedHeads)
    (hb : (⟨.seat r i, b⟩ : HeadWire p.n) ∈ right.receivedHeads)
    (honest : rho.seatOf r i ∈ rho.honest) : a = b :=
  Msg.head.inj (emitted_seat_unique (sapc p) E rho hs _ r i (.head a) (.head b)
    (voteTime p r) (voteTime p r) (hl r i a ha honest) (hr r i b hb honest))

/-- An honest archived signature cannot occur before its exact duty. -/
theorem archived_honest_head_time_le_read {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hs : UnforgeableSignatures (sapc p) E rho)
    (v : V) (t : Time) (r : Slot) (i : Fin p.n) (data : HeadData)
    (hh : (⟨.seat r i, data⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho t v).receivedHeads)
    (honest : rho.seatOf r i ∈ rho.honest) : voteTime p r ≤ t := by
  rcases fold_archive_origin p _ World.init v _ hh with hinit | ⟨parent, receipt, hm, hc⟩
  · simp [World.init, sapc, initial] at hinit
  · obtain ⟨he, htime⟩ := List.mem_filter.mp hm
    have hproc : Run.processes (sapc p) rho v parent receipt := List.mem_iff_getElem?.mp he
    have hem : ∃ time, time ≤ receipt ∧ Run.emits (sapc p) E rho (rho.seatOf r i)
        (fromHead ⟨.seat r i, data⟩) time := by
      rcases hc with rfl | hc
      · exact hs.unforgeable v _ receipt hproc _ honest rfl
      · exact hs.carried v _ receipt hproc _ hc _ honest rfl
    obtain ⟨time, hle, index, _, ho⟩ := hem
    have ht := (emittedAt_seat_action (sapc p) E rho index _ time r i (.head data) ho).1
    change time = voteTime p r at ht
    rw [← ht]
    exact hle.trans (of_decide_eq_true htime)

end AvailableChain.SAPC
end
