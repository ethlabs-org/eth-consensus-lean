module
public import AvailableChainPCSAProofs.Proofs.Outage.ArmAcks
public import AvailableChainKitV2.DutyExecution

public section

/-! Time-bounded ack provenance (pcsa34-r4.3 §5.4.1 steps 1 and 4). Every PC
that an honest node reads by time `T` (held, frozen or carried) has an
honest ack emitted by `T`, so its slot's early time is at most `T`. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A pooled ack came from a delivery at a time at most `T`, directly or carried. -/
def AckOriginBy (rho : V2.D.Run V (pcsaWith m p c)) (T : Time) (a : AckWire p.n) : Prop :=
  ∃ x o t, t ≤ T ∧ V2.D.Run.processes rho x o t ∧
    (ofAck p a = o ∨ carriesS p o (ofAck p a))

omit [DecidableEq V] in
theorem AckOriginBy_def (rho : V2.D.Run V (pcsaWith m p c)) (T : Time) (a : AckWire p.n) :
    AckOriginBy rho T a = (∃ x o t, t ≤ T ∧ V2.D.Run.processes rho x o t ∧
      (ofAck p a = o ∨ carriesS p o (ofAck p a))) := by
  delta AckOriginBy
  rfl

/-- Every indexed store before index `j` has PCs and pool acks delivered by `T`
when every earlier event is at a time at most `T`. -/
theorem pcsa_certSafe_by (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (j : Nat) (v : V) (T : Time)
    (hT : ∀ k < j, ∀ e, rho.events[k]? = some e → e.time ≤ T) :
    CertSafe (AckOriginBy rho T) (V2.D.Run.stateBefore E rho j v).st := by
  have hz : CertSafe (AckOriginBy rho T) (initial p.n) := by
    dsimp only [initial]
    simp [CertSafe_def]
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => CertSafe (AckOriginBy rho T) nd.st) (Nat.zero_le j) v ?_ hz
  intro k e _ hkj he hn h
  cases e with
  | restart u t =>
    change u = v at hn
    subst u
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u t =>
    change u = v at hn
    subst u
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v t]
    exact clock_certSafe p _ _ t h
  | deliver u o t =>
    change u = v at hn
    subst u
    have htT : t ≤ T := hT k hkj _ he
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    apply process_certSafe p _ _ (toWire p o) h
    · intro s i r hd
      exact ⟨v, o, t, htT, ⟨k, he⟩, Or.inl (pcsa_outage_decoded_ack o s i r hd)⟩
    · intro s N hd a ha
      refine ⟨v, o, t, htT, ⟨k, he⟩, Or.inr ?_⟩
      unfold carriesS
      rw [pcsa_outage_decoded_proposal o s N hd]
      exact Or.inl (Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))))
    · intro d hd a ha
      refine ⟨v, o, t, htT, ⟨k, he⟩, Or.inr ?_⟩
      unfold carriesS
      rw [pcsa_outage_decoded_pc o d hd]
      exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq V] in
/-- Every event before a tick of time `t` has a time at most `t`. -/
theorem pcsa_events_before_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) :
    ∀ k' < k, ∀ e, rho.events[k']? = some e → e.time ≤ t := by
  intro k' hk' e he
  obtain ⟨hkl', hke'⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k' k hkl' hkl hk'
  rw [hke', hke] at hkey
  exact V2.D.Engine.time_le_of_key_le _ _ hkey

/-- Unforgeability turns an honest pooled ack delivered by `T` into an emission by `T`. -/
theorem pcsa_ackOriginBy_emits (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.UnforgeableSignatures E rho) (T : Time) (a : AckWire p.n) (s : Slot)
    (i : Fin p.n) (r : BlockId) (ha : AckOriginBy rho T a)
    (hd : a.decode? = some (s, i, r)) (hh : rho.seatOf (.base (.ack s)) i ∈ rho.honest) :
    ∃ t ≤ T, V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t := by
  have heq : ofAck p a = ackObj p s i r := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => dsimp only [AckWire.decode?] at hd; contradiction
    | proposer k => dsimp only [AckWire.decode?] at hd; contradiction
    | seat l j =>
      cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at hd <;> simp at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      rfl
  obtain ⟨x, o, t, htT, hp, ho⟩ := ha
  rw [heq] at ho
  rcases ho with ho | ho
  · subst o
    obtain ⟨t', ht', he⟩ := hv.unforgeable x _ t hp _ hh rfl
    exact ⟨t', ht'.trans htT, he⟩
  · obtain ⟨t', ht', he⟩ := hv.carried x o t hp _ ho _ hh rfl
    exact ⟨t', ht'.trans htT, he⟩

variable [Fintype V]

/-- A well-formed PC whose acks were delivered by `T` has an honest ack of
its slot, emitted by `T`, on a block with its target's root. -/
theorem pcsa_pc_honest_ack_by (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (T : Time) (d : PC p.n)
    (hw : d.wellFormed = true) (ho : ∀ a ∈ d.acks, AckOriginBy rho T a) :
    SA.earlyTime p.toParams d.slot ≤ T ∧
      ∃ y X, HonestAckAt p c E rho y d.slot X ∧ X.root = d.target.root := by
  obtain ⟨i, hh, a, ha, hd⟩ := pcsa_pc_honest_ack rho h.cstar hf d hw
  obtain ⟨t, htT, k, hk, he⟩ :=
    pcsa_ackOriginBy_emits E rho h.valid.toUnforgeableSignatures T a _ i _ (ho a ha) hd hh
  obtain ⟨ht, haw, X, hX, hread, -⟩ :=
    pcsa_ack_emission_read E rho h.valid.toScheduleWellFormed _ d.slot i _ t k hk he
  exact ⟨ht ▸ htT, _, X, ⟨hh, ht ▸ haw, hread⟩, hX⟩

omit [DecidableEq V] [Fintype V] in
/-- Every frozen or carried view source and every held PC of a store with
the Outage invariant and delivered-by-`T` certificates is well formed, has
acks delivered by `T`, and has a stored target. -/
theorem pcsa_source_facts (R : Block → Prop) (rho : V2.D.Run V (pcsaWith m p c))
    (T : Time) (st : State p.n) (hO : OutageStore R st)
    (hC : CertSafe (AckOriginBy rho T) st) (k s : Slot) (d : PC p.n)
    (hd : d ∈ st.pcs ∨ d ∈ pcSnapshotAt st k ∨ d ∈ carriedPCs st s) :
    d.wellFormed = true ∧ (∀ a ∈ d.acks, AckOriginBy rho T a) ∧ d.target ∈ st.base.blocks := by
  rw [CertSafe_def] at hC
  have held : d ∈ st.pcs → d.wellFormed = true ∧ (∀ a ∈ d.acks, AckOriginBy rho T a) ∧
      d.target ∈ st.base.blocks := fun hd =>
    ⟨(hC.2 d hd).1, (hC.2 d hd).2, hO.pcBlocks d hd⟩
  rcases hd with hd | hd | hd
  · exact held hd
  · apply held
    change d ∈ ((st.pcSnapshot.find? (fun row => row.1 == k)).map Prod.snd).getD [] at hd
    cases hf : st.pcSnapshot.find? (fun row => row.1 == k) with
    | none => rw [hf] at hd; simp at hd
    | some row =>
      rw [hf] at hd
      exact hO.snapSub row (List.mem_of_find?_eq_some hf) d hd
  · obtain ⟨hm, hv⟩ := List.mem_filter.mp hd
    have hv' := hv
    change (d.wellFormed && decide (d.target ∈ st.base.blocks) &&
      activeCompatible st d.target) = true at hv'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv'
    obtain ⟨⟨hw, hb⟩, -⟩ := hv'
    refine ⟨hw, ?_, hb⟩
    obtain ⟨o, ho, hdo⟩ := List.mem_filterMap.mp hm
    cases hdec : o.decode with
    | none => rw [hdec] at hdo; simp at hdo
    | some msg =>
      cases msg with
      | block s' N =>
        rw [hdec] at hdo
        dsimp only at hdo
        split at hdo
        · intro a ha
          have hpa : a ∈ N.pcAcks := by
            change a ∈ (N.pc.map PC.acks).getD []
            rw [hdo]
            exact ha
          have hdA : (a.decode?).isSome := by
            have hall := (Bool.and_eq_true_iff.mp hw).2
            have := List.all_eq_true.mp hall a ha
            cases hda : a.decode? with
            | none => rw [hda] at this; simp at this
            | some _ => rfl
          exact hC.1 a (hO.carried o ho s' N hdec a hpa hdA)
        · contradiction
      | vote _ _ _ => rw [hdec] at hdo; simp at hdo
      | row _ _ => rw [hdec] at hdo; simp at hdo
      | ack _ _ _ => rw [hdec] at hdo; simp at hdo
      | pc _ => rw [hdec] at hdo; simp at hdo

end AvailableChain.PCSA.Run
end
