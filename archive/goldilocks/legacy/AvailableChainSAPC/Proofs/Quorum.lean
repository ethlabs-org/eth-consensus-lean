module
public import AvailableChainSAPC.Proofs.CertificateValidity
public import AvailableChainSAPC.Proofs.Cap

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A same-label set containing only faulty seats has at most `a` seats. -/
theorem faulty_seats_card_le {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (seats : Finset (Fin p.n))
    (h : ∀ i ∈ seats, rho.seatOf r i ∉ rho.honest) :
    seats.card ≤ (faulty rho).card := by
  apply Finset.card_le_card_of_injOn (rho.seatOf r)
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h i hi⟩
  · intro i _ j _ he
    exact (rho.seatOf r).injective he

theorem quorum_has_honest {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (seats : Finset (Fin p.n))
    (hq : pcQuorum p ≤ seats.card) (ha : (faulty rho).card < pcQuorum p) :
    ∃ i ∈ seats, rho.seatOf r i ∈ rho.honest := by
  by_contra hn
  push Not at hn
  have := faulty_seats_card_le p rho r seats hn
  omega

/-- Two q-seat sets intersect in an honest seat under the cap. This
uses one label and does not identify seats across labels. -/
theorem quorums_intersect_honest {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (rho : Run V (sapc p)) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (r : Slot) (left right : Finset (Fin p.n))
    (hl : pcQuorum p ≤ left.card) (hr : pcQuorum p ≤ right.card) :
    ∃ i, i ∈ left ∧ i ∈ right ∧ rho.seatOf r i ∈ rho.honest := by
  by_contra hn
  have hf : (left ∩ right).card ≤ (faulty rho).card := by
    apply faulty_seats_card_le p rho r
    intro i hi hh
    exact hn ⟨i, (Finset.mem_inter.mp hi).1, (Finset.mem_inter.mp hi).2, hh⟩
  have hu : (left ∪ right).card ≤ p.n := by
    simpa using Finset.card_le_univ (left ∪ right)
  have he := Finset.card_union_add_card_inter left right
  have hb := (cap_bounds p).2.2
  change (faulty rho).card ≤ pcFaultCap p at hcap
  omega

def pcSeats {n : Nat} (c : PC n) : Finset (Fin n) :=
  (c.witnesses.filterMap headSeat?).toFinset

theorem pcSeats_card (p : Params) {n : Nat} (c : PC n)
    (hw : pcWellFormed p c = true) : (pcSeats c).card = pcQuorum p := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  simpa only [pcSeats, List.card_toFinset, beq_iff_eq] using h

theorem pcSeats_witness (p : Params) {n : Nat} (c : PC n)
    (hw : pcWellFormed p c = true) (i : Fin n) (hi : i ∈ pcSeats c) :
    ∃ data, (⟨.seat (c.slot + 1) i, data⟩ : HeadWire n) ∈ c.witnesses ∧
      data.ack = some (c.slot, c.target) ∧ Block.Preceq c.target data.target := by
  obtain ⟨o, ho, hi⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hi)
  have h := pcWellFormed_witness p c hw o ho
  have ha := head_auth_of_label_seat o _ i h.1 hi
  exact ⟨o.payload, by simpa only [← ha] using ho, h.2.1, h.2.2.1⟩

/-- A PC has an honest original ack whenever `q>a`. The premise can
come from clean majority; this theorem does not require the cap. -/
theorem pc_honest_witness {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (rho : Run V (sapc p)) (st : State p.n) (c : PC p.n)
    (hv : pcValid p st c = true) (ha : (faulty rho).card < pcQuorum p) :
    ∃ i data, rho.seatOf (c.slot + 1) i ∈ rho.honest ∧
      (⟨.seat (c.slot + 1) i, data⟩ : HeadWire p.n) ∈ st.receivedHeads ∧
      data.ack = some (c.slot, c.target) ∧ Block.Preceq c.target data.target := by
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  obtain ⟨i, hi, hh⟩ := quorum_has_honest p rho (c.slot + 1) (pcSeats c)
    (le_of_eq (pcSeats_card p c hw).symm) ha
  obtain ⟨data, hm, hack, hext⟩ := pcSeats_witness p c hw i hi
  have harchive := (Bool.and_eq_true_iff.mp hv).2
  exact ⟨i, data, hh, of_decide_eq_true (List.all_eq_true.mp harchive _ hm), hack, hext⟩

/-- Conflicting equal-rank certificates cannot occur in authentic
archives under the cap, even before GST or at different readers. -/
theorem pc_same_slot_unique {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (left right : State p.n) (hl : ArchiveAuthenticated p E rho left)
    (hr : ArchiveAuthenticated p E rho right) (c d : PC p.n)
    (hc : pcValid p left c = true) (hd : pcValid p right d = true)
    (hslot : c.slot = d.slot) : c.target = d.target := by
  have hwc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hwd := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hd).1).1
  obtain ⟨i, hic, hid, honest⟩ := quorums_intersect_honest p rho hcap
    (c.slot + 1) (pcSeats c) (pcSeats d)
    (le_of_eq (pcSeats_card p c hwc).symm) (le_of_eq (pcSeats_card p d hwd).symm)
  obtain ⟨a, ha, hacka, _⟩ := pcSeats_witness p c hwc i hic
  obtain ⟨b, hb, hackb, _⟩ := pcSeats_witness p d hwd i hid
  have hac := of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 _ ha)
  have hbc := of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hd).2 _ hb)
  have he := authenticated_heads_equal p E rho hs left right hl hr (c.slot + 1) i a b
    hac (by simpa only [hslot] using hbc) honest
  have hack := hacka.symm.trans ((congrArg HeadData.ack he).trans hackb)
  exact (Prod.mk.inj (Option.some.inj hack)).2

theorem installedPC_same_slot_at_reads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (u v : V) (t t' : Time) (c d : PC p.n)
    (hc : (Run.readAt (sapc p) rho t u).bestPC = some c)
    (hd : (Run.readAt (sapc p) rho t' v).bestPC = some d)
    (hslot : c.slot = d.slot) : c.target = d.target :=
  pc_same_slot_unique p E rho hx.toScheduleWellFormed hcap _ _
    (archive_authenticated_at_read p E rho hx.toUnforgeableSignatures t u)
    (archive_authenticated_at_read p E rho hx.toUnforgeableSignatures t' v) c d
    (installedPC_valid_at_read p rho u t c hc) (installedPC_valid_at_read p rho v t' d hd) hslot

/-- An installed PC cannot precede the ack duty when `q>a`. -/
theorem installedPC_time_le_read {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : UnforgeableSignatures (sapc p) E rho)
    (ha : (faulty rho).card < pcQuorum p) (v : V) (t : Time) (c : PC p.n)
    (hc : (Run.readAt (sapc p) rho t v).bestPC = some c) : voteTime p (c.slot + 1) ≤ t := by
  obtain ⟨i, data, honest, hm, _, _⟩ := pc_honest_witness p rho _ c
    (installedPC_valid_at_read p rho v t c hc) ha
  exact archived_honest_head_time_le_read p E rho hx v t (c.slot + 1) i data hm honest

/-- Distinct raw seats in the exact-target N test. -/
def timelySeats (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block) :
    Finset (Fin n) :=
  ((st.receivedHeads.filter (fun o => headLabel? o == some r && o.payload.target == b &&
    stampHead st o < earlyTime p r)).filterMap headSeat?).toFinset

theorem timelySeats_quorum (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block)
    (h : timelyCandidate p st r b = true) : pcQuorum p ≤ (timelySeats p st r b).card := by
  have hcount := (Bool.and_eq_true_iff.mp h).2
  simpa only [timelySeats, List.card_toFinset, decide_eq_true_eq] using hcount

theorem timelySeats_witness (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block)
    (i : Fin n) (hi : i ∈ timelySeats p st r b) :
    ∃ data, (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads ∧ data.target = b ∧
      stampHead st ⟨.seat r i, data⟩ < earlyTime p r := by
  obtain ⟨o, ho, hi⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hi)
  obtain ⟨hm, hf⟩ := List.mem_filter.mp ho
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  have ha := head_auth_of_label_seat o r i hf.1.1 hi
  refine ⟨o.payload, ?_, hf.1.2, ?_⟩
  · simpa only [← ha] using hm
  · simpa only [← ha] using hf.2

/-- Exact-target N contains an honest preparation whenever `q>a`. -/
theorem timelyCandidate_honest_witness {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (st : State p.n) (r : Slot) (b : Block)
    (h : timelyCandidate p st r b = true) (ha : (faulty rho).card < pcQuorum p) :
    ∃ i data, rho.seatOf r i ∈ rho.honest ∧
      (⟨.seat r i, data⟩ : HeadWire p.n) ∈ st.receivedHeads ∧ data.target = b := by
  obtain ⟨i, hi, hh⟩ := quorum_has_honest p rho r (timelySeats p st r b)
    (timelySeats_quorum p st r b h) ha
  obtain ⟨data, hm, ht, _⟩ := timelySeats_witness p st r b i hi
  exact ⟨i, data, hh, hm, ht⟩

/-- The raw N test has at most one target at a label under the cap,
including across readers with different arrival orders and stamps. -/
theorem timelyCandidate_unique {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (left right : State p.n) (hl : ArchiveAuthenticated p E rho left)
    (hr : ArchiveAuthenticated p E rho right) (r : Slot) (a b : Block)
    (ha : timelyCandidate p left r a = true) (hb : timelyCandidate p right r b = true) :
    a = b := by
  obtain ⟨i, hil, hir, honest⟩ := quorums_intersect_honest p rho hcap r
    (timelySeats p left r a) (timelySeats p right r b)
    (timelySeats_quorum p left r a ha) (timelySeats_quorum p right r b hb)
  obtain ⟨da, hma, hta, _⟩ := timelySeats_witness p left r a i hil
  obtain ⟨db, hmb, htb, _⟩ := timelySeats_witness p right r b i hir
  have he := authenticated_heads_equal p E rho hs left right hl hr r i da db hma hmb honest
  exact hta.symm.trans ((congrArg HeadData.target he).trans htb)

end AvailableChain.SAPC
end
