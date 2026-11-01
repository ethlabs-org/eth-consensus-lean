module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! Formation step 2 and the local ack rule (pcsa34-r4.3 §5.3).
OPEN: F1 and equal honest HEADs must supply timely, non-equivocating,
resolved seat witnesses at the post-clock early read. N-target uniqueness
uses QNHeadUnique through Shared.Count and local equivocation exclusion.
OPEN: derive all-awake-early A2 with whole-PC relay. The old ack-only
split in FormationAckCounterexample fails current F1. FormationView gives A2 under
frozen identity receipt and carried-PC presence. Root-form carriage closes
the old target-alias gap; no current C7 counterexample is known. -/

namespace AvailableChain.PCSA

/-- Each supplied exact HEAD seat contributes once to the N count. -/
theorem pcsa_formation_nCount_lower (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (P : Block) (Q : Finset (Fin p.n))
    (hHeads : ∀ i ∈ Q, ∃ o ∈ timelyHeads p v s,
      GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? v o = some P) :
    Q.card ≤ nCount p v s P := by
  classical
  rw [pcsa_nCount_card]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨o, ho, hs, hr⟩ := hHeads i hi
  exact (Gen.AC.Root.vote_pool_mem_seats _ i).mpr
    ⟨o, List.mem_filter.mpr ⟨ho, beq_iff_eq.mpr hr⟩, hs⟩

/-- A quorum of exact timely HEAD witnesses passes the N threshold. -/
theorem pcsa_formation_holdsN (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (P : Block) (Q : Finset (Fin p.n))
    (hQ : nQuorum p.n ≤ Q.card)
    (hHeads : ∀ i ∈ Q, ∃ o ∈ timelyHeads p v s,
      GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? v o = some P) :
    holdsN p v s P = true := by
  change decide (nQuorum p.n ≤ nCount p v s P) = true
  exact decide_eq_true (le_trans hQ (pcsa_formation_nCount_lower p v s P Q hHeads))

/-- A passing N count has an exact timely HEAD witness. -/
theorem pcsa_formation_n_witness (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (P : Block) (hN : holdsN p v s P = true) :
    ∃ o ∈ timelyHeads p v s, GridCO.resolvedHead? v o = some P := by
  have hn : nQuorum p.n ≤ nCount p v s P := of_decide_eq_true hN
  have hpos : 0 < nQuorum p.n := by
    rw [pcsa_nQuorum_eq_qN, Gen.Pure.qN_def]
    have := p.nPos
    omega
  let heads := (timelyHeads p v s).filter (fun o => GridCO.resolvedHead? v o == some P)
  have hne : heads ≠ [] := by
    intro he
    have hz : nCount p v s P = 0 := by
      change (GridCO.seats p.n heads).length = 0
      rw [he]
      rfl
    omega
  obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil heads hne
  exact ⟨o, (List.mem_filter.mp ho).1, beq_iff_eq.mp (List.mem_filter.mp ho).2⟩

/-- A unique passing slot-s N target is selected by the executable rule. -/
theorem pcsa_formation_nTarget (p : Params) (st : State p.n) (s : Slot) (P : Block)
    (hSlot : P.slot = s) (hN : holdsN p (actView st) s P = true)
    (hUnique : ∀ B, B ∈ (timelyHeads p (actView st) s).filterMap
      (GridCO.resolvedHead? (actView st)) → B.slot = s →
      holdsN p (actView st) s B = true → B = P) : nTarget? p st s = some P := by
  obtain ⟨o, ho, hr⟩ := pcsa_formation_n_witness p (actView st) s P hN
  let candidates := (timelyHeads p (actView st) s).filterMap
    (GridCO.resolvedHead? (actView st))
  have hm : P ∈ candidates := List.mem_filterMap.mpr ⟨o, ho, hr⟩
  have hp : (candidates.find? (fun B => B.slot == s && holdsN p (actView st) s B)).isSome =
      true := List.find?_isSome.mpr ⟨P, hm, by simp only [hSlot, BEq.rfl, hN, Bool.and_self]⟩
  change candidates.find? _ = some P
  cases he : candidates.find? (fun B => B.slot == s && holdsN p (actView st) s B) with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hp
  | some B =>
    have htest := List.find?_some
      (p := fun X : Block => X.slot == s && holdsN p (actView st) s X) he
    have hb := Bool.and_eq_true_iff.mp htest
    have heq := hUnique B (List.mem_of_find?_eq_some he) (beq_iff_eq.mp hb.1) hb.2
    exact congrArg some heq

/-- QNHeadUnique closes N selection from counted exact HEAD witnesses.
The excluded seat set and honest single-HEAD fact are explicit inputs. -/
theorem pcsa_formation_nTarget_of_single_heads (p : Params) (st : State p.n)
    (s : Slot) (P : Block) (F : Finset (Fin p.n))
    (hF : F.card < pcQuorum p.n) (hSlot : P.slot = s)
    (hN : holdsN p (actView st) s P = true)
    (hOne : ∀ i, i ∉ F → ∀ X Y,
      (∃ o ∈ timelyHeads p (actView st) s,
        GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView st) o = some X) →
      (∃ o ∈ timelyHeads p (actView st) s,
        GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView st) o = some Y) → X = Y) :
    nTarget? p st s = some P := by
  classical
  let sent := fun i B => ∃ o ∈ timelyHeads p (actView st) s,
    GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView st) o = some B
  let seats := fun B => (GridCO.seats p.n
    ((timelyHeads p (actView st) s).filter
      (fun o => GridCO.resolvedHead? (actView st) o == some B))).toFinset
  have hSent (B : Block) : ∀ i ∈ seats B, sent i B := by
    intro i hi
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ i).mp hi
    exact ⟨o, (List.mem_filter.mp ho).1, hs, beq_iff_eq.mp (List.mem_filter.mp ho).2⟩
  have hP : nQuorum p.n ≤ (seats P).card := by
    rw [← pcsa_nCount_card]
    exact of_decide_eq_true hN
  apply pcsa_formation_nTarget p st s P hSlot hN
  intro B _ _ hB
  have hCount : nQuorum p.n ≤ (seats B).card := by
    rw [← pcsa_nCount_card]
    exact of_decide_eq_true hB
  exact pcsa_n_target_unique sent F (seats B) (seats P) B P hOne hF
    (hSent B) (hSent P) hCount hP

/-- The timely filter retains only one exact object per seat. -/
theorem pcsa_formation_timely_seat_unique (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (i : Fin p.n) (o u : GridCO.Wire p.n .root)
    (ho : o ∈ timelyHeads p v s) (hu : u ∈ timelyHeads p v s)
    (hi : GridCO.headSeat? o = some i) (hj : GridCO.headSeat? u = some i) : o = u := by
  have hp : o ∈ GridCO.votesAt v s := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
  have hq : u ∈ GridCO.votesAt v s := (List.mem_filter.mp (List.mem_filter.mp hu).1).1
  have hn := (List.mem_filter.mp ho).2
  change (match GridCO.headSeat? o with
    | some i => !GridCO.equivocates (GridCO.votesAt v s) i
    | none => false) = true at hn
  rw [hi] at hn
  change (!GridCO.equivocates (GridCO.votesAt v s) i) = true at hn
  have hno : GridCO.equivocates (GridCO.votesAt v s) i = false := by
    simpa only [Bool.not_eq_true'] using hn
  by_contra hne
  have he := (Gen.AC.Root.cap_pair (GridCO.votesAt v s) i).mpr ⟨o, hp, u, hq, hne, hi, hj⟩
  rw [hno] at he
  cases he

/-- A passing own-slot N count fixes the N target without a run uniqueness input. -/
theorem pcsa_formation_nTarget_of_holdsN (p : Params) (st : State p.n) (s : Slot)
    (P : Block) (hSlot : P.slot = s) (hN : holdsN p (actView st) s P = true) :
    nTarget? p st s = some P := by
  have hF : (∅ : Finset (Fin p.n)).card < pcQuorum p.n := by
    change 0 < Gen.Pure.qA p.n
    rw [Gen.Pure.qA_def]
    have := p.nPos
    omega
  apply pcsa_formation_nTarget_of_single_heads p st s P ∅ hF hSlot hN
  intro i _ X Y hX hY
  obtain ⟨o, ho, hi, hr⟩ := hX
  obtain ⟨u, hu, hj, ht⟩ := hY
  have he := pcsa_formation_timely_seat_unique p (actView st) s i o u ho hu hi hj
  subst u
  exact Option.some.inj (hr.symm.trans ht)

/-- A view target below the proposal passes A2. -/
theorem pcsa_formation_viewOK (p : Params) (st : State p.n) (s : Slot) (P : Block)
    (hView : ∀ C, voterPC p st s = some C → Block.Preceq C.target P) :
    viewOK p st s P = true := by
  delta viewOK
  cases hv : voterPC p st s with
  | none => rfl
  | some C =>
    exact Bool.or_eq_true_iff.mpr (Or.inr (hView C hv))

/-- An N target that passes A2 is the local ack decision. -/
theorem pcsa_formation_ackFor (p : Params) (st : State p.n) (s : Slot) (P : Block)
    (hN : nTarget? p st s = some P) (hView : viewOK p st s P = true) :
    ackFor p st s = some P := by
  change (nTarget? p st s).filter (viewOK p st s) = some P
  rw [hN]
  exact Option.filter_eq_some_iff.mpr ⟨rfl, hView⟩

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- The post-clock N count and view prefix give an honest early ack. -/
theorem pcsa_formation_honestAck (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (_h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (nd : Node p)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.earlyTime p.toParams s) = true)
    (hRead : pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd)
    (hSlot : N.erase.slot = s) (hN : holdsN p (actView nd.st) s N.erase = true)
    (hView : ∀ C, voterPC p nd.st s = some C → Block.Preceq C.target N.erase) :
    HonestAckAt p c E rho y s N.erase := by
  rw [pcsa_HonestAckAt_def, pcsa_ackAt_def, hRead]
  exact ⟨hy, haw, congrArg some (pcsa_formation_ackFor p nd.st s N.erase
    (pcsa_formation_nTarget_of_holdsN p nd.st s N.erase hSlot hN)
    (pcsa_formation_viewOK p nd.st s N.erase hView))⟩

end AvailableChain.PCSA.Run
end
