module
public import AvailableChainGeneric.Statements.AC.Duty.Transfer

public section

namespace AvailableChain.Gen.AC.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
G1 composes the batch's raw coverage and support with the local gate
write. The prefix and level folds retain the proposed deadline lower bound. -/
theorem gate_of_coveringBatch_statement : GateOfCoveringBatchStatement := by
  rw [GateOfCoveringBatchStatement_def]
  intro V In P E rho mode A i s x D hwrite hcover hguard hne hmem hsupport hlevel
  have fold_preserves {α β : Type} (step : α → β → α) (Q : α → Prop)
      (hstep : ∀ st b, Q st → Q (step st b)) (xs : List β) (st : α) (h : Q st) :
      Q (xs.foldl step st) := by
    induction xs generalizing st with
    | nil => exact h
    | cons b xs ih => exact ih (step st b) (hstep st b h)
  have fold_installs {α β : Type} (step : α → β → α) (Q : α → Prop)
      (hstep : ∀ st b, Q st → Q (step st b)) (b : β) (hb : ∀ st, Q (step st b))
      (xs : List β) (hm : b ∈ xs) (st : α) : Q (xs.foldl step st) := by
    induction xs generalizing st with
    | nil => simp at hm
    | cons c xs ih =>
        rcases List.mem_cons.mp hm with he | hm
        · subst c
          exact fold_preserves step Q hstep xs (step st b) (hb st)
        · exact ih hm (step st c)
  -- All writes in this gate use the same proposed deadline. Thus neither
  -- uniqueness of old keys nor a bound on old deadlines is needed here.
  -- Source: spec:911–916; GridCO/Model/Protocol.lean:409–414.
  have write_installs {n : Nat} (st : GridCO.State n mode) (B : Block)
      (g : Nat) (d : Time) :
      ∃ deadline, d ≤ deadline ∧
        (B, g, deadline) ∈ (GridCO.writeObligation st B g d).obligations := by
    refine ⟨max ((GridCO.deadlineOf st B g).getD d) d, le_max_right _ _, ?_⟩
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have write_preserves {n : Nat} (st : GridCO.State n mode) (B C : Block)
      (g k : Nat) (d : Time)
      (h : ∃ deadline, d ≤ deadline ∧ (B, g, deadline) ∈ st.obligations) :
      ∃ deadline, d ≤ deadline ∧
        (B, g, deadline) ∈ (GridCO.writeObligation st C k d).obligations := by
    by_cases he : (B, g) = (C, k)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact write_installs st B g d
    · obtain ⟨deadline, hd, hr⟩ := h
      refine ⟨deadline, hd, List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hr, ?_⟩))⟩
      simpa only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
        Prod.mk.injEq, not_and_or] using he
  obtain ⟨C, hraw, hDC⟩ := hcover
  change Block.preceq D C = true at hDC
  have hg := hguard C hraw
  obtain ⟨hleases, hfast⟩ := hwrite C hraw hg
  have hprefix : D ∈ A.gatePrefixes i x s C := by
    rw [ACReads.gatePrefixes_def]
    exact List.mem_filter.mpr ⟨hmem, by
      simpa only [Bool.and_eq_true, bne_iff_ne] using And.intro hne hDC⟩
  refine ⟨C, hraw, hDC, hg, ?_, ?_⟩
  · rw [hfast, ACReads.gateFast_def]
    exact List.mem_filter.mpr ⟨hmem, by
      simpa only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] using
        And.intro (And.intro hne hDC) hsupport⟩
  · rw [hleases, ACReads.gateLeases_def]
    let d := SA.gateTime A.prm s + SA.lifetime A.prm
    let g := SA.releaseThreshold A.prm
    let Q := fun st : GridCO.State A.prm.n mode =>
      ∃ deadline, d ≤ deadline ∧ (D, g, deadline) ∈ st.obligations
    let step := fun (st : GridCO.State A.prm.n mode) b =>
      (A.gateLevels i x s b).foldl (fun acc level => GridCO.writeObligation acc b level d) st
    have hstep : ∀ st b, Q st → Q (step st b) := by
      intro st b h
      exact fold_preserves _ Q (fun acc level hp => write_preserves acc D b g level d hp)
        _ st h
    exact fold_installs step Q hstep D
      (fun st => fold_installs _ Q
        (fun acc level hp => write_preserves acc D D g level d hp)
        g (fun acc => write_installs acc D g d) _ hlevel st) _ hprefix _

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
G2 uses only the acceptance equation, absence of an old strict
descendant, normalization, and the post-gate lease invariant (IF.4). -/
theorem S_eq_of_exact_statement : SEqOfExactStatement := by
  rw [SEqOfExactStatement_def]
  intro V In P E rho mode A i s x X hwrite hraw hguard hold hanchor hbelow
  have hadvance : GridCO.advance (A.output i x) X = X := by
    unfold GridCO.advance
    split
    · exact hold ‹_›
    · rfl
  have hout : A.output (i + 1) x = X := by
    rw [hwrite hraw hguard, hadvance, normalizeOutput_def]
    exact ite_eq_left hanchor
  refine ⟨hout, ?_⟩
  intro lease hm hlive
  rw [← hout]
  exact hbelow lease hm hlive

variable {V In : Type} {P : ProtocolSpecD In} {E : Generic.Env V} {rho : D.Run V P}

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A covering batch gives gate service from its local count and walk facts. -/
theorem gate_of_coveringBatch {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s :
    Slot) (x : V) (D : Block)
    (hwrite : ∀ C, A.raw i s x = some C →
      (∀ lease ∈ (A.gateView i x s).obligations,
        Block.Compatible (Lease.target lease) C) →
      A.leases (i + 1) x = A.gateLeases i x s C ∧ A.fast i s x = A.gateFast i x s C)
    (hcover : ∃ C, A.raw i s x = some C ∧ Block.Preceq D C)
    (hguard : ∀ C, A.raw i s x = some C →
      ∀ lease ∈ (A.gateView i x s).obligations, Block.Compatible (Lease.target lease) C)
    (hne : D ≠ .genesis) (hmem : D ∈ (A.gateView i x s).blocks)
    (hsupport : SA.releaseThreshold A.prm ≤ GridCO.prefixSupport A.prm.engine (A.gateView i x s)
      s D)
    (hlevel : SA.releaseThreshold A.prm ∈ A.gateLevels i x s D) :
    GateService A i s x D :=
  gate_of_coveringBatch_statement A i s x D hwrite hcover hguard hne hmem hsupport hlevel

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
An accepted exact result replaces an old output that is not its strict
descendant. All live targets then precede that result. -/
theorem S_eq_of_exact {mode : GridCO.HeadMode} (A : ACReads E rho mode) (i : Nat) (s : Slot) (x :
    V) (X : Block)
    (hwrite : A.raw i s x = some X →
      (∀ lease ∈ (A.gateView i x s).obligations,
        Block.Compatible (Lease.target lease) X) →
      A.output (i + 1) x = normalizeOutput (A.anchor i x) (GridCO.advance (A.output i x) X))
    (hraw : A.raw i s x = some X)
    (hguard : ∀ lease ∈ (A.gateView i x s).obligations,
      Block.Compatible (Lease.target lease) X)
    (hold : Block.Preceq X (A.output i x) → A.output i x = X)
    (hanchor : Block.Preceq (A.anchor i x) X)
    (hbelow : ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
      Block.Preceq (Lease.target lease) (A.output (i + 1) x)) :
    A.output (i + 1) x = X ∧
      ∀ lease ∈ A.leases (i + 1) x, A.now (i + 1) x < Lease.deadline lease →
        Block.Preceq (Lease.target lease) X :=
  S_eq_of_exact_statement A i s x X hwrite hraw hguard hold hanchor hbelow

end AvailableChain.Gen.AC.Duty
