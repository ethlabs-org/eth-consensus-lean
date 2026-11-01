module
public import AvailableChainGeneric.Statements.Pure.Schedule

@[expose] public section

namespace AvailableChain.Gen.Pure.SlotGrid

/-- t gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def t (Δ : Time) (s : Nat) : Time := slotLen Δ * (s : Time)
/-- v gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def v (Δ : Time) (s : Nat) : Time := t Δ s + Δ
/-- q gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
def q (Δ : Time) (s : Nat) : Time := t Δ s + 5 * Δ
/-- e gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def e (Δ : Time) (s : Nat) : Time := t Δ s + 2 * Δ
/-- z gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def z (Δ : Time) (s : Nat) : Time := t Δ s + 3 * Δ
/-- d gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def d (Δ : Time) (s : Nat) : Time := t Δ s + 6 * Δ
/-- P gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def P (Δ : Time) (R : Nat) : Time := 4 * (R : Time) * Δ
/-- L gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
def L (Δ : Time) (k : Nat) : Time := (4 * (k : Time) - 1) * Δ
/-- T gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def T (Δ : Time) (R r : Nat) : Time := t Δ (r * R)
/-- a gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def a (Δ : Time) (R r : Nat) : Time := d Δ (r * R)

/-- t_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem t_def (Δ : Time) (s : Nat) :
    t Δ s = slotLen Δ * (s : Time) := by rfl
/-- v_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem v_def (Δ : Time) (s : Nat) : v Δ s = t Δ s + Δ := by rfl
/-- q_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem q_def (Δ : Time) (s : Nat) : q Δ s = t Δ s + 5 * Δ := by rfl
/-- e_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem e_def (Δ : Time) (s : Nat) : e Δ s = t Δ s + 2 * Δ := by rfl
/-- z_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem z_def (Δ : Time) (s : Nat) : z Δ s = t Δ s + 3 * Δ := by rfl
/-- d_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem d_def (Δ : Time) (s : Nat) : d Δ s = t Δ s + 6 * Δ := by rfl
/-- P_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem P_def (Δ : Time) (R : Nat) :
    P Δ R = 4 * (R : Time) * Δ := by rfl
/-- L_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem L_def (Δ : Time) (k : Nat) :
    L Δ k = (4 * (k : Time) - 1) * Δ := by rfl
/-- T_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem T_def (Δ : Time) (R r : Nat) : T Δ R r = t Δ (r * R) := by rfl
/-- a_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem a_def (Δ : Time) (R r : Nat) : a Δ R r = d Δ (r * R) := by rfl

end AvailableChain.Gen.Pure.SlotGrid

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- GridIdentitiesStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def GridIdentitiesStatement : Prop :=
  ∀ (Δ : Time) (s w k : Nat), 0 < Δ →
    q Δ s = v Δ (s + 1) ∧
    e Δ s + Δ = z Δ s ∧
    z Δ s + Δ = t Δ s + 4 * Δ ∧
    t Δ s + 4 * Δ < q Δ s ∧
    q Δ s + Δ = d Δ s ∧
    d Δ w + L Δ k = q Δ (w + k)

/-- GridPredecessorStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def GridPredecessorStatement : Prop :=
  ∀ (Δ : Time) (s : Nat), 1 ≤ s →
    v Δ s = q Δ (s - 1) ∧ e Δ s = d Δ (s - 1)

/-- GridRoundEquationsStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def GridRoundEquationsStatement : Prop :=
  ∀ (Δ : Time) (R r : Nat),
    T Δ R r = (r : Time) * P Δ R ∧
    a Δ R r = d Δ (r * R) ∧
    a Δ R r = T Δ R r + 6 * Δ

/-- GridOffsetOrderStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def GridOffsetOrderStatement : Prop :=
  ∀ (Δ c : Time) (i j : Nat), 0 < Δ →
    ((t Δ i + c ≤ t Δ j + c) ↔ i ≤ j) ∧
    ((t Δ i + c < t Δ j + c) ↔ i < j)

/-- InFlightLabelAtGateStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def InFlightLabelAtGateStatement : Prop :=
  ∀ (Δ : Time) (s r : Nat), 0 < Δ →
    v Δ r ≤ d Δ s → d Δ s < q Δ r → r = s + 1

/-- NoGateBetweenReleaseAndGateStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
def NoGateBetweenReleaseAndGateStatement : Prop :=
  ∀ (Δ : Time) (s r : Nat), 0 < Δ →
    ¬ (q Δ s < d Δ r ∧ d Δ r < d Δ s)

/-- LiveLeaseLabelBoundsStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
def LiveLeaseLabelBoundsStatement : Prop :=
  ∀ (Δ : Time) (s w k : Nat), 0 < Δ →
    d Δ w < q Δ s → q Δ s < d Δ w + L Δ k →
    w < s ∧ s < w + k

/-- RepairExpiryEquationsStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
def RepairExpiryEquationsStatement : Prop :=
  ∀ (Δ : Time) (b k : Nat), 1 ≤ b → 2 ≤ k →
    d Δ (b + k - 2) + L Δ k = t Δ (b + 2 * k - 1) + Δ ∧
    t Δ (b + 2 * k - 1) = t Δ b + 2 * L Δ k - 2 * Δ ∧
    d Δ (b - 1) + L Δ k = t Δ b + L Δ k + 2 * Δ ∧
    d Δ (b - 1) + L Δ k = t Δ (b + k) + Δ
/-- GridIdentitiesStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem GridIdentitiesStatement_def : GridIdentitiesStatement =
    (∀ (Δ : Time) (s w k : Nat), 0 < Δ →
      q Δ s = v Δ (s + 1) ∧ e Δ s + Δ = z Δ s ∧
      z Δ s + Δ = t Δ s + 4 * Δ ∧ t Δ s + 4 * Δ < q Δ s ∧
      q Δ s + Δ = d Δ s ∧ d Δ w + L Δ k = q Δ (w + k)) := by rfl

/-- GridPredecessorStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem GridPredecessorStatement_def : GridPredecessorStatement =
    (∀ (Δ : Time) (s : Nat), 1 ≤ s →
      v Δ s = q Δ (s - 1) ∧ e Δ s = d Δ (s - 1)) := by rfl

/-- GridRoundEquationsStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem GridRoundEquationsStatement_def : GridRoundEquationsStatement =
    (∀ (Δ : Time) (R r : Nat),
      T Δ R r = (r : Time) * P Δ R ∧
      a Δ R r = d Δ (r * R) ∧ a Δ R r = T Δ R r + 6 * Δ) := by rfl

/-- GridOffsetOrderStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem GridOffsetOrderStatement_def : GridOffsetOrderStatement =
    (∀ (Δ c : Time) (i j : Nat), 0 < Δ →
      ((t Δ i + c ≤ t Δ j + c) ↔ i ≤ j) ∧
      ((t Δ i + c < t Δ j + c) ↔ i < j)) := by rfl

/-- InFlightLabelAtGateStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem InFlightLabelAtGateStatement_def : InFlightLabelAtGateStatement =
    (∀ (Δ : Time) (s r : Nat), 0 < Δ →
      v Δ r ≤ d Δ s → d Δ s < q Δ r → r = s + 1) := by rfl

/-- NoGateBetweenReleaseAndGateStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem NoGateBetweenReleaseAndGateStatement_def :
    NoGateBetweenReleaseAndGateStatement =
    (∀ (Δ : Time) (s r : Nat), 0 < Δ →
      ¬ (q Δ s < d Δ r ∧ d Δ r < d Δ s)) := by rfl

/-- LiveLeaseLabelBoundsStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem LiveLeaseLabelBoundsStatement_def : LiveLeaseLabelBoundsStatement =
    (∀ (Δ : Time) (s w k : Nat), 0 < Δ →
      d Δ w < q Δ s → q Δ s < d Δ w + L Δ k →
      w < s ∧ s < w + k) := by rfl

/-- RepairExpiryEquationsStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem RepairExpiryEquationsStatement_def : RepairExpiryEquationsStatement =
    (∀ (Δ : Time) (b k : Nat), 1 ≤ b → 2 ≤ k →
      d Δ (b + k - 2) + L Δ k = t Δ (b + 2 * k - 1) + Δ ∧
      t Δ (b + 2 * k - 1) = t Δ b + 2 * L Δ k - 2 * Δ ∧
      d Δ (b - 1) + L Δ k = t Δ b + L Δ k + 2 * Δ ∧
      d Δ (b - 1) + L Δ k = t Δ (b + k) + Δ) := by rfl

end AvailableChain.Gen.Pure
