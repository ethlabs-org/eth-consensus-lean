module
public import AvailableChainModel.Objects.Time
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace AvailableChain.Gen.Pure

abbrev Pattern := Finset (Nat × Nat)                   -- (round offset, slot offset)

/-- DC: Conditions.lean:201; INTENTIONAL: Patterns differ by use; GLY r3.19 S051. -/
def PatAt (H : Slot → Prop) (R : Nat) (pat : Pattern) (p : Nat) : Prop :=
  ∀ o ∈ pat, H ((p + o.1) * R + o.2)

def InWindow (q g r : Nat) : Prop := q ≤ r ∧ r < q + g

/-- The slot length: slot s starts at slotLen Δ · s (the SA slot clock, 4Δ). The one
place that fixes 4Δ (fgsa-lean O6). -/
def slotLen (Δ : Time) : Time := 4 * Δ

/-- The last round offset of `pat` (0 for the empty pattern). -/
def Pattern.lastRound (pat : Pattern) : Nat := pat.sup Prod.fst

/-- The last slot offset in the last round of `pat` (0 for the empty pattern). -/
def Pattern.lastSlot (pat : Pattern) : Nat :=
  (pat.filter (fun o => o.1 = pat.lastRound)).sup Prod.snd

/-- From the start of the last pattern round to the start of the last pattern slot,
plus Δ. A slot lasts 4Δ. -/
def Pattern.tailEnd (Δ : Time) (pat : Pattern) : Time := slotLen Δ * pat.lastSlot + Δ

/-- The last slot of `pat` in the last window round, plus Δ ("pattern end + Δ").
The window base rounds are q, …, q+g−1; the last pattern round is q+g−1+lastRound. -/
def windowEnd (_R : Nat) (P Δ : Time) (pat : Pattern) (q g : Nat) : Time :=
  ((q : Time) + g - 1 + pat.lastRound) * P + pat.tailEnd Δ

/-- The time form: the last pattern round starts at or before t + gP. -/
def windowEndAt (_R : Nat) (P Δ : Time) (pat : Pattern) (t : Time) (g : Nat) : Time :=
  t + g * P + pat.tailEnd Δ

/-- The start q ≥ 1 is here, once (D34).
DC: Conditions.lean:217; INTENTIONAL: Round samples; one-way DC; GLY r3.19 S059. -/
def RecPat (H : Slot → Prop) (R : Nat) (pat : Pattern) (P Δ GST horizon : Time)
    (lo g : Nat) : Prop :=
  lo ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P → windowEnd R P Δ pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ PatAt H R pat r

/-- The Rec_c form: for every integer time t ≥ max GST 1 (00:291), a pattern whose
rounds b, …, b + lastRound all start in [t, t + gP]. For a pattern with lastRound 2
this is "base round r − 2 with t + 2P ≤ T_r ≤ t + gP".
DC: Conditions.lean:232; INTENTIONAL: Rec_c needs the 9Δ guard; GLY r3.19 S060. -/
def RecPatAt (H : Slot → Prop) (R : Nat) (pat : Pattern) (P Δ GST horizon : Time)
    (lo g : Nat) : Prop :=
  lo ≤ g ∧ ∀ t : Time, max GST 1 ≤ t → windowEndAt R P Δ pat t g ≤ horizon →
    ∃ b : Nat, t ≤ ↑b * P ∧ (↑b + ↑pat.lastRound) * P ≤ t + ↑g * P ∧ PatAt H R pat b

/-- DC: Conditions.lean:201; same: Three opening slots; GLY r3.19 S061. -/
def Qualified (H : Slot → Prop) (R r : Nat) : Prop := H (r*R) ∧ H (r*R+1) ∧ H (r*R+2)
/-- DC: Conditions.lean:232; same: Same pointwise body; GLY r3.19 S062. -/
def Strong (H : Slot → Prop) (R r : Nat) : Prop :=
  Qualified H R r ∧ 2 ≤ r ∧ H ((r-2)*R) ∧ H ((r-1)*R)
/-- DC: Conditions.lean:201; INTENTIONAL: Use the forward pattern; GLY r3.19 S063. -/
def FGood (H : Slot → Prop) (R r : Nat) : Prop := H (r*R) ∧ H ((r+1)*R) ∧ H ((r+2)*R+2)
/-- DC: Conditions.lean:201; INTENTIONAL: Extra slot removes G ≤ P; GLY r3.19 S064. -/
def FGood4 (H : Slot → Prop) (R r : Nat) : Prop := FGood H R r ∧ H ((r+1)*R+2)
/-- DC: Conditions.lean:201; INTENTIONAL: Weaker two-window pattern; GLY r3.19 S065. -/
def Skip (H : Slot → Prop) (R p : Nat) : Prop := H (p*R) ∧ H ((p+2)*R+2)

inductive FinForm
  | fgood (r : Nat) | fgood4 (r : Nat)
  | recF | recF4 | recS | recSkip | recC | strongW | lit

def FinForm.pat : FinForm → Pattern
  | .recS                => {(0,0), (0,1), (0,2)}
  | .fgood _  | .recF    => {(0,0), (1,0), (2,2)}
  | .fgood4 _ | .recF4   => {(0,0), (1,0), (1,2), (2,2)}
  | .recSkip             => {(0,0), (2,2)}
  | .strongW | .lit | .recC => {(0,0), (1,0), (2,0), (2,1), (2,2)}

def FinForm.lo : FinForm → Nat
  | .strongW | .lit | .recC => 3
  | _ => 1

def FinForm.len (f : FinForm) (g : Nat) : Nat :=
  match f with
  | .strongW => g - 1
  | .lit     => g - 2
  | _        => g

def FinForm.holds (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    FinForm → Prop
  | .fgood r  => PatAt H R (FinForm.fgood r).pat r
  | .fgood4 r => PatAt H R (FinForm.fgood4 r).pat r
  | .recC     => RecPatAt H R FinForm.recC.pat P Δ GST horizon FinForm.recC.lo g
  | f         => f.lo ≤ g ∧ RecPat H R f.pat P Δ GST horizon 1 (f.len g)

/-- DC: Conditions.lean:217; INTENTIONAL: Healing search at round starts; GLY r3.19 S070. -/
def RecS (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recS.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ Qualified H R r
/-- DC: Conditions.lean:217; INTENTIONAL: Use the forward pattern; GLY r3.19 S071. -/
def RecF (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recF.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood H R r
/-- DC: Conditions.lean:217; INTENTIONAL: Extra slot removes G ≤ P; GLY r3.19 S072. -/
def RecF4 (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recF4.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood4 H R r
/-- DC: Conditions.lean:217; INTENTIONAL: Weaker two-window pattern; GLY r3.19 S073. -/
def RecSkip (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recSkip.pat q g ≤ horizon →
    ∃ p, InWindow q g p ∧ Skip H R p
/-- DC: Conditions.lean:232; INTENTIONAL: Allow faulty proposers at g=3; GLY r3.19 S074. -/
def StrongRecW (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  3 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P →
    windowEnd R P Δ FinForm.strongW.pat q (g - 1) ≤ horizon →
    ∃ r, q + 2 ≤ r ∧ r ≤ q + g ∧ Strong H R r
/-- DC: Conditions.lean:232; INTENTIONAL: Keep the literal window; GLY r3.19 S075. -/
def Lit (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  3 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P →
    windowEnd R P Δ FinForm.lit.pat q (g - 2) ≤ horizon →
    ∃ r, q + 2 ≤ r ∧ r < q + g ∧ Strong H R r
/-- DC: Conditions.lean:232; INTENTIONAL: The proof window must fit; GLY r3.19 S076. -/
def RecC (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  3 ≤ g ∧ ∀ t : Time, max GST 1 ≤ t → t + g * P + 9 * Δ ≤ horizon →
    ∃ r : Nat, t + 2 * P ≤ r * P ∧ r * P ≤ t + g * P ∧ Strong H R r

def windowEndA (f : FinForm) (R : Nat) (P Δ : Time) (q g : Nat) : Time :=
  windowEnd R P Δ f.pat q (f.len g)
def windowEndAtA (R : Nat) (P Δ : Time) (t : Time) (g : Nat) : Time :=
  windowEndAt R P Δ FinForm.recC.pat t g         -- fgsa-lean O5: the Gen term

/-- DC: Conditions.lean:217; INTENTIONAL: One bound serves both searches; GLY r3.19 S079. -/
def QualSearch (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) : Prop :=
  ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P → ↑q * P + ↑g * P + 9 * Δ ≤ horizon →
    ∃ r : Nat, ↑q * P ≤ ↑r * P ∧ ↑r * P ≤ ↑q * P + ↑g * P ∧ Qualified H R r

/-- The slot index of the last slot of `pat` at base round b (true maximum, any R). -/
def lastSlotIdx (R : Nat) (pat : Pattern) (b : Nat) : Nat := pat.sup (fun o => (b + o.1) * R + o.2)

/-- Pattern compatibility: every slot offset is at most R + lastSlot. Under it the
lexicographic (lastRound, lastSlot) is the true last slot. -/
def Pattern.Compat (R : Nat) (pat : Pattern) : Prop := ∀ o ∈ pat, o.2 ≤ R + pat.lastSlot

theorem PatAt_def (H : Slot → Prop) (R : Nat) (pat : Pattern) (p : Nat) :
    PatAt H R pat p =
      (∀ o ∈ pat, H ((p + o.1) * R + o.2)) := by rw [PatAt]

theorem InWindow_def (q g r : Nat) :
    InWindow q g r =
      (q ≤ r ∧ r < q + g) := by rw [InWindow]

theorem slotLen_def (Δ : Time) :
    slotLen Δ =
      (4 * Δ) := by rw [slotLen]

theorem Pattern.lastRound_def (pat : Pattern) :
    Pattern.lastRound pat =
      (pat.sup Prod.fst) := by rw [Pattern.lastRound]

theorem Pattern.lastSlot_def (pat : Pattern) :
    Pattern.lastSlot pat =
      ((pat.filter (fun o => o.1 = pat.lastRound)).sup Prod.snd) := by rw [Pattern.lastSlot]

theorem Pattern.tailEnd_def (Δ : Time) (pat : Pattern) :
    Pattern.tailEnd Δ pat =
      (slotLen Δ * pat.lastSlot + Δ) := by rw [Pattern.tailEnd]

theorem windowEnd_def (_R : Nat) (P Δ : Time) (pat : Pattern) (q g : Nat) :
    windowEnd _R P Δ pat q g =
      (((q : Time) + g - 1 + pat.lastRound) * P + pat.tailEnd Δ) := by rw [windowEnd]

theorem windowEndAt_def (_R : Nat) (P Δ : Time) (pat : Pattern) (t : Time) (g : Nat) :
    windowEndAt _R P Δ pat t g =
      (t + g * P + pat.tailEnd Δ) := by rw [windowEndAt]

theorem RecPat_def (H : Slot → Prop) (R : Nat) (pat : Pattern) (P Δ GST horizon : Time)
    (lo g : Nat) :
    RecPat H R pat P Δ GST horizon lo g =
      (lo ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P → windowEnd R P Δ pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ PatAt H R pat r) := by rw [RecPat]

theorem RecPatAt_def (H : Slot → Prop) (R : Nat) (pat : Pattern) (P Δ GST horizon : Time)
    (lo g : Nat) :
    RecPatAt H R pat P Δ GST horizon lo g =
      (lo ≤ g ∧ ∀ t : Time, max GST 1 ≤ t → windowEndAt R P Δ pat t g ≤ horizon →
    ∃ b : Nat, t ≤ ↑b * P ∧ (↑b + ↑pat.lastRound) * P ≤ t + ↑g * P ∧ PatAt H R pat b) := by
  rw [RecPatAt]

theorem Qualified_def (H : Slot → Prop) (R r : Nat) :
    Qualified H R r =
      (H (r*R) ∧ H (r*R+1) ∧ H (r*R+2)) := by rw [Qualified]

theorem Strong_def (H : Slot → Prop) (R r : Nat) :
    Strong H R r =
      (Qualified H R r ∧ 2 ≤ r ∧ H ((r-2)*R) ∧ H ((r-1)*R)) := by rw [Strong]

theorem FGood_def (H : Slot → Prop) (R r : Nat) :
    FGood H R r =
      (H (r*R) ∧ H ((r+1)*R) ∧ H ((r+2)*R+2)) := by rw [FGood]

theorem FGood4_def (H : Slot → Prop) (R r : Nat) :
    FGood4 H R r =
      (FGood H R r ∧ H ((r+1)*R+2)) := by rw [FGood4]

theorem Skip_def (H : Slot → Prop) (R p : Nat) :
    Skip H R p =
      (H (p*R) ∧ H ((p+2)*R+2)) := by rw [Skip]

theorem FinForm.pat_def (f : FinForm) :
    f.pat =
      (match f with
  | .recS                => {(0,0), (0,1), (0,2)}
  | .fgood _  | .recF    => {(0,0), (1,0), (2,2)}
  | .fgood4 _ | .recF4   => {(0,0), (1,0), (1,2), (2,2)}
  | .recSkip             => {(0,0), (2,2)}
  | .strongW | .lit | .recC => {(0,0), (1,0), (2,0), (2,1), (2,2)}) := by
  cases f <;> rw [FinForm.pat]

theorem FinForm.lo_def (f : FinForm) :
    f.lo =
      (match f with
  | .strongW | .lit | .recC => 3
  | _ => 1) := by
  cases f <;> rw [FinForm.lo] <;> simp

theorem FinForm.len_def (f : FinForm) (g : Nat) :
    FinForm.len f g =
      (match f with
  | .strongW => g - 1
  | .lit     => g - 2
  | _        => g) := by
  cases f <;> rw [FinForm.len] <;> simp

theorem FinForm.holds_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time)
    (g : Nat) (f : FinForm) :
    f.holds H R P Δ GST horizon g =
      (match f with
  | .fgood r  => PatAt H R (FinForm.fgood r).pat r
  | .fgood4 r => PatAt H R (FinForm.fgood4 r).pat r
  | .recC     => RecPatAt H R FinForm.recC.pat P Δ GST horizon FinForm.recC.lo g
  | f         => f.lo ≤ g ∧ RecPat H R f.pat P Δ GST horizon 1 (f.len g)) := by
  cases f <;> rw [FinForm.holds] <;> simp

theorem RecS_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    RecS H R P Δ GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recS.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ Qualified H R r) := by rw [RecS]

theorem RecF_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    RecF H R P Δ GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recF.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood H R r) := by rw [RecF]

theorem RecF4_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    RecF4 H R P Δ GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recF4.pat q g ≤ horizon →
    ∃ r, InWindow q g r ∧ FGood4 H R r) := by rw [RecF4]

theorem RecSkip_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    RecSkip H R P Δ GST horizon g =
      (1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P → windowEnd R P Δ FinForm.recSkip.pat q g ≤ horizon →
    ∃ p, InWindow q g p ∧ Skip H R p) := by rw [RecSkip]

theorem StrongRecW_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    StrongRecW H R P Δ GST horizon g =
      (3 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P →
    windowEnd R P Δ FinForm.strongW.pat q (g - 1) ≤ horizon →
    ∃ r, q + 2 ≤ r ∧ r ≤ q + g ∧ Strong H R r) := by rw [StrongRecW]

theorem Lit_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    Lit H R P Δ GST horizon g =
      (3 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ q * P →
    windowEnd R P Δ FinForm.lit.pat q (g - 2) ≤ horizon →
    ∃ r, q + 2 ≤ r ∧ r < q + g ∧ Strong H R r) := by rw [Lit]

theorem RecC_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    RecC H R P Δ GST horizon g =
      (3 ≤ g ∧ ∀ t : Time, max GST 1 ≤ t → t + g * P + 9 * Δ ≤ horizon →
    ∃ r : Nat, t + 2 * P ≤ r * P ∧ r * P ≤ t + g * P ∧ Strong H R r) := by rw [RecC]

theorem windowEndA_def (f : FinForm) (R : Nat) (P Δ : Time) (q g : Nat) :
    windowEndA f R P Δ q g =
      (windowEnd R P Δ f.pat q (f.len g)) := by rw [windowEndA]

theorem windowEndAtA_def (R : Nat) (P Δ : Time) (t : Time) (g : Nat) :
    windowEndAtA R P Δ t g =
      (windowEndAt R P Δ FinForm.recC.pat t g) := by rw [windowEndAtA]

theorem QualSearch_def (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time) (g : Nat) :
    QualSearch H R P Δ GST horizon g =
      (∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P → ↑q * P + ↑g * P + 9 * Δ ≤ horizon →
    ∃ r : Nat, ↑q * P ≤ ↑r * P ∧ ↑r * P ≤ ↑q * P + ↑g * P ∧ Qualified H R r) := by rw [QualSearch]

theorem lastSlotIdx_def (R : Nat) (pat : Pattern) (b : Nat) :
    lastSlotIdx R pat b =
      (pat.sup (fun o => (b + o.1) * R + o.2)) := by rw [lastSlotIdx]

theorem Pattern.Compat_def (R : Nat) (pat : Pattern) :
    Pattern.Compat R pat =
      (∀ o ∈ pat, o.2 ≤ R + pat.lastSlot) := by rw [Pattern.Compat]

end AvailableChain.Gen.Pure
