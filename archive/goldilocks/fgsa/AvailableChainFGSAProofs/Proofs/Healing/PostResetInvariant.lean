module
public import AvailableChainFGSAClaims.Statements.Healed

public section

/-! Post-reset carrier: blueprint 21 H.12–H.18; post-reset plan,
"Induction design" and J1/J2. B1 makes source_prefix an output; B15, B17
and B18 require compatibility before admission and a duty's own view.
The induction cut is the global event-prefix index. These declarations
contain no induction proof and consume no delivery contract. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:2868–2876, H.22:3044–3055; plan "Induction design";
B1/B17. Full H0 without the derived source_prefix field. -/
structure PostResetStart (w : HealingWitness) : Prop extends H0Reset p c E rho w where
  proposal_lower : w.sStar + 2 ≤ w.u
  proposal : HonestProposal E rho (fgsaInterface p c) w.u w.QStar
  proposal_first : ∀ v Q, w.sStar + 2 ≤ v →
    HonestProposal E rho (fgsaInterface p c) v Q → w.u ≤ v
  after_gst : E.t_GST ≤ tstar p w

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.18:2868–2876; plan "Induction design"; B1/B17.
Assemble frozen H0 after H.18 supplies the source prefix. -/
theorem PostResetStart.toH0 {w : HealingWitness}
    (start : PostResetStart p c E rho w) (hsp : Block.Preceq w.CStar w.QStar) :
    H0 p c E rho w :=
  { toH0Reset := start.toH0Reset
    proposal_lower := start.proposal_lower
    proposal := start.proposal
    proposal_first := start.proposal_first
    after_gst := start.after_gst
    source_prefix := hsp }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12:2652–2666 ("at q_(s*) … it keeps C* at that first transfer"); plan J1 and
"Induction design"; B1/B15/B17/B18. Stated at EACH honest node's OWN release tick j at q_(s*),
with that duty's own view X (as in RKeep), not at a pre-time cut with the full TF: the consumer
is the base case of PostResetProtectedKept at such a tick, and Kept / D_at depend on the state
at j and on X. First conjunct: the node holds C* in TF(j). Second: for every covered view X ⊆
TF(j) that holds C* and every high source (RKeep's three source guards), C* has height M + 1,
R.H = M + 1, R.lo ≤ h(C*), and, when X also holds every prefix of C* (RKeep's path guard), C* ∈
D_at and C* is kept — exactly protected_kept's kept clause for B = C* at the first release tick.
The horizon guard is the one in frozen TDelReset. H0Reset is the future producer's input (J1),
not a field here. -/
def ResetTransferCore (w : HealingWitness) : Prop :=
  SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
  ∀ j x, x ∈ rho.honest →
  rho.events[j]? = some (.tick x (SA.releaseTime p.toParams w.sStar)) →
  (∃ C ∈ (storeAt p c E rho j x).fg.TF, eraseFG C = w.CStar) ∧
  ∀ (X : Finset (FGBlock (Fin p.n))) C,
  X ⊆ (storeAt p c E rho j x).fg.TF → C ∈ X → eraseFG C = w.CStar →
  (∀ K s, SourceBefore p c E rho j K s → high p w K → K ∈ X) →
  (∀ K s, SourceBefore p c E rho j K s → high p w K →
    Block.Compatible (eraseFG K) w.CStar) →
  (∀ K K' s s', SourceBefore p c E rho j K s → SourceBefore p c E rho j K' s' →
    high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
  (heightView p C).h = w.M + 1 ∧ (R_at p c E rho j x).H = w.M + 1 ∧
    (R_at p c E rho j x).lo ≤ (heightView p C).h ∧
    ((∀ A, FGBlock.Preceq A C → A ∈ X) →
      C ∈ D_at p c E rho j x X ∧ Kept p c E rho j x X C)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2633–2651; plan "Induction design"; B1/B17/B18.
C* and its prefixes have label s*. Other bodies are actual post-reset
honest raw results at gates that passed. Membership uses the historical
gate event, not an honest node's current F, J, H, h_max or lo.
Vetoed raw results belong to the separate H.16 transfer field. -/
def ProtectedBody (w : HealingWitness) (B : FGBlock (Fin p.n)) (s : Slot) : Prop :=
  (s = w.sStar ∧ Block.Preceq (eraseFG B) w.CStar) ∨
  (w.sStar ≤ s ∧ ∃ k y, y ∈ rho.honest ∧ IsGateTick p c rho k y s ∧
    gatePassedAt p c E rho k ∧ gateResultAt p c E rho k = some (some (eraseFG B)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2633–2651; plan carrier protected_kept; B1/B17/B18.
Prefix restriction of frozen RKeep geometry, without its public H0 premise.
Each tick j is before i. X is that duty's own covered view. The final
kept-path clause is restricted to ProtectedBody; its path and compatibility
guards are the frozen guards. This definition does not consume RKeep.
OPEN OBLIGATION (lean-framework design review, 2026-10-03): frozen RKeep's last
clause quantifies over EVERY B that is prefix-closed in X and compatible with C*
and all high sources, not only ProtectedBody B. So frozen RKeep is NOT a projection
of this field. J3 must prove the general clause from the invariant, or show that
the guards force ProtectedBody B. -/
def PostResetProtectedKept (w : HealingWitness) (i : Nat) : Prop :=
  ∀ j, j < i → ∀ x (X : Finset (FGBlock (Fin p.n))) C,
  x ∈ rho.honest → X ⊆ (storeAt p c E rho j x).fg.TF →
  (∃ t, rho.events[j]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t) →
  C ∈ X → eraseFG C = w.CStar →
  (∀ K s, SourceBefore p c E rho j K s → high p w K → K ∈ X) →
  (∀ K s, SourceBefore p c E rho j K s → high p w K →
    Block.Compatible (eraseFG K) w.CStar) →
  (∀ K K' s s', SourceBefore p c E rho j K s → SourceBefore p c E rho j K' s' →
    high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
  let st := storeAt p c E rho j x
  let R := R_at p c E rho j x
  w.M + 1 ≤ st.fg.h_max ∧ (R.contest = true → st.fg.h_max = w.M + 1) ∧
  R.lo ≤ max (w.M + 1) (st.fg.h_max - 1) ∧
  (∀ B ∈ [R.Z, st.fg.F], FGBlock.Preceq B C ∨
    ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧ FGBlock.Preceq B K) ∧
  (∃ B ∈ X, (heightView p B).h = max (w.M + 1) (st.fg.h_max - 1)) ∧
  (∀ B s, ProtectedBody p c E rho w B s →
    (∀ A, FGBlock.Preceq A B → A ∈ X) → Block.Compatible (eraseFG B) w.CStar →
    (∀ K s', SourceBefore p c E rho j K s' → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K)) → Kept p c E rho j x X B)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2487–2627; plan carrier high_compatible; B15/B17.
Every pair of high sources whose rows precede i is compatible. No source
label lower bound is added: frozen THigh also covers old action rounds. -/
def PostResetHighCompatible (w : HealingWitness) (i : Nat) : Prop :=
  ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
    high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13–H.14:2487–2651; plan carrier reset_compatible;
B1/B15/B17. Every high source whose row precedes i is compatible with C*. -/
def PostResetResetCompatible (w : HealingWitness) (i : Nat) : Prop :=
  ∀ K s, SourceBefore p c E rho i K s → high p w K →
    Block.Compatible w.CStar (eraseFG K)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.15 (Lemma U):2885–2923; plan J4 and carrier lease_safe;
B1/B13/B17/B18.
Every successful write or renewal strictly above C* has the H5 HEAD,
parent and output clauses in this prefix. Later raw results extend its
target or finality covers it. The exact gateWriteKeys membership guards
identify writes, including pre-reset writes. They are stated inline to
avoid a StoreKeys import; no last-write fact or future read is assumed. -/
def PostResetLeaseSafe (w : HealingWitness) (i : Nat) : Prop :=
  ∀ k, k < i → ∀ y s B g C, y ∈ rho.honest → IsGateTick p c rho k y s →
  gatePassedAt p c E rho k → gateResultAt p c E rho k = some (some C) →
  Block.Preceq w.CStar B → B ≠ w.CStar →
  let pre := FGSA.clockPre p (storeAt p c E rho k y) (SA.gateTime p.toParams s)
  B ∈ (FGSA.actView pre).blocks → B ≠ .genesis → Block.Preceq B C →
  g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root (FGSA.actView
      pre) s B →
  (∀ l, l < i → ∀ x j D, x ∈ rho.honest → s + 1 ≤ j →
    IsGateTick p c rho l x j → gateResultAt p c E rho l = some (some D) →
    Block.Preceq B D ∨ Block.Preceq B (F_at p c E rho l x)) ∧
  (∀ x j H, x ∈ rho.honest → s + 1 ≤ j →
    timeIdx rho (SA.voteTime p.toParams j) ≤ i → headAtLabel p c E rho x j = some H →
    Block.Preceq B H) ∧
  (∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
    HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq B Q.parent) ∧
  (∀ j x, j < i → x ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
    HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) j →
    Block.Preceq B (S_at p c E rho j x))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17/H.18:2946–3060; plan J4 and carrier fprov;
B1/B13/B17/B18. Both frozen RFProv clauses at states before
events j < i, without the public H0 premise. The reset lower cut and each
source gate deadline remain unchanged. -/
def PostResetFProv (w : HealingWitness) (i : Nat) : Prop :=
  ∀ j, j < i → ∀ x,
  x ∈ rho.honest → afterTicksIdx rho (p.actionTime w.rStar) ≤ j →
  let t := (storeAt p c E rho j x).base.now
  (Block.Preceq (F_at p c E rho j x) w.CStar ∨
    ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧
      SA.gateTime p.toParams s + P p ≤ t ∧
      Block.Preceq (F_at p c E rho j x) (eraseFG K)) ∧
  (high p w (storeAt p c E rho j x).fg.J →
    ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧
      SA.gateTime p.toParams s ≤ t ∧
      Block.Preceq (J_at p c E rho j x) (eraseFG K))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2924–2945, H5:3318–3325; plan J5 and carrier
raw_transfer; B1/B13/B17/B18. DC: SAME raw-result transfer clauses.
All four frozen H5RawTransfer clauses. The source gate is an event before i;
each reader is also in the prefix, with complete inclusive time cuts for
postClock, HEAD and proposal reads. The output horizon guard is unchanged.
There is no fast threshold or passed-gate guard on the raw source. -/
def PostResetRawTransfer (w : HealingWitness) (i : Nat) : Prop :=
  ∀ k, k < i → ∀ y j C, y ∈ rho.honest → w.sStar ≤ j →
  IsGateTick p c rho k y j → gateResult p c E rho y j = some (some C) →
  (∀ x nd, x ∈ rho.honest → timeIdx rho (SA.releaseTime p.toParams j) ≤ i →
    postClock E rho x (SA.releaseTime p.toParams j) = some nd →
    ∀ lease ∈ nd.st.base.obligations, nd.st.base.now < lease.2.2 → Block.Compatible lease.1 C) ∧
  (∀ x s H, x ∈ rho.honest → j + 1 ≤ s →
    timeIdx rho (SA.voteTime p.toParams s) ≤ i → headAtLabel p c E rho x s = some H →
    Block.Preceq C H) ∧
  (∀ v Q, j + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
    HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent) ∧
  (∀ a x, a < i → x ∈ rho.honest → SA.gateTime p.toParams j + 4 * p.Δ ≤ rho.horizon →
    HealSuffix p c rho (SA.gateTime p.toParams j + 4 * p.Δ) a →
    Block.Preceq C (S_at p c E rho a x))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2764–2867, H.22:3109–3114; plan J6 and carrier
service; B1/B17. PROVISIONAL (J6 may refine).
Prefix restriction of H3/ExactService. HEAD service waits for the complete
vote-time cut. Gate service waits for the post-gate cut, including all ticks
at that time. Both frozen horizon guards and all exact gate clauses remain. -/
def PostResetService (w : HealingWitness) (i : Nat) : Prop :=
  ∀ v Q, HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
  timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
  (SA.voteTime p.toParams v ≤ rho.horizon → timeIdx rho (SA.voteTime p.toParams v) ≤ i →
    ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q) ∧
  (SA.gateTime p.toParams v ≤ rho.horizon →
    afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i → ∀ x ∈ rho.honest,
    gateResult p c E rho x v = some (some Q) ∧
    (∃ j, j < i ∧ IsGateTick p c rho j x v ∧ gatePassedAt p c E rho j) ∧
    (∃ nd, postClock E rho x (SA.gateTime p.toParams v) = some nd ∧
      Q ∈ (fastWriteAt nd.st v).getD []) ∧
    (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
    (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.12–H.18; plan "Induction design", J2–J6; B1/B15/B17/B18.
The seven named predicates at the global event-prefix cut i. H0Reset is
an input to future producers; neither H0 nor PostResetStart is a parameter. -/
structure PostResetInv (w : HealingWitness) (i : Nat) : Prop where
  protected_kept : PostResetProtectedKept p c E rho w i
  high_compatible : PostResetHighCompatible p c E rho w i
  reset_compatible : PostResetResetCompatible p c E rho w i
  lease_safe : PostResetLeaseSafe p c E rho w i
  fprov : PostResetFProv p c E rho w i
  raw_transfer : PostResetRawTransfer p c E rho w i
  service : PostResetService p c E rho w i

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem ResetTransferCore_def (w : HealingWitness) :
    ResetTransferCore p c E rho w = (
    SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
    ∀ j x, x ∈ rho.honest →
    rho.events[j]? = some (.tick x (SA.releaseTime p.toParams w.sStar)) →
    (∃ C ∈ (storeAt p c E rho j x).fg.TF, eraseFG C = w.CStar) ∧
    ∀ (X : Finset (FGBlock (Fin p.n))) C,
    X ⊆ (storeAt p c E rho j x).fg.TF → C ∈ X → eraseFG C = w.CStar →
    (∀ K s, SourceBefore p c E rho j K s → high p w K → K ∈ X) →
    (∀ K s, SourceBefore p c E rho j K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar) →
    (∀ K K' s s', SourceBefore p c E rho j K s → SourceBefore p c E rho j K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
    (heightView p C).h = w.M + 1 ∧ (R_at p c E rho j x).H = w.M + 1 ∧
      (R_at p c E rho j x).lo ≤ (heightView p C).h ∧
      ((∀ A, FGBlock.Preceq A C → A ∈ X) →
        C ∈ D_at p c E rho j x X ∧ Kept p c E rho j x X C)) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem ProtectedBody_def (w : HealingWitness) (B : FGBlock (Fin p.n)) (s : Slot) :
    ProtectedBody p c E rho w B s = (
    (s = w.sStar ∧ Block.Preceq (eraseFG B) w.CStar) ∨
    (w.sStar ≤ s ∧ ∃ k y, y ∈ rho.honest ∧ IsGateTick p c rho k y s ∧
      gatePassedAt p c E rho k ∧ gateResultAt p c E rho k = some (some (eraseFG B)))) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetProtectedKept_def (w : HealingWitness) (i : Nat) :
    PostResetProtectedKept p c E rho w i = (
    ∀ j, j < i → ∀ x (X : Finset (FGBlock (Fin p.n))) C,
    x ∈ rho.honest → X ⊆ (storeAt p c E rho j x).fg.TF →
    (∃ t, rho.events[j]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t) →
    C ∈ X → eraseFG C = w.CStar →
    (∀ K s, SourceBefore p c E rho j K s → high p w K → K ∈ X) →
    (∀ K s, SourceBefore p c E rho j K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar) →
    (∀ K K' s s', SourceBefore p c E rho j K s → SourceBefore p c E rho j K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
    let st := storeAt p c E rho j x
    let R := R_at p c E rho j x
    w.M + 1 ≤ st.fg.h_max ∧ (R.contest = true → st.fg.h_max = w.M + 1) ∧
    R.lo ≤ max (w.M + 1) (st.fg.h_max - 1) ∧
    (∀ B ∈ [R.Z, st.fg.F], FGBlock.Preceq B C ∨
      ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧ FGBlock.Preceq B K) ∧
    (∃ B ∈ X, (heightView p B).h = max (w.M + 1) (st.fg.h_max - 1)) ∧
    (∀ B s, ProtectedBody p c E rho w B s →
      (∀ A, FGBlock.Preceq A B → A ∈ X) → Block.Compatible (eraseFG B) w.CStar →
      (∀ K s', SourceBefore p c E rho j K s' → high p w K →
        Block.Compatible (eraseFG B) (eraseFG K)) → Kept p c E rho j x X B)) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetHighCompatible_def (w : HealingWitness) (i : Nat) :
    PostResetHighCompatible p c E rho w i = (
    ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetResetCompatible_def (w : HealingWitness) (i : Nat) :
    PostResetResetCompatible p c E rho w i = (
    ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible w.CStar (eraseFG K)) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetLeaseSafe_def (w : HealingWitness) (i : Nat) :
    PostResetLeaseSafe p c E rho w i = (
    ∀ k, k < i → ∀ y s B g C, y ∈ rho.honest → IsGateTick p c rho k y s →
    gatePassedAt p c E rho k → gateResultAt p c E rho k = some (some C) →
    Block.Preceq w.CStar B → B ≠ w.CStar →
    let pre := FGSA.clockPre p (storeAt p c E rho k y) (SA.gateTime p.toParams s)
    B ∈ (FGSA.actView pre).blocks → B ≠ .genesis → Block.Preceq B C →
    g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root (FGSA.actView
        pre) s B →
    (∀ l, l < i → ∀ x j D, x ∈ rho.honest → s + 1 ≤ j →
      IsGateTick p c rho l x j → gateResultAt p c E rho l = some (some D) →
      Block.Preceq B D ∨ Block.Preceq B (F_at p c E rho l x)) ∧
    (∀ x j H, x ∈ rho.honest → s + 1 ≤ j →
      timeIdx rho (SA.voteTime p.toParams j) ≤ i → headAtLabel p c E rho x j = some H →
      Block.Preceq B H) ∧
    (∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq B Q.parent) ∧
    (∀ j x, j < i → x ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) j →
      Block.Preceq B (S_at p c E rho j x))) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetFProv_def (w : HealingWitness) (i : Nat) :
    PostResetFProv p c E rho w i = (
    ∀ j, j < i → ∀ x,
    x ∈ rho.honest → afterTicksIdx rho (p.actionTime w.rStar) ≤ j →
    let t := (storeAt p c E rho j x).base.now
    (Block.Preceq (F_at p c E rho j x) w.CStar ∨
      ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧
        SA.gateTime p.toParams s + P p ≤ t ∧
        Block.Preceq (F_at p c E rho j x) (eraseFG K)) ∧
    (high p w (storeAt p c E rho j x).fg.J →
      ∃ K s, SourceBefore p c E rho j K s ∧ high p w K ∧
        SA.gateTime p.toParams s ≤ t ∧
        Block.Preceq (J_at p c E rho j x) (eraseFG K))) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetRawTransfer_def (w : HealingWitness) (i : Nat) :
    PostResetRawTransfer p c E rho w i = (
    ∀ k, k < i → ∀ y j C, y ∈ rho.honest → w.sStar ≤ j →
    IsGateTick p c rho k y j → gateResult p c E rho y j = some (some C) →
    (∀ x nd, x ∈ rho.honest → timeIdx rho (SA.releaseTime p.toParams j) ≤ i →
      postClock E rho x (SA.releaseTime p.toParams j) = some nd →
      ∀ lease ∈ nd.st.base.obligations, nd.st.base.now < lease.2.2 → Block.Compatible lease.1 C) ∧
    (∀ x s H, x ∈ rho.honest → j + 1 ≤ s →
      timeIdx rho (SA.voteTime p.toParams s) ≤ i → headAtLabel p c E rho x s = some H →
      Block.Preceq C H) ∧
    (∀ v Q, j + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent) ∧
    (∀ a x, a < i → x ∈ rho.honest → SA.gateTime p.toParams j + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams j + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a x))) := by rfl

-- equation export required by BUILD §7.2 B3a (body not exposed across modules)
theorem PostResetService_def (w : HealingWitness) (i : Nat) :
    PostResetService p c E rho w i = (
    ∀ v Q, HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
    timeIdx rho (SA.proposalTime p.toParams v) ≤ i →
    (SA.voteTime p.toParams v ≤ rho.horizon → timeIdx rho (SA.voteTime p.toParams v) ≤ i →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q) ∧
    (SA.gateTime p.toParams v ≤ rho.horizon →
      afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i → ∀ x ∈ rho.honest,
      gateResult p c E rho x v = some (some Q) ∧
      (∃ j, j < i ∧ IsGateTick p c rho j x v ∧ gatePassedAt p c E rho j) ∧
      (∃ nd, postClock E rho x (SA.gateTime p.toParams v) = some nd ∧
        Q ∈ (fastWriteAt nd.st v).getD []) ∧
      (fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams v) x) = Q ∧
      (∀ r, v = r * p.R → actionSource p c E rho x r = some (some Q)))) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.16:2930–2938, H.12:2664–2665; plan J5A C0;
B1/B13/B17/B18. DC: INTENTIONAL; DC has no leases; this is the SA port.
The global induction carries this predicate jointly with PostResetInv.
The successor instance is proved before raw_transfer at the new cut. -/
def PostResetResetLeaseCompatible (w : HealingWitness) (i : Nat) : Prop :=
  ∀ j, j < i → ∀ x, x ∈ rho.honest →
    afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ j →
    let st := (storeAt p c E rho j x).base
    ∀ lease ∈ st.obligations, st.now < lease.2.2 → Block.Compatible lease.1 w.CStar

-- equation export required by BUILD §7.2 B3a
theorem PostResetResetLeaseCompatible_def (w : HealingWitness) (i : Nat) :
    PostResetResetLeaseCompatible p c E rho w i = (
    ∀ j, j < i → ∀ x, x ∈ rho.honest →
      afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ j →
      let st := (storeAt p c E rho j x).base
      ∀ lease ∈ st.obligations, st.now < lease.2.2 → Block.Compatible lease.1 w.CStar) := by rfl

end AvailableChain.FGSA.Run
end
