module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRuleComp
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Rule

public section

/-! # Candidate `cert-recovery`: the late-certificate stage

A candidate that adds one more backward stage after evidence-release's. The rule (cert-recovery's
spec, §"Rules"):

* **Formation slots.** A stored lock (`CLock`) is evidence-release's weighted lock with `a`, the
  first slot of its formation: its own slot `j` for a fast or optimistic lock, `j − k + 1` for a
  slow lock (`firstSlot`). No step changes `a`; a move changes only the block.
* **The arrival record** (`CertCtx`, the stage's context): the votes the node has archived, each
  with the time it first received it (`arrival x = some τ`; `none`: not archived), and the time
  of the node's latest restart. How the archive is kept (its two-per-validator cap, the votes too
  old for the pool, the restart dropping it) is the SA's business; the stage reads it as given.
* **Late certificate.** For a slot `i` and a block `Y`, `lateSet i Y` is the validators with an
  archived slot-`i` vote, first received at or after the early cutoff `t_i + 2Δ`, whose head is a
  block of the tree of slot at most `i` that does not extend `Y` (each validator once). A slot has
  a certificate (`HasCert`) when some archived slot-`i` vote is late and resolved so.
* **The stage** (`lateTarget`): a lock that the node has held since its formation began
  (`restart_time ≤ t_a`, `Eligible`) moves from `T` to the deepest block `Y ⪯ T` of the tree whose
  late certificate is below the lock's weight at `Y` for every slot of `[a, j]` that has one
  (`CertPass`), or to `Φ.F`; any other lock keeps its place. With no certificate every block
  passes, so the lock stays at `T`.

**One convention, as the reference simulator.** `CertPass` constrains only the formation slots that
have a certificate, where the rule's wording tests every slot of `[a, j]`: for a slot without one
the late certificate is empty (`lateSet_eq_empty_of_not_hasCert`), so that test asks `0 < W(Y)`.
The two agree wherever the lock's weight at `Y` is positive (`certPass_iff_formation`), and with a
certificate in the window passing already forces it. They differ only at a block of weight `0`
when no formation slot has a certificate; there the stage keeps the lock at `T`. In the candidate
`T` is evidence-release's target, which has positive weight (it is keepable) or is `Φ.F`, where
both forms give `Φ.F`, so the candidate's result is the rule's (an argument, not a theorem here).

The stage is lawful with keep premise `lateKeep` (for an eligible lock, the late certificate of
each formation slot with one lies in a set of fewer validators than the weight) and fixes its own
choice for every lock (`lateStage_lawful`, `lateStage_fixes`). -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

/-- A weighted lock with the first slot of its formation. -/
structure CLock where
  /-- The weighted lock. -/
  w : WLock
  /-- The first slot of its formation. -/
  a : Int

/-- The store of locks with formation slots: forgotten to the lock, moved by changing its block. -/
abbrev clockStore : LockStore where
  Lk := CLock
  lock c := c.w.lock
  withBlock c r := { c with w := { c.w with lock := { c.w.lock with block := r } } }

theorem clockStore_lawful : clockStore.Lawful where
  lock_withBlock _ _ := rfl
  withBlock_withBlock _ _ _ := rfl
  withBlock_self _ := rfl

/-- Forgetting the formation slot: the map to evidence-release's weighted locks. -/
def forgetA : LockStore.Hom clockStore wlockStore where
  toFun c := c.w
  lock_map _ := rfl
  map_withBlock _ _ := rfl

theorem forgetA_apply (c : CLock) : forgetA.toFun c = c.w := by
  rfl

/-- The first slot of the formation of a lock written in slot `j`: `j` for a fast or optimistic
lock, `j − k + 1` for a slow lock (its `k` saved confirmations). -/
def firstSlot (k : Nat) (l : Lock) : Int :=
  if l.fast then (l.slot : Int) else (l.slot : Int) - k + 1

/-- A written weighted lock with its formation slot, for the SA's window `k`. -/
def tagA (sp : SAParams) (w : WLock) : CLock :=
  ⟨w, firstSlot sp.k w.lock⟩

theorem tagA_a (sp : SAParams) (w : WLock) : (tagA sp w).a = firstSlot sp.k w.lock := by
  rfl

theorem forgetA_tagA (sp : SAParams) (w : WLock) : forgetA.toFun (tagA sp w) = w := by
  rfl

/-- The arrival record: the first-receipt time of each archived vote, and the latest restart. -/
structure CertCtx (n : Nat) where
  /-- The first-receipt time of an archived vote (`none`: not archived). -/
  arrival : Vote n → Option Time
  /-- The time of the latest restart (`⊥`: none). -/
  restart : WithBot Time

variable (sp : SAParams) {FGP : Type}

/-- The late certificate of slot `i` against `Y`: the validators with an archived slot-`i` vote
first received at or after `t_i + 2Δ` whose head, a block of the tree of slot at most `i`, does not
extend `Y`. -/
def lateSet (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (i : Int) (Y : Blk sp.n FGP) :
    Set (Fin sp.n) :=
  {v | ∃ x τ, ctx.arrival x = some τ ∧ x.val = v ∧ (x.slot : Int) = i ∧
    sp.ts i + 2 * sp.Δ ≤ τ ∧ ∃ H ∈ Φ.tree, H.root = x.head ∧ (H.slot : Int) ≤ i ∧ ¬ Φ.Anc Y H}

/-- Slot `i` has a late certificate: an archived slot-`i` vote first received at or after
`t_i + 2Δ`, with its head a block of the tree of slot at most `i`. -/
def HasCert (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (i : Int) : Prop :=
  ∃ x τ, ctx.arrival x = some τ ∧ (x.slot : Int) = i ∧ sp.ts i + 2 * sp.Δ ≤ τ ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ (H.slot : Int) ≤ i

/-- `Y` passes the late-certificate test for `c`: for every formation slot with a certificate,
the certificate against `Y` is below the lock's weight at `Y`. -/
def CertPass (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (c : CLock) (Y : Blk sp.n FGP) : Prop :=
  ∀ i : Int, c.a ≤ i → i ≤ c.w.lock.slot → HasCert sp ctx Φ i →
    (lateSet sp ctx Φ i Y).ncard < c.w.weight Y.root

/-- The node has held the lock since its formation began: no restart after `t_a`. -/
def Eligible (ctx : CertCtx sp.n) (c : CLock) : Prop :=
  ctx.restart ≤ ((sp.ts c.a : Time) : WithBot Time)

/-- The blocks the stage may keep `c` on, at or below `T`. -/
def passing (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (c : CLock) (T : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {Y | Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ CertPass sp ctx Φ c Y}

open Classical in
/-- Where the stage moves `c` from `T`: for an eligible lock the deepest passing block, or `Φ.F`;
any other lock stays at `T`. -/
noncomputable def lateTarget (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (c : CLock)
    (T : Blk sp.n FGP) : Blk sp.n FGP :=
  if Eligible sp ctx c then (deepest Φ (passing sp ctx Φ c T)).getD Φ.F else T

/-- The late-certificate stage, reading the arrival record. -/
noncomputable def lateStage : UnlockStage sp clockStore (CertCtx sp.n) where
  target ctx Φ _ _ c T := lateTarget sp ctx Φ c T

/-- The stage's keep premise at `Y`: for an eligible lock, the late certificate against `Y` of
each formation slot with a certificate lies in a set of fewer validators than the weight. -/
def lateKeep : UnlockStage.Keep sp clockStore (CertCtx sp.n) :=
  fun ctx Φ _ _ c Y => Eligible sp ctx c → ∀ i : Int, c.a ≤ i → i ≤ c.w.lock.slot →
    HasCert sp ctx Φ i →
    ∃ O : Set (Fin sp.n), lateSet sp ctx Φ i Y ⊆ O ∧ O.ncard < c.w.weight Y.root

variable {sp}

theorem lateStage_target (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (c : CLock) (T : Blk sp.n FGP) :
    (lateStage sp).target ctx Φ V s c T = lateTarget sp ctx Φ c T := by
  rfl

theorem mem_passing {ctx : CertCtx sp.n} {Φ : Frm sp.n FGP} {c : CLock} {T Y : Blk sp.n FGP} :
    Y ∈ passing sp ctx Φ c T ↔ Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ CertPass sp ctx Φ c Y :=
  Iff.rfl

theorem lateKeep_iff (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (c : CLock) (Y : Blk sp.n FGP) :
    lateKeep sp ctx Φ V s c Y ↔ (Eligible sp ctx c → ∀ i : Int, c.a ≤ i → i ≤ c.w.lock.slot →
      HasCert sp ctx Φ i →
      ∃ O : Set (Fin sp.n), lateSet sp ctx Φ i Y ⊆ O ∧ O.ncard < c.w.weight Y.root) :=
  Iff.rfl

theorem lateTarget_of_eligible {ctx : CertCtx sp.n} {c : CLock} (h : Eligible sp ctx c)
    (Φ : Frm sp.n FGP) (T : Blk sp.n FGP) :
    lateTarget sp ctx Φ c T = (deepest Φ (passing sp ctx Φ c T)).getD Φ.F := by
  rw [lateTarget, ite_eq_left h]

theorem lateTarget_of_not_eligible {ctx : CertCtx sp.n} {c : CLock} (h : ¬ Eligible sp ctx c)
    (Φ : Frm sp.n FGP) (T : Blk sp.n FGP) : lateTarget sp ctx Φ c T = T := by
  rw [lateTarget, ite_eq_right h]

/-- The stage's target is in the tree, at or below `T`. -/
theorem lateTarget_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n) (c : CLock)
    {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) :
    lateTarget sp ctx Φ c T ∈ Φ.tree ∧ Φ.Anc (lateTarget sp ctx Φ c T) T := by
  by_cases he : Eligible sp ctx c
  · rw [lateTarget_of_eligible he]
    cases h : deepest Φ (passing sp ctx Φ c T) with
    | none => exact ⟨hΦ.rooted.1, hΦ.rooted.2 T hT⟩
    | some D => exact ⟨(deepest_mem h).1.1, (deepest_mem h).1.2.1⟩
  · rw [lateTarget_of_not_eligible he]
    exact ⟨hT, .refl⟩

/-- **The keep.** A block `Y ⪯ T` of the tree that passes stays at or below the target. -/
theorem lateTarget_keeps {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n) (c : CLock)
    {T Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree) (hYT : Φ.Anc Y T)
    (hk : Eligible sp ctx c → CertPass sp ctx Φ c Y) : Φ.Anc Y (lateTarget sp ctx Φ c T) := by
  by_cases he : Eligible sp ctx c
  · have hS : passing sp ctx Φ c T ⊆ Φ.tree := fun X hX => hX.1
    have hYS : Y ∈ passing sp ctx Φ c T := ⟨hY, hYT, hk he⟩
    obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Y, hYS⟩
    have hYD := anc_deepest hΦ hS (fun X hX C hC => anc_total hΦ.coherent hX.2.1 hC.2.1) hD Y hYS
    rw [lateTarget_of_eligible he, hD, Option.getD_some]
    exact hYD
  · rw [lateTarget_of_not_eligible he]
    exact hYT

/-- The stage fixes its own choice. -/
theorem lateTarget_lateTarget {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (c : CLock) {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) :
    lateTarget sp ctx Φ c (lateTarget sp ctx Φ c T) = lateTarget sp ctx Φ c T := by
  by_cases he : Eligible sp ctx c
  · have hsub : ∀ {X}, Φ.Anc X T → passing sp ctx Φ c X ⊆ passing sp ctx Φ c T :=
      fun hXT Y hY => ⟨hY.1, hY.2.1.trans hXT, hY.2.2⟩
    rw [lateTarget_of_eligible he, lateTarget_of_eligible he]
    rcases hd : deepest Φ (passing sp ctx Φ c T) with _ | D
    · rw [Option.getD_none]
      have hempty : passing sp ctx Φ c T = ∅ := by
        by_contra hne
        obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => hX.1) (Set.nonempty_iff_ne_empty.2 hne)
        rw [hd] at hD
        cases hD
      rcases hd' : deepest Φ (passing sp ctx Φ c Φ.F) with _ | D'
      · rfl
      · have := hsub (hΦ.rooted.2 T hT) (deepest_mem hd').1
        rw [hempty] at this
        exact absurd this (Set.notMem_empty _)
    · rw [Option.getD_some]
      obtain ⟨hDt, hDT, hDp⟩ := (deepest_mem hd).1
      have hDS : D ∈ passing sp ctx Φ c D := ⟨hDt, .refl, hDp⟩
      have hsubT : passing sp ctx Φ c D ⊆ Φ.tree := fun X hX => hX.1
      obtain ⟨D', hD'⟩ := exists_deepest hΦ hsubT ⟨D, hDS⟩
      rw [hD', Option.getD_some]
      have h1 := (deepest_mem hD').1.2.1
      have h2 := anc_deepest hΦ hsubT
        (fun X hX C hC => anc_total hΦ.coherent hX.2.1 hC.2.1) hD' D hDS
      exact Anc.antisymm hΦ.coherent h1 h2
  · rw [lateTarget_of_not_eligible he, lateTarget_of_not_eligible he]

/-- The late certificate inside a smaller set gives the test. -/
theorem certPass_of_keep {ctx : CertCtx sp.n} {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int}
    {c : CLock} {Y : Blk sp.n FGP} (hk : lateKeep sp ctx Φ V s c Y) (he : Eligible sp ctx c) :
    CertPass sp ctx Φ c Y := by
  intro i hi₁ hi₂ hc
  obtain ⟨O, hO, hOw⟩ := hk he i hi₁ hi₂ hc
  exact lt_of_le_of_lt (Set.ncard_le_ncard hO O.toFinite) hOw

/-- A slot without a certificate has an empty late certificate. -/
theorem lateSet_eq_empty_of_not_hasCert {ctx : CertCtx sp.n} {Φ : Frm sp.n FGP} {i : Int}
    (h : ¬ HasCert sp ctx Φ i) (Y : Blk sp.n FGP) : lateSet sp ctx Φ i Y = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, τ, hx, -, hxs, hτ, H, hH, hHr, hHs, -⟩
  exact h ⟨x, τ, hx, hxs, hτ, H, hH, hHr, hHs⟩

/-- **The test against the rule's wording.** Where the lock's weight at `Y` is positive, passing is
the late certificate of every formation slot being below the weight. -/
theorem certPass_iff_formation {ctx : CertCtx sp.n} {Φ : Frm sp.n FGP} {c : CLock}
    {Y : Blk sp.n FGP} (hW : 0 < c.w.weight Y.root) :
    CertPass sp ctx Φ c Y ↔ ∀ i : Int, c.a ≤ i → i ≤ c.w.lock.slot →
      (lateSet sp ctx Φ i Y).ncard < c.w.weight Y.root := by
  constructor
  · intro h i hi₁ hi₂
    by_cases hc : HasCert sp ctx Φ i
    · exact h i hi₁ hi₂ hc
    · rw [lateSet_eq_empty_of_not_hasCert hc, Set.ncard_empty]
      exact hW
  · intro h i hi₁ hi₂ _
    exact h i hi₁ hi₂

variable (sp) in
/-- **The late-certificate stage is lawful.** -/
theorem lateStage_lawful : (lateStage sp).Lawful (lateKeep sp) where
  target_withBlock _ _ _ _ _ _ _ := rfl
  target_anc := by
    intro _ ctx Φ V s c T hΦ hT
    exact lateTarget_anc hΦ ctx c hT
  keeps := by
    intro _ ctx Φ V s c T Y hΦ hY hYT hk
    exact lateTarget_keeps hΦ ctx c hY hYT (certPass_of_keep hk)

variable (sp) in
/-- **The late-certificate stage fixes its own choice**, for every lock. -/
theorem lateStage_fixes : (lateStage sp).Fixes fun _ _ => True where
  target_target := by
    intro _ ctx Φ V s c T hΦ hT _
    exact lateTarget_lateTarget hΦ ctx c hT

/-- With no late certificate in the formation window, every block passes, so the stage keeps the
lock at `T` (a block of the tree). -/
theorem lateTarget_of_noCert {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {ctx : CertCtx sp.n}
    {c : CLock} (h : ∀ i : Int, c.a ≤ i → i ≤ c.w.lock.slot → ¬ HasCert sp ctx Φ i)
    {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) : lateTarget sp ctx Φ c T = T := by
  have hpass : ∀ Y, CertPass sp ctx Φ c Y := fun Y i hi₁ hi₂ hc => absurd hc (h i hi₁ hi₂)
  obtain ⟨hLt, hLT⟩ := lateTarget_anc hΦ ctx c hT
  exact Anc.antisymm hΦ.coherent hLT
    (lateTarget_keeps hΦ ctx c hT .refl fun _ => hpass T)

end Consensus.Goldilocks.LateCertificate

end
