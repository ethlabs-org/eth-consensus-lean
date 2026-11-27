module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.CommitteeRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service

public section

/-! # Goldilocks under `Sleepy`: record writes inside one call

Which blocks one AC call can write as the record (`Writes`, `call_writes_guarded`,
`call_writes`), and that a changed record has an actual writer whose optimistic fast lock stays
stored (`call_record_writer`), with the keep and write toolkit (`KeepAll`, `RecLock`,
`call_reclock`) that `Compose/Sleepy/Served` builds the record step on. Split out of
`Compose/Sleepy/Served`, so that a new writer fact does not rebuild Served's cone. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### Record writes inside one call -/

section Writes

variable {FGP : Type} {sp : ACParams}

/-- The record moves from `r` to `r'` by a sequence of `update_latest_confirmed` writes with
candidates `C ∈ Φ.tree` satisfying `New`: each keeps the record when `C ⪯` it in the tree and
moves it to `C` otherwise. -/
def Writes (Φ : AC.Frm sp.n FGP) (New : AC.Blk sp.n FGP → Prop) : Nat → Nat → Prop :=
  Relation.ReflTransGen fun r r' => ∃ C ∈ Φ.tree, New C ∧
    ((AC.AncR Φ C r ∧ r' = r) ∨ (¬ AC.AncR Φ C r ∧ r' = C.root))

theorem writes_iff {Φ : AC.Frm sp.n FGP} {New : AC.Blk sp.n FGP → Prop} {r r' : Nat} :
    Writes Φ New r r' ↔ Relation.ReflTransGen (fun r r' => ∃ C ∈ Φ.tree, New C ∧
      ((AC.AncR Φ C r ∧ r' = r) ∨ (¬ AC.AncR Φ C r ∧ r' = C.root))) r r' := Iff.rfl

theorem Writes.mono {Φ : AC.Frm sp.n FGP} {New New' : AC.Blk sp.n FGP → Prop}
    {r r' : Nat} (h : Writes Φ New r r') (hN : ∀ C, New C → New' C) : Writes Φ New' r r' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨C, hC, hn, h'⟩ := hs
    exact ih.tail ⟨C, hC, hN C hn, h'⟩

theorem Writes.of_eq {Φ : AC.Frm sp.n FGP} {New : AC.Blk sp.n FGP → Prop} {r r' : Nat}
    (h : r' = r) : Writes Φ New r r' :=
  h ▸ .refl

theorem writes_update (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) {C : AC.Blk sp.n FGP}
    (hC : C ∈ Φ.tree) {New : AC.Blk sp.n FGP → Prop} (hN : New C) {r r' : Nat}
    (hr : A.latestConfirmed = r) (hr' : r' = (AC.updateLatestConfirmed sp A Φ C).latestConfirmed) :
    Writes Φ New r r' := by
  subst hr hr'
  refine Relation.ReflTransGen.single ⟨C, hC, hN, ?_⟩
  unfold AC.updateLatestConfirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

theorem admitVote_latestConfirmed (A : AC.ACState sp.n) (t : Time) (v : Vote sp.n) :
    (AC.admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold AC.admitVote
  split_ifs <;> rfl

theorem blockReceipt_latestConfirmed (A : AC.ACState sp.n) (t : Time)
    (B : AC.Blk sp.n FGP) : (AC.blockReceipt sp A t B).latestConfirmed = A.latestConfirmed :=
  rfl

theorem writes_optimistic (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time)
    {r : Nat} (hr : A.latestConfirmed = r) :
    Writes Φ (fun B => AC.optimisticSelect sp A Φ t = some B) r
      (AC.optimisticConfirmation sp A Φ t).latestConfirmed := by
  subst hr
  unfold AC.optimisticConfirmation
  rcases h : AC.optimisticSelect sp A Φ t with _ | B
  · exact .refl
  · have hB := h
    unfold AC.optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    refine writes_update { A with locks := (AC.addLocks sp A.locks Φ t (sp.slot t)
      {(B.root, true, AC.fastExpiry sp A.locks Φ t (sp.slot t))}) }
      Φ (AC.deepest_mem hB).1.1 ?_ rfl rfl
    rfl

theorem writes_tryVote (x : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun B => ∃ e ∈ (AC.tryVote sp x A Φ t).2,
        AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some B)
      A.latestConfirmed (AC.tryVote sp x A Φ t).1.latestConfirmed := by
  unfold AC.tryVote
  dsimp only
  by_cases h₁ : ¬ AC.joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t
  · rw [ite_eq_left h₁]
    exact .refl
  rw [ite_eq_right h₁]
  by_cases h₂ : t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ AC.voteReady sp A Φ (sp.slot t))
  · rw [ite_eq_left h₂]
    exact .refl
  rw [ite_eq_right h₂]
  by_cases hm : A.mayVote (sp.slot t) = true
  · simp only [hm, ite_true]
    refine (writes_optimistic _ Φ t ?_).mono fun B hB => ⟨_, List.mem_singleton_self _, hB⟩
    rw [admitVote_latestConfirmed]
    split_ifs <;> rfl
  · simp only [hm, Bool.false_eq_true, ite_false]
    split_ifs <;> exact Writes.of_eq rfl

theorem writes_updateConfirmation (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time)
    (s : Nat) :
    Writes Φ (fun C => AC.getConfirmation sp A Φ s = some C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t C) A.latestConfirmed
      (AC.updateConfirmation sp A Φ t s).latestConfirmed := by
  unfold AC.updateConfirmation
  dsimp only
  rcases hC : AC.getConfirmation sp A Φ s with _ | C
  · exact .refl
  · dsimp only
    split_ifs with hveto
    · exact .refl
    all_goals
      refine writes_update { A with saved := Function.update A.saved s ((some C).map Block.root) }
        Φ (AC.deepest_mem hC).1.1 ?_ rfl rfl
      exact ⟨rfl, hveto⟩

theorem writes_onTick (x : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun C => (∃ e ∈ (AC.acOnTick sp x A Φ t).2,
        AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some C) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ AC.joined sp A t ∧
          AC.getConfirmation sp A Φ (sp.slot t - 1) = some C ∧
          ¬ AC.conflictsWithLock sp A.locks Φ t C))
      A.latestConfirmed (AC.acOnTick sp x A Φ t).1.latestConfirmed := by
  unfold AC.acOnTick
  dsimp only
  by_cases hj : AC.joined sp A t
  · rw [ite_eq_right (not_not_intro hj)]
    by_cases hu : t = sp.ts (sp.slot t) + sp.Δ
    · rw [ite_eq_left hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · exfalso
        have := sp.toParams.hΔ
        linarith [ht.1.symm.trans hu]
      · rw [ite_eq_right ht]
        exact (writes_tryVote x A Φ t).mono fun C h => Or.inl h
    · rw [ite_eq_right hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · rw [ite_eq_left ht]
        exact (writes_updateConfirmation A Φ t _).mono fun C h => Or.inr ⟨ht.1, ht.2, hj, h⟩
      · rw [ite_eq_right ht]
        exact .refl
  · rw [ite_eq_left hj]
    exact .refl

theorem proposal_latestConfirmed (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    (t : Time) : (AC.acProposal sp A Φ t).1.latestConfirmed = A.latestConfirmed := by
  unfold AC.acProposal
  dsimp only
  split_ifs <;> rfl

theorem toFG_latestConfirmed (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) :
    (AC.acToFG sp A Φ t).1.latestConfirmed = A.latestConfirmed := by
  unfold AC.acToFG
  split_ifs <;> rfl

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
  {tr : AC.GTrace sp FGP ro}

/-- **The record writes of a call**: every candidate is the result of the call's update or the
selection of one of its optimistic checks. -/
theorem call_writes_guarded {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    Writes ℓ.frame (fun C => ∃ s CV,
      (AC.ResultAt tr x i s C CV ∧
        ¬ AC.conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) C) ∨
      AC.OptimisticLockAt tr x i s C CV)
      (tr.state x i).latestConfirmed (tr.post i).latestConfirmed := by
  obtain ⟨hΦ, -⟩ := AC.frameIn_of_callAt hr hx hc
  have opt : ∀ C, (∃ CV, AC.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) →
      ∃ s CV, (AC.ResultAt tr x i s C CV ∧
        ¬ AC.conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) C) ∨
        AC.OptimisticLockAt tr x i s C CV :=
    fun C ⟨CV, h⟩ => ⟨_, CV, Or.inr h⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits
  rw [hA] at opt
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (writes_onTick x A ℓ.frame _).mono fun C h => ?_
    rcases h with ⟨e, he', hsel⟩ | ⟨ht, hs0, hj, hC, hnv⟩
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
    · have hu : AC.UpdateAt tr x i (sp.slot (tr.time i) - 1) ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        conv_lhs => rw [ht]
        simp only [ACParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      exact ⟨_, _, Or.inl ⟨⟨ℓ, hu, hA ▸ hC, rfl⟩, hA ▸ hnv⟩⟩
  | proposal => exact .of_eq (proposal_latestConfirmed A _ _)
  | toFG => exact .of_eq (toFG_latestConfirmed A _ _)
  | message m =>
    rw [hcall] at hemits
    have h₁ := writes_optimistic (AC.admitVote sp A (tr.time i) m) ℓ.frame (tr.time i)
      (admitVote_latestConfirmed _ _ _)
    refine (h₁.mono fun C h => ?_).trans ((writes_tryVote x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := writes_optimistic (AC.blockReceipt sp A (tr.time i) B) ℓ.frame (tr.time i)
      (blockReceipt_latestConfirmed _ _ _)
    refine (h₁.mono fun C h => ?_).trans ((writes_tryVote x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | restart =>
    exact .of_eq ((AC.restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.2.1

/-- Forgetting the regular update's non-veto guard gives the original write interface. -/
theorem call_writes {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    Writes ℓ.frame (fun C => ∃ s CV, AC.ResultAt tr x i s C CV ∨ AC.OptimisticLockAt tr x i s C CV)
      (tr.state x i).latestConfirmed (tr.post i).latestConfirmed := by
  refine (call_writes_guarded hr hx hc).mono ?_
  rintro C ⟨s, CV, h | h⟩
  · exact ⟨s, CV, Or.inl h.1⟩
  · exact ⟨s, CV, Or.inr h⟩

/-! ### The record and its fast lock inside one call -/

/-- A lock that every lock function keeps at `(Φ, t)`: of the previous slot or later, live at
`t`, on a block of the tree that is its own viable ancestor. -/
def KeepOK (Φ : AC.Frm sp.n FGP) (t : Time) (l : AC.Lock) : Prop :=
  sp.slot t ≤ l.slot + 1 ∧ l.LiveAt sp t ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧
    (B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot)

/-- `A'` holds every lock of `A` that the lock functions keep. -/
def KeepAll (Φ : AC.Frm sp.n FGP) (t : Time) (A A' : AC.ACState sp.n) : Prop :=
  ∀ l ∈ A.locks, KeepOK Φ t l → l ∈ A'.locks

theorem keepOK_iff {Φ : AC.Frm sp.n FGP} {t : Time} {l : AC.Lock} :
    KeepOK Φ t l ↔ sp.slot t ≤ l.slot + 1 ∧ l.LiveAt sp t ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧
      (B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) := Iff.rfl

theorem keepAll_iff {Φ : AC.Frm sp.n FGP} {t : Time} {A A' : AC.ACState sp.n} :
    KeepAll Φ t A A' ↔ ∀ l ∈ A.locks, KeepOK Φ t l → l ∈ A'.locks := Iff.rfl

theorem KeepAll.of_eq {Φ : AC.Frm sp.n FGP} {t : Time} {A A' : AC.ACState sp.n}
    (h : A'.locks = A.locks) : KeepAll Φ t A A' := fun _ hl _ => h ▸ hl

theorem KeepAll.trans {Φ : AC.Frm sp.n FGP} {t : Time} {A B C : AC.ACState sp.n}
    (h₁ : KeepAll Φ t A B) (h₂ : KeepAll Φ t B C) : KeepAll Φ t A C :=
  fun l hl hk => h₂ l (h₁ l hl hk) hk

theorem live_keep {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {L : Set AC.Lock}
    {l : AC.Lock} (hl : l ∈ L) (hk : KeepOK Φ t l) : l ∈ AC.liveLocks sp L Φ t := by
  obtain ⟨-, hs, B, hB, hBr, hc⟩ := hk
  refine ⟨l, hl, B, hB, hBr, hs, ?_⟩
  rw [AC.viableAncestor_self hΦ hB hc, hBr]

theorem keepAll_addLocks {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {A A' : AC.ACState sp.n} {s : Nat} {N : Set (Nat × Bool × Nat)}
    (h : A'.locks = AC.addLocks sp A.locks Φ t s N) : KeepAll Φ t A A' :=
  fun _ hl hk => h ▸ live_keep hΦ (Or.inl hl) hk

theorem keepAll_unlock {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {A A' : AC.ACState sp.n} {V : AC.View sp.n}
    (h : A'.locks = AC.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) V) : KeepAll Φ t A A' := by
  intro l hl hk
  rw [h]
  obtain ⟨B, hB, hBr, -⟩ := hk.2.2
  refine ⟨l, live_keep hΦ hl hk, B, hB, hBr, ?_⟩
  have : ¬ ((l.slot : Int) < (sp.slot t : Int) - 1) := by have := hk.1; omega
  simp only [this, ↓reduceIte]

/-- The record of a state inside a call from the record `r₀`: unchanged, or the root of a block
`C` of the tree that the call wrote, with `Res C` (a result), or with `Opt C` (an optimistic
selection) and the fast lock of the slot on the viable ancestor of `C`. -/
def RecLock (Φ : AC.Frm sp.n FGP) (t : Time) (r₀ : Nat)
    (Res Opt : AC.Blk sp.n FGP → Prop) (A : AC.ACState sp.n) : Prop :=
  A.latestConfirmed = r₀ ∨ ∃ C ∈ Φ.tree, A.latestConfirmed = C.root ∧
    (Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
      (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : AC.Lock) ∈ A.locks))

theorem recLock_iff {Φ : AC.Frm sp.n FGP} {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n} :
    RecLock Φ t r₀ Res Opt A ↔ A.latestConfirmed = r₀ ∨ ∃ C ∈ Φ.tree, A.latestConfirmed = C.root ∧
      (Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
        (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : AC.Lock) ∈ A.locks)) := Iff.rfl

theorem RecLock.mono {Φ : AC.Frm sp.n FGP} {t : Time} {r₀ : Nat}
    {Res Opt Res' Opt' : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hR : ∀ C, Res C → Res' C) (hO : ∀ C, Opt C → Opt' C) :
    RecLock Φ t r₀ Res' Opt' A :=
  h.imp_right fun ⟨C, hC, hCr, h'⟩ => ⟨C, hC, hCr, h'.imp (hR C) fun ⟨h₁, h₂⟩ => ⟨hO C h₁, h₂⟩⟩

theorem RecLock.keep {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A A' : AC.ACState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hk : KeepAll Φ t A A')
    (hr : A'.latestConfirmed = A.latestConfirmed) : RecLock Φ t r₀ Res Opt A' := by
  rcases h with h | ⟨C, hC, hCr, hres | ⟨hopt, hl⟩⟩
  · exact Or.inl (hr.trans h)
  · exact Or.inr ⟨C, hC, hr.trans hCr, Or.inl hres⟩
  · obtain ⟨hva, -⟩ := AC.viableAncestor_anc hΦ hC
    obtain ⟨e, he, hl⟩ := hl
    exact Or.inr ⟨C, hC, hr.trans hCr, Or.inr ⟨hopt, e, he, hk _ hl ⟨Nat.le_succ _,
      (Nat.le_add_right _ 2).trans he, _, hva, rfl,
      (AC.viableAncestor_spec hΦ hC).2.1.symm⟩⟩⟩

theorem ulc_rec (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (C : AC.Blk sp.n FGP) :
    (AC.updateLatestConfirmed sp A Φ C).latestConfirmed = A.latestConfirmed ∨
      (AC.updateLatestConfirmed sp A Φ C).latestConfirmed = C.root := by
  unfold AC.updateLatestConfirmed
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem RecLock.write {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A A' : AC.ACState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hk : KeepAll Φ t A A') {C : AC.Blk sp.n FGP}
    (hC : C ∈ Φ.tree)
    (hr : A'.latestConfirmed = A.latestConfirmed ∨ A'.latestConfirmed = C.root)
    (hnew : Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
      (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : AC.Lock) ∈ A'.locks)) :
    RecLock Φ t r₀ Res Opt A' :=
  hr.elim (h.keep hΦ hk) fun h' => Or.inr ⟨C, hC, h', hnew⟩

theorem reclock_optimistic {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) :
    KeepAll Φ t A (AC.optimisticConfirmation sp A Φ t) ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨ AC.optimisticSelect sp A Φ t = some B)
        (AC.optimisticConfirmation sp A Φ t) := by
  unfold AC.optimisticConfirmation
  rcases hs : AC.optimisticSelect sp A Φ t with _ | B
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  · have hB := hs
    unfold AC.optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    have hBt := (AC.deepest_mem hB).1.1
    have hk : KeepAll Φ t A (AC.updateLatestConfirmed sp
        { A with locks := (AC.addLocks sp A.locks Φ t (sp.slot t)
      {(B.root, true, AC.fastExpiry sp A.locks Φ t (sp.slot t))}) } Φ B) :=
      keepAll_addLocks hΦ (by rw [AC.updateLatestConfirmed_keeps_locks])
    refine ⟨hk, (h.mono (fun _ h => h) fun _ h => Or.inl h).write hΦ hk hBt (ulc_rec _ _ _)
      (Or.inr ⟨Or.inr rfl, ?_⟩)⟩
    have he := AC.le_fastExpiry (sp := sp) A.locks Φ t (sp.slot t) hcap le_rfl
    refine ⟨_, he, ?_⟩
    rw [AC.updateLatestConfirmed_keeps_locks]
    exact ⟨⟨B.root, sp.slot t, true, _⟩, Or.inr ⟨_, Set.mem_singleton _, rfl⟩, B, hBt, rfl,
      (Nat.le_add_right _ 2).trans he, rfl⟩

theorem reclock_opt_admit {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A A₂ : AC.ACState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (hk : KeepAll Φ t A A₂) (hr : A₂.latestConfirmed = A.latestConfirmed) (v : Vote sp.n)
    (hcap : ∀ l ∈ A₂.locks, l.expiry ≤ l.slot + sp.k) :
    KeepAll Φ t A (AC.optimisticConfirmation sp (AC.admitVote sp A₂ t v) Φ t) ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨
          AC.optimisticSelect sp (AC.admitVote sp A₂ t v) Φ t = some B)
        (AC.optimisticConfirmation sp (AC.admitVote sp A₂ t v) Φ t) := by
  have hk' : KeepAll Φ t A (AC.admitVote sp A₂ t v) :=
    hk.trans (KeepAll.of_eq (AC.admitVote_locks_eq _ _ _))
  obtain ⟨hk₂, hr₂⟩ := reclock_optimistic hΦ
    (h.keep hΦ hk' ((admitVote_latestConfirmed _ _ _).trans hr))
    (by rw [AC.admitVote_locks_eq]; exact hcap)
  exact ⟨hk'.trans hk₂, hr₂⟩

theorem reclock_tryVote {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (x : Fin sp.n) (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) :
    KeepAll Φ t A (AC.tryVote sp x A Φ t).1 ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨ ∃ e ∈ (AC.tryVote sp x A Φ t).2,
          AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some B)
        (AC.tryVote sp x A Φ t).1 := by
  unfold AC.tryVote
  dsimp only
  by_cases h₁ : ¬ AC.joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t
  · rw [ite_eq_left h₁]
    exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  rw [ite_eq_right h₁]
  by_cases h₂ : t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ AC.voteReady sp A Φ (sp.slot t))
  · rw [ite_eq_left h₂]
    exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  rw [ite_eq_right h₂]
  by_cases h₃ : 0 < sp.slot t
  · rw [ite_eq_left h₃]
    by_cases hm : A.mayVote (sp.slot t) = true
    · simp only [hm, ite_true]
      refine (reclock_opt_admit hΦ h ?_ ?_ _ ?_).imp id fun hr => hr.mono
        (fun _ h => h) fun B h => h.imp_right fun h => ⟨_, List.mem_singleton_self _, h⟩
      · exact keepAll_unlock hΦ rfl
      · rfl
      · rintro _ ⟨l, ⟨l₀, hl₀, B, hB, hr, ht, rfl⟩, hs, B₁, hB₁, hr₁, rfl⟩
        have := hcap l₀ hl₀
        split_ifs <;> exact this
    · simp only [hm, Bool.false_eq_true, ite_false]
      refine ⟨keepAll_unlock hΦ rfl, RecLock.mono ?_ (fun _ h => h) fun _ h => Or.inl h⟩
      exact h.keep hΦ (keepAll_unlock hΦ rfl) rfl
  · rw [ite_eq_right h₃]
    by_cases hm : A.mayVote (sp.slot t) = true
    · simp only [hm, ite_true]
      refine (reclock_opt_admit hΦ h ?_ ?_ _ ?_).imp id fun hr => hr.mono
        (fun _ h => h) fun B h => h.imp_right fun h => ⟨_, List.mem_singleton_self _, h⟩
      · exact KeepAll.of_eq rfl
      · rfl
      · exact hcap
    · simp only [hm, Bool.false_eq_true, ite_false]
      exact ⟨KeepAll.of_eq rfl,
        (h.keep hΦ (KeepAll.of_eq rfl) rfl).mono
          (fun _ h => h) fun _ h => Or.inl h⟩

theorem reclock_update {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (s : Nat) :
    KeepAll Φ t A (AC.updateConfirmation sp A Φ t s) ∧
      RecLock Φ t r₀ (fun C => Res C ∨ AC.getConfirmation sp A Φ s = some C) Opt
        (AC.updateConfirmation sp A Φ t s) := by
  unfold AC.updateConfirmation
  dsimp only
  rcases hC : AC.getConfirmation sp A Φ s with _ | C
  · exact ⟨KeepAll.of_eq rfl, (h.mono (fun _ h => Or.inl h) fun _ h => h).keep hΦ
      (KeepAll.of_eq rfl) rfl⟩
  · dsimp only
    -- a veto keeps the record; the new locks never drop a kept one
    split_ifs
    · exact ⟨keepAll_addLocks hΦ rfl, (h.mono (fun _ h => Or.inl h) fun _ h => h).keep hΦ
        (keepAll_addLocks hΦ rfl) rfl⟩
    all_goals
      refine ⟨?_, (h.mono (fun _ h => Or.inl h) fun _ h => h).write hΦ ?_
        (AC.deepest_mem hC).1.1 (ulc_rec _ _ _) (Or.inl (Or.inr rfl))⟩ <;>
      exact keepAll_addLocks hΦ (by rw [AC.updateLatestConfirmed_keeps_locks])

theorem reclock_onTick {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : AC.Blk sp.n FGP → Prop} {A : AC.ACState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (x : Fin sp.n) (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) :
    KeepAll Φ t A (AC.acOnTick sp x A Φ t).1 ∧
      RecLock Φ t r₀ (fun C => Res C ∨ (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧
          AC.joined sp A t ∧ AC.getConfirmation sp A Φ (sp.slot t - 1) = some C))
        (fun B => Opt B ∨ ∃ e ∈ (AC.acOnTick sp x A Φ t).2,
          AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some B)
        (AC.acOnTick sp x A Φ t).1 := by
  unfold AC.acOnTick
  dsimp only
  by_cases hj : AC.joined sp A t
  · rw [ite_eq_right (not_not_intro hj)]
    by_cases hu : t = sp.ts (sp.slot t) + sp.Δ
    · rw [ite_eq_left hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · exfalso
        have := sp.toParams.hΔ
        linarith [ht.1.symm.trans hu]
      · rw [ite_eq_right ht]
        exact (reclock_tryVote hΦ h x hcap).imp id fun hr => hr.mono
          (fun _ h => Or.inl h) fun _ h => h
    · rw [ite_eq_right hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · rw [ite_eq_left ht]
        exact (reclock_update hΦ h _).imp id fun hr => hr.mono
          (fun C h => h.imp_right fun h => ⟨ht.1, ht.2, hj, h⟩) fun _ h => Or.inl h
      · rw [ite_eq_right ht]
        exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => Or.inl h) fun _ h => Or.inl h⟩
  · rw [ite_eq_left hj]
    exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => Or.inl h) fun _ h => Or.inl h⟩

theorem proposal_keeps {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : AC.ACState sp.n)
    (t : Time) : KeepAll Φ t A (AC.acProposal sp A Φ t).1 := by
  unfold AC.acProposal
  dsimp only
  split_ifs
  · exact keepAll_unlock hΦ rfl
  · exact KeepAll.of_eq rfl

theorem toFG_locks (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) :
    (AC.acToFG sp A Φ t).1.locks = A.locks := by
  unfold AC.acToFG
  split_ifs <;> rfl

/-- **The record and its fast lock across a call**: the call keeps the keepable locks, and leaves
the record unchanged or names a block of the frame that it wrote, as a result of its update, or
as the selection of one of its optimistic checks with that slot's fast lock on its viable
ancestor. -/
theorem call_reclock {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    KeepAll ℓ.frame (tr.time i) (tr.state x i) (tr.post i) ∧
      RecLock ℓ.frame (tr.time i) (tr.state x i).latestConfirmed
        (fun C => ∃ s CV, AC.ResultAt tr x i s C CV)
        (fun C => ∃ CV, AC.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) (tr.post i) := by
  obtain ⟨hΦ, -⟩ := AC.frameIn_of_callAt hr hx hc
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  have hwf := AC.locksWF_state hr hini hx i
  generalize hA : tr.state x i = A at hpost hemits
  rw [hA] at hwf
  have h₀ : RecLock ℓ.frame (tr.time i) A.latestConfirmed (fun _ => False) (fun _ => False) A :=
    Or.inl rfl
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (reclock_onTick hΦ h₀ x (fun l hl => hwf.cap hl)).imp id
      fun h => h.mono (fun C h => ?_) fun C h => ?_
    · obtain ⟨ht, hs0, hj, hC⟩ := h.resolve_left id
      have hu : AC.UpdateAt tr x i (sp.slot (tr.time i) - 1) ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        conv_lhs => rw [ht]
        simp only [ACParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      exact ⟨_, _, ℓ, hu, hA ▸ hC, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h.resolve_left id
      exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | proposal =>
    exact ⟨proposal_keeps hΦ A _, h₀.mono (fun _ h => h.elim) (fun _ h => h.elim) |>.keep hΦ
      (proposal_keeps hΦ A _) (proposal_latestConfirmed A _ _)⟩
  | toFG =>
    exact ⟨KeepAll.of_eq (toFG_locks A _ _), h₀.mono (fun _ h => h.elim) (fun _ h => h.elim)
      |>.keep hΦ (KeepAll.of_eq (toFG_locks A _ _)) (toFG_latestConfirmed A _ _)⟩
  | message m =>
    rw [hcall] at hemits
    obtain ⟨hk₁, hr₁⟩ := reclock_opt_admit hΦ h₀ (KeepAll.of_eq rfl) rfl m
      (fun l hl => hwf.cap hl)
    have hwf₁ : AC.LocksWF sp (AC.admitVote sp A (tr.time i) m).locks := by
      rw [AC.admitVote_locks_eq]; exact hwf
    obtain ⟨hk₂, hr₂⟩ := reclock_tryVote hΦ hr₁ x
      (fun l hl => (hwf₁.optimisticConfirmation ℓ.frame (tr.time i)).cap hl)
    refine ⟨hk₁.trans hk₂, hr₂.mono (fun _ h => h.elim) fun C h => ?_⟩
    rcases h with (h | h) | ⟨e, he', hsel⟩
    · exact h.elim
    · exact ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, rfl, h, rfl⟩
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have hk₀ : KeepAll ℓ.frame (tr.time i) A (AC.blockReceipt sp A (tr.time i) B) :=
      KeepAll.of_eq (AC.blockReceipt_locks _ _ _)
    obtain ⟨hk₁, hr₁⟩ := reclock_optimistic hΦ
      (h₀.keep hΦ hk₀ (blockReceipt_latestConfirmed _ _ _))
      (by rw [AC.blockReceipt_locks]; exact fun l hl => hwf.cap hl)
    have hwf₁ : AC.LocksWF sp (AC.blockReceipt sp A (tr.time i) B).locks := by
      rw [AC.blockReceipt_locks]; exact hwf
    obtain ⟨hk₂, hr₂⟩ := reclock_tryVote hΦ hr₁ x
      (fun l hl => (hwf₁.optimisticConfirmation ℓ.frame (tr.time i)).cap hl)
    refine ⟨hk₀.trans (hk₁.trans hk₂), hr₂.mono (fun _ h => h.elim) fun C h => ?_⟩
    rcases h with (h | h) | ⟨e, he', hsel⟩
    · exact h.elim
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, rfl, h, rfl⟩
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | restart =>
    have hrs := (AC.restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)
    exact ⟨KeepAll.of_eq hrs.2.1, Or.inl hrs.2.2.1⟩

/-- A changed record has an actual writer in this call. An optimistic writer also
leaves its normalized fast lock in the post-state; no read invariant is required. -/
theorem call_record_writer {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hne : (tr.post i).latestConfirmed ≠ (tr.state x i).latestConfirmed) :
    ∃ C ∈ ℓ.frame.tree, (tr.post i).latestConfirmed = C.root ∧
      ((∃ s CV, AC.ResultAt tr x i s C CV) ∨
        ((∃ CV, AC.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) ∧
          ∃ e, (⟨(ℓ.frame.viableAncestor C).root, sp.slot (tr.time i), true, e⟩ : AC.Lock) ∈
            (tr.post i).locks)) :=
  ((call_reclock hr hini hx hc).2.resolve_left hne).imp fun _ ⟨hC, hr, h⟩ =>
    ⟨hC, hr, h.imp_right fun ⟨ho, e, _, hl⟩ => ⟨ho, e, hl⟩⟩

end Writes

end Consensus.Goldilocks.Compose

end
