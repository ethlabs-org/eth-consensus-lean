module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Sleepy
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
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
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: record writes inside one call

Which blocks one AC call can write as the record (`Writes`, `call_writes_guarded`,
`call_writes`), and that a changed record has an actual writer whose optimistic fast lock stays
stored (`call_record_writer`), with the keep and write toolkit (`KeepAll`, `RecLock`,
`call_reclock`) that `Compose/Sleepy/Served` builds the record step on. Split out of
`Compose/Sleepy/Served`, so that a new writer fact does not rebuild Served's cone. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### Record writes inside one call -/

section Writes

variable {FGP : Type} {sp : SAParams}

/-- The record moves from `r` to `r'` by a sequence of `update_latest_confirmed` writes with
candidates `C ∈ Φ.tree` satisfying `New`: each keeps the record when `C ⪯` it in the tree and
moves it to `C` otherwise. -/
def Writes (Φ : SA.Frm sp.n FGP) (New : SA.Blk sp.n FGP → Prop) : Nat → Nat → Prop :=
  Relation.ReflTransGen fun r r' => ∃ C ∈ Φ.tree, New C ∧
    ((SA.AncR Φ C r ∧ r' = r) ∨ (¬ SA.AncR Φ C r ∧ r' = C.root))

theorem writes_iff {Φ : SA.Frm sp.n FGP} {New : SA.Blk sp.n FGP → Prop} {r r' : Nat} :
    Writes Φ New r r' ↔ Relation.ReflTransGen (fun r r' => ∃ C ∈ Φ.tree, New C ∧
      ((SA.AncR Φ C r ∧ r' = r) ∨ (¬ SA.AncR Φ C r ∧ r' = C.root))) r r' := Iff.rfl

theorem Writes.mono {Φ : SA.Frm sp.n FGP} {New New' : SA.Blk sp.n FGP → Prop}
    {r r' : Nat} (h : Writes Φ New r r') (hN : ∀ C, New C → New' C) : Writes Φ New' r r' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨C, hC, hn, h'⟩ := hs
    exact ih.tail ⟨C, hC, hN C hn, h'⟩

theorem Writes.of_eq {Φ : SA.Frm sp.n FGP} {New : SA.Blk sp.n FGP → Prop} {r r' : Nat}
    (h : r' = r) : Writes Φ New r r' :=
  h ▸ .refl

theorem writes_update (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) {C : SA.Blk sp.n FGP}
    (hC : C ∈ Φ.tree) {New : SA.Blk sp.n FGP → Prop} (hN : New C) {r r' : Nat}
    (hr : A.latestConfirmed = r) (hr' : r' = (SA.updateLatestConfirmed sp A Φ C).latestConfirmed) :
    Writes Φ New r r' := by
  subst hr hr'
  refine Relation.ReflTransGen.single ⟨C, hC, hN, ?_⟩
  unfold SA.updateLatestConfirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

theorem admitVote_latestConfirmed (A : SA.SAState sp.n) (t : Time) (v : Vote sp.n) :
    (SA.admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold SA.admitVote
  split_ifs <;> rfl

theorem foldl_admit_latestConfirmed (t : Time) (l : List (Vote sp.n))
    (A : SA.SAState sp.n) :
    (l.foldl (fun A v => SA.admitVote sp A t v) A).latestConfirmed = A.latestConfirmed := by
  induction l generalizing A with
  | nil => rfl
  | cons v l ih => rw [List.foldl_cons, ih, admitVote_latestConfirmed]

theorem blockReceipt_latestConfirmed (A : SA.SAState sp.n) (t : Time)
    (B : SA.Blk sp.n FGP) : (SA.blockReceipt sp A t B).latestConfirmed = A.latestConfirmed := by
  unfold SA.blockReceipt
  rw [foldl_admit_latestConfirmed]

theorem writes_optimistic (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    {r : Nat} (hr : A.latestConfirmed = r) :
    Writes Φ (fun B => SA.optimisticSelect sp A Φ t = some B) r
      (SA.optimisticConfirmation sp A Φ t).latestConfirmed := by
  subst hr
  unfold SA.optimisticConfirmation
  rcases h : SA.optimisticSelect sp A Φ t with _ | B
  · exact .refl
  · have hB := h
    unfold SA.optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    refine writes_update { A with locks := (SA.addLocks sp A.locks Φ t (sp.slot t)
      {(B.root, true, SA.fastExpiry sp A.locks Φ t (sp.slot t))}) }
      Φ (SA.deepest_mem hB).1.1 ?_ rfl rfl
    rfl

theorem writes_tryVote (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun B => ∃ e ∈ (SA.tryVote sp x A Φ t).2,
        SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some B)
      A.latestConfirmed (SA.tryVote sp x A Φ t).1.latestConfirmed := by
  unfold SA.tryVote
  dsimp only
  split_ifs
  · exact .refl
  · exact .refl
  all_goals
    refine (writes_optimistic _ Φ t ?_).mono fun B hB => ⟨_, List.mem_singleton_self _, hB⟩
    rw [admitVote_latestConfirmed]

theorem writes_updateConfirmation (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    (s : Nat) :
    Writes Φ (fun C => SA.getConfirmation sp A Φ s = some C ∧
      ¬ SA.conflictsWithLock sp A.locks Φ t C) A.latestConfirmed
      (SA.updateConfirmation sp A Φ t s).latestConfirmed := by
  unfold SA.updateConfirmation
  dsimp only
  rcases hC : SA.getConfirmation sp A Φ s with _ | C
  · exact .refl
  · dsimp only
    split_ifs with hveto
    · exact .refl
    all_goals
      refine writes_update { A with saved := Function.update A.saved s ((some C).map Block.root) }
        Φ (SA.deepest_mem hC).1.1 ?_ rfl rfl
      exact ⟨rfl, hveto⟩

theorem writes_onTick (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun C => (∃ e ∈ (SA.acOnTick sp x A Φ t).2,
        SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some C) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ SA.joined sp A t ∧
          SA.getConfirmation sp A Φ (sp.slot t - 1) = some C ∧
          ¬ SA.conflictsWithLock sp A.locks Φ t C))
      A.latestConfirmed (SA.acOnTick sp x A Φ t).1.latestConfirmed := by
  unfold SA.acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · exact (writes_updateConfirmation A Φ t _).mono fun C h => Or.inr ⟨ht.1, ht.2, hj, h⟩
  · exact (writes_tryVote x A Φ t).mono fun C h => Or.inl h
  · exact .refl
  · exact .refl

theorem proposal_latestConfirmed (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : (SA.acProposal sp A Φ t).1.latestConfirmed = A.latestConfirmed := by
  unfold SA.acProposal
  dsimp only
  split_ifs <;> rfl

theorem toFG_latestConfirmed (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.acToFG sp A Φ t).1.latestConfirmed = A.latestConfirmed := by
  unfold SA.acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}
  {tr : SA.SATrace sp FGP ro}

/-- **The record writes of a call**: every candidate is the result of the call's update or the
selection of one of its optimistic checks. -/
theorem call_writes_guarded (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    Writes ℓ.frame (fun C => ∃ s CV,
      (SA.ResultAt tr x i s C CV ∧
        ¬ SA.conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) C) ∨
      SA.OptimisticLockAt tr x i s C CV)
      (tr.state x i).latestConfirmed (tr.post i).latestConfirmed := by
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hx hc
  have opt : ∀ C, (∃ CV, SA.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) →
      ∃ s CV, (SA.ResultAt tr x i s C CV ∧
        ¬ SA.conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) C) ∨
        SA.OptimisticLockAt tr x i s C CV :=
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
    · have hu : SA.UpdateAt tr x i (sp.slot (tr.time i) - 1) ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      exact ⟨_, _, Or.inl ⟨⟨ℓ, hu, hA ▸ hC, rfl⟩, hA ▸ hnv⟩⟩
  | proposal => exact .of_eq (proposal_latestConfirmed A _ _)
  | toFG => exact .of_eq (toFG_latestConfirmed A _ _)
  | message m =>
    rw [hcall] at hemits
    have h₁ := writes_optimistic (SA.admitVote sp A (tr.time i) m) ℓ.frame (tr.time i)
      (admitVote_latestConfirmed _ _ _)
    refine (h₁.mono fun C h => ?_).trans ((writes_tryVote x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := writes_optimistic (SA.blockReceipt sp A (tr.time i) B) ℓ.frame (tr.time i)
      (blockReceipt_latestConfirmed _ _ _)
    refine (h₁.mono fun C h => ?_).trans ((writes_tryVote x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | restart =>
    exact .of_eq ((SA.restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.2.1

/-- Forgetting the regular update's non-veto guard gives the original write interface. -/
theorem call_writes (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    Writes ℓ.frame (fun C => ∃ s CV, SA.ResultAt tr x i s C CV ∨ SA.OptimisticLockAt tr x i s C CV)
      (tr.state x i).latestConfirmed (tr.post i).latestConfirmed := by
  refine (call_writes_guarded hr hx hc).mono ?_
  rintro C ⟨s, CV, h | h⟩
  · exact ⟨s, CV, Or.inl h.1⟩
  · exact ⟨s, CV, Or.inr h⟩

/-! ### The record and its fast lock inside one call -/

/-- A lock that every lock function keeps at `(Φ, t)`: of the previous slot or later, live at
`t`, on a block of the tree that is its own viable ancestor. -/
def KeepOK (Φ : SA.Frm sp.n FGP) (t : Time) (l : SA.Lock) : Prop :=
  sp.slot t ≤ l.slot + 1 ∧ l.LiveAt sp t ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧
    (B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot)

/-- `A'` holds every lock of `A` that the lock functions keep. -/
def KeepAll (Φ : SA.Frm sp.n FGP) (t : Time) (A A' : SA.SAState sp.n) : Prop :=
  ∀ l ∈ A.locks, KeepOK Φ t l → l ∈ A'.locks

theorem keepOK_iff {Φ : SA.Frm sp.n FGP} {t : Time} {l : SA.Lock} :
    KeepOK Φ t l ↔ sp.slot t ≤ l.slot + 1 ∧ l.LiveAt sp t ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧
      (B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) := Iff.rfl

theorem keepAll_iff {Φ : SA.Frm sp.n FGP} {t : Time} {A A' : SA.SAState sp.n} :
    KeepAll Φ t A A' ↔ ∀ l ∈ A.locks, KeepOK Φ t l → l ∈ A'.locks := Iff.rfl

theorem KeepAll.of_eq {Φ : SA.Frm sp.n FGP} {t : Time} {A A' : SA.SAState sp.n}
    (h : A'.locks = A.locks) : KeepAll Φ t A A' := fun _ hl _ => h ▸ hl

theorem KeepAll.trans {Φ : SA.Frm sp.n FGP} {t : Time} {A B C : SA.SAState sp.n}
    (h₁ : KeepAll Φ t A B) (h₂ : KeepAll Φ t B C) : KeepAll Φ t A C :=
  fun l hl hk => h₂ l (h₁ l hl hk) hk

theorem live_keep {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {L : Set SA.Lock}
    {l : SA.Lock} (hl : l ∈ L) (hk : KeepOK Φ t l) : l ∈ SA.liveLocks sp L Φ t := by
  obtain ⟨-, hs, B, hB, hBr, hc⟩ := hk
  refine ⟨l, hl, B, hB, hBr, hs, ?_⟩
  rw [SA.viableAncestor_self hΦ hB hc, hBr]

theorem keepAll_addLocks {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {A A' : SA.SAState sp.n} {s : Nat} {N : Set (Nat × Bool × Nat)}
    (h : A'.locks = SA.addLocks sp A.locks Φ t s N) : KeepAll Φ t A A' :=
  fun _ hl hk => h ▸ live_keep hΦ (Or.inl hl) hk

theorem keepAll_unlock {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {A A' : SA.SAState sp.n} {V : SA.View sp.n}
    (h : A'.locks = SA.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) V) : KeepAll Φ t A A' := by
  intro l hl hk
  rw [h]
  obtain ⟨B, hB, hBr, -⟩ := hk.2.2
  refine ⟨l, live_keep hΦ hl hk, B, hB, hBr, ?_⟩
  have : ¬ ((l.slot : Int) < (sp.slot t : Int) - 1) := by have := hk.1; omega
  simp only [this, ↓reduceIte]

/-- The record of a state inside a call from the record `r₀`: unchanged, or the root of a block
`C` of the tree that the call wrote, with `Res C` (a result), or with `Opt C` (an optimistic
selection) and the fast lock of the slot on the viable ancestor of `C`. -/
def RecLock (Φ : SA.Frm sp.n FGP) (t : Time) (r₀ : Nat)
    (Res Opt : SA.Blk sp.n FGP → Prop) (A : SA.SAState sp.n) : Prop :=
  A.latestConfirmed = r₀ ∨ ∃ C ∈ Φ.tree, A.latestConfirmed = C.root ∧
    (Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
      (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : SA.Lock) ∈ A.locks))

theorem recLock_iff {Φ : SA.Frm sp.n FGP} {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n} :
    RecLock Φ t r₀ Res Opt A ↔ A.latestConfirmed = r₀ ∨ ∃ C ∈ Φ.tree, A.latestConfirmed = C.root ∧
      (Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
        (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : SA.Lock) ∈ A.locks)) := Iff.rfl

theorem RecLock.mono {Φ : SA.Frm sp.n FGP} {t : Time} {r₀ : Nat}
    {Res Opt Res' Opt' : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hR : ∀ C, Res C → Res' C) (hO : ∀ C, Opt C → Opt' C) :
    RecLock Φ t r₀ Res' Opt' A :=
  h.imp_right fun ⟨C, hC, hCr, h'⟩ => ⟨C, hC, hCr, h'.imp (hR C) fun ⟨h₁, h₂⟩ => ⟨hO C h₁, h₂⟩⟩

theorem RecLock.keep {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A A' : SA.SAState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hk : KeepAll Φ t A A')
    (hr : A'.latestConfirmed = A.latestConfirmed) : RecLock Φ t r₀ Res Opt A' := by
  rcases h with h | ⟨C, hC, hCr, hres | ⟨hopt, hl⟩⟩
  · exact Or.inl (hr.trans h)
  · exact Or.inr ⟨C, hC, hr.trans hCr, Or.inl hres⟩
  · obtain ⟨hva, -⟩ := SA.viableAncestor_anc hΦ hC
    obtain ⟨e, he, hl⟩ := hl
    exact Or.inr ⟨C, hC, hr.trans hCr, Or.inr ⟨hopt, e, he, hk _ hl ⟨Nat.le_succ _,
      (Nat.le_add_right _ 2).trans he, _, hva, rfl,
      (SA.viableAncestor_spec hΦ hC).2.1.symm⟩⟩⟩

theorem ulc_rec (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (C : SA.Blk sp.n FGP) :
    (SA.updateLatestConfirmed sp A Φ C).latestConfirmed = A.latestConfirmed ∨
      (SA.updateLatestConfirmed sp A Φ C).latestConfirmed = C.root := by
  unfold SA.updateLatestConfirmed
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem RecLock.write {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A A' : SA.SAState sp.n}
    (h : RecLock Φ t r₀ Res Opt A) (hk : KeepAll Φ t A A') {C : SA.Blk sp.n FGP}
    (hC : C ∈ Φ.tree)
    (hr : A'.latestConfirmed = A.latestConfirmed ∨ A'.latestConfirmed = C.root)
    (hnew : Res C ∨ (Opt C ∧ ∃ e, sp.slot t + 2 ≤ e ∧
      (⟨(Φ.viableAncestor C).root, sp.slot t, true, e⟩ : SA.Lock) ∈ A'.locks)) :
    RecLock Φ t r₀ Res Opt A' :=
  hr.elim (h.keep hΦ hk) fun h' => Or.inr ⟨C, hC, h', hnew⟩

theorem reclock_optimistic {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n} (h : RecLock Φ t r₀ Res Opt A) :
    KeepAll Φ t A (SA.optimisticConfirmation sp A Φ t) ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨ SA.optimisticSelect sp A Φ t = some B)
        (SA.optimisticConfirmation sp A Φ t) := by
  unfold SA.optimisticConfirmation
  rcases hs : SA.optimisticSelect sp A Φ t with _ | B
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  · have hB := hs
    unfold SA.optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    have hBt := (SA.deepest_mem hB).1.1
    have hk : KeepAll Φ t A (SA.updateLatestConfirmed sp
        { A with locks := (SA.addLocks sp A.locks Φ t (sp.slot t)
      {(B.root, true, SA.fastExpiry sp A.locks Φ t (sp.slot t))}) } Φ B) :=
      keepAll_addLocks hΦ (by rw [SA.updateLatestConfirmed_locks_eq])
    refine ⟨hk, (h.mono (fun _ h => h) fun _ h => Or.inl h).write hΦ hk hBt (ulc_rec _ _ _)
      (Or.inr ⟨Or.inr rfl, ?_⟩)⟩
    have he := SA.le_fastExpiry (sp := sp) A.locks Φ t (sp.slot t)
    refine ⟨_, he, ?_⟩
    rw [SA.updateLatestConfirmed_locks_eq]
    exact ⟨⟨B.root, sp.slot t, true, _⟩, Or.inr ⟨_, Set.mem_singleton _, rfl⟩, B, hBt, rfl,
      (Nat.le_add_right _ 2).trans he, rfl⟩

theorem reclock_opt_admit {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A A₂ : SA.SAState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (hk : KeepAll Φ t A A₂) (hr : A₂.latestConfirmed = A.latestConfirmed) (v : Vote sp.n) :
    KeepAll Φ t A (SA.optimisticConfirmation sp (SA.admitVote sp A₂ t v) Φ t) ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨
          SA.optimisticSelect sp (SA.admitVote sp A₂ t v) Φ t = some B)
        (SA.optimisticConfirmation sp (SA.admitVote sp A₂ t v) Φ t) := by
  have hk' : KeepAll Φ t A (SA.admitVote sp A₂ t v) :=
    hk.trans (KeepAll.of_eq (SA.admitVote_locks_eq _ _ _))
  obtain ⟨hk₂, hr₂⟩ := reclock_optimistic hΦ
    (h.keep hΦ hk' ((admitVote_latestConfirmed _ _ _).trans hr))
  exact ⟨hk'.trans hk₂, hr₂⟩

theorem reclock_tryVote {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (x : Fin sp.n) :
    KeepAll Φ t A (SA.tryVote sp x A Φ t).1 ∧
      RecLock Φ t r₀ Res (fun B => Opt B ∨ ∃ e ∈ (SA.tryVote sp x A Φ t).2,
          SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some B)
        (SA.tryVote sp x A Φ t).1 := by
  unfold SA.tryVote
  dsimp only
  split_ifs
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => h) fun _ h => Or.inl h⟩
  · refine (reclock_opt_admit hΦ h ?_ ?_ _).imp id fun hr => hr.mono
      (fun _ h => h) fun B h => h.imp_right fun h => ⟨_, List.mem_singleton_self _, h⟩
    · exact keepAll_unlock hΦ rfl
    · rfl
  · refine (reclock_opt_admit hΦ h ?_ ?_ _).imp id fun hr => hr.mono
      (fun _ h => h) fun B h => h.imp_right fun h => ⟨_, List.mem_singleton_self _, h⟩
    · exact KeepAll.of_eq rfl
    · rfl

theorem reclock_update {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (s : Nat) :
    KeepAll Φ t A (SA.updateConfirmation sp A Φ t s) ∧
      RecLock Φ t r₀ (fun C => Res C ∨ SA.getConfirmation sp A Φ s = some C) Opt
        (SA.updateConfirmation sp A Φ t s) := by
  unfold SA.updateConfirmation
  dsimp only
  rcases hC : SA.getConfirmation sp A Φ s with _ | C
  · exact ⟨KeepAll.of_eq rfl, (h.mono (fun _ h => Or.inl h) fun _ h => h).keep hΦ
      (KeepAll.of_eq rfl) rfl⟩
  · dsimp only
    -- a veto keeps the record; the new locks never drop a kept one
    split_ifs
    · exact ⟨keepAll_addLocks hΦ rfl, (h.mono (fun _ h => Or.inl h) fun _ h => h).keep hΦ
        (keepAll_addLocks hΦ rfl) rfl⟩
    all_goals
      refine ⟨?_, (h.mono (fun _ h => Or.inl h) fun _ h => h).write hΦ ?_
        (SA.deepest_mem hC).1.1 (ulc_rec _ _ _) (Or.inl (Or.inr rfl))⟩ <;>
      exact keepAll_addLocks hΦ (by rw [SA.updateLatestConfirmed_locks_eq])

theorem reclock_onTick {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {r₀ : Nat}
    {Res Opt : SA.Blk sp.n FGP → Prop} {A : SA.SAState sp.n} (h : RecLock Φ t r₀ Res Opt A)
    (x : Fin sp.n) :
    KeepAll Φ t A (SA.acOnTick sp x A Φ t).1 ∧
      RecLock Φ t r₀ (fun C => Res C ∨ (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧
          SA.joined sp A t ∧ SA.getConfirmation sp A Φ (sp.slot t - 1) = some C))
        (fun B => Opt B ∨ ∃ e ∈ (SA.acOnTick sp x A Φ t).2,
          SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some B)
        (SA.acOnTick sp x A Φ t).1 := by
  unfold SA.acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · exact (reclock_update hΦ h _).imp id fun hr => hr.mono
      (fun C h => h.imp_right fun h => ⟨ht.1, ht.2, hj, h⟩) fun _ h => Or.inl h
  · exact (reclock_tryVote hΦ h x).imp id fun hr => hr.mono (fun _ h => Or.inl h) fun _ h => h
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => Or.inl h) fun _ h => Or.inl h⟩
  · exact ⟨KeepAll.of_eq rfl, h.mono (fun _ h => Or.inl h) fun _ h => Or.inl h⟩

theorem proposal_keeps {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n)
    (t : Time) : KeepAll Φ t A (SA.acProposal sp A Φ t).1 := by
  unfold SA.acProposal
  dsimp only
  split_ifs
  · exact keepAll_unlock hΦ rfl
  · exact KeepAll.of_eq rfl

theorem toFG_locks (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.acToFG sp A Φ t).1.locks = A.locks := by
  unfold SA.acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-- **The record and its fast lock across a call**: the call keeps the keepable locks, and leaves
the record unchanged or names a block of the frame that it wrote, as a result of its update, or
as the selection of one of its optimistic checks with that slot's fast lock on its viable
ancestor. -/
theorem call_reclock (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    KeepAll ℓ.frame (tr.time i) (tr.state x i) (tr.post i) ∧
      RecLock ℓ.frame (tr.time i) (tr.state x i).latestConfirmed
        (fun C => ∃ s CV, SA.ResultAt tr x i s C CV)
        (fun C => ∃ CV, SA.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) (tr.post i) := by
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hx hc
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits
  have h₀ : RecLock ℓ.frame (tr.time i) A.latestConfirmed (fun _ => False) (fun _ => False) A :=
    Or.inl rfl
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (reclock_onTick hΦ h₀ x).imp id fun h => h.mono (fun C h => ?_) fun C h => ?_
    · obtain ⟨ht, hs0, hj, hC⟩ := h.resolve_left id
      have hu : SA.UpdateAt tr x i (sp.slot (tr.time i) - 1) ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
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
    obtain ⟨hk₂, hr₂⟩ := reclock_tryVote hΦ hr₁ x
    refine ⟨hk₁.trans hk₂, hr₂.mono (fun _ h => h.elim) fun C h => ?_⟩
    rcases h with (h | h) | ⟨e, he', hsel⟩
    · exact h.elim
    · exact ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, rfl, h, rfl⟩
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have hk₀ : KeepAll ℓ.frame (tr.time i) A (SA.blockReceipt sp A (tr.time i) B) :=
      KeepAll.of_eq (SA.blockReceipt_locks _ _ _)
    obtain ⟨hk₁, hr₁⟩ := reclock_optimistic hΦ
      (h₀.keep hΦ hk₀ (blockReceipt_latestConfirmed _ _ _))
    obtain ⟨hk₂, hr₂⟩ := reclock_tryVote hΦ hr₁ x
    refine ⟨hk₀.trans (hk₁.trans hk₂), hr₂.mono (fun _ h => h.elim) fun C h => ?_⟩
    rcases h with (h | h) | ⟨e, he', hsel⟩
    · exact h.elim
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, rfl, h, rfl⟩
    · exact ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | restart =>
    have hrs := (SA.restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)
    exact ⟨KeepAll.of_eq hrs.2.1, Or.inl hrs.2.2.1⟩

/-- A changed record has an actual writer in this call. An optimistic writer also
leaves its normalized fast lock in the post-state; no read invariant is required. -/
theorem call_record_writer (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hne : (tr.post i).latestConfirmed ≠ (tr.state x i).latestConfirmed) :
    ∃ C ∈ ℓ.frame.tree, (tr.post i).latestConfirmed = C.root ∧
      ((∃ s CV, SA.ResultAt tr x i s C CV) ∨
        ((∃ CV, SA.OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) ∧
          ∃ e, (⟨(ℓ.frame.viableAncestor C).root, sp.slot (tr.time i), true, e⟩ : SA.Lock) ∈
            (tr.post i).locks)) :=
  ((call_reclock hr hx hc).2.resolve_left hne).imp fun _ ⟨hC, hr, h⟩ =>
    ⟨hC, hr, h.imp_right fun ⟨ho, e, _, hl⟩ => ⟨ho, e, hl⟩⟩

end Writes

end Consensus.Goldilocks.Compose

end
