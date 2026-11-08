module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtACEnv
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: the pre-`b` frontier over AC traces (vocabulary and first facts)

The frontier of the Sleepy record invariant up to a horizon `b`
(`Compose.SleepyInvariantUpTo`, `Compose.sleepy_invariant_before`) has an AC content: the
origins within `b` compare, the honest votes at times `≤ b` extend the origins of earlier labels,
and the records and stored locks at the cuts within `b` name genesis or blocks below those
origins. This module states that content over an AC trace of the SA with the unlock given at a
write mode (`ACRunU wm u`), read on the trace itself rather than on a composite run's projection:

* the origins within `b` (`OriginWithinAC`, the body of `Compose.OriginWithin` read on `tr`), the
  ancestor closure of their chain (`OnOriginChainWithinAC`), the bounded frontier
  (`OriginsBelowAC`, `VotesBelowAC`) and the conclusion (`FrontierAC`);
* the deadline-cut service `SyncUntilAC` gives the service before `b` that the frontier reads
  (`SyncUntilAC.service`): every delivery the frontier uses has its receiver's deadline at or
  before `b` (so within the `b + 1` cut);
* `f < n/2` from `f < h_0` (`two_faults_lt_of_faultBound`);
* the restarts of an honest voter and of an honest updater (`vote_restartsAC`,
  `update_restartsAC`), and, from the tick duty, the slot-`s` vote of an honest validator awake
  and joined at `t_s + Δ` (`vote_of_awake_joinedAC`). -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### Vocabulary -/

/-- **An origin of label `s` within `b`** (`Compose.OriginWithin`, read on the AC trace): the
result `C` of an honest joined update of slot `s`, or the block an honest optimistic check of
slot `s` selects, at a cut at a time `≤ b`. -/
def OriginWithinAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (C : Blk sp.n FGP) (s : Nat)
    (b : Time) : Prop :=
  ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧ (ResultAt tr x i s C CV ∨ OptimisticLockAt tr x i s C CV)

/-- `B` is genesis or an ancestor (inside `U`) of an origin within `b`. -/
def OnOriginChainWithinAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (B : Blk sp.n FGP) (b : Time) : Prop :=
  B.root = sp.genesisRoot ∨ ∃ C s, OriginWithinAC tr H C s b ∧ Anc U B C

/-- **`P_s` up to `b`**: the origins within `b` of labels below `s` are pairwise compatible. -/
def OriginsBelowAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (s : Nat) (b : Time) : Prop :=
  ∀ C j C' j', j < s → j' < s → OriginWithinAC tr H C j b → OriginWithinAC tr H C' j' b →
    Compatible U C C'

/-- **`V_s` up to `b`**: every honest vote at a time `≤ b` of a slot `m` with `j < m ≤ s` extends
every origin within `b` of label `j`. -/
def VotesBelowAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (s : Nat) (b : Time) : Prop :=
  ∀ C j, OriginWithinAC tr H C j b → ∀ y ∈ H, ∀ i e, VoteAt tr y i e → tr.time i ≤ b →
    j < e.msg.slot → e.msg.slot ≤ s → VoteExtends U e.msg C

/-- **The pre-`b` frontier over an AC trace**: the AC fields of `Compose.SleepyInvariantUpTo`
(S1 for the origins, S2 for the votes, and the record and lock parts of S1), stated over the AC
trace of the SA with ancestry inside `U`. The FG fields (`caches`, `sources`, `viable`) are
dropped: under trivial frames `Φ.F = fc_root` is genesis and every block of the tree is viable. -/
structure FrontierAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b : Time) : Prop where
  /-- S1: any two origins within `b` are compatible. -/
  origins_compatible : ∀ C s C' s', OriginWithinAC tr H C s b → OriginWithinAC tr H C' s' b →
    Compatible U C C'
  /-- S2: every honest vote at a time `≤ b` of a slot after the label of an origin within `b`
  extends it. -/
  vote_extends : ∀ C s, OriginWithinAC tr H C s b → ∀ y ∈ H, ∀ i e, VoteAt tr y i e →
    tr.time i ≤ b → s < e.msg.slot → VoteExtends U e.msg C
  /-- S1: at a cut within `b`, every honest record is genesis, or names a block of the frame of
  an earlier call of the node that is an origin within `b`. -/
  record : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) →
    (tr.state y i).latestConfirmed = sp.genesisRoot ∨
      ∃ C ∈ U, C.root = (tr.state y i).latestConfirmed ∧
        (∃ k < i, ∃ ℓ, tr.CallAt y k ℓ ∧ C ∈ ℓ.frame.tree) ∧ ∃ s, OriginWithinAC tr H C s b
  /-- S1: at a cut within `b`, every honest stored lock names a block of `U` on the chain of the
  origins within `b`. -/
  locks : ∀ y ∈ H, ∀ i, (∀ k < i, tr.time k ≤ b) → ∀ l ∈ (tr.state y i).locks,
    ∃ L ∈ U, L.root = l.block ∧ OnOriginChainWithinAC tr H U L b

variable {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

theorem originWithinAC_iff {C : Blk sp.n FGP} {s : Nat} {b : Time} :
    OriginWithinAC tr H C s b ↔ ∃ x ∈ H, ∃ i CV, tr.time i ≤ b ∧
      (ResultAt tr x i s C CV ∨ OptimisticLockAt tr x i s C CV) :=
  Iff.rfl

theorem onOriginChainWithinAC_iff {B : Blk sp.n FGP} {b : Time} :
    OnOriginChainWithinAC tr H U B b ↔
      B.root = sp.genesisRoot ∨ ∃ C s, OriginWithinAC tr H C s b ∧ Anc U B C :=
  Iff.rfl

theorem originsBelowAC_iff {s : Nat} {b : Time} :
    OriginsBelowAC tr H U s b ↔ ∀ C j C' j', j < s → j' < s → OriginWithinAC tr H C j b →
      OriginWithinAC tr H C' j' b → Compatible U C C' :=
  Iff.rfl

theorem votesBelowAC_iff {s : Nat} {b : Time} :
    VotesBelowAC tr H U s b ↔ ∀ C j, OriginWithinAC tr H C j b → ∀ y ∈ H, ∀ i e,
      VoteAt tr y i e → tr.time i ≤ b → j < e.msg.slot → e.msg.slot ≤ s →
        VoteExtends U e.msg C :=
  Iff.rfl

theorem OriginWithinAC.mono {C : Blk sp.n FGP} {s : Nat} {b b' : Time}
    (h : OriginWithinAC tr H C s b) (hb : b ≤ b') : OriginWithinAC tr H C s b' :=
  let ⟨x, hx, i, CV, hi, h⟩ := originWithinAC_iff.1 h
  originWithinAC_iff.2 ⟨x, hx, i, CV, hi.trans hb, h⟩

/-! ### Service, faults and slot arithmetic -/

/-- **The deadline-cut service gives the service before `b`**: a delivery owed when the
receiver's deadline is at most `b` is owed by `SyncUntilAC` (whose cut is `b + 1`), so served in
the sense of `MessageServedBefore`. The no-restart clause of `SyncUntilAC.message` is not used:
the frontier's retention across restarts comes from the restart bounds of the voters and the
updaters (`vote_restartsAC`, `update_restartsAC`). -/
theorem SyncUntilAC.service {b : Time} (h : SyncUntilAC tr H U b) :
    ServiceWindowBefore H U 0 b tr where
  message x hx i v hv _ y hy j ℓ hc hdb hdl := by
    obtain ⟨k, hk, h1, h2, h3, -⟩ := h.message x hx i v hv y hy j ℓ hc hdl (by linarith)
    exact (messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k, hk, h1, h2, h3⟩)
  relay x hx i B hB _ y hy j ℓ hc hdb hdl hanc :=
    h.relay x hx i B hB y hy j ℓ hc hdl (by linarith) hanc

/-- `f < n/2` from `f < h_t` at some `t`. -/
theorem two_faults_lt_of_faultBound {t : Time} (h : FaultBound tr H t) : 2 * Hᶜ.ncard < sp.n := by
  have hle : honestAwakeJoined tr H t ≤ H.ncard := Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold FaultBound at h
  omega

theorem ts_nonnegAC (s : Nat) : (0 : Time) ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  simp only [SAParams.ts]
  exact mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (Int.natCast_nonneg s)

theorem ts_le_tsAC {s s' : Nat} (h : s ≤ s') : sp.ts s ≤ sp.ts s' :=
  (ts_le_iff sp).2 (by exact_mod_cast h)

theorem ts_succ₂AC (s : Nat) : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot of `t_s + Δ` is `s`. -/
theorem slot_ts_deltaAC (s : Nat) : sp.slot (sp.ts s + sp.Δ) = s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  exact slot_of_mem sp s (by linarith) (by rw [ts_succ]; linarith)

/-! ### Restarts of voters and updaters -/

variable {wm : WriteMode} {u : Nat → Set Lock} {proposer : Nat → Fin sp.n}

/-- At an honest slot-`(s+1)` vote, the voter's restarts up to the vote were at or before `t_s`,
and the vote is cast from `t_{s+1} = t_s + 4Δ` on. -/
theorem vote_restartsAC (hr : ACLocalRunU wm u H U tr) {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s) ∧ sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  obtain ⟨-, hslot, hjoin, -⟩ := castAt_specU hr hy hc
  have hti : sp.slot (tr.time i) = s + 1 := hslot ▸ hs
  have hjp : joined sp (tr.post i) (tr.time i) := by
    unfold joined; rw [restartTime_of_castAtU hr hy hc]; exact hjoin
  refine ⟨fun c hc' hrc => ?_, ?_⟩
  · have h := ((joined_awakeU sp) _ ro H _ tr hr y hy i ℓ hc.1 hjp).2 c hc' hrc
    rw [hti, show (((s + 1 : Nat) : Int) - 1) = (s : Int) by push_cast; ring] at h
    exact h
  · have h := (ts_le_iff_le_slot sp (hr.time_nonneg i) ((s + 1 : Nat) : Int)).2 (by rw [hti])
    rwa [ts_succ] at h

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before `t_s`. -/
theorem update_restartsAC (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n} (hX : X ∈ H)
    {i₀ s : Nat} {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) :
    ∀ k ≤ i₀, tr.RestartAt X k → tr.time k ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  obtain ⟨hcX, htick, hti₀, hjX⟩ := hupd
  have he := hr.exec i₀ ℓX hcX.2 (hcX.1 ▸ hX)
  rw [hcX.1, htick] at he
  have hj' : joined sp (tr.post i₀) (tr.time i₀) := by
    have hpost : tr.post i₀ = (acOnTickWithM sp wm X (u i₀)
        (tr.state X i₀) ℓX.frame (tr.time i₀)).1 :=
      (congrArg Prod.fst he).symm
    unfold joined; rw [hpost, onTick_restartTimeWith]; exact hjX
  have hsl : sp.slot (tr.time i₀) = s + 1 := by
    rw [hti₀]
    exact slot_of_mem sp (s + 1) (by rw [ts_succ]; linarith) (by rw [ts_succ₂AC]; linarith)
  intro k hk hrk
  have := ((joined_awakeU sp) FGP ro H U tr hr X hX i₀ ℓX hcX hj').2 k hk hrk
  rwa [hsl, hcast] at this

/-! ### The tick duty gives the votes -/

/-- **An honest validator awake and joined at `t_s + Δ` votes in slot `s`**, at or before
`t_s + Δ`: the tick duty runs its tick there, whose `try_vote` votes unless it voted in slot `s`
already. -/
theorem vote_of_awake_joinedAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hw : tr.awake y (sp.ts s + sp.Δ))
    (hj : JoinedAt tr y (sp.ts s + sp.Δ)) :
    ∃ k e, VoteAt tr y k e ∧ e.msg.slot = s ∧ tr.time k ≤ sp.ts s + sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 := ts_nonnegAC (sp := sp) s
  have hslot := slot_ts_deltaAC (sp := sp) s
  obtain ⟨i, ℓ, hc, hcall, hti⟩ := htick y hy _ (by linarith)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 1)
      (by simp only [SAParams.ts]; ring)) hw
  have hjs : joined sp (tr.state y i) (tr.time i) := by
    unfold joined
    rcases restartTime_stateU hr hy i with h | ⟨k, hk, hrk, h⟩
    · rw [h]; exact bot_le
    · rw [h, hti]
      exact WithBot.coe_le_coe.2 (hj k hrk (hti ▸ hr.time_mono hk.le))
  by_cases hv : (tr.state y i).votedSlot = sp.slot (tr.time i)
  · rw [hti, hslot] at hv
    obtain ⟨j, hj, e, hve, hes⟩ := vote_of_votedSlotU hr hy i s hv
    exact ⟨j, e, hve, hes, hti ▸ hr.time_mono hj.le⟩
  · have htv : tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ := by rw [hti, hslot]
    obtain ⟨e, he, hes⟩ := tryVote_votesWith (wm := wm) (L := u i) y ℓ.frame hjs hv htv
    have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1, hcall] at hx
    have hem : (acOnTickWithM sp wm y (u i) (tr.state y i) ℓ.frame (tr.time i)).2 = ℓ.emits :=
      congrArg Prod.snd hx
    have he' : e ∈ ℓ.emits := by
      rw [← hem]
      unfold acOnTickWithM
      simp only [hjs, not_true_eq_false, ↓reduceIte]
      rw [ite_eq_left htv]
      exact he
    refine ⟨i, e, ⟨ℓ, hc, he'⟩, ?_, hti.le⟩
    rw [hti, hslot] at hes
    exact_mod_cast hes

end Consensus.Goldilocks.Comparison

end
