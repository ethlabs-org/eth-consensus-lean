module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
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
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the steps of the served head

The chain-generic steps of `Compose/Sleepy/Served`, which imports them privately, shared with the
growing-fault forms (`Growing/Sleepy/Node/ServedRead`): the record step (`record_step_of`), the
served cuts of the latest view's slot (`exec_tick_cuts`, `tickAt_acCall`, `not_before_tick`,
`latest_slot_tick_at_read`), the read invariant (`ReadAtCut`, `ReadInvWith`,
`ReadSyncOrService`), the honest head in the frame (`honest_head_in_frame_at_read`), the
supporters and the majority of the latest view (`latest_honest_supporter`, `latest_awake_voter`,
`latest_majority`, with `latestView_lt_six`), the record writer and its label or lock
(`record_writer`, `record_label_or_lock`), and the head support at a read (`head_support_at`,
`read_head_support_of`). `ReadInvWith.awake` charges the slot count at `t_s + Δ`
(`|Hᶜ|` below the honest validators awake and joined then) only for the slots `s` with
`t_s + Δ ≤ t < t_s + 6Δ`, its one use being the latest view's slot at `t`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- Inside a coherent `U`, ancestry towards a block of a subset `S ⊆ U` in which every block
descends from a parentless root stays inside `S` (`S` is parent-closed). -/
theorem anc_of_anc_superset {n : Nat} {FGP ACP : Type} {S U : Set (Block n FGP ACP)}
    (hU : Coherent U) (hSU : S ⊆ U) {g : Block n FGP ACP} (hg : g.parent = none)
    (hS : ∀ B ∈ S, Anc S g B) {A B : Block n FGP ACP} (h : Anc U A B) : B ∈ S → Anc S A B := by
  induction h with
  | refl => exact fun _ => .refl
  | @tail c d _ e ih =>
    intro hd
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hS d hd) with rfl | ⟨p, -, hp⟩
    · exact absurd (e.2.2.symm.trans hg) (Option.some_ne_none _)
    · obtain rfl : p = c :=
        hU.1 (hSU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
      exact (ih hp.1).tail hp

/-- The record step over a chain `Ch` of pairwise compatible honest blocks that holds the
record's block, `Σ.F`, and the selections of the cut. -/
theorem record_step_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hcomp : ∀ X Y, X ∈ tr.HonestBlocks H → Y ∈ tr.HonestBlocks H → Ch X → Ch Y →
      Compatible (tr.HonestBlocks H) X Y)
    (hrec : ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧ Ch C)
    (hFc : Ch (tr.state y i).fg.F)
    (hnew : ∀ C s CV, SA.ResultAt tr.projAC y i s C CV ∨ SA.OptimisticLockAt tr.projAC y i s C CV →
      Ch C) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' := by
  intro E hE hEr
  have hac := ac_projection _ _ dg H _ tr proposer (requirements sp ro)
    (fun y _ => payloadFrom_initial (requirements sp ro) y) hrun.toLocalRun hnc
  have hU := hac.coherent
  have hst : ∀ k, tr.projAC.state y k = (tr.state y k).ac := projAC_state hrun.toLocalRun hy
  by_cases hcall : ∃ ℓ, tr.projAC.CallAt y i ℓ
  swap
  · refine ⟨E, hE, ?_, .refl⟩
    rw [← hst, tr.projAC.state_succ_of_not fun ℓ h => hcall ⟨ℓ, h⟩, hst]
    exact hEr
  obtain ⟨ℓ, hc⟩ := hcall
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hac hy hc
  have hw := call_writes hac hy hc
  rw [← tr.projAC.state_succ_of_call hc, hst, hst] at hw
  -- the record's block before the call: in `y`'s tree, on the chain, in the frame or below `Σ.F`
  obtain ⟨C₀, hC₀, hC₀r, hEc⟩ := hrec
  obtain rfl : E = C₀ := hU.1 hE ⟨y, hy, i, hC₀⟩ (hEr.trans hC₀r.symm)
  have hfr : ℓ.frame = Node.frame (tr.state y i) := frame_of_projAC hrun hy hc
  have hpos : E ∈ ℓ.frame.tree ∨ Anc (tr.HonestBlocks H) E ℓ.frame.F := by
    rw [hfr]
    have hFt : (tr.state y i).fg.F ∈ (tr.state y i).fg.tree := (hfr ▸ hΦ.rooted.1).1
    rcases hcomp _ _ hE ⟨y, hy, i, hFt⟩ hEc hFc with h | h
    · exact Or.inr h
    · obtain ⟨-, -, -, hanc⟩ :=
        Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
      exact Or.inl ⟨hC₀, anc_of_anc_superset hU (fun X hX => ⟨y, hy, i, hX⟩)
        (by simp [Params.genesisBlock]) hanc h hC₀⟩
  -- each write keeps the record's block or moves it to a descendant
  suffices key : ∀ r', Writes ℓ.frame (fun C => ∃ s CV, SA.ResultAt tr.projAC y i s C CV ∨
      SA.OptimisticLockAt tr.projAC y i s C CV) (tr.state y i).ac.latestConfirmed r' →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = r' ∧ Anc (tr.HonestBlocks H) E E' ∧
        (E' ∈ ℓ.frame.tree ∨ Anc (tr.HonestBlocks H) E' ℓ.frame.F) ∧ Ch E' by
    obtain ⟨E', hE', hE'r, hEE', -⟩ := key _ hw
    exact ⟨E', hE', hE'r, hEE'⟩
  intro r' hw'
  rw [writes_iff] at hw'
  induction hw' with
  | refl => exact ⟨E, hE, hEr, .refl, hpos, hEc⟩
  | tail _ hstep ih =>
    obtain ⟨E₁, hE₁, hE₁r, hEE₁, hpos₁, hc₁⟩ := ih
    obtain ⟨C, hC, ⟨s, CV, hO⟩, hk | ⟨hn, rfl⟩⟩ := hstep
    · exact ⟨E₁, hE₁, hE₁r.trans hk.2.symm, hEE₁, hpos₁, hc₁⟩
    have hCc : Ch C := hnew C s CV hO
    have hE₁C : Anc (tr.HonestBlocks H) E₁ C := by
      rcases hpos₁ with hT | hF
      · rcases hcomp _ _ hE₁ (hΦU hC) hc₁ hCc with h | h
        · exact h
        · exact absurd ⟨E₁, hT, hE₁r, SA.anc_tree_of_anc_U hU hΦ hΦU hC h hT⟩ hn
      · exact hF.trans ((hΦ.rooted.2 C hC).mono hΦU)
    exact ⟨C, hΦU hC, rfl, hEE₁.trans hE₁C, Or.inl hC, hCc⟩

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
theorem exec_tick_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 = (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- The first cut of a tick is the AC's tick call. -/
theorem tickAt_acCall {y : Fin sp.n} {j : Nat} {T : Time} (hT : tr.TickAt proposer dg y j T) :
    ∃ ℓ, tr.projAC.CallAt y j ℓ ∧ ℓ.call = .tick ∧ tr.time j = T := by
  obtain ⟨x, -, hk, -⟩ := hT
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j) T (.tick x)).2.length := by
    rw [exec_tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) T (.tick x)).2[0]'hlen =
      (Node.acCall y (tr.state y j) T .tick).2 := by
    simp only [exec_tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  exact ⟨ℓ, projAC_callAt.2 ⟨hn0, hl⟩, hcall, ht0⟩

/-- A call of an honest node at a time `T` where it is joined is not before its tick at `T`: at
one time restarts come first, then the tick, and a restart at `T` is not joined at `T`. -/
theorem not_before_tick (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i j₁ : Nat} (hc : tr.IsCall y i) (hj : tr.JoinedAt y (tr.time i))
    (hT : tr.TickAt proposer dg y j₁ (tr.time i)) (hij : i < j₁) : False := by
  obtain ⟨x₁, hj₁⟩ := hT
  obtain ⟨c, hcc⟩ := hc
  obtain ⟨j₀, e, hg, hj₀i, hij₀⟩ := hrun.grouped y hy i c hcc
  have hph := hrun.phase_order y hy y hy j₀ j₁ _ e (.tick x₁) hg hj₁ (by omega)
  cases e with
  | tick x => exact absurd (hrun.tick_unique y hy j₀ j₁ _ ⟨x, hg⟩ ⟨x₁, hj₁⟩) (by omega)
  | restart =>
    have hlen : (Node.exec proposer dg y (tr.state y j₀) (tr.time i) .restart).2.length = 1 := rfl
    obtain ⟨hn0, -, -, -, hl0⟩ := hg.2.1 0 (by rw [hlen]; omega)
    obtain rfl : i = j₀ := by rw [hlen] at hij₀; omega
    simp only [Nat.add_zero] at hn0 hl0
    obtain ⟨hpos, h⟩ := hj i ⟨_, ⟨hn0, hl0⟩, rfl⟩ le_rfl
    rw [sp.slotTime_eq] at h
    have hσ := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) (sp.slot (tr.time i))).2 le_rfl
    have h1 : ((sp.toParams.slotOf (tr.time i) - 1 : Nat) : Int) + 1 = sp.slot (tr.time i) := by
      simp only [SAParams.slot]; omega
    have h2 : sp.ts (sp.slot (tr.time i) : Int) =
        4 * sp.Δ * ((sp.toParams.slotOf (tr.time i) - 1 : Nat) : Int) + 4 * sp.Δ := by
      simp only [SAParams.ts]; rw [← h1]; ring
    linarith [sp.toParams.hΔ]
  | block B => simp [Node.Event.phase] at hph
  | message m => simp [Node.Event.phase] at hph
  | attestation a => simp [Node.Event.phase] at hph

/-- `y`'s state before cut `i`, read at the time `t ≥ 0`: every earlier cut is at or before `t`,
cut `i` at or after it, `y`'s tick at `t` (if any) at or before cut `i`, and `y` is awake and
joined at `t`. -/
structure ReadAtCut (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat) (t : Time) : Prop where
  /-- The read time is from `0` on. -/
  nonneg : 0 ≤ t
  /-- Every cut before `i` is at or before `t`. -/
  before : ∀ k < i, tr.time k ≤ t
  /-- Cut `i` is at or after `t`. -/
  after : t ≤ tr.time i
  /-- `y`'s tick at `t` is at or before cut `i`. -/
  tick : ∀ k, tr.TickAt proposer dg y k t → k ≤ i
  /-- `y` is awake at `t`. -/
  awake : tr.awake y t
  /-- `y` is joined at `t`. -/
  joined : tr.JoinedAt y t

/-- What the head support at a read of `y` before cut `i` at `t` reads of the invariant: a chain
`Ch` of pairwise compatible honest blocks, closed under ancestors, that holds the record's block,
the stored locks and the caches; origins `O`, among them those whose event precedes the cut,
viable at the cuts up to `i` and extended by the earlier honest votes of later slots; the
service `Service` (`ReadSyncOrService` at the served head); and `f < h_t` at the slot points
`t_s + Δ ≤ t` with `t < t_s + 6Δ`. `Compose/Sleepy/Served` builds it under `Sleepy` from the full
invariant, or from the invariant up to `b ≥ t`. -/
structure ReadInvWith (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop)
    (O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (y : Fin sp.n) (i : Nat) (t : Time)
    (Service : Prop) : Prop where
  compat : ∀ X Y, X ∈ tr.HonestBlocks H → Y ∈ tr.HonestBlocks H → Ch X → Ch Y →
    Compatible (tr.HonestBlocks H) X Y
  anc : ∀ A B, A ∈ tr.HonestBlocks H → Anc (tr.HonestBlocks H) A B → Ch B → Ch A
  record : ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧ Ch C
  locks : ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧ Ch L
  caches : Ch (tr.state y i).fg.F ∧ Ch (tr.state y i).fg.J
  origin : ∀ C s, OriginBefore tr H C s i → O C s
  viable : ∀ m ≤ i, ∀ C s, O C s → C ∈ (Node.frame (tr.state y m)).tree →
    (Node.frame (tr.state y m)).Anc C (Node.frame (tr.state y m)).fcRoot ∨
      C ∈ (Node.frame (tr.state y m)).viableTree (Node.frame (tr.state y m)).tree
  vote_extends : ∀ C s, O C s → ∀ x ∈ H, ∀ k < i, ∀ e, SA.VoteAt tr.projAC x k e →
    s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg C
  sync : Service
  awake : ∀ s : Nat, sp.ts s + sp.Δ ≤ t → t < sp.ts s + 6 * sp.Δ →
    Hᶜ.ncard < {x | x ∈ H ∧ tr.awake x (sp.ts s + sp.Δ) ∧ tr.JoinedAt x (sp.ts s + sp.Δ)}.ncard

abbrev ReadSyncOrService (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (t : Time) :=
  SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) 0 (t - sp.Δ) tr.projAC ∨
    SA.ServiceBefore H (tr.HonestBlocks H) t tr.projAC

/-- **The tick of the latest view's slot at a read.** At a read of an honest node at `t`, with
`l` the latest view's slot at `t`: `t_l + 2Δ ≤ t`, the node's restarts up to `t` are at or before
`t_l`, and it ran its AC tick at `t_l + 2Δ` at a cut at or before `i`. -/
theorem latest_slot_tick_at_read (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {t : Time} (hrd : ReadAtCut proposer dg tr y i t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2) :
    sp.ts L + 2 * sp.Δ ≤ t ∧
      (∀ r, tr.RestartAt y r → tr.time r ≤ t → tr.time r ≤ sp.ts L) ∧
      ∃ j ≤ i, ∃ ℓ, tr.projAC.CallAt y j ℓ ∧ tr.time j = sp.ts L + 2 * sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht0 := hrd.nonneg
  have hσ := (SA.ts_le_iff_le_slot sp ht0 (sp.slot t)).2 le_rfl
  have hLσ : (sp.slot t : Int) ≤ L + 1 ∧ sp.ts L + 2 * sp.Δ ≤ t := by
    simp only [SA.latestView] at hL
    split_ifs at hL with h
    · exact ⟨by omega, by rw [hL]; exact h⟩
    · refine ⟨by omega, ?_⟩
      have hts : sp.ts (L : Int) = sp.ts (sp.slot t : Int) - 4 * sp.Δ := by
        simp only [SAParams.ts]; rw [hL]; ring
      linarith
  have hres : ∀ r, tr.RestartAt y r → tr.time r ≤ t → tr.time r ≤ sp.ts L := by
    intro r hr htr
    obtain ⟨-, h⟩ := hrd.joined r hr htr
    rw [sp.slotTime_eq] at h
    refine h.trans ?_
    simp only [SAParams.ts]
    have : ((sp.toParams.slotOf t - 1 : Nat) : Int) ≤ L := by
      have := hLσ.1; simp only [SAParams.slot] at this; omega
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hT0 : 0 ≤ sp.ts L + 2 * sp.Δ := by simp only [SAParams.ts]; positivity
  have hwT : tr.awake y (sp.ts L + 2 * sp.Δ) := by
    rcases hLσ.2.lt_or_eq with hlt | heq
    · by_contra hn
      obtain ⟨k, hk, hk1, hk2⟩ := hrun.restart_at_wake y hy _ _ hT0 hlt hn hrd.awake
      exact absurd (hres k hk hk2)
        (not_le.2 ((lt_add_of_pos_right _ (mul_pos two_pos hΔ)).trans hk1))
    · rw [heq]; exact hrd.awake
  obtain ⟨j₁, x₁, hj₁⟩ := hrun.tick_of_awake y hy _ hT0
    (Dvd.intro (4 * (L : Int) + 2) (by simp only [SAParams.ts]; ring)) hwT
  obtain ⟨ℓ₁, hc₁, -, ht₁⟩ := tickAt_acCall ⟨x₁, hj₁⟩
  refine ⟨hLσ.2, hres, j₁, ?_, ℓ₁, hc₁, ht₁⟩
  rcases hLσ.2.lt_or_eq with hlt | heq
  · by_contra hji
    have := hrun.time_mono (not_le.1 hji).le
    linarith [hrd.after]
  · rw [heq] at hj₁
    exact hrd.tick j₁ ⟨x₁, hj₁⟩

/-- **An honest head reaches a read node** (acceptance relay): at a read at `t`, with `l` the
latest view's slot, the head `Hd` of an honest slot-`l` vote that extends the node's `Σ.F` is in
its frame, with a finite stamp: the voter accepted it before its vote, and it is relayed to the
node before `t_l + 2Δ` (by its tick then), with no restart since. -/
theorem honest_head_in_frame_at_read (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (hsync : ReadSyncOrService tr H t ∨ ∃ a,
      SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC ∧
      CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t ∧
      a ≤ sp.ts (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hy : y ∈ H)
    (hrd : ReadAtCut proposer dg tr y i t) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {x : Fin sp.n} (hx : x ∈ H) {j' : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x j' e) (hes : e.msg.slot = L)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocks H)
    (hHdr : Hd.root = e.msg.head) (hF : Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd) :
    Hd ∈ (Node.frame (tr.state y i)).tree ∧ (tr.projAC.state y i).blockStamp Hd.root < ⊤ := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hTt, hres, jc, hjci, ℓj, hcj, htj⟩ := latest_slot_tick_at_read hrun hy hrd hL
  have hres' : ∀ r, tr.projAC.RestartAt y r → tr.projAC.time r ≤ t → tr.projAC.time r ≤ sp.ts L :=
    fun r ⟨ℓr, hcr, hrr⟩ hrt => hres r ⟨ℓr, projAC_callAt.1 hcr, hrr⟩ hrt
  have hjct : ∀ r ≤ jc, tr.projAC.time r ≤ t := fun r h =>
    (hr.time_mono h).trans (htj.trans_le hTt)
  obtain ⟨ℓ', hcall, hem⟩ := hv
  obtain ⟨⟨Hd', hHd'Φ, hHd'r, -⟩, htj'⟩ := cast_head_fcRoot hr hx ⟨hcall, hem⟩
  obtain rfl : Hd' = Hd :=
    hU.1 ((SA.frameIn_of_callAt hr hx hcall).2 hHd'Φ) hHd (hHd'r.trans hHdr.symm)
  rw [hes] at htj'
  have hgr := fg_grows hrun hy hjci
  have hframe := frame_of_projAC hrun hy hcj
  have hFj : Anc (tr.HonestBlocks H) ℓj.frame.F Hd' := by
    rw [hframe]; exact hgr.2.trans hF
  have htop : ∀ t : Time, SA.ETime.of t < ⊤ := fun t => WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  -- `y` accepted `Hd'` before `t_l + 2Δ`, by its tick then
  obtain ⟨hinj, hacc⟩ : Hd' ∈ (tr.state y jc).fg.tree ∧
      SA.AcceptedBefore tr.projAC y Hd' (sp.ts L + 2 * sp.Δ) := by
    rcases frame_anc_accepted hr hx j' ℓ' hcall Hd' hHd'Φ Hd' .refl with hg | ⟨k, hk, hkA⟩
    · refine ⟨?_, Or.inl hg⟩
      obtain ⟨-, -, hgen, -⟩ := Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy jc)
      rwa [hU.1 hHd ⟨y, hy, jc, hgen⟩ hg]
    · have hkt : tr.projAC.time k ≤ sp.ts L + sp.Δ := (hr.time_mono hk).trans htj'
      have hdl : tr.projAC.deadline y jc (tr.projAC.time k) ≤ tr.projAC.time jc := by
        change _ ≤ tr.time jc
        rw [htj, two_mul, ← add_assoc]
        exact (ac_deadline_le_of_restarts (fun r hr' hrr => hres' r hrr (hjct r hr'))
          (tr.projAC.time k)).trans
          (add_le_add (max_le hkt (le_add_of_nonneg_right hΔ.le)) le_rfl)
      obtain ⟨k₂, hk₂j, hk₂, hk₂t⟩ : ∃ k₂ ≤ jc, tr.projAC.AcceptAt y k₂ Hd' ∧
          tr.projAC.time k₂ < sp.ts L + 2 * sp.Δ := by
        have finish : (∃ k₂ ≤ jc, tr.projAC.AcceptAt y k₂ Hd' ∧
            tr.projAC.time k₂ < tr.projAC.deadline y k₂ (tr.projAC.time k)) →
            ∃ k₂ ≤ jc, tr.projAC.AcceptAt y k₂ Hd' ∧
              tr.projAC.time k₂ < sp.ts L + 2 * sp.Δ := by
          rintro ⟨k₂, hk₂j, hk₂, hk₂t⟩
          have hd₂ := ac_deadline_le_of_restarts
            (fun r hr' hrr => hres' r hrr (hjct r (hr'.trans hk₂j)))
            (tr.projAC.time k)
          have hmax : max (tr.projAC.time k) (sp.ts L) ≤ sp.ts L + sp.Δ :=
            max_le hkt (le_add_of_nonneg_right hΔ.le)
          refine ⟨k₂, hk₂j, hk₂, hk₂t.trans_le (hd₂.trans ?_)⟩
          rw [two_mul, ← add_assoc]
          exact add_le_add hmax le_rfl
        rcases hsync with hsync | ⟨a, hsync, hcatch, ha⟩
        · apply finish
          exact hsync.elim
            (fun h => h.2 x hx k Hd' hkA (hr.time_nonneg k)
              (le_sub_iff_add_le.2 ((add_le_add hkt le_rfl).trans
                (by rw [add_assoc, ← two_mul]; exact hTt)))
              y hy jc ℓj hcj hdl hFj)
            (fun h => h.relay x hx k Hd' hkA (hr.time_nonneg k)
              y hy jc ℓj hcj (hdl.trans (hjct jc le_rfl)) hdl hFj)
        · rw [← hL] at ha
          by_cases hka : a ≤ tr.projAC.time k
          · exact finish (hsync.relay x hx k Hd' hkA hka y hy jc ℓj hcj
              (hdl.trans (hjct jc le_rfl)) hdl hFj)
          · obtain ⟨k₂, hk₂j, hk₂, hk₂t⟩ := hcatch.relay x hx k Hd' hkA (lt_of_not_ge hka)
              y hy jc ℓj hcj
              (by change a + _ ≤ tr.time jc; rw [htj]; exact add_le_add ha le_rfl)
              (hjct jc le_rfl) hFj
            exact ⟨k₂, hk₂j, hk₂, hk₂t.trans_le (add_le_add ha le_rfl)⟩
      have h1 := (SA.accept_new sp hr hy hk₂).1
      obtain ⟨ℓk, hck, hkc⟩ := hk₂
      refine ⟨?_, Or.inr ⟨k₂, ⟨ℓk, hck, hkc⟩, hk₂t⟩⟩
      have h2 := h1 ℓk hck
      rw [frame_of_projAC hrun hy hck] at h2
      exact (fg_grows hrun hy hk₂j).1 h2.1
  have hanc : ∀ m, ∀ B ∈ (tr.state y m).fg.tree, (tr.state y m).fg.Anc
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := fun m =>
    (Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy m)).2.2.2
  have hHdjc : Hd' ∈ (Node.frame (tr.state y jc)).tree :=
    ⟨hinj, anc_of_anc_superset hU (fun X hX => ⟨y, hy, jc, hX⟩) (by simp [Params.genesisBlock])
      (hanc jc) (hgr.2.trans hF) hinj⟩
  have hst := SA.blockStamp_lt_of_acceptedBefore sp hr hy hcj (by rw [hframe]; exact hHdjc) hacc
    (fun k hk hrk => by
      change tr.time k < _
      exact (hres' k hrk (hjct k hk)).trans_lt (lt_add_of_pos_right _ (mul_pos two_pos hΔ)))
    (Or.inl (by change _ ≤ tr.time jc; rw [htj]))
  refine ⟨⟨hgr.1 hinj, anc_of_anc_superset hU (fun X hX => ⟨y, hy, i, hX⟩)
    (by simp [Params.genesisBlock]) (hanc i) hF (hgr.1 hinj)⟩, ?_⟩
  refine blockStamp_finite (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hy
    hjci (fun r h1 h2 hrr => ?_) (lt_trans hst (htop _))
  have h3 : tr.time r ≤ sp.ts L := hres' r hrr (hrd.before r h2)
  have h4 : tr.time jc ≤ tr.time r := hr.time_mono h1
  rw [htj] at h4
  exact absurd (h4.trans h3) (not_le.2 (lt_add_of_pos_right _ (mul_pos two_pos hΔ)))

theorem latest_honest_supporter (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadSyncOrService tr H t))
    (hrd : ReadAtCut proposer dg tr y i t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree) {j : Nat} (hO : O R j)
    (hjl : (j : Int) < (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2) :
    ∀ w ∈ SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes,
      w ∈ H → w ∈ SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R := by
  obtain ⟨L, hL⟩ : ∃ L : Nat, (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  apply latest_honest_supporter_of_target_votes hrun hnc hy hR hL
  · intro z hz q hq e hv hs
    exact hI.vote_extends R j hO z hz q hq e hv (by rw [hs]; omega)
  · intro z hz q e hv hs Hd hHd hHdr hF
    exact honest_head_in_frame_at_read hrun hnc (Or.inl hI.sync) hy hrd hL hz hv hs hHd hHdr hF

/-- **The awake validators vote in the latest view** (Sync): at a read at `t`, an honest
validator awake and joined at `t_l + Δ`, with `l` the latest view's slot, votes in slot `l` by
then, and its vote reaches the node before `t_l + 2Δ ≤ t`, so before the read, and the node has
not restarted since. -/
theorem latest_awake_voter (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (hsync : ReadSyncOrService tr H t ∨ ∃ a,
      SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC ∧
      a ≤ sp.ts (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hy : y ∈ H)
    (hrd : ReadAtCut proposer dg tr y i t) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {x : Fin sp.n} (hx : x ∈ H) (hxw : tr.awake x (sp.ts L + sp.Δ))
    (hxj : tr.JoinedAt x (sp.ts L + sp.Δ)) :
    x ∈ SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hTt, hres, jc, hjci, ℓj, hcj, htj⟩ := latest_slot_tick_at_read hrun hy hrd hL
  obtain ⟨k, e, ⟨ℓ, hck, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hx hxw hxj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hx ⟨hck, he⟩
  have hk0 : sp.ts L ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) L).2 (by omega)
  have hres' : ∀ r, tr.projAC.RestartAt y r → tr.projAC.time r ≤ t → tr.projAC.time r ≤ sp.ts L :=
    fun r ⟨ℓr, hcr, hrr⟩ hrt => hres r ⟨ℓr, projAC_callAt.1 hcr, hrr⟩ hrt
  have hjct : ∀ r ≤ jc, tr.projAC.time r ≤ t := fun r h =>
    (hr.time_mono h).trans (htj.trans_le hTt)
  have hdl : ∀ c ≤ jc, tr.projAC.deadline y c (tr.projAC.time k) ≤ tr.projAC.time k + sp.Δ :=
    fun c hcj' => (ac_deadline_le_of_restarts
      (fun r hr' hrr => hres' r hrr (hjct r (hr'.trans hcj'))) _).trans
      (by rw [max_eq_left hk0])
  have hdj : tr.projAC.deadline y jc (tr.projAC.time k) ≤ tr.projAC.time jc := by
    change _ ≤ tr.time jc; rw [htj, two_mul, ← add_assoc]
    exact (hdl jc le_rfl).trans (add_le_add hk le_rfl)
  have served : SA.MessageServedBefore tr.projAC y jc (tr.projAC.time k) e.msg := by
    rcases hsync with hsync | ⟨a, hsync, ha⟩
    · exact hsync.elim
        (fun h => (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          (h.1 x hx k e.msg ⟨ℓ, hck, Or.inl ⟨e, he, rfl⟩⟩ (hr.time_nonneg k)
          (le_sub_iff_add_le.2 ((add_le_add hk le_rfl).trans
            (by rw [add_assoc, ← two_mul]; exact hTt))) y hy jc ℓj hcj hdj)))
        (fun h => h.message x hx k e.msg ⟨ℓ, hck, Or.inl ⟨e, he, rfl⟩⟩ (hr.time_nonneg k)
          y hy jc ℓj hcj (hdj.trans (hjct jc le_rfl)) hdj)
    · rw [← hL] at ha
      exact (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
        (hsync.message x hx k e.msg ⟨ℓ, hck, Or.inl ⟨e, he, rfl⟩⟩ (ha.trans hk0)
          y hy jc ℓj hcj (hdj.trans (hjct jc le_rfl)) hdj))
  rcases (SA.messageServedBefore_iff _ _ _ _).mp served with served | retained
  swap
  · have evidence := retained.evidence hr hy
    have hmono := SA.pool_mono hr hy hjci (fun r hrj hri hrr => by
      obtain ⟨ℓr, hcr, hrr'⟩ := hrr
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr'
      by_cases heq : r = jc
      · subst r
        have hbound := hres' jc ⟨ℓr, hcr, hrr'⟩ (hrd.before jc hri)
        change tr.time jc ≤ _ at hbound
        rw [htj] at hbound
        exact absurd hbound (not_le.2 (lt_add_of_pos_right _ (mul_pos two_pos hΔ)))
      · have h₁ := hprev jc (by omega) ℓj hcj
        have h₂ := hres' r ⟨ℓr, hcr, hrr'⟩ (hrd.before r hri)
        change tr.time jc < _ at h₁
        rw [htj] at h₁
        exact lt_irrefl _ (h₂.trans_lt ((lt_add_of_pos_right _ (mul_pos two_pos hΔ)).trans
          (h₁.trans hu)))) L
    rcases (SA.poolEvidenceBefore_iff _ _ _).mp evidence with hv |
      ⟨a, _, _, hav, _, has, _, ha, _⟩
    · exact ⟨e.msg, mem_latest_votes hrun hnc hy hL
        (hmono (by simpa only [hes] using hv.1)), hval⟩
    · exact ⟨a, mem_latest_votes hrun hnc hy hL
        (hmono (by simpa only [has, hes] using ha.1)), hav.trans hval⟩
  obtain ⟨k', hk'j, hkk', hp, hk'dl⟩ := served
  have hk'dl' : tr.projAC.time k' < sp.ts L + 2 * sp.Δ :=
    hk'dl.trans_le ((hdl k' hk'j).trans
      (by rw [two_mul, ← add_assoc]; exact add_le_add hk le_rfl))
  have hk'i : k' < i :=
    lt_of_lt_of_le (lt_of_le_of_ne hk'j (by rintro rfl; exact hk'dl'.ne htj))
      hjci
  have hts1 : sp.ts ((L + 1 : Nat) : Int) = sp.ts L + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsk' : sp.slot (tr.projAC.time k') = L :=
    SA.slot_of_mem sp L (hk0.trans hkk') (by
      rw [hts1]
      exact hk'dl'.trans
        (add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right (by norm_num) hΔ)))
  have hpm := SA.pool_mono hr hy (Nat.succ_le_of_lt hk'i) (fun r hr1 hr2 hrr => by
    obtain ⟨ℓr, hcr, hrr'⟩ := hrr
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr'
    obtain ⟨ℓ', hc', -⟩ := hp
    have h1 := hprev k' (by omega) ℓ' hc'
    have h2 := hres' r ⟨ℓr, hcr, hrr'⟩ (hrd.before r hr2)
    exact lt_irrefl _ (h1.trans (hu.trans_le (h2.trans (hk0.trans hkk'))))) L
  rcases SA.held_of_processAt hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
    h | ⟨a, ha, -, -, -, hav, -⟩
  · rw [hes] at h
    exact ⟨e.msg, mem_latest_votes hrun hnc hy hL (hpm h), hval⟩
  · rw [hes] at ha
    exact ⟨a, mem_latest_votes hrun hnc hy hL (hpm ha), hav.trans hval⟩

/-- A read at `t ≥ 0` is before `t_l + 6Δ`, with `l` the latest view's slot at `t`. -/
theorem latestView_lt_six {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} (ht0 : 0 ≤ t) {L : Nat} (hL : (L : Int) = (SA.latestView sp A Φ t).2) :
    t < sp.ts L + 6 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hlt : t < sp.ts ((sp.slot t : Int) + 1) := lt_of_not_ge fun h => by
    have := (SA.ts_le_iff_le_slot sp ht0 _).1 h
    omega
  have hts : sp.ts ((sp.slot t : Int) + 1) = sp.ts (sp.slot t : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  simp only [SA.latestView] at hL
  split_ifs at hL with h
  · rw [hL]; linarith
  · have : sp.ts (L : Int) = sp.ts (sp.slot t : Int) - 4 * sp.Δ := by
      simp only [SAParams.ts]; rw [hL]; ring
    linarith

/-- **The supporter majority of an older origin**: at a read at `t`, an
origin `R` of the frame whose label is below the latest view's slot `l` is supported by a strict
majority of the latest view's voters: the honest voters support it, the more than `f` validators
awake and joined at `t_l + Δ` are voters, and the other voters are faulty. -/
theorem latest_majority (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadSyncOrService tr H t))
    (hrd : ReadAtCut proposer dg tr y i t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ (Node.frame (tr.state y i)).tree) {j : Nat}
    (hO : O R j)
    (hjl : (j : Int) < (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
        t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
        R).ncard := by
  set l := (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
  set Vt := SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
    t).1.votes
  set Sp := SA.supporters (Node.frame (tr.state y i))
    (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1 l R
  obtain ⟨L, hL⟩ : ∃ L : Nat, (L : Int) = l := ⟨l.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hHV : Vt ∩ H ⊆ Sp := fun w hwV =>
    latest_honest_supporter hrun hnc hy hI hrd hR hO hjl w hwV.1 hwV.2
  have hSX : {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)} ⊆
      Vt ∩ H := fun x hx =>
    ⟨latest_awake_voter hrun hnc (Or.inl hI.sync) hy hrd hL hx.1 hx.2.1 hx.2.2, hx.1⟩
  have h₁ := Set.ncard_le_ncard (hSX.trans hHV) (Set.toFinite _)
  have h₂ := Set.ncard_le_ncard hHV (Set.toFinite _)
  have h₃ : Vt.ncard ≤ (Vt ∩ H).ncard + Hᶜ.ncard := by
    refine (Set.ncard_le_ncard (fun w hw => ?_) (Set.toFinite _)).trans
      (Set.ncard_union_le _ _)
    by_cases hwH : w ∈ H
    · exact Or.inl ⟨hw, hwH⟩
    · exact Or.inr hwH
  have h₄ := hI.awake L (by linarith [(latest_slot_tick_at_read hrun hy hrd hL).1, sp.toParams.hΔ])
    (latestView_lt_six hrd.nonneg hL)
  omega

/-- **How the record was written** (honest node, before cut `m`): it is genesis (the initial
record), or the root of a block `C` of the frame of an earlier call `k` that wrote it, as the
result of its update, or as the selection of its optimistic check of the slot `slot(t_k)`, whose
fast lock on `C` is still stored when every later call before `m` is in the next slot at the
latest and holds `C` in its frame (the record has not changed since). -/
theorem record_writer (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop} (m : Nat)
    (hOO : ∀ k < m, ∀ C s CV, SA.OptimisticLockAt tr.projAC y k s C CV → O C s)
    (hvi : ∀ k < m, ∀ C s, O C s → C ∈ (Node.frame (tr.state y k)).tree →
      (Node.frame (tr.state y k)).Anc C (Node.frame (tr.state y k)).fcRoot ∨
        C ∈ (Node.frame (tr.state y k)).viableTree (Node.frame (tr.state y k)).tree) :
    (tr.projAC.state y m).latestConfirmed = sp.genesisRoot ∨
      ∃ k < m, ∃ ℓk, tr.projAC.CallAt y k ℓk ∧ ∃ C ∈ ℓk.frame.tree,
        C.root = (tr.projAC.state y m).latestConfirmed ∧
        ((∃ s CV, SA.ResultAt tr.projAC y k s C CV) ∨
          ((∃ CV, SA.OptimisticLockAt tr.projAC y k (sp.slot (tr.time k)) C CV) ∧
            ((∀ m', k < m' → m' < m → ∀ ℓ', tr.projAC.CallAt y m' ℓ' →
                sp.slot (tr.time m') ≤ sp.slot (tr.time k) + 1 ∧ C ∈ ℓ'.frame.tree) →
              ∃ e, sp.slot (tr.time k) + 2 ≤ e ∧ (⟨C.root, sp.slot (tr.time k), true, e⟩ : SA.Lock)
                  ∈ (tr.projAC.state y m).locks))) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  induction m with
  | zero =>
    left
    change (tr.projAC.init y).latestConfirmed = _
    rw [hr.init y hy]
    rfl
  | succ m ih =>
    have ih := ih (fun k hk => hOO k (by omega)) (fun k hk => hvi k (by omega))
    by_cases hcall : ∃ ℓ, tr.projAC.CallAt y m ℓ
    swap
    · rw [tr.projAC.state_succ_of_not fun ℓ h => hcall ⟨ℓ, h⟩]
      refine ih.imp_right fun ⟨k, hkm, ℓk, hck, C, hC, hCr, h⟩ =>
        ⟨k, hkm.trans (Nat.lt_succ_self m), ℓk, hck, C, hC, hCr,
          h.imp_right fun ⟨hO, hL⟩ => ⟨hO, fun hcond => hL fun m' h₁ h₂ =>
            hcond m' h₁ (h₂.trans (Nat.lt_succ_self m))⟩⟩
    obtain ⟨ℓ, hc⟩ := hcall
    rw [tr.projAC.state_succ_of_call hc]
    obtain ⟨hk, hrl⟩ := call_reclock hr hy hc
    have hΦ := (SA.frameIn_of_callAt hr hy hc).1
    have hframe : ℓ.frame = Node.frame (tr.state y m) := frame_of_projAC hrun hy hc
    have hcand : ∀ C ∈ ℓ.frame.tree, ∀ s, O C s →
        C ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc C ℓ.frame.fcRoot := by
      intro C hC s hO
      rw [hframe] at hC ⊢
      exact (hvi m (Nat.lt_succ_self m) C s hO hC).symm
    rcases recLock_iff.1 hrl with hsame | ⟨C, hC, hCr, hres | ⟨⟨CV, hOm⟩, hl⟩⟩
    · rcases ih with hg | ⟨k, hkm, ℓk, hck, C, hC, hCr, hR | ⟨hO, hL⟩⟩
      · exact Or.inl (hsame.trans hg)
      · exact Or.inr ⟨k, hkm.trans (Nat.lt_succ_self m), ℓk, hck, C, hC, hCr.trans hsame.symm,
          Or.inl hR⟩
      · refine Or.inr ⟨k, hkm.trans (Nat.lt_succ_self m), ℓk, hck, C, hC, hCr.trans hsame.symm,
          Or.inr ⟨hO, fun hcond => ?_⟩⟩
        have hl := hL fun m' h₁ h₂ => hcond m' h₁ (h₂.trans (Nat.lt_succ_self m))
        obtain ⟨hs1, hCm⟩ := hcond m hkm (Nat.lt_succ_self m) ℓ hc
        obtain ⟨CV, hOk⟩ := hO
        obtain ⟨e, he, hl⟩ := hl
        exact ⟨e, he, keepAll_iff.1 hk _ hl (keepOK_iff.2 ⟨hs1,
          le_trans hs1 (show _ ≤ e by omega), C, hCm, rfl,
          hcand C hCm _ (hOO k (by omega) C _ CV hOk)⟩)⟩
    · exact Or.inr ⟨m, Nat.lt_succ_self m, ℓ, hc, C, hC, hCr.symm, Or.inl hres⟩
    · rw [SA.viableAncestor_self hΦ hC (hcand C hC _ (hOO m (Nat.lt_succ_self m) C _ CV hOm))]
        at hl
      exact Or.inr ⟨m, Nat.lt_succ_self m, ℓ, hc, C, hC, hCr.symm, Or.inr ⟨⟨CV, hOm⟩, fun _ => hl⟩⟩

/-- **The record's label or its fast lock**: read at a time `t` at or after
every cut before `i` (so `t ≥ 0` unless the record is genesis), a record block `R` of the frame
that is not at or below `fc_root` is an origin of a label below the latest view's slot at `t` (a
result, or an optimistic selection of an older slot), or a live lock block at `t` (an optimistic
selection of the current slot, or of the previous one before `t_σ + 2Δ`, whose fast lock is still
stored on `R`). -/
theorem record_label_or_lock (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadSyncOrService tr H t))
    (hle : ∀ k < i, tr.time k ≤ t) {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R)
    (hRf : ¬ (Node.frame (tr.state y i)).Anc R (Node.frame (tr.state y i)).fcRoot) :
    0 ≤ t ∧ (R ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t ∨
      ∃ j, O R j ∧ (j : Int) <
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hst := projAC_state hrun.toLocalRun hy i
  have hts1 : ∀ a : Nat, sp.ts ((a + 1 : Nat) : Int) = sp.ts (a : Int) + 4 * sp.Δ := fun a => by
    simp only [SAParams.ts]; push_cast; ring
  have hOb : ∀ k < i, ∀ C s CV, SA.ResultAt tr.projAC y k s C CV ∨
      SA.OptimisticLockAt tr.projAC y k s C CV → O C s :=
    fun k hk C s CV h => hI.origin C s (originBefore_iff.2 ⟨y, hy, k, hk, CV, h⟩)
  rcases record_writer hrun hnc hy i (fun k hk C s CV h => hOb k hk C s CV (Or.inr h))
      (fun k hk => hI.viable k hk.le) with
    hg | ⟨k, hki, ℓk, hck, C, hCk, hCr, hres | ⟨hopt, hlock⟩⟩
  · -- genesis is at or below `Σ.F`
    exfalso
    apply hRf
    obtain ⟨-, -, hgen, hanc⟩ := Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
    have hRg := hU.1 (hΦU hR.1) ⟨y, hy, i, hgen⟩ (hR.2.trans (hst ▸ hg))
    have hRF : R = (Node.frame (tr.state y i)).F := by
      refine Anc.antisymm hU ?_ ((hΦ.rooted.2 _ hR.1).mono hΦU)
      rw [hRg]
      exact (hanc _ hΦ.rooted.1.1).mono fun X hX => ⟨y, hy, i, hX⟩
    rw [hRF]
    exact hΦ.F_anc_fcRoot
  all_goals
    have hCU : C ∈ tr.HonestBlocks H := (SA.frameIn_of_callAt hr hy hck).2 hCk
    obtain rfl : R = C := hU.1 (hΦU hR.1) hCU (hR.2.trans (hst ▸ hCr.symm))
    have hki' : tr.time k ≤ t := hle k hki
    have ht0 : 0 ≤ t := (hr.time_nonneg k).trans hki'
    have hσ := (SA.ts_le_iff_le_slot sp ht0 (sp.slot t)).2 le_rfl
    refine ⟨ht0, ?_⟩
  · -- a result: its label is below the latest view's slot
    obtain ⟨s, CV, hRes⟩ := hres
    refine Or.inr ⟨s, hOb k hki R s CV (Or.inl hRes), ?_⟩
    obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hRes
    have h1 : sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ ≤ t := by
      have htk' : tr.time k = sp.ts s + 6 * sp.Δ := htk
      rw [hts1]; linarith
    simp only [SA.latestView]
    split_ifs with h
    · have := (SA.ts_le_iff_le_slot sp ht0 _).1 (by linarith : sp.ts ((s + 1 : Nat) : Int) ≤ _)
      push_cast at this ⊢
      omega
    · have : sp.ts ((s + 1 : Nat) : Int) < sp.ts (sp.slot t : Int) := by
        rw [not_le] at h; linarith
      rw [SA.ts_lt_iff] at this
      push_cast at this ⊢
      omega
  · -- an optimistic selection: an older label, or its fast lock is still stored on `R`
    obtain ⟨CV, hOk⟩ := hopt
    by_cases hsl : ((sp.slot (tr.time k) : Nat) : Int) <
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
    · exact Or.inr ⟨_, hOb k hki R _ CV (Or.inr hOk), hsl⟩
    left
    have hlσ : (sp.slot t : Int) - 1 ≤
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 := by
      simp only [SA.latestView]; split_ifs <;> omega
    have hs : sp.slot t ≤ sp.slot (tr.time k) + 1 := by omega
    have hRk : R ∈ (tr.state y k).fg.tree := by
      rw [frame_of_projAC hrun hy hck] at hCk; exact hCk.1
    have hl := hlock fun m' h₁ h₂ ℓ' hc' => by
      refine ⟨(SA.slot_mono sp (hr.time_nonneg m') (hle m' h₂)).trans hs, ?_⟩
      rw [frame_of_projAC hrun hy hc']
      have hg₁ := fg_grows hrun hy h₁.le
      have hg₂ := fg_grows hrun hy h₂.le
      exact ⟨hg₁.1 hRk, anc_of_anc_superset hU (fun X hX => ⟨y, hy, m', hX⟩)
        (by simp [Params.genesisBlock])
        (Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy m')).2.2.2
        (hg₂.2.trans ((hΦ.rooted.2 R hR.1).mono hΦU)) (hg₁.1 hRk)⟩
    rw [hst] at hl
    obtain ⟨e, he, hl⟩ := hl
    refine ⟨hR.1, _, ⟨_, hl, R, hR.1, rfl, show _ ≤ e by omega, rfl⟩, ?_⟩
    rw [SA.viableAncestor_self hΦ hR.1
      (hI.viable i le_rfl R _ (hOb k hki R _ CV (Or.inr hOk)) hR.1).symm]

/-- **G1, G2 at a read**: the state of an honest node before cut `i` read at `t`, with every
earlier cut at or before `t` and a read point (`ReadAtCut`) when `t ≥ 0`: the anchor at `t` is
compatible with the record's block `R`, and `R` is at or below it, or viable with a strict
majority of the latest view's voters at `t` as supporters. -/
theorem head_support_at (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadSyncOrService tr H t))
    (hle : ∀ k < i, tr.time k ≤ t) (hrd : 0 ≤ t → ReadAtCut proposer dg tr y i t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R) :
    Compatible (Node.frame (tr.state y i)).tree
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
              t).1.votes).ncard <
            2 * (SA.supporters (Node.frame (tr.state y i))
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
              R).ncard)) := by
  have hac := ac_projection _ _ dg H _ tr proposer (requirements sp ro)
    (fun y _ => payloadFrom_initial (requirements sp ro) y) hrun.toLocalRun hnc
  have hU := hac.coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, hX.1⟩
  -- the record's block, the live lock blocks and `fc_root` are on the origin chain
  have hRc : Ch R := by
    obtain ⟨C₀, hC₀, hC₀r, hgo⟩ := hI.record
    obtain rfl : R = C₀ := hU.1 (hΦU hR.1) ⟨y, hy, i, hC₀⟩ (hR.2.trans hC₀r.symm)
    exact hgo
  set Φ := Node.frame (tr.state y i) with hΦdef
  set S := SA.liveLockBlocks sp (tr.state y i).ac.locks Φ t ∪ {Φ.fcRoot}
  have hSc : ∀ X ∈ S, X ∈ Φ.tree ∧ Ch X := by
    rintro X (⟨hX, l, ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩, hXr⟩ | hX)
    · obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB
      obtain rfl : X = Φ.viableAncestor B := hΦ.coherent.1 hX hvt hXr.symm
      obtain ⟨L, hL, hLr, hLc⟩ := hI.locks l₀ hl₀
      obtain rfl : B = L := hU.1 (hΦU hB) ⟨y, hy, i, hL⟩ (hBr.trans hLr.symm)
      exact ⟨hX, hI.anc _ _ (hΦU hX) (hva.mono hΦU) hLc⟩
    · rw [Set.mem_singleton_iff.1 hX]
      refine ⟨hΦ.fcRoot_mem, ?_⟩
      change Ch (tr.state y i).fg.fcRoot
      unfold Store.fcRoot
      split_ifs
      exacts [hI.caches.2, hI.caches.1]
  have hcomp : ∀ X Y, X ∈ Φ.tree → Y ∈ Φ.tree → Ch X → Ch Y →
      Compatible Φ.tree X Y := fun X Y hX hY hXc hYc =>
    (hI.compat _ _ (hΦU hX) (hΦU hY) hXc hYc).imp
      (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hX h hY)
      fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hY h hX
  have hSsub : S ⊆ Φ.tree := fun X hX => (hSc X hX).1
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hSsub ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : SA.getAnchor sp (tr.state y i).ac Φ t = D := by
    simp only [SA.getAnchor, S, hD, Option.getD_some]
  have hDS := (SA.deepest_mem hD).1
  have hdom : ∀ X ∈ S, Φ.Anc X D := SA.anc_deepest hΦ hSsub
    (fun X hX Y hY => hcomp X Y (hSc X hX).1 (hSc Y hY).1 (hSc X hX).2 (hSc Y hY).2) hD
  refine ⟨ha ▸ hcomp D R (hSc D hDS).1 hR.1 (hSc D hDS).2 hRc, ?_⟩
  rw [ha]
  by_cases hRf : Φ.Anc R Φ.fcRoot
  · exact Or.inl (hRf.trans (hdom _ (Or.inr rfl)))
  obtain ⟨ht0, hl | ⟨j, hO, hjl⟩⟩ := record_label_or_lock hrun hnc hy hI hle hR hRf
  · exact Or.inl (hdom R (Or.inl hl))
  · exact Or.inr ⟨(hI.viable i le_rfl R j hO hR.1).resolve_left hRf,
      latest_majority hrun hnc hy hI (hrd ht0) hR.1 hO hjl⟩

/-- G1, G2 at a read, from `ReadInv` at every cut whose earlier cuts are at or before `t`. When
the node's tick at `t` is at a cut `≥ i`, it makes no call in between (the tick is its first event
at `t`), so the read is the one before the tick's cut. -/
theorem read_head_support_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ∀ m, (∀ k < m, tr.time k ≤ t) → tr.time m ≤ tr.time i →
      ReadInvWith tr H Ch O y m t (ReadSyncOrService tr H t))
    (hle : ∀ k < i, tr.time k ≤ t) (hti : t ≤ tr.time i)
    (hwj : 0 ≤ t → tr.awake y t ∧ tr.JoinedAt y t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : RecordAt tr y i R) :
    Compatible (Node.frame (tr.state y i)).tree
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
              t).1.votes).ncard <
            2 * (SA.supporters (Node.frame (tr.state y i))
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
              (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2
              R).ncard)) := by
  by_cases hT : ∃ j₁, i ≤ j₁ ∧ tr.TickAt proposer dg y j₁ t
  · obtain ⟨j₁, hij, hT⟩ := hT
    obtain ⟨-, -, -, ht₁⟩ := tickAt_acCall hT
    have ht0 : 0 ≤ t := ht₁ ▸ hrun.time_nonneg j₁
    obtain ⟨hw, hj⟩ := hwj ht0
    -- no call of `y` in `[i, j₁)`: it would be at `t`, before the tick
    have hst : ∀ m, i ≤ m → m ≤ j₁ → tr.state y m = tr.state y i := by
      intro m him
      induction m, him using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ m him ih =>
        intro hm
        have htm : tr.time m = t := le_antisymm
          (by rw [← ht₁]; exact hrun.time_mono (by omega)) (hti.trans (hrun.time_mono him))
        rw [tr.state_succ_of_not fun c hc => not_before_tick hrun hy ⟨c, hc⟩
          (by rw [htm]; exact hj) (by rw [htm]; exact hT) (by omega), ih (by omega)]
    have hs := hst j₁ hij le_rfl
    have hle₁ : ∀ k < j₁, tr.time k ≤ t := fun k hk => ht₁ ▸ hrun.time_mono hk.le
    have h := head_support_at hrun hnc hy (hI j₁ hle₁ (ht₁.trans_le hti)) hle₁
      (fun _ => ⟨ht0, hle₁, ht₁.ge, fun k hk => (hrun.tick_unique y hy k j₁ t hk hT).le, hw, hj⟩)
      (R := R) (by rw [RecordAt, hs]; exact hR)
    rwa [hs] at h
  · exact head_support_at hrun hnc hy (hI i hle le_rfl) hle (fun ht0 => ⟨ht0, hle, hti,
      fun k hk => not_lt.1 fun hik => hT ⟨k, hik.le, hk⟩, (hwj ht0).1, (hwj ht0).2⟩) hR

end Consensus.Goldilocks.Compose

end
