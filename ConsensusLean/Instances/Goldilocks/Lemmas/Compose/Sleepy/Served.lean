module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Sleepy
import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
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

-- The served head shares a proof across whole-run, prefix and deadline-bounded service through
-- the private `ReadInvWith`; the scoped relay also shares the read/tick machinery.

public section

/-! # Goldilocks under `Sleepy`: the served head (S4) and the record step (G3)

workbench#11 §5, the facts the Service milestone reads (`ServedFacts`, in
`Lemmas/Compose/Service/Sleepy`), from `SleepyInvariant`:

* **The record step** (`record_step`, G3, at every honest cut): a record write takes an origin
  `C` of the frame, compatible with the old record (genesis or an origin, in the node's tree);
  it keeps the record when `C` is below it in the frame, and otherwise the old record is below
  `C` (below `Σ.F ⪯ C` when it left the frame). Restarts keep the record.
* **The served head** (`served_head_support`, G1, G2, at a cut after the update of slot
  `slot(t) − 2` or `slot(t) − 1` with no restart since, awake and joined): the anchor (the
  deepest of the live lock blocks and `fc_root`, all on the origin chain) is compatible with the
  record `R`. If `R` was
  written by an optimistic check of the current slot, or of the previous one before its
  `t_s + 2Δ`, its fast lock is still live at `R` (full viability keeps it there), so `R ⪯` the
  anchor. Otherwise `R`'s label is below the latest view's slot: every honest vote of that slot
  extends `R` (S2), the more than `f` cast by the validators awake and joined at its `t + Δ`
  reach the served node by its tick at `t_l + 2Δ` and are resolved (their heads are relayed,
  extending `Σ.F ⪯ R`), and the node keeps them (joined at `t`, it has not restarted since
  `t_{σ−1}`; the update clause is not needed), and only faulty seats remain, so the supporters
  are a strict majority of the voters; `R` is fully viable (S3). Which case holds is read off
  how the record was last written (`record_writer`: genesis, a result, or an optimistic
  selection whose fast lock every later call keeps while `R` stays viable and the slot at most
  one later).
* **The head at a read** (`read_head_support`, for R.1): the same, for the state before a cut `i`
  read at a time `t` with every earlier cut at or before `t` and cut `i` at or after it, the node
  awake and joined at `t`. The votes and heads the latest view at `t` needs arrive before
  `t_l + 2Δ ≤ t`, so at cuts before `i`; when the node's tick at `t` is at a cut `≥ i`, the node
  makes no call before it at `t`, and the read is the one before the tick's cut.

The record step and the head at a read hold up to a horizon `b` too (`record_step_upTo`,
`read_head_support_upTo`), from `SleepyInvariantUpTo` under the prefix premises up to `b`: a read
at `t ≤ b` needs `Sync` for the sends up to `t − Δ` and `f < h_t` at `t_l + Δ ≤ t`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The record step -/

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9). -/
private theorem requirements (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- Inside a coherent `U`, ancestry towards a block of a subset `S ⊆ U` in which every block
descends from a parentless root stays inside `S` (`S` is parent-closed). -/
private theorem anc_of_anc_superset {n : Nat} {FGP ACP : Type} {S U : Set (Block n FGP ACP)}
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
private theorem record_step_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
  have hac := ac_projection _ _ dg H _ tr proposer (requirements sp ro) hrun.toLocalRun hnc
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

/-- **G3, the record step**: at every cut of an honest node, the record moves to a descendant
(inside the honest blocks). -/
theorem record_step (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
  record_step_of hrun hnc hy i
    (fun _ _ hX hY hXc hYc =>
      OnOriginChain.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc)
    ⟨C, hC, hCr, onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i).1 fun C s _ hO => onOriginChain_iff.2 (Or.inr
      ⟨C, s, hO.elim (Origin.of_result hy) (Origin.of_optimistic hy), .refl⟩)

/-- **G3 up to `b`, the record step**: at every cut of an honest node at a time `≤ b` (with the
earlier ones), the record moves to a descendant (inside the honest blocks). -/
theorem record_step_upTo {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hi : ∀ k ≤ i, tr.time k ≤ b) :
    ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
      ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        Anc (tr.HonestBlocks H) E E' :=
  have hi' : ∀ k < i, tr.time k ≤ b := fun k hk => hi k hk.le
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i hi'
  record_step_of hrun hnc hy i
    (fun _ _ hX hY hXc hYc =>
      OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc)
    ⟨C, hC, hCr, onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i hi').1 fun C s CV hO => onOriginChainWithin_iff.2 (Or.inr
      ⟨C, s, originWithin_iff.2 ⟨y, hy, i, CV, hi i le_rfl, hO⟩, .refl⟩)

/-! ### The served head -/

/-! ### Served cuts: the tick of the latest view's slot, delivery -/

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 = (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- The first cut of a tick is the AC's tick call. -/
private theorem tick_acCall {y : Fin sp.n} {j : Nat} {T : Time} (hT : tr.TickAt proposer dg y j T) :
    ∃ ℓ, tr.projAC.CallAt y j ℓ ∧ ℓ.call = .tick ∧ tr.time j = T := by
  obtain ⟨x, -, hk, -⟩ := hT
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j) T (.tick x)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) T (.tick x)).2[0]'hlen =
      (Node.acCall y (tr.state y j) T .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  exact ⟨ℓ, projAC_callAt.2 ⟨hn0, hl⟩, hcall, ht0⟩

/-- A call of an honest node at a time `T` where it is joined is not before its tick at `T`: at
one time restarts come first, then the tick, and a restart at `T` is not joined at `T`. -/
private theorem not_before_tick (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
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
private structure ReadAt (proposer : Nat → Fin sp.n)
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

/-- A cut of an honest node awake and joined at its time is read at its time. -/
private theorem readAt_self (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hc : tr.IsCall y i) (hw : tr.awake y (tr.time i)) (hj : tr.JoinedAt y (tr.time i)) :
    ReadAt proposer dg tr y i (tr.time i) :=
  ⟨hrun.time_nonneg i, fun _ hk => hrun.time_mono hk.le, le_rfl,
    fun _ hk => not_lt.1 fun hik => not_before_tick hrun hy hc hj hk hik, hw, hj⟩

/-- What the head support at a read of `y` before cut `i` at `t` reads of the invariant: a chain
`Ch` of pairwise compatible honest blocks, closed under ancestors, that holds the record's block,
the stored locks and the caches; origins `O`, among them those whose event precedes the cut,
viable at the cuts up to `i` and extended by the earlier honest votes of later slots;
`Sync[0, t − Δ]`; and `f < h_t` at the slot points `t_s + Δ ≤ t`. Under `Sleepy` with the full
invariant (`ReadInv.of_full`), or up to `b ≥ t` (`ReadInv.of_upTo`). -/
private structure ReadInvWith (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
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
  awake : ∀ s : Nat, sp.ts s + sp.Δ ≤ t →
    Hᶜ.ncard < {x | x ∈ H ∧ tr.awake x (sp.ts s + sp.Δ) ∧ tr.JoinedAt x (sp.ts s + sp.Δ)}.ncard

private abbrev ReadInv (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop)
    (O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (y : Fin sp.n) (i : Nat) (t : Time) :=
  ReadInvWith tr H Ch O y i t
    (SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) 0 (t - sp.Δ) tr.projAC)

private abbrev ReadService (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (t : Time) :=
  SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) 0 (t - sp.Δ) tr.projAC ∨
    SA.ServiceBefore H (tr.HonestBlocks H) t tr.projAC

private theorem ReadInv.service {Ch O y i t} (h : ReadInv tr H Ch O y i t) :
    ReadInvWith tr H Ch O y i t (ReadService tr H t) :=
  { h with sync := Or.inl h.sync }

/-- `ReadInv` from the full invariant under `Sleepy`. -/
private theorem ReadInv.of_full (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (t : Time) : ReadInv tr H (OnOriginChain tr H) (Origin tr H) y i t :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
  { compat := fun _ _ hX hY hXc hYc =>
      OnOriginChain.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc
    anc := fun _ _ hA hAB h => OnOriginChain.of_anc hrun hnc hA hAB h
    record := ⟨C, hC, hCr, onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    locks := hinv.locks y hy i
    caches := hinv.caches y hy i
    origin := fun _ _ h => h.origin
    viable := fun m _ C s hO hC => hinv.viable y hy m C s hO hC
    vote_extends := fun C s hO x hx k _ e hv hs => hinv.vote_extends C s hO x hx k e hv hs
    sync := syncAC_of_sleepy hrun hsl le_rfl
    awake := fun s _ => faults_lt_awake_joined hsl s }

private theorem ReadInvWith.of_before {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hi : ∀ k < i, tr.time k ≤ b) {t : Time}
    (ht : t ≤ b) (hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ t → tr.FaultBound H (sp.ts s + sp.Δ)) :
    ReadInvWith tr H (fun B => OnOriginChainWithin tr H B b)
      (fun C s => OriginWithin tr H C s b) y i t (ReadService tr H t) :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i hi
  { compat := fun _ _ hX hY hXc hYc =>
      OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hX hY hXc hYc
    anc := fun _ _ hA hAB h => OnOriginChainWithin.of_anc hrun hnc hA hAB h
    record := ⟨C, hC, hCr,
      onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    locks := hinv.locks y hy i hi
    caches := hinv.caches y hy i hi
    origin := fun _ _ h => h.within hi
    viable := fun m hm C s hO hC => hinv.viable y hy m (fun k hk => hi k (by omega)) C s hO hC
    vote_extends := fun C s hO x hx k hk e hv hs =>
      hinv.vote_extends C s hO x hx k e hv (hi k hk) hs
    sync := Or.inr {
      message := fun x hx k m hm h0 z hz j ℓ hc hd hj =>
        hsync.message x hx k m hm h0 z hz j ℓ hc (hd.trans ht) hj
      relay := fun x hx k B hB h0 z hz j ℓ hc hd hj ha =>
        hsync.relay x hx k B hB h0 z hz j ℓ hc (hd.trans ht) hj ha }
    awake := hfb }

/-- **The tick of the latest view's slot at a read.** At a read of an honest node at `t`, with
`l` the latest view's slot at `t`: `t_l + 2Δ ≤ t`, the node's restarts up to `t` are at or before
`t_l`, and it ran its AC tick at `t_l + 2Δ` at a cut at or before `i`. -/
private theorem served_tick (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {t : Time} (hrd : ReadAt proposer dg tr y i t)
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
      linarith [hres k hk hk2]
    · rw [heq]; exact hrd.awake
  obtain ⟨j₁, x₁, hj₁⟩ := hrun.tick_of_awake y hy _ hT0
    (Dvd.intro (4 * (L : Int) + 2) (by simp only [SAParams.ts]; ring)) hwT
  obtain ⟨ℓ₁, hc₁, -, ht₁⟩ := tick_acCall ⟨x₁, hj₁⟩
  refine ⟨hLσ.2, hres, j₁, ?_, ℓ₁, hc₁, ht₁⟩
  rcases hLσ.2.lt_or_eq with hlt | heq
  · by_contra hji
    have := hrun.time_mono (not_le.1 hji).le
    linarith [hrd.after]
  · rw [heq] at hj₁
    exact hrd.tick j₁ ⟨x₁, hj₁⟩

/-- A vote of the slot-`L` pool of an honest node is a vote of its latest view, of slot `L`. -/
theorem mem_latest_votes (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i L : Nat} {t : Time}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {u : Vote sp.n} (hu : u ∈ (tr.projAC.state y i).pool L) :
    u ∈ (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hus : u.slot = L := SA.state_pool_slot sp hr hy i L u hu
  have hst : (tr.projAC.state y i).voteStamp u < ⊤ := by
    rcases SA.pool_origin hr hy i u (hus ▸ hu) with ⟨k, -, -, h, -⟩ | ⟨k, -, -, -, -, h, -⟩ <;>
      rw [h] <;> exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  rw [projAC_state hrun.toLocalRun hy] at hu hst
  simp only [SA.latestView] at hL ⊢
  rw [← hL]
  simp [SA.voteView, SA.voteViewList, SA.View.ofLists, SA.SAState.poolAt, hu, hst]

/-- The FG state of an honest node only grows: its tree, and its finalized tip, to a descendant. -/
theorem fg_grows (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {j i : Nat}
    (h : j ≤ i) : (tr.state y j).fg.tree ⊆ (tr.state y i).fg.tree ∧
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F (tr.state y i).fg.F := by
  induction i, h using Nat.le_induction with
  | base => exact ⟨subset_rfl, .refl⟩
  | succ i _ ih =>
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      obtain ⟨-, hT, hF⟩ := chain_fg y (.cons (hrun.cutLaw y hy i c hc) (.nil _))
        (fg_reachable hrun.toLocalRun hy i)
      rw [tr.state_succ_of_call hc]
      refine ⟨ih.1.trans hT, ih.2.trans (hF.mono fun X hX => ⟨y, hy, i + 1, ?_⟩)⟩
      rwa [tr.state_succ_of_call hc]
    · rw [tr.state_succ_of_not fun c h => hc ⟨c, h⟩]
      exact ih

/-- The votes and the support of the latest view, of slot `L`. -/
private theorem latestView_mem {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {L : Nat} (hL : (L : Int) = (SA.latestView sp A Φ t).2) (v : Vote sp.n) :
    (v ∈ (SA.latestView sp A Φ t).1.votes ↔ v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧
      (v ∈ (SA.latestView sp A Φ t).1.support ↔
        (v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧ SA.resolutionTime A Φ v < ⊤) := by
  simp only [SA.latestView] at hL ⊢
  rw [← hL]
  simp only [SA.voteView, SA.voteViewList, SA.View.ofLists, SA.SAState.poolAt, Set.mem_ofPred_eq,
    List.mem_filter, decide_eq_true_eq, Int.natCast_nonneg, not_lt.2, ↓reduceIte, Int.toNat_natCast,
    and_assoc, true_and]

/-- **An honest head reaches a read node** (acceptance relay): at a read at `t`, with `l` the
latest view's slot, the head `Hd` of an honest slot-`l` vote that extends the node's `Σ.F` is in
its frame, with a finite stamp: the voter accepted it before its vote, and it is relayed to the
node before `t_l + 2Δ` (by its tick then), with no restart since. -/
private theorem head_in_frame (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (hsync : ReadService tr H t ∨ ∃ a,
      SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC ∧
      CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t ∧
      a ≤ sp.ts (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hy : y ∈ H)
    (hrd : ReadAt proposer dg tr y i t) {L : Nat}
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
  obtain ⟨hTt, hres, jc, hjci, ℓj, hcj, htj⟩ := served_tick hrun hy hrd hL
  have hres' : ∀ r, tr.projAC.RestartAt y r → tr.projAC.time r ≤ t → tr.projAC.time r ≤ sp.ts L :=
    fun r ⟨ℓr, hcr, hrr⟩ hrt => hres r ⟨ℓr, projAC_callAt.1 hcr, hrr⟩ hrt
  have hjct : ∀ r ≤ jc, tr.projAC.time r ≤ t := fun r h => by
    have := hr.time_mono h
    change _ ≤ tr.time jc at this
    linarith
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
        have := ac_deadline_le_of_restarts (fun r hr' hrr => hres' r hrr (hjct r hr'))
          (tr.projAC.time k)
        change _ ≤ tr.time jc
        rw [htj]
        linarith [max_le hkt (show sp.ts L ≤ sp.ts L + sp.Δ by linarith)]
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
            max_le hkt (by linarith)
          exact ⟨k₂, hk₂j, hk₂, by linarith⟩
        rcases hsync with hsync | ⟨a, hsync, hcatch, ha⟩
        · apply finish
          exact hsync.elim
            (fun h => h.2 x hx k Hd' hkA (hr.time_nonneg k)
              (by have hkt' : tr.time k ≤ sp.ts L + sp.Δ := hkt; linarith)
              y hy jc ℓj hcj hdl hFj)
            (fun h => h.relay x hx k Hd' hkA (hr.time_nonneg k)
              y hy jc ℓj hcj (hdl.trans (hjct jc le_rfl)) hdl hFj)
        · rw [← hL] at ha
          by_cases hka : a ≤ tr.projAC.time k
          · exact finish (hsync.relay x hx k Hd' hkA hka y hy jc ℓj hcj
              (hdl.trans (hjct jc le_rfl)) hdl hFj)
          · obtain ⟨k₂, hk₂j, hk₂, hk₂t⟩ := hcatch.relay x hx k Hd' hkA (lt_of_not_ge hka)
              y hy jc ℓj hcj (by change a + _ ≤ tr.time jc; rw [htj]; linarith)
              (hjct jc le_rfl) hFj
            exact ⟨k₂, hk₂j, hk₂, by linarith⟩
      have h1 := (SA.accept_new sp hr hy hk₂).1
      obtain ⟨ℓk, hck, hkc⟩ := hk₂
      refine ⟨?_, Or.inr ⟨k₂, ⟨ℓk, hck, hkc⟩, by linarith⟩⟩
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
      have h3 : tr.time k ≤ sp.ts L := hres' k hrk (hjct k hk)
      change tr.time k < _
      linarith)
    (Or.inl (by change _ ≤ tr.time jc; rw [htj]))
  refine ⟨⟨hgr.1 hinj, anc_of_anc_superset hU (fun X hX => ⟨y, hy, i, hX⟩)
    (by simp [Params.genesisBlock]) (hanc i) hF (hgr.1 hinj)⟩, ?_⟩
  refine blockStamp_finite (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hy
    hjci (fun r h1 h2 hrr => ?_) (lt_trans hst (htop _))
  have h3 : tr.time r ≤ sp.ts L := hres' r hrr (hrd.before r h2)
  have h4 : tr.time jc ≤ tr.time r := hr.time_mono h1
  linarith

/-- Honest latest-view voters support a held target when their votes extend it and their
heads are relayed with finite stamps. The target-vote and relay premises are independent of
the invariant and service window used to establish them. -/
theorem latest_honest_supporter_of_target_votes (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hvotes : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hrelay : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      ∀ Hd ∈ tr.HonestBlocks H, Hd.root = e.msg.head →
        Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd →
        Hd ∈ (Node.frame (tr.state y i)).tree ∧ (tr.projAC.state y i).blockStamp Hd.root < ⊤) :
    ∀ w ∈ SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
        t).1.votes, w ∈ H →
      w ∈ SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R := by
  intro w ⟨v, hvV, hvw⟩ hwH
  subst hvw
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hst := projAC_state hrun.toLocalRun hy i
  have hpool : ∀ u ∈ (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes, u ∈ (tr.projAC.state y i).pool L ∧ u.slot = L := fun u hu => by
    have h := ((latestView_mem hL u).1.1 hu).1
    rw [← hst] at h
    exact ⟨h, SA.state_pool_slot sp hr hy i L u h⟩
  obtain ⟨hvp, hvs⟩ := hpool v hvV
  -- the vote is `v.val`'s own, of slot `L`, and extends `R` (S2)
  obtain ⟨j', hj', e, hve, hev⟩ := hrun'.honest.pool_vote y hy i L v hvp hwH
  obtain ⟨Hd, hHdU, hHdr, hRHd⟩ := hvotes v.val hwH j' hj' e hve (by rw [hev, hvs])
  have hF : Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd :=
    ((hΦ.rooted.2 R hR).mono hΦU).trans hRHd
  obtain ⟨hHdΦ, hbst⟩ := hrelay v.val hwH j' e hve (by rw [hev, hvs]) Hd hHdU hHdr hF
  obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ := SA.honest_head hrun' hwH hve
  obtain rfl : Hd = Hd₂ := hU.1 hHdU hHd₂ (hHdr.trans hHd₂r.symm)
  rw [hev] at hHdr hHd₂s
  -- the vote is resolved
  have hvst : (tr.state y i).ac.voteStamp v < ⊤ := ((latestView_mem hL v).1.1 hvV).2
  have hres : SA.resolutionTime (tr.state y i).ac (Node.frame (tr.state y i)) v < ⊤ := by
    unfold SA.resolutionTime
    rw [← hHdr, SA.lookup_of_mem hΦ hHdΦ]
    dsimp only
    simp only [not_lt.2 hHd₂s, ↓reduceIte]
    rw [← hst] at hvst ⊢
    exact max_lt hvst hbst
  -- an honest validator does not equivocate
  have hne : v.val ∉ SA.equivocators (SA.latestView sp (tr.state y i).ac
      (Node.frame (tr.state y i)) t).1.votes := by
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    obtain ⟨hap, has⟩ := hpool a ha
    obtain ⟨hbp, hbs⟩ := hpool b hb
    obtain ⟨ja, -, ea, hea, hea'⟩ := hrun'.honest.pool_vote y hy i L a hap (by rw [hav]; exact hwH)
    obtain ⟨jb, -, eb, heb, heb'⟩ := hrun'.honest.pool_vote y hy i L b hbp (by rw [hbv]; exact hwH)
    rw [hav] at hea
    rw [hbv] at heb
    obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp _ ro H _ _ hr v.val hwH ja jb ea eb hea heb
      (by rw [hea', heb', has, hbs])
    exact hab (hea'.symm.trans heb')
  refine ⟨hne, v, (latestView_mem hL v).2.2 ⟨(latestView_mem hL v).1.1 hvV, hres⟩, rfl,
    by rw [hvs]; exact hL, Hd, hHdΦ, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hR hRHd hHdΦ⟩

private theorem latest_honest_supporter (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadService tr H t))
    (hrd : ReadAt proposer dg tr y i t) {R : SA.Blk sp.n (List (FG.Att sp.n))}
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
    exact head_in_frame hrun hnc (Or.inl hI.sync) hy hrd hL hz hv hs hHd hHdr hF

/-- **The awake validators vote in the latest view** (Sync): at a read at `t`, an honest
validator awake and joined at `t_l + Δ`, with `l` the latest view's slot, votes in slot `l` by
then, and its vote reaches the node before `t_l + 2Δ ≤ t`, so before the read, and the node has
not restarted since. -/
private theorem latest_awake_voter (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time}
    (hsync : ReadService tr H t ∨ ∃ a,
      SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC ∧
      a ≤ sp.ts (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hy : y ∈ H)
    (hrd : ReadAt proposer dg tr y i t) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {x : Fin sp.n} (hx : x ∈ H) (hxw : tr.awake x (sp.ts L + sp.Δ))
    (hxj : tr.JoinedAt x (sp.ts L + sp.Δ)) :
    x ∈ SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hTt, hres, jc, hjci, ℓj, hcj, htj⟩ := served_tick hrun hy hrd hL
  obtain ⟨k, e, ⟨ℓ, hck, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hx hxw hxj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hx ⟨hck, he⟩
  have hk0 : sp.ts L ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) L).2 (by omega)
  have hres' : ∀ r, tr.projAC.RestartAt y r → tr.projAC.time r ≤ t → tr.projAC.time r ≤ sp.ts L :=
    fun r ⟨ℓr, hcr, hrr⟩ hrt => hres r ⟨ℓr, projAC_callAt.1 hcr, hrr⟩ hrt
  have hjct : ∀ r ≤ jc, tr.projAC.time r ≤ t := fun r h => by
    have := hr.time_mono h
    change _ ≤ tr.time jc at this
    linarith
  have hdl : ∀ c ≤ jc, tr.projAC.deadline y c (tr.projAC.time k) ≤ tr.projAC.time k + sp.Δ :=
    fun c hcj' => (ac_deadline_le_of_restarts
      (fun r hr' hrr => hres' r hrr (hjct r (hr'.trans hcj'))) _).trans
      (by rw [max_eq_left hk0])
  have hdj : tr.projAC.deadline y jc (tr.projAC.time k) ≤ tr.projAC.time jc := by
    have := hdl jc le_rfl; change _ ≤ tr.time jc; rw [htj]; linarith
  have served : SA.MessageServedBefore tr.projAC y jc (tr.projAC.time k) e.msg := by
    rcases hsync with hsync | ⟨a, hsync, ha⟩
    · exact hsync.elim
        (fun h => (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl
          (h.1 x hx k e.msg ⟨ℓ, hck, Or.inl ⟨e, he, rfl⟩⟩ (hr.time_nonneg k)
          (by have hk' : tr.time k ≤ sp.ts L + sp.Δ := hk; linarith) y hy jc ℓj hcj hdj)))
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
        linarith
      · have h₁ := hprev jc (by omega) ℓj hcj
        have h₂ := hres' r ⟨ℓr, hcr, hrr'⟩ (hrd.before r hri)
        change tr.time jc < _ at h₁
        rw [htj] at h₁
        linarith) L
    rcases (SA.poolEvidenceBefore_iff _ _ _).mp evidence with hv |
      ⟨a, _, _, hav, _, has, _, ha, _⟩
    · exact ⟨e.msg, mem_latest_votes hrun hnc hy hL
        (hmono (by simpa only [hes] using hv.1)), hval⟩
    · exact ⟨a, mem_latest_votes hrun hnc hy hL
        (hmono (by simpa only [has, hes] using ha.1)), hav.trans hval⟩
  obtain ⟨k', hk'j, hkk', hp, hk'dl⟩ := served
  have hk'dl' : tr.projAC.time k' < sp.ts L + 2 * sp.Δ := by
    have := hdl k' hk'j; linarith
  have hk'i : k' < i :=
    lt_of_lt_of_le (lt_of_le_of_ne hk'j (by rintro rfl; change tr.time k' < _ at hk'dl'; linarith))
      hjci
  have hts1 : sp.ts ((L + 1 : Nat) : Int) = sp.ts L + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsk' : sp.slot (tr.projAC.time k') = L :=
    SA.slot_of_mem sp L (hk0.trans hkk') (by rw [hts1]; linarith)
  have hpm := SA.pool_mono hr hy (Nat.succ_le_of_lt hk'i) (fun r hr1 hr2 hrr => by
    obtain ⟨ℓr, hcr, hrr'⟩ := hrr
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr'
    obtain ⟨ℓ', hc', -⟩ := hp
    have h1 := hprev k' (by omega) ℓ' hc'
    have h2 := hres' r ⟨ℓr, hcr, hrr'⟩ (hrd.before r hr2)
    linarith) L
  rcases SA.held_of_processAt hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
    h | ⟨a, ha, -, -, -, hav, -⟩
  · rw [hes] at h
    exact ⟨e.msg, mem_latest_votes hrun hnc hy hL (hpm h), hval⟩
  · rw [hes] at ha
    exact ⟨a, mem_latest_votes hrun hnc hy hL (hpm ha), hav.trans hval⟩

private theorem latest_majority_of_target_votes_at_read
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    (hrd : ReadAt proposer dg tr y i t)
    {a : Time} (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac
      (Node.frame (tr.state y i)) t).2) (ha : a ≤ sp.ts L)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
          t).2 R).ncard := by
  set Vt := SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
    t).1.votes
  set Sp := SA.supporters (Node.frame (tr.state y i))
    (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
    (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R
  have hHV : Vt ∩ H ⊆ Sp := by
    intro w hw
    apply latest_honest_supporter_of_target_votes hrun hnc hy hR hL hvotes ?_ w hw.1 hw.2
    intro z hz q e hv hs Hd hHd hHdr hF
    exact head_in_frame hrun hnc (Or.inr ⟨a, hsync, hcatch, by rw [← hL]; exact ha⟩)
      hy hrd hL hz hv hs hHd hHdr hF
  have hSX : {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)} ⊆
      Vt ∩ H := fun x hx =>
    ⟨latest_awake_voter hrun hnc (Or.inr ⟨a, hsync, by rw [← hL]; exact ha⟩)
      hy hrd hL hx.1 hx.2.1 hx.2.2, hx.1⟩
  have h₁ := Set.ncard_le_ncard (hSX.trans hHV) (Set.toFinite _)
  have h₂ := Set.ncard_le_ncard hHV (Set.toFinite _)
  have h₃ : Vt.ncard ≤ (Vt ∩ H).ncard + Hᶜ.ncard := by
    refine (Set.ncard_le_ncard (fun w hw => ?_) (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    by_cases hwH : w ∈ H
    · exact Or.inl ⟨hw, hwH⟩
    · exact Or.inr hwH
  change Vt.ncard < 2 * Sp.ncard
  omega

/-- Scoped target support at an arbitrary read, including a read before the node's tick
at the same clock. Direct votes are required through that clock, not just the initial cut. -/
theorem read_majority_of_target_votes
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    {a : Time} (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hvotes : ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e,
      SA.VoteAt tr.projAC z q e → e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes).ncard <
      2 * (SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard := by
  by_cases hT : ∃ j, i ≤ j ∧ tr.TickAt proposer dg y j t
  · obtain ⟨j, hij, hT⟩ := hT
    obtain ⟨-, -, -, htj⟩ := tick_acCall hT
    have hst : ∀ m, i ≤ m → m ≤ j → tr.state y m = tr.state y i := by
      intro m him
      induction m, him using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ m him ih =>
        intro hm
        have htm : tr.time m = t := le_antisymm
          (by rw [← htj]; exact hrun.time_mono (by omega)) (hti.trans (hrun.time_mono him))
        rw [tr.state_succ_of_not fun c hc => not_before_tick hrun hy ⟨c, hc⟩
          (by rw [htm]; exact hj) (by rw [htm]; exact hT) (by omega), ih (by omega)]
    have hs := hst j hij le_rfl
    have hlej : ∀ q < j, tr.time q ≤ t := fun q hq => htj ▸ hrun.time_mono hq.le
    have hrd : ReadAt proposer dg tr y j t :=
      ⟨ht0, hlej, htj.ge, fun q hq => (hrun.tick_unique y hy q j t hq hT).le, hw, hj⟩
    have h := latest_majority_of_target_votes_at_read hrun hnc hy hrd hsync hcatch
      (by rw [hs]; exact hL) ha (by rw [hs]; exact hR)
      (fun z hz q hq => hvotes z hz q (hlej q hq)) hfault
    rwa [hs] at h
  · exact latest_majority_of_target_votes_at_read hrun hnc hy
      ⟨ht0, hle, hti, fun q hq => not_lt.1 fun hiq => hT ⟨q, hiq.le, hq⟩, hw, hj⟩
      hsync hcatch hL ha hR (fun z hz q hq => hvotes z hz q (hle q hq)) hfault

/-- Post-GST head support for the actual record. Only the current view's votes and
participation are needed; historical record recency and anchor compatibility are supplied
separately. The live-lock arm requires no majority or service before GST. -/
theorem anchor_compatible_of_live_candidates
    {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    {t : Time} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcomp : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}, Compatible Φ.tree X R) :
    Compatible Φ.tree (SA.getAnchor sp A Φ t) R := by
  have hsub : SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.mp hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hsub ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : SA.getAnchor sp A Φ t = D := by simp only [SA.getAnchor, hD, Option.getD_some]
  rw [ha]
  exact hcomp D (SA.deepest_mem hD).1

/-- Scoped service and current-label votes complete the head certificate, after the
record has been classified against its actual-clock anchor. -/
theorem read_head_support_of_target_votes
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hle : ∀ q < i, tr.time q ≤ t) (hti : t ≤ tr.time i)
    (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    {a : Time} (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree)
    (hanchor : Compatible (Node.frame (tr.state y i)).tree
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
          e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R))
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    Compatible (Node.frame (tr.state y i)).tree
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) R ∧
      ((Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        (SA.voters (SA.latestView sp (tr.state y i).ac
          (Node.frame (tr.state y i)) t).1.votes).ncard <
          2 * (SA.supporters (Node.frame (tr.state y i))
            (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
            (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R).ncard)) := by
  refine ⟨hanchor, ?_⟩
  rcases hsource with h | ⟨hv, hvotes⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv, read_majority_of_target_votes hrun hnc hy ht0 hle hti hw hj
      hsync hcatch hL ha hR hvotes hfault⟩

/-- **The supporter majority of an older origin** (workbench#11 §2.4, §5): at a read at `t`, an
origin `R` of the frame whose label is below the latest view's slot `l` is supported by a strict
majority of the latest view's voters: the honest voters support it, the more than `f` validators
awake and joined at `t_l + Δ` are voters, and the other voters are faulty. -/
private theorem latest_majority (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadService tr H t))
    (hrd : ReadAt proposer dg tr y i t)
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
  have h₄ := hI.awake L (by linarith [(served_tick hrun hy hrd hL).1, sp.toParams.hΔ])
  omega

/-- **How the record was written** (honest node, before cut `m`): it is genesis (the initial
record), or the root of a block `C` of the frame of an earlier call `k` that wrote it, as the
result of its update, or as the selection of its optimistic check of the slot `slot(t_k)`, whose
fast lock on `C` is still stored when every later call before `m` is in the next slot at the
latest and holds `C` in its frame (the record has not changed since). -/
private theorem record_writer (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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

/-- **The record's label or its fast lock** (workbench#11 §5): read at a time `t` at or after
every cut before `i` (so `t ≥ 0` unless the record is genesis), a record block `R` of the frame
that is not at or below `fc_root` is an origin of a label below the latest view's slot at `t` (a
result, or an optimistic selection of an older slot), or a live lock block at `t` (an optimistic
selection of the current slot, or of the previous one before `t_σ + 2Δ`, whose fast lock is still
stored on `R`). -/
private theorem record_label_or_lock (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadService tr H t))
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
earlier cut at or before `t` and a read point (`ReadAt`) when `t ≥ 0`: the anchor at `t` is
compatible with the record's block `R`, and `R` is at or below it, or viable with a strict
majority of the latest view's voters at `t` as supporters. -/
private theorem head_support_at (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ReadInvWith tr H Ch O y i t (ReadService tr H t))
    (hle : ∀ k < i, tr.time k ≤ t) (hrd : 0 ≤ t → ReadAt proposer dg tr y i t)
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
  have hac := ac_projection _ _ dg H _ tr proposer (requirements sp ro) hrun.toLocalRun hnc
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
private theorem read_head_support_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    {O : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hI : ∀ m, (∀ k < m, tr.time k ≤ t) →
      ReadInvWith tr H Ch O y m t (ReadService tr H t))
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
    obtain ⟨-, -, -, ht₁⟩ := tick_acCall hT
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
    have h := head_support_at hrun hnc hy (hI j₁ hle₁) hle₁
      (fun _ => ⟨ht0, hle₁, ht₁.ge, fun k hk => (hrun.tick_unique y hy k j₁ t hk hT).le, hw, hj⟩)
      (R := R) (by rw [RecordAt, hs]; exact hR)
    rwa [hs] at h
  · exact head_support_at hrun hnc hy (hI i hle) hle (fun ht0 => ⟨ht0, hle, hti,
      fun k hk => not_lt.1 fun hik => hT ⟨k, hik.le, hk⟩, (hwj ht0).1, (hwj ht0).2⟩) hR

/-- **G1, G2 at a read** (for R.1): the state of an honest node before cut `i`, read at a time
`t` at or after every cut before `i` and at or before cut `i`, the node awake and joined at `t`
(when `t ≥ 0`): the anchor at `t` is compatible with the record's block `R`, and `R` is at or
below it, or viable with a strict majority of the latest view's voters at `t` as supporters. When
the node's tick at `t` is at a cut `≥ i`, it makes no call in between (the tick is its first event
at `t`), so the read is the one before the tick's cut. -/
theorem read_head_support (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {t : Time} (hle : ∀ k < i, tr.time k ≤ t) (hti : t ≤ tr.time i)
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
              R).ncard)) :=
  read_head_support_of hrun hnc hy
    (fun m _ => (ReadInv.of_full hinv hrun hnc hsl hy m t).service) hle hti hwj hR

/-- G1, G2 with recipient service bounded by the read time, not the next cut's time.
Only the fault bounds at `t_s + Δ ≤ t` are needed for the latest-view majority. -/
theorem read_head_support_before {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (htb : t ≤ b)
    (hfb : ∀ s : Nat, sp.ts s + sp.Δ ≤ t → tr.FaultBound H (sp.ts s + sp.Δ))
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
              R).ncard)) :=
  read_head_support_of hrun hnc hy
    (fun _ hm => ReadInvWith.of_before hinv hrun hnc hsync hy
      (fun k hk => (hm k hk).trans htb) htb hfb) hle hti hwj hR

/-- **G1, G2 at a served cut**: at a cut of an honest node awake and joined at its time that has
run the update of slot `slot(t) − 2` or `slot(t) − 1` with no restart since (A1.6's condition,
and A1.7's in the slot after the proposal's), the record's block has `HeadSupport`. -/
theorem served_head_support (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hc : tr.IsCall y i) (hw : tr.awake y (tr.time i)) (hj : tr.JoinedAt y (tr.time i))
    {s' : Nat} (_hs' : sp.slot (tr.time i) ≤ s' + 2) (_hu : UpdatedNoRestart tr y i s')
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : RecordAt tr y i R) :
    HeadSupport tr y i R :=
  -- the update clause is not needed here: joining at `t` already excludes the restarts after the
  -- latest view's slot started, which would clear the pools
  have h := head_support_at hrun hnc hy (ReadInv.of_full hinv hrun hnc hsl hy i (tr.time i)).service
    (fun _ hk => hrun.time_mono hk.le) (fun _ => readAt_self hrun hy hc hw hj) hR
  ⟨h.1, h.2⟩

/-- **The served-cut facts under `Sleepy`** (`ServedFacts`, the target of the Service
milestone's served-cut facts). -/
theorem sleepy_served_facts (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hs : ServedAt tr y i) :
    ServedFacts tr H y i :=
  have hinv := sleepy_invariant hrun hnc hsl
  have ⟨hc, hw, hj, _, hs', hu⟩ := hs
  ⟨fun _ hR => served_head_support hinv hrun hnc hsl hy hc hw hj hs'.ge hu hR,
    record_step hinv hrun hnc hy i⟩

end Consensus.Goldilocks.Compose

end
