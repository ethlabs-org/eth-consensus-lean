module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: what an origin carries to the next voters

The growing-fault forms of `Compose/Sleepy/Transport`. Each event is read with its node honest at
its own cut: the writer of an origin at its event cut `i₀`, the next voter at its vote cut `i`;
a vote or a head travels from the writer to the voter (`SleepyServiceFrom`, the service from a
start `a` with `a + κ ≤ t_s`) with the writer honest at its send or acceptance, which may be long
before a compromise that comes before the vote; a head the writer accepted before `a` reaches the
voter by the catch-up, before `a + κ`.

* `carryAt_of_writer_at`: `Carry_y` for votes released by a writer while honest in
  `[t_s, t_s + 2Δ)` whose heads, above the voter's `Σ.F`, are genesis or accepted by the writer
  while honest before `t_s + 2Δ`;
* `result_writer_at`: what a result's writer did with its counted votes (the analogue of
  `optimistic_writer_votes_at`);
* `result_carry_at`, `optimistic_carry_at`: `Carry_y` for the counted votes of an origin of label
  `s` at a slot-`(s+1)` vote whose `Σ.F` is at or below it;
* `result_writer_pool_at` (A1.8 (d)): every slot-`s` vote of the voter's merged view reaches the
  pool of the result's writer, honest at its update (`t_s + 6Δ`); the voter relays each vote it
  admitted while honest.

The voter's side is the static argument on the prefix through its vote, with the deliveries as
premises (`carryAt_of_delivered`); the deliveries come from the service. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

/-! ### One honest voter over an SA trace, with the deliveries given -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- **`Carry_y` from deliveries.** For an honest `y` casting its slot-`(s+1)` vote: if each
counted vote is of slot `s`, has a release time `τ ∈ [t_s, t_s + 2Δ)` at which it is served to
`y` (once `y`'s deadline for `τ` is at or before the vote), and has a head that is genesis or is
relayed to `y` from a time before `t_s + 2Δ` (likewise) or that `y` accepted before the freeze
`t_s + 3Δ`, then `Carry_y(s, ·, ·)` holds for the counted votes: `carryAt_of_served`, with the
frames closed under acceptance by `frame_anc_accepted`. This is the voter's side of
`carryAt_of_writer_heads`, without the sender. -/
theorem carryAt_of_delivered (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ τ, sp.ts s ≤ τ ∧ τ < sp.ts s + 2 * sp.Δ ∧
        (T.deadline y i τ ≤ T.time i → SA.MessageServedBefore T y i τ v)) ∧
      ∃ Hv : SA.Blk sp.n FGP, Hv.root = v.head ∧
        ((∃ τ, τ < sp.ts s + 2 * sp.Δ ∧ (T.deadline y i τ ≤ T.time i →
            ∃ k ≤ i, T.AcceptAt y k Hv ∧ T.time k < T.deadline y k τ)) ∨
          SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ))) :
    SA.CarryAt T U y i e s CV :=
  carryAt_of_served hr (frame_anc_accepted hr hy) hy hc hs hW

private theorem tryVote_pool (x : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) (σ : Nat) : A.pool σ ⊆ (SA.tryVote sp x A Φ t).1.pool σ := by
  unfold SA.tryVote
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  all_goals
    first
    | exact List.Subset.refl _
    | intro w hw
      rw [SA.optimistic_pool]
      exact SA.mem_admitVote_pool hw

private theorem foldl_admit_pool {t : Time} {σ : Nat} :
    ∀ (l : List (Vote sp.n)) (A : SA.SAState sp.n),
      A.pool σ ⊆ (l.foldl (fun A v => SA.admitVote sp A t v) A).pool σ
  | [], _ => List.Subset.refl _
  | _ :: l, _ => fun _ hw => foldl_admit_pool l _ (SA.mem_admitVote_pool hw)

/-- The receipt of a block admits each of its votes of the slot of `t` or the previous one: the
node holds it after the receipt, or two other votes of its validator. -/
private theorem blockReceipt_held (A : SA.SAState sp.n) {t : Time} {B : SA.Blk sp.n FGP}
    {v : Vote sp.n} (hv : v ∈ SA.blockVotes B) (h₁ : (sp.slot t : Int) - 1 ≤ v.slot)
    (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (SA.blockReceipt sp A t B).pool v.slot ∨
      v.val ∈ SA.equivocators {w | w ∈ (SA.blockReceipt sp A t B).pool v.slot} := by
  unfold SA.blockReceipt
  generalize ({ A with blockStamp := Function.update A.blockStamp B.root (SA.ETime.of t) } :
    SA.SAState sp.n) = A'
  generalize SA.blockVotes B = l at hv
  induction l generalizing A' with
  | nil => simp at hv
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · have hs := foldl_admit_pool (t := t) (σ := v.slot) l (SA.admitVote sp A' t v)
      rcases SA.admitVote_held A' t v h₁ h₂ with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · exact Or.inl (hs h)
      · exact Or.inr ⟨a, hs ha, b, hs hb, hab, hav, hbv⟩
    · exact ih _ hv

/-- **A slot-`s` vote of an honest voter's merged view of slot `s + 1`** is in the voter's pool
after a call at or before its vote, or two other votes of its validator are. -/
private theorem merged_in_pool (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) {s : Nat} (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      ∃ k ≤ i, v ∈ (T.state y (k + 1)).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (T.state y (k + 1)).pool s} := by
  rintro v (hv | ⟨B, hB, hBs, hvB⟩) hvs
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SA.SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    exact ⟨i, le_rfl, Or.inl (SA.readPoint_pool hr hy hc (by simpa using hv)).1⟩
  -- a vote of a slot-`(s+1)` block of the tree, which `y` accepted at a cut `k ≤ i`
  obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hc
  rcases SA.frame_genesis_or_accepted sp hr hy hc.1 B hB with h0 | ⟨k, hki, ℓk, hck, hcall⟩
  · omega
  have hBk : B.slot ≤ sp.slot (T.time k) := by
    rcases hr.frameLaw y hy k ℓk hck with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩ <;>
    · rw [hcall] at hok
      obtain ⟨-, -, -, h⟩ := hok
      exact h
  have hki' := SA.slot_mono sp (hr.time_nonneg k) (hr.time_mono hki)
  have he := hr.exec k ℓk hck.2 (hck.1 ▸ hy)
  rw [hck.1, hcall] at he
  have hpost : T.post k = (SA.tryVote sp y (SA.optimisticConfirmation sp
      (SA.blockReceipt sp (T.state y k) (T.time k) B) ℓk.frame (T.time k)) ℓk.frame
      (T.time k)).1 := (congrArg Prod.fst he).symm
  have hsub : ∀ w ∈ (SA.blockReceipt sp (T.state y k) (T.time k) B).pool s,
      w ∈ (T.state y (k + 1)).pool s := fun w hw => by
    rw [Trace.state_succ_of_call T hck, hpost]
    exact tryVote_pool _ _ _ _ _ (by rw [SA.optimistic_pool]; exact hw)
  refine ⟨k, hki, ?_⟩
  rcases blockReceipt_held (T.state y k) hvB (t := T.time k) (by omega) (by omega) with
    h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · rw [hvs] at h
    exact Or.inl (hsub v h)
  · rw [hvs] at ha hb
    exact Or.inr ⟨a, hsub a ha, b, hsub b hb, hab, hav, hbv⟩

end Node

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### From the writer to the voter -/

/-- **`Carry_y` from a writer, under growing faults**: for a node honest at its slot-`(s+1)` vote
at a time `≤ b`, with the service from `a` (`a + κ ≤ t_s`), `Carry_y(s, ·, ·)` holds for votes of
slot `s` that a writer `w` sent or admitted while honest at a time in `[t_s, t_s + 2Δ)`, whose
heads are above the voter's `Σ.F` and are genesis or accepted by `w` while honest before
`t_s + 2Δ`. A head accepted before `a` is caught up by the voter before `a + κ ≤ t_s`. -/
theorem carryAt_of_writer_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {s : Nat}
    (hsa : a + κ ≤ sp.ts s) {w y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hi : tr.time i ≤ b)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, w ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit w k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, w ∈ H (tr.time k) ∧ tr.projAC.AcceptAt w k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ)) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hsub := upTo_subset hrun hd
  have hΔ := sp.toParams.hΔ
  have ha : a ≤ sp.ts s := (le_add_of_nonneg_right hsync.kappa).trans hsa
  have hti : sp.ts s ≤ tr.time i := by
    have h := (castAt_spec_at hrun hnc hy hc).2.1
    rw [hs] at h
    exact (SA.ts_le_iff_le_slot sp hd (s : Int)).2 (by omega)
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hcarry := carryAt_of_delivered hr hy hc' hs (CV := CV) fun v hv => by
    obtain ⟨hvs, ⟨k, hwk, hsend, hk1, hk2⟩, Hv, hHvr, hFHv, hacc⟩ := hW v hv
    refine ⟨hvs, ⟨tr.time k, hk1, hk2, fun hdl => ?_⟩, Hv, hHvr, ?_⟩
    · rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm (le_refl _)] at hdl
      exact sa_messageServedBefore_upTo hm le_rfl (hsync.message w k v hwk hsend
        (ha.trans hk1) y i ℓ hy hc.1 (hdl.trans hi) hdl)
    rcases hacc with hg | ⟨kw, hwkw, hkw, hkwt⟩
    · exact Or.inr (Or.inl hg)
    by_cases hakw : a ≤ tr.time kw
    · refine Or.inl ⟨tr.time kw, hkwt, fun hdl => ?_⟩
      rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm (le_refl _)] at hdl
      obtain ⟨ky, hky, hacc', hkyt⟩ := hsync.acRelay w kw Hv hwkw hkw hakw y i ℓ
        hy hc.1 (hdl.trans hi) hdl hFHv
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ac_acceptAt_upTo _).mpr ⟨hkyd, hacc'⟩,
        by rw [ac_deadline_upTo (trA := tr.projAC) (d := tr.time i) hm hkyd]; exact hkyt⟩
    · -- a head accepted before `a`: caught up by the voter before `a + κ ≤ t_s`
      obtain ⟨ky, -, hacc', hkyt⟩ := hsync.acOld w kw Hv hwkw hkw (lt_of_not_ge hakw) y i ℓ
        hy hc.1 (hsa.trans hti) hFHv
      have hkyd : tr.time ky ≤ tr.time i := (hkyt.trans_le (hsa.trans hti)).le
      refine Or.inr (Or.inr ⟨ky, (ac_acceptAt_upTo _).mpr ⟨hkyd, hacc'⟩, ?_⟩)
      change tr.time ky < sp.ts s + 3 * sp.Δ
      linarith
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ac_acceptAt_upTo _).mp hk).2, hkt⟩

/-- **What a result's writer did with its counted votes**, for a writer honest at its update:
each was sent or admitted by it while honest at a time in `[t_s, t_s + 2Δ)`, and its head, held
while honest, extends the result and is genesis or was accepted by the writer while honest before
`t_s + 2Δ`. -/
theorem result_writer_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, X ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, X ∈ H (tr.time k) ∧ tr.projAC.AcceptAt X k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ) := by
  have hd := hrun.time_nonneg i₀
  have hsub := upTo_subset hrun hd
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hk1, hk2⟩, Hv, hHv, hHvr, hCHv, hacc⟩ :=
    result_writer (acRun_upTo hrun hnc hd).localRun hX
      ((sa_resultAt_upTo hrun.time_mono).mpr ⟨le_rfl, hR⟩) v hv
  obtain ⟨hkd, hk⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).mp hk
  refine ⟨hvs, ⟨k, hrun.antitone hkd hX, hk, hk1, hk2⟩, Hv, hsub hHv, hHvr, hCHv.mono hsub,
    hacc.imp_right fun ⟨k', hk', hk't⟩ => ?_⟩
  obtain ⟨hk'd, hk'⟩ := (ac_acceptAt_upTo _).mp hk'
  exact ⟨k', hrun.antitone hk'd hX, hk', hk't⟩

/-- **A result's counted votes reach the next voters** (`Carry_y`) under growing faults: the
writer honest at its update, the voter at its slot-`(s+1)` vote at a time `≤ b`, with the
voter's `Σ.F` at or below the result and the service from `a` (`a + κ ≤ t_s`). -/
theorem result_carry_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {X : Fin sp.n} {i₀ s : Nat}
    (hsa : a + κ ≤ sp.ts s)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (hX : X ∈ H (tr.time i₀))
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV :=
  carryAt_of_writer_at hrun hnc hsync hsa hy hc hs hib fun v hv => by
    obtain ⟨h₁, h₂, Hv, -, hHvr, hCHv, h₃⟩ := result_writer_at hrun hnc hX hR v hv
    exact ⟨h₁, h₂, Hv, hHvr, hF.trans hCHv, h₃⟩

/-- **An optimistic selection's counted votes reach the next voters** (`Carry_y`) under growing
faults, as `result_carry_at`, the checker honest at its check. -/
theorem optimistic_carry_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {X : Fin sp.n} {i₀ s : Nat} (hsa : a + κ ≤ sp.ts s)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hX : X ∈ H (tr.time i₀)) (hO : SA.OptimisticLockAt tr.projAC X i₀ s C CV) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV :=
  carryAt_of_writer_at hrun hnc hsync hsa hy hc hs hib fun v hv => by
    obtain ⟨h₁, h₂, Hv, -, hHvr, hCHv, h₃⟩ := optimistic_writer_votes_at hrun hnc hX hO v hv
    exact ⟨h₁, h₂, Hv, hHvr, hF.trans hCHv, h₃⟩

/-! ### The voter's slot-`s` votes reach the result's writer (A1.8 (d)) -/

/-- **A vote released while honest reaches an update**: a slot-`s` vote that a node honest then
sent or admitted at a time in `[t_s, t_s + 5Δ]` is held at an update of slot `s` (at
`t_s + 6Δ ≤ b`) of a writer honest then whose restarts are at or before `t_s`, or two other votes
of its validator are. -/
private theorem served_held_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {X x : Fin sp.n} {c s : Nat} (ha : a ≤ sp.ts s) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hX : X ∈ H (tr.time c))
    (hc : tr.projAC.CallAt X c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hcb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.projAC.RestartAt X k → tr.time k ≤ sp.ts s) {v : Vote sp.n}
    (hvs : v.slot = s) {k : Nat} (hx : x ∈ H (tr.time k)) (hsend : tr.projAC.SendOrAdmit x k v)
    (h1 : sp.ts s ≤ tr.time k) (h2 : tr.time k ≤ sp.ts s + 5 * sp.Δ) :
    v ∈ (tr.projAC.state X c).pool s ∨
      v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X c).pool s} := by
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg c
  have hr := acRun_upTo hrun hnc hd
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hrs' : ∀ k' ≤ c, tr.projAC.RestartAt X k' → tr.projAC.time k' ≤ tr.time k :=
    fun k' hk' hr' => (hrs k' hk' hr').trans h1
  have hdl := ac_deadline_le_of_restarts (T := tr.projAC) hrs' (tr.time k)
  change tr.projAC.deadline X c (tr.time k) ≤ max (tr.time k) (tr.time k) + sp.Δ at hdl
  rw [max_self] at hdl
  have hserv := hsync.message x k v hx hsend (ha.trans h1) X c ℓ hX hc
    (by linarith) (by linarith)
  have hserv' := sa_messageServedBefore_upTo (d := tr.time c) hrun.time_mono le_rfl hserv
  have h := SA.held_of_deadline_service hr.localRun hX
    (fun k' hk' hr' => hrs' k' hk' ((ac_restartAt_upTo tr.projAC).1 hr').2)
    (by change tr.time k + sp.Δ ≤ tr.time c; linarith)
    (fun t ht₁ ht₂ => by
      change tr.time k ≤ t at ht₁
      change t < tr.time k + sp.Δ at ht₂
      have ht0 : 0 ≤ t := (hrun.time_nonneg k).trans ht₁
      have hsl := (SA.ts_le_iff_le_slot sp ht0 s).1 (h1.trans ht₁)
      have hb : ¬ ((s + 2 : Nat) : Int) ≤ sp.slot t := fun h => by
        have := (SA.ts_le_iff_le_slot sp ht0 _).2 h
        rw [hts₂] at this; linarith only [this, ht₂, h2, hΔ]
      rw [hvs]
      clear * - hsl hb
      omega) hserv'
  rw [projAC_upTo_state hrun le_rfl, hvs] at h
  exact h

/-- **A1.8 (d) under growing faults**: for a result whose writer is honest at its update within
`b`, every slot-`s` vote of the merged view of a node honest at its slot-`(s+1)` vote is in the
writer's pool, or its validator equivocates there. The voter relays each vote it admitted while
honest; the writer receives it before its update (`t_s + 6Δ`). -/
theorem result_writer_pool_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {X : Fin sp.n} {i₀ s : Nat} (ha : a ≤ sp.ts s)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hX : X ∈ H (tr.time i₀)) (hR : SA.ResultAt tr.projAC X i₀ s C CV) (hi₀ : tr.time i₀ ≤ b)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨ℓX, hupd, -, -⟩ := hR
  have hd₀ := hrun.time_nonneg i₀
  have hrX := (acRun_upTo hrun hnc hd₀).localRun
  have hrsX : ∀ k ≤ i₀, tr.projAC.RestartAt X k → tr.time k ≤ sp.ts s := fun k hk hrk =>
    Compose.update_restarts hrX hX ((sa_updateAt_upTo hm).2 ⟨le_rfl, hupd⟩) k hk
      ((ac_restartAt_upTo tr.projAC).2 ⟨hm hk, hrk⟩)
  have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hupd.2.2.1
  -- the voter's side, on the prefix through its vote
  have hd := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc'
  change e.msg.slot = sp.slot (tr.time i) at hys
  change SA.joined sp e.readPoint (tr.time i) at hyj
  have hsi : sp.slot (tr.time i) = s + 1 := by omega
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h := (cast_head_fcRoot_at hrun hnc hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hrsy : ∀ k ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y k →
      tr.time k ≤ sp.ts s := by
    have hj' : SA.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc']; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) _ ro _ _ _ hr y hy i ℓ hc'.1 hj').2 k hk hrk
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at this
    rwa [hsi, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by push_cast; ring] at this
  -- every slot-`s` vote of the voter's pool up to its vote reaches the writer
  have hpool : ∀ k ≤ i, ∀ v ∈ ((tr.projAC.upTo (tr.time i)).state y (k + 1)).pool s,
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
    intro k hk v hv
    have hvs : v.slot = s := SA.state_pool_slot sp hr hy (k + 1) s v hv
    rcases SA.pool_origin hr hy (k + 1) v (hvs ▸ hv) with
      ⟨k', hk', hsend, -, hsl⟩ | ⟨k', hk', ℓk, hck, hrk, -, B, hB, hvB⟩
    · have hsk : sp.ts s ≤ tr.time k' :=
        (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k') s).2 (by rw [← hvs]; exact_mod_cast hsl)
      have hki : tr.time k' ≤ tr.time i := hm ((Nat.le_of_lt_succ hk').trans hk)
      obtain ⟨-, hsend⟩ := (ac_sendOrAdmit_upTo hm).mp hsend
      exact served_held_at hrun hnc hsync ha hX hupd.1 ht₀ hi₀ hrsX hvs (hrun.antitone hki hy)
        hsend hsk (hki.trans hti)
    · -- a restart's vote is of a block of slot at most `slot(t_{k'})`, so of slot below `s`
      exfalso
      have hBv := (SA.frame_validPayload sp hr hy hck B hB).1 v hvB
      have hBs := SA.frame_slot_le sp hr hy hck B hB
      change B.slot ≤ sp.slot (tr.time k') at hBs
      have htk := hrsy k' ((Nat.le_of_lt_succ hk').trans hk) ⟨ℓk, hck, hrk⟩
      have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (tr.time k') := fun h => by
        have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k') _).2 h
        rw [hts] at this; linarith only [this, htk, hΔ]
      clear * - this hBv hBs hvs
      omega
  intro v hv hvs
  obtain ⟨k, hki, h | ⟨a, ha, c, hc'', hac, hav, hcv⟩⟩ := merged_in_pool hr hy hc' hs v hv hvs
  · exact hpool k hki v h
  · rcases hpool k hki a ha with ha' | ha'
    · rcases hpool k hki c hc'' with hc' | hc'
      · exact Or.inr ⟨a, ha', c, hc', hac, hav, hcv⟩
      · exact Or.inr (hcv ▸ hc')
    · exact Or.inr (hav ▸ ha')

end Consensus.Goldilocks.Compose.Growing

end
