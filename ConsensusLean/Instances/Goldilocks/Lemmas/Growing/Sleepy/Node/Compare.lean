module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: origins of one label, and `P_{s+1}`

The growing-fault forms of the comparison part of `Compose/Sleepy/Compare`. Two origins of one
label `s` within `b` are compatible (`same_label_compatible_at`), each side read at its own cut:

* **result / result, result / optimistic** (relay only): a writer of a result honest at its
  update (`t_s + 6Δ`) counts more than half of its pool's voters, without equivocation, for its
  result; every vote the other writer released while honest (in `[t_s, t_s + 2Δ)`) reaches it,
  so the other side's validators are voters there and none counts for an incompatible result;
* **optimistic / optimistic**: the two `≥ 3n/4` voter sets meet in a validator honest at the later
  check `d` (`2 f_d < n`), whose one slot-`s` vote is in both pools.

`origins_below_succ_at`: `P_s` and `V_s` up to `b` give `P_{s+1}` up to `b` over the healed
family, through the honest supporter of a member's origin (`honest_supporter_at`), for a label `s`
whose slot count and service are available. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- `u` has a slot-`s` vote whose head extends `D` (inside the blocks held while honest), which
`X` sent or admitted while honest, at a time in `[t_s, t_s + 2Δ)`. -/
private def Released (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (X : Fin sp.n)
    (s : Nat) (D : SA.Blk sp.n (List (FG.Att sp.n))) : Set (Fin sp.n) :=
  {u | ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧
    (∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R) ∧
    ∃ k, X ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧
      tr.time k < sp.ts s + 2 * sp.Δ}

/-- Lift a forwarded vote of the prefix through `d` to a release while honest. -/
private theorem released_of_fwd (hrun : Growing.GoldilocksRun proposer dg H tr) {d : Time}
    (hd : 0 ≤ d) {X : Fin sp.n} (hX : X ∈ H d) {s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {u : Fin sp.n} (hu : u ∈ SA.Fwd (tr.projAC.upTo d) ((tr.upTo d).HonestBlocks (H d)) X s D) :
    u ∈ Released tr H X s D := by
  obtain ⟨v, hvu, hvs, ⟨R, hR, hRr, hDR⟩, k, hsend, h1, h2⟩ := SA.fwd_iff.1 hu
  obtain ⟨hkd, hsend⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).1 hsend
  exact ⟨v, hvu, hvs, ⟨R, upTo_subset hrun hd hR, hRr, hDR.mono (upTo_subset hrun hd)⟩, k,
    hrun.antitone hkd hX, hsend, h1, h2⟩

/-- **A result's side**, at the update of slot `s` (at `t_s + 6Δ`) of a writer honest then: its
restarts are at or before `t_s`; its counted validators `S` are more than half of its voters,
released by it while honest, and each has a non-equivocating pool vote extending the result. -/
private theorem result_side_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {Y : Fin sp.n} {c s : Nat} (hY : Y ∈ H (tr.time c))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksNode sp ro)) (S : Set (Fin sp.n)),
      tr.projAC.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (SA.voters {v | v ∈ (tr.projAC.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Released tr H Y s D ∧
      ∀ u ∈ S, u ∉ SA.equivocators {v | v ∈ (tr.projAC.state Y c).pool s} ∧
        ∃ v ∈ (tr.projAC.state Y c).pool s, v.val = u ∧
          ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R := by
  have hd := hrun.time_nonneg c
  have hr := acRun_upTo hrun hnc hd
  have hst := projAC_upTo_state hrun (y := Y) (le_refl (tr.time c))
  have hmaj := SA.result_majority hR
  obtain ⟨ℓ, hu, -, rfl⟩ := hR
  have hu' := (sa_updateAt_upTo hrun.time_mono).2 ⟨le_rfl, hu⟩
  obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hY hu.1
  refine ⟨ℓ, _, hu.1, hu.2.2.1, fun k hk hrk => ?_, hmaj, ?_, ?_⟩
  · exact Compose.update_restarts hr.localRun hY hu' k hk
      ((ac_restartAt_upTo tr.projAC).2 ⟨hrun.time_mono hk, hrk⟩)
  · rintro u ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvp' : v ∈ ((tr.projAC.upTo (tr.time c)).state Y c).pool s := hst.symm ▸ hvp
    have hvs := SA.state_pool_slot sp hr.localRun hY c s v hvp'
    obtain ⟨k, hsend, h1, h2⟩ := SA.admitted_of_held hr.localRun hY hvs hvp' le_rfl
      (fun k _ hstk => by
        rw [hst] at hstk
        have hst' : (tr.projAC.state Y c).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
          unfold SA.resolutionTime at hres
          split at hres
          · exact absurd hres (by simp [SA.ETime.of])
          · split_ifs at hres
            · exact absurd hres (by simp [SA.ETime.of])
            · exact lt_of_le_of_lt (le_max_left _ _) hres
        rw [hstk] at hst'
        exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst'))
    obtain ⟨hkc, hsend⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).1 hsend
    exact ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, k, hrun.antitone hkc hY, hsend,
      h1, h2⟩
  · rintro u ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- **An optimistic selection's seats**, at the check of a node honest then: three quarters of the
committee are optimistic voters of the selection, released by the checker while honest; an
optimistic voter honest at the check has its one slot-`s` vote there. -/
private theorem optimistic_side_at
    (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {k s : Nat} (hX : X ∈ H (tr.time k))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.OptimisticLockAt tr.projAC X k s D CV) :
    ∃ (ℓ : ACLabel (goldilocksNode sp ro)) (A : SA.SAState sp.n),
      ℓ.frame.tree ⊆ tr.HonestBlocksAt H ∧
      3 * sp.n ≤ 4 * (SA.optimisticVoters sp A ℓ.frame s D).ncard ∧
      SA.optimisticVoters sp A ℓ.frame s D ⊆ Released tr H X s D ∧
      ∀ v ∈ A.pool s, v.val ∈ H (tr.time k) →
        v.slot = s ∧ ∃ j ≤ k, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hd := hrun.time_nonneg k
  have hr := acRun_upTo hrun hnc hd
  obtain ⟨ℓ, A, hpt, hU, h34, hfwd⟩ := SA.optimistic_side hr hX
    ((sa_optimisticLockAt_upTo hrun.time_mono).2 ⟨le_rfl, hfl⟩)
  rw [hrun.stock] at h34
  refine ⟨ℓ, A, fun B hB => upTo_subset hrun hd (hU hB), h34,
    fun u hu => released_of_fwd hrun hd hX (hfwd hu), fun v hv hvH => ?_⟩
  obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote hr hX hpt hv hvH
  obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
  exact ⟨hvs, j, hj, e, hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, rfl⟩

/-- **A released vote reaches an update** of slot `s` (at `t_s + 6Δ ≤ b`) of a writer honest then,
with its restarts at or before `t_s`: the writer holds it, or two other votes of its validator.
The release is served with the sender honest at the release and the writer at its call. -/
private theorem released_held_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {X Y : Fin sp.n} {c s : Nat} (ha : a ≤ sp.ts s) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hY : Y ∈ H (tr.time c))
    (hc : tr.projAC.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hcb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {u : Fin sp.n} (hu : u ∈ Released tr H X s D) :
    ∃ v : Vote sp.n, v.val = u ∧
      (∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) D R) ∧
      (v ∈ (tr.projAC.state Y c).pool s ∨
        u ∈ SA.equivocators {w | w ∈ (tr.projAC.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hX, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have hd := hrun.time_nonneg c
  have hr := acRun_upTo hrun hnc hd
  have hrs' : ∀ k' ≤ c, tr.projAC.RestartAt Y k' → tr.projAC.time k' ≤ tr.time k :=
    fun k' hk' hr' => (hrs k' hk' hr').trans h1
  have hdl := ac_deadline_le_of_restarts (T := tr.projAC) hrs' (tr.time k)
  change tr.projAC.deadline Y c (tr.time k) ≤ max (tr.time k) (tr.time k) + sp.Δ at hdl
  rw [max_self] at hdl
  have hserv := hsync.message X k v hX hsend (ha.trans h1) Y c ℓ hY hc
    (by linarith) (by linarith)
  have hserv' := sa_messageServedBefore_upTo (d := tr.time c) hrun.time_mono le_rfl hserv
  have h := SA.held_of_deadline_service hr.localRun hY
    (fun k' hk' hr' => hrs' k' hk' ((ac_restartAt_upTo tr.projAC).1 hr').2)
    (by change tr.time k + sp.Δ ≤ tr.time c; linarith)
    (fun t ht₁ ht₂ => by
      change tr.time k ≤ t at ht₁
      change t < tr.time k + sp.Δ at ht₂
      rw [SA.CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]
      omega) hserv'
  rw [projAC_upTo_state hrun le_rfl, hvs] at h
  exact h

/-- **Against an update**: at the update of slot `s` of a writer honest then, whose counted
validators `S` support `DY` without equivocating, the validators `T` with votes for a block `D`
incompatible with `DY`, released while honest by another node, are voters there, none in `S`. -/
private theorem against_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {X Y : Fin sp.n} {c s : Nat} (ha : a ≤ sp.ts s) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hY : Y ∈ H (tr.time c))
    (hc : tr.projAC.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hcb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.projAC.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : SA.Blk sp.n (List (FG.Att sp.n))} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ SA.equivocators {v | v ∈ (tr.projAC.state Y c).pool s} ∧
      ∃ v ∈ (tr.projAC.state Y c).pool s, v.val = u ∧
        ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) DY R)
    (hT : T ⊆ Released tr H X s D) (hncp : ¬ Compatible (tr.HonestBlocksAt H) D DY) :
    T.ncard + S.ncard ≤ (SA.voters {v | v ∈ (tr.projAC.state Y c).pool s}).ncard := by
  have hU := honestBlocksAt_coherent hrun hnc
  have held := fun {u} (hu : u ∈ Released tr H X s D) =>
    released_held_at hrun hnc hsync ha hY hc ht hcb hrs hu
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hncp (Anc.total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

private theorem ncard_le_n (T : Set (Fin sp.n)) : T.ncard ≤ sp.n :=
  (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])

/-- **A result and an optimistic selection of one label are compatible** (relay only), the writer
honest at its update within `b`, the checker honest at its check. -/
theorem result_optimistic_compatible_at
    (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {s : Nat}
    (ha : a ≤ sp.ts s)
    {X x : Fin sp.n} {i i' : Nat} (hX : X ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hx : x ∈ H (tr.time i')) {C C' : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV CV' : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC X i s C CV)
    (hO : SA.OptimisticLockAt tr.projAC x i' s C' CV') :
    Compatible (tr.HonestBlocksAt H) C C' := by
  by_contra hncp
  obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := result_side_at hrun hnc hX hR
  obtain ⟨ℓo, Ao, -, h34, hT, -⟩ := optimistic_side_at hrun hnc hx hO
  have := against_update_at hrun hnc hsync ha hX hc ht hib hrs hS hT fun h => hncp (Or.symm h)
  have := ncard_le_n (SA.voters {v | v ∈ (tr.projAC.state X i).pool s})
  omega

/-- **Two origins within `b` of one label are compatible** (RR, RO, OO), each read at its own
cut; the shared validator of two optimistic selections is honest at the later check. -/
theorem same_label_compatible_at
    (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (ha : a ≤ sp.ts s) (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocksAt H) C C' := by
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨X, i, CV, hX, hi, hR | hO⟩ := originWithin_iff.1 hC <;>
    obtain ⟨X', i', CV', hX', hi', hR' | hO'⟩ := originWithin_iff.1 hC'
  · -- RR: each side's counted validators reach the other writer, where none supports it
    by_contra hncp
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := result_side_at hrun hnc hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := result_side_at hrun hnc hX' hR'
    have h1 := against_update_at hrun hnc hsync ha hX hc ht hi hrs hS hSF'
      fun h => hncp (Or.symm h)
    have h2 := against_update_at hrun hnc hsync ha hX' hc' ht' hi' hrs' hS' hSF hncp
    omega
  · exact result_optimistic_compatible_at hrun hnc hsync ha hX hi hX' hR hO'
  · exact Or.symm (result_optimistic_compatible_at hrun hnc hsync ha hX' hi' hX hR' hO)
  · -- OO: a validator honest at the later check is in both voter sets, with one slot-`s` vote
    by_contra hncp
    set d := max (tr.time i) (tr.time i')
    have hf := hB.two d ((hrun.time_nonneg i).trans (le_max_left _ _)) (max_le hi hi')
    obtain ⟨ℓ, A, hΦU, h34, -, hpool⟩ := optimistic_side_at hrun hnc hX hO
    obtain ⟨ℓ', A', hΦU', h34', -, hpool'⟩ := optimistic_side_at hrun hnc hX' hO'
    have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ℓ.frame s C)
      (SA.optimisticVoters sp A' ℓ'.frame s C')
    have := ncard_le_n (SA.optimisticVoters sp A ℓ.frame s C ∪
      SA.optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H d)ᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C ∩ SA.optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH : v.val ∈ H d := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ :=
      hpool v hv (hrun.antitone (le_max_left _ _) huH)
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      hpool' v' hv' (hv'u ▸ hrun.antitone (le_max_right _ _) huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := one_vote_per_slot_at hrun hnc he₁ he₂ (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hncp (Anc.total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- Two blocks below the head of one vote are compatible. -/
private theorem compatible_of_voteExtends (hU : Coherent (tr.HonestBlocksAt H)) {v : Vote sp.n}
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.VoteExtends (tr.HonestBlocksAt H) v C)
    (h' : SA.VoteExtends (tr.HonestBlocksAt H) v C') :
    Compatible (tr.HonestBlocksAt H) C C' := by
  obtain ⟨Hd, hHd, hHdr, hC⟩ := h
  obtain ⟨Hd', hHd', hHd'r, hC'⟩ := h'
  obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
  exact Anc.total hU hC hC'

/-- **Extending the healed frontier up to `b`**: `P_s` and `V_s` up to `b` give `P_{s+1}` up to
`b`, for a label `s` whose slot count and service are available (`σ₀ ≤ s`, `a ≤ t_s`). Each member
of label `s` is below an origin of its label (`HealedOrigin.below_origin`); a member of label
`s` and one of a label `j < s` are both below the head of that origin's honest supporter
(`honest_supporter_at`, then `V_s`); members of label `s` compare through their origins
(`same_label_compatible_at`). -/
theorem origins_below_succ_at
    (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {g : Time} {rL rO s : Nat} (hs : σ₀ ≤ s) (ha : a ≤ sp.ts s)
    (hP : HealedOriginsBelow tr H g rL rO s b) (hV : HealedVotesBelow tr H g rL rO s b) :
    HealedOriginsBelow tr H g rL rO (s + 1) b := by
  have hU := honestBlocksAt_coherent hrun hnc
  rw [healedOriginsBelow_iff] at hP ⊢
  have hnew : ∀ C C' j, j < s → HealedOrigin tr H g rL rO C s b →
      HealedOrigin tr H g rL rO C' j b → Compatible (tr.HonestBlocksAt H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
    obtain ⟨x, i, e, hv, hib, hes, hext⟩ := honest_supporter_at hrun hnc hsync hB hs ha hO
    exact compatible_of_voteExtends hU (voteExtends_of_anc hext hCO)
      (healedVotesBelow_iff.1 hV C' j hC' x i e hv hib (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · obtain ⟨O, hO, hCO⟩ := hC.below_origin hrun hnc
    obtain ⟨O', hO', hC'O'⟩ := hC'.below_origin hrun hnc
    exact compatible_of_anc_both hU hCO hC'O' (same_label_compatible_at hrun hnc hsync hB ha hO hO')

end Consensus.Goldilocks.Compose.Growing

end
