module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.CoefficientAdapters
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- An actual stored time-live lock gives the anchor arm only when its normalized
block still covers the record and the current live blocks form a chain. -/
theorem record_below_anchor_of_stored_live_lock
    {sp : SA.SAParams} {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {A : SA.SAState sp.n} {t : Time} {R B : SA.Blk sp.n FGP} {l : SA.Lock}
    (hl : l ∈ A.locks) (hB : B ∈ Φ.tree) (hroot : B.root = l.block)
    (ht : sp.slot t ≤ l.slot + sp.k) (hcover : Φ.Anc R (Φ.viableAncestor B))
    (hchain : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t,
      ∀ Y ∈ SA.liveLockBlocks sp A.locks Φ t, Goldilocks.Compatible Φ.tree X Y) :
    Φ.Anc R (SA.getAnchor sp A Φ t) := by
  have hmem : Φ.viableAncestor B ∈ SA.liveLockBlocks sp A.locks Φ t :=
    ⟨(SA.viableAncestor_anc hΦ hB).1,
      ⟨⟨(Φ.viableAncestor B).root, l.slot, l.fast⟩, ⟨l, hl, B, hB, hroot, ht, rfl⟩, rfl⟩⟩
  exact hcover.trans ((SA.anc_getAnchor hΦ hchain).2 _ (Or.inl hmem))

/-- Whole-record equality at the actual clock. Current source classification, viability
and live-candidate compatibility remain explicit, with no pre-repair invariant. -/
theorem read_eq_record_of_current_votes
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {a : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hrp : Regimes.ReadPoint tr i t) (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC)
    (hcatch : CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L)
    (hrecord : ∀ R, SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed = some R →
      (∀ X ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t ∪
          {(Node.frame (tr.state y i)).fcRoot},
        Goldilocks.Compatible (Node.frame (tr.state y i)).tree X R) ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
            e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R)))
    (hfault : Hᶜ.ncard <
      {x | x ∈ H ∧ tr.awake x (sp.ts L + sp.Δ) ∧ tr.JoinedAt x (sp.ts L + sp.Δ)}.ncard) :
    Regimes.readAfter tr y i t =
      (SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F := by
  have hΦ := Compose.frameOK_state hrun.toLocalRun hy i
  cases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact SA.acConfirmed_eq_F hΦ (SA.lookup_eq_none hl)
  | some R =>
    obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
    obtain ⟨hcomp, hsource⟩ := hrecord R hl
    have hanchor := Compose.anchor_compatible_of_live_candidates hΦ hcomp
    obtain ⟨hc, hs⟩ := Compose.read_head_support_of_target_votes hrun hnc hy ht0
      hrp.1 hrp.2 hw hj hsync hcatch hL ha hR hanchor hsource hfault
    exact SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)

/-- The source arm consumed by `read_eq_record_of_current_votes`: either actual anchor
coverage, or an actual recent raw witness covering the whole record. Its finite transfer
uses explicit current-domain and stored-lock comparisons, not last-setter recency. -/
theorem read_source_of_recent_result
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a b t : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {y : Fin sp.n} {i L : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (htb : t ≤ b)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∃ x ∈ H, ∃ r s C CV, SA.ResultAt tr.projAC x r s C CV ∧
          Anc (tr.HonestBlocks H) R C ∧ tr.time r ≤ b ∧
          Healing.cutZ sp.toParams g ≤ sp.ts s ∧ s < L ∧
          (∀ z ∈ H, ∀ q ell e, SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → s < e.msg.slot →
            (∀ w ∈ H, ∀ p < q, ∀ e', SA.VoteAt tr.projAC w p e' →
              s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg R) →
            Anc (tr.HonestBlocks H) R ell.frame.fcRoot ∨
              R ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) ∧
          (∀ z ∈ H, ∀ q ell e, SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state z q).locks,
              sp.slot (tr.time q) ≤ l.slot + sp.k → l.slot ≤ s →
              ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block →
                Goldilocks.Compatible (tr.HonestBlocks H) Y R))) :
    (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
          e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg R) := by
  rcases hsource with h | ⟨hv, x, hx, r, s, C, CV, hres, hRC, hrb, hts, hsL, hd, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv, hp.latest_votes_of_recent_result hc hx hres hRC hrb hts hd hl htb hsL⟩

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- The four directed record/F cases. Compatibility alone is insufficient:
the producer must supply directed record evolution as well as cache growth. -/
theorem effective_tip_step (Q : HealthyPreparationQuery S A V)
    {C C' F F' R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hC : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C')
    (hF : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F F')
    (hR : (R = C ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F C) ∨
      (R = F ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C F))
    (hR' : (R' = C' ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F' C') ∨
      (R' = F' ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C' F')) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  rcases hR with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    rcases hR' with ⟨rfl, hFC⟩ | ⟨rfl, hCF⟩
  · exact hC
  · exact hC.trans hCF
  · exact hF.trans hFC
  · exact hF

/-- Finite cut induction from explicit record evolution and effective-tip
dichotomies. The interval includes its start cut; no clock increase is needed. -/
theorem effective_tip_mono (Q : HealthyPreparationQuery S A V)
    (C F R : Nat → SA.Blk Q.params.n (List (FG.Att Q.params.n)))
    {i j : Nat} (hij : i ≤ j)
    (hC : ∀ k, i ≤ k → k < j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C k) (C (k + 1)))
    (hF : ∀ k, i ≤ k → k < j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (F k) (F (k + 1)))
    (hR : ∀ k, i ≤ k → k ≤ j →
      (R k = C k ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (F k) (C k)) ∨
      (R k = F k ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C k) (F k))) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (R i) (R j) := by
  have aux : ∀ k, i ≤ k → k ≤ j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (R i) (R k) := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base => intro _; exact .refl
    | succ k hik ih =>
      intro hkj
      exact (ih (by omega)).trans (effective_tip_step S A V Q
        (hC k hik (by omega)) (hF k hik (by omega))
        (hR k hik (by omega)) (hR (k + 1) (by omega) hkj))
  exact aux j hij le_rfl

/-- Actual tips below compatible origin witnesses are comparable. The read
producer must supply these witnesses at the actual stored-clock cuts, including
cuts preceding endCut heal; post-base preservation alone cannot do so. -/
theorem tips_comparable_of_origin_witnesses (Q : HealthyPreparationQuery S A V)
    {R R' C C' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C)
    (hR' : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R' C')
    (hCC : Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hU := Compose.honest_blocks_coherent
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases hCC with h | h
  · exact Anc.total hU (hR.trans h) hR'
  · exact Anc.total hU hR (hR'.trans h)

/-- Common recent-origin comparison, including the genesis alternative.
Membership and chain coverage must concern the actual read tips, not just caches. -/
theorem tips_comparable_of_origin_chain (Q : HealthyPreparationQuery S A V)
    {s₀ : Nat} {R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : R ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2))
    (hR' : R' ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2))
    (hc : Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) R s₀)
    (hc' : Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) R' s₀)
    (hcomp : ∀ C p C' p', Compose.OriginFrom Q.trace (honestKeys S Q.run.2) C p s₀ →
      Compose.OriginFrom Q.trace (honestKeys S Q.run.2) C' p' s₀ →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hU := Compose.honest_blocks_coherent hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases Compose.onOriginChainFrom_iff.1 hc with hg | ⟨C, p, hp, hRC⟩
  · rw [Compose.honest_eq_genesis hr hU hR hg]
    exact Or.inl (Compose.honest_genesis_anc hr hR').2
  rcases Compose.onOriginChainFrom_iff.1 hc' with hg | ⟨C', p', hp', hRC'⟩
  · rw [Compose.honest_eq_genesis hr hU hR' hg]
    exact Or.inr (Compose.honest_genesis_anc hr hR).2
  exact tips_comparable_of_origin_witnesses S A V Q hRC hRC' (hcomp C p C' p' hp hp')

/-- A read-support producer at genuine read points suffices at stored engine clocks.
The representative is the last local event, not the original global cut. -/
theorem healthy_stored_read_eq_record (Q : HealthyPreparationQuery S A V)
    {c t₀ : Time} (hc : 0 ≤ c)
    (hread : ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
      Regimes.ReadPoint Q.trace k t →
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t → t₀ ≤ t → t ≤ Q.run.2.horizon →
      Regimes.readAfter Q.trace y k t =
        (SA.lookup (Node.frame (Q.trace.state y k))
          (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)
    {v : V} {i : Nat} (hi : i ≤ Q.run.2.events.length)
    (hfloor : t₀ ≤ (stateAt S Q.run.2 Q.hn v i).now)
    (hr : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i)) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now =
      (SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F := by
  have hready := ready_at_stored_now S Q.run.2 Q.hn Q.valid hi hc hr
  obtain ⟨q, hq, hs, hrp, hth⟩ : ∃ q ≤ Q.run.2.events.length,
      stateAt S Q.run.2 Q.hn v i = stateAt S Q.run.2 Q.hn v q ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q)
        (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with hs | ⟨j, hj, e, he, hev, hs, ht⟩
    · refine ⟨0, Nat.zero_le _, hs, ?_, ?_⟩
      · rw [hs, cutMap_zero]
        exact ⟨fun k hk => by omega,
          (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).time_nonneg 0⟩
      · rw [hs]
        exact Q.valid.horizon_nonneg
    · refine ⟨j + 1, by omega, hs, ?_, ?_⟩
      · rw [ht]
        exact readPoint_after_event S Q.run.2 Q.hn Q.valid he
      · rw [ht]
        exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).2
  have hnready := ready_transport S Q.run.2 Q.hn Q.valid
    (now_bounds_cut S Q.run.2 Q.hn Q.valid v hi).1 hth hready
  have heq := hread _ _ _ ⟨q, hq, rfl⟩ hrp hnready hfloor hth
  have hstate : Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
      Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q) := by
    rw [← simTrace_state S Q.run.2 Q.hn Q.valid v hr.1 i hi,
      ← simTrace_state S Q.run.2 Q.hn Q.valid v hr.1 q hq, hs]
  simpa only [Regimes.readAfter, hstate] using heq

/-- A semantic repair completed within `B` from ready is strictly before the stored
clock, even at a cut exactly at heal and before the reader's same-time tick. `K` shares
the coefficient envelope; no repair budget is inferred from reset or drain alone. -/
theorem healthy_repair_floor_at_stored_now (Q : HealthyPreparationQuery S A V)
    {c d C h B K r τ : Time} (hc : 0 ≤ c) (hd : 1 ≤ d) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hready : Q.ready = max Q.gst 0 + C * d + 1)
    (hheal : Q.heal = max Q.gst 0 + h * d)
    (hbudget : C + 2 * max B K + r + 3 ≤ h)
    (hrepair : τ ≤ Q.ready + (B * (d + 1) + r))
    {v : V} {i : Nat} (hi : i ≤ Q.run.2.events.length)
    (hcut : Q.heal ≤ Q.run.2.cutTime i)
    (hv : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i)) :
    τ + 1 ≤ (stateAt S Q.run.2 Q.hn v i).now := by
  have hstrict : τ < Q.heal - 1 := by
    rw [hheal]
    apply repair_lt_heal_sub_one hd hB hr hbudget
    rwa [hready] at hrepair
  have hlag := stored_now_ge_cutTime_sub_one S Q.run.2 Q.hn Q.valid hi hc hv
  exact Int.add_one_le_iff.mpr (hstrict.trans_le ((sub_le_sub_right hcut 1).trans hlag))

/-- Once established at the original starting cut, the repair floor persists forward
through the original interval. No ordering of last-local-event representatives is used. -/
theorem healthy_repair_floor_interval (Q : HealthyPreparationQuery S A V)
    {v : V} {i : Nat} {τ : Time}
    (hfloor : τ + 1 ≤ (stateAt S Q.run.2 Q.hn v i).now) :
    ∀ j, i ≤ j → τ + 1 ≤ (stateAt S Q.run.2 Q.hn v j).now := by
  intro j hij
  exact hfloor.trans (now_mono S Q.run.2 Q.hn Q.valid v hij)

/-- The finite reset consumer starts strictly after actual repair completion, not at
the endCut-heal state. The semantic completion bound and post-repair read producer are
separate hypotheses; scoped service remains in the supplied reset premises. -/
theorem healthy_stored_read_eq_record_after_repair (Q : HealthyPreparationQuery S A V)
    {c d C h B K r τ ΔF a : Time}
    (hp : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon)
    (hc : 0 ≤ c) (hd : 1 ≤ d) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hready : Q.ready = max Q.gst 0 + C * d + 1)
    (hheal : Q.heal = max Q.gst 0 + h * d)
    (hbudget : C + 2 * max B K + r + 3 ≤ h)
    (hrepair : τ ≤ Q.ready + (B * (d + 1) + r))
    (hread : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon →
      ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
        Regimes.ReadPoint Q.trace k t →
        Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t →
        τ < t → t ≤ Q.run.2.horizon →
        Regimes.readAfter Q.trace y k t =
          (SA.lookup (Node.frame (Q.trace.state y k))
            (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)
    {v : V} {i : Nat} (hi : i ≤ Q.run.2.events.length)
    (hcut : Q.heal ≤ Q.run.2.cutTime i)
    (hv : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i)) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now =
      (SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F := by
  apply healthy_stored_read_eq_record S A V Q hc
    (t₀ := τ + 1) (fun y k t hk hpoint hready ht htb =>
      hread hp y k t hk hpoint hready (Int.add_one_le_iff.mp ht) htb) hi
  · exact healthy_repair_floor_at_stored_now S A V Q hc hd hB hr
      hready hheal hbudget hrepair hi hcut hv
  · exact hv

section ConditionalSafety
variable (Q : HealthyPreparationQuery S A V) {c t₀ ΔF a : Time}
  (hsync : Healing.ResetService Q.trace (honestKeys S Q.run.2)
    Q.gst ΔF Q.run.2.horizon)
  (hreset : Healing.IsReset Q.trace (honestKeys S Q.run.2) Q.gst a)
  (ha : a ≤ Q.run.2.horizon)
  (hsnapshot : ∃ k, Healing.FirstCutAfter Q.trace k
    (Healing.cutZ Q.params.toParams Q.gst) ∧ Q.trace.time k ≤ Q.run.2.horizon)
  (hc : 0 ≤ c)
  (hread : ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
    Regimes.ReadPoint Q.trace k t →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t → t₀ ≤ t → t ≤ Q.run.2.horizon →
    Regimes.readAfter Q.trace y k t =
      (SA.lookup (Node.frame (Q.trace.state y k))
        (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)

include hsync hreset ha hsnapshot hc hread

/-- Directed record preservation is transported at the original ordered engine cuts;
only read support is evaluated at the last local event. -/
theorem healthy_cut_tips_ancestor_of_interval
    {v : V} {i j : Nat} (hi : i ≤ Q.run.2.events.length)
    (hj : j ≤ Q.run.2.events.length) (hij : i ≤ j)
    (hfloori : t₀ ≤ (stateAt S Q.run.2 Q.hn v i).now)
    (hfloorj : t₀ ≤ (stateAt S Q.run.2 Q.hn v j).now)
    (hvi : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i))
    (hvj : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime j))
    (hinterval : EffectiveRecordInterval Q.trace (honestKeys S Q.run.2) (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (cutMap S Q.run.2 Q.hn j)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  have hp := reset_premises_of_healthy_query S A V Q hsync hreset ha hsnapshot
  have hri := healthy_stored_read_eq_record S A V Q hc hread hi hfloori hvi
  have hrj := healthy_stored_read_eq_record S A V Q hc hread hj hfloorj hvj
  rw [hrj]
  exact effective_record_of_interval hp.run hp.noColl
    (honest_ownKey (S := S) hvi.1) (cutMap_mono S Q.run.2 Q.hn hij) hinterval
      (by rw [hri]; exact .refl)

end ConditionalSafety

/-- Finite schedule to be synthesized from the original healthy progress interval.
The window pays for the opening and its update, with strict pre-read reserve. -/
structure HealthyRepairSchedule (Q : HealthyPreparationQuery S A V) where
  resetTime : Time
  deltaF : Time
  reset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
    (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst deltaF resetTime Q.run.2.horizon
  cleanLabel : Nat
  cleanLabel_eq : cleanLabel = Healing.cleanLabel Q.params resetTime
  duration_bound : 18 * Q.params.Δ ≤ (Sys (family S) V).cDur (K S A) Q.run
  oldLabel : Nat
  old_bound : cleanLabel + 2 * Q.params.k + 1 ≤ oldLabel
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts oldLabel) (max (SA.gbar Q.gst + 4 * Q.params.Δ) 0))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

/-- An operational opening; no unguarded support-head premise is included. -/
structure HealthyRepairOpening (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) where
  slot : Nat
  cut : Nat
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  fresh : D.query < Q.params.ts slot
  bounded : Q.params.ts slot ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ
  old_lt : D.oldLabel < slot
  label : block.slot = slot
  proposes : Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn slot) cut block
  accepts : Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn slot) cut block
  time : Q.trace.time cut = Q.params.ts slot
  ready : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run)
    (runProposer S Q.run.2 Q.hn slot) (Q.params.ts slot)

/-- Immediate receiver repair at its actual update. This says nothing about later
canonical reads. A retained optimistic source may have label u+1 and is not mature
at this update; no latest-view inequality follows. A missing lookup needs no cover. -/
def HealthyReceiverRepair (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) (O : HealthyRepairOpening S A V Q D) : Prop :=
  ∀ y ∈ honestKeys S Q.run.2,
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y
      (Q.params.ts O.slot + 6 * Q.params.Δ) → ∃ j ell,
    SA.UpdateAt Q.trace.projAC y j O.slot ell ∧
    Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ ∧
    Q.trace.time j ≤ Q.run.2.horizon ∧
    ∀ R, SA.lookup (Node.frame (Q.trace.state y (j + 1)))
      (Q.trace.state y (j + 1)).ac.latestConfirmed = some R →
      ∃ x ∈ honestKeys S Q.run.2, ∃ q s C CV,
        q ≤ j ∧ Q.trace.time q ≤ Q.trace.time j ∧ D.oldLabel ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨
          SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C

/-- Coverage of the effective current record, not recency of its own setter.
Maturity and anchor geometry are separate read-certificate obligations. -/
def HealthyRecordCover (Q : HealthyPreparationQuery S A V) (cleanLabel : Nat)
    (y : Fin Q.params.n) (n : Nat) (R : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  R = (Q.trace.state y n).fg.F ∨ ∃ x ∈ honestKeys S Q.run.2, ∃ q s C CV,
    q < n ∧ Q.trace.time q ≤ Q.run.2.horizon ∧ cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
    (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C

/-- The last local representative and finite service at the actual stored clock.
No record geometry is part of this context. -/
structure HealthyReadContext (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) (v : V) (i : Nat) where
  cut : Nat
  state_eq : Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
    Q.trace.state (Q.run.2.ownKey v) cut
  label : Nat
  time_nonneg : 0 ≤ (stateAt S Q.run.2 Q.hn v i).now
  time_bound : (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon
  repaired : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
    (stateAt S Q.run.2 Q.hn v i).now
  readPoint : Regimes.ReadPoint Q.trace cut (stateAt S Q.run.2 Q.hn v i).now
  awake : Q.trace.awake (Q.run.2.ownKey v) (stateAt S Q.run.2 Q.hn v i).now
  joined : Q.trace.JoinedAt (Q.run.2.ownKey v) (stateAt S Q.run.2 Q.hn v i).now
  latest : (label : Int) = (SA.latestView Q.params
    (Q.trace.state (Q.run.2.ownKey v) cut).ac
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) cut)) (stateAt S Q.run.2 Q.hn v i).now).2
  reset_le : D.resetTime ≤ Q.params.ts label
  sync : SyncACWindowBefore (honestKeys S Q.run.2)
    (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D.resetTime
    (stateAt S Q.run.2 Q.hn v i).now Q.trace.projAC
  catchup : CatchACWindowBefore Q.trace.projAC (honestKeys S Q.run.2)
    (Q.trace.HonestBlocks (honestKeys S Q.run.2)) D.resetTime (2 * Q.params.Δ)
    (stateAt S Q.run.2 Q.hn v i).now
  fault : (honestKeys S Q.run.2)ᶜ.ncard <
    {x | x ∈ honestKeys S Q.run.2 ∧ Q.trace.awake x (Q.params.ts label + Q.params.Δ) ∧
      Q.trace.JoinedAt x (Q.params.ts label + Q.params.Δ)}.ncard

section EndpointProducers
variable (Q : HealthyPreparationQuery S A V)
  (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
  (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
    Q.ready Q.heal Q.run)
  (W : HealthyBaseTiming S A V Q)
  (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
    HealthyStateFacts S A V Q W.slot k)

include h0 hb hp W states

/-- OPEN reset/snapshot, old threshold and joint coefficient/window producer. -/
theorem healthy_repair_schedule : Nonempty (HealthyRepairSchedule S A V Q) := by
  sorry

/-- OPEN existence of a bounded operational opening that repairs every ready receiver.
Proof route: opening → operational unanimity → held-only selection → receiver repair.
Unanimity and live-lock comparison are not inferred from operational opening data alone;
no `Healing.ReadyProposal` unguarded-support clause is assumed. -/
theorem healthy_bounded_repairing_opening (D : HealthyRepairSchedule S A V Q) :
    ∃ O : HealthyRepairOpening S A V Q D, HealthyReceiverRepair S A V Q D O := by
  sorry

/-- OPEN canonical transport and renewal for the CURRENT record. The actual read
clock must be strictly after the opening update; old overwritten records are not covered. -/
theorem healthy_current_record_sources (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
      ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  sorry

omit h0 hb hp W states in
/-- The representative of a healthy stored-clock read is after the repair deadline,
including observations at heal before the reader's same-time tick. -/
theorem healthy_read_representative (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∃ q ≤ Q.run.2.events.length,
      Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
        Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q) ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q) (stateAt S Q.run.2 Q.hn v i).now ∧
      0 ≤ (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon ∧
      D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
        (stateAt S Q.run.2 Q.hn v i).now ∧
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run - 1) (Q.run.2.ownKey v)
        (stateAt S Q.run.2 Q.hn v i).now := by
  have hi' : i ≤ Q.run.2.events.length := hi.1
  have hc : 0 ≤ (Sys (family S) V).cDur (K S A) Q.run - 1 := by
    have hd := D.duration_bound
    have hΔ := Q.params.toParams.hΔ
    change 0 < Q.params.Δ at hΔ
    have hΔ1 : 1 ≤ Q.params.Δ := hΔ
    linarith
  have hr : Q.run.2.point.Ready (((Sys (family S) V).cDur (K S A) Q.run - 1) + 1)
      v (Q.run.2.cutTime i) := by simpa only [sub_add_cancel, chainTrace] using hv
  have hlag := stored_now_ge_cutTime_sub_one S Q.run.2 Q.hn Q.valid hi.1 hc hr
  have hfloor : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
      (stateAt S Q.run.2 Q.hn v i).now := by
    have hh : Q.heal ≤ Q.run.2.cutTime i := hi.2
    linarith [D.reserve]
  have ht0 := (now_bounds_cut S Q.run.2 Q.hn Q.valid v hi.1).1
  obtain ⟨q, hq, hs, hrp, hth⟩ : ∃ q ≤ Q.run.2.events.length,
      stateAt S Q.run.2 Q.hn v i = stateAt S Q.run.2 Q.hn v q ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q)
        (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with hs | ⟨j, hj, e, he, hev, hs, ht⟩
    · refine ⟨0, Nat.zero_le _, hs, ?_, ?_⟩
      · rw [hs, cutMap_zero]
        exact ⟨fun k hk => by omega, D.reset.run.time_nonneg 0⟩
      · rw [hs]
        exact Q.valid.horizon_nonneg
    · refine ⟨j + 1, by omega, hs, ?_, ?_⟩
      · rw [ht]
        exact readPoint_after_event S Q.run.2 Q.hn Q.valid he
      · rw [ht]
        exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).2
  refine ⟨q, hq, ?_, hrp, ht0, hth, hfloor, ?_⟩
  · rw [← simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 i hi.1,
      ← simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 q hq, hs]
  · exact ready_transport S Q.run.2 Q.hn Q.valid ht0 hth
      (ready_at_stored_now S Q.run.2 Q.hn Q.valid hi.1 hc hr)

omit h0 hb hp W states in
/-- After drain, the latest view is a natural label beyond the reset, and its
voting time is no later than the read. -/
theorem healthy_read_label (D : HealthyRepairSchedule S A V Q)
    (ac : SA.SAState Q.params.n) (frame : SA.Frm Q.params.n (List (FG.Att Q.params.n)))
    {t : Time} (ht0 : 0 ≤ t)
    (ht : Healing.drainTime Q.params D.resetTime ≤ t) :
    ∃ L : Nat, (L : Int) = (SA.latestView Q.params ac frame t).2 ∧
      D.resetTime ≤ Q.params.ts L ∧ Q.params.ts L + Q.params.Δ ≤ t := by
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hslot : (Q.params.slot D.resetTime + 2 * Q.params.k + 5 : Nat) ≤ Q.params.slot t := by
    rw [Healing.drainTime_eq] at ht
    exact_mod_cast (SA.ts_le_iff_le_slot Q.params ht0 _).mp ht
  have hpos : 0 < Q.params.slot t := by omega
  have ha0 : 0 ≤ D.resetTime := by
    obtain ⟨⟨y, hy, k, att, hk, _, he⟩, _⟩ := D.reset.reset
    exact he ▸ D.reset.run.time_nonneg k
  have ha : D.resetTime < Q.params.ts (Q.params.slot D.resetTime + 1 : Nat) := by
    have hh := Int.lt_ediv_add_one_mul_self D.resetTime (by linarith : 0 < 4 * Q.params.Δ)
    rw [← SA.slot_eq Q.params ha0] at hh
    simpa only [SA.SAParams.ts, Nat.cast_add, Nat.cast_one, mul_comm] using hh
  have htlo := (SA.ts_le_iff_le_slot Q.params ht0 (Q.params.slot t)).mpr le_rfl
  by_cases hphase : Q.params.ts (Q.params.slot t) + 2 * Q.params.Δ ≤ t
  · refine ⟨Q.params.slot t, ?_, ?_, by linarith⟩
    · simp only [SA.latestView, ite_eq_left hphase]
    · exact ha.le.trans ((SA.ts_le_iff Q.params).mpr (by exact_mod_cast (by omega :
        Q.params.slot D.resetTime + 1 ≤ Q.params.slot t)))
  · refine ⟨Q.params.slot t - 1, ?_, ?_, ?_⟩
    · simp only [SA.latestView, ite_eq_right hphase]
      omega
    · exact ha.le.trans ((SA.ts_le_iff Q.params).mpr (by exact_mod_cast (by omega :
        Q.params.slot D.resetTime + 1 ≤ Q.params.slot t - 1)))
    · have hs : ((Q.params.slot t - 1 : Nat) : Int) = (Q.params.slot t : Int) - 1 := by omega
      simp only [SA.SAParams.ts] at htlo ⊢
      rw [hs]
      nlinarith

/-- OPEN current anchor candidates are compatible with the current looked-up record. -/
theorem healthy_current_live_candidates (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now ∪
        {(Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot},
      Goldilocks.Compatible (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree X R := by
  sorry

/-- OPEN pairwise compatibility of normalized current live locks. -/
theorem healthy_current_live_chain (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now,
      ∀ Y ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now,
      Goldilocks.Compatible (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree X Y := by
  sorry

/-- OPEN actual anchor coverage or a mature raw witness; a young optimistic origin
does not satisfy the raw arm merely because it was produced before this read. -/
theorem healthy_current_mature_or_anchor (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (SA.getAnchor Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now) ∨
    ∃ x ∈ honestKeys S Q.run.2, ∃ r s B CV,
      SA.ResultAt Q.trace.projAC x r s B CV ∧
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B ∧
      Q.trace.time r ≤ Q.run.2.horizon ∧ Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s ∧
      D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧ s < C.label := by
  sorry

/-- OPEN current viability for a record supported by a mature result. -/
theorem healthy_current_record_viable (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s) (hL : s < C.label)
    (hfc : ¬ (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot)
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    R ∈ (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).viableTree
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree := by
  sorry

omit h0 hb hp W states in
/-- M4 vote-domain input from the bounded actual-result theorem. -/
theorem healthy_current_vote_domain (D : HealthyRepairSchedule S A V Q)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2) Q.gst (2 * Q.params.Δ))
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : D.cleanLabel + Q.params.k + 2 ≤ s) :
    ∀ z ∈ honestKeys S Q.run.2, ∀ q ell e, SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.run.2.horizon → s < e.msg.slot →
      (∀ w ∈ honestKeys S Q.run.2, ∀ p < q, ∀ e', SA.VoteAt Q.trace.projAC w p e' →
        s < e'.msg.slot → SA.VoteExtends (Q.trace.HonestBlocks (honestKeys S Q.run.2)) e'.msg R) →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R ell.frame.fcRoot ∨
        R ∈ ell.frame.viableTree (SA.voterBlockTree Q.params e.readPoint ell.frame e.msg.slot) := by
  intro z hz q ell e he hqb hse hprior
  exact D.reset.result_prefix_vote_domain_before hc hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb he hse hqb hprior

omit h0 hb hp W states in
/-- Finite catch service follows directly from the healthy engine's PSync and awake interval. -/
theorem healthy_repair_catch :
    Healing.CatchRun Q.trace (honestKeys S Q.run.2) Q.gst (2 * Q.params.Δ) := by
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst := by
    constructor
    · intro v hv o s hs w hw a hsa hc hh haw
      have h := Q.healthy.1.msgs v hv ⟨Q.run.1, o⟩ s ⟨o, rfl, hs⟩ w hw a hsa hc hh haw
      rcases h with ⟨u, hu, hsent | hrecv, hnowake⟩
      · obtain ⟨o', he, hs'⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl hs', hnowake⟩
      · obtain ⟨o', he, hr'⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr hr', hnowake⟩
    · exact Q.healthy.1.txs
  exact catchRun_of_psync S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    hnet Q.healthy.2.2

-- Preserve the producer's existing section hypotheses although the finite adapter needs fewer.
set_option linter.unusedSectionVars false in
/-- Comparison against actually stored time-live locks at the first successor. -/
theorem healthy_current_stored_locks (D : HealthyRepairSchedule S A V Q)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s) :
    ∀ z ∈ honestKeys S Q.run.2, ∀ q ell e, SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.run.2.horizon → e.msg.slot = s + 1 →
      ∀ l ∈ (Q.trace.projAC.state z q).locks, Q.params.slot (Q.trace.time q) ≤ l.slot + Q.params.k →
        l.slot ≤ s → ∀ Y ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2), Y.root = l.block →
          Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Y R := by
  intro z hz q ell e he hqb hes
  have hrun := (Compose.goldilocks_ac_projection _ _ _ _ _ _
    D.reset.run D.reset.noColl).localRun
  have hslot := (SA.castAt_spec hrun hz he).2.1
  exact D.reset.result_prefix_stored_locks (healthy_repair_catch S A V Q) hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb hqb (by
      change s + 1 ≤ Q.params.slot (Q.trace.time q)
      change e.msg.slot = Q.params.slot (Q.trace.time q) at hslot
      omega)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Stored-clock representative, repair floor and finite service producer.
The existing endpoint signature is retained; record repair is not needed for service. -/
theorem healthy_current_read_context (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) : Nonempty (HealthyReadContext S A V Q D v i) := by
  obtain ⟨q, hq, heq, hread, ht0, htb, hrepairTime, hready⟩ :=
    healthy_read_representative S A V Q D hi hv
  have hΔ := Q.params.toParams.hΔ
  have hquery : D.query ≤ (stateAt S Q.run.2 Q.hn v i).now := by
    have hindex : (0 : Int) ≤ (Q.index : Time) := Int.natCast_nonneg _
    nlinarith
  have hdrain := (le_max_of_le_right (le_max_left _ _)).trans D.lower
  obtain ⟨L, hL, haL, hLt⟩ := healthy_read_label S A V Q D
    (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q)).ac
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q)))
    ht0 (hdrain.trans hquery)
  have haw := Compose.ready_implies_joined Q.params _ _ _ _ _ D.reset.run
    (Q.run.2.ownKey v) (honest_ownKey (S := S) hv.1) _
    ((Sys (family S) V).cDur (K S A) Q.run - 1) ht0
    (by have := D.duration_bound; linarith) hready.2
  have hza : Healing.cutZ Q.params.toParams Q.gst < D.resetTime :=
    Healing.cutZ_lt_reset_of_snapshot D.reset.run
      (by obtain ⟨k, hk, _⟩ := D.reset.snapshot; exact ⟨k, hk⟩) D.reset.reset
  exact ⟨{ cut := cutMap S Q.run.2 Q.hn q
           state_eq := heq
           label := L
           time_nonneg := ht0
           time_bound := htb
           repaired := hrepairTime
           readPoint := hread
           awake := haw.1
           joined := haw.2
           latest := hL
           reset_le := haL
           sync := Healing.sync_window_at_reset_of_reset_before D.reset htb
           catchup := Healing.catch_window_at_reset_of_reset_catch_before D.reset
             (healthy_repair_catch S A V Q) htb
           fault := Healing.fault_bound_late_before D.reset (by linarith) (hLt.trans htb) }⟩

/-- Assemble the current whole-record certificate through the landed scoped adapters. -/
theorem healthy_current_record_read (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now =
      (SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F := by
  obtain ⟨C⟩ := healthy_current_read_context S A V Q h0 hb hp W states D O hrepair hi hv
  have hc := healthy_repair_catch S A V Q
  have heq := read_eq_record_of_current_votes D.reset.run D.reset.noColl
    (honest_ownKey (S := S) hv.1) C.time_nonneg C.readPoint C.awake C.joined
    C.sync C.catchup C.latest C.reset_le (fun R hR => ⟨
      healthy_current_live_candidates S A V Q h0 hb hp W states D C hR, ?_⟩) C.fault
  · simpa only [Regimes.readAfter, C.state_eq] using heq
  apply read_source_of_recent_result D.reset hc C.time_bound
  by_cases hfc : (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot
  · exact Or.inl (hfc.trans ((SA.anc_getAnchor
      (Compose.frameOK_state D.reset.run.toLocalRun (honest_ownKey (S := S) hv.1) C.cut)
      (healthy_current_live_chain S A V Q h0 hb hp W states D C)).2 _ (Or.inr rfl)))
  rcases healthy_current_mature_or_anchor S A V Q h0 hb hp W states D O hrepair C hR with
    ha | ⟨x, hx, r, s, B, CV, hr, hRB, hrb, hs, hlate, hL⟩
  · exact Or.inl ha
  exact Or.inr ⟨healthy_current_record_viable S A V Q h0 hb hp W states D C
    hx hr hRB hrb hs hL hfc hR, x, hx, r, s, B, CV, hr, hRB, hrb, hs, hL,
    healthy_current_vote_domain S A V Q D hc hx hr hRB hrb
      (by have := Q.params.two_le_k; omega),
    healthy_current_stored_locks S A V Q h0 hb hp W states D hx hr hRB hrb hlate⟩

omit h0 hb hp W states in
/-- Bound completed events, not the next-event clock of a terminal observation. -/
theorem healthy_cut_prefix_time {i : Nat} (hi : i ≤ Q.run.2.events.length) :
    ∀ q < cutMap S Q.run.2 Q.hn i, Q.trace.time q ≤ Q.run.2.horizon := by
  intro q hq
  apply simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid
  have hlen : q < (allCuts S Q.run.2 Q.hn).length := by
    rw [length_allCuts]
    exact hq.trans_le (cutMap_mono S Q.run.2 Q.hn hi)
  rw [simTrace_label, List.getElem?_eq_getElem hlen]
  simp

/-- OPEN M5 mixed-source pairwise compatibility at the two actual cuts. -/
theorem healthy_current_sources_compatible (D : HealthyRepairSchedule S A V Q)
    {u v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hbi : ∀ q < cutMap S Q.run.2 Q.hn i, Q.trace.time q ≤ Q.run.2.horizon)
    (hbj : ∀ q < cutMap S Q.run.2 Q.hn j, Q.trace.time q ≤ Q.run.2.horizon)
    (hu : u ∈ Q.run.2.honest) (hv : v ∈ Q.run.2.honest)
    {R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey u)
      (cutMap S Q.run.2 Q.hn i) R)
    (hR' : HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn j) R') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  sorry

/-- OPEN actual candidate comparison on the original directed cut interval. -/
theorem healthy_current_record_candidates (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∀ q, cutMap S Q.run.2 Q.hn i ≤ q → q < cutMap S Q.run.2 Q.hn j → ∀ B s CV,
      SA.ResultAt Q.trace.projAC (Q.run.2.ownKey v) q s B CV ∨
        SA.OptimisticLockAt Q.trace.projAC (Q.run.2.ownKey v) q s B CV →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
            (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) B := by
  sorry

/-- OPEN next-floor comparison, independently of candidate comparison. -/
theorem healthy_current_record_next_floor (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∀ q, cutMap S Q.run.2 Q.hn i ≤ q → q < cutMap S Q.run.2 Q.hn j →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        (Q.trace.state (Q.run.2.ownKey v) (q + 1)).fg.F
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
            (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  sorry

/-- Candidate and next-floor inputs produce the original directed cut interval. -/
theorem healthy_current_record_interval (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    EffectiveRecordInterval Q.trace (honestKeys S Q.run.2) (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (cutMap S Q.run.2 Q.hn j)
      ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  exact effectiveRecordInterval_of_candidates_before D.reset (honest_ownKey (S := S) hv.1)
    (healthy_current_record_candidates S A V Q h0 hb hp W states D O hrepair hi hj hij hv)
    (healthy_current_record_next_floor S A V Q h0 hb hp W states D O hrepair hi hj hij hv)

end EndpointProducers

/-- OPEN comparability of actual stored-clock tips. Old-row realization,
label replacement and head/lock/frame comparability remain obligations. InCuts
includes cuts at heal before endCut heal; the state facts do not cover these. -/
theorem healthy_cut_tips_comparable (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    let C := fun v i => Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (stateAt S Q.run.2 Q.hn v i).now
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C u i) (C v j) ∨
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C v j) (C u i) := by
  obtain ⟨D⟩ := healthy_repair_schedule S A V Q h0 hb hp W states
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  have hri := healthy_current_record_read S A V Q h0 hb hp W states D O hr hi hu
  have hrj := healthy_current_record_read S A V Q h0 hb hp W states D O hr hj hv
  dsimp only
  rw [hri, hrj]
  exact healthy_current_sources_compatible S A V Q h0 hb hp W states D hi hj
    (healthy_cut_prefix_time S A V Q hi.1) (healthy_cut_prefix_time S A V Q hj.1) hu.1 hv.1
    (healthy_current_record_sources S A V Q h0 hb hp W states D O hr hi hu)
    (healthy_current_record_sources S A V Q h0 hb hp W states D O hr hj hv)

/-- OPEN temporal ancestry, not merely common-chain membership. The stored
clock and equality-time boundary are retained exactly as in the engine reads. -/
theorem healthy_cut_tips_ancestor (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  obtain ⟨D⟩ := healthy_repair_schedule S A V Q h0 hb hp W states
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  rw [healthy_current_record_read S A V Q h0 hb hp W states D O hr hi hvi,
    healthy_current_record_read S A V Q h0 hb hp W states D O hr hj hvj]
  exact effective_record_of_interval D.reset.run D.reset.noColl
    (honest_ownKey (S := S) hvi.1) (cutMap_mono S Q.run.2 Q.hn hij)
    (healthy_current_record_interval S A V Q h0 hb hp W states D O hr hi hj hij hvi) .refl

/-- Arbitrary-cut engine agreement reduces to the named open tip comparability
obligation. No equality between stored clock and cut time is assumed. -/
theorem healthy_cut_agreement (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Consensus.Compatible ((chainTrace Q.run.2).read .confirmed u i)
      ((chainTrace Q.run.2).read .confirmed v j) := by
  have hs := simTrace_simulates S Q.run.2 Q.hn Q.valid
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  rcases healthy_cut_tips_comparable S A V Q h0 hb hp W states u v i j hi hj hu hv with h | h
  · exact Or.inl (confirmed_prefix_of_anc hs hnc hu.1 hv.1 hi.1 hj.1 h)
  · exact Or.inr (confirmed_prefix_of_anc hs hnc hv.1 hu.1 hj.1 hi.1 h)

/-- Arbitrary-cut monotonicity reduces to directed tip ancestry. Agreement
alone is not used to infer temporal movement. -/
theorem healthy_cut_monotone (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    (chainTrace Q.run.2).read .confirmed v i <+:
      (chainTrace Q.run.2).read .confirmed v j := by
  exact confirmed_prefix_of_anc (simTrace_simulates S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) hvi.1 hvj.1 hi.1 hj.1
    (healthy_cut_tips_ancestor S A V Q h0 hb hp W states v i j hi hij hj hvi hvj)

/-- Assembly with finite preparation; only the two named cut adapters remain
for projection. Their OPEN types retain the exact equality-time boundary case. -/
theorem healthy_ready_safety (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    (chainTrace Q.run.2).ReadySafe ((Sys (family S) V).cDur (K S A) Q.run)
      .confirmed Q.heal := by
  obtain ⟨W, inv, ⟨D⟩⟩ := healthy_old_inventory_initialize S A V Q h0 hb hp
  have base := healthy_prepare S A V Q h0 hb hp W inv D
  have states := healthy_preserve S A V Q h0 hb W base
  exact ⟨healthy_cut_agreement S A V Q h0 hb hp W states,
    healthy_cut_monotone S A V Q h0 hb hp W states⟩

end Consensus.Goldilocks.Refinement
end
