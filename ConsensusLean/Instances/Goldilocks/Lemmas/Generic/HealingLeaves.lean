module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLagCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Generic healing leaves

The healing leaves proved once over any node AC: a node run under growing faults
(`Growing.LocalRun`) from any starts `ini`. The Goldilocks originals are instances.

Held attestations: an attestation on a block held at an observation honest at `t`, with a signer
honest at `t`, was signed before the cut (`held_att_signed_at_from`); two such attestations, with
a signer honest at a time after both observations, are not slashable (`held_atts_safe_at_from`).

Leaf 2, lower bound (`HZ_le_hmax_at_from`): after its relay obligation is paid, a receiver honest
at its cut has at least the snapshot height `HZ`. Relay and catch-up carry a held block of
height at least the receiver's `h_max` to the receiver (`held_of_relay_le_at_from`), and the
block's state is the same at both holders (`σ_eq_honest_at_from`).

Leaf 3 (`exists_frameWindow_seq_of_service_at_from`): per-cut height range and relay calls give
a frame window of the requested length, by the sequential pigeonhole over the cuts of nodes
honest at them with the merged-key lag between independently honest observations
(`frameKey'_lag_obs_from`).

Proposal membership and leaf 5, the round crossing (`proposal_mem_at_from`,
`round_cross_at_from`): an honest proposal is held by its proposer after its cut, and delivered
historical rows (`rows_delivered_service_at_from`, under the signed-row service clause) or higher
reports raise the proposal one height above the crossed block.
-/

namespace Consensus.Goldilocks.Generic

/-- An attestation on a block held at an observation honest at `t`, with a signer honest at `t`,
was signed before the cut, for any node run under growing faults from any starts `ini`. -/
theorem held_att_signed_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (h.upTo ht) hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := h.att_unforgeable y k a
      (h.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (h.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **Held attestations at independently honest observations are not slashable**, for any node
run under growing faults from any starts `ini`. Attestations on blocks held by `y` (observed while
honest at `u`) and by `x` (observed while honest at `t`), with a signer honest at a time `d` after
both observations, were signed by that signer's client run on the prefix up to `d`, which client
safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y x : Fin P.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at_from h hu hytime hy ha (h.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at_from h ht hxtime hx hb
    (hab.1 ▸ h.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  obtain ⟨inputs, hin, hs⟩ :=
    Store.signed_run_of_exec (Compose.fg_exec (h.upTo (hu.trans hud))) hav (max k l + 1)
  exact FG.client_safety P.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

/-! ## Leaf 2, lower bound -/

section HZLowerBound

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ CatchRun)

/-- Reachability at a held-state observation, not necessarily the time of cut `i`. -/
theorem fg_reachable_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.state y i).fg.Reachable A.genesisPayload := by
  simpa only [Trace.upTo_state tr y hle] using Compose.fg_reachable (h.upTo ht) hy i

/-- Ancestry in a tree observed while honest lies in the historical honest universe. -/
theorem honest_anc_of_store_anc_at_from {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (h : (tr.state y k).fg.Anc B C) :
    Anc (tr.HonestBlocksAt H) B C :=
  h.mono fun _ hB => ⟨y, k, t, ht, hle, hy, hB⟩

/-- A held block's replay state is identical at two independently honest observations. -/
theorem σ_eq_honest_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin P.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : A.Blk} (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Healing.Store.σ_eq_of_mem (fg_reachable_at_from h ht hle hy) (fg_reachable_at_from h hu hle' hz)
    (Compose.Growing.honest_blocks_coherent_local h hnc).1
    (fun _ hX => ⟨y, i, t, ht, hle, hy, hX⟩)
    (fun _ hX => ⟨z, j, u, hu, hle', hz, hX⟩) hBy hBz

/-- Strict-height finalized ancestry for two independently honest held-state observations. -/
theorem F_anc_of_hmax_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin P.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hle : (tr.state y m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B :=
  honest_anc_of_store_anc_at_from ht hxtime hx <| Store.F_anc_of_hmax_le_of_safe
    (fg_reachable_at_from h hu hytime hy) (fg_reachable_at_from h ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩)
    (fun _ hX => ⟨x, i, t, ht, hxtime, hx, hX⟩) hf
    (held_atts_safe_at_from h hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hB hle

/-- Relay and catch-up carry a held block to a receiver whose height has not passed it. -/
theorem held_of_relay_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree := by
  have hm0 := h.time_nonneg m
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hs : ∀ j ≤ m, (tr.upTo (tr.time m)).state z j = tr.state z j :=
    fun j hj => Trace.upTo_state tr z (fun k hk => h.time_mono (by omega))
  have hr := h.upTo hm0
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocksAt H) (tr.state z j).fg.F B := by
    intro j hj
    have hheight := Healing.hmax_mono hr hz hj
    dsimp only at hheight
    rw [hs j hj, hs m le_rfl] at hheight
    apply F_anc_of_hmax_le_at_from h hnc hm0
      (fun k hk => h.time_mono (by omega)) hz hτ0 hτ hx
      (by rwa [max_comm]) hB (hheight.trans hh)
  have hlift : ∀ k, k + 1 ≤ m → tr.AcceptAt z k B → B ∈ (tr.state z m).fg.tree := by
    intro k hkm ha
    have ha' : (tr.upTo (tr.time m)).AcceptAt z k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨h.time_mono (by omega), ha⟩
    have hmem := Healing.accept_mem_from hr hz ha'
    have := Compose.tree_mono hr hz hkm hmem
    rwa [hs m le_rfl] at this
  have hB' : B ∈ ((tr.upTo τ).state x i).fg.tree := by
    rwa [Trace.upTo_state tr x hτ]
  rcases Healing.tree_accepted (h.upTo hτ0) hx hB' with he | ⟨k, hk, ha⟩
  · rw [he]
    exact Healing.Store.genesis_mem (fg_reachable_at_from h hm0 hm hz)
  have ha := ((RunTrace.upTo_acceptAt tr).mp ha).2
  have hxk := h.antitone (hτ k hk) hx
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' := (tr.deadline_mono z j (max_le_max (hτ k hk) le_rfl) P.Δ).trans hdl
    obtain ⟨k', hk'j, ha', -⟩ := hsvc.relay x k B hxk ha hg z j
      (h.antitone (h.time_mono hjm.le) hz) hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha'
  · obtain ⟨j₀, hfirst, hj₀⟩ := Healing.exists_firstCutFrom_le hcm
    obtain ⟨k', hk', ha'⟩ := hcatch x k B hxk ha
      (lt_of_lt_of_le (not_le.mp hg) (le_max_left _ _)) z j₀
      (h.antitone hcm hz) hfirst (hF j₀ hj₀)
    exact hlift k' (by omega) ha'

/-- The snapshot height is attained by a member of its own honest cohort. -/
theorem exists_HZ_holder_at_from {g : Time} (hH : (H (cutZ P g)).Nonempty) {j : Nat}
    (hj : FirstCutAfter tr j (cutZ P g)) :
    ∃ x ∈ H (cutZ P g), (tr.state x j).fg.hmax = HZ tr H g := by
  obtain ⟨y, hy⟩ := hH
  have hne : {h | ∃ y ∈ H (cutZ P g), ∃ j,
      FirstCutAfter tr j (cutZ P g) ∧ (tr.state y j).fg.hmax = h}.Nonempty :=
    ⟨_, y, hy, j, hj, rfl⟩
  obtain ⟨x, hx, j', hj', he⟩ := Nat.sSup_mem hne
    (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset (by
      rintro _ ⟨z, -, j', hj', rfl⟩
      obtain rfl := hj'.unique hj
      exact ⟨z, rfl⟩)).bddAbove)
  obtain rfl := hj'.unique hj
  exact ⟨x, hx, he⟩

/-- **Leaf 2, lower bound.** After its relay obligation is paid, a receiver honest at its cut
has at least the snapshot height, for any node run under growing faults from any starts `ini`. -/
theorem HZ_le_hmax_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ P g)).Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ P g))
    {z : Fin P.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ P g) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : HZ tr H g ≤ (tr.state z m).fg.hmax := by
  obtain ⟨j, hj⟩ := hsnap
  obtain ⟨x, hx, hxe⟩ := exists_HZ_holder_at_from hH hj
  have hc0 : 0 ≤ cutZ P g := by
    have := P.slotTime_strictMono.monotone (Nat.zero_le (P.slotOf (gbar g) + 3))
    rwa [P.slotTime_zero] at this
  have hRx := fg_reachable_at_from h hc0 hj.1 hx
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hRz := fg_reachable_at_from h (h.time_nonneg m) hm hz
  obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ := Store.cache_invariants _ _ _ _ hRx
  by_cases hle : HZ tr H g ≤ (tr.state z m).fg.hmax
  · exact hle
  have hBz := held_of_relay_le_at_from h hnc hsvc hcatch hc0 hx hz hf hB
    (by omega) hj.1 hcall hcm
  have he := σ_eq_honest_at_from h hnc hc0 hj.1 hx (h.time_nonneg m) hm hz hB hBz
  have hh := (Store.cache_invariants _ _ _ _ hRz).2.2.2.2.1 B hBz
  rw [← he] at hh
  omega

end HZLowerBound

/-! ## Store ancestry below honest blocks -/

section StoreAnc

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Historical ancestry descends into the reader's actual held tree, for any node run under
growing faults from any starts `ini`. -/
theorem store_anc_of_honest_anc_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (hBC : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc B C := by
  have hs := Trace.upTo_state tr y hle
  have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
  have hanc := RunTrace.anc_upTo_of_right h hnc ht hc hBC
  rw [← hs]
  exact Healing.store_anc_of_honest_anc_from (h.upTo ht)
    (Compose.NoCollRun.upTo hnc t) hy hanc (by rwa [hs])

end StoreAnc

/-! ## Leaf 3, the frame window -/

section FrameWindowLeaf

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing.Growing (CatchRun)

/-- The merged frame key of the generic statements is the merged frame key of the stores. -/
theorem frameKey'_eq (st : Store P A.Payload) : frameKey' A st = Healing.frameKey' st := by
  rw [Healing.frameKey'_def, Healing.keyMerge_eq, Healing.frameKey_def]
  rfl

/-- `Σ.J` of two stores observed while honest with equal `h_j` agree. -/
private theorem J_eq_of_hj_eq_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin P.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * P.fg.q - P.n)
    (he : (tr.state y m).fg.hj = (tr.state x i).fg.hj) :
    (tr.state y m).fg.J = (tr.state x i).fg.J :=
  Healing.Store.J_eq_of_cache_hj_eq_of_safe (fg_reachable_at_from h hu hytime hy)
    (fg_reachable_at_from h ht hxtime hx) (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩) (fun _ hX => ⟨x, i, t, ht, hxtime, hx, hX⟩) hf
    (held_atts_safe_at_from h hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    he

/-- `h_j < h_max` at a store observed while honest. -/
private theorem hj_lt_hmax_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  Healing.Store.hj_lt_hmax_of_reachable (fg_reachable_at_from h ht hle hy)

/-- **The frame-key lag** with the source `x` honest at its cut `i` and the receiver `z` honest at
its cut `m`, after a call of `z` at or after the relay deadline of `i`. -/
theorem frameKey_lag_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    Healing.frameKey (tr.state x i).fg ≤ Healing.frameKey (tr.state z m).fg := by
  have hi0 := h.time_nonneg i
  have hm0 := h.time_nonneg m
  have hxle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => h.time_mono hk.le
  have hzle : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hfmi : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n := by
    rw [max_eq_right him]; exact hf _ hm0 hmb
  exact Healing.frameKey_le_of_relay (fg_reachable_at_from h hi0 hxle hx)
    (fg_reachable_at_from h hm0 hzle hz)
    (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨x, i, tr.time i, hi0, hxle, hx, hX⟩)
    (fun _ hX => ⟨z, m, tr.time m, hm0, hzle, hz, hX⟩) (hf _ hm0 hmb)
    (held_atts_safe_at_from h hm0 hzle hz hi0 hxle hx le_rfl him)
    (held_atts_safe_at_from h hm0 hzle hz hm0 hzle hz le_rfl le_rfl)
    (fun _ _ hBC hC => store_anc_of_honest_anc_at_from h hnc hi0 hxle hx hBC hC)
    (fun _ _ hBC hC => store_anc_of_honest_anc_at_from h hnc hm0 hzle hz hBC hC)
    (fun _ hB hh => held_of_relay_le_at_from h hnc hsvc hcatch hi0 hx hz hfmi hB hh hxle hcall
      hcm)

/-- **The merged-key lag** between independently honest observations. -/
theorem frameKey'_lag_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    Healing.frameKey' (tr.state x i).fg ≤ Healing.frameKey' (tr.state z m).fg :=
  (Healing.frameKey'_def _).symm ▸ (Healing.frameKey'_def _).symm ▸ Healing.keyMerge_mono
    (frameKey_lag_obs_from h hnc hf hsvc hcatch hx hz him hmb hcall hcm)

/-- A merged key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`. -/
theorem frameWindow_of_frameKey'_eq_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      Healing.frameKey' (tr.state y i).fg = Healing.frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow tr H lo hi floor kindJ J := by
  have hle : ∀ i k, k < i → tr.time k ≤ tr.time i := fun _ _ hk => h.time_mono hk.le
  obtain ⟨floor, kindJ, J, h1, h2, h3⟩ := Healing.frameData_of_frameKey'_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload)
    (fun y i hy => hj_lt_hmax_obs_from h (h.time_nonneg i) (hle i) hy) hK
    (fun y z i m hy hz _ hi _ hm he => J_eq_of_hj_eq_obs_from h hnc (h.time_nonneg i) (hle i) hy
      (h.time_nonneg m) (hle m) hz
      (hf _ ((h.time_nonneg i).trans (le_max_left _ _)) (max_le (hi.trans hhi) (hm.trans hhi)))
      he)
  exact ⟨floor, kindJ, J, ⟨h1, h2, h3⟩⟩

/-- **Leaf 3.** Per-cut height range and relay calls produce a frame window, by the sequential
pigeonhole over the cuts of nodes honest at them with the merged-key lag between independently
honest observations, for any node run under growing faults from any starts `ini`. -/
theorem exists_frameWindow_seq_of_service_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' A (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := Healing.Growing.exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => Healing.frameKey' (tr.state y i).fg)
    (2 * hz) 4 len hlen hlam
    (fun y i hy h1 h2 => by
      have := hrange y i hy h1 h2
      exact Healing.frameKey'_bounds this.1 this.2)
    (fun x z i m hx hz' hi _ him hmT => frameKey'_lag_obs_from h hnc hf hsvc hcatch hx hz'
      ((le_add_of_nonneg_right hlam).trans him) (hmT.le.trans hTb)
      (hcall z i m hz' hi him hmT) (hlo.trans (hi.trans ((le_add_of_nonneg_right hlam).trans him))))
    hT
  -- the window ends before `T`
  have hS : ∀ j, j ≤ 4 → ∑ i ∈ Finset.range (j + 1), (len (2 * hz + i) + lam) ≤
      ∑ i ∈ Finset.range 5, (len (2 * hz + i) + lam) := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun i _ _ => add_nonneg (hlen _) hlam
  have hend : a + len v < T := by
    have := hS (v - 2 * hz) (by omega)
    linarith
  refine ⟨v, hv1, hv2, a, h1, h2,
    fun y i hy hi1 hi2 => by rw [frameKey'_eq]; exact hK y i hy hi1 hi2,
    frameWindow_of_frameKey'_eq_obs_from h hnc hf (hend.le.trans hTb) ?_⟩
  intro y z i m hy hz' hi1 hi2 hm1 hm2
  rw [hK y i hy hi1 hi2, hK z m hz' hm1 hm2]

end FrameWindowLeaf

/-! ## Proposal membership and leaf 5, the round crossing -/

section RoundCross

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing.Growing (NoRestartAfter)

/-- An honestly signed row is processed strictly before a sufficiently late honest proposal,
even if the signer has been compromised by then, under the signed-row service clause
(`Service.signedRow`, `Healing.Growing.ResetService.signedRow`). -/
theorem rows_delivered_service_at_from {g ΔF b v : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hnr : NoRestartAfter tr H (gbar g))
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hv : gbar g ≤ v) {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : A.Blk} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin P.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att P.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) : ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j ≤ kX, ∀ τ : Time,
      tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := fun j hj τ =>
    Compose.deadline_le_of_restarts
      (fun k' hk' hr => hnr p k' (hrun.antitone (hrun.time_mono (hk'.trans hj)) hp) hr) τ ΔF
  have hg : max (tr.time k) g ≤ v := max_le hk ((Healing.le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX,
      tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := by
    intro j hj
    have := hdl0 j hj (max (tr.time k) g)
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hrows y k att hy hsig p kX hp
    ⟨_, hcall⟩ hkb (by linarith [hdl kX le_rfl])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith only [hdl k' le_rfl, hlt, hvx]

/-- A proposal's immediate acceptance is held while its proposer is honest, for a run from starts
`ini` at which the AC meets the requirements, with the genesis root: the middle component of
`Healing.accept_of_proposesAt_from` on the proposer's prefix. -/
theorem proposal_mem_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {p : Fin P.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {B : A.Blk}
    (hB : tr.ProposesAt p k B) : B ∈ (tr.state p (k + 1)).fg.tree := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hB' : (tr.upTo (tr.time k)).ProposesAt p k B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  have hm := (Healing.accept_of_proposesAt_from hr hroot (hnc.upTo _) hp (hq p) hB').2.1
  rwa [Trace.upTo_state tr p (fun q hq => hrun.time_mono (by omega))] at hm

/-- Leaf 5: delivered historical rows cross one height; honesty is read separately at every cut.
For a run from starts `ini` at which the AC meets the requirements, with the genesis root and the
signed-row service clause (`Service.signedRow`). -/
theorem round_cross_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hnr : NoRestartAfter tr H (gbar g))
    {B D X : A.Blk} (hBH : B ∈ tr.HonestBlocksAt H)
    (hBD : Anc (tr.HonestBlocksAt H) B D) (hpar : X.parent = some D.root)
    {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ P.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : B.slot + P.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ B ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ B.root).h ∧
          att.T = ((tr.state w c).fg.σ B.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        B ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ B.root).h < ((tr.state w c).fg.σ R.root).h) :
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  classical
  have hage' : B.slot + P.fg.δt ≤ X.slot := hage
  have hd := hrun.time_nonneg kX
  have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq =>
    hrun.time_mono (by omega)
  have hs := Trace.upTo_state tr p hle
  have hs1 := Trace.upTo_state tr p hle1
  -- Restrict only the proposer's local execution; historical witnesses remain in the full trace.
  have hr := hrun.upTo hd
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  have hcoh := Compose.Growing.honest_blocks_coherent_local hrun hnc
  obtain ⟨Pr, hpar', hPr⟩ :=
    Healing.proposal_parent_held_from hr hroot (hnc.upTo _) hp (hq p) hX'
  rw [hs] at hPr
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt_from hr hroot (hnc.upTo _) hp (hq p) hX'
  rw [hs1] at hXm he
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨p, kX, _, hd, hle, hp, hPr⟩
  have hDH : D ∈ tr.HonestBlocksAt H := by
    rcases Relation.ReflTransGen.cases_tail hBD with rfl | ⟨Z, -, hZ⟩
    · exact hBH
    · exact hZ.2.1
  obtain rfl : D = Pr := hcoh.1 hDH hPrH (Option.some_injective _ (hpar.symm.trans hpar'))
  have hR := fg_reachable_at_from hrun hd hle hp
  have hR1 := fg_reachable_at_from hrun hd hle1 hp
  have hBDs := store_anc_of_honest_anc_at_from hrun hnc hd hle hp hBD hPr
  have hBst : B ∈ (tr.state p kX).fg.tree := by
    by_cases he : B = D
    · exact he ▸ hPr
    · exact (Anc.mem hBDs he).1
  have hBDh := Healing.h_le_of_store_anc hR hBDs
  have hmono : (tr.state p kX).fg.tree ⊆ (tr.state p (kX + 1)).fg.tree := by
    simpa only [hs, hs1] using Compose.tree_mono hr hp (Nat.le_succ kX)
  have hDm := hmono hPr
  have hBm := hmono hBst
  have hσB := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hBst hBm
  have hσD := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hPr hDm
  have hle' := Healing.h_le_of_store_anc hR1 (.single ⟨hDm, hXm, hpar⟩)
  refine ⟨hBm, hXm, ?_⟩
  rw [← hσB]
  rw [← hσD] at hle'
  by_cases hlt : ((tr.state p kX).fg.σ B.root).h < ((tr.state p kX).fg.σ D.root).h
  · omega
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ B.root).h := by omega
  have hDTh := Healing.Th_eq_of_anc hR hBDs hDh
  have hThS : ((tr.state p kX).fg.σ D.root).ThSlot ≤ B.slot := by
    rw [Healing.ThSlot_eq_of_anc hR hBDs hDh]
    exact Healing.ThSlot_le_slot hR hBst
  let S := Finset.univ.filter (· ∈ H (tr.time kX))
  have hScard : P.fg.q ≤ S.card := by
    have hcard : S.card = (H (tr.time kX)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : (H (tr.time kX)).ncard + (H (tr.time kX))ᶜ.ncard = P.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    change (2 * P.n + 2) / 3 ≤ _
    omega
  obtain ⟨hfg, hXt, hDt, hσX, hσD', hplace⟩ :=
    Healing.proposal_rows_placed_from hr (fun y _ => hq y) hroot (hnc.upTo _) hp hX' hpar
      (by rwa [hs])
  have hcross := Healing.cross_step hfg hp hXt hDt hpar S hScard ?_ ?_
  · have h1 := hcross.1
    rw [← hσX, he, ← hσD', hs] at h1
    omega
  · intro y hyS
    have hy : y ∈ H (tr.time kX) := (Finset.mem_filter.1 hyS).2
    rcases hrow y hy with ⟨w, c, hw, hBw, k, att, hyk, hsig, hk, hah, haT⟩ |
      ⟨R, hRD, w, c, hw, hBw, hRw, hhR⟩
    · have hσ := σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
        (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst
      rw [hσ] at hah haT
      have hproc := rows_delivered_service_at_from hrows hnr hrun hv hp hX hvx hkb hyk hsig hk
      have hval := Healing.signAt_val (hrun.upTo (hrun.time_nonneg k)) hyk
        ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hsig⟩)
      rw [← hσD', hs]
      refine ⟨att, hval, hah.trans hDh.symm, haT.trans hDTh.symm, ?_⟩
      exact hplace att (by
        obtain ⟨j, hj, hproc⟩ := hproc
        exact ⟨j, hj, (RunTrace.upTo_processAttAt _).mpr ⟨hrun.time_mono hj.le, hproc⟩⟩)
        (by rw [hs]; exact hah.trans hDh.symm)
        (by rw [hs]; exact haT.trans hDTh.symm)
    · exfalso
      have hRDs := store_anc_of_honest_anc_at_from hrun hnc hd hle hp hRD hPr
      have hRst : R ∈ (tr.state p kX).fg.tree := by
        by_cases he : R = D
        · exact he ▸ hPr
        · exact (Anc.mem hRDs he).1
      have hRDh := Healing.h_le_of_store_anc hR hRDs
      rw [σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst,
        σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hRw hRst] at hhR
      omega
  · rw [← hσD', hs]
    omega

end RoundCross

end Consensus.Goldilocks.Generic
