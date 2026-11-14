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

end Consensus.Goldilocks.Generic

end
