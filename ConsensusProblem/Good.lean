module
public import ConsensusProblem.Regimes
public import Mathlib.Tactic

@[expose] public section

/-! # The definition of a good protocol (L0)

`Good S X K`: system `S`, with progress requirements read by `X`, meets the
contract `K` (numbers only). Three parts:

* `Behaviour`: a fixed table of properties, each under a fixed regime
  (`Regimes.lean`) over the environment point and the communication log:
  - always: non-framing, nesting `final ⪯ stable ⪯ available`, the final
    output never rolls back;
  - final: local accountability for fraction `α` in every environment, and
    transaction liveness when healthy from a GST (with progress);
  - available and stable: ready-reader safety and transaction liveness when
    sleepy, and from the heal point when healthy from a GST ("stay in
    recovery"; safety needs progress only up to the heal point);
  - stable: outage resilience (what was stable at `T` stays in the available
    ledger of eligible readers during and after the window).
* `Adequate`: the acceptance interface that rules out a vacuous system: every
  well-formed environment point with admissible external data has, for every
  GST, a valid excuse-free run with that point whose log is eager from the GST
  (synchronous, asynchronous before the GST, or silent), carrying the progress
  that holds for the point and data; valid runs are closed under prefixes.
* `Realizable` (for at least five validators): every regime of the table, at
  every `Δ`, every GST and arbitrarily late outages, is met by a clean witness
  (valid, no excuse, a faulty and an honest validator) with active claims.

What L0 cannot check, and L1 proves once for the model: the log is the
engine's real communication (`Model.sysOf_log_faithful`), and the external data
are fixed before execution (`Model.sysExternal`: the PKI and the selection).

Claims hold on valid runs, unless the run's excuse holds (an observed hash
collision in the model): `System.Holds`. There are no other escapes. -/

namespace Consensus

namespace System

variable {V : Type}

/-- On valid runs satisfying `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r

/-- On valid runs, `P` holds. -/
def HoldsAlways (S : System V) (P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → P r

/-- A weaker premise: a claim under `A` holds under any `B` implying `A`. -/
theorem Holds.mono_premise {S : System V} {A B P : S.Run → Prop} (h : S.Holds A P)
    (hAB : ∀ r, B r → A r) : S.Holds B P :=
  fun r hv hb => h r hv (hAB r hb)

variable [Fintype V] [DecidableEq V]

/-- Accountable safety, non-framing and faults below the accountable fraction give
agreement of `g`. -/
theorem agree_of_accountable (S : System V) (hL : S.Laws) (r : S.Run) {g : S.schema.Id}
    {t₀ : Time} {α : ℚ} (hacc : S.AccountablySafe r α g t₀) (hnf : S.NonFraming r)
    (hb : (S.trace r).point.FaultsBelow α) : (S.trace r).Agree g t₀ := by
  classical
  intro u hu v hv i j hi hj
  rcases hacc u hu v hv i j hi hj with hc | hcard
  · exact hc
  · exfalso
    have hsub : S.convicted r (S.view r u i ∪ S.view r v j) ⊆ (S.trace r).point.faulty := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold convicted Consensus.convicted at hx; simpa using hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxh => hnf x hxh ?_⟩
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, hu, hL.view_mono r u i _ hi.1 ho⟩
      · exact ⟨v, hv, hL.view_mono r v j _ hj.1 ho⟩
    change (Fintype.card V : ℚ) * α ≤
      (S.convicted r (S.view r u i ∪ S.view r v j)).card at hcard
    have hc : ((S.convicted r (S.view r u i ∪ S.view r v j)).card : ℚ) ≤
        (S.trace r).point.faulty.card := by exact_mod_cast Finset.card_le_card hsub
    unfold EnvPoint.FaultsBelow at hb
    linarith

end System

/-- The output resilience is measured against: the available output if
provided, else the same output. -/
def resilienceTarget (O : OutputSchema) (g : O.Id) : O.Id := (O.output .available).getD g

/-- Schema package: a final output is provided. -/
def OutputSchema.BFTCore (O : OutputSchema) : Prop := (O.output .final).isSome

/-- Schema package: an available output and no final output. -/
def OutputSchema.DACore (O : OutputSchema) : Prop :=
  (O.output .available).isSome ∧ O.output .final = none

/-- The schema serves a ledger: it is a `BFTCore` (a final output, possibly
with others) or a `DACore` (an available output without a final one). A schema
that provides neither (no output at all, or only a stable one) is not a
consensus service; `Behaviour` requires this. -/
def OutputSchema.Serves (O : OutputSchema) : Prop := O.BFTCore ∨ O.DACore

/-- External run data and its admissibility: what a run fixes before execution
besides its environment point (in the model: the PKI and the selection). -/
structure External {V : Type} (S : System V) where
  /-- The external data of runs in environment `E`. -/
  Ext : Env V → Type
  /-- The external data of a run. -/
  ext : (r : S.Run) → Ext (S.trace r).point.env
  /-- Admissible external data (in the model: the protocol's selection spec). -/
  Admits : (E : Env V) → Ext E → Prop

/-- Progress requirements (leader-based progress), read **only** from the
environment point and the external data (by typing). `holds π c start stop p x`:
requirement `π` with catch-up `c` holds on the window `[start, stop]`. A smaller
window or a smaller horizon is weaker. -/
structure Progress {V : Type} (S : System V) (Prog : Type) extends External S where
  holds : Prog → Time → Time → Time → (p : EnvPoint V) → Ext p.env → Prop
  mono : ∀ {π : Prog} {c s s' e e' : Time} {p : EnvPoint V} {x : Ext p.env},
    s ≤ s' → e' ≤ e → holds π c s e p x → holds π c s' e' p x
  shrink : ∀ {π : Prog} {c s e : Time} {p : EnvPoint V} {x : Ext p.env} {b : Time},
    b ≤ p.horizon → holds π c s e p x → holds π c s e { p with horizon := b } x

/-- What a protocol advertises: numbers (`Params`) over a nonempty index type,
and a progress requirement per capability and index. -/
structure Contract (O : OutputSchema) (Prog : Type) where
  Idx : Type
  idx_nonempty : Nonempty Idx
  params : Params Idx
  progress : Capability → Idx → Prog

namespace System

variable {V : Type} (S : System V) {Prog : Type}

/-- The environment point of a run. -/
abbrev pt (r : S.Run) : EnvPoint V := (S.trace r).point

/-- The catch-up duration of run `r`. -/
def cDur (K : Contract S.schema Prog) (r : S.Run) : Time := K.params.cDur (S.pt r).env.Δ

/-- The heal point of `cap` at `i` after GST `g` in run `r`. -/
def heal (K : Contract S.schema Prog) (cap : Capability) (i : K.Idx) (g : Time)
    (r : S.Run) : Time :=
  K.params.healPoint (S.pt r).env.Δ cap i g

/-- The start of progress windows after GST `g` in run `r`. -/
def ready (K : Contract S.schema Prog) (g : Time) (r : S.Run) : Time :=
  readyFrom (S.cDur K r) g

/-- The latency of `cap` at `i` in run `r`. -/
def lat (K : Contract S.schema Prog) (cap : Capability) (i : K.Idx) (r : S.Run) : Time :=
  K.params.latDur (S.pt r).env.Δ cap i

/-- The progress requirement of `cap` at `i` holds on `[start, stop]` in run `r`. -/
def prog (X : Progress S Prog) (K : Contract S.schema Prog) (cap : Capability) (i : K.Idx)
    (start stop : Time) (r : S.Run) : Prop :=
  X.holds (K.progress cap i) (S.cDur K r) start stop (S.pt r) (X.ext r)

variable [Fintype V] [DecidableEq V]

/-- Run `r` is in the sleepy regime. -/
def Sleepy (K : Contract S.schema Prog) (r : S.Run) : Prop :=
  Regime.Sleepy K.params (S.pt r) (S.log r)

/-- Run `r` is in the healthy regime from GST `g`. -/
def Healthy (K : Contract S.schema Prog) (g : Time) (r : S.Run) : Prop :=
  Regime.Healthy K.params (S.pt r) (S.log r) g

/-- Run `r` is in the outage regime `(T, [b₀, b₁))`. -/
def Outage (K : Contract S.schema Prog) (T b₀ b₁ : Time) (r : S.Run) : Prop :=
  Regime.Outage K.params (S.pt r) (S.log r) T b₀ b₁

/-- A clean witness: valid, no excuse, a faulty and an honest validator. -/
def Witness (r : S.Run) : Prop :=
  S.Valid r ∧ ¬ S.Excuse r ∧ (S.pt r).faulty.Nonempty ∧ (S.pt r).honest.Nonempty

end System

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- The claims of the final output `g`: local accountability for fraction `α`
in every environment (no premise), and transaction liveness from the heal
point when healthy from a GST with progress from `readyFrom` to the horizon. -/
structure FinalClaims (S : System V) (X : Progress S Prog) (K : Contract S.schema Prog)
    (g : S.schema.Id) : Prop where
  accountable : S.Holds (fun _ => True) (fun r => S.AccountablySafe r K.params.α g 0)
  live : ∀ i gst, S.Holds
    (fun r => S.Healthy K gst r ∧ S.prog X K .final i (S.ready K gst r) (S.pt r).horizon r)
    (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K .final i gst r) (S.lat K .final i r))

/-- The claims of an available or stable output `g` (capability `cap`):
ready-reader safety and liveness when sleepy (from `0`), and when healthy from a
GST (from the heal point; safety needs progress only on `[readyFrom, heal]`). -/
structure DAClaims (S : System V) (X : Progress S Prog) (K : Contract S.schema Prog)
    (cap : Capability) (g : S.schema.Id) : Prop where
  sleepySafe : S.Holds (S.Sleepy K) (fun r => (S.trace r).ReadySafe (S.cDur K r) g 0)
  sleepyLive : ∀ i, S.Holds (fun r => S.Sleepy K r ∧ S.prog X K cap i 0 (S.pt r).horizon r)
    (fun r => (S.trace r).TxLive (S.cDur K r) g 0 (S.lat K cap i r))
  healedSafe : ∀ i gst, S.Holds
    (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.heal K cap i gst r) r)
    (fun r => (S.trace r).ReadySafe (S.cDur K r) g (S.heal K cap i gst r))
  healedLive : ∀ i gst, S.Holds
    (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
    (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r))

/-- **Behaviour**: the fixed property table. -/
structure Behaviour (S : System V) (X : Progress S Prog) (K : Contract S.schema Prog) :
    Prop where
  laws : S.Laws
  admissible : K.params.Admissible
  serves : S.schema.Serves
  /-- Honest validators are never convicted by honest evidence. -/
  nonFraming : S.HoldsAlways S.NonFraming
  /-- Lower-rank outputs are prefixes of higher-rank ones, unconditionally. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → S.schema.output c₁ = some g₁ →
    S.schema.output c₂ = some g₂ → S.HoldsAlways (fun r => (S.trace r).Nested g₁ g₂)
  /-- The final output never rolls back, unconditionally. -/
  finalMonotone : ∀ g, S.schema.output .final = some g →
    S.HoldsAlways (fun r => (S.trace r).Monotone g 0)
  final : ∀ g, S.schema.output .final = some g → FinalClaims S X K g
  da : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    DAClaims S X K cap g
  /-- Outage resilience of the stable output, into the resilience target:
  what a node ready at `T` reads as stable is kept by eligible readers. -/
  persists : ∀ g, S.schema.output .stable = some g → ∀ T b₀ b₁,
    S.Holds (S.Outage K T b₀ b₁) (fun r => (S.trace r).ProtectedThrough (S.cDur K r) g
      (resilienceTarget S.schema g) T b₀ b₁)

/-- **Adequacy**: the L0 acceptance interface, which rules out a vacuous
system. -/
structure System.Adequate (S : System V) (X : Progress S Prog) : Prop where
  /-- Every environment has admissible external data (otherwise coverage would
  be vacuous). -/
  admits : ∀ E : Env V, ∃ e : X.Ext E, X.Admits E e
  /-- Coverage: every well-formed point, admissible external data and GST `g`
  has a valid excuse-free run with that point, whose log is eager from `g`
  (`g ≤ 0`: synchronous; `g > horizon`: silent), and on which every progress
  requirement that holds at the point and data holds. The run's own external
  data `X.ext r` need not be `e` (L0 transports the progress, not the data);
  `Model.sysOf_adequate` keeps the given PKI and selection. -/
  covers : ∀ p : EnvPoint V, p.WellFormed → ∀ e : X.Ext p.env, X.Admits p.env e → ∀ g : Time,
    ∃ r, S.Valid r ∧ ¬ S.Excuse r ∧ S.pt r = p ∧ (S.log r).EagerFrom (S.pt r) g ∧
      ∀ π c s t, X.holds π c s t p e → X.holds π c s t (S.pt r) (X.ext r)
  /-- Prefix closure: the prefix of a valid run up to any `b ∈ [0, horizon]` is
  a valid run with the same reads, views and log up to `b`, no new excuse, and
  the same progress on windows ending by `b`. -/
  prefixClosed : ∀ r, S.Valid r → ∀ b : Time, 0 ≤ b → b ≤ (S.pt r).horizon → ∃ r', S.Valid r' ∧
    (S.trace r').PrefixOf (S.trace r) b ∧
    (∀ v i, i ≤ (S.trace r').cuts → S.view r' v i = S.view r v i) ∧
    (S.log r').AgreesUpTo (S.log r) b ∧ (S.Excuse r' → S.Excuse r) ∧
    ∀ π c s t, t ≤ b → X.holds π c s t (S.pt r) (X.ext r) → X.holds π c s t (S.pt r') (X.ext r')

/-- Safety is active after `t₀`: two distinct readers ready at one time after
`t₀`, one of them ready again at a later time within the horizon. -/
def SafeActive (c t₀ : Time) (p : EnvPoint V) : Prop :=
  ∃ u w t t', u ≠ w ∧ t₀ < t ∧ t < t' ∧ t' ≤ p.horizon ∧
    p.Ready c u t ∧ p.Ready c w t ∧ p.Ready c u t'

/-- The outage is active: armed at `T ≥ 0` before the window, which lasts at
least `Δ` and ends within the horizon; a node is ready at `T` (a protected
source); an honest node sleeps in the window; an honest node is caught up
before the window and awake through its end (an eligible reader). -/
def OutageActive (c T b₀ b₁ : Time) (p : EnvPoint V) : Prop :=
  0 ≤ T ∧ T < b₀ ∧ b₀ + p.env.Δ ≤ b₁ ∧ b₁ ≤ p.horizon ∧ (∃ u, p.Ready c u T) ∧
    (∃ v ∈ p.honest, ∃ t, b₀ ≤ t ∧ t < b₁ ∧ p.env.awake v t = false) ∧
    ∃ w ∈ p.honest, p.AwakeOnClosed w (max 0 (b₀ - c - 1)) b₁

/-- **Realizability**: every regime is met by a clean witness with active
claims, at every `Δ`, every GST (with a log silent before it), and arbitrarily
late outages. -/
structure Realizable (S : System V) (X : Progress S Prog) (K : Contract S.schema Prog) :
    Prop where
  sleepy : ∀ cap i (Δ : Time), 0 < Δ → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧ S.Sleepy K r ∧
    S.prog X K cap i 0 (S.pt r).horizon r ∧
    (S.trace r).TxLiveActive (S.cDur K r) 0 (S.lat K cap i r)
  healthy : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    (S.log r).EagerFrom (S.pt r) g ∧ S.Healthy K g r ∧
    S.prog X K cap i (S.ready K g r) (S.pt r).horizon r ∧
    (S.trace r).TxLiveActive (S.cDur K r) (S.heal K cap i g r) (S.lat K cap i r) ∧
    SafeActive (S.cDur K r) (S.heal K cap i g r) (S.pt r)
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    S.Outage K T b₀ b₁ r ∧ OutageActive (S.cDur K r) T b₀ b₁ (S.pt r) ∧ (k : Time) * Δ ≤ T

/-- **A good protocol.** -/
structure Good (S : System V) (X : Progress S Prog) (K : Contract S.schema Prog) : Prop where
  behaviour : Behaviour S X K
  adequate : S.Adequate X
  realizable : 5 ≤ Fintype.card V → Realizable S X K

namespace Good

variable {S : System V} {X : Progress S Prog} {K : Contract S.schema Prog}

/-- Final agreement in every environment with faults below `α`. -/
theorem final_agree (h : Good S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g)
    (r : S.Run) (hv : S.Valid r) (hb : (S.pt r).FaultsBelow K.params.α) :
    (S.trace r).Agree g 0 ∨ S.Excuse r :=
  ((h.behaviour.final g hg).accountable r hv trivial).imp
    (fun ha => S.agree_of_accountable h.behaviour.laws r ha (h.behaviour.nonFraming r hv) hb) id

/-- Final safety in the healthy regime: a set of more than `φ·n` honest
validators bounds the faults below `1 − φ ≤ α`. -/
theorem final_safe_healthy (h : Good S X K) {g : S.schema.Id}
    (hg : S.schema.output .final = some g) (r : S.Run) (hv : S.Valid r) {gst : Time}
    (hH : S.Healthy K gst r) : (S.trace r).Safe g 0 ∨ S.Excuse r := by
  have hb : (S.pt r).FaultsBelow K.params.α :=
    hH.2.faultsBelow.mono _ h.behaviour.admissible.α_range.1
  exact (h.final_agree hg r hv hb).imp (fun ha => ⟨ha, h.behaviour.finalMonotone g hg r hv⟩) id

/-- Through an outage, what a node ready at `T` read as stable is compatible
with the final read of every eligible reader (both are prefixes of its
available read). -/
theorem persists_final_compatible (h : Good S X K) {g gf : S.schema.Id}
    (hs : S.schema.output .stable = some g) (hf : S.schema.output .final = some gf)
    (r : S.Run) (hv : S.Valid r) {T b₀ b₁ : Time} (hO : S.Outage K T b₀ b₁ r)
    {v w : V} (hvr : (S.pt r).Ready (S.cDur K r) v T) (hwh : w ∈ (S.pt r).honest) {t : Time}
    (ht : b₀ ≤ t) (hth : t ≤ (S.pt r).horizon)
    (hr : (S.trace r).ResilienceReader (S.cDur K r) b₀ b₁ w t) :
    Compatible ((S.trace r).readAt g v T) ((S.trace r).readAt gf w t) ∨ S.Excuse r := by
  rcases h.behaviour.persists g hs T b₀ b₁ r hv hO with hp | he
  · left
    have h1 := hp v hvr t ht hth w hwh hr
    have hcut : (S.trace r).endCut t ≤ (S.trace r).cuts := Nat.findGreatest_le _
    have h2 : (S.trace r).readAt gf w t <+:
        (S.trace r).readAt (resilienceTarget S.schema g) w t := by
      unfold resilienceTarget
      cases ha : S.schema.output .available with
      | some ga =>
        exact h.behaviour.nested .final .available gf ga (by decide) hf ha r hv w hwh _ hcut
      | none =>
        exact h.behaviour.nested .final .stable gf g (by decide) hf hs r hv w hwh _ hcut
    exact List.prefix_or_prefix_of_prefix h1 h2
  · exact Or.inr he

omit [Fintype V] [DecidableEq V] in
/-- Run quantities that depend only on `Δ` agree on a prefix. -/
private theorem cDur_prefix {r r' : S.Run} {b : Time} (hP : (S.trace r').PrefixOf (S.trace r) b) :
    S.cDur K r' = S.cDur K r := by
  unfold System.cDur; rw [hP.env]

/-- Sleepy safety of the past: a run synchronous and sleepy up to `b` is safe
for ready readers at cuts up to `b`, whatever happens after `b`. -/
theorem sleepySafe_prefix (h : Good S X K) {cap : Capability} {g : S.schema.Id}
    (hcap : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g)
    (r : S.Run) (hv : S.Valid r) {b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ (S.pt r).horizon)
    (hs : (S.log r).SyncUntil (S.pt r) b)
    (hθ : (S.pt r).SleepyOn K.params.θ (S.cDur K r) 0 b) :
    (S.trace r).ReadySafeUpTo (S.cDur K r) g 0 b ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hreg : S.Sleepy K r' := by
    unfold System.Sleepy Regime.Sleepy
    rw [show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨?_, hθ⟩
    have hd : (S.log r).Delivers (S.pt r) (fun a => max a 0 + (S.pt r).env.Δ) b :=
      hs.reindex (f := fun a => max a 0) (fun a => le_max_left a 0) (fun _ => rfl) le_rfl
    exact hd.prefix hL hbh (fun a => le_add_of_le_of_nonneg (le_max_left _ _) (S.pt r).env.Δ_pos.le)
  rcases (h.behaviour.da cap g hcap hg).sleepySafe r' hv' hreg with hr | he
  · rw [hc] at hr; exact Or.inl (hP.readySafeUpTo hr)
  · exact Or.inr (hE he)

/-- Healed safety of the past: a run partially synchronous with GST `gst` and
healthy up to `b`, with progress on `[readyFrom, heal]` and `heal ≤ b`, is
safe for ready readers at cuts in `[heal, b]`, whatever happens after `b`. -/
theorem healedSafe_prefix (h : Good S X K) {cap : Capability} {g : S.schema.Id}
    (hcap : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g)
    (r : S.Run) (hv : S.Valid r) (i : K.Idx) (gst : Time) {b : Time} (hb0 : 0 ≤ b)
    (hbh : b ≤ (S.pt r).horizon)
    (hs : (S.log r).Delivers (S.pt r) (fun a => max a gst + (S.pt r).env.Δ) b)
    (hH : (S.pt r).HealthyOn K.params.φ gst b)
    (hp : S.prog X K cap i (S.ready K gst r) (S.heal K cap i gst r) r)
    (hhb : S.heal K cap i gst r ≤ b) :
    (S.trace r).ReadySafeUpTo (S.cDur K r) g (S.heal K cap i gst r) b ∨ S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, hX⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hheal : S.heal K cap i gst r' = S.heal K cap i gst r := by
    unfold System.heal; rw [hP.env]
  have hready : S.ready K gst r' = S.ready K gst r := by
    unfold System.ready; rw [hc]
  have hreg : S.Healthy K gst r' := by
    unfold System.Healthy Regime.Healthy
    rw [show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨?_, hH⟩
    exact hs.prefix hL hbh (fun a => le_add_of_le_of_nonneg (le_max_left _ _) (S.pt r).env.Δ_pos.le)
  have hpr : S.prog X K cap i (S.ready K gst r') (S.heal K cap i gst r') r' := by
    rw [hready, hheal]
    unfold System.prog at hp ⊢
    rw [hc]
    exact hX _ _ _ _ hhb hp
  rcases (h.behaviour.da cap g hcap hg).healedSafe i gst r' hv' ⟨hreg, hpr⟩ with hr | he
  · rw [hc, hheal] at hr; exact Or.inl (hP.readySafeUpTo hr)
  · exact Or.inr (hE he)

/-- Outage resilience of the past: a run in the outage regime up to `b`
(synchronous for deadlines up to `b₀`, partially synchronous with GST `b₁` up
to `b`, η-sleepy on `[0, b]`, covered at `b₀`) keeps what nodes ready at `T` read
as stable, at reading times in `[b₀, b]`, whatever happens after `b`. -/
theorem outage_prefix (h : Good S X K) {g : S.schema.Id}
    (hg : S.schema.output .stable = some g) (r : S.Run) (hv : S.Valid r)
    {T b₀ b₁ b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ (S.pt r).horizon)
    (hT : OutageTimes K.params (S.pt r).env.Δ T b₀ b₁)
    (hs : (S.log r).SyncUntil (S.pt r) b₀)
    (hps : (S.log r).Delivers (S.pt r) (fun a => max a b₁ + (S.pt r).env.Δ) b)
    (hθ : (S.pt r).EtaSleepyOn K.params.θ (K.params.ηDur (S.pt r).env.Δ) (S.cDur K r) 0 b)
    (hcov : (S.pt r).ReadyOfAll K.params.cover (S.cDur K r) b₀) :
    (S.trace r).ProtectedUpTo (S.cDur K r) g (resilienceTarget S.schema g) T b₀ b₁ b ∨
      S.Excuse r := by
  obtain ⟨r', hv', hP, -, hL, hE, -⟩ := h.adequate.prefixClosed r hv b hb0 hbh
  have hc := cDur_prefix (K := K) hP
  have hΔ := (S.pt r).env.Δ_pos
  have hreg : S.Outage K T b₀ b₁ r' := by
    unfold System.Outage Regime.Outage
    rw [show S.pt r' = { S.pt r with horizon := b } from hP.point]
    refine ⟨hT, ⟨?_, ?_⟩, hθ, hcov⟩
    · exact hs.prefix hL hbh (fun a => le_add_of_nonneg_right hΔ.le)
    · exact hps.prefix hL hbh (fun a => le_add_of_le_of_nonneg (le_max_left _ _) hΔ.le)
  have hTb : T ≤ b₀ := by
    obtain ⟨-, hl, -, -⟩ := hT
    have : (0 : Time) ≤ (K.params.lag : Time) * (S.pt r).env.Δ := by positivity
    linarith
  rcases h.behaviour.persists g hg T b₀ b₁ r' hv' hreg with hr | he
  · rw [hc] at hr; exact Or.inl (hP.protectedUpTo hTb hr)
  · exact Or.inr (hE he)

end Good

end Consensus

end
