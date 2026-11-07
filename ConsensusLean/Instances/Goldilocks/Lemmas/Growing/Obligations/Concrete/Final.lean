module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing obligations: the final branch of healthy liveness

The growing-fault form of the static final route (`Obligations/CarrierProcessed` and
`Obligations/Concrete`), without a constant-fault premise. Honesty is read at each event's own
time: a proposer at its acceptance, a reader at its read time.

* `held_forward_blockCall_lt_at`: holdings of a wrapper of a signer honest at its stamp give a
  block call strictly before the deadline;
* `publication_held_ready_tail_at`: one protocol-delay publication tail gives holdings strictly
  before a ready read. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- Holdings of a decoded wrapper of a signer honest at its stamp, strictly before `D`, give a
block call strictly before `D`. The form of `held_forward_blockCall_before_at` without an
observation cut. -/
theorem held_forward_blockCall_lt_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hx : rho.key x ∉ rho.faultyAt t)
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) :
    ∃ k, (simTraceAt S rho hn).BlockCallAt y k B ∧ (simTraceAt S rho hn).time k < D := by
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
  rw [simTraceAt_eq]
  rcases hsource with hs | hr
  · obtain ⟨i, hi, ho⟩ := hs
    have hxy := released_forward_signer S rho hn hi ho hdecode
    rw [hxy] at hdecode
    have hstamp : t = u := released_forward_stamp S rho hn hv hi ho hdecode
    have hacc : ∃ k < cutMap S rho hn (i + 1),
        (simTrace S rho hn).AcceptAt (rho.ownKey (rho.key y)) k B ∧
        (simTrace S rho hn).time k = t := by
      rcases hi with he | ⟨receipt, he⟩
      · exact tick_released_forward_acceptance S rho hn hv he ho hdecode
      · exact delivery_released_forward_acceptance S rho hn hv he ho hdecode
    obtain ⟨k, _, ha, ht⟩ := hacc
    exact ⟨k, ⟨true, hkey ▸ ha⟩, ht ▸ hstamp ▸ huD⟩
  · obtain ⟨i, hi⟩ := hr
    have htu := received_forward_stamp_le_of_stamp_at S rho hn hv hi (.refl o) hx hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    exact ⟨k, hkey ▸ hc, ht ▸ huD⟩

/-- **One protocol-delay publication tail gives holdings strictly before a ready read.** The
origin is honest at its publication event, the reader is ready at the read time `t`; the holding
time is strictly before `t`, so the reader is honest then. -/
theorem publication_held_ready_tail_at (hn : 1 ≤ Fintype.card V) {g : Time}
    (hnet : rho.log.PSync rho.point g)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r)
    (hx : rho.key r.origin ∉ rho.faultyAt ((publisherExecution S rho).eventTime r.event))
    (hrow : ¬ rho.log.fgAtt r.object)
    {y : Fin (Fintype.card V)} {t c : Time}
    (hy : Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((publisherExecution S rho).eventTime r.event) g) 0 +
      (S.params (Model.pubOf E) hn).Δ ≤ t)
    (hc : (S.params (Model.pubOf E) hn).Δ ≤ c + 1) :
    ∃ d, rho.log.Held rho.point (rho.key y) r.object d ∧ d < t := by
  let a := max (max (max ((publisherExecution S rho).eventTime r.event) g) 0) (t - c - 1)
  have hga : max a g = a := max_eq_left (by dsimp [a, Time]; omega)
  have hlt : a + E.ΔAC - 1 < t := by
    change max (max ((publisherExecution S rho).eventTime r.event) g) 0 + E.ΔAC ≤ t
      at hbudget
    change E.ΔAC ≤ c + 1 at hc
    dsimp [a, Time] at *; omega
  have hw : rho.point.AwakeOnClosed (rho.key y) a (a + E.ΔAC - 1) := by
    intro u hau hud
    have h := hy.2 u (by dsimp [a, Time] at *; omega) (hud.trans hlt.le)
    exact ((awakeAt_iff S rho hn y u).mp ((simTraceAt_awake_iff S rho hn y u).mp h)).1
  have hyd : rho.key y ∉ rho.faultyAt (max a g + E.ΔAC - 1) := by
    rw [hga]
    exact not_faulty_of_mem_honestKeysAt S rho hy.1 hlt.le (hlt.le.trans ht)
  have hh := (publication_held_psync_at S rho hn hnet r hr hx hrow hyd
    (show (publisherExecution S rho).eventTime r.event ≤ a by dsimp [a, Time]; omega)
    (by rw [hga]; exact hlt.le.trans ht) (by rw [hga]; exact hw)).1
  rw [hga] at hh
  exact ⟨a + E.ΔAC - 1, hh, hlt⟩

end Engine

end Consensus.Goldilocks.Obligations.Growing

end
