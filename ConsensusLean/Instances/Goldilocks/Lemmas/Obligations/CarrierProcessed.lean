module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowAssembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowFieldsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the carrier is processed by the deadline (#136)

consensus-lean#136. `carrier_processed_of_honest` proves the premise (H4) `hcarrier` of
`final_window_extract_of` (FinalWindowAssembly.lean) from the `FinalQuery` alone: an honest
proposal `P` of a slot `s` with `query < t_s` and `t_s + Δ ≤ deadline` gets a `BlockCallAt` by
the deadline at every honest node that is ready at the deadline.

The steps: the honest proposer accepts `P` at `t_s` (`accept_of_proposesAt`); the acceptance
publishes an authenticated forwarding wrapper (`forwardAtAcceptance`); one protocol-delay tail
after `max(t_s, GST) = t_s` makes it held at the reader strictly before the deadline
(`publication_held_ready_tail`, catch-up `cDur ≥ Δp − 1`); holdings give a block call before
the deadline (`held_forward_blockCall_lt`, the cut-free form of
`held_forward_blockCall_before`). `final_window_extract_of'` is `final_window_extract_of` with
(H4) discharged; (H1)–(H3) stay explicit. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

section Held

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- Holdings of an honest decoded wrapper strictly before `D` give a block call strictly
before `D`. The form of `held_forward_blockCall_before` without an observation cut. -/
theorem held_forward_blockCall_lt (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho)
    {o : Wire (Fintype.card V)} {t d D : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hheld : rho.log.Held rho.point (rho.key y) o d)
    (hdecode : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B))
    (hd : d < D) :
    ∃ k, (simTrace S rho hn).BlockCallAt y k B ∧ (simTrace S rho hn).time k < D := by
  obtain ⟨u, hud, hsource, _⟩ := hheld
  have huD : u < D := hud.trans_lt hd
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply _
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
    have htu := received_forward_stamp_le S rho hn hv hi (.refl o)
      ((mem_honestKeys_iff S rho x).mp hx) hdecode
    obtain ⟨k, _, hc, ht⟩ := received_forward_blockCall S rho hn hi (.refl o) hdecode htu
    exact ⟨k, hkey ▸ hc, ht ▸ huD⟩

end Held

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **(H4) of `final_window_extract_of`.** Every honest node that is ready at the deadline
processes an honest proposal of a slot `s` by the deadline, when `query < t_s` and
`t_s + Δ ≤ deadline`. -/
theorem carrier_processed_of_honest (Q : FinalQuery S A V) :
    ∀ s P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) s P → Q.query < Q.params.ts s →
      Q.params.ts s + Q.params.Δ ≤ Q.deadline →
      ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j P ∧ Q.trace.time j ≤ Q.deadline := by
  intro s P hP hq hD y hy
  have hmem := hP.1
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hrun hP
  obtain ⟨hacc, -, -⟩ := Healing.accept_of_proposesAt hrun
    (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision) hmem hk
  have htk : Q.trace.time k = Q.params.ts s := by
    rw [hk.2.2, honestProposalRun_slot hP, Q.params.slotTime_eq]
    simp [SA.SAParams.ts]
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S Q.run.2 Q.hn _ _ _).mp
      (forwardAtAcceptance S Q.run.2 Q.hn Q.valid) _ hmem _ _ hacc
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  have hΔ := Q.run.1.ΔAC_pos
  have hg : max Q.gst 0 ≤ Q.query :=
    (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hΔ.le)).trans Q.mature
  have hmax : max (max (Q.params.ts s) Q.gst) 0 = Q.params.ts s := by
    have h1 := le_max_left Q.gst 0
    have h2 := le_max_right Q.gst 0
    have h3 : Q.gst ≤ Q.params.ts s := by linarith
    have h4 : (0 : Time) ≤ Q.params.ts s := by linarith
    rw [max_eq_left h3, max_eq_left h4]
  have hc : Q.params.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := by
    have hc1 : (1 : Time) ≤ ((K S A).params.catchUp : Time) := by
      rw [goldilocksContract_params_eq]
      change (1 : Time) ≤ ((contract_coefficients S A).catchUp : Nat)
      exact_mod_cast (contract_coefficients S A).catchUp.pos
    change Q.run.1.ΔAC ≤ ((K S A).params.catchUp : Time) * Q.run.1.ΔAC + 1
    nlinarith
  obtain ⟨d, hheld, hdt⟩ := publication_held_ready_tail S Q.run.2 Q.hn hnet r hr
    (horg ▸ (mem_honestKeys_iff S Q.run.2 _).mp hmem)
    (not_isFGAtt_of_decodeForward hdecode) hy Q.bounded
    (by rw [htime, htk, hmax]; exact hD) hc
  obtain ⟨j, hj, hjt⟩ := held_forward_blockCall_lt S Q.run.2 Q.hn Q.valid hmem hheld hdecode hdt
  exact ⟨j, hj, hjt.le⟩

/-- **Final-window extraction at a gap `c` with (H4) discharged.** `final_window_extract_of_gap`
with the carrier premise from `carrier_processed_of_honest`; the gap, forwarding-delay and latency
premises, (H1) `hreset`, (H2) `hpropose` and (H3) `hplace` stay explicit. -/
theorem final_window_extract_of_gap' (Q : FinalQuery S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c])
    {ΔR a ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon)
    (hdel : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (c : Nat))
    (hlat : Q.query + 4 * ((Q.index : Nat) + 3 * c) * Q.params.Δ + Q.params.Δ ≤ Q.deadline)
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen) :
    ∃ W : FinalWindowData S A V Q, W.gap = c ∧
      Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * W.gap) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) :=
  final_window_extract_of_gap S A V Q hc2 h3c hpat hs hdel hlat hreset hpropose hplace
    (carrier_processed_of_honest S A V Q)

/-- **Final-window extraction with (H4) discharged.** `final_window_extract_of` with the
carrier premise from `carrier_processed_of_honest`; (H1) `hreset`, (H2) `hpropose` and
(H3) `hplace` stay explicit. -/
theorem final_window_extract_of' (Q : FinalQuery S A V) {ΔR a : Time}
    (hreset : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon)
    (hpropose : ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGrid S A V Q).slotTime s) →
      ∃ P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P)
    (hplace : max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
        ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
        ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
      Q.query + (finalGrid S A V Q).slotLen) :
    ∃ W : FinalWindowData S A V Q, Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      (∃ (proposer : Nat → Fin Q.params.n)
        (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
        Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
        Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
        (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
          (W.start + ![0, cF A.fgDelay, 2 * cF A.fgDelay, 3 * cF A.fgDelay] i) (W.block i)) ∧
        Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
        Q.params.ts (W.start + 3 * cF A.fgDelay) ≤ b) ∧
      ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc)
        (W.block i.succ) :=
  final_window_extract_of S A V Q hreset hpropose hplace (carrier_processed_of_honest S A V Q)

end Consensus.Goldilocks.Obligations

end
