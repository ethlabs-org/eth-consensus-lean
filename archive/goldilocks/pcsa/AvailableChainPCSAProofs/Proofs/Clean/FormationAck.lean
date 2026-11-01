module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCount
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties

public section

/-! Formation step 3 emission and fresh-seat count (pcsa34-r4.3 §5.3).
An honest ack decision is turned into its scheduled wire emission.
F2 then gives a PC quorum; no additional ack emission hypothesis is needed.
OPEN: produce the early N target and A2 for participating nodes from F1–F7.
OPEN: derive the view bound with whole-PC relay, including ack-only nodes.
The old missing-PC fixture fails current F1 and is a relay regression.
Root-form carriage closes the PC target alias gap. Its fixture needs the
root-form relay schedule. The all-early view bound remains to be derived. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- An honest early ack decision emits the exact ack for each owned seat. -/
theorem pcsa_formation_ack_emits (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (_h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (i : Fin p.n)
    (hAck : HonestAckAt p c E rho y s N.erase) (hSeat : rho.seatOf (.base (.ack s)) i = y) :
    V2.D.Run.emits E rho y (ackObj p s i N.erase.root) (SA.earlyTime p.toParams s) := by
  have ha := hAck
  rw [pcsa_HonestAckAt_def] at ha
  have hread := ha.2.2
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, hfor⟩ := Option.map_eq_some_iff.mp hread
  rw [pcsa_postClock_def] at hnd
  obtain ⟨pre, hpre, hclock⟩ := Option.map_eq_some_iff.mp hnd
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  have ht := V2.D.Run.tickIdx?_spec hk
  refine ⟨k, ht, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho ht).2]
  apply (V2.D.Engine.mem_tick_seat_iff E rho _ y _ (.base (.ack s)) i (.ack N.erase.root)).mpr
  refine ⟨ha.2.1, hSeat, .ackAction s, rfl, rfl, ?_⟩
  cases m <;>
    change (ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.earlyTime p.toParams s)) s).map (fun B => Msg.ack B.root) = some (.ack N.erase.root)
  all_goals
    change ackFor p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.earlyTime p.toParams s)) s = some N.erase at hfor
    rw [hfor]
    rfl

/-- F2 and honest ack decisions supply a fresh emitted PC quorum. -/
theorem pcsa_formation_ack_quorum (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase) :
    ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧
      ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
          (ackObj p s i N.erase.root) (SA.earlyTime p.toParams s) := by
  classical
  let H : Finset V := awakeHonestLabel p c E rho s
  let holder : Fin p.n → V := rho.seatOf (.base (.ack s))
  let Q : Finset (Fin p.n) := Finset.univ.filter (fun i => holder i ∈ H)
  have hbij : Function.Bijective holder := h.base.cstar (.base (.ack s)) trivial
  have hcard : Q.card = H.card := by
    apply Finset.card_bij (fun i _ => holder i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ he
      exact hbij.injective he
    · intro y hy
      obtain ⟨i, hi⟩ := hbij.surjective y
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hy⟩, hi⟩
  have hn : nQuorum p.n ≤ Q.card := hcard ▸ h.participation
  have hq : pcQuorum p.n ≤ Q.card := by
    have hi := pcsa_n_inter_card hn hn
    rwa [Finset.inter_self] at hi
  refine ⟨Q, hq, ?_⟩
  intro i hi
  have hm : rho.seatOf (.base (.ack s)) i ∈ awakeHonestLabel p c E rho s :=
    (Finset.mem_filter.mp hi).2
  rw [pcsa_awakeHonestLabel_def] at hm
  have he := (Finset.mem_inter.mp hm).2
  rw [Gen.V2.Duty.awakeHonest_def] at he
  obtain ⟨hy, haw⟩ := Finset.mem_filter.mp he
  exact ⟨hy, pcsa_formation_ack_emits E rho s N ΔF h _ i (hAck _ hy haw) rfl⟩

/-- Only the nodes awake at both reads are needed for the emitted PC quorum. -/
theorem pcsa_formation_participating_ack_quorum (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      E.awake y (SA.earlyTime p.toParams s) = true → HonestAckAt p c E rho y s N.erase) :
    ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧
      ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
          (ackObj p s i N.erase.root) (SA.earlyTime p.toParams s) := by
  classical
  let H : Finset V := awakeHonestLabel p c E rho s
  let holder : Fin p.n → V := rho.seatOf (.base (.ack s))
  let Q : Finset (Fin p.n) := Finset.univ.filter (fun i => holder i ∈ H)
  have hbij : Function.Bijective holder := h.base.cstar (.base (.ack s)) trivial
  have hcard : Q.card = H.card := by
    apply Finset.card_bij (fun i _ => holder i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ he
      exact hbij.injective he
    · intro y hy
      obtain ⟨i, hi⟩ := hbij.surjective y
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hy⟩, hi⟩
  have hn : nQuorum p.n ≤ Q.card := hcard ▸ h.participation
  have hq : pcQuorum p.n ≤ Q.card := by
    have hi := pcsa_n_inter_card hn hn
    rwa [Finset.inter_self] at hi
  refine ⟨Q, hq, ?_⟩
  intro i hi
  have hm : rho.seatOf (.base (.ack s)) i ∈ awakeHonestLabel p c E rho s :=
    (Finset.mem_filter.mp hi).2
  rw [pcsa_awakeHonestLabel_def] at hm
  have hv := (Finset.mem_inter.mp hm).1
  have he := (Finset.mem_inter.mp hm).2
  rw [Gen.V2.Duty.awakeHonest_def] at hv he
  obtain ⟨hy, hawV⟩ := Finset.mem_filter.mp hv
  obtain ⟨_, hawE⟩ := Finset.mem_filter.mp he
  exact ⟨hy, pcsa_formation_ack_emits E rho s N ΔF h _ i (hAck _ hy hawV hawE) rfl⟩

end AvailableChain.PCSA.Run
end
