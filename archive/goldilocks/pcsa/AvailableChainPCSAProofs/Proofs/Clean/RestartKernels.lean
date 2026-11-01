module
public import AvailableChainPCSAProofs.Proofs.Clean.AckResults
public import AvailableChainPCSAProofs.Proofs.Clean.PCChain
public import AvailableChainPCSAProofs.Proofs.Clean.JointAux

public section

/-! The joint-step kernels of the CI restart from label `a`: the clean kernels
with every label quantifier from `a` and the delivery window in place of CLEAN.
PCs of slot below `a` and acks of labels below `a` are outside the restart. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- From label `a`: adjacent HEAD coverage and ordered results give coverage of
every earlier result of a label at least `a`. -/
theorem pcsa_heads_cover_past_results_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {a : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hchain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i i' X Y, a ≤ i → i ≤ i' → i' ≤ j →
      gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
      (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y))
    (hheads : ∀ i x y H X, a < i → i ≤ j → HonestHeadAt p c E rho x i H → y ∈ rho.honest →
      gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H)
    (k : Slot) (hk : k ≤ j) (z : V) (H : Block) (hH : HonestHeadAt p c E rho z k H)
    (y : V) (hy : y ∈ rho.honest) (i : Slot) (X : Block) (hai : a ≤ i) (hi : i < k)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Preceq X H := by
  have hprev : k - 1 ≤ j := (Nat.sub_le k 1).trans hk
  have hak : a ≤ k - 1 := hai.trans (Nat.le_pred_of_lt hi)
  obtain ⟨D, hD⟩ := pcsa_clean_result_exists_win E rho h hF y hy (k - 1) hak
    ((pcsa_gate_time_mono p hprev).trans hc)
  have hiPrev : i ≤ k - 1 := Nat.le_pred_of_lt hi
  have hXD : Block.Preceq X D := by
    rcases hiPrev.lt_or_eq with hlt | heq
    · exact (hchain y hy y hy i (k - 1) X D hai hiPrev hprev hX hD).1 hlt
    · subst i
      have he : X = D := Option.some.inj (Option.some.inj (hX.symm.trans hD))
      rw [he]
      exact Gen.Pure.block_preceq_refl _
  exact Gen.Pure.block_preceq_trans hXD
    (hheads k z y H D (Nat.lt_of_le_of_lt hai hi) hk hH hy hD)

/-- From label `a`: prior-result and prior-ack coverage make every ack/result pair
of labels at least `a` compatible. -/
theorem pcsa_ack_result_compatible_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {a : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hpast : ∀ k, k ≤ j → ∀ z H, HonestHeadAt p c E rho z k H →
      ∀ y ∈ rho.honest, ∀ i X, a ≤ i → i < k →
        gateResultAt p c E rho y i = some (some X) → Block.Preceq X H)
    (hdis : ∀ k i, a ≤ k → k < i → i ≤ j → ∀ z B, HonestAckAt p c E rho z k B →
      ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Preceq B X)
    (s : Slot) (has : a ≤ s) (hs : s ≤ j) (z : V) (B : Block)
    (ha : HonestAckAt p c E rho z s B)
    (i : Slot) (hai : a ≤ i) (hi : i ≤ j) (y : V) (hy : y ∈ rho.honest) (X : Block)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Compatible B X := by
  rcases lt_trichotomy s i with hlt | heq | hgt
  · exact Bool.or_eq_true_iff.mpr (Or.inl (hdis s i has hlt hi z B ha y hy X hX))
  · subst i
    have hcut : SA.gateTime p.toParams s ≤ cut := (pcsa_gate_time_mono p hs).trans hc
    exact pcsa_honestAck_same_label_result_win E rho h hF hFault z y hy s B X has hcut ha hX
  · obtain ⟨u, hu⟩ := pcsa_ack_has_honest_head E rho h.base hF hFault z s B ha
    exact Bool.or_eq_true_iff.mpr (Or.inr (hpast s hs u B hu y hy i X hai hgt hX))

/-- From slot `a`: earlier ack dissemination orders the bounded held PC targets of
slot at least `a`. -/
theorem pcsa_pc_storeAt_chain_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) (a j : Slot)
    (hdis : ∀ i i', a ≤ i → i < i' → i' ≤ j → ∀ y A, HonestAckAt p c E rho y i A →
      ∀ z H, HonestHeadAt p c E rho z i' H → Block.Preceq A H)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t t' : Time)
    (ht : t < SA.voteTime p.toParams (j + 1))
    (ht' : t' < SA.voteTime p.toParams (j + 1)) (C D : PC p.n)
    (haC : a ≤ C.slot) (haD : a ≤ D.slot)
    (hC : C ∈ (storeAt p c E rho x t).pcs) (hD : D ∈ (storeAt p c E rho y t').pcs) :
    Block.Compatible C.target D.target ∧ (C.slot < D.slot → Block.Preceq C.target D.target) := by
  obtain ⟨hcj, u, hu⟩ := pcsa_pc_storeAt_ack_slot E rho h hFault j x hx t ht C hC
  obtain ⟨hdj, v, hv⟩ := pcsa_pc_storeAt_ack_slot E rho h hFault j y hy t' ht' D hD
  have forward (hlt : C.slot < D.slot) : Block.Preceq C.target D.target := by
    obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault v D.slot D.target hv
    exact hdis C.slot D.slot haC hlt hdj u C.target hu z D.target hz
  refine ⟨?_, forward⟩
  rcases lt_trichotomy C.slot D.slot with hlt | heq | hgt
  · exact Bool.or_eq_true_iff.mpr (Or.inl (forward hlt))
  · have hh := pcsa_ack_targets_unique E rho h hF hFault u v C.slot C.target D.target
      hu (heq.symm ▸ hv)
    rw [hh]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (Gen.Pure.block_preceq_refl _)
  · obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h hF hFault u C.slot C.target hu
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (hdis D.slot C.slot haD hgt hcj v D.target hv z C.target hz))

/-- From slot `a`: every bounded held PC of slot at least `a` is compatible with
every result of a label at least `a`. -/
theorem pcsa_pc_storeAt_result_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {a : Slot} {T₀ cut : Time}
    (h : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hpast : ∀ k, k ≤ j → ∀ z H, HonestHeadAt p c E rho z k H →
      ∀ y ∈ rho.honest, ∀ i X, a ≤ i → i < k →
        gateResultAt p c E rho y i = some (some X) → Block.Preceq X H)
    (hdis : ∀ k i, a ≤ k → k < i → i ≤ j → ∀ z B, HonestAckAt p c E rho z k B →
      ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Preceq B X)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t : Time)
    (ht : t < SA.voteTime p.toParams (j + 1)) (C : PC p.n) (haC : a ≤ C.slot)
    (hC : C ∈ (storeAt p c E rho x t).pcs) (i : Slot) (hai : a ≤ i) (hi : i ≤ j) (X : Block)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Compatible C.target X := by
  obtain ⟨hcj, z, hz⟩ := pcsa_pc_storeAt_ack_slot E rho h.base hFault j x hx t ht C hC
  exact pcsa_ack_result_compatible_from E rho h hF hFault j hc hpast hdis C.slot haC hcj z
    C.target hz i hai hi y hy X hX
end AvailableChain.PCSA.Run

end
