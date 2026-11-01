module
public import AvailableChainPCSAProofs.Proofs.PC.AckOrigins
public import AvailableChainPCSAProofs.Proofs.Shared.HeadSupport
public import AvailableChainPCSAProofs.Proofs.Shared.RunEvidence

public section

/-! PC uniqueness through honest ackers and q_N HEAD intersection (proof plan C1). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- A held PC has q_N HEAD support; each honest supporting seat emitted its root. -/
theorem held_pc_head_support (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (x : V) (t : Time) (d : PC p.n)
    (hd : d ∈ (storeAt p c E rho x t).pcs) :
    ∃ S : Finset (Fin p.n), Gen.Pure.qN p.n ≤ S.card ∧ ∀ i ∈ S,
      rho.seatOf (.base (.head d.slot)) i ∈ rho.honest →
      ∃ a, V2.D.Run.emits E rho (rho.seatOf (.base (.head d.slot)) i)
        (⟨.seat (.base (.head d.slot)) i, .head d.target.root⟩ : Obj p) a := by
  obtain ⟨i, hi, a, k, hk, ho⟩ := held_pc_honest_ack E rho h hf x t d hd
  obtain ⟨b, hr, hb⟩ := ack_emission_nTarget p c m E rho _ d.slot i _ a k hk ho
  obtain ⟨S, hS, hs⟩ := nTarget_support p _ d.slot b hb
  have he := clock_evidence p (RootBlockInRun p c E rho) (HeadAuthentic E rho)
    (V2.D.Run.stateBefore E rho k (rho.seatOf (.base (.ack d.slot)) i)).st a
    (evidence_stateBefore E rho h.valid.toUnforgeableSignatures k _ hi)
  rw [StoreEvidence_def] at he
  refine ⟨S, hS, ?_⟩
  intro j hj hh
  have ha := he.2.2 _ (hs j hj)
  rw [HeadAuthentic_def] at ha
  simpa only [hr] using ha d.slot j b.root rfl hh

/-- Two held PCs of one slot name the same root, even with different honest ackers. -/
theorem held_pc_root_unique (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (x y : V) (t u : Time)
    (a b : PC p.n) (ha : a ∈ (storeAt p c E rho x t).pcs)
    (hb : b ∈ (storeAt p c E rho y u).pcs) (hs : a.slot = b.slot) :
    a.target.root = b.target.root := by
  classical
  obtain ⟨S, hS, hsent⟩ := held_pc_head_support E rho h hf x t a ha
  obtain ⟨T, hT, hsent'⟩ := held_pc_head_support E rho h hf y u b hb
  rw [← hs] at hsent'
  let F : Finset (Fin p.n) := Finset.univ.filter
    (fun i => rho.seatOf (.base (.head a.slot)) i ∉ rho.honest)
  have hF : F.card < Gen.Pure.qA p.n := lt_of_le_of_lt
    (fresh_faulty_card rho h.cstar (.head a.slot) trivial F
      (fun i hi => (Finset.mem_filter.mp hi).2)) hf
  let sent := fun (i : Fin p.n) (r : BlockId) =>
    rho.seatOf (.base (.head a.slot)) i ∈ rho.honest →
      ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head a.slot)) i)
        (⟨.seat (.base (.head a.slot)) i, .head r⟩ : Obj p) t
  apply Gen.Pure.qN_head_unique sent F S T a.target.root b.target.root
    ?_ hF hsent hsent' hS hT
  intro i hi r r' hr hr'
  have hh : rho.seatOf (.base (.head a.slot)) i ∈ rho.honest := by simpa [F] using hi
  obtain ⟨t, ht⟩ := hr hh
  obtain ⟨u, hu⟩ := hr' hh
  exact (head_emission_unique p c m E rho h.valid.nodup _ a.slot i r r' t u ht hu).1

/-- Named-body provenance upgrades root uniqueness to full PC-target uniqueness. -/
theorem held_pc_target_unique (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (x y : V)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (t u : Time)
    (a b : PC p.n) (ha : a ∈ (storeAt p c E rho x t).pcs)
    (hb : b ∈ (storeAt p c E rho y u).pcs) (hs : a.slot = b.slot) :
    a.target = b.target := by
  have he := evidence_storeAt E rho h.valid x hx t
  have he' := evidence_storeAt E rho h.valid y hy u
  rw [StoreEvidence_def] at he he'
  exact pcsa_rootBlock_eq E rho h.idealization a.target b.target (he.2.1 a ha) (he'.2.1 b hb)
    (held_pc_root_unique E rho h hf x y t u a b ha hb hs)

end AvailableChain.PCSA.Run
end
