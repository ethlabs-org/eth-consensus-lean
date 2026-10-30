module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint

public section

/-! # Goldilocks Healing: where the honest slot-`p` walks start (T1 §6)

The anchor of an honest vote of slot `p`, and the anchor of the honest proposal of slot `p`
(`d.start`), are `fc_root` (genesis) or a live lock block. A lock of a slot below `p` is settled
(`LocksSettled` from `t_{p−1}`): every honest vote of slot `p` and the proposal head `d.head`
extend its stored block, which extends the lock block. A lock of slot `p` is written by an
optimistic confirmation on three quarters of the committee, so it is extended by an honest
slot-`p` vote; at a vote, one cast at an earlier cut (`lock_origin_readPoint`). No lock has a
later slot. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n}

/-- **The anchor of an honest slot-`p` vote**: a block of `U` that every honest vote of slot
`p` and the proposal head extend, or extended by an honest slot-`p` vote of an earlier cut. -/
theorem vote_anchor_cases (hs : UnanimitySetting tr H U g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) :
    getAnchor sp e.readPoint ℓ.frame (tr.time j) ∈ U ∧
      ((Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time j)) d.head ∧
        ∀ z ∈ H, ∀ j' e', VoteAt tr z j' e' → e'.msg.slot = p →
          VoteExtends U e'.msg (getAnchor sp e.readPoint ℓ.frame (tr.time j))) ∨
      ∃ z ∈ H, ∃ j' < j, ∃ e', VoteAt tr z j' e' ∧ e'.msg.slot = p ∧
        VoteExtends U e'.msg (getAnchor sp e.readPoint ℓ.frame (tr.time j))) := by
  sorry

/-- **The anchor of the proposal**: a block of `U` that every honest vote of slot `p` extends,
or extended by some honest slot-`p` vote. -/
theorem proposal_anchor_cases (hs : UnanimitySetting tr H U g p P k ℓp d pay) :
    d.start ∈ U ∧
      ((∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = p → VoteExtends U e.msg d.start) ∨
        ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = p ∧ VoteExtends U e.msg d.start) := by
  sorry

end Consensus.Goldilocks.SA

end
