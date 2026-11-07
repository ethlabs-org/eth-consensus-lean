module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.Rule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.WeightInv

public section

/-! # Candidate `cert-recovery`: idempotence on reachable states

The idempotence of the candidate's unlock (`certUnlock_idempotent`) assumes that the stored
weights are antitone along the chains of the call's frame. On the evidence-release SA's runs that
holds of every stored weight, in the frame of the last call and every later frame of the run's
coherent block set (`EvidenceRelease.weightAntitone_of_reachable`); the late-certificate stage
moves locks and never changes a weight. So for locks whose weighted locks are stored locks of a
reachable evidence-release state, the unlock is idempotent with no further hypothesis
(`certUnlock_idempotent_of_reachable`). -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

/-- **Idempotence on reachable states.** Let `X` be a reachable state of the evidence-release SA
inside a coherent `U`, with `Φ` the frame of its last call, and `Φ'` a frame of `U` whose finalized
tip is at or above `Φ`'s (such as the next call's). For locks with formation slots whose weighted
locks are stored locks of `X`, the candidate's unlocking in `Φ'` is idempotent, for every arrival
record. -/
theorem certUnlock_idempotent_of_reachable {U : Set (Blk sp.n FGP)} (hU : Coherent U)
    {ro : ReplayOrder sp FGP} {self : Fin sp.n} {X : (evidenceReleaseSA sp FGP ro).State}
    {Φ : (evidenceReleaseSA sp FGP ro).Frm} {t₀ : Time}
    (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ t₀) {Φ' : Frm sp.n FGP}
    (hΦ' : FrameOK Φ') (hΦ'U : Φ'.tree ⊆ U) (hF : Anc U Φ.F Φ'.F) (ctx : CertCtx sp.n)
    {L : Set CLock} (hL : ∀ c ∈ L, c.w ∈ X.wlocks) (t : Time) (s : Int) (V : View sp.n) :
    certUnlock sp ctx (certUnlock sp ctx L Φ' t s V) Φ' t s V = certUnlock sp ctx L Φ' t s V :=
  certUnlock_idempotent hΦ' ctx (fun c hc => (weightAntitone_iff Φ' c.w).2
    ((treeAntitone_iff Φ' _).1 (weightAntitone_of_reachable hU h hΦ' hΦ'U hF c.w (hL c hc))))
    t s V

end Consensus.Goldilocks.LateCertificate

end
