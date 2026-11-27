module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient

public section

/-! # Honest locks before the advance

`client_progress_of_lock`: client progress (HS.4 (b), `Healing/AcquireClient`) with the lock
premise as a hypothesis, in place of `HSShared` and `PhaseOn`, for any node AC (`Node.LocalRun`
from any starts `ini`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
  {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- **Client progress from the lock premise.** Client progress (HS.4 (b)) with the lock premise
as a hypothesis (no `HSShared`, no phase): at an honest `fg_attest(C)` with `C` of state height
`h` and entry `E`, if the lock at `h` is free or `E`, the client signs an attestation `(h, E)`
now or signed one at an earlier cut. -/
theorem client_progress_of_lock (hrun : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n}
    (hy : y ∈ H) {k : Nat} {C : A.Blk} {signed : Option (FG.Att P.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed))) {E : A.Blk} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hlock : (tr.state y k).record.lock h = none ∨
      (tr.state y k).record.lock h = some E.root) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  have hr := Compose.fg_reachable hrun hy k
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  have hCTh : ((tr.state y k).fg.σ C.root).Th = E.root := by
    rw [Th_eq_of_anc hr hEC (hCh.trans hEh.symm), hETh]
  have hσe : (tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th =
      (tr.state y k).fg.σ E.root := by rw [hCTh]
  have he₁ : ((tr.state y k).fg.σ E.root).h = h := hEh
  have he₂ : ((tr.state y k).fg.σ E.root).Th = E.root := hETh
  have hlaw := hrun.cutLaw y hy k _ hc
  cases signed with
  | some a =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = some (a, _) at hcl
    rw [hσe] at hcl
    obtain ⟨-, hah, haT, -⟩ := Client.createAtt_some hcl
    exact Or.inl ⟨a, rfl, hah.trans he₁, haT.trans he₂⟩
  | none =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases Client.createAtt_none hcl with ⟨h1, h2⟩ | ⟨b, hb, hbh, hbT⟩
    · simp only [he₁, he₂] at h1 h2
      rcases hlock with hl | hl
      · exact absurd hl h1
      · exact absurd hl h2
    simp only [he₁, he₂] at hbh hbT
    obtain ⟨hok, hsent, -⟩ := record_facts hrun hy k
    have hbT' : b.2.1 = E.root := by
      rcases hbT with hbT | ⟨hto, htg⟩
      · exact hbT
      obtain ⟨h1, h2⟩ := (Client.sentOK_iff _).1 hok b hb
      cases hτ : b.2.2.1
      · have := h2 hτ
        rw [hbh] at this
        rcases htg with htg | htg <;> rw [htg] at this
        · cases this
        · exact (Option.some.inj this).symm
      · have := h1 hτ
        rw [hbh, hto] at this
        simp at this
    obtain ⟨k', hk', att, hsa, rfl⟩ := hsent b hb
    exact Or.inr ⟨k', hk', att, hsa, hbh, hbT'⟩

end Consensus.Goldilocks.Healing

end
