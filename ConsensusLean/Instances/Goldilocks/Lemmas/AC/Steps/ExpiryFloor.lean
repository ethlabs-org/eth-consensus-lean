module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Goldilocks SA: every lock lives at least two and at most `k` slots

`LocksWF`: every lock `l` of a set has `l.slot + 2 ≤ l.expiry ≤ l.slot + k`. It holds at every
state an honest node reaches (`locksWF_state`), at a cast's read point
(`castAt_readPoint_locksWF`) and after each call (`locksWF_post`). The lock functions keep
each lock's slot and expiry (`live_locks`, `unlock` and the move-back; a restart keeps the set),
and `add_locks` writes only expiries in `[s + 2, s + k]`: `fastExpiry` (`le_fastExpiry`,
`fastExpiry_le`), or `s + k` for a slow lock and a slow-qualified update's fast lock (B′). So
`LocksWF` is per lock, independent of the frame and the time, and needs no regime. The cap half
gives "live ⇒ recent" (`LocksWF.slot_le_of_live`), the floor half a fresh fast lock's two slots. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Every lock of `L` lives at least two slots and at most `k` slots past its slot. -/
def LocksWF (sp : SAParams) (L : Set Lock) : Prop :=
  ∀ l ∈ L, l.slot + 2 ≤ l.expiry ∧ l.expiry ≤ l.slot + sp.k

/-- The floor half: a lock of a well-formed set lives through `slot + 2`. -/
theorem LocksWF.floor {L : Set Lock} (h : LocksWF sp L) {l : Lock} (hl : l ∈ L) :
    l.slot + 2 ≤ l.expiry :=
  (h l hl).1

/-- The cap half: a lock of a well-formed set expires by `slot + k`. -/
theorem LocksWF.cap {L : Set Lock} (h : LocksWF sp L) {l : Lock} (hl : l ∈ L) :
    l.expiry ≤ l.slot + sp.k :=
  (h l hl).2

/-- A subset of a well-formed set is well formed. -/
theorem LocksWF.mono {L L' : Set Lock} (h : LocksWF sp L) (hL : L' ⊆ L) : LocksWF sp L' :=
  fun l hl => h l (hL hl)

/-- `live_locks` keeps `LocksWF`: a live lock keeps its source's slot and expiry. -/
theorem LocksWF.liveLocks {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time) :
    LocksWF sp (SA.liveLocks sp L Φ t) := by
  sorry

/-- **Live ⇒ recent.** A live lock of a well-formed set has `slot(t) ≤ l.slot + k`. -/
theorem LocksWF.slot_le_of_live {L : Set Lock} (h : LocksWF sp L) {Φ : Frm sp.n FGP}
    {t : Time} {l : Lock} (hl : l ∈ SA.liveLocks sp L Φ t) : sp.slot t ≤ l.slot + sp.k := by
  sorry

/-- `unlock` keeps `LocksWF`: a moved lock keeps its slot and expiry. -/
theorem LocksWF.unlock {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : LocksWF sp (SA.unlock sp L Φ t s V) := by
  sorry

/-- `add_locks` keeps `LocksWF` when every new lock of slot `s` has an expiry in
`[s + 2, s + k]`. -/
theorem LocksWF.addLocks {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) {N : Set (Nat × Bool × Nat)} (hN : ∀ p ∈ N, s + 2 ≤ p.2.2 ∧ p.2.2 ≤ s + sp.k) :
    LocksWF sp (SA.addLocks sp L Φ t s N) := by
  sorry

/-- The optimistic confirmation keeps `LocksWF` (its lock has expiry `fastExpiry`). -/
theorem LocksWF.optimisticConfirmation {A : SAState sp.n} (h : LocksWF sp A.locks)
    (Φ : Frm sp.n FGP) (t : Time) : LocksWF sp (SA.optimisticConfirmation sp A Φ t).locks := by
  sorry

/-- The confirmation update keeps `LocksWF`: its fast lock on `D` has expiry `s + k` when
the path has a slow-test block (B′) and `fastExpiry` otherwise, its slow lock `s + k`. -/
theorem LocksWF.updateConfirmation {A : SAState sp.n} (h : LocksWF sp A.locks)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    LocksWF sp (SA.updateConfirmation sp A Φ t s).locks := by
  sorry

/-- `try_vote` keeps `LocksWF`, in its post-state and in its emissions' read points. -/
theorem LocksWF.tryVote {A : SAState sp.n} (h : LocksWF sp A.locks) (x : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksWF sp (SA.tryVote sp x A Φ t).1.locks ∧
      ∀ e ∈ (SA.tryVote sp x A Φ t).2, LocksWF sp e.readPoint.locks := by
  sorry

/-- **One SA call keeps `LocksWF`**, in its post-state and in every emission's read point
(a well-formed frame and `t ≥ 0` for the restart). -/
theorem LocksWF.step {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LocksWF sp A.locks)
    (x : Fin sp.n) {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    LocksWF sp ((goldilocksSA sp FGP ro).step x A Φ t c).1.locks ∧
      ∀ e ∈ ((goldilocksSA sp FGP ro).step x A Φ t c).2, LocksWF sp e.readPoint.locks := by
  sorry

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- **`LocksWF` at every honest state** of an SA trace. -/
theorem locksWF_state (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : LocksWF sp (tr.state y i).locks := by
  sorry

/-- **`LocksWF` after an honest call.** -/
theorem locksWF_post (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    LocksWF sp (tr.post i).locks := by
  sorry

/-- **`LocksWF` at the read point of an honest cast.** -/
theorem castAt_readPoint_locksWF (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) : LocksWF sp e.readPoint.locks := by
  sorry

end Consensus.Goldilocks.SA

end
