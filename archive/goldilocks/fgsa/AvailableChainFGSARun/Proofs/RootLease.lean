module
public import AvailableChainGeneric.Proofs.AC.Lease

public section

namespace AvailableChain.FGSA.RootLease

open Gen.AC.Root

/-- [ROOT-DIGEST-2 W2; DC lease algebra] Lease writes use only the obligations field. -/
theorem root_write_unique_keys {n : Nat} (st : GridCO.State n .root) (B : Block) (g : Nat)
    (d : Time) (hu : UniqueLeaseKeys st) :
    UniqueLeaseKeys (GridCO.writeObligation st B g d) :=
  Gen.AC.write_unique_keys { GridCO.initial n with obligations := st.obligations } B g d hu

/-- [ROOT-DIGEST-2 W2; DC lease algebra] A write cannot shorten an existing deadline. -/
theorem root_write_protectsUntil {n : Nat} (st : GridCO.State n .root) (B C : Block) (g k : Nat)
    (d limit : Time) (hu : UniqueLeaseKeys st) (h : ProtectsUntil st B g d) :
    ProtectsUntil (GridCO.writeObligation st C k limit) B g d :=
  Gen.AC.write_protectsUntil { GridCO.initial n with obligations := st.obligations }
    B C g k d limit hu h

/-- [ROOT-DIGEST-2 W2; DC lease algebra] Expiry retains a future deadline. -/
theorem root_expire_protectsUntil {n : Nat} (st : GridCO.State n .root) (B : Block) (g : Nat)
    (d t : Time) (h : ProtectsUntil st B g d) (ht : t < d) :
    ProtectsUntil (GridCO.expire st t) B g d :=
  Gen.AC.expire_protectsUntil { GridCO.initial n with obligations := st.obligations }
    B g d t h ht

/-- [ROOT-DIGEST-2 W2; DC lease algebra] Root-mode release retains a row below its threshold. -/
theorem root_release_protectsUntil (p : GridCO.Params) {n : Nat} (st : GridCO.State n .root)
    (r : Slot) (B : Block) (g : Nat) (d : Time) (h : ProtectsUntil st B g d)
    (hc : GridCO.releaseCount p st r B < g) :
    ProtectsUntil (GridCO.release p st r) B g d := by
  obtain ⟨deadline, hd, hr⟩ := h
  exact ⟨deadline, hd, List.mem_filter.mpr ⟨hr, decide_eq_true hc⟩⟩

end AvailableChain.FGSA.RootLease
end
