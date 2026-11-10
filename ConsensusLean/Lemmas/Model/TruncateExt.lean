module
public import ConsensusLean.Lemmas.Model.Truncate

/-! # External data preserved by truncation -/

public section

namespace Consensus.Model

variable {V : Type} [Fintype V] {O : OutputSchema}
  {F : ProtocolFamily O} {E : Env V}

theorem Run.truncate_sel (rho : Run F E) (b : Time) :
    (rho.truncate b).sel = rho.sel := by
  rw [Run.truncate_eq]

theorem Run.truncate_key (rho : Run F E) (b : Time) :
    (rho.truncate b).key = rho.key := by
  rw [Run.truncate_eq]

end Consensus.Model

end
