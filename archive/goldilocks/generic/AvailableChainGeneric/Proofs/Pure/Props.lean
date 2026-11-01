module
public import AvailableChainGeneric.Statements.Pure.Props
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

open AvailableChain

namespace AvailableChain.Gen.Pure

-- GLY r3.16 PROPERTY KERNEL; P3 r3.5.6:3644–3657; S3a FS2:1852–1853.
theorem compatOn_of_compatAt_mono_statement : CompatOnOfCompatAtMonoStatement := by
  rw [CompatOnOfCompatAtMonoStatement_def]
  intro V ι inst N out A hc hm htot
  rw [CompatOn_def]
  intro i j x y hi hj hx hy
  rcases htot i j with hij | hji
  · exact block_compatible_of_preceq_compatible
      (hm i j x hi hj hij hx) (hc j x y hj hx hy)
  · have h := block_compatible_of_preceq_compatible
      (hm j i y hj hi hji hy) (hc i y x hi hy hx)
    change Block.compatible (out i x) (out j y) = true
    rw [block_compatible_comm]
    exact h

-- LINK; keep the closed Statement's binder names.
theorem compatOn_of_compatAt_mono
    {V ι : Type} [Preorder ι] {N : V → Prop} {out : ι → V → Block} {A : ι → Prop}
    (hc : CompatAt N out A) (hm : MonoOn N out A)
    (htot : ∀ i j : ι, i ≤ j ∨ j ≤ i) : CompatOn N out A :=
  @compatOn_of_compatAt_mono_statement V ι _ N out A hc hm htot

-- S3a:1854; P3 r3.5.6:3650.
-- form: lean-framework ruling 2026-09-30 (later-read transport).
theorem servedOn_mono_statement : ServedOnMonoStatement := by
  rw [ServedOnMonoStatement_def]
  intro V ι inst N out B A A' hs hm hlater
  rw [ServedOn_def]
  intro j x hj hx
  rcases hlater j hj with ⟨i, hi, hi', hij⟩
  exact block_preceq_trans (hs i x hi hx) (hm i j x hi' hj hij hx)

-- LINK; keep the closed Statement's binder names.
theorem servedOn_mono
    {V ι : Type} [Preorder ι] {N : V → Prop} {out : ι → V → Block} {B : Block}
    {A A' : ι → Prop}
    (hs : ServedOn N out B A) (hm : MonoOn N out A')
    (hlater : ∀ j, A' j → ∃ i, A i ∧ A' i ∧ i ≤ j) : ServedOn N out B A' :=
  @servedOn_mono_statement V ι _ N out B A A' hs hm hlater

end AvailableChain.Gen.Pure
