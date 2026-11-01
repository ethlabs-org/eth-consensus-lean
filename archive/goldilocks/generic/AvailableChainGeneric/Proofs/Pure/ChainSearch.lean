module
public import AvailableChainGeneric.Statements.Pure.ChainSearch

public section

namespace AvailableChain.Gen.Pure

/-- chain_search proves finite fixed-offset search.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem chain_search : ChainSearchStatement := by
  rw [ChainSearchStatement_def]
  intro P guard g s k
  induction k with
  | zero => intro q hg hk; omega
  | succ n ih =>
    intro q hg _ hS hguard
    have hq : guard q := hguard 0 (by omega) q (le_refl q) (by simp)
    obtain ⟨p₀, hp₀lo, hp₀hi, hp₀P⟩ := hS q hq
    by_cases hn : n = 0
    · subst n
      refine ⟨fun _ => p₀, ?_, hp₀lo, hp₀hi, ?_, ?_⟩
      · intro j hj; exact hp₀P
      · intro j hj; omega
      · simp only [Nat.add_sub_cancel, Nat.zero_mul, Nat.add_zero]
        omega
    · have hnpos : 1 ≤ n := by omega
      have hstep : p₀ + s ≤ q + (s + g - 1) := by omega
      have htailguard : ∀ j, j < n → ∀ q', p₀ + s ≤ q' →
          q' ≤ p₀ + s + j * (s + g - 1) → guard q' := by
        intro j hj q' hlo hhi
        apply hguard (j + 1) (by omega) q' (by omega)
        calc
          q' ≤ p₀ + s + j * (s + g - 1) := hhi
          _ ≤ q + (s + g - 1) + j * (s + g - 1) :=
            Nat.add_le_add_right hstep _
          _ = q + (j + 1) * (s + g - 1) := by
            simp only [Nat.add_mul, Nat.one_mul]
            omega
      obtain ⟨p, hP, hfirstlo, hfirsthi, hlinks, hlast⟩ :=
        ih (p₀ + s) hg hnpos hS htailguard
      let ps : Nat → Nat
        | 0 => p₀
        | j + 1 => p j
      refine ⟨ps, ?_, hp₀lo, hp₀hi, ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact hp₀P
        | succ j => exact hP j (by omega)
      · intro j hj
        cases j with
        | zero => exact ⟨hfirstlo, hfirsthi⟩
        | succ j => exact hlinks j (by omega)
      · have hnEq : n = (n - 1) + 1 := by omega
        have hsn : (n - 1) * s + s = n * s := by
          conv_rhs => rw [hnEq]
          simp only [Nat.add_mul, Nat.one_mul]
        change ps (n + 1 - 1) ≤ q + (n + 1) * (g - 1) + (n + 1 - 1) * s
        simp only [Nat.add_sub_cancel]
        rw [hnEq, show ps ((n - 1) + 1) = p (n - 1) from rfl]
        rw [← hnEq]
        simp only [Nat.add_mul, Nat.one_mul]
        omega

/-- chain_search_of_antitone_guard needs only the final reachable-start guard.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem chain_search_of_antitone_guard : AntitoneChainSearchStatement := by
  rw [AntitoneChainSearchStatement_def]
  intro P guard g s k q hg hk hS hanti hguard
  apply chain_search P guard g s k q hg hk hS
  intro j hj q' _ hhi
  apply hanti q' (q + (k - 1) * (s + g - 1)) _ hguard
  exact hhi.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (s + g - 1) (by omega : j ≤ k - 1)) q)

/-- chain_search_qf4 specializes to two searches; shift 3 gives q + 2g + 1.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem chain_search_qf4 : TwoStepChainSearchStatement := by
  rw [TwoStepChainSearchStatement_def]
  intro P guard g s q hg hS hanti hguard
  have hguard' : guard (q + (2 - 1) * (s + g - 1)) := by simpa using hguard
  obtain ⟨p, hP, hfirstlo, hfirsthi, hlinks, hlast⟩ :=
    chain_search_of_antitone_guard P guard g s 2 q hg (by omega) hS hanti hguard'
  have hlink := hlinks 0 (by omega)
  have hbound : p 1 ≤ q + 2 * (g - 1) + s := by simpa using hlast
  refine ⟨p 0, p 1, hP 0 (by omega), hP 1 (by omega), hfirstlo, hfirsthi,
    hlink.1, hlink.2, hbound, ?_⟩
  intro hs
  omega

end AvailableChain.Gen.Pure
