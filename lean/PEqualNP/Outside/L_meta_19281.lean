import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19281 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
