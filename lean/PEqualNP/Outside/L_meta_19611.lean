import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19611 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3383575 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.not, [16]⟩,
    ⟨.or, [13, 17]⟩], 18⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
