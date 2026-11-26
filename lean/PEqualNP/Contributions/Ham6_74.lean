import PEqualNP.Library.Helpers.ReplayCol

/-!
A 74-gate circuit for Hamiltonicity on six labelled vertices. Input wire numbers
are the lexicographic indices of undirected edges. The target is the 60-cycle
disjunction from L-meta-17428, with the upper bound replaced by 74.

The first 30 gates recognize the 15 perfect matchings. Two edge-disjoint
perfect matchings form a 6-cycle. The remaining gates test for such a pair
using shared disjunctions. Bit-column replay checks all 32,768 inputs.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.Helpers.ReplayCol

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Contributions.ham6_size_le_74 :
    PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool =>
      (x 0 && x 4 && x 5 && x 9 && x 12 && x 14) ||
      (x 0 && x 3 && x 5 && x 9 && x 13 && x 14) ||
      (x 0 && x 4 && x 5 && x 10 && x 12 && x 13) ||
      (x 0 && x 2 && x 5 && x 10 && x 13 && x 14) ||
      (x 0 && x 3 && x 5 && x 11 && x 12 && x 13) ||
      (x 0 && x 2 && x 5 && x 11 && x 12 && x 14) ||
      (x 0 && x 4 && x 6 && x 9 && x 10 && x 14) ||
      (x 0 && x 3 && x 6 && x 9 && x 11 && x 14) ||
      (x 0 && x 4 && x 6 && x 10 && x 11 && x 12) ||
      (x 0 && x 1 && x 6 && x 11 && x 12 && x 14) ||
      (x 0 && x 3 && x 6 && x 10 && x 11 && x 13) ||
      (x 0 && x 1 && x 6 && x 10 && x 13 && x 14) ||
      (x 0 && x 4 && x 7 && x 9 && x 10 && x 13) ||
      (x 0 && x 2 && x 7 && x 10 && x 11 && x 13) ||
      (x 0 && x 4 && x 7 && x 9 && x 11 && x 12) ||
      (x 0 && x 1 && x 7 && x 11 && x 12 && x 13) ||
      (x 0 && x 2 && x 7 && x 9 && x 11 && x 14) ||
      (x 0 && x 1 && x 7 && x 9 && x 13 && x 14) ||
      (x 0 && x 3 && x 8 && x 9 && x 11 && x 12) ||
      (x 0 && x 2 && x 8 && x 10 && x 11 && x 12) ||
      (x 0 && x 3 && x 8 && x 9 && x 10 && x 13) ||
      (x 0 && x 1 && x 8 && x 10 && x 12 && x 13) ||
      (x 0 && x 2 && x 8 && x 9 && x 10 && x 14) ||
      (x 0 && x 1 && x 8 && x 9 && x 12 && x 14) ||
      (x 1 && x 4 && x 5 && x 6 && x 12 && x 14) ||
      (x 1 && x 3 && x 5 && x 6 && x 13 && x 14) ||
      (x 1 && x 4 && x 5 && x 7 && x 12 && x 13) ||
      (x 1 && x 2 && x 5 && x 7 && x 13 && x 14) ||
      (x 1 && x 3 && x 5 && x 8 && x 12 && x 13) ||
      (x 1 && x 2 && x 5 && x 8 && x 12 && x 14) ||
      (x 1 && x 4 && x 6 && x 7 && x 9 && x 14) ||
      (x 1 && x 3 && x 6 && x 8 && x 9 && x 14) ||
      (x 1 && x 4 && x 7 && x 8 && x 9 && x 12) ||
      (x 1 && x 3 && x 7 && x 8 && x 9 && x 13) ||
      (x 1 && x 4 && x 6 && x 7 && x 10 && x 13) ||
      (x 1 && x 2 && x 7 && x 8 && x 10 && x 13) ||
      (x 1 && x 4 && x 6 && x 8 && x 10 && x 12) ||
      (x 1 && x 2 && x 6 && x 8 && x 10 && x 14) ||
      (x 1 && x 3 && x 6 && x 8 && x 11 && x 12) ||
      (x 1 && x 2 && x 7 && x 8 && x 11 && x 12) ||
      (x 1 && x 3 && x 6 && x 7 && x 11 && x 13) ||
      (x 1 && x 2 && x 6 && x 7 && x 11 && x 14) ||
      (x 2 && x 4 && x 5 && x 6 && x 10 && x 14) ||
      (x 2 && x 3 && x 5 && x 6 && x 11 && x 14) ||
      (x 2 && x 4 && x 6 && x 7 && x 10 && x 11) ||
      (x 2 && x 3 && x 6 && x 8 && x 10 && x 11) ||
      (x 2 && x 4 && x 5 && x 7 && x 9 && x 14) ||
      (x 2 && x 3 && x 5 && x 8 && x 9 && x 14) ||
      (x 2 && x 4 && x 7 && x 8 && x 9 && x 10) ||
      (x 2 && x 3 && x 7 && x 8 && x 9 && x 11) ||
      (x 2 && x 4 && x 5 && x 7 && x 11 && x 12) ||
      (x 2 && x 4 && x 5 && x 8 && x 10 && x 12) ||
      (x 2 && x 3 && x 5 && x 8 && x 10 && x 13) ||
      (x 2 && x 3 && x 5 && x 7 && x 11 && x 13) ||
      (x 3 && x 4 && x 5 && x 7 && x 9 && x 13) ||
      (x 3 && x 4 && x 6 && x 7 && x 9 && x 11) ||
      (x 3 && x 4 && x 5 && x 6 && x 10 && x 13) ||
      (x 3 && x 4 && x 6 && x 8 && x 9 && x 10) ||
      (x 3 && x 4 && x 5 && x 6 && x 11 && x 12) ||
      (x 3 && x 4 && x 5 && x 8 && x 9 && x 12)) 74 := by
  apply hasCircuitSize_of_colReplay ⟨[
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [15, 14]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [17, 13]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [19, 12]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.and, [21, 14]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.and, [23, 13]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.and, [25, 12]⟩,
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.and, [27, 14]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.and, [29, 11]⟩,
    ⟨GateOp.and, [2, 8]⟩,
    ⟨GateOp.and, [31, 10]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.and, [33, 13]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.and, [35, 11]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.and, [37, 9]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [39, 12]⟩,
    ⟨GateOp.and, [4, 6]⟩,
    ⟨GateOp.and, [41, 10]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.and, [43, 9]⟩,
    ⟨GateOp.or, [34, 40]⟩,
    ⟨GateOp.or, [28, 34]⟩,
    ⟨GateOp.or, [28, 40]⟩,
    ⟨GateOp.or, [22, 32]⟩,
    ⟨GateOp.or, [36, 45]⟩,
    ⟨GateOp.or, [38, 45]⟩,
    ⟨GateOp.or, [20, 26]⟩,
    ⟨GateOp.or, [30, 32]⟩,
    ⟨GateOp.or, [20, 42]⟩,
    ⟨GateOp.or, [18, 50]⟩,
    ⟨GateOp.or, [47, 53]⟩,
    ⟨GateOp.or, [44, 47]⟩,
    ⟨GateOp.or, [18, 36]⟩,
    ⟨GateOp.or, [26, 42]⟩,
    ⟨GateOp.or, [24, 38]⟩,
    ⟨GateOp.or, [24, 49]⟩,
    ⟨GateOp.or, [22, 30]⟩,
    ⟨GateOp.or, [20, 44]⟩,
    ⟨GateOp.or, [16, 46]⟩,
    ⟨GateOp.or, [16, 22]⟩,
    ⟨GateOp.or, [36, 38]⟩,
    ⟨GateOp.or, [42, 44]⟩,
    ⟨GateOp.or, [26, 56]⟩,
    ⟨GateOp.or, [30, 63]⟩,
    ⟨GateOp.or, [18, 24]⟩,
    ⟨GateOp.or, [46, 48]⟩,
    ⟨GateOp.or, [16, 32]⟩,
    ⟨GateOp.and, [59, 55]⟩,
    ⟨GateOp.and, [68, 58]⟩,
    ⟨GateOp.and, [51, 66]⟩,
    ⟨GateOp.and, [57, 67]⟩,
    ⟨GateOp.and, [71, 60]⟩,
    ⟨GateOp.and, [65, 69]⟩,
    ⟨GateOp.and, [70, 62]⟩,
    ⟨GateOp.and, [61, 54]⟩,
    ⟨GateOp.and, [52, 64]⟩,
    ⟨GateOp.or, [72, 73]⟩,
    ⟨GateOp.or, [81, 74]⟩,
    ⟨GateOp.or, [82, 75]⟩,
    ⟨GateOp.or, [83, 76]⟩,
    ⟨GateOp.or, [84, 77]⟩,
    ⟨GateOp.or, [85, 78]⟩,
    ⟨GateOp.or, [86, 79]⟩,
    ⟨GateOp.or, [87, 80]⟩], 88⟩
  decide +kernel
