# Lower bounds for blocks of a 3 × 3 Boolean matrix product

L-meta-18919 asks for nine outputs in 44 gates. In search shard 6 exactly one gate is a NOT, so at most 43 gates can have two effective operands. Write an output as

$$
Y_{ij}=(A_{i0}\land B_{0j})\lor(A_{i1}\land B_{1j})\lor(A_{i2}\land B_{2j}).
$$

The six off-diagonal outputs jointly require **30 two-input gates**. The direct construction attains 30 with 18 ANDs and 12 ORs. The lower bound counts gates even if intermediate wires can feed any number of later gates. In particular an nine-output implementation with one NOT and size at most 44 must contain **at least four two-input AND/OR gates whose results reach multiple outputs**.

The Lean proof in [BooleanMatrixProduct.lean](../lean/PEqualNP/Contributions/BooleanMatrixProduct.lean) establishes the six-output bound on the project's gate-list interpreter. The theorem `six_output_bound` counts only two-input gates on paths to the six selected taps. The theorem `physical_gate_bound` expresses the bound using gate positions in the original list. Run `lake build PEqualNP.Contributions.BooleanMatrixProduct` from `lean/`.

## Counting the first forks

Give each output a distinct terminal tap, including a tap that reads an existing output wire. Retain vertices on paths to the chosen taps. A fork is a wire with two or more readers. Count a repeated operand to the same gate once, and count the first operand of a NOT as its only effective operand. For a live network with $n$ input wires, $m$ taps, and $b$ binary gates, the surplus of outgoing edges beyond one per nonterminal vertex is at most $b+m-n$. This follows by summing indegrees and outdegrees. Constants and gates that read just one earlier wire preserve the inequality.

Suppose an input can affect two different outputs. Follow its unique reader repeatedly until reaching its first fork. Every path from that input to a tap passes through this fork. Two inputs must have different first forks if one can fix all the other inputs and obtain at least three distinct output vectors by varying the pair. Otherwise one bit at their common fork would determine all the variations. The Lean proof uses three runs with distinct output vectors and traces a differing output back to a differing input.

For the six off-diagonal outputs, all 18 input bits each affect two outputs. Every pair has a three-run separation witness. The proof file gives the selectors and checks each witness against the dot-product definition. There are therefore at least 18 forks, and $b\ge18+18-6=30$.

## Selecting other outputs

The same argument applies to any nonempty set of $k$ outputs containing at most two cells in each row and each column. Each essential input then occurs in one or two dot products. If $n$ distinct inputs occur, there are $6k-n$ inputs occurring twice. Any two of the repeated inputs can be independently observed.

* For two entries of $A$, select an output in each corresponding row using different columns. Set each of those columns of $B$ to the unit vector selecting the desired entry. This works also for two entries in the same row since it has two selected outputs.
* For two entries of $B$, exchange the roles of rows and columns.
* For $A_{ri}$ and $B_{jc}$, observe the former in a selected output in row $r$ outside column $c$, and the latter in a selected output in column $c$ outside row $r$. The two unit selectors can be set independently.

Thus $b\ge n+$6k-n$-k=5k$. The direct construction attains equality. This includes all 36 pairs of outputs and all six complements of permutation matrices. The Lean file instantiates the general fork argument on the off-diagonal selection. The other five six-cell selections follow by relabelling columns.

For the four-shared-gate conclusion, sum the six lower bounds of 30. Each gate reaching only one final output is counted four times. Any shared gate is counted at most six times. If $s$ gates are shared, a circuit with at most 43 binary gates can contribute at most $4(43-s)+6s$, which must be at least 180. This yields $s\ge4$.

## Three outputs in one row

An independent finite calculation gives a lower bound of 15 two-input gates for a full row, and by transposition for a full column. Here there are 12 essential inputs and three taps. With 14 binary gates the outgoing surplus is at most five. Split a fanout of degree $d$ into $d-1$ binary copies, allowing arbitrary computation between copies. Each of the three row bits has a first fork and these three forks are distinct by the two-bit separation argument above.

Fix the columns of $B$ to unit selectors. Once fixed, the only varying signals are the three row bits. Compress the computation to its copy vertices and three output taps. Each copy has at most two next destinations. A path can merge with another path before the next destination, which is covered by allowing arbitrary Boolean functions at that destination. Each row bit enters at its first copy vertex. Repeated destinations or unused copies can be relaxed to two distinct forward destinations because the extra signal can be ignored.

The [finite search](../methods/find/matrix_product_row.py) enumerates all such cores through five binary copies. Every source must reach every receiver. Removing one vertex cannot disconnect two sources from two receivers required to distinguish four bit pairs. Removing two vertices cannot disconnect all three sources from all three receivers on a permutation demand. For each surviving core and each of the 27 ordered demands, the program permits a fresh choice of the local truth tables, and tests whether all three receivers obtain their requested bits. Internal tables are normalized to vanish at 000 since their complements can be absorbed by downstream functions.

| Binary copies | All sources reach all receivers | Pass the one- and two-vertex cut tests | Support every demand |
|---:|---:|---:|---:|
| 3 | 0 | 0 | 0 |
| 4 | 150 | 0 | 0 |
| 5 | 16,500 | 636 | 0 |

Fewer than three copies already contradict the distinct-first-fork condition. The program also tests a six-copy positive control that sends all three bits to each receiver. Consequently at least six copies are needed and $b\ge12-3+6=15$. This last calculation is reproducible in Python and separate from the Lean-checked six-output result.

Together the arguments show that optimizing separate blocks of up to three outputs each cannot save a binary gate over the direct construction. A circuit meeting shard 6 must share work across a larger block. The nine-output search remains open.
