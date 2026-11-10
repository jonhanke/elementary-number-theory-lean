# Book maps

For each book of this release, a table from the results of the book to the Lean declarations and their status (generated from the coverage tables of the source repository and the kernel-level audit of its declarations).

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008)](hardy-wright.md) | 626 | 279 | 14 | 1 | 178 | 154 | 79 |
| [K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory* (2nd ed., 1990), Chapters 1–11, 15, 16 and the results of Chapter 17 proved here](ireland-rosen.md) | 401 | 120 | 5 | 0 | 178 | 98 | 53 |
| [I. Niven, H. S. Zuckerman and H. L. Montgomery, *An Introduction to the Theory of Numbers* (5th ed., 1991)](niven-zuckerman-montgomery.md) | 406 | 194 | 4 | 0 | 191 | 17 | 84 |
| [Special values of Dirichlet $L$-functions and Gauss's sign of quadratic Gauss sums](special-values.md) | 25 | 25 | 0 | 0 | 0 | 0 | 3 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case or one instance is proved. *Conditional*: proved from a named unproved input (here only the abc conjecture, in a note of Hardy–Wright). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: refuted as stated in the book (the corrected form is proved), in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history, open problems) are omitted from the maps.
