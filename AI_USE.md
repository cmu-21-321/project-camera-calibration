# AI-use statement

**Tool:** Claude Code

## Summary

- **Written by me:** the core definitions and the base development (`Gram.lean`, `Params.lean`,
  `Recovery.lean`, `Satisfies.lean`, `Main.lean`, `Basic.lean`). I also typed, debugged and completed most of the proofs in the extension
  myself, working lemma by lemma.
- **Claude's main contributions:**
  - significant aid in the mathematical argument for the extension (uniqueness from three non-parallel views), and help with the
    Lean statements of its lemmas;
  - minor hints and for some of the harder ones some rough outlines for the extension proofs
  - more help on the final part of one proof (`eq_zero_of_vanishesOn_three`);
  - a final refactoring pass.

## 1. Base formalization: uniqueness assuming the constraints determine `B` up to scale

- I wrote the definitions (`Camera`, `Camera.U`, the consistency conditions, `Satisfies`, and the previous homography, orthonormality, etc. conditions) and the
  base results including: `gram_eq`, `params_unique`, `U_eq_of_gram_eq_smul`, `gram_dot`, the now missing `Gram.lean` results, and `Recovery.lean` and did the proofs
- there were a lot more proofs in gram but in final pass found mathlib lemmas that could replace them for simplicity

## 2. Extension: uniqueness from three pairwise non-parallel views

This covers `Plane.lean` and `Unique.lean`.

**The mathematics.** Zhang's paper assumed that the constraints determine the matrix `B` up to scale. I
wanted to extend the formalization and prove this from a geometric condition instead.
- **Strategy (Claude and me).** Claude and I collaborated on the
  strategy that made the most sense to tackle this where we decided on: conjugate to `C = U⁻ᵀ B U⁻¹`, and show that a symmetric matrix whose quadratic form
  vanishes on three pairwise non-parallel planes is zero.

**Lean statements.** Claude helped me draft the definition `VanishesOn` and the statements of the
extension's lemmas. I adjusted them where proofs required it and set them up in the project.

**Lean proofs.**
- **Written by me.** I wrote the proofs of `bilin_zero_of_vanishesOn`,
  `dotProduct_sub_smul_one_mulVec_self_eq_zero` (originally `form_on_span`),
  `eq_of_vanishesOn_sub_smul_one` (originally `mu_eq`), `cross_dot_self_smul_eq` (originally
  `decomp`), and the lemmas in `Unique.lean`. Claude helped me debug and search for some key mathlib lemmas.
- **More direct:**
  - `eq_zero_of_vanishesOn_three`: I wrote the setup and the key identity `h`, and claude with some guiding tips to finish up the last few bits which were quite hard to find on my own.

## 3. Final refactoring

At my request, and with my review of each change, Claude carried out a cleanup pass:
- style fixes, renames, and docstring and copyright templates;
- minimal imports and conversion to the Lean module system;
- splitting long proofs into private helper lemmas, keeping the proof steps;
- docstring formatting and style, i.e. adding the copywrite statements mathlib requires
- definition changes to align with Mathlib:
  - `IsSymm` for symmetry;
  - Mathlib's matrix inverse `K.U⁻¹` in place of `Camera.A`;
  - `ConsistentHomographyPair` as a structure using Mathlib's `Orthonormal`;
  - removing `HomographyM3`, `IsOrthonormalPair` and `UniqueToScaleFactor`.

New things written in this pass to refactor the code:
- in `Basic.lean`: `Camera.det_U`, `Camera.isUnit_det_U`, `Camera.inv_mul_U`, `Camera.U_mul_inv`
  and `dotProduct_eq_of_orthonormal`;

## 4. Report

I had Claude help me make the LaTeX template I used so that it could compile the lean font correctly then some basic revision stuff to ensure clarity and grammar was fine.
