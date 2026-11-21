# AI-use statement

**Tool:** Claude Code (Anthropic's Claude models)

## Summary

- **Written by me:** the core definitions and the base development (`Gram.lean`, `Params.lean`,
  `Recovery.lean`). I also typed, debugged and completed most of the proofs in the extension
  myself, working lemma by lemma.
- **Claude's main contributions:**
  - the mathematical argument for the extension (uniqueness from three non-parallel views), and the
    Lean statements of its lemmas;
  - minor hints on some of the extension proofs on what have statements should be made;
  - the final part of one proof (`eq_zero_of_vanishesOn_three`);
  - a final refactoring pass.

## 1. Base formalization: uniqueness assuming the constraints determine `B` up to scale

- I wrote the definitions (`Camera`, `Camera.U`, the consistency condition, `Satisfies`) and the
  base results: `gram_eq`, `params_unique`, `U_eq_of_gram_eq_smul` (originally
  `equal_under_scalar_mul`) and `gram_dot`.
- In a review I ran for a sanity check, Claude found that `consistent_satisfies` was stated incorrectly
  (`Satisfies K.U H` instead of `Satisfies (K.Uᵀ * K.U) H`). I corrected it and proved it, using
  the tactic steps Claude suggested.

## 2. Extension: uniqueness from three pairwise non-parallel views

This covers `Plane.lean`, `Unique.lean` and `zhang_nonparallel_uniqueness`.

**The mathematics.** Zhang's paper assumed that the constraints determine the matrix `B` up to scale. I
wanted to extend the formalization and prove this from a geometric condition instead.
- **Strategy (Claude and me).** I pointed out that `U` represents `A⁻¹`. Claude and I collaborated on the
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
  - `eq_zero_of_vanishesOn_three`: I wrote the setup and the key identity `h`, and claude helped finish up the last few bits which were quite hard to find
  - `zhang_nonparallel_uniqueness`: Claude redid the very short finishing proof on this during the refactor where I decided to get rid of the
    additional lemma from my original proof with a uniqueness to scale assumption definition.

## 3. Final refactoring

At my request, and with my review of each change, Claude carried out a cleanup pass:
- style fixes, renames, and docstring and copyright templates;
- minimal imports and conversion to the Lean module system;
- splitting long proofs into private helper lemmas, keeping the proof steps;
- definition changes to align with Mathlib:
  - `IsSymm` for symmetry;
  - Mathlib's matrix inverse `K.U⁻¹` in place of `Camera.A`;
  - `ConsistentHomographyPair` as a structure using Mathlib's `Orthonormal`;
  - removing `HomographyM3`, `IsOrthonormalPair` and `UniqueToScaleFactor`.

New code Claude wrote in this pass:
- in `Basic.lean`: `Camera.det_U`, `Camera.isUnit_det_U`, `Camera.inv_mul_U`, `Camera.U_mul_inv`
  and `dotProduct_eq_of_orthonormal`;
- in `Plane.lean`: `cross_dot_cross_ne_zero`;
- in `Main.lean`: the current proof of `zhang_nonparallel_uniqueness`.

## How I checked the work

- The project builds with no `sorry`. Both main theorems depend only on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
- I checked that the definitions and main theorem statements match the model in Zhang's paper.
