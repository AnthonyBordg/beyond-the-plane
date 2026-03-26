# Beyond the Plane: Abstracting Away Geometry from AlphaGeometry

This repository contains the Lean 4 formalization accompanying the paper of the same title.  
A preprint of the paper is available: https://doi.org/10.5281/zenodo.18959740

## Project Structure
- `BeyondThePlane/`: Main library.
  - `Syntax.lean`: Sections 2.1.1 through 2.1.10 of the paper.
  - `Semantics.lean`: Sections 2.2.1 through 2.3.3 of the paper.
  - `ObservableCategory.lean`: A dependency of the above file.  
  - `AffineGeometry`: Section 3.2.2 of the paper. 

## Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (Version: `v4.27.0-rc1`)
- `elan` (Lean version manager)

## How to Build
To verify the proofs locally, follow these steps:

1. Open a terminal in the project root.
2. Fetch the Mathlib cache to avoid long compilation times:
   ```bash
   lake exe cache get   

## Credits

* **Project Lead & Scientific Direction**: 
    * **Anthony Bordg** (team lead): PI responsible for the original ideation, conceptualization, and AlphaGeometry-specific domain expertise.

* **Formalization & Support Team**:  
    * **Farzad Jafarrahmani** (research engineer): core formalization.
    * **Nathan Corbyn** (PhD student) & **Pablo Donato** (postdoc): inputs on dependent types for signatures.
    * **Elsa Lubek** (intern): code review.
    * **mathlib**: This project relies extensively on mathlib4. In particular, the `CategoryTheory` library—developed by Kim Morrison and others—was foundational to the formalization of `Semantics.lean`. 

## License
This project is licensed under the **Apache License 2.0**. See the [LICENSE](LICENSE) file for the full license text.