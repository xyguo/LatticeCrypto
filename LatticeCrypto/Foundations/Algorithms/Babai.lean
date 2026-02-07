-- Re-export all submodules
import LatticeCrypto.Foundations.Algorithms.Babai.Algorithm
import LatticeCrypto.Foundations.Algorithms.Babai.Correctness
import LatticeCrypto.Foundations.Algorithms.Babai.Quality
/-!
# LLL Basis Reduction Algorithm

This module provides the implementation and analysis of the Lenstra-Lenstra-Lovász (LLL)
lattice basis reduction algorithm. The code is organized into several submodules:

- **Algorithm**: Algorithm implementations
- **Correctness**: Proofs that the algorithm indeed find a lattice point
- **Quality**: Approximation bounds and quality guarantees

## References

- László Babai. On Lovász' lattice reduction and the nearest lattice point problem.
- Regev: Lecture notes on lattice-based cryptography: [Lecture 3: CVP Algorithm](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/cvp.pdf)
- Noah Stephens-Davidowitz: Lecture notes on Lattice Mini Course: [Lecture 5: CVP and Babai’s Algorithm](https://www.noahsd.com/mini_lattices/05__babai.pdf)
-/
