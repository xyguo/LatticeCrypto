-- Re-export all submodules
import LatticeCrypto.Foundations.Algorithms.LLL.Defs
import LatticeCrypto.Foundations.Algorithms.LLL.Algorithm
import LatticeCrypto.Foundations.Algorithms.LLL.Correctness
import LatticeCrypto.Foundations.Algorithms.LLL.Quality
import LatticeCrypto.Foundations.Algorithms.LLL.Runtime
/-!
# LLL Basis Reduction Algorithm

This module provides the implementation and analysis of the Lenstra-Lenstra-Lovász (LLL)
lattice basis reduction algorithm. The code is organized into several submodules:

- **Defs**: Core definitions (Gram-Schmidt, LLL predicates, parameters)
- **Algorithm**: Algorithm implementations
- **Correctness**: Proofs that the algorithm preserves the lattice
- **Quality**: Approximation bounds and quality guarantees
- **Runtime**: Complexity analysis and iteration bounds

## References

- Lenstra, Lenstra, Lovász: "Factoring polynomials with rational coefficients"
- Regev: Lecture notes on lattice-based cryptography: [Lecture 2: LLL Algorithm](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/lll.pdf)
- Peikert: Lecture notes on Lattices in cryptography: [Lecture 3: LLL Algorithm](https://github.com/cpeikert/LatticesInCryptography/blob/main/lec03%20-%20LLL%20Algorithm.pdf)
-/
