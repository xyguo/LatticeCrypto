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
- **Matrix**: Matrix-based formulation of size reduction
- **Algorithm**: Algorithm implementations
- **Correctness**: Proofs that the algorithm preserves the lattice
- **Quality**: Approximation bounds and quality guarantees
- **Runtime**: Complexity analysis and iteration bounds

## References

- Lenstra, Lenstra, Lovász: "Factoring polynomials with rational coefficients"
- Regev: Lecture notes on lattice-based cryptography
- Peikert: Lecture notes on lattices in cryptography
-/
