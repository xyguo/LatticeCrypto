# Intro
This project aims to implement fundamental lattice-based cryptography algorithms using Lean4. The goal is **NOT** to create highly efficient algorithms that can be used in practice; Instead, this library is mainly for pedagogical purpose: we want to provide readable implementations whose security can be _formally verified_ using Lean's proof system.

# Project Outline

## Phase 1: Mathematical Foundations

### 1.0 Basic Mathematical Tools

- Basic inequalities: Cauchy-schwartz, Holder
- Computation complexity: asymptotics, TM, circuits (?), P, NP, BPP, EXP, P/poly (?), reduction.
- Probability: common distributions, expectation, concentration inequalities (Markov/Chebyshev/Chernoff)
- Fourier transform, FFT, Poisson's Summation Formula
- Discrete Gaussian, sampling (Babai's Nearest Plane)

### 1.1 Basic Lattice Theory
- **Module**: `Lattice.Foundations.Basic`
- Lattice definition and properties
- Basis representation and linear independence
- Lattice operations (addition, scaling)
- Fundamental lattice parameters (determinant, successive minima)

### 1.2 Lattice Algorithms
- **Module**: `Lattice.Foundations.Algorithms`
- Gram-Schmidt orthogonalization
- LLL (Lenstra-Lenstra-Lovász) lattice reduction algorithm
- BKZ (Block Korkine-Zolotarev) algorithm basics
- Shortest vector problem (SVP) and closest vector problem (CVP)

### 1.3 Lattice Problems and Hardness
- **Module**: `Lattice.Foundations.Hardness`
- Definition of hard lattice problems (SVP, CVP, SIS, LWE)
- Reduction between problems
- Worst-case to average-case reductions
- Formal statements of hardness assumptions

## Phase 2: Cryptographic Primitives

### 2.1 Learning With Errors (LWE)
- **Module**: `Lattice.Primitives.LWE`
- LWE problem definition and variants
- Error distribution (discrete Gaussian)
- LWE-based encryption schemes
- Security proofs and reductions

### 2.2 Short Integer Solution (SIS)
- **Module**: `Lattice.Primitives.SIS`
- SIS problem definition
- Hash functions from SIS
- Digital signatures from SIS
- Collision resistance proofs

### 2.3 Ring-LWE and Module-LWE
- **Module**: `Lattice.Primitives.RingLWE`
- Polynomial rings and ideals
- Ring-LWE problem definition
- Module-LWE generalization
- Efficiency considerations

## Phase 3: Cryptographic Schemes

### 3.1 Public Key Encryption
- **Module**: `Lattice.Schemes.PKE`
- Regev's LWE-based encryption
- Ring-LWE based schemes (e.g., New Hope style)
- Key generation, encryption, decryption algorithms
- IND-CPA and IND-CCA security proofs

### 3.2 Digital Signatures
- **Module**: `Lattice.Schemes.Signatures`
- Hash-and-sign signatures from SIS
- Fiat-Shamir with aborts (e.g., Dilithium style)
- Signature verification and security analysis
- Existential unforgeability proofs

### 3.3 Key Exchange
- **Module**: `Lattice.Schemes.KeyExchange`
- Diffie-Hellman style key exchange
- Ring-LWE based key exchange protocols
- Error reconciliation mechanisms
- Forward secrecy analysis

## Phase 4: Advanced Constructions

### 4.1 Homomorphic Encryption
- **Module**: `Lattice.Advanced.FHE`
- Somewhat homomorphic encryption (SWHE)
- Bootstrapping techniques
- Fully homomorphic encryption (FHE) basics
- Circuit evaluation and noise management

### 4.2 Zero-Knowledge Proofs
- **Module**: `Lattice.Advanced.ZKProofs`
- Lattice-based commitment schemes
- Zero-knowledge proofs for lattice relations
- Bulletproofs-style constructions
- Soundness and zero-knowledge properties

### 4.3 Post-Quantum Security
- **Module**: `Lattice.Advanced.PostQuantum`
- Quantum algorithms and lattice problems
- NIST post-quantum standardization
- Concrete security parameters
- Implementation considerations

## Phase 5: Utilities and Examples

### 5.1 Utility Functions
- **Module**: `Lattice.Utils`
- Random sampling (Gaussian, uniform)
- Matrix and vector operations
- Polynomial arithmetic
- Serialization helpers

### 5.2 Security Proofs Framework
- **Module**: `Lattice.Proofs`
- Generic proof templates
- Game-based security definitions
- Reduction framework
- Automation tactics for common proof patterns

### 5.3 Examples and Tutorials
- **Module**: `Lattice.Examples`
- Complete worked examples
- Interactive tutorials
- Performance benchmarks
- Educational demonstrations

## Implementation Philosophy

1. **Formal Verification First**: Every cryptographic claim should be formally verified in Lean
2. **Readable Code**: Prioritize clarity over performance optimization
3. **Educational Value**: Include extensive documentation and examples
4. **Modular Design**: Each component should be independently understandable
5. **Security Focus**: Emphasize provable security over practical efficiency

## Dependencies and Tools

- **Mathlib**: For basic mathematical structures and theorems
- **Lean 4**: For formal verification and implementation
- **Custom Tactics**: For automating common cryptographic proof patterns
- **Documentation**: Extensive inline documentation and examples

