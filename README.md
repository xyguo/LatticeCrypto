# Intro
This project aims to implement fundamental lattice-based cryptography algorithms using Lean4. The goal is **NOT** to create highly efficient algorithms that can be used in practice; Instead, this library is mainly for pedagogical purpose: we want to provide readable implementations whose security can be _formally verified_ using Lean's proof system.

## Dependencies and Tools

- **Mathlib4 (v4.24.0)**: For basic mathematical structures and theorems
- **LLMs**: The project is impossible without the help of ChatGPT/Gemini and Aristotle. 
  - As a result, many Lean proofs may look way complicated than they should be: this usually means they are "vibe proved" by LLMs: But what really matters is the statement of the theorems. As long as the statement is correct, we are good.

# Project Outline

## Phase 1: Mathematical Foundations

### 1.1 Basic Lattice Theory
- **Module**: `LatticeCrypto.Foundations.Lattice`
- [X] Lattice definition and properties
- [X] Basis representation and linear independence
- [X] Lattice operations (shift, scaling)
- [X] Related structures (coset, dual lattice)
- [X] Fundamental lattice parameters (fundamental domain, determinant)
- [X] Successive minima and the Minkowski's First and Second Theorems

### 1.2 Major analytic tools
- **Module**: `LatticeCrypto.Foundations.Lattice`
- [X] Discrete Gaussian
  - [ ] Probability: common distributions, expectation, concentration inequalities (Markov/Chebyshev/Chernoff)
  - [X] Fourier transform, FFT, Poisson's Summation Formula
- [X] Banasczyk's transference theorem
- [X] Smoothing parameter

### 1.3 Lattice Algorithms
- **Module**: `LatticeCrypto.Foundations.Algorithms`
- [X] ~~Gram-Schmidt orthogonalization~~ (using Mathlib version)
- [ ] LLL (Lenstra-Lenstra-Lovász) lattice reduction algorithm
- [ ] BKZ (Block Korkine-Zolotarev) algorithm basics
- [ ] Babai's Nearest Plane
- [ ] Discrete Gaussian sampling

### 1.4 Lattice Problems and Hardness
- **Module**: `LatticeCrypto.Foundations.Hardness`
- [ ] Computation complexity: asymptotics, TM, circuits (?), P, NP, BPP, EXP, P/poly (?), reduction.
- [ ] Definition of hard lattice problems (SVP, CVP, GapSVP, GapCVP, SIVP)
- [ ] Reduction between problems (?)
- [ ] Formal statements of hardness assumptions (?)

## Phase 2: Cryptographic Primitives

### 2.1 Short Integer Solution (SIS)
- **Module**: `LatticeCrypto.Primitives.SIS`
- [ ] SIS problem definition
- [ ] CRHF from SIS

### 2.2 Learning With Errors (LWE)
- **Module**: `LatticeCrypto.Primitives.LWE`
- [ ] LWE problem definition and variants
- [ ] Error distribution (discrete Gaussian)
- [ ] PKE from LWE

### 2.3 Ring/Module-SIS and Ring/Module-LWE
- **Module**: `LatticeCrypto.Primitives.RingLWE`, `LatticeCrypto.Primitives.ModuleLWE`, `LatticeCrypto.Primitives.RingSIS`, `LatticeCrypto.Primitives.ModuleSIS`
- [ ] Polynomial rings and ideals
- [ ] Ring-LWE/SIS problem definition
- [ ] Module-LWE/SIS generalization

## Phase 3: Worst-case to Average-case Reductions

### 3.1 SIS ([Micciancio-Regev03])

### 3.2 LWE ([Regev05])

### 3.3 Ring-LWE/SIS ([LPR12])

### 3.4 Module-LWE/SIS ([LS12])