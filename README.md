# Intro
This project aims to implement fundamental lattice-based cryptography algorithms using Lean4. The goal is **NOT** to create highly efficient algorithms that can be used in practice; Instead, this library is mainly for pedagogical purpose: we want to provide readable implementations whose security can be _formally verified_ using Lean's proof system.

## Dependencies and Tools

- **Mathlib4 (v4.24.0)**: For basic mathematical structures and theorems
- **LLMs**: The project is impossible without the help of ChatGPT/Gemini and Aristotle. 
  - As a result, many Lean proofs may look way complicated than they should be: this usually means they are "vibe proved" by LLMs: But what really matters is the statement of the theorems. As long as the statement is correct, we are good.

# Project Outline

## Phase 1: Mathematical Foundations

### 1.1 Basic Lattice Theory
- **Module**: `Lattice.Foundations.Lattice`
- [X] Lattice definition and properties
- [X] Basis representation and linear independence
- [ ] Lattice operations (shift, scaling)
- [ ] Related structures (coset, fundamental domain, dual lattice)
- [ ] Fundamental lattice parameters (determinant, successive minima)

### 1.2 Lattice Algorithms
- **Module**: `Lattice.Foundations.Algorithms`
- [ ] Gram-Schmidt orthogonalization
- [ ] LLL (Lenstra-Lenstra-Lovász) lattice reduction algorithm
- [ ] BKZ (Block Korkine-Zolotarev) algorithm basics
- [ ] Babai's Nearest Plane

### 1.3 Basic Mathematical Tools
- **Module**: `Lattice.Utils`
- [ ] Computation complexity: asymptotics, TM, circuits (?), P, NP, BPP, EXP, P/poly (?), reduction.
- [ ] Discrete Gaussian, sampling
- [ ] Adapting existing Mathlib definitions
  - [ ] Basic inequalities: Cauchy-schwartz, Holder
  - [ ] Probability: common distributions, expectation, concentration inequalities (Markov/Chebyshev/Chernoff)
  - [ ] Fourier transform, FFT, Poisson's Summation Formula
  - [ ] Polynomial arithmetic

### 1.3 Lattice Problems and Hardness
- **Module**: `Lattice.Foundations.Hardness`
- [ ] Definition of hard lattice problems (SVP, CVP, GapSVP, GapCVP, SIVP)
- [ ] Reduction between problems (?)
- [ ] Formal statements of hardness assumptions (?)

## Phase 2: Cryptographic Primitives

### 2.1 Learning With Errors (LWE)
- **Module**: `Lattice.Primitives.LWE`
- [ ] LWE problem definition and variants
- [ ] Error distribution (discrete Gaussian)
- [ ] Worst-case to average-case reductions ([Regev05])
- [ ] PKE from LWE

### 2.2 Short Integer Solution (SIS)
- **Module**: `Lattice.Primitives.SIS`
- [ ] SIS problem definition
- [ ] Worst-case to average-case reductions ([Micciancio-Regev03])
- [ ] CRHF from SIS

### 2.3 Ring-LWE and Module-LWE
- **Module**: `Lattice.Primitives.RingLWE`
- [ ] Polynomial rings and ideals
- [ ] Ring-LWE problem definition
- [ ] Module-LWE generalization
- [ ] Worst-case to average-case reductions ([LPR12, LS12])

