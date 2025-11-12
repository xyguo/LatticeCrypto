-- This module serves as the root of the `Lattice` library.
-- Import modules here that should be built as part of the library.

-- Phase 1: Mathematical Foundations
import Lattice.Foundations.Basic
import Lattice.Foundations.Algorithms
import Lattice.Foundations.Hardness

-- Phase 2: Cryptographic Primitives
import Lattice.Primitives.LWE
import Lattice.Primitives.SIS
import Lattice.Primitives.RingLWE

-- Phase 3: Cryptographic Schemes
import Lattice.Schemes.PKE
import Lattice.Schemes.Signatures
import Lattice.Schemes.KeyExchange

-- Phase 4: Advanced Constructions
import Lattice.Advanced.FHE
import Lattice.Advanced.ZKProofs
import Lattice.Advanced.PostQuantum
