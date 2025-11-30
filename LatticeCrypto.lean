-- This module serves as the root of the `LatticeCrypto` library.
-- Import modules here that should be built as part of the library.

-- Phase 1: Mathematical Foundations
import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Algorithms
import LatticeCrypto.Foundations.Hardness

-- Phase 2: Cryptographic Primitives
import LatticeCrypto.Primitives.LWE
import LatticeCrypto.Primitives.SIS
import LatticeCrypto.Primitives.RingLWE

-- Phase 3: Cryptographic Schemes
import LatticeCrypto.Schemes.PKE
import LatticeCrypto.Schemes.Signatures
import LatticeCrypto.Schemes.KeyExchange

-- Phase 4: Advanced Constructions
import LatticeCrypto.Advanced.FHE
import LatticeCrypto.Advanced.ZKProofs
import LatticeCrypto.Advanced.PostQuantum
