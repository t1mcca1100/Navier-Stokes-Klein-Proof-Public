# Navier-Stokes Global Regularity via Klein Topology

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17967348.svg)](https://doi.org/10.5281/zenodo.17967348)

**Author:** Timothy McCall  
**Date:** December 17, 2025  
**License:** CC-BY 4.0

## Overview

Lean 4 formalization of the core topological theorem for Navier-Stokes global regularity on T³.

**Main Result:** For Klein-compatible velocity fields V, the total vortex stretching vanishes:
```
∫ ω · V dμ = 0
```

## Verification Status

| Component | Status |
|-----------|--------|
| Theorems proven | 12 |
| Lemmas proven | 2 |
| Main theorem | 1 |
| Axioms | 2 (curl, curl_parity) |
| Sorry | **0** |

## Compile
```bash
lake env lean NS_Klein_Core_v3_-_DOI__10_5281_17967348.lean
```

## Paper

Full 32-page paper: [DOI 10.5281/zenodo.17967348](https://doi.org/10.5281/zenodo.17967348)

## Patent Notice

US Provisional Patent Application No. 63/939,013 and continuations.

## License

[CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/)
