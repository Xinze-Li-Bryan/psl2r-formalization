# Formalizing PSL(2,ℝ) and Hyperbolic Geometry in Lean 4

This project formalizes the fundamental equivalence in hyperbolic geometry:

$$T^1\mathbb{H} \cong \mathrm{PSL}(2,\mathbb{R}) \cong \mathrm{Isom}^+(\mathbb{H}^2)$$

where:
- $T^1\mathbb{H}$ is the unit tangent bundle of the hyperbolic plane
- $\mathrm{PSL}(2,\mathbb{R}) = \mathrm{SL}(2,\mathbb{R})/\{\pm I\}$ is the projective special linear group
- $\mathrm{Isom}^+(\mathbb{H}^2)$ is the group of orientation-preserving isometries of the hyperbolic plane

## Project Status

🚧 **Under Development** 🚧

This is an active formalization project building on Lean 4 and Mathlib4.

## What's Already in Mathlib4

Mathlib4 provides strong foundations for this project:

- **Upper Half-Plane Model** (`Mathlib.Analysis.Complex.UpperHalfPlane.*`)
  - Definition of $\mathbb{H} = \{z \in \mathbb{C} \mid \mathrm{Im}(z) > 0\}$
  - Poincaré (hyperbolic) metric
  - Complete metric space structure
  
- **Special Linear Group** (`Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`)
  - Definition of $\mathrm{SL}(n,R)$
  - Group structure and properties
  
- **Isometric Action** (`UpperHalfPlane.instIsIsometricSMulSpecialLinearGroupFinOfNatNatReal`)
  - Theorem: $\mathrm{SL}(2,\mathbb{R})$ acts on $\mathbb{H}$ as isometries

## What We're Building

### Core Definitions
1. **Projective Special Linear Group**: $\mathrm{PSL}(2,\mathbb{R}) := \mathrm{SL}(2,\mathbb{R})/\{\pm I\}$
2. **Unit Tangent Bundle**: $T^1\mathbb{H} = \{(z,v) \in \mathbb{H} \times \mathbb{C} \mid |v| = \mathrm{Im}(z)\}$
3. **Orientation-Preserving Isometry Group**: $\mathrm{Isom}^+(\mathbb{H}^2)$

### Isomorphisms
1. **$\mathrm{PSL}(2,\mathbb{R}) \to \mathrm{Isom}^+(\mathbb{H}^2)$** via Möbius transformations:
   $$g = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \mapsto \left(z \mapsto \frac{az+b}{cz+d}\right)$$

2. **$\mathrm{PSL}(2,\mathbb{R}) \to T^1\mathbb{H}$** via frame action:
   $$g \mapsto \left(\frac{ai+b}{ci+d}, \frac{1}{(ci+d)^2}\right)$$

3. **$T^1\mathbb{H} \to \mathrm{Isom}^+(\mathbb{H}^2)$** via unique isometry sending base frame to given frame

## Project Structure

```
.
├── PSL2R/                    # Main Lean source files
│   ├── Basic.lean           # Basic definitions
│   ├── PSL.lean             # PSL(2,R) definition and properties
│   ├── UnitTangentBundle.lean  # Unit tangent bundle
│   ├── IsometryGroup.lean   # Isometry group
│   └── Equivalence.lean     # Main equivalence theorems
├── blueprint/               # Mathematical blueprint
├── lakefile.toml           # Lake build configuration
└── README.md               # This file
```

## Installation

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
- [VS Code](https://code.visualstudio.com/) with [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Setup
```bash
# Clone the repository
git clone https://github.com/YOUR_USERNAME/psl2r-formalization.git
cd psl2r-formalization

# Build the project
lake exe cache get
lake build
```

## Contributing

Contributions are welcome! Please feel free to:
- Open issues for bugs or suggestions
- Submit pull requests
- Discuss mathematical approaches

## References

Key references for this formalization:
- Katok, S. *Fuchsian Groups*. University of Chicago Press, 1992.
- Thurston, W. *Three-Dimensional Geometry and Topology*. Princeton University Press, 1997.
- Ratcliffe, J. *Foundations of Hyperbolic Manifolds*. Springer, 2006.

## Acknowledgments

This project builds on the extensive [Mathlib4](https://github.com/leanprover-community/mathlib4) library.

## License

This project is licensed under the Apache License 2.0.