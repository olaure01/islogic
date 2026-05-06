# IS Logic

Lambek calculus and Intersection Subtyping Logic (IS)

Formalization of the results presented at [LICS 2016](https://doi.org/10.4230/LIPIcs.LICS.2026.12) (see [links between results in the paper and Rocq statements](references.txt)).

## Installation

Requires [OLlibs v2.1.1](https://github.com/olaure01/ollibs) (add-ons for the standard library): [see installation instructions](https://github.com/olaure01/ollibs/blob/master/README.md).

1. [install OLlibs v2.1.1](https://github.com/olaure01/ollibs/blob/master/README.md)
2. build

        $ ./configure
        $ make

(working with the Rocq prover version 9.1).


## Contents

### Lambek & IS

* `lformulas.v`:
  Lambek formulas without ⊗ and ⊸

* `lambek_is.v`:
  L and IS (through parameter),
  cut and Scut eliminations (through parameter)

* `ish.v`:
  ISₕ


### Negative fragments

* `nformulas.v`:
  negative formulas

* `nlambek_neg.v`:
  nL and nLʳᵉᵛ

* `nis.v`:
  nIS, nIS₁ and nIS₁ʳᵉᵛ


### Polymorphic fragments

* `fformulas.v`:
  formulas of system F

* `fis.v`:
  ∀IS, ∀IS₁ and ∀IS₁ʳᵉᵛ


### Intersection types

* `iformulas.v`:
  intersection formulas,
  β and η conditions

* `bcd.v`:
  BCD subtyping relation on intersection formulas
    with a parameter `lax` for inequation axioms indexed by atoms

* `bcd_prop.v`:
  β condition

* `iis1.v`:
  ∩IS₁

* `ilambek.v`:
  ∩L

* `equivalences.v`:
  Girard's translation from ∩IS₁ to L (correctness & completeness)

* `iis1_prop.v`:
  ∩IS₁ direct cut elimination
  β condition

* `iis1r.v`:
  ∩IS₁ʳ and proof-search algorithm

* `iish.v`:
  ∩ISₕ

* `relevant.v`:
  logic B+ (with Ω),
  equivalences between B+ and ∩ISₕ

### Models of Eta

* `scott.v`:
  ∩IS Scott

* `park.v`:
  ∩IS Park
