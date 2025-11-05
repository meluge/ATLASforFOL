# First-Order Quantified Separator (Alloy)

Synthesize **minimal** first-order formulas that separate positive/negative relational examples by encoding FOL semantics in **Alloy** and optimizing with **Max-SAT**. Supports **syntactic constraints** (quantifier prefix, operator set, size budget).

## Highlights
- Quantified FOL over finite structures (many-sorted friendly).
- Syntactic constraints: e.g., prefix `∃∀`, allowed ops `{∧, ¬}`, size/weight budgets.
- Returns *minimal* separators (readable, compact).

## Examples (schematic)
- Unconstrained: `∀x ∃y. E(y, x)`
- With prefix `∃∀`: `∃x ∀y. ¬E(x, y)`

## Status
WIP — setup & CLI docs coming soon.

## Cite
```bibtex
@inproceedings{an2025foqsep,
  title     = {First-Order Quantified Separator in Alloy Analyzer},
  author    = {One An},
  booktitle = {Proc. ASE},
  year      = {2025},
  note      = {Short paper}
}
