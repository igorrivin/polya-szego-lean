# Polya-Szego Lean Formalizations

Machine-verified Lean 4 proofs of problems from Polya and Szego's *Problems and Theorems in Analysis I* (1925).

## Overview

This repository contains:
- **318 LLM-generated formalizations** of Polya-Szego problems
- **80 verified proofs** produced by [Aristotle](https://aristotle.so)
- Metadata linking problems to their Aristotle verification runs

## Results

| Metric | Count |
|--------|-------|
| Problems formalized | 318 |
| Submitted to Aristotle | 80 |
| Successfully verified | 80 (100%) |
| Verification ongoing | 238 |

## Directory Structure

```
polya-szego-lean/
├── original/           # LLM-generated Lean 4 formalizations (DeepSeek V3.2)
│   └── Problem_*.lean
├── verified/           # Aristotle-verified complete proofs
│   └── *-output.lean
├── metadata/           # Submission tracking
│   └── submissions.json
└── README.md
```

## Example

### Problem 112: Complex Exponential Identity

**Original problem:** Prove that Re(a* · e^{iφ}) = |a| cos(φ - arg(a))

**Verified proof (Aristotle):**
```lean
theorem problem_112_part_one (a : ℂ) (φ : ℝ) :
    (star a * Complex.exp (Complex.I * φ)).re =
    ‖a‖ * Real.cos (φ - Complex.arg a) := by
  norm_num [Complex.exp_re, Complex.exp_im, Real.cos_sub]
  rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg]
  ring
```

## Requirements

- Lean 4 (v4.24.0)
- Mathlib (commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7)

## Pipeline

1. **OCR Extraction:** Problems extracted from PDF using Nougat/Gemini
2. **LLM Formalization:** DeepSeek V3.2 generates Lean 4 statements
3. **Aristotle Verification:** Automated proof synthesis and error correction
4. **Human Review:** Spot-checking for semantic correctness

## Related Work

- [Initial Benchmark Report](https://igorrivin.github.io/research/polya-szego-benchmark/)
- [Aristotle Update](https://igorrivin.github.io/research/polya-szego-aristotle/)

## Citation

```bibtex
@misc{rivin2026polyaszego,
  author = {Rivin, Igor},
  title = {Polya-Szego Lean Formalizations},
  year = {2026},
  publisher = {GitHub},
  url = {https://github.com/igorrivin/polya-szego-lean}
}
```

## License

MIT License. The original Polya-Szego problems are in the public domain.

## Acknowledgments

- [Aristotle](https://aristotle.so) for automated proof verification
- [Mathlib](https://github.com/leanprover-community/mathlib4) community
- DeepSeek for V3.2 model access
