# Uniqueness in Zhang's Camera Calibration

A Lean 4 and Mathlib formalization for 21-321 (Fall 2026), of a uniqueness result behind
Zhang's camera calibration method: three views whose plane normals are pairwise
non-parallel determine camera intrinsics uniquely.

The main theorem is `CameraCalibration.zhang_intrinsics_unique` in
[`CameraCalibration/Main.lean`](CameraCalibration/Main.lean).

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
lake build
```

## Contents

- [`CameraCalibration/`](CameraCalibration): the Lean code
- [`report/report.pdf`](report/report.pdf): the report, including the proof and source code for the typesetting
- [`AI_USE.md`](AI_USE.md): AI-use statement
- [`COLLABORATION.md`](COLLABORATION.md): collaboration statement

## Reference

Z. Zhang, "A flexible new technique for camera calibration," *IEEE Transactions on Pattern
Analysis and Machine Intelligence*, 22(11):1330–1334, 2000.
