; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Explicit updates:
;   mix antigen cover --record-new-coverage-baseline
;   mix antigen cover --refresh-existing-coverage-baseline (no record changes or floor reductions)
(cover-floor Cure.Core.Certificate 186 210)
(cover-floor Cure.Core.Conv 81 93)
(cover-floor Cure.Core.Eval 100 118)
(cover-floor Cure.Core.Inductive 108 152)
(cover-floor Cure.Core.Kernel 555 685)
(cover-floor Cure.Core.Normalise 115 124)
(cover-floor Cure.Core.Quote 35 41)
(cover-floor Cure.Core.Serialize 115 188)
(cover-total 1295 1611)
