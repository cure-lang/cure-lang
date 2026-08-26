; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of
; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop
; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:
;   mix antigen cover --record-new-coverage-baseline
(cover-floor Cure.Core.Certificate 186 205)
(cover-floor Cure.Core.Conv 81 87)
(cover-floor Cure.Core.Eval 100 109)
(cover-floor Cure.Core.Inductive 108 141)
(cover-floor Cure.Core.Kernel 555 684)
(cover-floor Cure.Core.Normalise 115 120)
(cover-floor Cure.Core.Quote 35 36)
(cover-floor Cure.Core.Serialize 115 127)
(cover-total 1295 1509)
