#;#;
#<<END
TR opt: flfma.rkt 3:0 (flfma 1.0000000000000002 0.9999999999999998 -1.0) -- ternary float
TR opt: flfma.rkt 4:0 (flfma 1e+308 2.0 -1e+308) -- ternary float
TR opt: flfma.rkt 5:0 (flfma 5e-324 0.5 5e-324) -- ternary float
END
#<<END
-4.930380657631324e-32
1e+308
1e-323

END
#lang typed/racket/base
#:optimize
#reader typed-racket-test/optimizer/reset-port

(require racket/flonum)
(flfma 1.0000000000000002 0.9999999999999998 -1.0)
(flfma 1e308 2.0 -1e308)
(flfma 5e-324 0.5 5e-324)
