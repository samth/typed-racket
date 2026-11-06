#;#;
#<<END
TR opt: c99-flonums.rkt 3:0 (fllog1p 0.0) -- unary float
TR opt: c99-flonums.rkt 4:0 (flexpm1 0.0) -- unary float
TR opt: c99-flonums.rkt 5:0 (flsinh 0.0) -- unary float
TR opt: c99-flonums.rkt 6:0 (flcosh 0.0) -- unary float
TR opt: c99-flonums.rkt 7:0 (fltanh 0.0) -- unary float
TR opt: c99-flonums.rkt 8:0 (flasinh 0.0) -- unary float
TR opt: c99-flonums.rkt 9:0 (flacosh 1.0) -- unary float
TR opt: c99-flonums.rkt 10:0 (flatanh 0.0) -- unary float
TR opt: c99-flonums.rkt 11:0 (fllog2 2.0) -- unary float
TR opt: c99-flonums.rkt 12:0 (flexp2 0.0) -- unary float
TR opt: c99-flonums.rkt 13:0 (flnextafter 0.0 1.0) -- binary float
END
#<<END
0.0
0.0
0.0
1.0
0.0
0.0
0.0
0.0
1.0
1.0
5e-324

END
#lang typed/racket/base
#:optimize
#reader typed-racket-test/optimizer/reset-port

(require racket/flonum)
(fllog1p 0.0)
(flexpm1 0.0)
(flsinh 0.0)
(flcosh 0.0)
(fltanh 0.0)
(flasinh 0.0)
(flacosh 1.0)
(flatanh 0.0)
(fllog2 2.0)
(flexp2 0.0)
(flnextafter 0.0 1.0)
