; Tainted flow from a2 to b2.
(define a #t)
(define a2 (source a))
(define b (list (lambda (x) x)))
(define (set-b) (set-car! b (lambda (x) #f)))
(define res
  (begin
    (if a2 (set-b))
    ((car b) 10)))
(define b2 (sink res))