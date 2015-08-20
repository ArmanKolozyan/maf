;; Expected result: 1
(define (square x) (* x x))
(define (modulo-power base exp n)
  (if (= exp 0)
      1
      (if (odd? exp)
          (modulo (* base (modulo-power base (- exp 1) n)) n)
          (modulo (square (modulo-power base (/ exp 2) n)) n))))
(define (is-trivial-composite? n)
  (or (= (modulo n 2) 0)
      (= (modulo n 3) 0)
      (= (modulo n 5) 0)
      (= (modulo n 7) 0)
      (= (modulo n 11) 0)
      (= (modulo n 13) 0)
      (= (modulo n 17) 0)
      (= (modulo n 19) 0)
      (= (modulo n 23) 0)))
(define (is-fermat-prime? n iterations)
  (or (<= iterations 0)
      (let* ((byte-size (ceiling (/ (log n) (log 2))))
             (a (random byte-size)))
        (if (= (modulo-power a (- n 1) n) 1)
            (is-fermat-prime? n (- iterations 1))
            #f))))
(define (generate-fermat-prime byte-size iterations)
  (let ((n (random byte-size)))
    (if
     (and (not (is-trivial-composite? n)) (is-fermat-prime? n iterations))
     n
     (generate-fermat-prime byte-size iterations))))
(define iterations 10)
(define byte-size 15)
(generate-fermat-prime byte-size iterations)
