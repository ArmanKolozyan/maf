(define (factorial n)
  (if (= n 0)
      1
      (* n (factorial (- n 1)))))

(define (power-of-two n)
  (if (= n 0)
      1
      (* 2 (power-of-two (- n 1)))))

(define (sum-of-digits n)
  (if (< n 10)
      n
      (+ (remainder n 10) (sum-of-digits (quotient n 10)))))

(define (fibonacci n)
  (cond ((= n 0) 0)
        ((= n 1) 1)
        (else (+ (fibonacci (- n 1)) (fibonacci (- n 2))))))

(define (print-natural-numbers n)
  (define (print-helper current)
    (if (> current n)
        'done
        (begin
          (display current)
          (newline)
          (print-helper (+ current 1)))))
  (print-helper 1))

(define (calculate-gcd a b)
  (if (= b 0)
      a
      (calculate-gcd b (remainder a b))))

(define (is-prime n)
  (define (check-prime current)
    (cond ((< current 2) #f)
          ((= current n) #t)
          ((= (remainder n current) 0) #f)
          (else (check-prime (+ current 1)))))
  (check-prime 2))

(define (print-primes-between start end)
  (define (print-helper current)
    (if (> current end)
        'done
        (begin
          (if (is-prime current)
              (begin
                (display current)
                (newline)))
          (print-helper (+ current 1)))))
  (print-helper start))

(define (main)
  (display "Factorial of 5: ")
  (display (factorial 5))
  (newline)

  (display "Power of two, 5th term: ")
  (display (power-of-two 5))
  (newline)

  (display "Sum of digits of 123: ")
  (display (sum-of-digits 123))
  (newline)

  (display "Fibonacci of 10th term: ")
  (display (fibonacci 10))
  (newline)

  (display "Printing natural numbers up to 10:")
  (newline)
  (print-natural-numbers 10)

  (display "GCD of 24 and 36: ")
  (display (calculate-gcd 24 36))
  (newline)

  (display "Is 17 prime? ")
  (display (is-prime 17))
  (newline)

  (display "Printing prime numbers between 1 and 20:")
  (newline)
  (print-primes-between 1 20))

(main)
