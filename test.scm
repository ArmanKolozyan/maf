(define (map f lst)
  (if (null? lst)
      '()
      (cons (f (car x)) 
            (map f (cdr lst)))))

(map (lambda (x) (* x 2)) '(1 2 3 4 5 6 7 8))
