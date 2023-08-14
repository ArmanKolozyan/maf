(define (sign number)
  (cond ((zero? number) 0)
        ((> number 0) 1)
        (else -1)))

(define (divides? deler deeltal)
  (= 0  (modulo deeltal deler)))

(define (leap-year? year)
  (if (divides? 4 year)
      (if (divides? 100 year)
          (divides? 400 year)
          #t)
      #f))

(define (leap-year2? year)
  (cond ((divides? 400 year) #t)
        ((divides? 100 year) #f)
        ((divides? 4 year) #t)
        (else #f)))

(define (leap-year3? year)
 (if (divides? 400 year)
     #t
     (if (divides? 100 year)
         #f
         (divides? 4 year))))


(define (leap-year4? year)
 (or (divides? 400 year)
          (not (divides? 100 year))))type of ) Consequently, we can create aconsdefine (request-reply tag other-contracts)  other-contracts)))
                                                                                (ensures/c (list funct(message/c 'ion that constructs a contra

                                                                                                                 ct for this type of interactionstag (list actor?))
\begin{minted}{scheme}\end{minted}


(and (not (or (leap-year? 1989)
              (leap-year? 1900)))
     (leap-year? 2000)
     (= -1 (sign -5))
     (= 1 (sign 17.28)`request-reply'' patterns.
     @
     (= 0 (sign 0)))
