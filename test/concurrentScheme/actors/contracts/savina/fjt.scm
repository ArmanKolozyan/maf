;; Adapted from Savina benchmarks ("Fork Join (throughput)" benchmark, coming from JGF)
(define N (int-top))
(define A (int-top))
(define (perform-computation theta)
  (let ((sint (+ 1 theta)))
    (* sint sint)))
(define throughput-actor
  (actor "throughput" (processed)
           (message ()
                    (perform-computation 37.2)
                    (if (= (+ processed 1) N)
                        (terminate)
                        (become throughput-actor (+ processed 1))))))
(define build-vector (lambda (n f)
                       (letrec ((v (make-vector n #f))
                                (loop (lambda (i)
                                        (if (< i n)
                                            (begin
                                              (vector-set! v i (f i))
                                              (loop (+ i 1)))
                                            v))))
                         (loop 0))))
(define actors (build-vector A (lambda (i) (create throughput-actor 0))))
(define vector-foreach (lambda (f v)
                         (letrec ((loop (lambda (i)
                                          (if (< i (vector-length v))
                                              (begin
                                                (f (vector-ref v i))
                                                (loop (+ i 1)))
                                              'done))))
                           (loop 0))))
(define loop (lambda (n)
               (if (= n N)
                   'done
                   (begin
                     (vector-foreach (lambda (a) (send a message)) actors)
                     (loop (+ n 1))))))
(loop 0)