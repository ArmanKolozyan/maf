(define NumWorkers (int-top))
(define Threshold (int-top))

(define (build-vector n f)
  (letrec ((v (make-vector n #f))
           (loop (lambda (i)
                   (if (< i n)
                       (begin
                         (vector-set! v i (f i))
                         (loop (+ i 1)))
                       v))))
    (loop 0)))
(define (vector-foreach f v)
  (letrec ((loop (lambda (i)
                   (if (< i (vector-length v))
                       (begin
                         (f (vector-ref v i))
                         (loop (+ i 1)))
                       'done))))
    (loop 0)))
(define (append l m)
  (if (null? l)
      m
      (cons (car l) (append (cdr l) m))))
(define (for-each f l)
  (if (null? l)
      #t
      (if (pair? l)
          (begin (f (car l)) (for-each f (cdr l)))
          (error "Cannot for-each over a non-list"))))

(define master-actor
  (actor "master-actor" (workers num-workers-terminated num-work-sent num-work-completed)
           (work (target node)
                 (send (vector-ref workers (modulo num-work-sent NumWorkers)) work target node)
                 (become master-actor workers num-workers-terminated (+ num-work-sent 1) num-work-completed))
           (received ()
                     (if (= (+ num-work-completed 1) num-work-sent)
                         (vector-foreach (lambda (a) (send a stop)) workers)
                         #t)
                     (become master-actor workers num-workers-terminated num-work-sent (+ num-work-completed 1)))
           (done ()
                 (vector-foreach (lambda (a) (send a stop)) workers)
                 (become master-actor workers num-workers-terminated num-work-sent num-work-completed))
           (stop ()
                 (if (= (+ num-workers-terminated 1) NumWorkers)
                     (terminate)
                     (become master-actor workers (+ num-workers-terminated 1) num-work-sent num-work-completed)))))

(define MaxNeighbors (int-top))
;; represent full non-determinism
(define (neighbors node)
  (letrec ((loop (lambda (i acc)
                   (if (= i MaxNeighbors)
                       acc
                       (loop (+ i 1) (cons (int-top) acc))))))
    (loop 0 '())))

(define worker-actor
  (actor "worker-actor" (master id)
           (work (target node)
                 (letrec ((loop (lambda (queue nodes-processed)
                                  (if (or (null? queue) (= nodes-processed Threshold))
                                      (if (not (null? queue))
                                          (for-each (lambda (node) (send master work target node)) queue)
                                          #t)
                                      (let ((loop-node (car queue)))
                                        (if (member target (neighbors loop-node))
                                            (send master done)
                                            (loop (append queue (neighbors loop-node)) (+ nodes-processed 1))))))))
                   (loop (cons node '()) 0))
                 (send master received)
                 (become worker-actor master id))
           (stop ()
                 (send master stop)
                 (terminate))))

(define origin 0)
(define target 10)
(define master-actor-init
  (actor "master-actor-init" ()
           (start ()
                  (become master-actor (build-vector NumWorkers (lambda (i)
                                                                    (let ((w (create worker-actor a/self i)))
                                                                      (if (= i 0)
                                                                          (send w work target origin)
                                                                          #t)
                                                                      w)))
                            0 0 0))))
(define master
  (create master-actor-init))
(send master start)