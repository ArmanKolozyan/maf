package scalaam.test.language.scheme

import scalaam.language.scheme.{SchemeExp, SchemeLattice}
import scalaam.modular.ModAnalysis
import scalaam.modular.scheme.SchemeModFSemantics

object SchemePrimitiveBenchmarks {

  type Analysis = ModAnalysis[SchemeExp] with SchemeModFSemantics
  type V = (ModAnalysis[SchemeExp] with SchemeModFSemantics)#Value
  type A = (ModAnalysis[SchemeExp] with SchemeModFSemantics)#Addr
  type P = (ModAnalysis[SchemeExp] with SchemeModFSemantics)#Prim
  type Env = (ModAnalysis[SchemeExp] with SchemeModFSemantics)#Component
  type L = SchemeLattice[V, A, P, Env]

  val progs = List(
    "(eq? 'a 'a)",
    "(eq? (cons 'a '()) (cons 'a '()))",
    "(eq? (list 'a) (list 'a))",
    "(eq? '() '())",
    "(eq? car car)",
    "(let ((x '(a))) (eq? x x))",
    "(let ((x (make-vector 0 1))) (eq? x x))",
    "(let ((p (lambda (x) x))) (eq? p p))",
    "(equal? 'a 'a)",
    "(equal? '(a) '(a))",
    "(equal? '(a (b) c) '(a (b) c))",
    "(equal? \"abc\" \"abc\")",
    "(equal? 2 2)",
    "(equal? 1 2)",
    "(equal? #\\a #\\b)",
    "(equal? '(a b c) '(a b))",
    "(equal? (cons 'a (cons 'b (cons 'c '()))) '(a b c))",
    "(equal? '(a b c) '(a c b))",
    "(real? 3)",
    "(real? 1.5)",
    "(integer? 0)",
    "(integer? '())",
    "(number? 0)",
    "(number? -1)",
    "(number? 0.5)",
    "(number? '())",
    "(odd? 0)",
    "(odd? 1)",
    "(odd? 101)",
    //"(max 3 4)",
    //"(max 3.9 4)",
    //"(max 1)",
    //"(max 1 2 3 4 5 4 3 2 1)",
    //"(min 3 4)",
    //"(min 3 4.9)",
    //"(min 1)",
    //"(min 5 4 3 2 1 2 3 4 5)",
    "(+ 3 4)",
    "(+ 3)",
    "(+)",
    "(* 3 4)",
    "(* 4)",
    "(*)",
    "(- 3 4)",
    "(- 3 4 5)",
    "(- 3)",
    "(/ 4 2)",
    "(/ 1 2)",
    "(/ 1.0 1)",
    "(/ 1 1.0)",
    "(/ 4 2.0)",
    "(< 1 2)",
    "(< 2 1)",
    "(< 1 1)",
    "(< 2.0 2.1)",
    "(< 2.1 2.0)",
    "(<= 1 2)",
    "(<= 2 1)",
    "(<= 1 1)",
    "(<= 2.0 2.1)",
    "(<= 2.1 2.0)",
    "(> 1 2)",
    "(> 2 1)",
    "(> 1 1)",
    "(> 2.0 2.1)",
    "(> 2.1 2.0)",
    "(>= 1 2)",
    "(>= 2 1)",
    "(>= 1 1)",
    "(>= 2.0 2.1)",
    "(>= 2.1 2.0)",
    "(= 1 1)",
    "(= 2 1)",
    "(abs -7)",
    "(abs 7)",
    "(abs 0)",
    "(modulo 13 4)",
    "(modulo -13 4)",
    "(modulo 13 -4)",
    "(modulo -13 -4)",
    "(quotient 3 5)",
    "(quotient 4 2)",
    "(quotient -6 2)",
    "(remainder 13 4)",
    "(remainder -13 4)",
    "(remainder 13 -4)",
    "(remainder -13 -4)",
    "(expt 5 2)",
    "(expt 1 0)",
    "(expt 0 0)",
    "(ceiling -4.3)",
    "(ceiling 3.5)",
    "(floor -4.3)",
    "(floor 3.5)",
    "(floor 7)",
    "(sin 0)",
    "(asin 0)",
    "(cos 0)",
    "(acos 1)",
    "(tan 0)",
    "(< (- (tan 4) (/ (sin 4) (cos 4))) 0.0001)",
    "(atan 0)",
    "(sqrt 0)",
    "(sqrt 4)",
    "(sqrt 16)",
    "(sqrt 4.0)",
    "(log 1)",
    "(negative? 0)",
    "(negative? -1)",
    "(negative? 1)",
    "(positive? 0)",
    "(positive? -1)",
    "(positive? 1)",
    "(zero? 0)",
    "(zero? 1)",
    "(zero? -1)",
    "(even? 0)",
    "(even? 1)",
    "(even? -1)",
    "(even? -2)",
    "(exact->inexact 5)",
    "(exact->inexact 0)",
    "(inexact->exact 5.0)",
    "(inexact->exact 0.000)",
    "(number->string 0)",
    "(number->string .5)",
    "(number->string -123.456)",
    "(not #t)",
    "(not 3)",
    "(not (cons 3 '()))",
    "(not #f)",
    "(not '())",
    "(not (list))",
    "(not 'nil)",
    "(boolean? #f)",
    "(boolean? 0)",
    "(boolean? '())",
    "(pair? (cons 'a 'b))",
    "(pair? '(a b c))",
    "(pair? '())",
    "(equal? (cons 'a '()) '(a))",
    "(equal? (cons '(a) '(b c d)) '((a) b c d))",
    "(equal? (cons \"a\" '(b c)) '(\"a\" b c))",
    "(equal? (car '(a b c)) 'a)",
    "(equal? (car '((a) b c d)) '(a))",
    "(equal? (car (cons 1 2)) 1)",
    "(equal? (cdr '((a) b c d)) '(b c d))",
    "(equal? (cdr (cons 1 2)) 2)",
    "(null? '())",
    "(null? (list))",
    "(null? '(1 2 3))",
    "(list? '(a b c))",
    "(list? '((a b) c d))",
    "(list? '())",
    "(list? (cons 'a 'b))",
    "(list? 'a)",
    "(let ((x '(a))) (set-cdr! x x) (list? x))",
    "(let ((x (cons 1 2))) (set-car! x 3) (and (= (car x) 3) (= (cdr x) 2)))",
    "(let ((x (cons 1 2))) (set-cdr! x 3) (and (= (car x) 1) (= (cdr x) 3)))",
    "(equal? (list 'a (+ 3 4) 'c) '(a 7 c))",
    "(list)",
    "(length '(a b c))",
    "(length '(a (b) (c d e)))",
    "(length '())",
    "(list-ref '(a b c) 0)",
    "(list-ref '(a b c d) 2)",
    "(list-ref '(a b c d) (inexact->exact (round 1.8)))",
    "(equal? (memq 'a '(a b c)) '(a b c))",
    "(equal? (memq 'b '(a b c)) '(b c))",
    "(memq 'a '(b c d))",
    "(memq (list 'a) '(b (a) c))",
    "(equal? (member (list 'a) '(b (a) c)) '((a) c))",
    "(member 'd '(a b c))",
    "(equal? (assq 'a '((a 1) (b 2) (c 3))) '(a 1))",
    "(equal? (assq 'b '((a 1) (b 2) (c 3))) '(b 2))",
    "(equal? (assq 'c '((a 1) (b 2) (c 3))) '(c 3))",
    "(assq 'd '((a 1) (b 2) (c 3)))",
    "(assq (list 'a) '(((a)) ((b)) ((c))))",
    "(equal? (assoc (list 'a) '(((a)) ((b)) ((c)))) '((a)))",
    "(symbol? 'foo)",
    "(symbol? (car '(a b)))",
    "(symbol? \"bar\")",
    "(symbol? 'nil)",
    "(symbol? '())",
    "(symbol? #f)",
    "(symbol->string 'flying-fish)",
    "(string->symbol \"flying-fish\")",
    "(char? #\\a)",
    "(char? 0)",
    "(char? '())",
    "(string-append \"foo\" \"bar\")",
    "(string-length \"foobar\")",
    "(string? 'foo)",
    "(string? 1)",
    "(string? \"\")",
    "(string? \"foo\")",
    "(string<? \"foo\" \"bar\")",
    "(string<? \"bar\" \"foo\")",
    "(string<? \"foo\" \"foo\")",
    "(string<? \"f\" \"foo\")",
    "(let ((vec (vector 'a 'b 'c))) (and (equal? (vector-ref vec 0) 'a) (equal? (vector-ref vec 1) 'b) (equal? (vector-ref vec 2) 'c)))",
    "(let ((vec (vector 0 '(2 2 2 2) \"Anna\"))) (vector-set! vec 1 '(\"Sue\" \"Sue\")) (and (equal? (vector-ref vec 0) 0) (equal? (vector-ref vec 1) '(\"Sue\" \"Sue\")) (equal? (vector-ref vec 2) \"Anna\")))",
    "(vector? (vector 'a 'b 'c))",
    "(vector? 'a)",
    "(vector-length (vector))",
    "(vector-length (vector 0 1 0))",
  )

  class Answers(lat: L) {

    import lat._

    val t = bool(true)
    val f = bool(false)

    val answers =
      List(
        t,
        f,
        f,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        f,
        f,
        f,
        t,
        f,
        t,
        t,
        t,
        f,
        t,
        t,
        t,
        f,
        f,
        t,
        t,
        //number(4),
        //number(4),
        //number(1),
        //number(5),
        //number(3),
        //number(3),
        //number(1),
        //number(1),
        number(7),
        number(3),
        number(0),
        number(12),
        number(4),
        number(1),
        number(-1),
        number(-6),
        number(-3),
        number(2),
        real (0.5),
        real (1.0),
        real (1.0),
        real (2.0),
        t,
        f,
        f,
        t,
        f,
        t,
        f,
        t,
        t,
        f,
        f,
        t,
        f,
        f,
        t,
        f,
        t,
        t,
        f,
        t,
        t,
        f,
        number(7),
        number(7),
        number(0),
        number(1),
        number(3),
        number(-3),
        number(-1),
        number(0),
        number(2),
        number(-3),
        number(1),
        number(-1),
        number(1),
        number(-1),
        number(25),
        number(1),
        number(1),
        real(-4.0),
        real(4.0),
        real(-5.0),
        real(3.0),
        number(7),
        real(0.0),
        real(0.0),
        real(1.0),
        real(0.0),
        real(0),
        t,
        real(0.0),
        number(0),
        number(2),
        number(4),
        real(2.0),
        real(0.0),
        f,
        t,
        f,
        f,
        f,
        t,
        t,
        f,
        f,
        t,
        f,
        f,
        t,
        real(5.0),
        real(0.0),
        number(5),
        number(0),
        string("0"),
        string("0.5"),
        string("-123.456"),
        f,
        f,
        f,
        t,
        f,
        f,
        f,
        t,
        f,
        f,
        t,
        t,
        f,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        t,
        f,
        t,
        t,
        t,
        f,
        f,
        f,
        t,
        t,
        t,
        nil,
        number(3),
        number(3),
        number(0),
        symbol("a"),
        symbol("c"),
        symbol("c"),
        t,
        t,
        f,
        f,
        t,
        f,
        t,
        t,
        t,
        f,
        f,
        t,
        t,
        t,
        f,
        t,
        f,
        f,
        string("flying-fish"),
        symbol("flying-fish"),
        t,
        f,
        f,
        string("foobar"),
        number(6),
        f,
        f,
        t,
        t,
        f,
        t,
        f,
        t,
        t,
        t,
        t,
        f,
        number(0),
        number(3))
  }
}