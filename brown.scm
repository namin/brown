;; The Mystery of the Tower Revealed:
;; A Non-Reflective Description of the Reflective Tower
;; Mitchell Wand & Daniel P. Friedman


;; Appendix

;; decomposing expressions

(define first car)
(define second cadr)
(define third caddr)
(define rest cdr)

;; cells

(define (deref-cell cell) (vector-ref cell 0))
(define make-cell (lambda (val) (vector val)))
(define set-cell!
  (lambda (cell val) (vector-set! cell 0 val) val))

;; input/otput with prompts

(define print (lambda (s) (printf s)))

(define prompt&read
  (lambda (prompt)
    (printf "~a" prompt) (print "-> ") (read)))
(define print&prompt
  (lambda (prompt v)
    (printf "~a:: ~a\n" prompt v) prompt))

;; find the global binding of an identifier

(define host-value
  (lambda (id) (eval id)))

(define primop-name-table
  (list 'car 'cdr 'cons 'eq? 'atom? 'symbol?
        'null? 'not 'add1 'sub1 'zero? '+ '- '*
        'set-car! 'set-cdr!
        'print 'length 'read 'newline 'reset
        'make-cell 'deref-cell 'set-cell!
        'ef
        'readloop 'make-reifier))

;; 4 Up and Down the Tower

(define ef
  (lambda (bool x y)
     (if bool x y)))

;; 5.1 Currying

(define-syntax C
  (syntax-rules ()
  [(_ m n) (m n)]
  [(_ m n p ...) (C (m n) p ...)]))

(define-syntax curry
  (syntax-rules ()
  [(_ (i) b ...) (lambda (i) b ...)]
  [(_ (i j ...) b ...)
   (lambda (i)
     (curry (j ...) b ...))]))

(define meta-cons
  (curry (k mk theta)
    (C theta k mk)))

;; applicative-order Y combinator (from Appendix)

(define Y
  (lambda (f)
    (let ([d (lambda (x)
               (f (lambda (arg)
                    (C x x arg))))])
      (d d))))

;; 5.2 Denotations

(define (atom? x) (not (list? x)))

(define denotation
  (lambda (e)
    (cond
      [(atom? e) (denotation-of-identifier e)]
      [(eq? (first e) 'lambda)
       (denotation-of-abstraction e)]
      [else (denotation-of-application e)])))

(define denotation-of-identifier
  (curry (e r k)
    (C r e
       (lambda (cell)
         (let ([v (deref-cell cell)])
           (if (eq? v 'UNASSIGNED)
               ;; added eof logic for batch mode
               (if (not (eq? e #!eof))
                   (wrong
                    (list "Brown: unbound id" e))
                   (lambda (x) x))
               (k v)))))))

(define denotation-of-application
  (curry (e r k)
    (C denotation (first e) r
       (lambda (f) (C f (rest e) r k)))))

(define denotation-of-abstraction
  (curry (e r k)
    (k (F->BF
        (lambda (v*)
          (C denotation (third e)
             (extend r (second e) v*)))))))

(define F->BF
  (curry (fun e r k)
    (C Y (curry (eval-args e k)
           (if (null? e) (k '())
               (C denotation (first e) r
                  (lambda (v)
                    (C eval-args (rest e)
                       (lambda (w)
                         (k (cons v w))))))))
       e (curry (v* mk) (C fun v* k mk)))))

;; 5.3 Reification

(define U->BF
  (curry (r1 e r k)
    (if (= (length e) 1)
        (C denotation (first e) r
           (lambda (v) (C r1 v k)))
        (wrong (list "U->BF: wrong number of args "
                     e)))))

(define K->BF
  (curry (k1 e r k)
    (if (= (length e) 1)
        (lambda (mk)
          (C denotation (first e) r
             k1 (C meta-cons k mk)))
        (wrong (list "K->BF: wrong number of args "
                     e)))))

;; 5.4 Building Reflective Procedures

(define make-reifier
  (let ([ERK '(E R K)])
    (curry (bf e r k mk)
      (mk (C bf ERK
             (extend r ERK
               (list e (U->BF r) (K->BF k))))))))

;; 5.5 Reflection

;; from section 3
(define initk
  (lambda (v)
    (lambda (mk)
      (mk (lambda (k) (k v))))))

(define z '(v))
  (define BF->K
    (curry (bf v)
      (C bf z
         (extend global-env z (list v)) initk)))
  (define BF->U
    (curry (bf v)
      (C bf z
         (extend global-env z (list v)))))

(define meaning
  (curry (erk k mk)
    (C denotation
       (first erk)
       (BF->U (second erk))
       (BF->K (third erk))
       (C meta-cons k mk))))

;; 5.6 The tower

(define R-E-P
  (lambda (prompt)
    (Y (curry (loop v)
         (C denotation
            (prompt&read
             (print&prompt prompt v))
             global-env
             loop)))))

(define tower
  ((Y (curry (loop n theta)
        (C theta (R-E-P n) (loop (add1 n)))))
   0))

(define readloop
  (lambda (prompt)
    (K->BF (R-E-P prompt))))

(define boot-tower
  (lambda ()
    (C initk 'starting-up tower)))

;; 5.8 Side Effects

(define wrong
  (curry (v mk)
    (printf "wrong: ~a\n" v)
    (C initk 'wrong mk)))

;; 5.7 The Initial Environment

(define extend
  (lambda (r names vals)
    (if (= (length names) (length vals))
        (let ([cells (map make-cell vals)])
          (curry (name k)
            (rib-lookup name names cells k
              (lambda () (C r name k)))))
        (wrong (list "extend: "
                     "Formals: " names
                     "Actuals: " vals)))))

(define rib-lookup
  (lambda (id names cells sk fk)
    (C Y (curry (lookup names cells)
           (cond
             [(null? names) (fk)]
             [(eq? (first names) id)
              (sk (first cells))]
             [else
              (C lookup
                 (rest names)
                 (rest cells))]))
       names cells)))

(define id->BF
  (let ([host->F
         (curry (f v* k) (k (apply f v*)))])
    (lambda (x)
      (F->BF (host->F (host-value x))))))

(define global-env
  (let ([id->F-cell
         (lambda (x) (make-cell (id->BF x)))])
      (let ([initnames
             (append
              (list'nil 't 'wrong 'meaning)
              primop-name-table)]
            [initcells
             (append
              (map make-cell
                   (list 'nil 't
                         (K->BF wrong)
                         (F->BF meaning)))
              (map id->F-cell
                   primop-name-table))])
          (curry (id k)
            (rib-lookup
             id initnames initcells k
             (lambda ()
               (let
                   ([c (make-cell 'UNASSIGNED)])
                 (set! initnames
                       (cons id initnames))
                 (set! initcells
                       (cons c initcells))
                 (k c))))))))

